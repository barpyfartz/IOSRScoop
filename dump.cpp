#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cstring>
#include <cstdint>
#include <algorithm>
#include <zlib.h>
#include <unordered_map>

struct mach_header_64 {
    uint32_t magic;
    int32_t  cputype;
    int32_t  cpusubtype;
    uint32_t filetype;
    uint32_t ncmds;
    uint32_t sizeofcmds;
    uint32_t flags;
    uint32_t reserved;
};

struct load_command {
    uint32_t cmd;
    uint32_t cmdsize;
};

struct segment_command_64 {
    uint32_t cmd;
    uint32_t cmdsize;
    char     segname[16];
    uint64_t vmaddr;
    uint64_t vmsize;
    uint64_t fileoff;
    uint64_t filesize;
    int32_t  maxprot;
    int32_t  initprot;
    uint32_t nsects;
    uint32_t flags;
};

struct section_64 {
    char     sectname[16];
    char     segname[16];
    uint64_t addr;
    uint64_t size;
    uint32_t offset;
    uint32_t align;
    uint32_t reloff;
    uint32_t nreloc;
    uint32_t flags;
    uint32_t reserved1;
    uint32_t reserved2;
    uint32_t reserved3;
};

#define MH_MAGIC_64 0xfeedfacf

namespace iosrscoop_mem {
    uint8_t* data = nullptr;
    size_t size = 0;
    size_t text_start = 0;
    size_t text_end = 0;
    uint64_t text_vmaddr = 0;
    uint64_t text_fileoff = 0;

    bool load_mach_o(const std::vector<uint8_t>& buffer) {
        data = const_cast<uint8_t*>(buffer.data());
        size = buffer.size();

        if (size < sizeof(mach_header_64)) return false;
        mach_header_64* header = (mach_header_64*)data;

        if (header->magic != MH_MAGIC_64) return false;

        size_t offset = sizeof(mach_header_64);
        for (uint32_t i = 0; i < header->ncmds; i++) {
            if (offset + sizeof(load_command) > size) break;
            load_command* lc = (load_command*)(data + offset);

            if (lc->cmd == 0x19) {
                segment_command_64* seg = (segment_command_64*)(data + offset);
                if (strcmp(seg->segname, "__TEXT") == 0) {
                    text_vmaddr = seg->vmaddr;
                    text_fileoff = seg->fileoff;
                    size_t sect_offset = offset + sizeof(segment_command_64);
                    for (uint32_t j = 0; j < seg->nsects; j++) {
                        if (sect_offset + sizeof(section_64) > size) break;
                        section_64* sect = (section_64*)(data + sect_offset);
                        if (strcmp(sect->sectname, "__text") == 0) {
                            text_start = sect->offset;
                            text_end = sect->offset + sect->size;
                            return true;
                        }
                        sect_offset += sizeof(section_64);
                    }
                }
            }
            offset += lc->cmdsize;
        }
        return false;
    }

    std::vector<uintptr_t> find_str_all(const char* str) {
        std::vector<uintptr_t> matches;
        size_t len = strlen(str);
        if (!len || size < len + 1) return matches;
        
        for (size_t i = 0; i <= size - (len + 1); i++) {
            if (memcmp(data + i, str, len) == 0 && data[i + len] == '\0') {
                matches.push_back(i);
            }
        }
        return matches;
    }

    uintptr_t find_bytes(const char* sig) {
        std::vector<uint8_t> bytes;
        std::vector<bool> mask;

        const char* p = sig;
        while (*p) {
            while (*p == ' ') p++;
            if (!*p) break;
            if (p[0] == '?' && p[1] == '?') {
                bytes.push_back(0);
                mask.push_back(false);
                p += 2;
            } else {
                bytes.push_back((uint8_t)strtol(p, nullptr, 16));
                mask.push_back(true);
                p += 2;
            }
        }

        size_t len = bytes.size();
        if (!len || text_end < text_start + len) return 0;

        size_t limit = text_end - len;
        for (size_t i = text_start; i <= limit; i++) {
            bool match = true;
            for (size_t k = 0; k < len && match; k++)
                if (mask[k] && data[i + k] != bytes[k]) match = false;
            if (match) return i;
        }
        return 0;
    }

    static inline bool is_adrp(uint32_t insn) { return (insn & 0x9F000000) == 0x90000000; }
    static inline bool is_adr(uint32_t insn) { return (insn & 0x9F000000) == 0x10000000; }
    static inline bool is_add_imm(uint32_t insn) { return (insn & 0xFF000000) == 0x91000000; }
    static inline uint64_t decode_add_imm(uint32_t insn) { return (insn >> 10) & 0xFFF; }
    
    static inline bool is_ldr_imm(uint32_t insn) {
        uint32_t op = insn & 0xFFC00000;
        return op == 0xB9400000 || op == 0xF9400000;
    }

    static inline uint64_t decode_ldr_imm(uint32_t insn) {
        return ((insn >> 10) & 0xFFF) << (insn >> 30);
    }

    static inline uint64_t decode_adr(uint32_t insn, uint64_t pc) {
        uint32_t immlo = (insn >> 29) & 3;
        uint32_t immhi = (insn >> 5) & 0x7FFFF;
        int64_t imm = (int64_t)((immhi << 2) | immlo);
        if (imm & 0x100000) imm -= 0x200000;
        return pc + imm;
    }

    static inline uint64_t decode_adrp(uint32_t insn, uint64_t pc) {
        uint64_t immhi = (insn >> 5) & 0x7FFFF;
        uint64_t immlo = (insn >> 29) & 3;
        int64_t imm = (int64_t)((immhi << 2) | immlo) << 12;
        if (imm & (1LL << 32)) imm |= ~((1LL << 33) - 1);
        return (pc & ~0xFFFULL) + (uint64_t)imm;
    }

    std::vector<uintptr_t> find_xrefs(uintptr_t target) {
        std::vector<uintptr_t> results;
        if (!text_start || !text_end) return results;

        size_t begin = (text_start + 3) & ~3ULL;
        size_t end = text_end - 8;

        uint64_t delta = text_vmaddr - text_fileoff;
        uint64_t target_VA = target + delta;

        for (size_t i = begin; i < end; i += 4) {
            uint32_t* code = (uint32_t*)(data + i);
            uint64_t pc_VA = i + delta;

            if (is_adrp(code[0])) {
                uint64_t page_base = decode_adrp(code[0], pc_VA);
                uint64_t add_val = 0;
                if (is_add_imm(code[1]))       add_val = decode_add_imm(code[1]);
                else if (is_ldr_imm(code[1]))  add_val = decode_ldr_imm(code[1]);
                else continue;

                if (page_base + add_val == target_VA) {
                    results.push_back(i);
                    if (results.size() >= 4) break;
                }
            }
            else if (is_adr(code[0])) {
                if (decode_adr(code[0], pc_VA) == target_VA) {
                    results.push_back(i);
                    if (results.size() >= 4) break;
                }
            }
        }
        return results;
    }

    static inline bool is_func_prologue(uint32_t insn) {
        return (insn & 0xFFC00000) == 0xA9800000 ||
               (insn & 0xFF8003FF) == 0xD10003FF ||
               insn == 0xD503233F;
    }

    uintptr_t find_func(uintptr_t from) {
        if (from < text_start || from >= text_end) return 0;

        int lo = (int)from - 65536;
        if (lo < (int)text_start) lo = (int)text_start;

        size_t start_i = (from & ~3ULL);
        for (int i = (int)start_i; i >= lo; i -= 4) {
            uint32_t insn = *(uint32_t*)(data + i);

            if (is_func_prologue(insn)) return i;

            bool is_ret = (insn & 0xFFFFFC00) == 0xD65F0000;
            bool is_br  = (insn & 0xFFFFFC00) == 0xD61F0000;
            bool is_b   = (insn & 0xFC000000) == 0x14000000;

            if ((is_ret || is_br || is_b) && i + 4 <= (int)from) {
                if (is_b) {
                    int64_t imm26 = (int64_t)(insn & 0x3FFFFFF);
                    if (imm26 & 0x2000000) imm26 |= ~(int64_t)0x3FFFFFF;
                    int64_t bt = (int64_t)i + (imm26 << 2);
                    if (bt >= (int64_t)lo && bt <= (int64_t)from) continue;
                }
                if (is_func_prologue(*(uint32_t*)(data + i + 4))) return i + 4;
            }
        }
        return 0;
    }
}

static bool read_entire_file(const std::string& path, std::vector<uint8_t>& out) {
    std::ifstream f(path, std::ios::binary);
    if (!f) return false;
    f.seekg(0, std::ios::end);
    size_t sz = f.tellg();
    f.seekg(0);
    out.resize(sz);
    f.read(reinterpret_cast<char*>(out.data()), sz);
    return f.good();
}

static bool extract_file_from_zip(const std::vector<uint8_t>& zip_data, const std::string& target_name, std::vector<uint8_t>& out) {
    if (zip_data.size() < 22) return false;
    size_t eocd = 0;
    for (size_t i = zip_data.size() - 22; i > 0; --i) {
        if (zip_data[i] == 0x50 && zip_data[i+1] == 0x4B && zip_data[i+2] == 0x05 && zip_data[i+3] == 0x06) { eocd = i; break; }
    }
    if (!eocd) return false;

    uint32_t cd_offset = *(uint32_t*)&zip_data[eocd + 16];
    uint16_t cd_entries = *(uint16_t*)&zip_data[eocd + 8];

    size_t pos = cd_offset;
    for (size_t i = 0; i < cd_entries; ++i) {
        if (pos + 46 > zip_data.size()) break;
        if (zip_data[pos] != 0x50 || zip_data[pos+1] != 0x4B || zip_data[pos+2] != 0x01 || zip_data[pos+3] != 0x02) break;

        uint16_t fn_len    = *(uint16_t*)&zip_data[pos + 28];
        uint16_t extra_len = *(uint16_t*)&zip_data[pos + 30];
        uint16_t cmnt_len  = *(uint16_t*)&zip_data[pos + 32];
        uint32_t l_offset  = *(uint32_t*)&zip_data[pos + 42];
        uint32_t comp_size = *(uint32_t*)&zip_data[pos + 20];
        uint32_t uncomp    = *(uint32_t*)&zip_data[pos + 24];
        uint16_t method    = *(uint16_t*)&zip_data[pos + 10];

        if (pos + 46 + fn_len > zip_data.size()) break;
        std::string name((char*)&zip_data[pos + 46], fn_len);

        if (name == target_name) {
            if (l_offset + 30 > zip_data.size()) return false;
            uint16_t lfn = *(uint16_t*)&zip_data[l_offset + 26];
            uint16_t lex = *(uint16_t*)&zip_data[l_offset + 28];
            size_t dp = l_offset + 30 + lfn + lex;

            if (dp + comp_size > zip_data.size()) return false;

            if (method == 0) {
                out.assign(zip_data.begin() + dp, zip_data.begin() + dp + comp_size);
                return true;
            }
            if (method == 8) {
                out.resize(uncomp);
                z_stream zs = {};
                zs.next_in  = const_cast<uint8_t*>(&zip_data[dp]);
                zs.avail_in = comp_size;
                zs.next_out = out.data();
                zs.avail_out = uncomp;
                if (inflateInit2(&zs, -15) != Z_OK) return false;
                int r = inflate(&zs, Z_FINISH);
                inflateEnd(&zs);
                if (r == Z_STREAM_END || r == Z_OK) {
                    out.resize(zs.total_out);
                    return true;
                }
            }
        }
        pos += 46 + fn_len + extra_len + cmnt_len;
    }
    return false;
}

bool extract_roblox_lib(const std::string& ipa_path, std::vector<uint8_t>& out_buffer) {
    std::vector<uint8_t> zip_data;
    if (!read_entire_file(ipa_path, zip_data)) return false;
    return extract_file_from_zip(zip_data, "Payload/Roblox.app/Frameworks/RobloxLib.framework/RobloxLib", out_buffer);
}

static std::string goyims(uintptr_t offset) {
    if (offset >= iosrscoop_mem::size) return "";
    std::string res;
    const uint8_t* d = iosrscoop_mem::data + offset;
    while (offset < iosrscoop_mem::size && *d != 0) {
        res.push_back((char)*d);
        offset++; d++;
        if (res.size() > 50) break;
    }
    return res;
}

static inline bool is_bl(uint32_t insn) { return (insn & 0xFC000000) == 0x94000000; }

static inline uint64_t decode_bl(uint32_t insn, uint64_t pc) {
    int64_t imm = (insn & 0x3FFFFFF);
    if (imm & 0x2000000) imm -= 0x4000000;
    return pc + (imm << 2);
}

static uintptr_t bl_up(uintptr_t from, int n) {
    int count = 0;
    int start = ((int)from - 4) & ~3;
    int lo = std::max((int)iosrscoop_mem::text_start, (int)from - 600);
    for (int j = start; j >= lo; j -= 4) {
        if (is_bl(*(uint32_t*)(iosrscoop_mem::data + j))) {
            uintptr_t candidate = decode_bl(*(uint32_t*)(iosrscoop_mem::data + j), (uint64_t)j);
            if (candidate >= iosrscoop_mem::text_start && candidate < iosrscoop_mem::text_end) {
                if (++count == n) return candidate;
            }
        }
    }
    return 0;
}

static uintptr_t bl_down(uintptr_t from, int n) {
    int count = 0;
    size_t end = std::min(from + 600, iosrscoop_mem::text_end - 4);
    size_t start = ((from + 4) & ~3ULL);
    for (size_t j = start; j <= end; j += 4) {
        if (is_bl(*(uint32_t*)(iosrscoop_mem::data + j))) {
            uintptr_t candidate = decode_bl(*(uint32_t*)(iosrscoop_mem::data + j), (uint64_t)j);
            if (candidate >= iosrscoop_mem::text_start && candidate < iosrscoop_mem::text_end) {
                if (++count == n) return candidate;
            }
        }
    }
    return 0;
}

static uintptr_t to_func(uintptr_t candidate) {
    if (!candidate) return 0;
    uintptr_t f = iosrscoop_mem::find_func(candidate);
    return f ? f : candidate;
}

static uintptr_t iqmaxx(const char* name) {
    auto matches = iosrscoop_mem::find_str_all(name);
    if (matches.empty()) return 0;
    
    uint64_t delta = iosrscoop_mem::text_vmaddr - iosrscoop_mem::text_fileoff;
    
    for (uintptr_t str_offset : matches) {
        uint64_t target_VA = str_offset + delta;
        for (size_t i = 0; i <= iosrscoop_mem::size - 16; i += 8) {
            if (*(uint64_t*)(iosrscoop_mem::data + i) == target_VA) {
                uint64_t func_VA = *(uint64_t*)(iosrscoop_mem::data + i + 8);
                if (func_VA >= iosrscoop_mem::text_vmaddr && func_VA < iosrscoop_mem::text_vmaddr + iosrscoop_mem::size) {
                    return func_VA - delta;
                }
            }
        }
    }
    return 0;
}

struct iOSScan {
    std::string name;
    std::string pattern;
    std::string sig;
    int up = 0;
    int down = 0;
    bool offset = false;
    bool reg = false;
    iOSScan(std::string n, std::string p, int u = 0, int d = 0) : name(n), pattern(p), sig(""), up(u), down(d), offset(false), reg(false) {}
    iOSScan(std::string n, std::string p, std::string s, int u, int d, bool o = false) : name(n), pattern(p), sig(s), up(u), down(d), offset(o), reg(false) {}
    iOSScan(std::string n, std::string p, std::string s, int u, int d, bool o, bool r) : name(n), pattern(p), sig(s), up(u), down(d), offset(o), reg(r) {}
};

void goy(const std::vector<iOSScan>& scans, std::vector<uintptr_t>& results) {
    uintptr_t desync_addr = 0;
    for (size_t i = 0; i < scans.size(); ++i) {
        if (scans[i].name == "TaskDesynchronize") { desync_addr = results[i]; break; }
    }
    if (!desync_addr) return;

    uintptr_t reg_xref = 0;
    size_t begin = (iosrscoop_mem::text_start + 3) & ~3ULL;
    size_t end = iosrscoop_mem::text_end - 8;
    uint64_t delta = iosrscoop_mem::text_vmaddr - iosrscoop_mem::text_fileoff;

    for (size_t i = begin; i < end; i += 4) {
        uint32_t* code = (uint32_t*)(iosrscoop_mem::data + i);
        if (iosrscoop_mem::is_adrp(code[0])) {
            uint64_t page = iosrscoop_mem::decode_adrp(code[0], i + delta);
            uint64_t offset = iosrscoop_mem::is_add_imm(code[1]) ? iosrscoop_mem::decode_add_imm(code[1]) : (iosrscoop_mem::is_ldr_imm(code[1]) ? iosrscoop_mem::decode_ldr_imm(code[1]) : 0);
            if (page + offset - delta == desync_addr) { reg_xref = i; break; }
        }
    }
    if (!reg_xref) return;

    size_t window_start = (reg_xref >= 300) ? reg_xref - 300 : iosrscoop_mem::text_start;
    size_t window_end = std::min(reg_xref + 500, iosrscoop_mem::text_end - 8);
    window_start = (window_start + 3) & ~3ULL;

    std::string pending_string = "";
    std::unordered_map<std::string, uintptr_t> resolved_tasks;

    for (size_t i = window_start; i < window_end; i += 4) {
        uint32_t* code = (uint32_t*)(iosrscoop_mem::data + i);
        uint64_t resolved_target_VA = 0;
        uint64_t pc_VA = i + delta;

        if (iosrscoop_mem::is_adrp(code[0]) && i + 4 < window_end) {
            uint64_t page = iosrscoop_mem::decode_adrp(code[0], pc_VA);
            uint64_t offset = iosrscoop_mem::is_add_imm(code[1]) ? iosrscoop_mem::decode_add_imm(code[1]) : (iosrscoop_mem::is_ldr_imm(code[1]) ? iosrscoop_mem::decode_ldr_imm(code[1]) : 0);
            resolved_target_VA = page + offset;
        } else if (iosrscoop_mem::is_adr(code[0])) {
            resolved_target_VA = iosrscoop_mem::decode_adr(code[0], pc_VA);
        }

        if (resolved_target_VA) {
            uint64_t resolved_target = resolved_target_VA - delta;
            if (resolved_target >= iosrscoop_mem::text_start && resolved_target < iosrscoop_mem::text_end) {
                if (!pending_string.empty()) { resolved_tasks[pending_string] = resolved_target; pending_string = ""; }
            } else {
                std::string s = goyims(resolved_target);
                if (s == "synchronize" || s == "desynchronize" || s == "defer" || s == "spawn" || s == "delay" || s == "wait" || s == "cancel") pending_string = s;
            }
        }
    }

    for (size_t i = 0; i < scans.size(); ++i) {
        if (scans[i].name.rfind("Task", 0) == 0 && scans[i].name.find("Scheduler") == std::string::npos) {
            std::string key = scans[i].name.substr(4);
            std::transform(key.begin(), key.end(), key.begin(), ::tolower);
            if (resolved_tasks.find(key) != resolved_tasks.end()) results[i] = resolved_tasks[key];
        }
    }
}

uintptr_t larp(uintptr_t get_fn_addr) {
    if (!get_fn_addr) return 0;
    uint64_t delta = iosrscoop_mem::text_vmaddr - iosrscoop_mem::text_fileoff;
    for (int i = 4; i < 500; i += 4) {
        uintptr_t curr_pc = get_fn_addr - i;
        if (curr_pc < iosrscoop_mem::text_start) break;
        uint32_t* code = (uint32_t*)(iosrscoop_mem::data + curr_pc);
        if (iosrscoop_mem::is_adrp(code[0])) {
            uint64_t page = iosrscoop_mem::decode_adrp(code[0], curr_pc + delta);
            uint64_t offset = iosrscoop_mem::is_add_imm(code[1]) ? iosrscoop_mem::decode_add_imm(code[1]) : (iosrscoop_mem::is_ldr_imm(code[1]) ? iosrscoop_mem::decode_ldr_imm(code[1]) : 0);
            uint64_t target_offset = page + offset - delta;
            if (target_offset > iosrscoop_mem::text_end) return target_offset;
        }
    }
    return 0;
}

std::vector<iOSScan> ios_scans = {
    // goyims
    {"Print",                         "Current identity is %d", 0, 0},
    {"LuaToCFunction",                "Current identity is %d", 1, 0}, // should be right????
    {"GameLoaded",                    "[FLog::LogStepTimeAndNetworkUsage] Game Loaded", "", 0, 0, false},
    {"FastLog",                       "[FLog::LogStepTimeAndNetworkUsage] Game Loaded", 1, 0},
    {"RawScheduler",                  "HumanoidParallelManagerTaskQueue", "", 1, 0, false},
    {"EnableLoadModule",              "EnableLoadModule", "", 0, 0, false},
    {"TaskDesynchronize",             "task.desynchronize() should only be called from a script that is a descendant of an Actor", 0, 0},
    {"TaskSynchronize",               "", "", 0, 0, false},
    {"TaskDefer",                     "", "", 0, 0, false},
    {"TaskSpawn",                     "", "", 0, 0, false},
    {"TaskDelay",                     "", "", 0, 0, false},
    {"TaskWait",                      "", "", 0, 0, false},
    {"TaskCancel",                    "", "", 0, 0, false},
    {"LuaResume",                     "cannot resume dead coroutine",                      "", 0, 0, false},
    {"LuaResumeFromSuspended",        "cannot resume non-suspended coroutine",             "", 0, 0, false},
    {"LuauYield",                     "attempt to yield across metamethod/C-call boundary", "", 0, 0, false},
    {"LuaMTooBig",                     "memory allocation error: block too big", "", 0, 0, false},
    {"LuauLoad",                      "%s: bytecode version mismatch (expected [%d..%d], got %d)", "", 0, 0, false},
    {"LuauExecuteNilError",           "table index is nil", "", 0, 0, false},
    // {"LuauMetatableChainError",       "metatable chain too long", "", 0, 0, false},
    {"LuauSetFenvProtectedError",     "'setfenv' cannot change environment of given object", "", 0, 0, false},
    {"LuauNotEnoughMemoryError",      "not enough memory", "", 0, 0, false},
    {"LuauInlineHits",                "LuauInlineHitsThreshold", "", 0, 0, false},
    // {"LuauTypeIdGenerator",           "generateTypeId__", "", 0, 0, true},
    {"LoadString",                    "loadstring() is not available", "", 0, 0, false},
    {"GetFenv",                       "getfenv", "", 0, 0, false, true},
    {"SetFenv",                       "'setfenv' cannot change environment of given object", "", 0, 0, false},
    {"TypeOf",                        "typeof", "", 0, 0, false, true},
    {"ScriptExecutionNotAllowed",     "Script execution is not allowed in this context", "", 0, 0, false},
    {"RobloxScriptContextBlocked",    "Script execution is not allowed in this context", "", 0, 0, false},
    {"TargetScriptDestroyed",         "The target script of this thread has been destroyed", "", 0, 0, false},
    {"RobloxThreadScriptDestroyed",   "The target script of this thread has been destroyed", "", 0, 0, false},
    {"CallbacksCannotYield",          "Callbacks cannot yield", "", 0, 0, false},
    // {"CoreScriptNotAuthorized",       "CoreScript %s is not authorized to create a CoreScript", "", 0, 0, false},
    {"LuauModuleInstructionLimit",    "Function '{}' at line {} exceeded total module instruction limit\n", "", 0, 0, false},
    {"LuauFuncCodeBlockLimit",        "Function '{}' at line {} exceeded function code block limit\n", "", 0, 0, false},
    {"DebugDisableOptimizedBytecode", "DebugDisableOptimizedBytecode", "", 0, 0, false},
    {"DebugDisableCodegen",           "DebugDisableCodegen", "", 0, 0, false},
    {"NcgNotSupported",               "Native code generation is not supported on this device", "", 0, 0, false},
    {"DebugDumpHeap",                 "debug.dumpheap is not enabled.", "", 0, 0, false},
    {"DebugDumpRefs",                 "debug.dumprefs is not enabled.", "", 0, 0, false},
    {"LuaHeapSavedTrace",             "Lua heap saved to %s", "", 0, 0, false},
    {"LuaHSetTable",                  "table index is nil", "", 0, 0, false},
    {"LuauGcAtomicWeakMs",            "AtomicWeakTimeMs", "", 0, 0, false},
    {"LuauGcMemTriggerPc",            "MemTriggerToStartPc", "", 0, 0, false},
    {"FireTouchInterest",             "new overlap in different world", "", 0, 0, false},
    {"RequireRobloxScriptFail",       "Cannot require a RobloxScript module from a non RobloxScript context", "", 0, 0, false},
    {"RequireCBoundaryFail",          "require must be called by a Luau function in this context (e.g. function() require(...) end)", "", 0, 0, false},
    {"MaliciousModuleDisabled",       "ModuleScript %s detected as malicious.  Script has been disabled.", "", 0, 0, false},
    {"DumpCodeSizeCommandBar",        "dumpcodesize can only be called from CommandBar", "", 0, 0, false},
    {"NcgFailedInterpreted",          "Native code generation of script %s failed:  %s.  Script will be interpreted.", "", 0, 0, false},
    {"FlogDeferredDeletionStart",     "[FLog::DataModelJobs] Deferred deletion start, data model: %p", "", 0, 0, false},
    {"FlogParallelGcFlushStart",      "[FLog::DataModelJobs] Parallel GC callback flushing started, data model: %p", "", 0, 0, false},
    {"MetricThreadStartDuration",     "ThreadStartDurationMs", "", 0, 0, false},
    {"MetricParallelFuncDuration",    "ParallelFunctionDurationMs", "", 0, 0, false},
    {"MetricJoinDuration",            "JoinDurationMs", "", 0, 0, false},
    {"TaskSchedulerCantInitFlags",    "Can't initialize the TaskScheduler before flags have been loaded", "", 0, 0, false},
    {"TaskSchedulerGetFn",            "Can't initialize the TaskScheduler before flags have been loaded", "", 0, 0, true}, 
    {"TaskSchedulerStepMarker",       "TS::Step", "", 0, 0, false},
    {"TaskSchedulerArbiterFail",      "Default job arbiter must always be valid", "", 0, 0, false},
    {"TaskSchedulerTargetFps",        "TaskSchedulerTargetFps", "", 0, 0, false},
};

int main(int argc, char** argv) {
    if (argc < 2) return 1;

    std::vector<uint8_t> binary_buffer;
    std::string version = "";
    {
        std::vector<uint8_t> zip_data;
        if (read_entire_file(argv[1], zip_data)) {
            if (!extract_file_from_zip(zip_data, "Payload/Roblox.app/Frameworks/RobloxLib.framework/RobloxLib", binary_buffer)) {
                binary_buffer = zip_data;
            } else {
                std::vector<uint8_t> info_plist_data;
                if (extract_file_from_zip(zip_data, "Payload/Roblox.app/Info.plist", info_plist_data)) {
                    std::string content((char*)info_plist_data.data(), info_plist_data.size());
                    size_t key_pos = content.find("<key>CFBundleShortVersionString</key>");
                    if (key_pos != std::string::npos) {
                        size_t str_pos = content.find("<string>", key_pos);
                        if (str_pos != std::string::npos) {
                            size_t end_pos = content.find("</string>", str_pos);
                            if (end_pos != std::string::npos) {
                                version = content.substr(str_pos + 8, end_pos - (str_pos + 8));
                            }
                        }
                    }
                }
            }
        } else {
            return 1;
        }
    }

    if (!iosrscoop_mem::load_mach_o(binary_buffer)) return 1;

    std::vector<uintptr_t> results(ios_scans.size(), 0);

    for (size_t i = 0; i < ios_scans.size(); ++i) {
        const auto& scan = ios_scans[i];
        if (scan.reg) {
            results[i] = iqmaxx(scan.pattern.c_str());
            continue;
        }
        if (scan.pattern.empty() && scan.sig.empty()) continue; 

        if (!scan.pattern.empty()) {
            auto string_offsets = iosrscoop_mem::find_str_all(scan.pattern.c_str());
            for (uintptr_t addr : string_offsets) {
                auto xrefs = iosrscoop_mem::find_xrefs(addr);
                if (!xrefs.empty()) {
                    uintptr_t tx = xrefs[0];
                    if (scan.up == 0 && scan.down == 0) results[i] = iosrscoop_mem::find_func(tx);
                    else if (scan.up > 0)               results[i] = to_func(bl_up(tx, scan.up));
                    else                                results[i] = to_func(bl_down(tx, scan.down));
                    break; 
                }
            }
        } else if (!scan.sig.empty()) {
            uintptr_t addr = iosrscoop_mem::find_bytes(scan.sig.c_str());
            if (addr && scan.offset) {
                results[i] = (scan.up > 0) ? to_func(bl_up(addr, scan.up)) : ((scan.down > 0) ? to_func(bl_down(addr, scan.down)) : to_func(addr));
            }
        }
    }

    goy(ios_scans, results);
    
    uintptr_t ts_get_fn = 0;
    for (size_t i = 0; i < ios_scans.size(); ++i) {
        if (ios_scans[i].name == "TaskSchedulerGetFn") { ts_get_fn = results[i]; break; }
    }
    uintptr_t ts_singleton = larp(ts_get_fn);
    uintptr_t luaD_throw = 0;
    auto exc_matches = iosrscoop_mem::find_str_all("13lua_exception");
    if (!exc_matches.empty()) {
        uint64_t delta = iosrscoop_mem::text_vmaddr - iosrscoop_mem::text_fileoff;
        uint64_t str_VA = exc_matches[0] + delta;
        uintptr_t tinfo_VA = 0;
        for (size_t i = 0; i <= iosrscoop_mem::size - 16; i += 8) {
            if (*(uint64_t*)(iosrscoop_mem::data + i) == str_VA) {
                tinfo_VA = i - 8 + delta;
                break;
            }
        }
        if (tinfo_VA) {
            auto tinfo_xrefs = iosrscoop_mem::find_xrefs(tinfo_VA - delta);
            if (!tinfo_xrefs.empty()) {
                luaD_throw = iosrscoop_mem::find_func(tinfo_xrefs[0]);
            }
        }
    }
    uintptr_t luau_execute = 0;
    uintptr_t lua_resume = 0;
    for (size_t i = 0; i < ios_scans.size(); ++i) {
        if (ios_scans[i].name == "LuaResume") { lua_resume = results[i]; break; }
    }
    if (lua_resume) {
        size_t end_resume = lua_resume + 4;
        while (end_resume < iosrscoop_mem::text_end) {
            uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + end_resume);
            if (iosrscoop_mem::is_func_prologue(insn)) break;
            end_resume += 4;
        }

        std::vector<uintptr_t> tail_targets;
        for (size_t pc = lua_resume; pc < end_resume; pc += 4) {
            uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + pc);
            if ((insn & 0xFC000000) == 0x14000000) {
                uintptr_t target = decode_bl(insn, pc);
                if (target >= iosrscoop_mem::text_start && target < iosrscoop_mem::text_end) {
                    if (target < lua_resume || target >= end_resume) {
                        tail_targets.push_back(target);
                    }
                }
            }
        }

        for (uintptr_t tail_target : tail_targets) {
            size_t end_tail = tail_target + 4;
            while (end_tail < iosrscoop_mem::text_end) {
                uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + end_tail);
                if (iosrscoop_mem::is_func_prologue(insn)) break;
                end_tail += 4;
            }

            std::vector<uintptr_t> bl_targets;
            for (size_t pc = tail_target; pc < end_tail; pc += 4) {
                uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + pc);
                if (is_bl(insn)) {
                    uintptr_t target = decode_bl(insn, pc);
                    if (target >= iosrscoop_mem::text_start && target < iosrscoop_mem::text_end) {
                        bl_targets.push_back(target);
                    }
                }
            }

            for (uintptr_t t : bl_targets) {
                int count = 0;
                for (size_t pc = t; pc < t + 4000 && pc < iosrscoop_mem::text_end; pc += 4) {
                    uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + pc);
                    if ((insn & 0xffc00c00) == 0xb8400400) {
                        uint32_t rt = insn & 0x1f;
                        uint32_t rn = (insn >> 5) & 0x1f;
                        uint32_t imm9 = (insn >> 12) & 0x1ff;
                        if (rt != 31 && rn != 31 && imm9 == 4) {
                            count++;
                        }
                    }
                }
                if (count > 10) {
                    luau_execute = t;
                    break;
                }
            }
            if (luau_execute) break;
        }
    }
    uintptr_t luaC_step = 0;
    if (lua_resume) {
        uintptr_t luau_range_start = (lua_resume >= 0x30000) ? lua_resume - 0x30000 : iosrscoop_mem::text_start;
        uintptr_t luau_range_end = std::min(lua_resume + 0x30000, (uintptr_t)iosrscoop_mem::text_end);

        struct GCFunction {
            uintptr_t addr;
            std::vector<uintptr_t> calls;
        };
        std::vector<GCFunction> gc_funcs;

        uintptr_t curr_func = 0;
        bool has_gc_offsets = false;
        std::vector<uintptr_t> bl_calls;

        for (size_t pc = luau_range_start; pc < luau_range_end; pc += 4) {
            uint32_t insn = *(uint32_t*)(iosrscoop_mem::data + pc);
            if (iosrscoop_mem::is_func_prologue(insn)) {
                if (curr_func != 0 && has_gc_offsets) {
                    gc_funcs.push_back({curr_func, bl_calls});
                }
                curr_func = pc;
                has_gc_offsets = false;
                bl_calls.clear();
            }

            if (curr_func != 0) {
                uint32_t op = insn & 0xffc00000;
                if (op == 0xf9400000 || op == 0xf9000000) {
                    uint32_t imm = ((insn >> 10) & 0xfff) << 3;
                    if (imm >= 0x4400 && imm <= 0x4750) {
                        has_gc_offsets = true;
                    }
                } else if (is_bl(insn)) {
                    uintptr_t target = decode_bl(insn, pc);
                    if (target >= iosrscoop_mem::text_start && target < iosrscoop_mem::text_end) {
                        bl_calls.push_back(target);
                    }
                }
            }
        }
        if (curr_func != 0 && has_gc_offsets) {
            gc_funcs.push_back({curr_func, bl_calls});
        }

        for (const auto& gf1 : gc_funcs) {
            int call_count = 0;
            for (const auto& gf2 : gc_funcs) {
                if (gf1.addr == gf2.addr) continue;
                for (uintptr_t target : gf2.calls) {
                    if (target == gf1.addr) {
                        call_count++;
                        break;
                    }
                }
            }
            if (call_count >= 1) {
                luaC_step = gf1.addr;
                break;
            }
        }
    }

    std::cout << std::hex << std::uppercase;
    for (size_t i = 0; i < ios_scans.size(); ++i) {
        std::cout << ios_scans[i].name << ": ";
        if (results[i]) std::cout << "0x" << results[i] << "\n";
        else std::cout << "NOT_FOUND\n";
    }

    std::cout << "TaskSchedulerInstancePtr: ";
    if (ts_singleton) std::cout << "0x" << ts_singleton << "\n";
    else std::cout << "not found\n";

    std::cout << "luau_execute: "; // ass resolver can be wrong
    if (luau_execute) std::cout << "0x" << luau_execute << "\n";
    else std::cout << "not found\n";

    std::cout << "luaD_throw: ";
    if (luaD_throw) std::cout << "0x" << luaD_throw << "\n";
    else std::cout << "not found\n";

    std::cout << "luaC_step: ";
    if (luaC_step) std::cout << "0x" << luaC_step << "\n";
    else std::cout << "not found\n";

    if (!version.empty()) {
        std::cout << "ver - " << version << "\n";
    }

    return 0;
}
