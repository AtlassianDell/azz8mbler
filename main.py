import argparse
import sys
import struct
import re
import os

symbol_table = {}
included_files = set()
macros = {}
reg_map_8bit = {
    'B': 0b000, 'C': 0b001, 'D': 0b010, 'E': 0b011,
    'H': 0b100, 'L': 0b101, 'F': 0b110, 'A': 0b111,
}
reg_map_16bit = {
    'BC': 0b00, 'DE': 0b01, 'HL': 0b10, 'SP': 0b11
}
reg_map_16bit_push_pop = {
    'BC': 0b00, 'DE': 0b01, 'HL': 0b10, 'AF': 0b11
}
ix_iy_map = {'IX': 0xDD, 'IY': 0xFD}
ix_iy_reg_map = {'IXH': 0b100, 'IXL': 0b101, 'IYH': 0b100, 'IYL': 0b101}
rel_jump_cond_map = {
    'NZ': 0b000, 'Z': 0b001, 'NC': 0b010, 'C': 0b011
}
abs_jump_cond_map = {
    'NZ': 0b000, 'Z': 0b001, 'NC': 0b010, 'C': 0b011,
    'PO': 0b100, 'PE': 0b101, 'P': 0b110, 'M': 0b111
}

def parse_expr(expr, location_counter, pass_num):
    original_expr = expr.strip()
    expr_upper = original_expr.upper()
    if not original_expr:
        raise ValueError("Empty expression where a value was expected.")
    expr_with_lc = expr_upper.replace('#', str(location_counter))
    def resolve_part(match):
        part = match.group(0)
        if part.startswith('$'):
            return str(int(part[1:], 16))
        elif part.startswith('%'):
            return str(int(part[1:], 2))
        elif part.startswith("'") and part.endswith("'"):
            if len(part) == 3:
                return str(ord(part[1]))
            else:
                raise ValueError(f"Invalid character literal: {part}")
        elif part.isalpha() or '_' in part:
            if part in symbol_table:
                return str(symbol_table[part])
            else:
                if pass_num == 2:
                    raise ValueError(f"Undefined symbol: '{part}' in expression '{original_expr}'")
                return '0'
        return part
    resolved_expr = re.sub(r'\b[A-Z_][A-Z0-9_]*\b|\$[0-9A-F]+|%[01]+|\'[^\']\'', resolve_part, expr_with_lc)
    try:
        safe_eval_globals = {'__builtins__': None}
        return int(eval(resolved_expr, safe_eval_globals))
    except (NameError, TypeError, SyntaxError) as e:
        if pass_num == 2:
            raise ValueError(f"Error evaluating expression '{original_expr}' after symbol resolution: {e}. Resolved to: '{resolved_expr}'")
        return 0
    except Exception as e:
        raise ValueError(f"Unexpected error evaluating expression '{original_expr}': {e}. Resolved to: '{resolved_expr}'") from e

def get_opcode(mnemonic, operands, location_counter, pass_num):
    operands = operands.strip()
    mnemonic = mnemonic.upper()
    if mnemonic == 'LD':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 2:
            raise ValueError(f"LD requires two operands, got {len(parts)}.")
        dest, src = parts[0], parts[1]
        if dest in reg_map_8bit and src in reg_map_8bit:
            r = reg_map_8bit[dest]
            r_prime = reg_map_8bit[src]
            return [0b01000000 | (r << 3) | r_prime], 1
        if dest in reg_map_8bit:
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 2
            return [0b00000110 | (reg_map_8bit[dest] << 3), val & 0xFF], 2
        if dest in reg_map_8bit and src == '(HL)':
            return [0b01000110 | (reg_map_8bit[dest] << 3)], 1
        if dest == '(HL)' and src in reg_map_8bit:
            return [0b01110000 | reg_map_8bit[src]], 1
        if dest == '(HL)':
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 2
            return [0x36, val & 0xFF], 2
        if dest == 'A':
            if src == '(BC)': return [0x0A], 1
            if src == '(DE)': return [0x1A], 1
        if dest == '(BC)' and src == 'A': return [0x02], 1
        if dest == '(DE)' and src == 'A': return [0x12], 1
        if dest == 'A' and src.startswith('(') and src.endswith(')'):
            addr = parse_expr(src[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0x3A, addr & 0xFF, (addr >> 8) & 0xFF], 3
        if dest.startswith('(') and dest.endswith(')') and src == 'A':
            addr = parse_expr(dest[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0x32, addr & 0xFF, (addr >> 8) & 0xFF], 3
        if dest in reg_map_16bit:
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0x01 | (reg_map_16bit[dest] << 4), val & 0xFF, (val >> 8) & 0xFF], 3
        if dest in reg_map_16bit and src.startswith('(') and src.endswith(')'):
            addr = parse_expr(src[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [0xED, 0x4B | (reg_map_16bit[dest] << 4), addr & 0xFF, (addr >> 8) & 0xFF], 4
        if dest.startswith('(') and dest.endswith(')') and src in reg_map_16bit:
            addr = parse_expr(dest[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [0xED, 0x43 | (reg_map_16bit[src] << 4), addr & 0xFF, (addr >> 8) & 0xFF], 4
        if dest == 'SP' and src == 'HL': return [0xF9], 1
        if dest == 'SP' and src in ix_iy_map:
            return [ix_iy_map[src], 0xF9], 2
        m_ld_ix_iy_r = re.match(r'\((IX|IY)([+-]\d+)\)', src)
        if dest in reg_map_8bit and m_ld_ix_iy_r:
            idx_reg, disp_str = m_ld_ix_iy_r.groups()
            disp = int(disp_str)
            if pass_num == 1: return [], 3
            return [ix_iy_map[idx_reg], 0x46 | (reg_map_8bit[dest] << 3), disp & 0xFF], 3
        m_ld_ix_iy_r = re.match(r'\((IX|IY)([+-]\d+)\)', dest)
        if m:
            idx_reg, disp_str = m_ld_ix_iy_r.groups()
            disp = int(disp_str)
            if pass_num == 1: return [], 3
            return [ix_iy_map[idx_reg], 0x70 | reg_map_8bit[src], disp & 0xFF], 3
        m_ld_ix_iy_n = re.match(r'\((IX|IY)([+-]\d+)\)', dest)
        if m:
            idx_reg, disp_str = m_ld_ix_iy_n.groups()
            disp = int(disp_str)
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [ix_iy_map[idx_reg], 0x36, disp & 0xFF, val & 0xFF], 4
        if dest == 'I' and src == 'A': return [0xED, 0x47], 2
        if dest == 'R' and src == 'A': return [0xED, 0x4F], 2
        if dest == 'A' and src == 'I': return [0xED, 0x57], 2
        if dest == 'A' and src == 'R': return [0xED, 0x5F], 2
        if dest in ix_iy_map:
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [ix_iy_map[dest], 0x21, val & 0xFF, (val >> 8) & 0xFF], 4
        if dest in ix_iy_reg_map and src not in ix_iy_map:
            parent_reg = dest[:2]
            child_reg = dest[2]
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [ix_iy_map[parent_reg], 0b00000110 | (ix_iy_reg_map[dest] << 3), val & 0xFF], 3
        if dest in ix_iy_reg_map and src in ix_iy_reg_map:
            parent_reg = dest[:2]
            src_reg_val = ix_iy_reg_map[src]
            dest_reg_val = ix_iy_reg_map[dest]
            return [ix_iy_map[parent_reg], 0b01000000 | (dest_reg_val << 3) | src_reg_val], 2
    if mnemonic == 'EX':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 2: raise ValueError("EX requires two operands.")
        dest, src = parts[0], parts[1]
        if dest == 'DE' and src == 'HL': return [0xEB], 1
        if dest == 'AF' and src == 'AF\'': return [0x08], 1
        if dest == '(SP)' and src == 'HL': return [0xE3], 1
        if dest == '(SP)' and src == 'IX': return [0xDD, 0xE3], 2
        if dest == '(SP)' and src == 'IY': return [0xFD, 0xE3], 2
    if mnemonic in ['PUSH', 'POP']:
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 1: raise ValueError(f"{mnemonic} requires one operand.")
        reg = parts[0]
        if reg not in reg_map_16bit_push_pop: raise ValueError(f"Invalid register for {mnemonic}: {reg}")
        if mnemonic == 'PUSH':
            return [0xC5 | (reg_map_16bit_push_pop[reg] << 4)], 1
        else:
            return [0xC1 | (reg_map_16bit_push_pop[reg] << 4)], 1
    if mnemonic == 'JR':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
            addr = parse_expr(parts[0], location_counter, pass_num)
            if pass_num == 1: return [], 2
            offset = addr - (location_counter + 2)
            if not -128 <= offset <= 127: raise ValueError("JR offset out of range (-128 to 127)")
            return [0x18, offset & 0xFF], 2
        elif num_parts == 2:
            cond, addr_str = parts[0], parts[1]
            if cond not in rel_jump_cond_map: raise ValueError("Invalid condition for JR")
            addr = parse_expr(addr_str, location_counter, pass_num)
            if pass_num == 1: return [], 2
            offset = addr - (location_counter + 2)
            if not -128 <= offset <= 127: raise ValueError("JR offset out of range (-128 to 127)")
            return [0x20 | (rel_jump_cond_map[cond] << 3), offset & 0xFF], 2
    if mnemonic == 'JP':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
            if parts[0] == '(HL)': return [0xE9], 1
            if parts[0] == '(IX)': return [0xDD, 0xE9], 2
            if parts[0] == '(IY)': return [0xFD, 0xE9], 2
            addr = parse_expr(parts[0], location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0xC3, addr & 0xFF, (addr >> 8) & 0xFF], 3
        elif num_parts == 2:
            cond, addr_str = parts[0], parts[1]
            if cond not in abs_jump_cond_map: raise ValueError("Invalid condition for JP")
            addr = parse_expr(addr_str, location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0xC2 | (abs_jump_cond_map[cond] << 3), addr & 0xFF, (addr >> 8) & 0xFF], 3
    if mnemonic == 'CALL':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
            addr = parse_expr(parts[0], location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0xCD, addr & 0xFF, (addr >> 8) & 0xFF], 3
        elif num_parts == 2:
            cond, addr_str = parts[0], parts[1]
            if cond not in abs_jump_cond_map: raise ValueError("Invalid condition for CALL")
            addr = parse_expr(addr_str, location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0xC4 | (abs_jump_cond_map[cond] << 3), addr & 0xFF, (addr >> 8) & 0xFF], 3
    if mnemonic == 'RET':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 0 or operands == '':
            return [0xC9], 1
        elif num_parts == 1:
            cond = parts[0]
            if cond not in abs_jump_cond_map: raise ValueError("Invalid condition for RET")
            return [0xC0 | (abs_jump_cond_map[cond] << 3)], 1
    if mnemonic == 'RETI' and not operands: return [0xED, 0x4D], 2
    if mnemonic == 'RETN' and not operands: return [0xED, 0x45], 2
    if mnemonic == 'RST':
        addr = parse_expr(operands.strip(), location_counter, pass_num)
        if pass_num == 1: return [], 1
        valid_rst_addrs = [0x00, 0x08, 0x10, 0x18, 0x20, 0x28, 0x30, 0x38]
        if addr not in valid_rst_addrs:
            raise ValueError(f"Invalid restart address for RST: {hex(addr)}")
        opcode = 0xC7 | addr
        return [opcode], 1
    if mnemonic in ['ADD', 'SUB', 'ADC', 'SBC', 'AND', 'XOR', 'OR', 'CP']:
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) == 1:
            op = parts[0]
            op_base = {'ADD': 0x80, 'SUB': 0x90, 'ADC': 0x88, 'SBC': 0x98,
                       'AND': 0xA0, 'XOR': 0xA8, 'OR': 0xB0, 'CP': 0xB8}
            if op in reg_map_8bit:
                return [op_base[mnemonic] | reg_map_8bit[op]], 1
            elif op == '(HL)':
                return [op_base[mnemonic] | 0x06], 1
            elif op.startswith('(') and op.endswith(')'):
                m = re.match(r'\((IX|IY)([+-]\d+)\)', op)
                if m:
                    idx_reg, disp_str = m.groups()
                    disp = int(disp_str)
                    op_base = {'ADD': 0x86, 'SUB': 0x96, 'ADC': 0x8E, 'SBC': 0x9E,
                               'AND': 0xA6, 'XOR': 0xAE, 'OR': 0xB6, 'CP': 0xBE}
                    if pass_num == 1: return [], 3
                    return [ix_iy_map[idx_reg], op_base[mnemonic], disp & 0xFF], 3
            else:
                val = parse_expr(op, location_counter, pass_num)
                op_base = {'ADD': 0xC6, 'SUB': 0xD6, 'ADC': 0xCE, 'SBC': 0xDE,
                           'AND': 0xE6, 'XOR': 0xEE, 'OR': 0xF6, 'CP': 0xFE}
                if pass_num == 1: return [], 2
                return [op_base[mnemonic], val & 0xFF], 2
        elif len(parts) == 2:
            dest, src = parts[0], parts[1]
            if mnemonic == 'ADD' and dest == 'HL' and src in reg_map_16bit:
                return [0x09 | (reg_map_16bit[src] << 4)], 1
            if mnemonic == 'ADC' and dest == 'HL' and src in reg_map_16bit:
                return [0xED, 0x4A | (reg_map_16bit[src] << 4)], 2
            if mnemonic == 'SBC' and dest == 'HL' and src in reg_map_16bit:
                return [0xED, 0x42 | (reg_map_16bit[src] << 4)], 2
            if mnemonic == 'ADD' and dest in ix_iy_map and src in reg_map_16bit:
                return [ix_iy_map[dest], 0x09 | (reg_map_16bit[src] << 4)], 2
            raise ValueError(f"Invalid operands for {mnemonic}: {operands}")
    if mnemonic in ['INC', 'DEC']:
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 1: raise ValueError(f"{mnemonic} requires one operand.")
        reg = parts[0]
        if reg in reg_map_8bit:
            op_inc = 0b00000100 | (reg_map_8bit[reg] << 3)
            op_dec = 0b00000101 | (reg_map_8bit[reg] << 3)
            return [op_inc if mnemonic == 'INC' else op_dec], 1
        if reg in reg_map_16bit:
            op_inc = 0b00000011 | (reg_map_16bit[reg] << 4)
            op_dec = 0b00001011 | (reg_map_16bit[reg] << 4)
            return [op_inc if mnemonic == 'INC' else op_dec], 1
        m = re.match(r'\((IX|IY)([+-]\d+)\)', reg)
        if m:
            idx_reg, disp_str = m.groups()
            disp = int(disp_str)
            op_inc = 0x34
            op_dec = 0x35
            if pass_num == 1: return [], 3
            return [ix_iy_map[idx_reg], op_inc if mnemonic == 'INC' else op_dec, disp & 0xFF], 3
    if mnemonic in ['RLC', 'RRC', 'RL', 'RR', 'SLA', 'SRA', 'SLL', 'SRL']:
        op_map = {'RLC': 0x00, 'RRC': 0x08, 'RL': 0x10, 'RR': 0x18, 'SLA': 0x20, 'SRA': 0x28, 'SLL': 0x30, 'SRL': 0x38}
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 1: raise ValueError(f"{mnemonic} requires one operand.")
        op = parts[0]
        if op in reg_map_8bit:
            return [0xCB, op_map[mnemonic] | reg_map_8bit[op]], 2
        elif op == '(HL)':
            return [0xCB, op_map[mnemonic] | 0x06], 2
        else:
            m = re.match(r'\((IX|IY)([+-]\d+)\)', op)
            if m:
                idx_reg, disp_str = m.groups()
                disp = int(disp_str)
                if pass_num == 1: return [], 4
                return [ix_iy_map[idx_reg], 0xCB, disp & 0xFF, op_map[mnemonic] | 0x06], 4
    if mnemonic in ['BIT', 'RES', 'SET']:
        op_map = {'BIT': 0x40, 'RES': 0x80, 'SET': 0xC0}
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 2: raise ValueError(f"{mnemonic} requires two operands.")
        bit, op = parts[0], parts[1]
        bit_val = parse_expr(bit, location_counter, pass_num)
        if not (0 <= bit_val <= 7): raise ValueError("Bit number must be 0-7.")
        if op in reg_map_8bit:
            return [0xCB, op_map[mnemonic] | (bit_val << 3) | reg_map_8bit[op]], 2
        elif op == '(HL)':
            return [0xCB, op_map[mnemonic] | (bit_val << 3) | 0x06], 2
        else:
            m = re.match(r'\((IX|IY)([+-]\d+)\)', op)
            if m:
                idx_reg, disp_str = m.groups()
                disp = int(disp_str)
                if pass_num == 1: return [], 4
                return [ix_iy_map[idx_reg], 0xCB, disp & 0xFF, op_map[mnemonic] | (bit_val << 3) | 0x06], 4
    if mnemonic == 'IN':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 2: raise ValueError("IN requires two operands.")
        dest, src = parts[0], parts[1]
        if dest == 'A' and src.startswith('(') and src.endswith(')'):
            port = parse_expr(src[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 2
            return [0xDB, port & 0xFF], 2
        if dest in reg_map_8bit and src == '(C)':
            return [0xED, 0b01000000 | (reg_map_8bit[dest] << 3)], 2
        raise ValueError("Invalid operands for IN.")
    if mnemonic == 'OUT':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) != 2: raise ValueError("OUT requires two operands.")
        dest, src = parts[0], parts[1]
        if dest.startswith('(') and dest.endswith(')') and src == 'A':
            port = parse_expr(dest[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 2
            return [0xD3, port & 0xFF], 2
        if dest == '(C)' and src in reg_map_8bit:
            return [0xED, 0b01000001 | (reg_map_8bit[src] << 3)], 2
        raise ValueError("Invalid operands for OUT.")
    if mnemonic == 'LDI' and not operands: return [0xED, 0xA0], 2
    if mnemonic == 'LDIR' and not operands: return [0xED, 0xB0], 2
    if mnemonic == 'LDD' and not operands: return [0xED, 0xA8], 2
    if mnemonic == 'LDDR' and not operands: return [0xED, 0xB8], 2
    if mnemonic == 'CPI' and not operands: return [0xED, 0xA1], 2
    if mnemonic == 'CPIR' and not operands: return [0xED, 0xB1], 2
    if mnemonic == 'CPD' and not operands: return [0xED, 0xA9], 2
    if mnemonic == 'CPDR' and not operands: return [0xED, 0xB9], 2
    if mnemonic == 'INI' and not operands: return [0xED, 0xA2], 2
    if mnemonic == 'INIR' and not operands: return [0xED, 0xB2], 2
    if mnemonic == 'IND' and not operands: return [0xED, 0xAA], 2
    if mnemonic == 'INDR' and not operands: return [0xED, 0xBA], 2
    if mnemonic == 'OUTI' and not operands: return [0xED, 0xA3], 2
    if mnemonic == 'OTIR' and not operands: return [0xED, 0xB3], 2
    if mnemonic == 'OUTD' and not operands: return [0xED, 0xAB], 2
    if mnemonic == 'OTDR' and not operands: return [0xED, 0xBB], 2
    if mnemonic == 'DI' and not operands: return [0xF3], 1
    if mnemonic == 'EI' and not operands: return [0xFB], 1
    if mnemonic == 'NOP' and not operands: return [0x00], 1
    if mnemonic == 'HALT' and not operands: return [0x76], 1
    if mnemonic == 'EXX' and not operands: return [0xD9], 1
    if mnemonic == 'DAA' and not operands: return [0x27], 1
    if mnemonic == 'CPL' and not operands: return [0x2F], 1
    if mnemonic == 'NEG' and not operands: return [0xED, 0x44], 2
    if mnemonic == 'RLD' and not operands: return [0xED, 0x6F], 2
    if mnemonic == 'RRD' and not operands: return [0xED, 0x67], 2
    if mnemonic == 'SCF' and not operands: return [0x37], 1
    if mnemonic == 'CCF' and not operands: return [0x3F], 1
    if mnemonic == 'IM' and not operands:
        if operands == '0': return [0xED, 0x46], 2
        if operands == '1': return [0xED, 0x56], 2
        if operands == '2': return [0xED, 0x5E], 2
        raise ValueError("Invalid interrupt mode (must be 0, 1, or 2).")
    raise ValueError(f"Unknown mnemonic or invalid operands: {mnemonic} {operands}")

def assemble(source_code, pass_num=1, current_dir='.'):
    global symbol_table, macros
    lines = source_code.splitlines()
    location_counter = 0
    assembled_code = []
    in_macro_def = False
    macro_def_name = None
    macro_def_args = []
    current_macro_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        original_line = line
        line = line.strip()
        if ';' in line:
            line = line[:line.find(';')]
        if not line:
            i += 1
            continue
        parts = re.split(r'\s+', line, maxsplit=2)
        label, mnemonic, operands = None, None, ''
        first_word = parts[0].upper()
        if first_word == 'MACRO':
            if in_macro_def:
                raise ValueError(f"Nested macros are not supported. Found 'MACRO' inside a macro definition on line {i + 1}.")
            macro_def_parts = parts[1:]
            macro_def_name = macro_def_parts[0].upper()
            if len(macro_def_parts) > 1:
                arg_string = macro_def_parts[1].upper().strip()
                if arg_string.endswith(':'):
                    arg_string = arg_string[:-1]
                macro_def_args = [arg.strip() for arg in arg_string.split(',')]
            else:
                macro_def_args = []
            in_macro_def = True
            current_macro_lines = []
            i += 1
            continue
        elif first_word == 'ENDMACRO':
            if not in_macro_def:
                raise ValueError(f"ENDMACRO without a preceding MACRO on line {i + 1}.")
            if pass_num == 1 and macro_def_name in macros:
                raise ValueError(f"Duplicate macro definition: {macro_def_name} on line {i + 1}")
            macros[macro_def_name] = {
                'args': macro_def_args,
                'body': current_macro_lines
            }
            in_macro_def = False
            macro_def_name = None
            macro_def_args = []
            current_macro_lines = []
            i += 1
            continue
        if in_macro_def:
            current_macro_lines.append(original_line)
            i += 1
            continue
        if first_word.endswith(':'):
            label = first_word[:-1]
            if len(parts) > 1:
                mnemonic = parts[1].upper()
                if len(parts) > 2:
                    operands = ' '.join(parts[2:])
            else:
                if pass_num == 1:
                    if label in symbol_table:
                        raise ValueError(f"Duplicate label: {label} on line {i + 1}")
                    symbol_table[label] = location_counter
                i += 1
                continue
        else:
            pseudo_ops_with_label = ['EQU', 'ORG']
            if len(parts) > 1 and parts[1].upper() in pseudo_ops_with_label:
                label = first_word
                mnemonic = parts[1].upper()
                if len(parts) > 2:
                    operands = ' '.join(parts[2:])
            else:
                mnemonic = first_word.upper()
                if len(parts) > 1:
                    operands = ' '.join(parts[1:])
        if mnemonic in macros:
            macro_info = macros[mnemonic]
            call_args = [arg.strip().upper() for arg in operands.split(',')] if operands else []
            if len(call_args) != len(macro_info['args']):
                raise ValueError(f"Macro '{mnemonic}' called with {len(call_args)} arguments, but defined with {len(macro_info['args'])} on line {i + 1}.")
            arg_map = {f"ARG:{arg_name.upper()}": arg_value for arg_name, arg_value in zip(macro_info['args'], call_args)}
            expanded_lines = []
            for macro_line in macro_info['body']:
                expanded_line = macro_line.upper()
                for arg_token, arg_value in arg_map.items():
                    expanded_line = expanded_line.replace(arg_token, arg_value)
                expanded_lines.append(expanded_line)
            lines = lines[:i] + expanded_lines + lines[i+1:]
            i -= 1
            continue
        if label:
            label = label.upper()
        if mnemonic:
            mnemonic = mnemonic.upper()
        if operands:
            operands = operands.upper()
        if mnemonic == 'INCLUDE':
            if not operands:
                raise ValueError("INCLUDE directive requires a filename.")
            file_match = re.match(r'^["\'](.+)["\']$', operands)
            if not file_match:
                raise ValueError("INCLUDE filename must be a quoted string.")
            filename = file_match.group(1)
            filepath = os.path.join(current_dir, filename)
            if filepath in included_files:
                raise ValueError(f"Circular include detected: {filepath}")
            included_files.add(filepath)
            try:
                with open(filepath, 'r') as f:
                    included_source = f.read()
                included_lines = included_source.splitlines()
                lines = lines[:i+1] + included_lines + lines[i+1:]
                i += 1
                included_files.remove(filepath)
            except FileNotFoundError:
                included_files.remove(filepath)
                raise FileNotFoundError(f"Included file not found: {filepath}")
            except Exception as e:
                included_files.remove(filepath)
                raise e
            continue
        if pass_num == 1 and label and not mnemonic in ['EQU', 'ORG']:
            if label in symbol_table:
                raise ValueError(f"Duplicate label: {label} on line {i + 1}")
            symbol_table[label] = location_counter
        if mnemonic == 'EQU' and label:
            value = parse_expr(operands, location_counter, pass_num)
            if pass_num == 1:
                symbol_table[label] = value
        elif mnemonic == 'ORG':
            value = parse_expr(operands, location_counter, pass_num)
            if pass_num == 1:
                location_counter = value
            elif pass_num == 2:
                if value > location_counter:
                    assembled_code.extend([0x00] * (value - location_counter))
                location_counter = value
        elif mnemonic == 'DB' or mnemonic == 'DEFB':
            items = re.split(r',(?=(?:[^"]*"[^"]*")*[^"]*$)', operands)
            items = [item.strip() for item in items]
            for item in items:
                if item.startswith('"') and item.endswith('"'):
                    string_val = item.strip('"')
                    values = [ord(c) for c in string_val]
                    location_counter += len(values)
                    if pass_num == 2:
                        assembled_code.extend(values)
                else:
                    value = parse_expr(item, location_counter, pass_num)
                    location_counter += 1
                    if pass_num == 2:
                        assembled_code.append(value & 0xFF)
        elif mnemonic == 'DW' or mnemonic == 'DEFW':
            values = [parse_expr(v, location_counter, pass_num) for v in operands.split(',')]
            location_counter += len(values) * 2
            if pass_num == 2:
                for v in values:
                    assembled_code.extend([v & 0xFF, (v >> 8) & 0xFF])
        elif mnemonic == 'DEFM':
            if operands.startswith('"') and operands.endswith('"'):
                string_val = operands.strip('"')
                values = [ord(c) for c in string_val]
                location_counter += len(values)
                if pass_num == 2:
                    assembled_code.extend(values)
            else:
                raise ValueError("DEFM requires a quoted string operand.")
        elif mnemonic == 'DEFS':
            parts = [p.strip() for p in operands.split(',')]
            size = parse_expr(parts[0], location_counter, pass_num)
            fill_value = 0x00
            if len(parts) > 1:
                fill_value = parse_expr(parts[1], location_counter, pass_num)
            location_counter += size
            if pass_num == 2:
                assembled_code.extend([fill_value & 0xFF] * size)
        elif mnemonic:
            try:
                opcodes, size = get_opcode(mnemonic, operands, location_counter, pass_num)
                location_counter += size
                if pass_num == 2:
                    assembled_code.extend(opcodes)
            except Exception as e:
                print(f"Error on line {i + 1}: '{line}'", file=sys.stderr)
                raise e
        i += 1
    if pass_num == 1:
        return location_counter
    else:
        return assembled_code

def main():
    parser = argparse.ArgumentParser(description="A Z80 Assembler")
    parser.add_argument("infile", help="Input assembly file (.asm)")
    parser.add_argument("-o", "--outfile", help="Output machine code file (.bin)", required=True)
    parser.add_argument("-t", "--plaintext", action="store_true", help="Output hex as plaintext")
    args = parser.parse_args()
    try:
        with open(args.infile, 'r') as f:
            source_code = f.read()
        print("Pass 1")
        symbol_table.clear()
        included_files.clear()
        try:
            assemble(source_code, pass_num=1, current_dir=os.path.dirname(args.infile) or '.')
        except ValueError as e:
            print(f"Error during Pass 1: {e}", file=sys.stderr)
            sys.exit(1)
        print("Pass 2")
        included_files.clear()
        try:
            machine_code = assemble(source_code, pass_num=2, current_dir=os.path.dirname(args.infile) or '.')
        except ValueError as e:
            print(f"Error during Pass 2: {e}", file=sys.stderr)
            sys.exit(1)
        with open(args.outfile, 'wb' if not args.plaintext else 'w') as f:
            if args.plaintext:
                hex_string = "".join(f"{b:02X}" for b in machine_code)
                f.write(hex_string)
                print(f"Done")
            else:
                f.write(bytes(machine_code))
                print(f"Done")
    except FileNotFoundError:
        print(f"Error: Input file not found at '{args.infile}'", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
