import argparse
import sys
import struct
import re

symbol_table = {}

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
ix_iy_map = {'IX': 0b11011101, 'IY': 0b11111101}
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
    
    if mnemonic == 'LD':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts != 2: raise ValueError("LD requires two operands.")
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
            if src.startswith('(') and src.endswith(')'):
                addr = parse_expr(src[1:-1], location_counter, pass_num)
                if pass_num == 1: return [], 3
                return [0x3A, addr & 0xFF, (addr >> 8) & 0xFF], 3

        if dest.startswith('(') and dest.endswith(')') and src == 'A':
            addr = parse_expr(dest[1:-1], location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0x32, addr & 0xFF, (addr >> 8) & 0xFF], 3

        if dest == '(BC)' and src == 'A': return [0x02], 1
        if dest == '(DE)' and src == 'A': return [0x12], 1

        if dest in reg_map_16bit and not dest in ['IX', 'IY']:
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 3
            return [0x01 | (reg_map_16bit[dest] << 4), val & 0xFF, (val >> 8) & 0xFF], 3

        if dest in ix_iy_map:
            val = parse_expr(src, location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [ix_iy_map[dest], 0x21, val & 0xFF, (val >> 8) & 0xFF], 4

        if dest.startswith('(') and dest.endswith(')'):
            if src in reg_map_16bit:
                addr = parse_expr(dest[1:-1], location_counter, pass_num)
                if pass_num == 1: return [], 3
                return [0xED, 0x43 | (reg_map_16bit[src] << 4), addr & 0xFF, (addr >> 8) & 0xFF], 4
        
        if dest == 'SP':
            if src == 'HL': return [0xF9], 1
            if src == 'IX': return [0xDD, 0xF9], 2
            if src == 'IY': return [0xFD, 0xF9], 2

    if mnemonic == 'JR':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
            addr = parse_expr(parts[0], location_counter, pass_num)
            if pass_num == 1: return [], 2
            offset = addr - (location_counter + 2)
            if not -128 <= offset <= 127: raise ValueError("JR offset out of range")
            return [0x18, offset & 0xFF], 2
        elif num_parts == 2:
            cond, addr_str = parts[0], parts[1]
            if cond not in rel_jump_cond_map: raise ValueError("Invalid condition for JR")
            addr = parse_expr(addr_str, location_counter, pass_num)
            if pass_num == 1: return [], 2
            offset = addr - (location_counter + 2)
            if not -128 <= offset <= 127: raise ValueError("JR offset out of range")
            return [0x20 | (rel_jump_cond_map[cond] << 3), offset & 0xFF], 2

    if mnemonic == 'JP':
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
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
        if not operands.strip():
            return [0xC9], 1
        else:
            parts = [p.strip().upper() for p in operands.split(',')]
            if len(parts) != 1: raise ValueError("RET with condition requires one operand.")
            cond = parts[0]
            if cond not in abs_jump_cond_map: raise ValueError("Invalid condition for RET")
            return [0xC0 | (abs_jump_cond_map[cond] << 3)], 1
    
    if mnemonic in ['PUSH', 'POP']:
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts != 1: raise ValueError(f"{mnemonic} requires one operand.")
        reg = parts[0]
        if reg not in reg_map_16bit_push_pop: raise ValueError(f"Invalid register for {mnemonic}: {reg}")
        
        if mnemonic == 'PUSH':
            return [0xC5 | (reg_map_16bit_push_pop[reg] << 4)], 1
        else:
            return [0xC1 | (reg_map_16bit_push_pop[reg] << 4)], 1
    
    if mnemonic == 'EXX' and not operands.strip():
        return [0xD9], 1

    if mnemonic == 'DAA' and not operands.strip():
        return [0x27], 1
    
    if mnemonic == 'CPL' and not operands.strip():
        return [0x2F], 1

    if mnemonic in ['INC', 'DEC']:
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts != 1: raise ValueError(f"{mnemonic} requires one operand.")
        reg = parts[0]
        if reg in reg_map_8bit:
            op_inc = 0b00000100 | (reg_map_8bit[reg] << 3)
            op_dec = 0b00000101 | (reg_map_8bit[reg] << 3)
            return [op_inc if mnemonic == 'INC' else op_dec], 1

    if mnemonic in ['INC', 'DEC']:
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts != 1: raise ValueError(f"{mnemonic} requires one operand.")
        reg = parts[0]
        if reg in reg_map_16bit:
            op_inc = 0b00000011 | (reg_map_16bit[reg] << 4)
            op_dec = 0b00001011 | (reg_map_16bit[reg] << 4)
            return [op_inc if mnemonic == 'INC' else op_dec], 1

    if mnemonic in ['AND', 'OR', 'XOR', 'CP', 'ADD', 'SUB', 'ADC', 'SBC']:
        parts = [p.strip().upper() for p in operands.split(',')]
        num_parts = len(parts)
        if num_parts == 1:
            op = parts[0]
            if op in reg_map_8bit:
                op_base = {'AND': 0xA0, 'XOR': 0xA8, 'OR': 0xB0, 'CP': 0xB8,
                           'ADD': 0x80, 'SUB': 0x90, 'ADC': 0x88, 'SBC': 0x98}
                return [op_base[mnemonic] | reg_map_8bit[op]], 1
            elif op == '(HL)':
                op_base = {'AND': 0xA6, 'XOR': 0xAE, 'OR': 0xB6, 'CP': 0xBE,
                           'ADD': 0x86, 'SUB': 0x96, 'ADC': 0x8E, 'SBC': 0x9E}
                if mnemonic in op_base:
                    return [op_base[mnemonic]], 1
                else:
                    val = parse_expr(op, location_counter, pass_num)
                    if pass_num == 1: return [], 2
                    op_base = {'AND': 0xE6, 'XOR': 0xEE, 'OR': 0xF6, 'CP': 0xFE,
                               'ADD': 0xC6, 'SUB': 0xD6, 'ADC': 0xCE, 'SBC': 0xDE}
                    return [op_base[mnemonic], val & 0xFF], 2
        elif num_parts == 2:
            dest, src = parts[0], parts[1]
            if mnemonic == 'ADD' and dest == 'HL' and src in reg_map_16bit:
                if src in reg_map_16bit:
                    return [0x09 | (reg_map_16bit[src] << 4)], 1
            else:
                raise ValueError(f"Invalid operands for {mnemonic}: {operands}")

    if mnemonic == 'RST':
        if not operands.strip(): raise ValueError("RST requires an operand.")
        addr = parse_expr(operands.strip(), location_counter, pass_num)
        if pass_num == 1:
            return [], 1
        
        valid_rst_addrs = [0x00, 0x08, 0x10, 0x18, 0x20, 0x28, 0x30, 0x38]
        if addr not in valid_rst_addrs:
            raise ValueError(f"Invalid restart address for RST: {hex(addr)}")
        
        opcode = 0xC7 | addr
        return [opcode], 1

    if mnemonic in ['DI', 'EI']:
        if operands.strip(): raise ValueError(f"{mnemonic} does not take operands.")
        if mnemonic == 'DI': return [0xF3], 1
        if mnemonic == 'EI': return [0xFB], 1
        
    if mnemonic == 'NOP' and not operands.strip(): return [0x00], 1
    
    if mnemonic == 'HALT' and not operands.strip(): return [0x76], 1
    
    if mnemonic == 'LD':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) == 2 and parts[0] == 'IY':
            val = parse_expr(parts[1], location_counter, pass_num)
            if pass_num == 1: return [], 4
            return [0xFD, 0x21, val & 0xFF, (val >> 8) & 0xFF], 4

    if mnemonic == 'LD':
        parts = [p.strip().upper() for p in operands.split(',')]
        if len(parts) == 2 and parts[1].startswith('(') and parts[1].endswith(')'):
            reg = parts[1][1:-1]
            if '+' in reg or '-' in reg:
                m = re.match(r'(IX|IY)([+-]\d+)', reg)
                if m:
                    idx_reg = m.group(1)
                    disp = int(m.group(2))
                    val = parse_expr(parts[0], location_counter, pass_num)
                    if pass_num == 1: return [], 4
                    return [ix_iy_map[idx_reg], 0x36, disp & 0xFF, val & 0xFF], 4
    
    raise ValueError(f"Unknown mnemonic or invalid operands: {mnemonic} {operands}")

def assemble(source_code, pass_num=1):
    global symbol_table
    lines = source_code.splitlines()
    location_counter = 0
    assembled_code = []

    for line_num, line in enumerate(lines):
        line = line.strip()
        if ';' in line:
            line = line[:line.find(';')]
        if not line:
            continue
            
        line_match = re.match(r'^\s*(?:(\w+):)?\s*(?:(\w+))?\s*(.*)$', line, re.IGNORECASE)
        if not line_match:
            continue
        
        label, mnemonic, operands = line_match.groups()
        
        if label:
            label = label.upper()
        if mnemonic:
            mnemonic = mnemonic.upper()
        if operands:
            operands = operands.strip()
        
        if pass_num == 1 and label:
            if label in symbol_table:
                raise ValueError(f"Duplicate label: {label} on line {line_num + 1}")
            symbol_table[label] = location_counter
        
        if mnemonic == 'DB':
            items = []
            current_item = ""
            in_quote = False
            for char in operands:
                if char == '"':
                    in_quote = not in_quote
                if char == ',' and not in_quote:
                    items.append(current_item.strip())
                    current_item = ""
                else:
                    current_item += char
            items.append(current_item.strip())

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
        elif mnemonic == 'DW':
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
        elif mnemonic == 'EQU' and label:
            value = parse_expr(operands, location_counter, pass_num)
            if pass_num == 1:
                symbol_table[label] = value
        elif mnemonic:
            try:
                opcodes, size = get_opcode(mnemonic, operands, location_counter, pass_num)
                location_counter += size
                if pass_num == 2:
                    assembled_code.extend(opcodes)
            except Exception as e:
                print(f"Error on line {line_num + 1}: '{line}'", file=sys.stderr)
                raise e

    if pass_num == 1:
        return location_counter
    else:
        return assembled_code

def main():
    parser = argparse.ArgumentParser(description="A Z80 Assembler.")
    parser.add_argument("infile", help="Input assembly file (.asm)")
    parser.add_argument("-o", "--outfile", help="Output machine code file (.bin)", required=True)
    parser.add_argument("-t", "--plaintext", action="store_true", help="Output hex as plaintext")
    
    args = parser.parse_args()

    try:
        with open(args.infile, 'r') as f:
            source_code = f.read()

        print("Pass 1: Building symbol table...")
        symbol_table.clear()
        try:
            assemble(source_code, pass_num=1)
        except ValueError as e:
            print(f"Error during Pass 1: {e}", file=sys.stderr)
            sys.exit(1)
        
        print("Pass 2: Generating machine code...")
        try:
            machine_code = assemble(source_code, pass_num=2)
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
