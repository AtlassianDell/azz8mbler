import sys
import os
import argparse

onearg = {
    "NOP": "00",
    "RET": "C9"
}

twoarg = {
    "JP": "C3"
}

parser = argparse.ArgumentParser(description="AZZ8MBLER")
parser.add_argument("inp", help="Path to the input assembly file")                                                                          # args.inp
parser.add_argument("-o","--output", help="Path for the output binary file")                                                                # args.out
parser.add_argument("-t", "--type", help="8xp or 8xz for TI Basic File, uncompiled ASM and compiled respectively", default="")              # args.t
args = parser.parse_args()

infile = open(args.inp).read().split("\n")
outfile = open(args.output, "w")
# number.to_bytes(2, 'little'), "big"

labels = {}

print("Pass 1")
for i in range(len(infile)):
    if infile[i].strip().endswith(":"):
        name = infile[i][:-1]
        labels[name] = i
        print(f"Label Found: {name}")
        infile[i] = ""

print("Pass 2")
for i in range(len(infile)):
    curline = infile[i]
    cmd = curline.split(" ")[0].upper()
    try:
        arg1 = curline.split(" ")[1]
    except:
        pass
    if curline:
        if cmd in onearg:
            print(f"{cmd}: Valid")
            outfile.write(onearg[cmd])
        elif cmd in twoarg:
            print(f"{cmd}: Valid, arg1 {arg1}")
            outfile.write(twoarg[cmd])
            if arg1.startswith("$"):
                outfile.write(int(arg1[1:], 16).to_bytes(2,"little").hex())
            else:
                outfile.write(int(arg1, 16).to_bytes(2,"little").hex())
        else:
            print("Invalid opcode!")
            sys.exit(1)