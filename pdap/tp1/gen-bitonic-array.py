#!/usr/bin/env python3
import sys
import random

if (len(sys.argv) != 3):
    print("Usage: gen-bitonic-array [array-size] [array-file-name]", file = sys.stderr)
    exit(1)

arraySize = int(sys.argv[1])
arrayFileName = sys.argv[2]

file = open(arrayFileName, 'w')

#file.write('%d\n\n' % arraySize)

random.seed()
mult = 1
peak = random.randint(2, arraySize - 2)
curNo = random.randint(50, 60);
for i in range(0, arraySize):
    if i == peak:
        mult = -1;
    delta = mult * random.randint(0, 3)
    curNo = curNo + delta
    file.write(f"{curNo}\n")

file.close()

print(f'File created: {arrayFileName}')
