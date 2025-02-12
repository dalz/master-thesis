import re
import sys

r = r"memory:\s*(0x[0-9A-Fa-f]+)\s*-(GET|PUT):.*\[(0x[0-9A-Fa-f]+)\]\.(8|16)\s*(->|<-)\s*(0x[0-9A-Fa-f]+|0)"

def parseGroup(result):
    return (int(result.group(1),0),result.group(2),int(result.group(3),0),int(result.group(4),0),int(result.group(6),0))

def parse(line):
    return parseGroup(re.search(r, line))

reference = open(sys.argv[1], "r")
selfimpel = open(sys.argv[2], "r")

line = 0

try:
    lsn = selfimpel.readline()
    lrn = reference.readline()
    while len(lrn) != 0:
        if len(lsn) == 0:
                break
        ls = parse(lsn)
        lr = parse(lrn)
        if ls == lr:
            lsn = selfimpel.readline()
            lrn = reference.readline()
            line += 1
        else:
            lsn = selfimpel.readline()
    if len(lrn) != 0:
        print("last correct line: " + str(line))
    else:
        print("all correct")

except Exception as e:
    print(e)
    print(lsn)
    print(lrn)
    selfimpel.close()
    reference.close()
    exit(255)
finally:
    selfimpel.close()
    reference.close()