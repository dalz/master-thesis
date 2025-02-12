import re
import sys




r = r"\s*(0x[0-9A-Fa-f]+)\s+((0x)?[0-9A-Fa-f]+)"



def parseGroup(result):
    return (int(result.group(1),0),int(result.group(2) if result.group(2).startswith("0x") else "0x" + result.group(2) ,0))

def parse(line):
    res = re.search(r, line)
    if res == None:
        return None
    return parseGroup(re.search(r, line))

reference = open(sys.argv[1], "r")
selfimpel = open(sys.argv[2], "r")

line = 1

try:
    lsn = selfimpel.readline()
    lrn = reference.readline()
    while len(lrn) != 0:
        ls = parse(lsn)
        lr = parse(lrn)
        if lr == None:
            line += 1
            lrn = reference.readline()
            continue
        if ls == lr:
            lsn = selfimpel.readline()
            lrn = reference.readline()
            line += 1
        else:
            lsn = selfimpel.readline()
            if len(lsn) == 0:
                break
    if len(lrn) != 0:
        print("last correct line: " + str(line))
    else:
        print("all correct")
except:
    selfimpel.close()
    reference.close()
    print(lrn)
    exit(255)
finally:
    selfimpel.close()
    reference.close()