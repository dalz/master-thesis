import glob
import sys
import re

def argparser():
    if len(sys.argv) != 4:
        print("agregator needs 3 arguments: memory result folder, instruction result folder, file to write sinopsis to")
    return (sys.argv[1], sys.argv[2], sys.argv[3],)

def getFilenames(paths):
    return list(map(lambda filePath: filePath.rsplit('/', 1)[-1], paths))

def getLinenumber(s):
    r = r"last correct line: (\d+)"
    return str(re.search(r, s).group(1))

def createCSVEntry(f):
    contents  = open(f, "r").readline().strip()
    status  =  contents == "all correct"
    if not(status):
        return (False, "Failure" + ";" + getLinenumber(contents) + ";")
    else:
        return (True, "Success" + ";;")

def main():
    (memPath, instPath, resFileName) = argparser()
    resultFile = open(resFileName, "w")
    #setup header
    resultFile.write("testcase;memtestresult;lastcorrectLinenumberInRef;instTestResult;lastcorrectLinenumberInRef;\n")

    memFilePaths  = sorted(glob.glob(memPath + "*.out"))
    instFilePaths = sorted(glob.glob(instPath + "*.out"))

    if getFilenames(memFilePaths) != getFilenames(instFilePaths):
        print("somefiles are missing to do correct comparison")
        exit(255)

    #tuppel of a memfile and inst file so we can put them on the same line in the resulting csv
    filePairs = list(zip(memFilePaths, instFilePaths))

    #For simplel counting
    Total = 0
    memCorrect = 0
    instCorrect = 0

    for pair in filePairs:
        Total +=1

        #write tescasenumber for the entry
        resultFile.write(pair[0].rsplit('/', 1)[-1] + ";")

        #memory file analysis
        (memIsCorrect,csvVal) = createCSVEntry(pair[0])
        if memIsCorrect:
            memCorrect += 1
        resultFile.write(csvVal)

        #instruction file analysis
        (InstIsCorrect,csvVal) = createCSVEntry(pair[1])
        if InstIsCorrect:
            instCorrect += 1
        resultFile.write(csvVal)

        #entry is done
        resultFile.write("\n")
    
    print("Memorytrans Testing: " + str(memCorrect) + "/" + str(Total))
    print("Instruction Testing: " + str(instCorrect) + "/" + str(Total))

if __name__ =="__main__":
    main()
