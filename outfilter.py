import sys
exit_code = 0
line = sys.stdin.readline()
while line:
    if (not line.startswith("[") and
       not line.startswith("Standard ML") and
       not line.startswith("- [autoloading")):
       sys.stdout.write(line)
    if line.find("syntax error") >= 0:
        print("test failure detected!")
        exit_code = 1
    if line.find("unbound structure") >= 0:
        print("compile failure detected!")
        exit_code = 2
    if line.find("ERROR FOUND") >= 0:
        print("Tiger doesn't compile")
        exit_code = 3
    if line.find("raised at") >= 0:
        print("Exception happened")
        exit_code = 4
    line = sys.stdin.readline()
sys.exit(exit_code)
