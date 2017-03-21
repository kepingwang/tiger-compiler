end=49
for i in $(seq 1 $end);
do
wget "http://www.cs.princeton.edu/~appel/modern/testcases/test"${i}.tig
done
