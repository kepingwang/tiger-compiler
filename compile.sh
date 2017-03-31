#!/bin/bash

testlist=$(ls $1)
echo $testlist
for file in $testlist;
do
echo
echo
echo vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
echo testing $file
if test -z $2; then
    cat $file
    echo -----------------------------------------------
    sed "s:\$1:$file:g" main_template.sml | sml | python3 outfilter.py
    ret=$?
else
    sed "s:\$1:$file:g" main_template.sml | sml | python3 outfilter.py
    ret=$?
fi
echo ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
echo
echo
if test $ret -ne 0; then
    echo testing aborted due to a failed test.
    break
fi
done

