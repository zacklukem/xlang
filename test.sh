#!/bin/bash

cargo build

TMPFILE=$(mktemp)
trap 'rm -f "$TMPFILE"' EXIT

NUM_TESTS=$(find examples -name "*.x" | wc -l | tr -d ' ')
FAILED=0

echo -e "\nrunning $NUM_TESTS integration tests"

for file in $(find examples/compile_pass -name "*.x")
do
    printf "test $file ... "
    target/debug/xlang $file > $TMPFILE 2>&1

    ERR=$?

    if [ $ERR -eq 0 ]; then
        echo -e "\033[32mok\033[0m"
    elif [ $ERR -eq 101 ]; then
        FAILED=1
        echo -e "\033[31mPANIC\033[0m"
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
    else
        FAILED=1
        echo -e "\033[31mFAIL\033[0m"
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
    fi
done

for file in $(find examples/compile_fail -name "*.x")
do
    printf "test $file ... "
    target/debug/xlang $file > $TMPFILE 2>&1

    ERR=$?

    if [ $ERR -eq 1 ]; then # Compile fail is always 1
        echo -e "\033[32mok\033[0m"
    elif [ $ERR -eq 101 ]; then
        FAILED=1
        echo -e "\033[31mPANIC\033[0m"
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
    else
        FAILED=1
        echo -e "\033[31mFAIL\033[0m"
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
    fi
done

printf "test result: "

if [ $FAILED -eq 0 ]; then
    echo -e "\033[32mok\033[0m."
else
    FAILED=1
    echo -e "\033[31mFAIL\033[0m."
fi

echo
