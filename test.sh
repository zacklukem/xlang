#!/bin/bash

cargo build

if [ $? -ne 0 ]; then
    exit 1
fi

TMPFILE=$(mktemp)
trap 'rm -f "$TMPFILE"' EXIT

NUM_TESTS=$(find examples -name "*.x" | wc -l | tr -d ' ')
FAILED=0

echo -e "\nrunning $NUM_TESTS integration tests"

rm -rf examples/build

mkdir -p examples/build/compile_pass
mkdir -p examples/build/compile_fail

for file in $(find examples/compile_pass -name "*.x")
do
    filename=$(basename -s .x "$file")

    printf "test $file ... "
    target/debug/xlang $file examples/build/compile_pass/$filename > $TMPFILE 2>&1

    ERR=$?

    if [ $ERR -eq 0 ]; then
        printf "\033[32mtranslate\033[0m "
    elif [ $ERR -eq 101 ]; then
        FAILED=1
        echo -e "\033[31mTRANSLATE_PANIC\033[0m "
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
        continue
    else
        FAILED=1
        echo -e "\033[31mTRANSLATE_FAIL\033[0m "
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
        continue
    fi

    gcc examples/build/compile_pass/$filename.c stl/c/xlang/check.c \
          -o examples/build/compile_pass/$filename \
          -I stl/c \
          > $TMPFILE 2>&1

    ERR=$?

    if [ $ERR -eq 0 ]; then
        printf "\033[32mcompile\033[0m "
    else
        FAILED=1
        echo -e "\033[31mCOMPILE_FAIL\033[0m "
        echo "Failure:"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
        continue
    fi

    examples/build/compile_pass/$filename > $TMPFILE 2>&1

    ERR=$?

    if [ $ERR -eq 0 ]; then
        echo -e "\033[32mrun\033[0m"
    else
        FAILED=1
        echo -e "\033[31mRUN_FAIL\033[0m "
        echo "Failure ($ERR):"
        cat $TMPFILE | sed -e 's/^/    /g'
        echo
        continue
    fi
done

for file in $(find examples/compile_fail -name "*.x")
do
    filename=$(basename -s .x "$file")

    printf "test $file ... "
    target/debug/xlang $file examples/build/compile_fail/$filename > $TMPFILE 2>&1

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

exit $FAILED
