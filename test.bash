#!/bin/bash

set -e
set -x

output_filename='test.html'
pid_filename='pen.pid'

./pen -p "$pid_filename" -S 1 8888 savannah.nongnu.org:80

while [ ! -e "$pid_filename" ]
do
    sleep .1
done

clean()
{
    rm -f "$output_filename"

    pen_pid=$(cat "$pid_filename")
    kill "$pen_pid"
}
trap clean EXIT

curl -o "$output_filename" http://127.0.0.1:8888
grep -q GNU "$output_filename"

echo -e '\x1b[01;32mOkay\x1b[0m'
