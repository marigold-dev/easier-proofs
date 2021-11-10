#!/bin/bash

for prog in examples/bool/props/*.properties
do
    printf "$prog : "
    res=$(dune exec -- easierproof < $prog)
    leftPartFileName=$(echo $prog | cut -d'.' -f 1)
    rightPart=".v"
    $(echo $res > "$leftPartFileName$rightPart")

done