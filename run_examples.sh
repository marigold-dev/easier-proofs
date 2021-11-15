#!/bin/bash

for prog in examples/bool/props/*.properties
do
    printf "$prog : "
    leftPartFileName=$(echo $prog | cut -d'.' -f 1)
    rightPart=".v"
    res=$(./_build/default/bin/main.exe "$leftPartFileName$rightPart" < $prog)
done