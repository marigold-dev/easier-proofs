#!/bin/bash

for prog in examples/bool/props/*
do
    printf "$prog : "
    res=$(dune exec -- easierproof < $prog)
    printf "output : \n \e[42m $res \e[0m \n"

done