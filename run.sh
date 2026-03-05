#!/bin/sh
cbmc --compact-trace --no-pointer-check --no-undefined-shift-check --no-signed-overflow-check ./reg_deduce_bounds-compare.c
