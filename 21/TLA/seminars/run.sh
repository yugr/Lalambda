#!/bin/sh

set -eu
set -x

for f in *.tla; do
  time ../tlc $f
done
