#!/bin/sh

set -eu
set -x

# Install marp from https://github.com/marp-team/marp-cli/releases

cd $(dirname $0)

marp --pdf talk.md
