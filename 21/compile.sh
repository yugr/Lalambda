#!/bin/sh

set -eu
set -x

# Install marp from https://github.com/marp-team/marp-cli/releases

marp talk.md --pdf
