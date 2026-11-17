#!/bin/bash
. ~/.profile
shopt -s expand_aliases

time nlately verify --isolate-assertions --cores=6 --verification-time-limit=7  Ownership-Dunno.dfy  --progress=batch  --filter-symbol=CLONING_PRESERVES_OWNERSHIP

