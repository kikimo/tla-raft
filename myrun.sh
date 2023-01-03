#!/bin/bash

java -Xms4g -Xmx12g -jar tla2tools.jar -deadlock -workers 4 -config Raft.cfg Raft.tla $@ 2>&1 | tee raft.log

