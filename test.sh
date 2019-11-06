#!/bin/bash

for file in test/*.ptt; do
  echo "Checking ${file}"
  dune exec ptt -- $file
  echo $'' # print newline ???
done

echo DONE
