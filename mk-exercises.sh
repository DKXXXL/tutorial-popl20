#!/bin/bash
set -e

# config
REPLACE="perl -0pe"
REMOVEPRF_RE='s/\(\*\s*REMOVE\s*\*\)\s*Proof.\s*.*?\s*Qed\.\R/Proof. (* FILL IN YOUR PROOF *) Admitted.\n/gms'
REMOVE_RE='s/\(\*\s*REMOVE\s*\*\)\s*(.*?)\s*:=.*?\.\R/\1. (* FILL IN HERE *) Admitted.\n/gms'
STRONGHIDE_RE='s/\(\*\s*STRONGHIDE\s*\*\)\s*(.*?)\(\*\s*ENDSTRONGHIDE\s*\*\)\R?//gms'
HIDE_RE='s/\(\*\s*HIDE\s*\*\)\s*(.*?)\(\*\s*ENDHIDE\s*\*\)/Definition hole := remove_this_line.\n(* ANSWER THE QUESTION AND REMOVE THE LINE ABOVE *)/gms'
IMPORT_RE='s/^From solutions/From exercises/gms'

# run replacement on all source files
mkdir -p exercises
for FILE in solutions/*.v; do
    DST=exercises/"$(basename -s .v "$FILE").v"
    cat "$FILE" \
      | $REPLACE "$REMOVEPRF_RE" \
      | $REPLACE "$REMOVE_RE" \
      | $REPLACE "$STRONGHIDE_RE" \
      | $REPLACE "$HIDE_RE" \
      | $REPLACE "$IMPORT_RE" > "$DST"
done
