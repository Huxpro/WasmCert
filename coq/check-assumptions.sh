#!/bin/sh
# Check that the soundness theorem only relies on the abstract numeric
# operators of Int.v/Float.v and the opaque [byte]/[char] types, i.e.
# on no admitted lemma or other axiom.
set -e
cd "$(dirname "$0")"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > "$tmp/Assumptions.v" <<'COQ'
From Wasm Require Import Soundness.
Print Assumptions soundness.
Print Assumptions type_safety.
COQ

coqc -Q . Wasm "$tmp/Assumptions.v" > "$tmp/out.txt"

# Axiom lines look like "name : type"; types may continue on indented lines.
unexpected=$(grep -E '^[^ ].* : ' "$tmp/out.txt" \
  | grep -Ev '^((I32|I64|F32|F64)\.[A-Za-z0-9_]+|byte|char) : ' || true)

if [ -n "$unexpected" ]; then
  echo "Unexpected assumptions:"
  echo "$unexpected"
  exit 1
fi
echo "OK: soundness only assumes the abstract numeric operators."
