#!/bin/sh
# Check that the development makes no assumptions of its own:
#
#  1. The main theorems depend on no axiom besides the classical real
#     number axioms of Coq's standard library, which Flocq uses for its
#     IEEE 754 floats.
#  2. No source file (other than the vendored Lib/) leaves a proof
#     unfinished or declares an axiom. Parameters are only allowed as
#     fields of a Module Type, where they declare an interface.
set -e
cd "$(dirname "$0")"

status=0

# ---------------------------------------------------------------------
# 1. Print Assumptions

allowed='
ClassicalDedekindReals.sig_forall_dec
ClassicalDedekindReals.sig_not_dec
Classical_Prop.classic
FunctionalExtensionality.functional_extensionality_dep
'

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat > "$tmp/Assumptions.v" <<'COQ'
From Wasm Require Import Soundness.
Print Assumptions soundness.
Print Assumptions type_safety.
Print Assumptions preservation__toplevel.
Print Assumptions progress.
COQ

coqc -Q . Wasm "$tmp/Assumptions.v" > "$tmp/out.txt"

# Each assumption starts at column 0 with its name; its type may follow
# on the same line or on indented continuation lines.
grep -E '^[^[:space:]]' "$tmp/out.txt" \
  | grep -Ev '^(Axioms:|Closed under the global context)' \
  | sed -E 's/[[:space:]].*//' | sort -u > "$tmp/names.txt"

for name in $(cat "$tmp/names.txt"); do
  if ! printf '%s\n' "$allowed" | grep -qx "$name"; then
    echo "Unexpected assumption: $name"
    status=1
  fi
done

# ---------------------------------------------------------------------
# 2. Sources

for f in $(sed -n 's/^\([A-Za-z].*\.v\)$/\1/p' _CoqProject | grep -v '^Lib/'); do
  awk -v file="$f" '
    { line = $0; sub(/\(\*.*\*\)/, "", line) }
    line ~ /^[[:space:]]*Module Type/ { intype = 1 }
    intype && line ~ /^[[:space:]]*End[[:space:]]/ { intype = 0; next }
    line ~ /(^|[^A-Za-z_])(Admitted|admit|Abort|give_up|skip)([^A-Za-z_]|$)/ {
      print file ":" FNR ": unfinished proof: " $0; bad = 1
    }
    !intype && line ~ /^[[:space:]]*(Axiom|Axioms|Parameter|Parameters|Conjecture|Hypothesis|Hypotheses|Variable|Variables)[[:space:]]/ {
      print file ":" FNR ": assumption: " $0; bad = 1
    }
    END { exit bad }
  ' "$f" || status=1
done

if [ "$status" -eq 0 ]; then
  echo "OK: no assumptions besides the standard library's classical reals:"
  sed 's/^/  /' "$tmp/names.txt"
fi
exit "$status"
