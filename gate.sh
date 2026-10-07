#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists, fully qualified, every declaration of this library cited in SPIKE_REPORT.md
# plus every name queried by scratch/Ax.lean; definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Miquel"
LIB="Miquel"
REQUIRED="Miquel.Dp Miquel.Dp_eq Miquel.Dp_eq_neg_det Miquel.Dp_eq_zero_iff_collinear Miquel.KK Miquel.KK_eq_dist_sq Miquel.Q Miquel.Q_eq_Dp_mul_power Miquel.Q_eq_det Miquel.Q_eq_zero_of_dist Miquel.Q_self Miquel.Q_swap12 Miquel.Q_swap34 Miquel.al1 Miquel.al1_eq_zero_iff_collinear Miquel.al2 Miquel.al2_eq_zero_iff_collinear Miquel.al3 Miquel.al3_eq_zero_iff_collinear Miquel.bridge Miquel.bridge_example Miquel.cert_x Miquel.cert_y Miquel.certx1 Miquel.certx1_spec Miquel.certx2 Miquel.certx2_spec Miquel.certy1 Miquel.certy1_spec Miquel.certy2 Miquel.certy2_spec Miquel.circX Miquel.circX_spec Miquel.circY Miquel.circY_spec Miquel.circ_aux Miquel.circ_aux_example Miquel.core Miquel.core_example Miquel.core_example_conclusion Miquel.core_example_point Miquel.dist_eq_five Miquel.dist_eq_of_Q_eq_zero Miquel.dist_eq_of_Q_eq_zero_example Miquel.dist_sq_re_im Miquel.exists_circle Miquel.frame Miquel.kk3 Miquel.kk3_spec Miquel.line_im Miquel.line_re Miquel.lx1 Miquel.lx1_spec Miquel.lx2 Miquel.lx2_spec Miquel.lx3 Miquel.lx3_spec Miquel.ly1 Miquel.ly1_spec Miquel.ly2 Miquel.ly2_spec Miquel.ly3 Miquel.ly3_spec Miquel.miquel Miquel.miquel_concyclic Miquel.miquel_example Miquel.miquel_hyps_example Miquel.miquel_negative_control Miquel.miquel_point_example Miquel.q1 Miquel.q1_spec Miquel.q2 Miquel.q2_spec Miquel.q3 Miquel.q3_spec Miquel.rpN Miquel.rpN_eq_zero_iff Miquel.rp_on Miquel.rp_zero Miquel.rpx Miquel.rpx_rpy_spec Miquel.rpy Miquel.sep Miquel.tang"
SOURCES="Miquel/*.lean Miquel.lean"
# Never fetch: the pinned Mathlib checkout must already be present.
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
# Portable (no GNU mktemp); the leading dot keeps it out of the SOURCES glob.
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
