#!/usr/bin/env bash
# Fail-closed clean rebuild + audit of lean-stat-kit (headless). Any failing step => nonzero exit.
#   MATHLIB_ENV=<dir with Mathlib v4.35.0 built (lake exe cache get)>  tools/rebuild.sh
#   default MATHLIB_ENV = mathlib-env/ (run `lake exe cache get` there once).
#   LAKE_BUILD=1 additionally runs `lake build` of the package (step 10).
set -euo pipefail
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
M=$(realpath "${MATHLIB_ENV:-$K/mathlib-env}")
L=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
OUT=$K/.build; LOG=$K/logs/rebuild-$(date +%Y%m%d-%H%M%S).log
mkdir -p logs; exec > >(tee "$LOG") 2>&1
die() { echo "REBUILD FAIL: $*"; exit 1; }
T0=$(date +%s)
MODULES=(StatKit/Csv StatKit/Descriptive StatKit/Gaussian StatKit/DistFree StatKit/Split StatKit/Bridge
  StatKit/Permutation StatKit Examples/Synthetic/Data Examples/Synthetic/Claims Examples/Synthetic/Permutation
  Examples/Btc/Data Examples/Btc/Clustering Examples/Btc/OutOfSample Examples/Btc/Permutation Examples)

echo "== 1. pins"
"$L" --version | tee /dev/stderr | grep -q "4.35.0, .*commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc" || die "lean pin"
grep -q '"rev": "56a005855ea17e0b0958f73ec801ae140b0a1679"' "$M/lake-manifest.json" 2>/dev/null \
  || grep -q 'rev = "v4.35.0"' "$M/lakefile.toml" || die "mathlib env pin"
cmp -s "$M/lake-manifest.json" mathlib-env/lake-manifest.json || die "mathlib env manifest differs from mathlib-env/"
echo "pins OK"

echo "== 2. SHA256SUMS"
sha256sum --quiet -c SHA256SUMS || die "checksum mismatch"
echo "checksums OK ($(wc -l < SHA256SUMS) files)"

echo "== 3. regenerate data modules and compare"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
python3 tools/emit_csv_module.py --input examples-data/synthetic.csv --cols day,price --scale 0,2 --embed \
  --module Examples.Synthetic.Data --lean-out "$TMP/SynData.lean" --canon-out "$TMP/syn.csv"
python3 tools/emit_csv_module.py --input examples-data/btc_ohlc.csv --no-header --cols 0,4 --names date,close \
  --module Examples.Btc.Data --lean-out "$TMP/BtcData.lean" --canon-out "$TMP/btc.csv"
sed -i 's#canonical [^ ]*syn.csv#canonical data/synthetic_canon.csv#' "$TMP/SynData.lean"
sed -i 's#canonical [^ ]*btc.csv#canonical data/btc_date_close.csv#' "$TMP/BtcData.lean"
cmp "$TMP/SynData.lean" Examples/Synthetic/Data.lean || die "synthetic module not reproducible"
cmp "$TMP/syn.csv" data/synthetic_canon.csv || die "synthetic canonical not reproducible"
cmp "$TMP/BtcData.lean" Examples/Btc/Data.lean || die "btc module not reproducible"
cmp "$TMP/btc.csv" data/btc_date_close.csv || die "btc canonical not reproducible"
echo "data modules reproducible"

echo "== 4. forbidden-construct scan"
if grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|implemented_by|@\[extern|\bunsafe\b|ofReduceBool|debug\.skipKernelTC' \
   StatKit.lean StatKit/*.lean Examples.lean Examples/*/*.lean; then die "forbidden construct"; fi
echo "scan clean"

echo "== 5. compile (fresh $OUT)"
rm -rf "$OUT"; mkdir -p "$OUT"
MP=$(ls -d "$M"/.lake/packages/*/.lake/build/lib/lean | tr "\n" ":")
export LEAN_PATH=$OUT:$MP$("$L" --print-libdir)
for m in "${MODULES[@]}"; do
  mkdir -p "$OUT/$(dirname "$m")"; s=$(date +%s)
  "$L" -o "$OUT/$m.olean" "$m.lean" || die "compile $m"
  echo "  ok $m ($(( $(date +%s) - s ))s)"
done

echo "== 6. runtime byte check (proved parser on the on-disk canonical file)"
"$L" --run Examples/Btc/DataCheck.lean data/btc_date_close.csv || die "btc data check"

echo "== 7. axiom audit (every theorem)"
N=$(python3 tools/gen_audit.py Audit.lean $(printf '%s.lean ' "${MODULES[@]}" | sed 's/^StatKit\.lean //; s/ StatKit\.lean / /; s/ Examples\.lean / /'))
"$L" Audit.lean > "$TMP/audit.txt" || die "audit compile"
cp "$TMP/audit.txt" logs/axioms.txt
python3 tools/check_axioms.py "$TMP/audit.txt" "$N" || die "axiom audit"

echo "== 8. sorry probe (negative control: the audit MUST reject it)"
"$L" tools/probe/SorryProbe.lean > "$TMP/probe.txt" 2>&1 || true
if python3 tools/check_axioms.py "$TMP/probe.txt" 1 >/dev/null; then die "audit accepted sorry"; fi
grep -q sorryAx "$TMP/probe.txt" || die "probe did not report sorryAx"
echo "probe correctly rejected (sorryAx)"

echo "== 9. planted-sorry probe in StatKit/Permutation (hole in a lemma must surface in the headline)"
PL=$TMP/PermPlanted.lean
sed 's/^  rw \[cnt_eq, (c_eq_g n k m).1, (c_eq_g n k m).2, g_add\]$/  sorry/' StatKit/Permutation.lean > "$PL"
cmp -s "$PL" StatKit/Permutation.lean && die "planted-sorry mutation did not apply"
printf '\n#print axioms StatKit.Permutation.permPValue_adj\n' >> "$PL"
if ! grep -nE '\bsorry\b' "$PL" >/dev/null; then die "planted file lacks sorry"; fi
echo "  forbidden-construct scan flags the planted file: OK"
"$L" "$PL" > "$TMP/planted.txt" 2>&1 || true
tr '\n' ' ' < "$TMP/planted.txt" | grep -q "permPValue_adj' depends on axioms: \[[^]]*sorryAx" \
  || die "planted sorry did not reach permPValue_adj's axioms"
if python3 tools/check_axioms.py "$TMP/planted.txt" 1 >/dev/null; then die "audit accepted planted sorry"; fi
echo "planted sorry correctly rejected (permPValue_adj depends on sorryAx)"

if [ "${LAKE_BUILD:-0}" = 1 ]; then
  echo "== 10. lake build (package)"
  s=$(date +%s)
  lake build > "$TMP/lake.txt" 2>&1 || { tail -30 "$TMP/lake.txt"; die "lake build"; }
  tail -2 "$TMP/lake.txt"
  echo "lake build OK ($(( $(date +%s) - s ))s)"
fi

echo "REBUILD PASS: ${#MODULES[@]} modules, $N theorems audited, $(( $(date +%s) - T0 ))s total; log $LOG"
