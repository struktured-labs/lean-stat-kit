# lean-stat-kit

Private, local-only Lean 4 library for **machine-checked statistics claims about a concrete dataset**:
verified CSV ingestion → exact rational descriptive statistics → Gaussian tail caps (Mills) →
distribution-free bounds (Markov / union / Chebyshev, any joint law) → pre-registered train/test split →
fail-closed audit harness. Extracted from the BTC Bitstamp rounds 1–3 and generalized.

Pins: Lean `v4.35.0` (commit eb6cafb7…), Mathlib `v4.35.0` (56a00585…); see `mathlib-env/`.
No `sorry`, no `native_decide`, no custom axioms: every theorem uses only `propext`, `Classical.choice`,
`Quot.sound` (checked by `tools/rebuild.sh`). Dataset facts are kernel-checked with `decide +kernel`.

## Build / audit

```
# once: a Mathlib v4.35.0 project with the official cache (lake exe cache get), e.g. mathlib-env/
MATHLIB_ENV=~/scratch/mathlib-v4.35.0 tools/rebuild.sh     # PASS/FAIL, log in logs/
./devc.sh StatKit/Descriptive                               # dev: compile one module into .out/
```
`rebuild.sh` steps (any failure ⇒ exit 1): pins → `SHA256SUMS` → regenerate data modules and `cmp`
→ forbidden-construct scan → clean compile in order → runtime byte check of the BTC file with the proved
parser → `#print axioms` for **every** theorem (generated `Audit.lean`, `tools/check_axioms.py`,
exact count) → sorry probe (negative control must be rejected).

## Adding a dataset
```
python3 tools/emit_csv_module.py --input my.csv --cols date,price --scale 0,2 --embed \
  --module My.Data --lean-out My/Data.lean --canon-out data/my_canon.csv
```
Unsigned decimal fields only (fail-closed otherwise); `--scale` = decimal places (value = field/10^s).
`--embed` (small files) puts the canonical bytes in Lean and proves `parse_ok : parseRows k (bytesOf
canonical) = some rows` and `rows_spec` by kernel. Without `--embed` (large files) it writes
`My/DataCheck.lean`, which runs the proved parser on the file at build time (`lean --run`).

## API (namespace `StatKit` unless noted)

**`StatKit.Csv`** (core Lean only) – `printRow`, `printRows`, `parseRows k`, `column`, `bytesOf`;
`parseField_print`, `parseField_sound`, `parseRowK_print`, `parseRowK_sound`, `parseRowsF_print`,
`parseRowsF_sound`, **`parseRows_iff`** (`parseRows k s = some rows ↔ (∀ r ∈ rows, r.length = k) ∧
printRows rows = s`, i.e. the bytes are exactly the canonical print of the rows), `rows_of_parse`.

**`StatKit.Descriptive`** (over `List ℚ`, kernel-evaluable) – `rsum`, `mean`, `sumSq`, `popVar`, `sqDev`;
`rsum_eq_sum`, `mean_mul_length`, `sqDev_expand`, `popVar_eq_sqDev`, `popVar_nonneg`, **`popVar_pos`**;
`countBeyond k2 μ v xs` (# with k2·v < (x−μ)²), `countBeyond_le_length`, `countBeyond_mul_le`,
**`countBeyond_le`** (empirical Chebyshev ≤ n/k2); `countAbsGt`, `countGt`, `countAbsGt_anti`,
`countGt_le_countAbsGt`; lag-1: `pairs`, `leadCount`, `bothCount`, `pairs_length`,
`bothCount_le_leadCount`, `leadCount_le_count`; `simpleReturns`, `simpleReturns_length`.

**`StatKit.Gaussian`** – `phi`, `phi_pos`, `mills_integral`, `mills_upper` (P(Z>t) ≤ φ(t)/t),
**`mills_two_sided`**, `gaussianReal_Iio_neg`, **`gaussianReal_sq_tail`** (N(μ,v) standardization:
P(k²v < (X−μ)²) ≤ 2φ(k)/k), `pi_ge`, `e_ge`, `phi_nat_sq`, **`tail_bound`** (rational cap from
π, e bounds), `kSD μ v k`, `kSD_measurable`, caps **`tail_k1`…`tail_k6`**
(0.49, 0.055, 0.003, 6.7e-5, 6e-7, 2.1e-9).

**`StatKit.DistFree`** – `card_filter_eq_sum_indicator`, **`markov_count`** (any n, any joint law with
common marginal ν: P(#{i : X_i ∈ T} ≥ m) ≤ n·ν(T)/m; no independence), `markov_count_ofReal`,
`union_bound`, `chebyshev_gaussian`.

**`StatKit.Split`** – `trainPart key cut`, `testPart key cut`, `dated`, `keysSorted`;
**`split_perm`** (partition), `split_length`, `train_keys`, `test_keys`, `split_eq_of_sorted`,
`keysSorted_pairwise`, **`split_eq_of_keysSorted`** (linear-time kernel check ⇒ train ++ test = data).

**`StatKit.Bridge`** – `fitVar`, `fitVar_coe`, `fitVar_ne`, `countBeyond_eq_kSD` (ℚ count = ℝ-event
count), **`fitted_out_of_sample`** (fit on train, count on test, Markov bound for the fitted model).

## Examples
* `Examples/Synthetic/{Data,Claims}` – 20-row toy price series (embedded, kernel-parsed): mean, variance,
  k-SD counts, empirical Chebyshev, lag-1 counts, Markov bound.
* `Examples/Btc/{Data,DataCheck,Clustering,OutOfSample}` – re-derives the BTC round-3 headlines from the
  round-1 canonical Bitstamp file (sha256 df6a3569…) using only the kit: `split_prefix`, `lengths`
  (5365 = 2921 + 2444), **`test_clustering`** (33 big days, 33 leads, 4 both; 4/33 is 8–9× 33/2444),
  `test_k3/k4/k5` (9 / 2 / 1 TEST returns beyond 3/4/5 TRAIN SDs) and **`round3_k5`**.

## Caveats
Statements are about the stated finite data and stated models only; Gaussian bounds are about the
*fitted model*, not the data-generating process. No forecasting or trading content.
