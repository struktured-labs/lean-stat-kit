# lean-stat-kit (`statkit`)

A Lean 4 + Mathlib library for **machine-checked statistical claims about concrete, finite
datasets**: verified CSV ingestion → exact rational descriptive statistics → Gaussian tail caps
(Mills) → distribution-free bounds (Markov / union / Chebyshev, any joint law) → pre-registered
train/test split → **exact permutation tests** → a fail-closed rebuild and axiom audit.

Every theorem is checked by the Lean kernel and audited to depend only on the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no custom axioms.
Dataset facts are evaluated by the kernel (`decide +kernel`) on exact rationals, not floats.

Pins: Lean `v4.35.0` (commit `eb6cafb7…`), Mathlib `v4.35.0` (commit `56a00585…`).
License: Apache-2.0 (same as Mathlib), see `LICENSE`.

> The BTC example uses public daily Bitstamp closes purely as a worked illustration of the tools.
> Nothing here is a forecast, a trading signal, or investment advice.

## What is proved vs. what is computed

| Proved (kernel-checked theorems) | Only computed / checked at runtime |
| --- | --- |
| Parser soundness and completeness: `parseRows k s = some rows ↔ (∀ r ∈ rows, r.length = k) ∧ printRows rows = s` | That the **large** BTC file on disk equals the embedded rows: `Examples/Btc/DataCheck.lean` runs the proved parser with `lean --run` (a compiled-code check, not a kernel proof) |
| Exact rational mean / variance / counts for the embedded data (`decide +kernel`) | CSV → canonical CSV conversion in `tools/emit_csv_module.py` (Python, reproducibility-checked by the rebuild) |
| Gaussian tail caps (Mills ratio, π and e bounds), Markov bound under any joint law | |
| Exact permutation p-values (generic definition, closed-form count, examples) | |

Statements are about the stated finite data and stated models only. Gaussian bounds are about a
*fitted model*, not about the data-generating process. A permutation p-value is exact under its
stated null (exchangeability); it says nothing about whether that null is the right model.

## Using it as a dependency

`lakefile.toml` of your project:
```toml
[[require]]
name = "statkit"
git = "https://github.com/struktured-labs/lean-stat-kit"
rev = "main"            # or a commit SHA for a reproducible pin
```
Your project must use Lean `v4.35.0` (`lean-toolchain`: `leanprover/lean4:v4.35.0`); statkit pulls
Mathlib at the `v4.35.0` commit. Then `lake update statkit && lake exe cache get && lake build`, and
`import StatKit` (or a single module such as `import StatKit.Permutation`).

## Building this repository

```
lake exe cache get      # official Mathlib v4.35.0 build cache
lake build              # library StatKit + library Examples
```

### Fail-closed rebuild and audit (independent of lake)
```
(cd mathlib-env && lake exe cache get)     # once; or point MATHLIB_ENV at any Mathlib v4.35.0 env
tools/rebuild.sh                           # PASS/FAIL, log in logs/;  LAKE_BUILD=1 also runs lake build
./devc.sh StatKit/Permutation              # dev: compile one module into .out/
```
`rebuild.sh` (any failure ⇒ exit 1): Lean/Mathlib pins → `SHA256SUMS` → regenerate the data modules
and byte-compare → forbidden-construct scan (`sorry`, `admit`, `native_decide`, `axiom`,
`implemented_by`, `extern`, `unsafe`, …) → clean compile of every module in order with plain `lean`
→ runtime byte check of the BTC file → `#print axioms` for **every** theorem (generated `Audit.lean`,
`tools/check_axioms.py`, exact count) → sorry probe (a planted `sorry` must be rejected) → planted
sorry *inside* a lemma of `StatKit/Permutation` must propagate to the headline
`permPValue_adj` and be rejected.

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
`parseRowsF_sound`, **`parseRows_iff`**, `rows_of_parse`.

**`StatKit.Descriptive`** (over `List ℚ`, kernel-evaluable) – `rsum`, `mean`, `sumSq`, `popVar`, `sqDev`;
`rsum_eq_sum`, `mean_mul_length`, `sqDev_expand`, `popVar_eq_sqDev`, `popVar_nonneg`, **`popVar_pos`**;
`countBeyond k2 μ v xs` (# with k2·v < (x−μ)²), `countBeyond_le_length`, `countBeyond_mul_le`,
**`countBeyond_le`** (empirical Chebyshev ≤ n/k2); `countAbsGt`, `countGt`, `countAbsGt_anti`,
`countGt_le_countAbsGt`; lag-1: `pairs`, `leadCount`, `bothCount`, `pairs_length`,
`bothCount_le_leadCount`, `leadCount_le_count`; `simpleReturns`, `simpleReturns_length`.

**`StatKit.Gaussian`** – `phi`, `phi_pos`, `mills_integral`, `mills_upper` (P(Z>t) ≤ φ(t)/t),
**`mills_two_sided`**, `gaussianReal_Iio_neg`, **`gaussianReal_sq_tail`** (P(k²v < (X−μ)²) ≤ 2φ(k)/k
for X ~ N(μ,v)), `pi_ge`, `e_ge`, `phi_nat_sq`, **`tail_bound`**, `kSD μ v k`, `kSD_measurable`, caps
**`tail_k1`…`tail_k6`** (0.49, 0.055, 0.003, 6.7e-5, 6e-7, 2.1e-9).

**`StatKit.DistFree`** – `card_filter_eq_sum_indicator`, **`markov_count`** (any n, any joint law with
common marginal ν: P(#{i : X_i ∈ T} ≥ m) ≤ n·ν(T)/m; no independence), `markov_count_ofReal`,
`union_bound`, `chebyshev_gaussian`.

**`StatKit.Split`** – `trainPart key cut`, `testPart key cut`, `dated`, `keysSorted`;
**`split_perm`**, `split_length`, `train_keys`, `test_keys`, `split_eq_of_sorted`,
`keysSorted_pairwise`, **`split_eq_of_keysSorted`** (linear-time kernel check ⇒ train ++ test = data).

**`StatKit.Bridge`** – `fitVar`, `fitVar_coe`, `fitVar_ne`, `countBeyond_eq_kSD`,
**`fitted_out_of_sample`** (fit on train, count on test, Markov bound for the fitted model).

**`StatKit.Permutation`** (namespace `StatKit.Permutation`) – exact permutation tests:
* `permPValue T x := #{π : Perm (Fin n) | T x ≤ T (x ∘ π)} / n!` — the exact one-sided permutation
  p-value of any statistic `T` (values in a linear order) at data `x : Fin n → α`.
* `orbit x`, `orbitPValue`; **`permPValue_eq_orbitPValue`**: for every statistic and every data vector,
  the permutation p-value equals the fraction of *distinct rearrangements* `s` of `x` with
  `T x ≤ T s` (`card_fiber`: every rearrangement is hit by equally many permutations).
* Binary data: `ones`, **`mem_orbit_iff_ones`** (the rearrangements of a Boolean vector are exactly
  the Boolean vectors with the same number of `true`s), `orbit_eq_filter`.
* Lag-1 clustering statistic `adj` (# adjacent true-true pairs), `adjF` on `Fin n → Bool`,
  `bothCount_eq_adj` (the kit's `bothCount p xs = adj (xs.map p)`), enumeration `seqs n` of all
  Boolean lists of length n (`mem_seqs`, `nodup_seqs`, `length_seqs`), bridge `card_filter_ofFn`.
* `adjCount n k m := C(k-1, m) · C(n+1-k, k-m)` (for k ≤ n, else 0; ℕ subtraction) and
  **`cnt_eq_adjCount`**: exactly `adjCount n k m` Boolean sequences of length n have k trues and m
  adjacent true-true pairs. `countP_count_eq`: C(n, k) sequences have k trues.
* `adjTail n k m₀ := ∑_{m₀ ≤ m ≤ k} adjCount n k m`; **`permPValue_adj`**:
  `permPValue adjF x = adjTail n (ones x) (adjF x) / C(n, ones x)` for every `x : Fin n → Bool`;
  **`permPValue_adj_list`**: the same for a Boolean list `l` (`l.get`).
* Kernel-fast evaluation: `chooseFast`, `chooseFast_eq`, `adjTailFast`, `adjTailFast_eq`.

Null hypothesis: all arrangements of the observed values are equally likely (exchangeability);
the lag-1 p-value is conditional on the observed number of `true`s. One-sided (upper tail) only.

## Examples
* `Examples/Synthetic/{Data,Claims}` – 20-row toy price series (embedded, kernel-parsed): mean,
  variance, k-SD counts, empirical Chebyshev, lag-1 counts, Markov bound.
* `Examples/Synthetic/Permutation` – `toy_pvalue` (p = 11/42 for 5 trues with 3 adjacencies in 10),
  `toy_bruteforce` / `toy_counts_bruteforce` (independent brute force over all 2¹⁰ lists),
  `tiny_perm_enumeration` / `five_perm_enumeration` (kernel enumeration of all 4! / 5! permutations,
  agreeing with the closed form), `up_pvalue` (up-day clustering of the toy series, p = 7099/7106).
* `Examples/Btc/{Data,DataCheck,Clustering,OutOfSample,Permutation}` – re-derives BTC round-3
  headlines from the canonical Bitstamp daily file (sha256 `df6a3569…`) using only the kit:
  `split_prefix`, `lengths` (5365 = 2921 + 2444), `test_clustering` (33 big days |r| > 10 %, 4
  big→big follow-ups), `test_k3/k4/k5`, `round3_k5`, and **`test_clustering_pvalue`**: exact
  permutation p-value of the 4 follow-ups among 2444 TEST days with 33 big days =
  871054795507765819404787578084125234291543573591286455302322051 /
  1146782563716190351837549810888705966372921069461479432491809942444 ≈ 7.5956 × 10⁻⁴
  (`test_clustering_pvalue_bounds`).

## Known limits
* CSV: unsigned decimal fields only; no signs, exponents, quoting, or missing values.
* Large files are checked by running the proved parser (`lean --run`), not by a kernel proof that
  the whole on-disk file parses to the embedded rows.
* Permutation tests: the closed form covers the lag-1 adjacency statistic on binary data; other
  statistics use the generic `permPValue` definition, which is only practical to evaluate by kernel
  enumeration for small n (no general fast evaluator yet). One-sided p-values only. The
  validity theorem (P(p ≤ α) ≤ α under exchangeability) is not yet formalized.
* Exchangeability is an assumption about the data, not something the kit checks.

## Layout
`StatKit/` library · `Examples/` worked examples · `tools/` generator, rebuild, audit, probes ·
`data/` canonical CSVs · `examples-data/` raw inputs · `mathlib-env/` pinned Mathlib env for the
lake-independent rebuild · `SHA256SUMS` checksums of all tracked files.
