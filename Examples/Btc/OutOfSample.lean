/-
  BTC example: re-derive the round-3 headline `round3_k5` with the generic kit only.
  Fit N(μ̂, σ̂²) on TRAIN (exact rational mean / population variance of 2921 returns), count TEST
  returns beyond k fitted SDs, and bound the fitted model's probability of that many exceedances
  under ANY joint law of 2444 variables with the fitted marginal (Markov; no independence).
-/
import Examples.Btc.Clustering

open StatKit StatKit.Gaussian MeasureTheory ProbabilityTheory

namespace Examples.Btc

set_option maxRecDepth 100000 in
theorem train_var_pos : 0 < popVar train := by decide +kernel

set_option maxRecDepth 100000 in
theorem test_k3 : countBeyond ((3 : ℕ) ^ 2 : ℚ) (mean train) (popVar train) test = 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem test_k4 : countBeyond ((4 : ℕ) ^ 2 : ℚ) (mean train) (popVar train) test = 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem test_k5 : countBeyond ((5 : ℕ) ^ 2 : ℚ) (mean train) (popVar train) test = 1 := by decide +kernel

/-- round-3 `round3_k5`, re-derived: 1 TEST return lies beyond 5 TRAIN SDs; the fitted normal gives
    that event per-day probability ≤ 6/10^7; and under any joint law of 2444 variables with the fitted
    marginal, P(at least 1 of them beyond 5 SDs) ≤ 2444·6/10^7 ≤ 15/10^4. -/
theorem round3_k5 :
    countBeyond ((5 : ℕ) ^ 2 : ℚ) (mean train) (popVar train) test = 1 ∧
    gaussianReal (mean train : ℝ) (fitVar train) (kSD (mean train : ℝ) (fitVar train) 5) ≤
      ENNReal.ofReal (6 / 10 ^ 7) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Fin test.length → Ω → ℝ),
      (∀ i, Measurable (X i)) → (∀ i, P.map (X i) = gaussianReal (mean train : ℝ) (fitVar train)) →
      ∀ [∀ ω, DecidablePred (fun i => X i ω ∈ kSD (mean train : ℝ) (fitVar train) 5)],
      P {ω | 1 ≤ (Finset.univ.filter (fun i => X i ω ∈ kSD (mean train : ℝ) (fitVar train) 5)).card} ≤
        ENNReal.ofReal (15 / 10 ^ 4)) := by
  have hcap := tail_k5 (mean train : ℝ) (fitVar_ne train_var_pos)
  refine ⟨test_k5, hcap, ?_⟩
  intro Ω _ P X hXm hX _
  have h := fitted_out_of_sample train test 5 hcap (by rw [test_k5]; norm_num) P X hXm hX
  rw [test_k5] at h
  have e : ((test.length : ℕ) : ℝ) = 2444 := by exact_mod_cast lengths.2.2
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [e]; norm_num

end Examples.Btc
