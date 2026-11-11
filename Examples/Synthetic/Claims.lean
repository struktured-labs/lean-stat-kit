/-
  Synthetic example (made-up 20-day toy price series, data/synthetic_canon.csv, embedded and
  kernel-checked in Examples.Synthetic.Data). Shows the whole kit end to end on tiny data.
-/
import StatKit
import Examples.Synthetic.Data

open MeasureTheory ProbabilityTheory StatKit StatKit.Gaussian StatKit.DistFree

namespace Examples.Synthetic

open Examples.Synthetic.Data

/-- 19 simple returns of the toy price column (the 10^2 scale cancels in returns) -/
def rets : List ℚ := simpleReturns col_price

theorem rets_length : rets.length = 19 := by decide +kernel

theorem mean_eq : mean rets = 1324839097144026734780117 / 156365160739077451101740800 := by
  decide +kernel
theorem var_eq : popVar rets =
    540751170297647524383132925661552862016094196110489 /
      110025285718308877503302542506459284686887556730880000 := by
  decide +kernel
theorem var_pos : 0 < popVar rets := by rw [var_eq]; norm_num

theorem beyond1 : countBeyond ((1 : ℕ) ^ 2 : ℚ) (mean rets) (popVar rets) rets = 2 := by decide +kernel
theorem beyond2 : countBeyond ((2 : ℕ) ^ 2 : ℚ) (mean rets) (popVar rets) rets = 2 := by decide +kernel
theorem beyond3 : countBeyond ((3 : ℕ) ^ 2 : ℚ) (mean rets) (popVar rets) rets = 1 := by decide +kernel

/-- general lemma instance: at most 19/4 returns beyond 2 SDs (empirical Chebyshev) -/
theorem chebyshev2 : (countBeyond ((2 : ℕ) ^ 2 : ℚ) (mean rets) (popVar rets) rets : ℚ) ≤ 19 / 4 := by
  have := countBeyond_le rets ((2 : ℕ) ^ 2 : ℚ) (by norm_num) var_pos
  rwa [rets_length] at this

/-- |r| > 10 % moves and lag-1 clustering -/
def big (x : ℚ) : Bool := decide (1 / 10 < |x|)
theorem big_count : rets.countP big = 2 := by decide +kernel
theorem big_lead : leadCount big rets = 2 := by decide +kernel
theorem big_both : bothCount big rets = 0 := by decide +kernel

/-- the fitted normal's 2-SD tail ≤ 0.055; Markov under ANY joint law of 19 variables with that
    marginal: P(at least 2 beyond 2 SDs) ≤ 19·0.055/2 (here fitted in-sample, for illustration) -/
theorem markov2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Fin rets.length → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, P.map (X i) = gaussianReal (mean rets : ℝ) (fitVar rets))
    [∀ ω, DecidablePred (fun i => X i ω ∈ kSD (mean rets : ℝ) (fitVar rets) 2)] :
    P {ω | countBeyond ((2 : ℕ) ^ 2 : ℚ) (mean rets) (popVar rets) rets ≤
        (Finset.univ.filter (fun i => X i ω ∈ kSD (mean rets : ℝ) (fitVar rets) 2)).card} ≤
      ENNReal.ofReal (19 * (55 / 1000) / 2) := by
  have h := fitted_out_of_sample rets rets 2 (tail_k2 _ (fitVar_ne var_pos)) (by rw [beyond2]; norm_num)
    P X hXm hX
  rw [beyond2] at h ⊢
  have e : ((rets.length : ℕ) : ℝ) = 19 := by exact_mod_cast rets_length
  refine h.trans (le_of_eq ?_)
  rw [e]; norm_num

end Examples.Synthetic
