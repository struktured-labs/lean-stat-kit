/-
  StatKit.Bridge: connects exact `ℚ` statistics to the Gaussian/measure toolkit.
  * `fitVar`: the population variance of a sample as an `NNReal` variance parameter.
  * `countBeyond_eq_kSD`: the `ℚ` count beyond k SDs equals the count of points (cast to ℝ) in the
    k-SD event of the fitted normal N(mean xs, popVar xs).
  * `fitted_out_of_sample`: generic pre-registered out-of-sample statement: fit on `train`,
    count on `test`, per-day Gaussian cap, Markov under any joint law of |test| variables.
-/
import StatKit.Descriptive
import StatKit.Gaussian
import StatKit.DistFree

open MeasureTheory ProbabilityTheory Real Set

namespace StatKit

open StatKit.Gaussian StatKit.DistFree

/-- the population variance of `xs` as a variance parameter -/
noncomputable def fitVar (xs : List ℚ) : NNReal := ⟨(popVar xs : ℝ), by exact_mod_cast popVar_nonneg xs⟩

theorem fitVar_coe (xs : List ℚ) : (fitVar xs : ℝ) = (popVar xs : ℝ) := rfl

theorem fitVar_ne {xs : List ℚ} (h : 0 < popVar xs) : fitVar xs ≠ 0 := by
  intro e
  have : (popVar xs : ℝ) = 0 := congrArg NNReal.toReal e
  have hp : (0 : ℝ) < popVar xs := by exact_mod_cast h
  linarith

open Classical in
/-- the exact `ℚ` count over `data` equals the count in the k-SD event of N(mean xs, popVar xs) -/
theorem countBeyond_eq_kSD (xs data : List ℚ) (k : ℕ) :
    data.countP (fun x : ℚ => decide ((x : ℝ) ∈ kSD (mean xs : ℝ) (fitVar xs) k)) =
      countBeyond ((k : ℚ) ^ 2) (mean xs) (popVar xs) data := by
  unfold countBeyond
  apply List.countP_congr
  intro x _
  have key : ((k : ℝ) ^ 2 * ((popVar xs : ℚ) : ℝ) < ((x : ℝ) - ((mean xs : ℚ) : ℝ)) ^ 2) ↔
      ((k : ℚ) ^ 2 * popVar xs < (x - mean xs) ^ 2) := by
    rw [← Rat.cast_lt (K := ℝ)]; push_cast; rfl
  rw [decide_eq_true_iff, kSD, Set.mem_ofPred_eq, fitVar_coe, key, decide_eq_true_iff]

/-- **Generic out-of-sample statement.** Fit N(μ̂, σ̂²) on `train`; let m be the number of `test`
    points beyond k fitted SDs (m ≥ 1); if the k-SD tail of the fitted normal is ≤ cap, then for any
    joint law of |test| variables with that marginal, P(at least m of them beyond k SDs) ≤ |test|·cap/m. -/
theorem fitted_out_of_sample (train test : List ℚ) (k : ℕ) {cap : ℝ}
    (hcap : gaussianReal (mean train : ℝ) (fitVar train) (kSD (mean train : ℝ) (fitVar train) k) ≤
      ENNReal.ofReal cap)
    (hm : 0 < countBeyond ((k : ℚ) ^ 2) (mean train) (popVar train) test)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Fin test.length → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, P.map (X i) = gaussianReal (mean train : ℝ) (fitVar train))
    [∀ ω, DecidablePred (fun i => X i ω ∈ kSD (mean train : ℝ) (fitVar train) k)] :
    P {ω | countBeyond ((k : ℚ) ^ 2) (mean train) (popVar train) test ≤
        (Finset.univ.filter (fun i => X i ω ∈ kSD (mean train : ℝ) (fitVar train) k)).card} ≤
      ENNReal.ofReal (test.length * cap / countBeyond ((k : ℚ) ^ 2) (mean train) (popVar train) test) := by
  have := markov_count_ofReal P _ (kSD_measurable _ _ k) X hXm hX hm hcap
  simpa using this

end StatKit
