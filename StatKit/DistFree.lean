/-
  StatKit.DistFree: distribution-free bounds over ANY joint law (no independence assumed).
  * `markov_count`: if each of n variables X_i has law ν, then P(#{i | X_i ∈ T} ≥ m) ≤ n·ν(T)/m.
  * `markov_count_ofReal`: same with ν(T) ≤ p, stated as ≤ ofReal(n·p/m).
  * `union_bound`: P(∃ i, X_i ∈ T) ≤ n·ν(T).
  * `chebyshev_gaussian`: for N(μ, v), P(|X − μ| ≥ c) ≤ v/c².
-/
import Mathlib

open MeasureTheory ProbabilityTheory Real Set

namespace StatKit.DistFree

theorem card_filter_eq_sum_indicator {ι α : Type*} [Fintype ι] (S : ι → Set α) (ω : α)
    [DecidablePred (fun i => ω ∈ S i)] :
    ((Finset.univ.filter (fun i => ω ∈ S i)).card : ENNReal) = ∑ i, (S i).indicator 1 ω := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : ω ∈ S i <;> simp [h]

/-- Markov's inequality for a count, over ANY joint law (no independence): if each X_i has law ν,
    then P(#{i | X_i ∈ T} ≥ k) ≤ |ι|·ν(T)/k. -/
theorem markov_count {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) (ν : Measure ℝ)
    {T : Set ℝ} (hT : MeasurableSet T) (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, P.map (X i) = ν) {k : ℕ} (hk : 0 < k) [hdec : ∀ ω, DecidablePred (fun i => X i ω ∈ T)] :
    P {ω | k ≤ (Finset.univ.filter (fun i => X i ω ∈ T)).card} ≤ Fintype.card ι * ν T / k := by
  let N : Ω → ENNReal := fun ω => ∑ i, (X i ⁻¹' T).indicator 1 ω
  have hNm : Measurable N :=
    Finset.measurable_sum _ (fun i _ => measurable_one.indicator (hXm i hT))
  have hevent : {ω | k ≤ (Finset.univ.filter (fun i => X i ω ∈ T)).card} = {ω | (k : ENNReal) ≤ N ω} := by
    ext ω
    have hc := @card_filter_eq_sum_indicator ι Ω _ (fun i => X i ⁻¹' T) ω (hdec ω)
    simp only [mem_ofPred_eq]
    rw [← Nat.cast_le (α := ENNReal)]
    exact Iff.of_eq (congrArg _ hc)
  have hint : ∫⁻ ω, N ω ∂P = ∑ _i : ι, ν T := by
    simp only [N]
    rw [lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hXm i hT))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lintegral_indicator_one (hXm i hT), ← hX i, Measure.map_apply (hXm i) hT]
  rw [hevent]
  calc P {ω | (k : ENNReal) ≤ N ω} ≤ (∫⁻ ω, N ω ∂P) / k :=
        meas_ge_le_lintegral_div hNm.aemeasurable (by exact_mod_cast hk.ne') (ENNReal.natCast_ne_top k)
    _ = Fintype.card ι * ν T / k := by
        rw [hint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem markov_count_ofReal {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (ν : Measure ℝ) {T : Set ℝ} (hT : MeasurableSet T) (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, P.map (X i) = ν) {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : ν T ≤ ENNReal.ofReal p)
    [∀ ω, DecidablePred (fun i => X i ω ∈ T)] :
    P {ω | m ≤ (Finset.univ.filter (fun i => X i ω ∈ T)).card} ≤
      ENNReal.ofReal (Fintype.card ι * p / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc P {ω | m ≤ (Finset.univ.filter (fun i => X i ω ∈ T)).card}
      ≤ Fintype.card ι * ν T / m := markov_count P ν hT X hXm hX hm
    _ ≤ Fintype.card ι * ENNReal.ofReal p / m := by gcongr
    _ = ENNReal.ofReal (Fintype.card ι * p / m) := by
        rw [ENNReal.ofReal_div_of_pos hmR, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]

/-- union bound: P(some X_i ∈ T) ≤ n·ν(T), any joint law -/
theorem union_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (ν : Measure ℝ) {T : Set ℝ} (hT : MeasurableSet T) (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, P.map (X i) = ν) :
    P {ω | ∃ i, X i ω ∈ T} ≤ Fintype.card ι * ν T := by
  have e : {ω | ∃ i, X i ω ∈ T} = ⋃ i, X i ⁻¹' T := by ext; simp
  rw [e]
  calc P (⋃ i, X i ⁻¹' T) ≤ ∑ i, P (X i ⁻¹' T) := measure_iUnion_fintype_le P _
    _ = ∑ _i : ι, ν T := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← hX i, Measure.map_apply (hXm i) hT]
    _ = Fintype.card ι * ν T := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Chebyshev for a Gaussian law: P(|X − μ| ≥ c) ≤ v / c² -/
theorem chebyshev_gaussian (μ : ℝ) (v : NNReal) {c : ℝ} (hc : 0 < c) :
    gaussianReal μ v {x | c ≤ |x - μ|} ≤ ENNReal.ofReal (v / c ^ 2) := by
  have h := meas_ge_le_variance_div_sq (memLp_id_gaussianReal (μ := μ) (v := v) 2) hc
  simpa [integral_id_gaussianReal, variance_id_gaussianReal] using h

end StatKit.DistFree
