/-
  StatKit.Gaussian: Gaussian tail toolkit on Mathlib's `gaussianReal` (dataset-agnostic).
  * `mills_upper`, `mills_two_sided`: Mills' inequality P(Z > a) ≤ φ(a)/a, P(|Z| > a) ≤ 2φ(a)/a.
  * `gaussianReal_sq_tail`: standardisation for any N(μ, v), v ≠ 0.
  * `tail_bound`: P((X−μ)² > k²v) ≤ c whenever 2/(3.14·k²·2.718^(k²)) ≤ c², c ≥ 0.
  * `tail_k1` … `tail_k6`: fixed rational caps for k = 1..6 SDs.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace StatKit.Gaussian


/-- standard normal density φ(x) = (√(2π))⁻¹ · exp(−x²/2) -/
noncomputable def phi (x : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2)

theorem gaussianPDFReal_zero_one : gaussianPDFReal 0 1 = phi := by
  funext x; simp [gaussianPDFReal, phi]

theorem phi_pos (x : ℝ) : 0 < phi x := by unfold phi; positivity

/-- d/dx (−φ x) = x · φ x -/
theorem hasDerivAt_neg_phi (x : ℝ) : HasDerivAt (fun t => -phi t) (x * phi x) x := by
  have h := (((hasDerivAt_pow 2 x).neg.div_const 2).exp.const_mul (√(2 * π))⁻¹).neg
  convert h using 1
  · funext t; simp [phi, neg_div]
  · simp only [phi, Pi.neg_apply]; push_cast; ring

theorem tendsto_neg_phi : Tendsto (fun t => -phi t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  have h2 : Tendsto (fun t : ℝ => rexp (-t ^ 2 / 2)) atTop (𝓝 0) := by
    have := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    refine this.congr (fun t => ?_)
    simp [neg_div]
  have h3 := (h2.const_mul (√(2 * π))⁻¹).neg
  simpa [phi] using h3

/-- ∫_{a}^{∞} x φ(x) dx = φ(a) for a ≥ 0 -/
theorem integral_Ioi_mul_phi {a : ℝ} (ha : 0 ≤ a) : ∫ x in Ioi a, x * phi x = phi a := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hasDerivAt_neg_phi x)
    (fun x hx => mul_nonneg (ha.trans (le_of_lt hx)) (phi_pos x).le) tendsto_neg_phi
  simpa using this

theorem integrableOn_Ioi_mul_phi {a : ℝ} (ha : 0 ≤ a) : IntegrableOn (fun x => x * phi x) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_neg_phi x)
    (fun x hx => mul_nonneg (ha.trans (le_of_lt hx)) (phi_pos x).le) tendsto_neg_phi

theorem integrable_phi : Integrable phi := by
  rw [← gaussianPDFReal_zero_one]; exact integrable_gaussianPDFReal 0 1

/-- **Mills' inequality** (integral form): ∫_{a}^{∞} φ ≤ φ(a)/a for a > 0. -/
theorem mills_integral {a : ℝ} (ha : 0 < a) : ∫ x in Ioi a, phi x ≤ phi a / a := by
  calc ∫ x in Ioi a, phi x ≤ ∫ x in Ioi a, x * phi x / a := by
        refine setIntegral_mono_on integrable_phi.integrableOn
          ((integrableOn_Ioi_mul_phi ha.le).div_const a) measurableSet_Ioi (fun x hx => ?_)
        have hxa : a < x := hx
        rw [le_div_iff₀ ha]
        nlinarith [phi_pos x]
    _ = phi a / a := by rw [integral_div, integral_Ioi_mul_phi ha.le]

/-- **Mills' inequality** (measure form, upper tail): P(Z > a) ≤ φ(a)/a for Z ~ N(0,1), a > 0. -/
theorem mills_upper {a : ℝ} (ha : 0 < a) :
    gaussianReal 0 1 (Ioi a) ≤ ENNReal.ofReal (phi a / a) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, gaussianPDFReal_zero_one]
  exact ENNReal.ofReal_le_ofReal (mills_integral ha)

theorem gaussianReal_Iio_neg (a : ℝ) : gaussianReal 0 1 (Iio (-a)) = gaussianReal 0 1 (Ioi a) := by
  have h : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  rw [← h, Measure.map_apply measurable_neg measurableSet_Ioi]
  congr 1
  ext x; simp

/-- **Mills' inequality** (two-sided): P(|Z| > a) ≤ 2·φ(a)/a for Z ~ N(0,1), a > 0. -/
theorem mills_two_sided {a : ℝ} (ha : 0 < a) :
    gaussianReal 0 1 {x | a < |x|} ≤ ENNReal.ofReal (2 * phi a / a) := by
  have hset : {x : ℝ | a < |x|} = Ioi a ∪ Iio (-a) := by
    ext x; simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith
  rw [hset]
  calc gaussianReal 0 1 (Ioi a ∪ Iio (-a))
      ≤ gaussianReal 0 1 (Ioi a) + gaussianReal 0 1 (Iio (-a)) := measure_union_le _ _
    _ = gaussianReal 0 1 (Ioi a) + gaussianReal 0 1 (Ioi a) := by rw [gaussianReal_Iio_neg]
    _ ≤ ENNReal.ofReal (phi a / a) + ENNReal.ofReal (phi a / a) :=
        add_le_add (mills_upper ha) (mills_upper ha)
    _ = ENNReal.ofReal (2 * phi a / a) := by
        rw [← ENNReal.ofReal_add (div_nonneg (phi_pos a).le ha.le) (div_nonneg (phi_pos a).le ha.le)]
        congr 1; ring

/-- Standardisation: for X ~ N(μ, v), v ≠ 0, and k > 0,
    P((X − μ)² > k²·v) = P(|Z| > k). -/
theorem gaussianReal_sq_tail (μ : ℝ) {v : NNReal} (hv : v ≠ 0) {k : ℝ} (hk : 0 < k) :
    gaussianReal μ v {x | k ^ 2 * (v : ℝ) < (x - μ) ^ 2} = gaussianReal 0 1 {z | k < |z|} := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.mp h.symm))
  have h1 : (gaussianReal 0 1).map (fun z => √(v : ℝ) * z) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  have h2 : (gaussianReal 0 v).map (· + μ) = gaussianReal μ v := by
    rw [gaussianReal_map_add_const]; simp
  have hS : MeasurableSet {x : ℝ | k ^ 2 * (v : ℝ) < (x - μ) ^ 2} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← h2, ← h1, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) hS]
  congr 1
  ext z
  simp only [mem_preimage, Function.comp_apply, mem_ofPred_eq, add_sub_cancel_right, mul_pow]
  have hs : √(v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt v.2
  rw [hs]
  constructor
  · intro h
    have h' : k ^ 2 < z ^ 2 := by nlinarith
    have := sq_lt_sq.mp h'
    rwa [abs_of_pos hk] at this
  · intro h
    have h' : k ^ 2 < z ^ 2 := sq_lt_sq.mpr (by rwa [abs_of_pos hk])
    nlinarith


theorem pi_ge : (314 / 100 : ℝ) ≤ π := by
  have := Real.pi_gt_d2; norm_num at this ⊢; linarith

theorem e_ge : (2718 / 1000 : ℝ) ≤ rexp 1 := by
  have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith

theorem phi_nat_sq (k : ℕ) (hk : 0 < k) : (2 * phi k / k) ^ 2 = 2 / (π * (k : ℝ) ^ 2 * rexp 1 ^ (k ^ 2)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have hs : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hE : rexp (-(k : ℝ) ^ 2 / 2) ^ 2 = (rexp 1 ^ (k ^ 2))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1; push_cast; ring
  have hF : 0 < rexp 1 ^ (k ^ 2) := by positivity
  simp only [phi]
  rw [div_pow, mul_pow, mul_pow, inv_pow, hs, hE]
  field_simp

theorem tail_bound (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (k : ℕ) (hk : 0 < k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : 2 / (314 / 100 * (k : ℝ) ^ 2 * (2718 / 1000) ^ (k ^ 2)) ≤ c ^ 2) :
    gaussianReal μ v {x | (k : ℝ) ^ 2 * (v : ℝ) < (x - μ) ^ 2} ≤ ENNReal.ofReal c := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [gaussianReal_sq_tail μ hv hkR]
  refine (mills_two_sided hkR).trans (ENNReal.ofReal_le_ofReal ?_)
  have hden : (314 / 100 : ℝ) * (k : ℝ) ^ 2 * (2718 / 1000) ^ (k ^ 2) ≤ π * (k : ℝ) ^ 2 * rexp 1 ^ (k ^ 2) := by
    gcongr
    · exact pi_ge
    · exact e_ge
  have hpos : (0 : ℝ) < 314 / 100 * (k : ℝ) ^ 2 * (2718 / 1000) ^ (k ^ 2) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hkR 2)) (pow_pos (by norm_num) _)
  have hq : (2 * phi k / k) ^ 2 ≤ c ^ 2 := by
    rw [phi_nat_sq k hk]
    exact (div_le_div_of_nonneg_left (by norm_num) hpos hden).trans hc
  have h0 : 0 ≤ 2 * phi k / k := div_nonneg (mul_nonneg (by norm_num) (phi_pos _).le) hkR.le
  nlinarith

/-- the k-SD two-sided event of N(μ, v) -/
def kSD (μ : ℝ) (v : NNReal) (k : ℕ) : Set ℝ := {x | (k : ℝ) ^ 2 * (v : ℝ) < (x - μ) ^ 2}

theorem kSD_measurable (μ : ℝ) (v : NNReal) (k : ℕ) : MeasurableSet (kSD μ v k) :=
  measurableSet_lt measurable_const (by fun_prop)

/-- Mills caps for k = 1..6 (true two-sided tails: 0.317, 0.0455, 0.0027, 6.3e-5, 5.7e-7, 2.0e-9) -/
theorem tail_k1 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 1) ≤ ENNReal.ofReal (49 / 100) :=
  tail_bound μ hv 1 (by norm_num) _ (by norm_num) (by norm_num)
theorem tail_k2 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 2) ≤ ENNReal.ofReal (55 / 1000) :=
  tail_bound μ hv 2 (by norm_num) _ (by norm_num) (by norm_num)
theorem tail_k3 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 3) ≤ ENNReal.ofReal (3 / 1000) :=
  tail_bound μ hv 3 (by norm_num) _ (by norm_num) (by norm_num)
theorem tail_k4 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 4) ≤ ENNReal.ofReal (67 / 10 ^ 6) :=
  tail_bound μ hv 4 (by norm_num) _ (by norm_num) (by norm_num)
theorem tail_k5 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 5) ≤ ENNReal.ofReal (6 / 10 ^ 7) :=
  tail_bound μ hv 5 (by norm_num) _ (by norm_num) (by norm_num)
theorem tail_k6 (μ : ℝ) {v : NNReal} (hv : v ≠ 0) : gaussianReal μ v (kSD μ v 6) ≤ ENNReal.ofReal (21 / 10 ^ 10) :=
  tail_bound μ hv 6 (by norm_num) _ (by norm_num) (by norm_num)

end StatKit.Gaussian
