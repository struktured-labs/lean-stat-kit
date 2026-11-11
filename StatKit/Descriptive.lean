/-
  StatKit.Descriptive: exact rational descriptive statistics over `List ℚ`, dataset-agnostic.
  Definitions use explicit recursion (`rsum`) so `decide +kernel` can evaluate them on concrete
  data; the lemmas are general (any list).
-/
import Mathlib

namespace StatKit

/-- sum, by explicit recursion (kernel-friendly) -/
def rsum : List ℚ → ℚ
  | [] => 0
  | x :: xs => x + rsum xs

theorem rsum_eq_sum (xs : List ℚ) : rsum xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rsum, ih]

/-- population mean Σx / n (0 for the empty list) -/
def mean (xs : List ℚ) : ℚ := rsum xs / xs.length

/-- Σ x² -/
def sumSq (xs : List ℚ) : ℚ := rsum (xs.map (· ^ 2))

/-- population variance Σx²/n − mean² -/
def popVar (xs : List ℚ) : ℚ := sumSq xs / xs.length - mean xs ^ 2

/-- Σ (x − μ)² -/
def sqDev (xs : List ℚ) (μ : ℚ) : ℚ := rsum (xs.map (fun x => (x - μ) ^ 2))

theorem sqDev_expand (xs : List ℚ) (μ : ℚ) :
    sqDev xs μ = sumSq xs - 2 * μ * rsum xs + xs.length * μ ^ 2 := by
  induction xs with
  | nil => simp [sqDev, sumSq, rsum]
  | cons x xs ih =>
    simp only [sqDev, sumSq, List.map_cons, rsum, List.length_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem mean_mul_length (xs : List ℚ) (h : xs ≠ []) : mean xs * xs.length = rsum xs := by
  have : (xs.length : ℚ) ≠ 0 := by exact_mod_cast List.length_pos_iff.mpr h |>.ne'
  simp [mean, this]

/-- variance as the mean squared deviation from the mean -/
theorem popVar_eq_sqDev (xs : List ℚ) (h : xs ≠ []) :
    popVar xs = sqDev xs (mean xs) / xs.length := by
  have hn : (xs.length : ℚ) ≠ 0 := by exact_mod_cast List.length_pos_iff.mpr h |>.ne'
  have hm := mean_mul_length xs h
  rw [sqDev_expand, popVar, ← hm]
  field_simp
  ring

theorem sqDev_nonneg (xs : List ℚ) (μ : ℚ) : 0 ≤ sqDev xs μ := by
  induction xs with
  | nil => simp [sqDev, rsum]
  | cons x xs ih =>
    simp only [sqDev, List.map_cons, rsum] at ih ⊢
    have := sq_nonneg (x - μ); linarith

theorem popVar_nonneg (xs : List ℚ) : 0 ≤ popVar xs := by
  rcases eq_or_ne xs [] with rfl | h
  · simp [popVar, sumSq, mean, rsum]
  · rw [popVar_eq_sqDev xs h]; exact div_nonneg (sqDev_nonneg _ _) (by positivity)

/-- the variance is positive as soon as two entries differ -/
theorem popVar_pos {xs : List ℚ} {a b : ℚ} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) :
    0 < popVar xs := by
  have h : xs ≠ [] := List.ne_nil_of_mem ha
  rw [popVar_eq_sqDev xs h]
  apply div_pos _ (by exact_mod_cast List.length_pos_iff.mpr h)
  have key : ∀ c ∈ xs, (c - mean xs) ^ 2 ≤ sqDev xs (mean xs) := by
    intro c hc
    rw [sqDev, rsum_eq_sum]
    exact List.single_le_sum (fun y hy => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact sq_nonneg _) _ (List.mem_map_of_mem hc)
  by_contra hle
  rw [not_lt] at hle
  have h1 : (a - mean xs) ^ 2 = 0 := le_antisymm ((key a ha).trans hle) (sq_nonneg _)
  have h2 : (b - mean xs) ^ 2 = 0 := le_antisymm ((key b hb).trans hle) (sq_nonneg _)
  have : a = b := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  exact hab this

/-! ### Counts beyond k standard deviations -/

/-- number of entries with (x − μ)² > k2 · v  (k2 = k², v = variance) -/
def countBeyond (k2 μ v : ℚ) (xs : List ℚ) : Nat :=
  xs.countP (fun x => decide (k2 * v < (x - μ) ^ 2))

theorem countBeyond_le_length (k2 μ v : ℚ) (xs : List ℚ) : countBeyond k2 μ v xs ≤ xs.length :=
  List.countP_le_length

/-- core inequality behind the empirical Chebyshev bound -/
theorem countBeyond_mul_le (k2 μ v : ℚ) (xs : List ℚ) :
    k2 * v * countBeyond k2 μ v xs ≤ sqDev xs μ := by
  induction xs with
  | nil => simp [countBeyond, sqDev, rsum]
  | cons x xs ih =>
    simp only [countBeyond, sqDev, List.map_cons, rsum, List.countP_cons] at ih ⊢
    by_cases hx : k2 * v < (x - μ) ^ 2
    · simp only [hx, decide_true, ite_true]; push_cast; linarith
    · simp only [hx, decide_false]; push_cast
      have := sq_nonneg (x - μ); linarith

/-- **Empirical Chebyshev** (no distributional assumption): at most n/k² entries lie more than
    k population SDs from the mean. -/
theorem countBeyond_le (xs : List ℚ) (k2 : ℚ) (hk : 0 < k2) (hv : 0 < popVar xs) :
    (countBeyond k2 (mean xs) (popVar xs) xs : ℚ) ≤ xs.length / k2 := by
  have h : xs ≠ [] := by rintro rfl; simp [popVar, sumSq, mean, rsum] at hv
  have hn : (0 : ℚ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr h
  have e := popVar_eq_sqDev xs h
  have key := countBeyond_mul_le k2 (mean xs) (popVar xs) xs
  rw [le_div_iff₀ hk]
  have hs : sqDev xs (mean xs) = popVar xs * xs.length := by rw [e]; field_simp
  rw [hs] at key
  nlinarith

/-! ### Threshold counts -/

/-- number of entries with |x| > t -/
def countAbsGt (t : ℚ) (xs : List ℚ) : Nat := xs.countP (fun x => decide (t < |x|))
/-- number of entries with x > t -/
def countGt (t : ℚ) (xs : List ℚ) : Nat := xs.countP (fun x => decide (t < x))

theorem countAbsGt_anti {s t : ℚ} (hst : s ≤ t) (xs : List ℚ) : countAbsGt t xs ≤ countAbsGt s xs := by
  unfold countAbsGt
  apply List.countP_mono_left
  intro x _ h
  simp only [decide_eq_true_eq] at h ⊢
  linarith

theorem countGt_le_countAbsGt (t : ℚ) (xs : List ℚ) : countGt t xs ≤ countAbsGt t xs := by
  unfold countGt countAbsGt
  apply List.countP_mono_left
  intro x _ h
  simp only [decide_eq_true_eq] at h ⊢
  exact lt_of_lt_of_le h (le_abs_self x)

/-! ### Lag-1 conditional counts (clustering) -/

/-- consecutive pairs (x_t, x_{t+1}) -/
def pairs {α : Type*} (xs : List α) : List (α × α) := xs.zip xs.tail

theorem pairs_length {α : Type*} (xs : List α) : (pairs xs).length = xs.length - 1 := by
  simp [pairs, List.length_zip]

/-- number of t (with a successor) where `p` holds at t -/
def leadCount {α : Type*} (p : α → Bool) (xs : List α) : Nat := (pairs xs).countP (fun q => p q.1)
/-- number of t where `p` holds at both t and t+1 -/
def bothCount {α : Type*} (p : α → Bool) (xs : List α) : Nat :=
  (pairs xs).countP (fun q => p q.1 && p q.2)

theorem bothCount_le_leadCount {α : Type*} (p : α → Bool) (xs : List α) :
    bothCount p xs ≤ leadCount p xs := by
  unfold bothCount leadCount
  apply List.countP_mono_left
  intro q _ h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem leadCount_le_count {α : Type*} (p : α → Bool) (xs : List α) :
    leadCount p xs ≤ xs.countP p := by
  induction xs with
  | nil => simp [leadCount, pairs]
  | cons x xs ih =>
    cases xs with
    | nil => simp [leadCount, pairs]
    | cons y ys =>
      have e : pairs (x :: y :: ys) = (x, y) :: pairs (y :: ys) := by simp [pairs]
      simp only [leadCount, e, List.countP_cons] at ih ⊢
      generalize (if p y = true then 1 else 0) = c at ih ⊢
      split <;> omega

/-! ### Simple returns from a positive price series -/

/-- r_t = (p_t − p_{t−1}) / p_{t−1} -/
def simpleReturns (ps : List ℕ) : List ℚ := (pairs ps).map (fun q => ((q.2 : ℚ) - q.1) / q.1)

theorem simpleReturns_length (ps : List ℕ) : (simpleReturns ps).length = ps.length - 1 := by
  simp [simpleReturns, pairs_length]

end StatKit
