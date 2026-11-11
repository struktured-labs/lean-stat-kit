/-
  StatKit.Permutation: exact permutation tests (no Monte Carlo).

  * `permPValue T x` is the exact one-sided permutation p-value of a statistic `T` at data
    `x : Fin n → α`: the fraction of all `n!` position permutations `π` with `T x ≤ T (x ∘ π)`.
  * `permPValue_eq_orbitPValue`: for any statistic and any data, this equals the fraction of
    distinct rearrangements `s` of `x` with `T x ≤ T s` (each rearrangement is hit by the same
    number of permutations).
  * Binary data, lag-1 clustering statistic `adj` (# of adjacent `true, true` pairs):
    `card_adj_eq` proves the closed form: among length-`n` Boolean sequences with `k` trues,
    exactly `C(k-1, m) * C(n+1-k, k-m)` have `m` adjacencies (for `k ≤ n`; Nat subtraction).
    `permPValue_adj` / `permPValue_adj_list` turn it into the exact rational p-value
    `adjTail n k m₀ / C(n, k)` with `adjTail n k m₀ = ∑_{m₀ ≤ m ≤ k} C(k-1, m) C(n+1-k, k-m)`.
  Null hypothesis behind the p-value: all arrangements of the observed values are equally
  likely (exchangeability / permutation null), conditional on the observed number of trues.
-/
import Mathlib
import StatKit.Descriptive

open Finset

namespace StatKit.Permutation

/-! ## 1. Generic exact permutation p-value -/

section Generic

variable {n : ℕ} {α β : Type*} [LinearOrder β]

/-- Exact one-sided permutation p-value: `#{π ∈ Sym(Fin n) : T x ≤ T (x ∘ π)} / n!`. -/
def permPValue (T : (Fin n → α) → β) (x : Fin n → α) : ℚ :=
  (#{π : Equiv.Perm (Fin n) | T x ≤ T (x ∘ π)} : ℚ) / (n.factorial : ℚ)

variable [DecidableEq α]

/-- all rearrangements of `x` (orbit under permutation of positions) -/
def orbit (x : Fin n → α) : Finset (Fin n → α) :=
  univ.image (fun π : Equiv.Perm (Fin n) => x ∘ π)

/-- p-value over distinct rearrangements: `#{s ∈ orbit x : T x ≤ T s} / #(orbit x)` -/
def orbitPValue (T : (Fin n → α) → β) (x : Fin n → α) : ℚ :=
  (#{s ∈ orbit x | T x ≤ T s} : ℚ) / (#(orbit x) : ℚ)

theorem mem_orbit {x s : Fin n → α} : s ∈ orbit x ↔ ∃ π : Equiv.Perm (Fin n), x ∘ π = s := by
  simp [orbit]

/-- every rearrangement is produced by the same number of permutations -/
theorem card_fiber (x : Fin n → α) (π₀ : Equiv.Perm (Fin n)) :
    #{π : Equiv.Perm (Fin n) | x ∘ π = x ∘ π₀} = #{π : Equiv.Perm (Fin n) | x ∘ π = x} := by
  symm
  apply Finset.card_nbij' (fun σ => σ * π₀) (fun τ => τ * π₀⁻¹)
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    funext i
    simpa [Equiv.Perm.mul_apply] using congrFun hσ (π₀ i)
  · intro τ hτ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    funext i
    simpa [Equiv.Perm.mul_apply] using congrFun hτ (π₀⁻¹ i)
  · intro σ _; simp
  · intro τ _; simp

/-- **Permutation p-value = rearrangement p-value**, for every statistic and every data vector. -/
theorem permPValue_eq_orbitPValue (T : (Fin n → α) → β) (x : Fin n → α) :
    permPValue T x = orbitPValue T x := by
  set c := #{π : Equiv.Perm (Fin n) | x ∘ π = x} with hc_def
  have hfib : ∀ s ∈ orbit x, #{π : Equiv.Perm (Fin n) | x ∘ π = s} = c := by
    intro s hs
    obtain ⟨π₀, rfl⟩ := mem_orbit.mp hs
    exact card_fiber x π₀
  have hnum : #{π : Equiv.Perm (Fin n) | T x ≤ T (x ∘ π)} = #{s ∈ orbit x | T x ≤ T s} * c := by
    rw [card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin n) => x ∘ π) (t := {s ∈ orbit x | T x ≤ T s})]
    · rw [Finset.sum_const_nat]
      intro s hs
      rw [mem_filter] at hs
      rw [← hfib s hs.1, filter_filter]
      congr 1
      apply filter_congr
      intro π _
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; exact hs.2, h⟩
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      exact ⟨mem_orbit.mpr ⟨π, rfl⟩, hπ⟩
  have hden : n.factorial = #(orbit x) * c := by
    have h1 : n.factorial = #(univ : Finset (Equiv.Perm (Fin n))) := by
      rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [h1, card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin n) => x ∘ π) (t := orbit x)]
    · rw [Finset.sum_const_nat]
      intro s hs
      exact hfib s hs
    · intro π _
      exact mem_orbit.mpr ⟨π, rfl⟩
  have hc : (c : ℚ) ≠ 0 := by
    have : 0 < c := card_pos.mpr ⟨1, by simp⟩
    exact_mod_cast this.ne'
  unfold permPValue orbitPValue
  rw [hnum, hden]
  push_cast
  exact mul_div_mul_right _ _ hc

end Generic

/-! ## 2. Binary data: rearrangements = sequences with the same number of trues -/

section Binary

variable {n : ℕ}

/-- number of `true` entries -/
def ones (x : Fin n → Bool) : ℕ := #{i | x i = true}

theorem ones_comp (x : Fin n → Bool) (π : Equiv.Perm (Fin n)) : ones (x ∘ π) = ones x := by
  unfold ones
  apply Finset.card_nbij' (fun i => π i) (fun i => π.symm i) <;> intro i _ <;> simp_all

theorem exists_perm_of_ones_eq {x s : Fin n → Bool} (h : ones s = ones x) :
    ∃ π : Equiv.Perm (Fin n), x ∘ π = s := by
  have h1 : Fintype.card {i // s i = true} = Fintype.card {i // x i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact h
  have h2 : Fintype.card {i // ¬ s i = true} = Fintype.card {i // ¬ x i = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  set e := Fintype.equivOfCardEq h1
  set f := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e f, ?_⟩
  funext i
  simp only [Function.comp]
  by_cases hi : s i = true
  · have hv : Equiv.subtypeCongr e f i = (e ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hi]
    rw [hv, hi]; exact (e ⟨i, hi⟩).2
  · have hv : Equiv.subtypeCongr e f i = (f ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hi]
    rw [hv]
    have := (f ⟨i, hi⟩).2
    simp only [Bool.not_eq_true] at this hi
    rw [this, hi]

theorem mem_orbit_iff_ones {x s : Fin n → Bool} : s ∈ orbit x ↔ ones s = ones x := by
  rw [mem_orbit]
  constructor
  · rintro ⟨π, rfl⟩; exact ones_comp x π
  · exact exists_perm_of_ones_eq

theorem orbit_eq_filter (x : Fin n → Bool) : orbit x = univ.filter (fun s => ones s = ones x) := by
  ext s; simp [mem_orbit_iff_ones]

end Binary

/-! ## 3. Lag-1 clustering statistic and exhaustive enumeration -/

/-- number of adjacent `(true, true)` pairs -/
def adj : List Bool → ℕ
  | a :: b :: l => (if (a && b) = true then 1 else 0) + adj (b :: l)
  | _ => 0

@[simp] theorem adj_nil : adj [] = 0 := rfl
@[simp] theorem adj_single (a : Bool) : adj [a] = 0 := rfl

theorem adj_false_cons (s : List Bool) : adj (false :: s) = adj s := by
  cases s with
  | nil => rfl
  | cons b l => simp [adj]

theorem adj_true_cons (s : List Bool) :
    adj (true :: s) = adj s + (if s.head? = some true then 1 else 0) := by
  cases s with
  | nil => rfl
  | cons b l => cases b <;> simp [adj] <;> omega

theorem adj_le_count (s : List Bool) : adj s ≤ s.count true := by
  induction s with
  | nil => simp [adj]
  | cons a l ih =>
    cases a
    · rw [adj_false_cons]; simpa using ih
    · rw [adj_true_cons, List.count_cons_self]
      split <;> omega

/-- the kit's lag-1 `bothCount` is `adj` of the indicator sequence -/
theorem bothCount_eq_adj {α : Type*} (p : α → Bool) (xs : List α) :
    bothCount p xs = adj (xs.map p) := by
  induction xs with
  | nil => simp [bothCount, pairs, adj]
  | cons x xs ih =>
    cases xs with
    | nil => simp [bothCount, pairs, adj]
    | cons y ys =>
      have e : pairs (x :: y :: ys) = (x, y) :: pairs (y :: ys) := by simp [pairs]
      simp only [bothCount, e, List.countP_cons] at ih ⊢
      rw [ih]
      simp only [List.map_cons, adj]
      split <;> simp_all [add_comm]

/-- all Boolean lists of length `n` -/
def seqs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (seqs n).map (false :: ·) ++ (seqs n).map (true :: ·)

theorem mem_seqs {n : ℕ} {s : List Bool} : s ∈ seqs n ↔ s.length = n := by
  induction n generalizing s with
  | zero => simp [seqs]
  | succ n ih =>
    cases s with
    | nil => simp [seqs]
    | cons b l => cases b <;> simp [seqs, ih]

theorem nodup_seqs (n : ℕ) : (seqs n).Nodup := by
  induction n with
  | zero => simp [seqs]
  | succ n ih =>
    rw [seqs, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => List.cons.inj h |>.2), ih.map (fun _ _ h => List.cons.inj h |>.2), ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, rfl⟩ := hb
    simp

theorem length_seqs (n : ℕ) : (seqs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [seqs, ih, pow_succ]; ring

/-- bridge: counting functions `Fin n → Bool` = counting the enumeration `seqs n` -/
theorem card_filter_ofFn (n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    #{x : Fin n → Bool | P (List.ofFn x)} = (seqs n).countP (fun s => decide (P s)) := by
  induction n generalizing P with
  | zero =>
    rw [card_filter]
    simp [seqs]
  | succ n ih =>
    rw [card_filter, ← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    have hc : ∀ (b : Bool) (y : Fin n → Bool),
        List.ofFn ((Fin.consEquiv (fun _ => Bool)) (b, y)) = b :: List.ofFn y := by
      intro b y; simp [Fin.consEquiv, List.ofFn_succ]
    simp only [hc]
    have ih' := fun b => ih (fun s => P (b :: s))
    simp only [card_filter] at ih'
    rw [ih' true, ih' false, seqs, List.countP_append, List.countP_map, List.countP_map]
    simp only [Function.comp_def]
    ring

theorem count_ofFn {n : ℕ} (x : Fin n → Bool) : (List.ofFn x).count true = ones x := by
  unfold ones
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, card_filter, card_filter, Fin.sum_univ_succ]
    cases h : x 0 <;> simp [h] <;> ring

/-! ## 4. Exact count of arrangements with `m` adjacencies -/

/-- starts with `true`, `k` trues, `m` adjacencies -/
def c1 (n k m : ℕ) : ℕ :=
  (seqs n).countP (fun s => s.head? = some true ∧ s.count true = k ∧ adj s = m)
/-- does not start with `true` (empty or starts with `false`) -/
def c0 (n k m : ℕ) : ℕ :=
  (seqs n).countP (fun s => ¬ s.head? = some true ∧ s.count true = k ∧ adj s = m)
/-- length `n`, `k` trues, `m` adjacencies -/
def cnt (n k m : ℕ) : ℕ := (seqs n).countP (fun s => s.count true = k ∧ adj s = m)

theorem countP_split {γ : Type*} (l : List γ) (p q : γ → Bool) :
    l.countP p = l.countP (fun a => q a && p a) + l.countP (fun a => !q a && p a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    cases q a <;> cases p a <;> simp <;> omega

theorem cnt_eq (n k m : ℕ) : cnt n k m = c0 n k m + c1 n k m := by
  unfold cnt c0 c1
  rw [countP_split _ _ (fun s => decide (s.head? = some true)), add_comm]
  congr 1

theorem c0_zero (k m : ℕ) : c0 0 k m = if k = 0 ∧ m = 0 then 1 else 0 := by
  simp only [c0, seqs, List.countP_singleton]
  by_cases hk : k = 0 <;> by_cases hm : m = 0 <;> simp [hk, hm, eq_comm]

theorem c1_zero (k m : ℕ) : c1 0 k m = 0 := by simp [c1, seqs]

theorem c0_succ (n k m : ℕ) : c0 (n + 1) k m = cnt n k m := by
  simp only [c0, cnt, seqs, List.countP_append, List.countP_map]
  have : List.countP ((fun s => decide (¬ s.head? = some true ∧ s.count true = k ∧ adj s = m)) ∘
      (true :: ·)) (seqs n) = 0 := by
    rw [List.countP_eq_zero]; intro s _; simp
  rw [this, add_zero]
  apply List.countP_congr; intro s _; simp [adj_false_cons]

theorem c1_succ_zero (n m : ℕ) : c1 (n + 1) 0 m = 0 := by
  simp only [c1, seqs, List.countP_append, List.countP_map, List.countP_eq_zero, add_eq_zero]
  constructor <;> intro s _ <;> simp

theorem c1_succ_succ (n k m : ℕ) :
    c1 (n + 1) (k + 1) m = (if m = 0 then 0 else c1 n k (m - 1)) + c0 n k m := by
  simp only [c1, c0, seqs, List.countP_append, List.countP_map]
  have h0 : List.countP ((fun s => decide (s.head? = some true ∧ s.count true = k + 1 ∧
      adj s = m)) ∘ (false :: ·)) (seqs n) = 0 := by
    rw [List.countP_eq_zero]; intro s _; simp
  rw [h0, zero_add, countP_split _ _ (fun s => decide (s.head? = some true))]
  congr 1
  · split
    · rw [List.countP_eq_zero]; intro s _ hs
      subst_vars
      simp only [Function.comp, adj_true_cons, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨h1, -, -, h3⟩ := hs
      simp [h1] at h3
    · apply List.countP_congr; intro s _
      simp only [Function.comp, adj_true_cons, Bool.and_eq_true, decide_eq_true_eq,
        List.count_cons_self, List.head?_cons, true_and, add_left_inj]
      constructor
      · rintro ⟨h1, h2, h3⟩; simp [h1] at h3; exact ⟨h1, h2, by omega⟩
      · rintro ⟨h1, h2, h3⟩; simp [h1]; exact ⟨h2, by omega⟩
  · apply List.countP_congr; intro s _
    simp only [Function.comp, adj_true_cons, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, List.count_cons_self, List.head?_cons,
      true_and, add_left_inj]
    constructor
    · rintro ⟨h1, h2, h3⟩; simp [h1] at h3; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; simp [h1]; exact ⟨h2, h3⟩

/-- closed form, not starting with `true` -/
def g0 (n k m : ℕ) : ℕ := if k ≤ n then (k - 1).choose m * (n - k).choose (k - m) else 0
/-- closed form, starting with `true` -/
def g1 (n k m : ℕ) : ℕ :=
  if 1 ≤ k ∧ k ≤ n then (k - 1).choose m * (n - k).choose (k - 1 - m) else 0
/-- **closed form**: # length-`n` Boolean sequences with `k` trues and `m` adjacent true-true
    pairs, `C(k-1, m) * C(n+1-k, k-m)` (Nat subtraction; `k = 0` gives `[m = 0]`). -/
def adjCount (n k m : ℕ) : ℕ :=
  if k ≤ n then (k - 1).choose m * (n + 1 - k).choose (k - m) else 0

theorem g_add (n k m : ℕ) : g0 n k m + g1 n k m = adjCount n k m := by
  unfold g0 g1 adjCount
  by_cases hk : k ≤ n
  · rcases k with _ | k
    · simp
    · simp only [hk, le_add_iff_nonneg_left, zero_le, and_self, ite_true, add_tsub_cancel_right]
      by_cases hm : m ≤ k
      · have e1 : k + 1 - m = (k - m) + 1 := by omega
        have e2 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
        rw [e1, e2, Nat.choose_succ_succ]; ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : k < m)]; simp
  · simp [hk]

theorem g0_succ (n k m : ℕ) : g0 (n + 1) k m = adjCount n k m := by
  unfold g0 adjCount
  by_cases hk : k ≤ n
  · simp only [hk, ite_true, (by omega : k ≤ n + 1)]
  · by_cases hk' : k = n + 1
    · subst hk'
      simp only [le_refl, ite_true, hk, ite_false, Nat.sub_self, Nat.add_sub_cancel]
      by_cases hm : m ≤ n
      · rw [Nat.choose_eq_zero_of_lt (by omega : 0 < n + 1 - m)]; simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < m)]; simp
    · rw [if_neg hk, if_neg (by omega)]

theorem g1_succ_zero (n m : ℕ) : g1 (n + 1) 0 m = 0 := by simp [g1]

theorem g1_succ_succ (n k m : ℕ) :
    g1 (n + 1) (k + 1) m = (if m = 0 then 0 else g1 n k (m - 1)) + g0 n k m := by
  unfold g1 g0
  by_cases hk : k ≤ n
  · have e : n + 1 - (k + 1) = n - k := by omega
    simp only [le_add_iff_nonneg_left, zero_le, true_and, add_le_add_iff_right, hk, ite_true,
      add_tsub_cancel_right, e]
    rcases m with _ | m
    · simp
    · simp only [add_eq_zero, one_ne_zero, and_false, ite_false, add_tsub_cancel_right]
      rcases k with _ | k
      · simp
      · simp only [le_add_iff_nonneg_left, zero_le, true_and, hk, ite_true, add_tsub_cancel_right]
        rw [Nat.choose_succ_succ]
        have e2 : k + 1 - (m + 1) = k - m := by omega
        rw [e2]; ring
  · simp [hk]
    all_goals omega

theorem c_eq_g (n : ℕ) : ∀ k m, c0 n k m = g0 n k m ∧ c1 n k m = g1 n k m := by
  induction n with
  | zero =>
    intro k m
    refine ⟨?_, by rw [c1_zero]; unfold g1; rw [if_neg (by omega)]⟩
    rw [c0_zero]; unfold g0
    rcases k with _ | k
    · rcases m with _ | m <;> simp
    · simp
  | succ n ih =>
    intro k m
    refine ⟨?_, ?_⟩
    · rw [c0_succ, g0_succ, cnt_eq, (ih k m).1, (ih k m).2, g_add]
    · rcases k with _ | k
      · rw [c1_succ_zero, g1_succ_zero]
      · rw [c1_succ_succ, g1_succ_succ, (ih k m).1]
        split
        · rfl
        · rw [(ih k (m - 1)).2]

/-- **Exact count**: `#{s ∈ Bool^n : #trues = k, #adjacent true-true = m} = adjCount n k m`. -/
theorem cnt_eq_adjCount (n k m : ℕ) : cnt n k m = adjCount n k m := by
  rw [cnt_eq, (c_eq_g n k m).1, (c_eq_g n k m).2, g_add]

/-- number of length-`n` Boolean lists with `k` trues is `C(n, k)` -/
theorem countP_count_eq (n k : ℕ) :
    (seqs n).countP (fun s => s.count true = k) = n.choose k := by
  induction n generalizing k with
  | zero => rcases k with _ | k <;> simp [seqs]
  | succ n ih =>
    rw [seqs, List.countP_append, List.countP_map, List.countP_map]
    have hf : List.countP ((fun s => decide (s.count true = k)) ∘ (false :: ·)) (seqs n) =
        n.choose k := by
      rw [← ih k]; apply List.countP_congr; intro s _; simp
    rw [hf]
    rcases k with _ | k
    · rw [List.countP_eq_zero.mpr (by intro s _; simp)]; simp
    · have ht : List.countP ((fun s => decide (s.count true = k + 1)) ∘ (true :: ·)) (seqs n) =
          n.choose k := by
        rw [← ih k]; apply List.countP_congr; intro s _; simp
      rw [ht, Nat.choose_succ_succ]; ring

/-! ## 5. Exact p-value for the lag-1 clustering statistic -/

/-- exact upper-tail count `∑_{m₀ ≤ m ≤ k} adjCount n k m` -/
def adjTail (n k m₀ : ℕ) : ℕ := ∑ m ∈ range (k + 1), if m₀ ≤ m then adjCount n k m else 0

/-- `countP p` split by the value of a bounded statistic -/
theorem countP_fiberwise {γ : Type*} (l : List γ) (p : γ → Prop) [DecidablePred p] (f : γ → ℕ)
    (K : ℕ) (hf : ∀ a, p a → f a ≤ K) :
    l.countP (fun a => decide (p a)) =
      ∑ m ∈ range (K + 1), l.countP (fun a => decide (p a ∧ f a = m)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih, sum_add_distrib]
    congr 1
    by_cases hp : p a
    · have hm : f a ∈ range (K + 1) := mem_range.mpr (Nat.lt_succ_of_le (hf a hp))
      simp [hp, sum_ite_eq', hm, eq_comm]
    · simp [hp]

theorem countP_tail (n k m₀ : ℕ) :
    (seqs n).countP (fun s => decide (s.count true = k ∧ m₀ ≤ adj s)) = adjTail n k m₀ := by
  rw [countP_fiberwise _ (fun s => s.count true = k ∧ m₀ ≤ adj s) adj k
    (fun s hs => by rw [← hs.1]; exact adj_le_count s)]
  unfold adjTail
  apply sum_congr rfl
  intro m _
  split
  · rw [← cnt_eq_adjCount]; unfold cnt
    apply List.countP_congr; intro s _; simp; omega
  · rw [List.countP_eq_zero]; intro s _; simp; omega

/-- lag-1 statistic on `Fin n → Bool` -/
def adjF {n : ℕ} (x : Fin n → Bool) : ℕ := adj (List.ofFn x)

/-- **Exact permutation p-value of the lag-1 clustering statistic.** For any binary data `x` of
    length `n` with `k = ones x` trues and observed `m₀ = adjF x` adjacencies, the fraction of the
    `n!` permutations `π` with `adjF (x ∘ π) ≥ m₀` is exactly `adjTail n k m₀ / C(n, k)`. -/
theorem permPValue_adj {n : ℕ} (x : Fin n → Bool) :
    permPValue adjF x = (adjTail n (ones x) (adjF x) : ℚ) / (n.choose (ones x) : ℚ) := by
  rw [permPValue_eq_orbitPValue]
  unfold orbitPValue
  rw [orbit_eq_filter, filter_filter]
  have hnum : #{s : Fin n → Bool | ones s = ones x ∧ adjF x ≤ adjF s} = adjTail n (ones x) (adjF x) := by
    rw [← countP_tail]
    rw [← card_filter_ofFn n (fun l => l.count true = ones x ∧ adjF x ≤ adj l)]
    congr 1; apply filter_congr; intro s _; simp [count_ofFn, adjF]
  have hden : #{s : Fin n → Bool | ones s = ones x} = n.choose (ones x) := by
    rw [← countP_count_eq]
    have := card_filter_ofFn n (fun l => l.count true = ones x)
    rw [← this]
    congr 1; apply filter_congr; intro s _; simp [count_ofFn]
  rw [hnum, hden]

/-- list form: for a Boolean list `l`, the exact p-value of its observed lag-1 count -/
theorem permPValue_adj_list (l : List Bool) :
    permPValue adjF l.get =
      (adjTail l.length (l.count true) (adj l) : ℚ) / (l.length.choose (l.count true) : ℚ) := by
  have h1 : List.ofFn l.get = l := List.ofFn_get l
  have h2 : ones l.get = l.count true := by rw [← count_ofFn, h1]
  have h3 : adjF l.get = adj l := by unfold adjF; rw [h1]
  rw [permPValue_adj, h2, h3]

/-- the p-value is positive and at most 1 -/
theorem adjTail_pos_le (n k m₀ : ℕ) (hk : k ≤ n) (hm : ∃ s ∈ seqs n, s.count true = k ∧ m₀ ≤ adj s) :
    0 < adjTail n k m₀ ∧ adjTail n k m₀ ≤ n.choose k := by
  rw [← countP_tail, ← countP_count_eq]
  refine ⟨List.countP_pos_iff.mpr (by simpa using hm), ?_⟩
  apply List.countP_mono_left; intro s _ h; simp at h ⊢; exact h.1

/-! ## 6. Fast evaluation for kernel computation -/

/-- `Nat.choose` via `descFactorial / factorial` (fast with kernel GMP arithmetic) -/
def chooseFast (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- `adjTail` with fast binomials (list fold), for `decide +kernel` -/
def adjTailFast (n k m₀ : ℕ) : ℕ :=
  ((List.range (k + 1)).map (fun m =>
    if m₀ ≤ m ∧ k ≤ n then chooseFast (k - 1) m * chooseFast (n + 1 - k) (k - m) else 0)).sum

theorem list_sum_range_map (f : ℕ → ℕ) (K : ℕ) :
    ((List.range K).map f).sum = ∑ i ∈ range K, f i := by
  induction K with
  | zero => simp
  | succ K ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem adjTailFast_eq (n k m₀ : ℕ) : adjTailFast n k m₀ = adjTail n k m₀ := by
  unfold adjTailFast adjTail adjCount
  rw [list_sum_range_map]
  apply sum_congr rfl
  intro m _
  simp only [chooseFast_eq]
  by_cases h1 : m₀ ≤ m <;> by_cases h2 : k ≤ n <;> simp [h1, h2]

end StatKit.Permutation
