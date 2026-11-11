/-
  Synthetic example for `StatKit.Permutation` (exact permutation test of lag-1 clustering).
  (1) a 10-element toy Boolean sequence, with an independent brute-force cross-check over all 2^10
      sequences; (2) the up-day indicator of the 20-day toy price series of `Examples.Synthetic`.
-/
import StatKit.Permutation
import Examples.Synthetic.Claims

open StatKit StatKit.Permutation

namespace Examples.Synthetic

/-- toy sequence: 5 trues, 3 adjacent true-true pairs -/
def toy : List Bool := [true, true, false, true, true, true, false, false, false, false]

theorem toy_stats : toy.length = 10 ∧ toy.count true = 5 ∧ adj toy = 3 := by decide

/-- exact permutation p-value: of the 10! permutations of `toy`, a fraction exactly 11/42
    give at least 3 adjacencies (= (C(4,3)·C(6,2) + C(4,4)·C(6,1)) / C(10,5) = 66/252). -/
theorem toy_pvalue : permPValue adjF toy.get = 11 / 42 := by
  rw [permPValue_adj_list, toy_stats.1, toy_stats.2.1, toy_stats.2.2, ← adjTailFast_eq,
    ← chooseFast_eq]
  have h1 : adjTailFast 10 5 3 = 66 := by decide +kernel
  have h2 : chooseFast 10 5 = 252 := by decide +kernel
  rw [h1, h2]; norm_num

/-- independent cross-check by brute force over all 1024 length-10 Boolean lists -/
theorem toy_bruteforce :
    (seqs 10).countP (fun s => decide (s.count true = 5 ∧ 3 ≤ adj s)) = 66 ∧
    (seqs 10).countP (fun s => decide (s.count true = 5)) = 252 := by
  decide +kernel

/-- closed-form count vs brute force for every m on the toy size (n = 10, k = 5) -/
theorem toy_counts_bruteforce :
    ∀ m < 6, (seqs 10).countP (fun s => decide (s.count true = 5 ∧ adj s = m)) =
      chooseFast 4 m * chooseFast 6 (5 - m) := by
  decide +kernel

/-- the generic definition checked by direct kernel enumeration of all 4! = 24 permutations:
    12 of them keep at least one adjacency for `[true, true, false, false]`, so p = 12/24 = 1/2 -/
theorem tiny_perm_enumeration :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      adjF ![true, true, false, false] ≤ adjF (![true, true, false, false] ∘ π))).card = 12 := by
  decide +kernel

theorem tiny_pvalue_direct : permPValue adjF ![true, true, false, false] = 1 / 2 := by
  unfold permPValue
  rw [tiny_perm_enumeration]; norm_num [Nat.factorial]

/-- ... and the closed-form theorem gives the same value -/
theorem tiny_pvalue_closed_form :
    permPValue adjF ![true, true, false, false] = 3 / 6 := by
  rw [permPValue_adj]
  have h1 : ones ![true, true, false, false] = 2 := by decide
  have h2 : adjF ![true, true, false, false] = 1 := by decide
  rw [h1, h2, ← adjTailFast_eq, ← chooseFast_eq]
  have h3 : adjTailFast 4 2 1 = 3 := by decide +kernel
  have h4 : chooseFast 4 2 = 6 := by decide +kernel
  rw [h3, h4]; norm_num

/-- enumeration over all 5! = 120 permutations of `[true, false, true, true, false]` (k = 3,
    one adjacency): 108 permutations reach ≥ 1 adjacency; closed form (C(2,1)C(3,2)+C(2,2)C(3,1))/C(5,3)
    = 9/10 = 108/120. -/
theorem five_perm_enumeration :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 5) =>
      adjF ![true, false, true, true, false] ≤ adjF (![true, false, true, true, false] ∘ π))).card
      = 108 := by
  decide +kernel

/-- up-day indicator of the 19 toy returns -/
def up (x : ℚ) : Bool := decide (0 < x)
theorem up_stats : (rets.map up).length = 19 ∧ (rets.map up).count true = 10 ∧
    adj (rets.map up) = 2 := by
  decide +kernel

/-- exact permutation p-value for clustering of up-days in the toy series: 7099/7106 (no evidence
    of clustering; the toy series alternates). -/
theorem up_pvalue : permPValue adjF (rets.map up).get = 7099 / 7106 := by
  rw [permPValue_adj_list, up_stats.1, up_stats.2.1, up_stats.2.2, ← adjTailFast_eq,
    ← chooseFast_eq]
  have h1 : adjTailFast 19 10 2 = 92287 := by decide +kernel
  have h2 : chooseFast 19 10 = 92378 := by decide +kernel
  rw [h1, h2]; norm_num

/-- the kit's `bothCount` agrees: 2 up-up follow-ups -/
theorem up_both : bothCount up rets = 2 := by rw [bothCount_eq_adj]; exact up_stats.2.2

end Examples.Synthetic
