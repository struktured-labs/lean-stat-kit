/-
  BTC example (illustration only; the core library is dataset-agnostic): exact permutation
  p-value for the round-3 TEST lag-1 clustering of big days (|return| > 10 %).
  TEST: n = 2444 days, k = 33 big days, m₀ = 4 big-day → big-day follow-ups (`Examples.Btc`).
  Null: all C(2444, 33) placements of the 33 big days are equally likely (exchangeability of the
  TEST indicator sequence, conditional on 33 big days). Not a forecast and not a trading signal.
-/
import StatKit.Permutation
import Examples.Btc.Clustering

open StatKit StatKit.Permutation

namespace Examples.Btc

/-- TEST big-day indicator sequence -/
def bigSeq : List Bool := test.map big

theorem bigSeq_stats : bigSeq.length = 2444 ∧ bigSeq.count true = 33 ∧ adj bigSeq = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bigSeq, List.length_map]; exact lengths.2.2
  · rw [bigSeq, List.count, List.countP_map, ← test_big]; rfl
  · rw [bigSeq, ← bothCount_eq_adj]; exact test_both

/-- exact upper-tail count `∑_{m=4}^{33} C(32, m) C(2412, 33 - m)` and `C(2444, 33)` -/
theorem tail_count : adjTailFast 2444 33 4 =
    451829951295811611815412187159825422599243264167574619629078827518581676 := by
  decide +kernel
theorem total_count : chooseFast 2444 33 =
    594854322119569493736162859848769453853556295224568152080972057120349040944 := by
  decide +kernel

/-- **Exact permutation p-value of the TEST lag-1 clustering** (proved, rational, reduced):
    the fraction of all 2444! permutations of the TEST big-day sequence with at least 4
    big→big follow-ups. ≈ 7.5956 × 10⁻⁴. -/
theorem test_clustering_pvalue : permPValue adjF bigSeq.get =
    871054795507765819404787578084125234291543573591286455302322051 /
      1146782563716190351837549810888705966372921069461479432491809942444 := by
  rw [permPValue_adj_list, bigSeq_stats.1, bigSeq_stats.2.1, bigSeq_stats.2.2, ← adjTailFast_eq,
    ← chooseFast_eq, tail_count, total_count]
  norm_num

theorem test_clustering_pvalue_bounds :
    7595 / 10000000 < permPValue adjF bigSeq.get ∧ permPValue adjF bigSeq.get < 7596 / 10000000 := by
  rw [test_clustering_pvalue]; constructor <;> norm_num

end Examples.Btc
