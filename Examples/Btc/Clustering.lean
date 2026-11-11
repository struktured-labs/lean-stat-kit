/-
  BTC example: re-derive the round-3 headline `test_clustering` with the generic kit only.
  Data: date and close columns of the round-1 canonical Bitstamp file (examples-data/btc_ohlc.csv,
  sha256 df6a3569…), emitted by tools/emit_csv_module.py; bytes checked by Examples/Btc/DataCheck.lean.
  Split (pre-registered in round 3, BTC PREREG3.md): TRAIN = returns dated ≤ 2019-12-31, TEST = later.
-/
import StatKit
import Examples.Btc.Data

open StatKit

namespace Examples.Btc

open Examples.Btc.Data

/-- 5365 daily simple returns -/
def rets : List ℚ := simpleReturns col_close
/-- each return dated by its later close -/
def datedRets : List (ℕ × ℚ) := dated col_date.tail rets

def trainD : List (ℕ × ℚ) := trainPart (·.1) 20191231 datedRets
def testD : List (ℕ × ℚ) := testPart (·.1) 20191231 datedRets
def train : List ℚ := trainD.map (·.2)
def test : List ℚ := testD.map (·.2)

/-- |r| > 10 % -/
def big (x : ℚ) : Bool := decide (1 / 10 < |x|)

set_option maxRecDepth 100000 in
theorem dates_sorted : keysSorted (·.1) datedRets = true := by decide +kernel
/-- the split is TRAIN-prefix ++ TEST-suffix of the dated returns -/
theorem split_prefix : trainD ++ testD = datedRets :=
  split_eq_of_keysSorted _ _ _ dates_sorted

set_option maxRecDepth 100000 in
theorem lengths : rets.length = 5365 ∧ train.length = 2921 ∧ test.length = 2444 := by decide +kernel

set_option maxRecDepth 100000 in
theorem test_big : test.countP big = 33 := by decide +kernel
set_option maxRecDepth 100000 in
theorem test_lead : leadCount big test = 33 := by decide +kernel
set_option maxRecDepth 100000 in
theorem test_both : bothCount big test = 4 := by decide +kernel

/-- round-3 `test_clustering`, re-derived: P̂(big next | big) = 4/33 is more than 8× and less than 9×
    the TEST base rate 33/2444. -/
theorem test_clustering :
    8 * ((test.countP big : ℚ) / test.length) < (bothCount big test : ℚ) / leadCount big test ∧
    (bothCount big test : ℚ) / leadCount big test < 9 * ((test.countP big : ℚ) / test.length) := by
  rw [test_big, test_lead, test_both, lengths.2.2]
  norm_num

end Examples.Btc
