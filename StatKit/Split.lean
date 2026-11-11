/-
  StatKit.Split: pre-registered train/test split by a key (e.g. a YYYYMMDD date), dataset-agnostic.
  TRAIN = entries with key ≤ cut, TEST = entries with key > cut.
  * `split_perm`: TRAIN ++ TEST is a permutation of the data (nothing lost or duplicated).
  * `split_eq_of_sorted`: if keys are non-decreasing, TRAIN ++ TEST = data exactly (TRAIN is a prefix).
  * `train_keys`, `test_keys`: every TRAIN key ≤ cut < every TEST key.
-/
import Mathlib

namespace StatKit

def trainPart {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) : List α :=
  xs.filter (fun x => decide (key x ≤ cut))
def testPart {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) : List α :=
  xs.filter (fun x => !decide (key x ≤ cut))

theorem split_perm {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) :
    (trainPart key cut xs ++ testPart key cut xs).Perm xs := by
  unfold trainPart testPart
  exact List.filter_append_perm _ xs

theorem split_length {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) :
    (trainPart key cut xs).length + (testPart key cut xs).length = xs.length := by
  rw [← List.length_append]; exact (split_perm key cut xs).length_eq

theorem train_keys {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) :
    ∀ x ∈ trainPart key cut xs, key x ≤ cut := by
  intro x hx; simpa [trainPart] using (List.mem_filter.mp hx).2

theorem test_keys {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α) :
    ∀ x ∈ testPart key cut xs, cut < key x := by
  intro x hx; have := (List.mem_filter.mp hx).2; simp at this; omega

theorem split_eq_of_sorted {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α)
    (hs : xs.Pairwise (fun a b => key a ≤ key b)) :
    trainPart key cut xs ++ testPart key cut xs = xs := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    have ht := (List.pairwise_cons.mp hs)
    by_cases ha : key a ≤ cut
    · simp [trainPart, testPart, ha] at ih ⊢
      exact ih ht.2
    · have hall : ∀ b ∈ t, ¬ key b ≤ cut := fun b hb => by have := ht.1 b hb; omega
      have h1 : t.filter (fun x => decide (key x ≤ cut)) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; simpa using hall b hb
      have h2 : t.filter (fun x => !decide (key x ≤ cut)) = t := by
        rw [List.filter_eq_self]; intro b hb; simpa using hall b hb
      simp [trainPart, testPart, ha, h1, h2]

/-- linear-time Bool check that keys are non-decreasing (kernel-friendly) -/
def keysSorted {α : Type*} (key : α → ℕ) : List α → Bool
  | a :: b :: t => decide (key a ≤ key b) && keysSorted key (b :: t)
  | _ => true

theorem keysSorted_head {α : Type*} (key : α → ℕ) :
    ∀ {a : α} {t : List α}, keysSorted key (a :: t) = true → ∀ b ∈ t, key a ≤ key b
  | _, [], _ => by simp
  | a, b :: t, h => by
    simp only [keysSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact le_trans h.1 (keysSorted_head key h.2 c hc)

theorem keysSorted_tail {α : Type*} (key : α → ℕ) {a : α} {t : List α}
    (h : keysSorted key (a :: t) = true) : keysSorted key t = true := by
  cases t with
  | nil => rfl
  | cons b u => simp only [keysSorted, Bool.and_eq_true] at h; exact h.2

theorem keysSorted_pairwise {α : Type*} (key : α → ℕ) :
    ∀ xs : List α, keysSorted key xs = true → xs.Pairwise (fun a b => key a ≤ key b)
  | [], _ => List.Pairwise.nil
  | _ :: t, h => List.Pairwise.cons (keysSorted_head key h) (keysSorted_pairwise key t (keysSorted_tail key h))

/-- for data checked sorted by key, TRAIN is a prefix and TEST the remaining suffix -/
theorem split_eq_of_keysSorted {α : Type*} (key : α → ℕ) (cut : ℕ) (xs : List α)
    (h : keysSorted key xs = true) : trainPart key cut xs ++ testPart key cut xs = xs :=
  split_eq_of_sorted key cut xs (keysSorted_pairwise key xs h)

/-- dated values: pair each value with its date (dates and values aligned) -/
def dated {β : Type*} (dates : List ℕ) (vals : List β) : List (ℕ × β) := dates.zip vals

end StatKit
