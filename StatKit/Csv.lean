/-
  StatKit.Csv: verified ingestion of canonical numeric CSV (dataset-agnostic, core Lean only).
  Format: every row has exactly `k ≥ 1` fields, each a canonical unsigned decimal (no sign, no
  leading zeros except "0"), separated by ',' and terminated by '\n'.
  Main theorem `parseRows_iff`: the parser accepts a byte list iff it is the canonical print of a
  list of rows of arity k, and then returns exactly those rows (round trip + uniqueness).
  Fixed-point decimals are handled outside the proof by the generator (value = field / 10^scale).
-/

namespace StatKit.Csv

abbrev comma : UInt8 := 44
abbrev lf : UInt8 := 10

def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- little-endian decimal digits, canonical -/
def digitsLE (n : Nat) : List Nat :=
  if n < 10 then [n] else n % 10 :: digitsLE (n / 10)
decreasing_by omega

def toByte (d : Nat) : UInt8 := UInt8.ofNat (48 + d)

/-- canonical printer for one field -/
def printNat (n : Nat) : List UInt8 := ((digitsLE n).map toByte).reverse

/-- value of an ASCII digit string (big-endian) -/
def val (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 10 + (b.toNat - 48)) 0

/-- own span, so the proof does not depend on library lemma names -/
def spanDigits : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: bs => if isDigit b then
      let r := spanDigits bs; (b :: r.1, r.2) else ([], b :: bs)

/-- read one field terminated by `sep`; fail closed unless canonical -/
def parseField (sep : UInt8) (s : List UInt8) : Option (Nat × List UInt8) :=
  let r := spanDigits s
  match r.2 with
  | b :: rest => if b = sep ∧ printNat (val r.1) = r.1 then some (val r.1, rest) else none
  | [] => none


/-- canonical print of one row (fields joined by ',', terminated by '\n') -/
def printRow : List Nat → List UInt8
  | [] => []
  | [x] => printNat x ++ [lf]
  | x :: y :: t => printNat x ++ comma :: printRow (y :: t)

/-- parse one row of exactly `k` fields -/
def parseRowK : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, _ => none
  | 1, s => do
      let (x, s) ← parseField lf s
      pure ([x], s)
  | k + 2, s => do
      let (x, s) ← parseField comma s
      let (xs, s) ← parseRowK (k + 1) s
      pure (x :: xs, s)

def printRows (rows : List (List Nat)) : List UInt8 := rows.flatMap printRow

def parseRowsF (k : Nat) : Nat → List UInt8 → Option (List (List Nat))
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, s@(_ :: _) => do
      let (r, rest) ← parseRowK k s
      let rs ← parseRowsF k f rest
      pure (r :: rs)

/-- parse a whole file of arity-`k` rows (fuel = input length) -/
def parseRows (k : Nat) (s : List UInt8) : Option (List (List Nat)) := parseRowsF k s.length s

/-- convenience: bytes of a `String` -/
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

/-- column `j` of a row list (missing fields read as 0; for arity-checked rows never used) -/
def column (j : Nat) (rows : List (List Nat)) : List Nat := rows.map (fun r => r.getD j 0)

/-! ## Field-level lemmas -/

theorem digitsLE_lt (n : Nat) : ∀ d ∈ digitsLE n, d < 10 := by
  fun_induction digitsLE n with
  | case1 n h => intro d hd; simp at hd; omega
  | case2 n h ih =>
    intro d hd; simp at hd
    rcases hd with hd | hd
    · omega
    · exact ih d hd

theorem digitsLE_ne_nil (n : Nat) : digitsLE n ≠ [] := by
  rw [digitsLE.eq_def]; split <;> simp

def valLE : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * valLE ds

theorem valLE_digitsLE (n : Nat) : valLE (digitsLE n) = n := by
  fun_induction digitsLE n with
  | case1 n h => simp [valLE]
  | case2 n h ih => simp only [valLE, ih]; omega

theorem toByte_isDigit (d : Nat) (h : d < 10) : isDigit (toByte d) = true := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem toByte_val (d : Nat) (h : d < 10) : (toByte d).toNat - 48 = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem val_rev_map (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    val ((ds.map toByte).reverse) = valLE ds := by
  unfold val
  rw [List.foldl_reverse]
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.foldr_cons, valLE]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        toByte_val d (h d List.mem_cons_self)]
    omega

theorem val_printNat (n : Nat) : val (printNat n) = n := by
  unfold printNat; rw [val_rev_map _ (digitsLE_lt n), valLE_digitsLE]

theorem printNat_digits (n : Nat) : ∀ b ∈ printNat n, isDigit b = true := by
  intro b hb
  simp only [printNat, List.mem_reverse, List.mem_map] at hb
  obtain ⟨d, hd, rfl⟩ := hb
  exact toByte_isDigit d (digitsLE_lt n d hd)

theorem spanDigits_append (p rest : List UInt8) (hp : ∀ b ∈ p, isDigit b = true)
    (b : UInt8) (hb : isDigit b = false) :
    spanDigits (p ++ b :: rest) = (p, b :: rest) := by
  induction p with
  | nil => simp [spanDigits, hb]
  | cons x p ih =>
    simp only [List.cons_append, spanDigits, hp x List.mem_cons_self, ite_true]
    rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]

theorem spanDigits_spec (s : List UInt8) : (spanDigits s).1 ++ (spanDigits s).2 = s := by
  induction s with
  | nil => rfl
  | cons b bs ih => unfold spanDigits; split <;> simp [ih]

/-- round trip, one field -/
theorem parseField_print (sep : UInt8) (hsep : isDigit sep = false) (n : Nat) (rest : List UInt8) :
    parseField sep (printNat n ++ sep :: rest) = some (n, rest) := by
  unfold parseField
  rw [spanDigits_append _ _ (printNat_digits n) sep hsep]
  simp [val_printNat]

/-- uniqueness / soundness, one field: anything accepted is canonical -/
theorem parseField_sound (sep : UInt8) (s rest : List UInt8) (n : Nat) :
    parseField sep s = some (n, rest) → s = printNat n ++ sep :: rest := by
  unfold parseField
  have hs := spanDigits_spec s
  generalize spanDigits s = r at hs ⊢
  obtain ⟨p, q⟩ := r
  cases q with
  | nil => simp
  | cons b q =>
    simp only
    split
    · rename_i hc; intro h; simp at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hc2⟩ := hc; rw [hc2]; exact hs.symm
    · simp



theorem comma_nd : isDigit comma = false := by decide
theorem lf_nd : isDigit lf = false := by decide

theorem printRow_ne_nil (r : List Nat) (h : r ≠ []) : printRow r ≠ [] := by
  match r, h with
  | [x], _ => simp [printRow]
  | x :: y :: t, _ => simp [printRow]

theorem parseRowK_print (r : List Nat) (rest : List UInt8) :
    r ≠ [] → parseRowK r.length (printRow r ++ rest) = some (r, rest) := by
  induction r with
  | nil => intro h; exact absurd rfl h
  | cons x t ih =>
    intro _
    match t, ih with
    | [], _ =>
      simp only [List.length_singleton, printRow, List.append_assoc, List.cons_append, List.nil_append]
      simp [parseRowK, parseField_print _ lf_nd]
    | y :: u, ih =>
      have ih' := ih (by simp)
      simp only [List.length_cons] at ih' ⊢
      simp only [printRow, List.append_assoc, List.cons_append]
      simp only [parseRowK, parseField_print _ comma_nd]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show printRow (y :: u) ++ rest = printRow (y :: u) ++ rest from rfl, ih']
      rfl

theorem parseRowK_sound (k : Nat) (s rest : List UInt8) (r : List Nat) :
    parseRowK k s = some (r, rest) → r.length = k ∧ s = printRow r ++ rest := by
  induction k using Nat.strongRecOn generalizing s rest r with
  | ind k ih =>
    match k with
    | 0 => simp [parseRowK]
    | 1 =>
      intro h
      simp only [parseRowK, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x, s1⟩, h1, h2⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨rfl, ?_⟩
      rw [parseField_sound _ _ _ _ h1]; simp [printRow]
    | k + 2 =>
      intro h
      simp only [parseRowK, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x, s1⟩, h1, ⟨xs, s2⟩, h2, h3⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      simp only at h2
      obtain ⟨hl, hs⟩ := ih (k + 1) (by omega) _ _ _ h2
      refine ⟨by simp [hl], ?_⟩
      rw [parseField_sound _ _ _ _ h1, hs]
      match xs, hl with
      | y :: u, _ => simp [printRow]

theorem parseRowsF_print (k : Nat) (rows : List (List Nat)) (hk : ∀ r ∈ rows, r.length = k ∧ r ≠ [])
    (f : Nat) (hf : rows.length ≤ f) : parseRowsF k f (printRows rows) = some rows := by
  induction rows generalizing f with
  | nil => cases f <;> rfl
  | cons r rs ih =>
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨hlen, hne⟩ := hk r List.mem_cons_self
      have hpr := parseRowK_print r (printRows rs) hne
      rw [hlen] at hpr
      have hne' : printRows (r :: rs) ≠ [] := by
        simp only [printRows, List.flatMap_cons]
        intro h; exact printRow_ne_nil r hne (List.append_eq_nil_iff.mp h).1
      obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil hne'
      rw [hbt, parseRowsF, ← hbt]
      simp only [printRows, List.flatMap_cons] at hpr ⊢
      rw [hpr]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show List.flatMap printRow rs = printRows rs from rfl,
        ih (fun x hx => hk x (List.mem_cons_of_mem _ hx)) f (by simp at hf; omega)]
      rfl

theorem printRows_length_ge (rows : List (List Nat)) (hk : ∀ r ∈ rows, r ≠ []) :
    rows.length ≤ (printRows rows).length := by
  induction rows with
  | nil => simp [printRows]
  | cons r rs ih =>
    have := ih (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    simp only [printRows, List.flatMap_cons, List.length_append, List.length_cons] at this ⊢
    have : 0 < (printRow r).length := List.length_pos_iff.mpr (printRow_ne_nil r (hk r List.mem_cons_self))
    omega

theorem parseRowsF_sound (k : Nat) (f : Nat) (s : List UInt8) (rows : List (List Nat)) :
    parseRowsF k f s = some rows → (∀ r ∈ rows, r.length = k) ∧ printRows rows = s := by
  induction f generalizing s rows with
  | zero => cases s with
    | nil => intro h; simp [parseRowsF] at h; subst h; simp [printRows]
    | cons _ _ => simp [parseRowsF]
  | succ f ih => cases s with
    | nil => intro h; simp [parseRowsF] at h; subst h; simp [printRows]
    | cons b t =>
      intro h
      simp only [parseRowsF, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨r, rest⟩, h1, rs, h2, h3⟩ := h
      simp only [pure, Option.some.injEq] at h3; subst h3
      obtain ⟨hl, e1⟩ := parseRowK_sound _ _ _ _ h1
      obtain ⟨hall, e2⟩ := ih _ _ h2
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hl
        · exact hall x hx
      · simp only [printRows, List.flatMap_cons] at e2 ⊢
        rw [e1, e2]

/-- **Main theorem.** For arity `k ≥ 1`: the parser accepts `s` with result `rows` iff every row has
    exactly `k` fields and `s` is the canonical print of `rows`. -/
theorem parseRows_iff (k : Nat) (hk : 0 < k) (s : List UInt8) (rows : List (List Nat)) :
    parseRows k s = some rows ↔ (∀ r ∈ rows, r.length = k) ∧ printRows rows = s := by
  constructor
  · exact parseRowsF_sound _ _ _ _
  · rintro ⟨hl, rfl⟩
    have hne : ∀ r ∈ rows, r.length = k ∧ r ≠ [] := by
      intro r hr; refine ⟨hl r hr, ?_⟩; intro h; have := hl r hr; rw [h] at this; simp at this; omega
    exact parseRowsF_print k rows hne _ (printRows_length_ge rows (fun r hr => (hne r hr).2))

/-- corollary used by generated data modules: a successful parse pins the data to the bytes -/
theorem rows_of_parse {k : Nat} {s : List UInt8} {rows : List (List Nat)} (hk : 0 < k)
    (h : parseRows k s = some rows) : printRows rows = s ∧ ∀ r ∈ rows, r.length = k :=
  let ⟨a, b⟩ := (parseRows_iff k hk s rows).mp h; ⟨b, a⟩

end StatKit.Csv
