/- GID: D5/S3/Combinatorics/LatinHTransversals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinHTransversals
   mirror-E: none(waiver:explicit-source-family-and-coordinate-certificates)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Literal H-family increments and affine cap certificates for three transversals. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinHTransversals

def order (k : ℕ) : ℕ := 4 * k

/-- The standard residue, including negative raw cap columns. -/
def residue (k : ℕ) (hk : 9 ≤ k) (x : ℤ) : Fin (order k) :=
  ⟨(x % (order k)).toNat, by
    have hp : (0 : ℤ) < order k := by dsimp [order]; omega
    have hlt := Int.emod_lt_of_pos x hp
    omega⟩

/-- Equation (7), evaluated on standard representatives in priority order. -/
def delta (k : ℕ) (a b : Fin (order k)) : ℤ :=
  let x : ℤ := a.val
  let y : ℤ := b.val
  if (a.val = 0 ∨ a.val = 5 ∨ a.val = 10) ∧ b.val % 4 = 1 ∧
      y - 4 * x / 5 ≠ 1 then 4
  else if (a.val = 1 ∧ b.val = 1) ∨ (a.val = 6 ∧ b.val = 5) ∨
      (a.val = 11 ∧ b.val = 9) then 3
  else if (a.val = 0 ∨ a.val = 5 ∨ a.val = 10) ∧
      1 ≤ y - 4 * x / 5 ∧ y - 4 * x / 5 ≤ 4 then 1
  else if (a.val = 1 ∨ a.val = 6 ∨ a.val = 11) ∧
      2 ≤ y - 4 * (x - 1) / 5 ∧ y - 4 * (x - 1) / 5 ≤ 4 then -1
  else if (a.val = 4 ∨ a.val = 9 ∨ a.val = 14) ∧ b.val % 4 = 1 then -4
  else if 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = 3 ∧
      b.val % 2 = 0 then 2
  else if 15 ≤ a.val ∧ a.val < order k - 21 ∧ a.val % 4 = 1 ∧
      b.val % 2 = 0 then -2
  else 0

def square (k : ℕ) (hk : 9 ≤ k) (a b : Fin (order k)) : Fin (order k) :=
  residue k hk ((a.val : ℤ) + (b.val : ℤ) + delta k a b)

def shift (j : Fin 3) : ℤ := if j.val = 1 then -4 else 0

def bulkColumnRaw (k : ℕ) (j : Fin 3) (t r : ℕ) : ℤ :=
  match r with
  | 0 => 12 + shift j - 2 * (t : ℤ)
  | 1 => 2 * (k : ℤ) + 10 + shift j - 2 * (t : ℤ)
  | 2 => -1 + shift j - 2 * (t : ℤ)
  | _ => 2 * (k : ℤ) + 1 + shift j - 2 * (t : ℤ)

def bulkSymbolRaw (k : ℕ) (j : Fin 3) (t r : ℕ) : ℤ :=
  match r with
  | 0 => 29 + shift j + 2 * (t : ℤ)
  | 1 => 2 * (k : ℤ) + 26 + shift j + 2 * (t : ℤ)
  | 2 => 16 + shift j + 2 * (t : ℤ)
  | _ => 2 * (k : ℤ) + 19 + shift j + 2 * (t : ℤ)

/-- The literal cap columns, as affine pairs `(coefficient of k, constant)`. -/
def capTable : Array (Array (ℤ × ℤ)) := #[
  #[(0,13),(0,17),(0,5),(0,5),(0,9),(0,9)],
  #[(0,18),(0,18),(0,1),(0,1),(0,1),(0,1)],
  #[(0,3),(0,11),(0,13),(2,7),(0,7),(0,19)],
  #[(2,9),(0,7),(0,3),(0,3),(0,16),(0,16)],
  #[(2,16),(2,16),(2,12),(2,12),(2,16),(0,7)],
  #[(2,5),(2,3),(2,1),(2,-1),(2,5),(2,3)],
  #[(0,5),(0,5),(0,11),(0,11),(0,5),(0,5)],
  #[(2,3),(2,7),(0,14),(0,14),(0,18),(0,18)],
  #[(2,14),(2,14),(2,10),(0,7),(2,14),(2,14)],
  #[(0,16),(0,16),(0,10),(0,10),(0,14),(0,14)],
  #[(0,1),(0,1),(0,-3),(0,-3),(0,13),(0,13)],
  #[(0,9),(0,9),(0,9),(0,9),(2,7),(2,9)],
  #[(2,12),(2,12),(2,8),(2,8),(2,12),(2,12)],
  #[(0,14),(0,14),(2,-1),(2,1),(2,3),(2,5)],
  #[(0,7),(0,3),(0,-1),(0,-1),(0,3),(0,3)],
  #[(0,22),(0,22),(0,18),(0,18),(0,22),(0,22)],
  #[(2,24),(0,28),(2,18),(2,26),(2,24),(0,28)],
  #[(0,26),(0,24),(0,20),(0,20),(0,26),(0,26)],
  #[(2,26),(2,24),(0,22),(0,22),(2,26),(2,20)],
  #[(0,28),(0,26),(2,26),(0,24),(2,30),(2,28)],
  #[(2,22),(2,26),(2,20),(2,14),(0,24),(2,16)],
  #[(0,24),(2,30),(2,11),(2,11),(2,15),(2,13)],
  #[(2,30),(2,18),(0,24),(0,13),(2,20),(2,30)],
  #[(2,15),(0,20),(2,7),(0,16),(2,28),(2,26)],
  #[(0,20),(0,15),(0,15),(2,16),(2,22),(0,24)],
  #[(2,11),(2,9),(2,22),(2,5),(2,9),(2,15)],
  #[(2,28),(2,28),(2,24),(2,20),(0,20),(0,20)],
  #[(2,7),(2,11),(0,16),(2,22),(2,11),(2,24)],
  #[(0,11),(0,19),(0,7),(2,10),(0,11),(0,11)],
  #[(0,17),(2,15),(2,13),(2,18),(0,28),(2,17)],
  #[(0,19),(2,22),(2,14),(2,24),(0,17),(0,15)],
  #[(2,20),(2,5),(2,5),(0,15),(2,17),(2,22)],
  #[(2,17),(2,17),(0,12),(0,12),(0,19),(2,18)],
  #[(0,15),(2,20),(2,16),(2,3),(0,15),(2,11)],
  #[(2,13),(2,13),(2,9),(2,9),(2,13),(0,17)],
  #[(2,18),(0,13),(2,3),(2,13),(2,18),(2,7)]
]

def capAffine (j : Fin 3) (odd : Bool) (i : Fin 36) : ℤ × ℤ :=
  (capTable.getD i.val #[]).getD (2 * j.val + if odd then 1 else 0) (0, 0)

def capEpsilon (j : Fin 3) (i : Fin 36) : ℤ :=
  if i.val = 0 ∨ i.val = 5 ∨ i.val = 10 then 4
  else if (i.val = 1 ∧ j.val ≠ 0) ∨ (i.val = 6 ∧ j.val ≠ 1) ∨
      (i.val = 11 ∧ j.val ≠ 2) then 3
  else 0

/-- Tail rows contribute `-ell` after reduction of `4k-ell` modulo `4k`. -/
def capSymbolAffine (j : Fin 3) (odd : Bool) (i : Fin 36) : ℤ × ℤ :=
  let p := capAffine j odd i
  (p.1, p.2 + if i.val < 15 then (i.val : ℤ) + capEpsilon j i
             else (i.val : ℤ) - 36)

def capColumnComplement (s : ℤ) : List (ℤ × ℤ) :=
  ((List.range 8).map (fun u : ℕ => ((0 : ℤ), 14 + s + 2 * (u : ℤ)))) ++
  ((List.range 10).map (fun u : ℕ => ((2 : ℤ), 12 + s + 2 * (u : ℤ)))) ++
  ((List.range 10).map (fun u : ℕ => ((0 : ℤ), 1 + s + 2 * (u : ℤ)))) ++
  ((List.range 8).map (fun u : ℕ => ((2 : ℤ), 3 + s + 2 * (u : ℤ))))

def capSymbolComplement (s : ℤ) : List (ℤ × ℤ) :=
  ((List.range 4).map (fun u : ℕ => ((0 : ℤ), 8 + s + 2 * (u : ℤ)))) ++
  ((List.range 14).map (fun u : ℕ => ((2 : ℤ), -2 + s + 2 * (u : ℤ)))) ++
  ((List.range 14).map (fun u : ℕ => ((0 : ℤ), 1 + s + 2 * (u : ℤ)))) ++
  ((List.range 4).map (fun u : ℕ => ((2 : ℤ), 11 + s + 2 * (u : ℤ))))

def columnRaw (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) : ℤ :=
  let odd := k % 2 = 1
  if h : a.val < 15 then
    let p := capAffine j odd ⟨a.val, by omega⟩
    p.1 * (k : ℤ) + p.2
  else if htail : order k - 21 ≤ a.val then
    let i : Fin 36 := ⟨a.val - (order k - 21) + 15, by
      have := a.isLt
      dsimp [order] at *
      omega⟩
    let p := capAffine j odd i
    p.1 * (k : ℤ) + p.2
  else
    bulkColumnRaw k j ((a.val - 15) / 4) ((a.val - 15) % 4)

def symbolRaw (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) : ℤ :=
  let odd := k % 2 = 1
  if h : a.val < 15 then
    (a.val : ℤ) + columnRaw k hk j a + capEpsilon j ⟨a.val, by omega⟩
  else if order k - 21 ≤ a.val then
    (a.val : ℤ) + columnRaw k hk j a
  else
    bulkSymbolRaw k j ((a.val - 15) / 4) ((a.val - 15) % 4)

def column (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) := residue k hk (columnRaw k hk j a)

def symbol (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) := residue k hk (symbolRaw k hk j a)

def entry (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) (a : Fin (order k)) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (a, column k hk j a, symbol k hk j a)

def T (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Set (Fin (order k) × Fin (order k) × Fin (order k)) :=
  Set.range (entry k hk j)

def d0 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 1, residue k hk 1, residue k hk 5)

def d1 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 6, residue k hk 5, residue k hk 14)

def d2 (k : ℕ) (hk : 9 ≤ k) :
    Fin (order k) × Fin (order k) × Fin (order k) :=
  (residue k hk 11, residue k hk 9, residue k hk 23)

def D (k : ℕ) (hk : 9 ≤ k) :
    Finset (Fin (order k) × Fin (order k) × Fin (order k)) :=
  {d0 k hk, d1 k hk, d2 k hk}

def IsTransversal (k : ℕ) (hk : 9 ≤ k)
    (T : Set (Fin (order k) × Fin (order k) × Fin (order k))) : Prop :=
  (∀ e ∈ T, e.2.2 = square k hk e.1 e.2.1) ∧
  (∀ a, ∃! e, e ∈ T ∧ e.1 = a) ∧
  (∀ b, ∃! e, e ∈ T ∧ e.2.1 = b) ∧
  (∀ c, ∃! e, e ∈ T ∧ e.2.2 = c)

def IsPinned (k : ℕ) (hk : 9 ≤ k)
    (e : Fin (order k) × Fin (order k) × Fin (order k)) : Prop :=
  (∃ T, IsTransversal k hk T) ∧ ∀ T, IsTransversal k hk T → e ∈ T

def bulkRow (k : ℕ) (hk : 9 ≤ k) (t : Fin (k - 9)) (r : Fin 4) :
    Fin (order k) :=
  ⟨15 + 4 * t.val + r.val, by
    have ht := t.isLt
    have hr := r.isLt
    dsimp [order]
    omega⟩


def headRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 15) : Fin (order k) :=
  ⟨i.val, by dsimp [order]; omega⟩


def tailRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 21) : Fin (order k) :=
  ⟨order k - 21 + i.val, by dsimp [order]; omega⟩



/-- Distinct bulk rows of one profile use distinct columns for every admissible order. -/
theorem bulk_column_injective (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Function.Injective (fun p : Fin (k - 9) × Fin 4 =>
      column k hk j (bulkRow k hk p.1 p.2)) := by
  intro ⟨t, r⟩ ⟨u, v⟩ heq
  have ht : t.val + 9 < k := by have := t.isLt; omega
  have hu : u.val + 9 < k := by have := u.isLt; omega
  have hraw (w : Fin (k - 9)) (s : Fin 4) :
      column k hk j (bulkRow k hk w s) =
        residue k hk (bulkColumnRaw k j w.val s.val) := by
    have hw : w.val + 9 < k := by have := w.isLt; omega
    have hs : s.val < 4 := s.isLt
    have hlo : 15 ≤ (bulkRow k hk w s).val := by dsimp [bulkRow]; omega
    have hhi : (bulkRow k hk w s).val < order k - 21 := by
      dsimp [bulkRow, order]
      omega
    have hquot : ((bulkRow k hk w s).val - 15) / 4 = w.val := by
      dsimp [bulkRow]
      omega
    have hrem : ((bulkRow k hk w s).val - 15) % 4 = s.val := by
      dsimp [bulkRow]
      omega
    simp [column, columnRaw, not_lt.mpr hlo, Nat.not_le.mpr hhi,
      hquot, hrem]
  change column k hk j (bulkRow k hk t r) =
    column k hk j (bulkRow k hk u v) at heq
  rw [hraw t r, hraw u v] at heq
  let x := bulkColumnRaw k j t.val r.val
  let y := bulkColumnRaw k j u.val v.val
  have hx : -(order k : ℤ) < x ∧ x < order k := by
    fin_cases r <;> fin_cases j <;>
      simp [x, bulkColumnRaw, shift, order] <;> omega
  have hy : -(order k : ℤ) < y ∧ y < order k := by
    fin_cases v <;> fin_cases j <;>
      simp [y, bulkColumnRaw, shift, order] <;> omega
  have hvalue (z : ℤ) (hz : -(order k : ℤ) < z ∧ z < order k) :
      ((residue k hk z).val : ℤ) =
        if z < 0 then z + order k else z := by
    have hn : 0 ≤ z % (order k : ℤ) :=
      Int.emod_nonneg _ (by dsimp [order]; omega)
    have hv : ((residue k hk z).val : ℤ) = z % (order k : ℤ) := by
      simp [residue, Int.toNat_of_nonneg hn]
    rw [hv]
    by_cases hneg : z < 0
    · have hstep : 0 ≤ z + order k ∧ z + order k < order k := by omega
      rw [if_pos hneg, show z % (order k : ℤ) =
        (z + order k) % (order k : ℤ) by simp,
        Int.emod_eq_of_lt hstep.1 hstep.2]
    · have hnonneg : 0 ≤ z := by omega
      rw [if_neg hneg, Int.emod_eq_of_lt hnonneg hz.2]
  have heq' : (if x < 0 then x + order k else x) =
      (if y < 0 then y + order k else y) := by
    have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
    simpa [x, y, hvalue x hx, hvalue y hy] using hv
  have htv : t.val = u.val ∧ r.val = v.val := by
    fin_cases r <;> fin_cases v <;> fin_cases j
    all_goals simp [x, y, bulkColumnRaw, shift, order] at heq' ⊢
    all_goals split_ifs at heq' <;> omega
  cases t
  cases u
  cases r
  cases v
  simp_all

/-- Distinct bulk rows of one profile use distinct symbols for every admissible order. -/
theorem bulk_symbol_injective (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Function.Injective (fun p : Fin (k - 9) × Fin 4 =>
      symbol k hk j (bulkRow k hk p.1 p.2)) := by
  intro ⟨t, r⟩ ⟨u, v⟩ heq
  have ht : t.val + 9 < k := by have := t.isLt; omega
  have hu : u.val + 9 < k := by have := u.isLt; omega
  have hraw (w : Fin (k - 9)) (s : Fin 4) :
      symbol k hk j (bulkRow k hk w s) =
        residue k hk (bulkSymbolRaw k j w.val s.val) := by
    have hw : w.val + 9 < k := by have := w.isLt; omega
    have hs : s.val < 4 := s.isLt
    have hlo : 15 ≤ (bulkRow k hk w s).val := by dsimp [bulkRow]; omega
    have hhi : (bulkRow k hk w s).val < order k - 21 := by
      dsimp [bulkRow, order]
      omega
    have hquot : ((bulkRow k hk w s).val - 15) / 4 = w.val := by
      dsimp [bulkRow]
      omega
    have hrem : ((bulkRow k hk w s).val - 15) % 4 = s.val := by
      dsimp [bulkRow]
      omega
    simp [symbol, symbolRaw, not_lt.mpr hlo, Nat.not_le.mpr hhi,
      hquot, hrem]
  change symbol k hk j (bulkRow k hk t r) =
    symbol k hk j (bulkRow k hk u v) at heq
  rw [hraw t r, hraw u v] at heq
  let x := bulkSymbolRaw k j t.val r.val
  let y := bulkSymbolRaw k j u.val v.val
  have hx : 0 ≤ x ∧ x < 2 * (order k : ℤ) := by
    fin_cases r <;> fin_cases j <;>
      simp [x, bulkSymbolRaw, shift, order] <;> omega
  have hy : 0 ≤ y ∧ y < 2 * (order k : ℤ) := by
    fin_cases v <;> fin_cases j <;>
      simp [y, bulkSymbolRaw, shift, order] <;> omega
  have hvalue (z : ℤ) (hz : 0 ≤ z ∧ z < 2 * (order k : ℤ)) :
      ((residue k hk z).val : ℤ) =
        if z < order k then z else z - order k := by
    have hn : 0 ≤ z % (order k : ℤ) :=
      Int.emod_nonneg _ (by dsimp [order]; omega)
    have hv : ((residue k hk z).val : ℤ) = z % (order k : ℤ) := by
      simp [residue, Int.toNat_of_nonneg hn]
    rw [hv]
    by_cases hsmall : z < order k
    · rw [if_pos hsmall, Int.emod_eq_of_lt hz.1 hsmall]
    · have hstep : 0 ≤ z - order k ∧ z - order k < order k := by omega
      rw [if_neg hsmall, show z % (order k : ℤ) =
        (z - order k) % (order k : ℤ) by simp,
        Int.emod_eq_of_lt hstep.1 hstep.2]
  have heq' : (if x < order k then x else x - order k) =
      (if y < order k then y else y - order k) := by
    have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
    simpa [x, y, hvalue x hx, hvalue y hy] using hv
  have htv : t.val = u.val ∧ r.val = v.val := by
    fin_cases r <;> fin_cases v <;> fin_cases j
    all_goals simp [x, y, bulkSymbolRaw, shift, order] at heq' ⊢
    all_goals split_ifs at heq' <;> omega
  cases t
  cases u
  cases r
  cases v
  simp_all

def capRow (k : ℕ) (hk : 9 ≤ k) (i : Fin 36) : Fin (order k) :=
  ⟨if i.val < 15 then i.val else order k - 36 + i.val, by
    have := i.isLt
    dsimp [order]
    split_ifs <;> omega⟩

set_option maxHeartbeats 3000000 in
-- The finite affine cap table and symbolic modulus are checked together.
/-- The literal cap columns have no repetitions, uniformly in the order. -/
theorem cap_column_injective (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Function.Injective (fun i : Fin 36 => column k hk j (capRow k hk i)) := by
  have hcap (i : Fin 36) :
      column k hk j (capRow k hk i) =
        let p := capAffine j (k % 2 = 1) i
        residue k hk (p.1 * (k : ℤ) + p.2) := by
    by_cases hi : i.val < 15
    · simp [column, columnRaw, capRow, hi]
    · have htail : order k - 21 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hhead : 15 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hind : (capRow k hk i).val - (order k - 21) + 15 = i.val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      simp [column, columnRaw, not_lt.mpr hhead, htail, hind]
  have hpair : Function.Injective (capAffine j (k % 2 = 1)) := by
    fin_cases j <;> by_cases hp : k % 2 = 1 <;>
      simp only [hp, decide_true, decide_false] <;> decide
  have hlisted (i : Fin 36) :
      capAffine j (k % 2 = 1) i ∈ capColumnComplement (shift j) := by
    have hp : List.Perm (List.ofFn (capAffine j (k % 2 = 1)))
        (capColumnComplement (shift j)) := by
      fin_cases j <;> by_cases hodd : k % 2 = 1 <;>
        simp only [hodd, decide_true, decide_false] <;> decide
    exact hp.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hmodinj (p q : ℤ × ℤ)
      (hp : p ∈ capColumnComplement (shift j))
      (hq : q ∈ capColumnComplement (shift j))
      (heq : residue k hk (p.1 * (k : ℤ) + p.2) =
        residue k hk (q.1 * (k : ℤ) + q.2)) : p = q := by
    let x := p.1 * (k : ℤ) + p.2
    let y := q.1 * (k : ℤ) + q.2
    have hs : shift j = 0 ∨ shift j = -4 := by fin_cases j <;> simp [shift]
    simp only [capColumnComplement, List.mem_append, List.mem_map,
      List.mem_range] at hp hq
    have hx : -(order k : ℤ) < x ∧ x < 2 * (order k : ℤ) := by
      rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals dsimp [x, order] <;> rcases hs with hs | hs <;>
        omega
    have hy : -(order k : ℤ) < y ∧ y < 2 * (order k : ℤ) := by
      rcases hq with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals dsimp [y, order] <;> rcases hs with hs | hs <;>
        omega
    have hvalue (z : ℤ) (hz : -(order k : ℤ) < z ∧
        z < 2 * (order k : ℤ)) :
        ((residue k hk z).val : ℤ) =
          if z < 0 then z + order k
          else if z < order k then z else z - order k := by
      have hn : 0 ≤ z % (order k : ℤ) :=
        Int.emod_nonneg _ (by dsimp [order]; omega)
      have hv : ((residue k hk z).val : ℤ) = z % (order k : ℤ) := by
        simp [residue, Int.toNat_of_nonneg hn]
      rw [hv]
      by_cases hneg : z < 0
      · have hstep : 0 ≤ z + order k ∧ z + order k < order k := by omega
        rw [if_pos hneg, show z % (order k : ℤ) =
          (z + order k) % (order k : ℤ) by simp,
          Int.emod_eq_of_lt hstep.1 hstep.2]
      · have hnonneg : 0 ≤ z := by omega
        rw [if_neg hneg]
        by_cases hsmall : z < order k
        · rw [if_pos hsmall, Int.emod_eq_of_lt hnonneg hsmall]
        · have hstep : 0 ≤ z - order k ∧ z - order k < order k := by omega
          rw [if_neg hsmall, show z % (order k : ℤ) =
            (z - order k) % (order k : ℤ) by simp,
            Int.emod_eq_of_lt hstep.1 hstep.2]
    have heq' :
        (if x < 0 then x + order k else if x < order k then x else x - order k) =
        (if y < 0 then y + order k else if y < order k then y else y - order k) := by
      have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
      simpa [x, y, hvalue x hx, hvalue y hy] using hv
    rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
      ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    all_goals rcases hq with (((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) |
      ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩)
    all_goals rcases hs with hs | hs
    all_goals simp [x, y, hs, order] at heq' ⊢
    all_goals split_ifs at heq' <;> omega
  intro i l heq
  change column k hk j (capRow k hk i) =
    column k hk j (capRow k hk l) at heq
  rw [hcap i, hcap l] at heq
  exact hpair (hmodinj _ _ (hlisted i) (hlisted l) heq)

set_option maxHeartbeats 3000000 in
-- The cap certificate reduces this unbounded claim to four affine symbol blocks.
/-- The literal cap symbols have no repetitions, uniformly in the order. -/
theorem cap_symbol_injective (k : ℕ) (hk : 9 ≤ k) (j : Fin 3) :
    Function.Injective (fun i : Fin 36 => symbol k hk j (capRow k hk i)) := by
  have hcap (i : Fin 36) :
      symbol k hk j (capRow k hk i) =
        let p := capSymbolAffine j (k % 2 = 1) i
        residue k hk (p.1 * (k : ℤ) + p.2) := by
    by_cases hi : i.val < 15
    · simp [symbol, symbolRaw, columnRaw, capSymbolAffine, capRow, hi]
      ring
    · have htail : order k - 21 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hhead : 15 ≤ (capRow k hk i).val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      have hind : (capRow k hk i).val - (order k - 21) + 15 = i.val := by
        dsimp [capRow, order]
        simp [hi]
        omega
      simp [symbol, symbolRaw, not_lt.mpr hhead, htail,
        columnRaw, hind, capSymbolAffine, hi]
      have hrow : ((capRow k hk i).val : ℤ) =
          (order k : ℤ) + (i.val : ℤ) - 36 := by
        dsimp [capRow, order]
        simp [hi]
        omega
      rw [hrow]
      have harg :
          (order k : ℤ) + (i.val : ℤ) - 36 +
              ((capAffine j (k % 2 = 1) i).1 * (k : ℤ) +
                (capAffine j (k % 2 = 1) i).2) =
          (order k : ℤ) +
              ((capAffine j (k % 2 = 1) i).1 * (k : ℤ) +
                ((capAffine j (k % 2 = 1) i).2 + ((i.val : ℤ) - 36))) := by
        ring
      rw [harg]
      have hperiod (z : ℤ) : residue k hk ((order k : ℤ) + z) =
          residue k hk z := by
        apply Fin.ext
        simp [residue]
      exact hperiod _
  have hpair : Function.Injective (capSymbolAffine j (k % 2 = 1)) := by
    fin_cases j <;> by_cases hp : k % 2 = 1 <;>
      simp only [hp, decide_true, decide_false] <;> decide
  have hlisted (i : Fin 36) :
      capSymbolAffine j (k % 2 = 1) i ∈ capSymbolComplement (shift j) := by
    have hp : List.Perm (List.ofFn (capSymbolAffine j (k % 2 = 1)))
        (capSymbolComplement (shift j)) := by
      fin_cases j <;> by_cases hodd : k % 2 = 1 <;>
        simp only [hodd, decide_true, decide_false] <;> decide
    exact hp.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hmodinj (p q : ℤ × ℤ)
      (hp : p ∈ capSymbolComplement (shift j))
      (hq : q ∈ capSymbolComplement (shift j))
      (heq : residue k hk (p.1 * (k : ℤ) + p.2) =
        residue k hk (q.1 * (k : ℤ) + q.2)) : p = q := by
    let x := p.1 * (k : ℤ) + p.2
    let y := q.1 * (k : ℤ) + q.2
    have hs : shift j = 0 ∨ shift j = -4 := by fin_cases j <;> simp [shift]
    simp only [capSymbolComplement, List.mem_append, List.mem_map,
      List.mem_range] at hp hq
    have hx : -(order k : ℤ) < x ∧ x < 2 * (order k : ℤ) := by
      rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals dsimp [x, order] <;> rcases hs with hs | hs <;> omega
    have hy : -(order k : ℤ) < y ∧ y < 2 * (order k : ℤ) := by
      rcases hq with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
      all_goals dsimp [y, order] <;> rcases hs with hs | hs <;> omega
    have hvalue (z : ℤ) (hz : -(order k : ℤ) < z ∧
        z < 2 * (order k : ℤ)) :
        ((residue k hk z).val : ℤ) =
          if z < 0 then z + order k
          else if z < order k then z else z - order k := by
      have hn : 0 ≤ z % (order k : ℤ) :=
        Int.emod_nonneg _ (by dsimp [order]; omega)
      have hv : ((residue k hk z).val : ℤ) = z % (order k : ℤ) := by
        simp [residue, Int.toNat_of_nonneg hn]
      rw [hv]
      by_cases hneg : z < 0
      · have hstep : 0 ≤ z + order k ∧ z + order k < order k := by omega
        rw [if_pos hneg, show z % (order k : ℤ) =
          (z + order k) % (order k : ℤ) by simp,
          Int.emod_eq_of_lt hstep.1 hstep.2]
      · have hnonneg : 0 ≤ z := by omega
        rw [if_neg hneg]
        by_cases hsmall : z < order k
        · rw [if_pos hsmall, Int.emod_eq_of_lt hnonneg hsmall]
        · have hstep : 0 ≤ z - order k ∧ z - order k < order k := by omega
          rw [if_neg hsmall, show z % (order k : ℤ) =
            (z - order k) % (order k : ℤ) by simp,
            Int.emod_eq_of_lt hstep.1 hstep.2]
    have heq' :
        (if x < 0 then x + order k else if x < order k then x else x - order k) =
        (if y < 0 then y + order k else if y < order k then y else y - order k) := by
      have hv := congrArg (fun z : Fin (order k) => (z.val : ℤ)) heq
      simpa [x, y, hvalue x hx, hvalue y hy] using hv
    rcases hp with (((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
      ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
    all_goals rcases hq with (((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) |
      ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩)
    all_goals rcases hs with hs | hs
    all_goals simp [x, y, hs, order] at heq' ⊢
    all_goals split_ifs at heq' <;> omega
  intro i l heq
  change symbol k hk j (capRow k hk i) =
    symbol k hk j (capRow k hk l) at heq
  rw [hcap i, hcap l] at heq
  exact hpair (hmodinj _ _ (hlisted i) (hlisted l) heq)

end D5.S3.Combinatorics.LatinHTransversals
