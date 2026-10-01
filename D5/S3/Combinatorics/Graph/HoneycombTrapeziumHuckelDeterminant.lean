/- GID: D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Molinari's honeycomb trapezium determinant equals its reduced Pascal determinant. -/

/- Declaration classification:
   proof_shape: sourceT, sourceR, sourceTriangle, huckel, reducedPascal: definition
   proof_shape: claim: proposition definition (not a proof of claim)
   proof_shape: result: bind-only
   escape_witness: none; Pascal recurrence, sparse sums, block determinant identities and signs.
   admission_basis: open-problem-resolution (#11470; Proved)
   Direct frozen dependencies: none (pinned Mathlib only)
   Private theorem/lemma declarations: none; all proof scaffolding is local to result.
   Private definitions construct index maps, matrices and an invertibility instance, not proofs of Prop.
-/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.LinearCombination

open scoped Matrix

namespace D5.S3.Combinatorics.Graph.HoneycombTrapeziumHuckelDeterminant

private abbrev Row (k n : ℕ) := Fin (n + 1 - k)

private abbrev Site (k n : ℕ) := Σ m : Row k n, Fin (2 * (m.val + k) + 1)

private abbrev Blue (k n : ℕ) := Σ m : Row k n, Fin (m.val + k + 1)

private abbrev Red (k n : ℕ) := Σ m : Row k n, Fin (m.val + k)

def sourceT {R : Type*} [CommRing R] (x y : ℕ → R) (m i j : ℕ) : R :=
  if m = 0 then x 0 + y 0
  else if i + 1 = j ∨ j + 1 = i then 1
  else if i = 0 ∧ j = 2 * m then y m
  else if i = 2 * m ∧ j = 0 then x m
  else 0

def sourceR {R : Type*} [CommRing R] (i j : ℕ) : R :=
  if i % 2 = 1 ∧ i = j + 1 then 1 else 0

def sourceTriangle {R : Type*} [CommRing R] (n : ℕ) (x y : ℕ → R) :
    Matrix (Site 0 n) (Site 0 n) R := fun a b =>
  if a.1 = b.1 then sourceT x y a.1.val a.2.val b.2.val
  else if a.1.val = b.1.val + 1 then sourceR a.2.val b.2.val
  else if b.1.val = a.1.val + 1 then sourceR b.2.val a.2.val
  else 0

private abbrev retainedSite {k n : ℕ} (a : Site k n) : Site 0 n :=
  ⟨⟨a.1.val + k, by have := a.1.isLt; omega⟩, ⟨a.2.val, by simpa using a.2.isLt⟩⟩

def huckel {R : Type*} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
    Matrix (Site k n) (Site k n) R :=
  (sourceTriangle n x y).submatrix retainedSite retainedSite

def reducedPascal {R : Type*} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
    Matrix (Fin (n + 1 - k)) (Fin (n + 1 - k)) R := fun i j =>
  if i = j then x (n - i.val) + y (n - i.val)
  else if i.val < j.val then
    (-1 : R) ^ (j.val - i.val) * (Nat.choose (n - i.val) (j.val - i.val) : R) * y (n - i.val)
  else (Nat.choose (n - j.val) (i.val - j.val) : R) * x (n - j.val)

def claim : Prop :=
  ∀ (R : Type) [CommRing R] (k n : ℕ), k ≤ n → ∀ (x y : ℕ → R),
    (huckel k n x y).det = (reducedPascal k n x y).det

private abbrev blueSite {k n : ℕ} (a : Blue k n) : Site k n :=
  ⟨a.1, ⟨2 * a.2.val, by have := a.2.isLt; omega⟩⟩

private abbrev redSite {k n : ℕ} (a : Red k n) : Site k n :=
  ⟨a.1, ⟨2 * a.2.val + 1, by have := a.2.isLt; omega⟩⟩

private def colourEquiv (k n : ℕ) : Blue k n ⊕ Red k n ≃ Site k n where
  toFun := Sum.elim blueSite redSite
  invFun a := if h : a.2.val % 2 = 0 then
    Sum.inl ⟨a.1, ⟨a.2.val / 2, by have := a.2.isLt; omega⟩⟩
    else Sum.inr ⟨a.1, ⟨a.2.val / 2, by have := a.2.isLt; omega⟩⟩
  left_inv := by
    rintro (⟨m,j⟩ | ⟨m,j⟩)
    · simp [blueSite]
    · simp [redSite]
      apply Fin.ext
      simp only
      omega
  right_inv := by
    rintro ⟨m,i⟩
    dsimp
    split <;> dsimp [blueSite, redSite] <;> congr 1 <;>
      apply Fin.ext <;> simp only <;> omega

private def liftEntry {R : Type*} [CommRing R] (m j l : ℕ) : R :=
  if l ≤ m then (-1 : R) ^ j * (Nat.choose j (m - l) : R) else 0

private def kernelLift {R : Type*} [CommRing R] (k n : ℕ) :
    Matrix (Blue k n) (Row k n) R := fun a l =>
  liftEntry (a.1.val + k) a.2.val (l.val + k)

private abbrev horizontalLeft {k n : ℕ} (a : Red k n) : Blue k n :=
  ⟨a.1, ⟨a.2.val, by have := a.2.isLt; omega⟩⟩

private abbrev horizontalRight {k n : ℕ} (a : Red k n) : Blue k n :=
  ⟨a.1, ⟨a.2.val + 1, by have := a.2.isLt; omega⟩⟩

private abbrev verticalBlue {k n : ℕ} (a : Red k n) (h : 0 < a.1.val) : Blue k n :=
  ⟨⟨a.1.val - 1, by have := a.1.isLt; omega⟩,
    ⟨a.2.val, by dsimp; have := a.2.isLt; omega⟩⟩

private def incidence {R : Type*} [CommRing R] (k n : ℕ) :
    Matrix (Red k n) (Blue k n) R := fun a b =>
  (if b = horizontalLeft a then 1 else 0) +
  (if b = horizontalRight a then 1 else 0) +
  (if h : 0 < a.1.val then if b = verticalBlue a h then 1 else 0 else 0)

private def tailMatrix {R : Type*} [CommRing R] (k n : ℕ) :
    Matrix (Red k n) (Red k n) R := fun a b => incidence k n a (horizontalRight b)

private abbrev leftBlue {k n : ℕ} (m : Row k n) : Blue k n :=
  ⟨m,⟨0,by omega⟩⟩

private abbrev rightBlue {k n : ℕ} (m : Row k n) : Blue k n :=
  ⟨m,⟨m.val+k,by omega⟩⟩

private def blueFrame (k n : ℕ) : Row k n ⊕ Red k n ≃ Blue k n where
  toFun := Sum.elim leftBlue horizontalRight
  invFun a := if h : a.2.val = 0 then Sum.inl a.1
    else Sum.inr ⟨a.1,⟨a.2.val-1,by have := a.2.isLt; omega⟩⟩
  left_inv := by
    rintro (m | ⟨m,j⟩)
    · simp [leftBlue]
    · simp [horizontalRight]
  right_inv := by
    rintro ⟨m,j⟩
    dsimp
    split
    · rename_i h
      dsimp [leftBlue]
      apply congrArg (fun v : Fin (m.val+k+1) => (Sigma.mk m v : Blue k n))
      apply Fin.ext
      change 0 = j.val
      omega
    · rename_i h
      dsimp [horizontalRight]
      apply congrArg (fun v : Fin (m.val+k+1) => (Sigma.mk m v : Blue k n))
      apply Fin.ext
      change j.val-1+1 = j.val
      omega

private def kernelTail {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Red k n) (Row k n) R :=
  (kernelLift k n).submatrix horizontalRight id

private def incidenceLeft {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Red k n) (Row k n) R :=
  (incidence k n).submatrix id leftBlue

section AbstractSchur
variable {R p q : Type*} [CommRing R] [Fintype p] [Fintype q]
  [DecidableEq p] [DecidableEq q]

private def hyperbolic (A : Matrix q q R) : Matrix (q ⊕ q) (q ⊕ q) R :=
  Matrix.fromBlocks A 1 1 0

private def hyperbolicInverse (A : Matrix q q R) : Matrix (q ⊕ q) (q ⊕ q) R :=
  Matrix.fromBlocks 0 1 1 (-A)

@[instance_reducible] private def hyperbolicInvertible (A : Matrix q q R) : Invertible (hyperbolic A) :=
  invertibleOfLeftInverse _ (hyperbolicInverse A) <| by
    simp [hyperbolic, hyperbolicInverse, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

end AbstractSchur

private def pascalW {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Row k n) (Row k n) R :=
  fun m l => (-1 : R)^(m.val+k) * (Nat.choose (m.val+k) (l.val+k) : R)

private def pascalCore {R : Type*} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
    Matrix (Row k n) (Row k n) R :=
  Matrix.diagonal (fun m => y (m.val+k)) * pascalW k n +
  (pascalW k n)ᵀ * Matrix.diagonal (fun m => x (m.val+k))

private def columnSigns {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Row k n) (Row k n) R :=
  Matrix.diagonal (fun m => (-1 : R)^(m.val+k))

private def endpointLeft {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Blue k n) (Row k n) R :=
  fun a m => if a = leftBlue m then 1 else 0

private def endpointRight {R : Type*} [CommRing R] (k n : ℕ) : Matrix (Blue k n) (Row k n) R :=
  fun a m => if a = rightBlue m then 1 else 0

set_option maxHeartbeats 8000000 in
/-- Molinari's Conjecture 2 (the `claim`) holds; the proof is repository-produced. -/
theorem result : claim := by
  classical

  have lift_left {R : Type} [CommRing R] (m l : ℕ) :
      liftEntry (R := R) m 0 l = if m = l then 1 else 0 := by
    by_cases h : l ≤ m
    · by_cases he : m = l
      · simp [liftEntry, h, he]
      · have hd : 0 < m - l := by omega
        simp [liftEntry, h, he, Nat.choose_eq_zero_of_lt hd]
    · have he : m ≠ l := by omega
      simp [liftEntry, h, he]

  have lift_horizontal_bottom {R : Type} [CommRing R] (m j l : ℕ)
      (h : m ≤ l) :
      liftEntry (R := R) m j l + liftEntry (R := R) m (j + 1) l = 0 := by
    by_cases he : l = m
    · subst l
      simp [liftEntry, pow_succ]
    · have hl : ¬l ≤ m := by omega
      simp [liftEntry, hl]

  have lift_recurrence {R : Type} [CommRing R] (m j l : ℕ) (hm : 0 < m) :
      liftEntry (R := R) m j l + liftEntry (R := R) m (j + 1) l +
        liftEntry (R := R) (m - 1) j l = 0 := by
    by_cases hl : l ≤ m - 1
    · have hlm : l ≤ m := by omega
      have hd : m - l = (m - 1 - l) + 1 := by omega
      simp only [liftEntry, if_pos hl, if_pos hlm, hd, Nat.choose_succ_succ',
        Nat.cast_add, pow_succ]
      ring
    · have hml : m ≤ l := by omega
      rw [lift_horizontal_bottom m j l hml]
      simp [liftEntry, hl]

  have incidence_mul {R : Type} [CommRing R] {k n : ℕ}
      (U : Matrix (Blue k n) (Row k n) R) (a : Red k n) (l : Row k n) :
      (incidence (R := R) k n * U) a l = U (horizontalLeft a) l + U (horizontalRight a) l +
        (if h : 0 < a.1.val then U (verticalBlue a h) l else 0) := by
    classical
    simp only [Matrix.mul_apply, incidence, add_mul, Finset.sum_add_distrib]
    split <;> simp

  have kernel_lift_zero {R : Type} [CommRing R] (k n : ℕ) :
      incidence (R := R) k n * kernelLift (R := R) k n = 0 := by
    ext a l
    rw [incidence_mul]
    change liftEntry (a.1.val + k) a.2.val (l.val + k) +
      liftEntry (a.1.val + k) (a.2.val + 1) (l.val + k) +
      (if h : 0 < a.1.val then liftEntry (a.1.val - 1 + k) a.2.val (l.val + k) else 0) = 0
    split
    · rename_i h
      rw [show a.1.val - 1 + k = a.1.val + k - 1 by omega]
      exact lift_recurrence _ _ _ (by omega)
    · rename_i h
      have ha : a.1.val = 0 := by omega
      simp only [ha, zero_add, add_zero]
      exact lift_horizontal_bottom _ _ _ (by omega)

  have blue_eq_iff {k n : ℕ} (a b : Blue k n) :
      a = b ↔ a.1 = b.1 ∧ a.2.val = b.2.val := by
    rcases a with ⟨m,j⟩
    rcases b with ⟨t,v⟩
    constructor
    · intro h; cases h; exact ⟨rfl,rfl⟩
    · rintro ⟨h,hj⟩
      cases h
      congr 1
      exact Fin.ext hj

  have sourceT_red_blue {R : Type} [CommRing R] (x y : ℕ → R)
      (m j v : ℕ) (hj : j < m) :
      sourceT x y m (2*j+1) (2*v) = if v = j ∨ v = j+1 then 1 else 0 := by
    have hm : m ≠ 0 := by omega
    have h0 : 2*j+1 ≠ 0 := by omega
    have he : 2*j+1 ≠ 2*m := by omega
    have hadj : (2*j+1+1 = 2*v ∨ 2*v+1 = 2*j+1) ↔ (v = j ∨ v = j+1) := by omega
    simp only [sourceT, if_neg hm, hadj, h0, he, false_and, if_false]

  have sourceT_blue_red {R : Type} [CommRing R] (x y : ℕ → R)
      (m j v : ℕ) (hj : j < m) :
      sourceT x y m (2*v) (2*j+1) = if v = j ∨ v = j+1 then 1 else 0 := by
    have hm : m ≠ 0 := by omega
    have h0 : 2*j+1 ≠ 0 := by omega
    have he : 2*j+1 ≠ 2*m := by omega
    have hadj : (2*v+1 = 2*j+1 ∨ 2*j+1+1 = 2*v) ↔ (v = j ∨ v = j+1) := by omega
    simp only [sourceT, if_neg hm, hadj, h0, he, and_false, if_false]

  have sourceT_red_red {R : Type} [CommRing R] (x y : ℕ → R)
      (m j v : ℕ) (hj : j < m) (hv : v < m) :
      sourceT x y m (2*j+1) (2*v+1) = 0 := by
    unfold sourceT
    split_ifs <;> first | rfl | omega

  have sourceT_blue_blue {R : Type} [CommRing R] (x y : ℕ → R)
      (m j v : ℕ) (hj : j ≤ m) (hv : v ≤ m) :
      sourceT x y m (2*j) (2*v) =
        (if j = 0 ∧ v = m then y m else 0) + (if j = m ∧ v = 0 then x m else 0) := by
    unfold sourceT
    split_ifs <;> simp_all <;> first | omega | ring

  have huckel_red_red {R : Type} [CommRing R] {k n : ℕ} (x y : ℕ → R)
      (a b : Red k n) : huckel k n x y (redSite a) (redSite b) = 0 := by
    have ha := a.2.isLt
    have hb := b.2.isLt
    have hab : 2*a.2.val+1 ≠ (2*b.2.val+1)+1 := by omega
    have hba : 2*b.2.val+1 ≠ (2*a.2.val+1)+1 := by omega
    simp only [huckel, Matrix.submatrix_apply, sourceTriangle, retainedSite, redSite,
      Fin.mk.injEq, Nat.add_zero]
    by_cases h : a.1.val + k = b.1.val + k
    · rw [if_pos h]
      exact sourceT_red_red x y _ _ _ ha (by omega)
    · have hrow : a.1.val ≠ b.1.val := by omega
      have hcross1 : 2*a.2.val ≠ 2*b.2.val+1 := by omega
      have hcross2 : 2*b.2.val ≠ 2*a.2.val+1 := by omega
      simp [hrow, sourceR, hcross1, hcross2]

  have incidence_apply {R : Type} [CommRing R] {k n : ℕ}
      (a : Red k n) (b : Blue k n) :
      incidence (R := R) k n a b =
        (if b.1.val = a.1.val ∧ b.2.val = a.2.val then 1 else 0) +
        (if b.1.val = a.1.val ∧ b.2.val = a.2.val+1 then 1 else 0) +
        (if 0 < a.1.val ∧ b.1.val = a.1.val-1 ∧ b.2.val = a.2.val then 1 else 0) := by
    classical
    unfold incidence
    by_cases h : 0 < a.1.val
    · simp [h, blue_eq_iff, horizontalLeft, horizontalRight, verticalBlue, Fin.ext_iff]
    · simp [h, blue_eq_iff, horizontalLeft, horizontalRight, Fin.ext_iff]

  have huckel_red_blue {R : Type} [CommRing R] {k n : ℕ} (x y : ℕ → R)
      (a : Red k n) (b : Blue k n) :
      huckel k n x y (redSite a) (blueSite b) = incidence (R := R) k n a b := by
    have ha := a.2.isLt
    simp only [huckel, Matrix.submatrix_apply, sourceTriangle, retainedSite, redSite, blueSite,
      Fin.mk.injEq, Nat.add_zero]
    rw [incidence_apply]
    have hrb : sourceR (R := R) (2*a.2.val+1) (2*b.2.val) =
        if b.2.val = a.2.val then 1 else 0 := by
      have he : 2*a.2.val+1 = 2*b.2.val+1 ↔ b.2.val = a.2.val := by omega
      simp [sourceR, eq_comm]
    have hbr : sourceR (R := R) (2*b.2.val) (2*a.2.val+1) = 0 := by simp [sourceR]
    rw [hrb, hbr]
    by_cases h : a.1.val = b.1.val
    · have he : a.1.val+k = b.1.val+k := by omega
      rw [if_pos he, sourceT_red_blue x y _ _ _ ha]
      have hd : ¬(0 < a.1.val ∧ b.1.val = a.1.val-1 ∧ b.2.val = a.2.val) := by omega
      simp only [h, true_and, if_neg hd, add_zero]
      by_cases h1 : b.2.val = a.2.val <;> by_cases h2 : b.2.val = a.2.val+1 <;>
        simp_all
    · have he : a.1.val+k ≠ b.1.val+k := by omega
      have hrev : b.1.val ≠ a.1.val := by omega
      have hd : a.1.val+k = b.1.val+k+1 ↔ 0 < a.1.val ∧ b.1.val = a.1.val-1 := by omega
      simp only [if_neg he, hrev, false_and, if_false, zero_add, hd]
      try simp only [ite_self]
      split_ifs <;> first | rfl | tauto | omega

  have huckel_blue_red {R : Type} [CommRing R] {k n : ℕ} (x y : ℕ → R)
      (a : Blue k n) (b : Red k n) :
      huckel k n x y (blueSite a) (redSite b) = incidence (R := R) k n b a := by
    have hb := b.2.isLt
    simp only [huckel, Matrix.submatrix_apply, sourceTriangle, retainedSite, redSite, blueSite,
      Fin.mk.injEq, Nat.add_zero]
    rw [incidence_apply]
    have hrb : sourceR (R := R) (2*b.2.val+1) (2*a.2.val) =
        if a.2.val = b.2.val then 1 else 0 := by
      have he : 2*b.2.val+1 = 2*a.2.val+1 ↔ a.2.val = b.2.val := by omega
      simp [sourceR, eq_comm]
    have hbr : sourceR (R := R) (2*a.2.val) (2*b.2.val+1) = 0 := by simp [sourceR]
    rw [hrb, hbr]
    by_cases h : a.1.val = b.1.val
    · have he : a.1.val+k = b.1.val+k := by omega
      rw [if_pos he, sourceT_blue_red x y _ _ _ (by omega)]
      have hd : ¬(0 < b.1.val ∧ a.1.val = b.1.val-1 ∧ a.2.val = b.2.val) := by omega
      simp only [h, true_and, if_neg hd, add_zero]
      by_cases h1 : a.2.val = b.2.val <;> by_cases h2 : a.2.val = b.2.val+1 <;> simp_all
    · have he : a.1.val+k ≠ b.1.val+k := by omega
      have hd : b.1.val+k = a.1.val+k+1 ↔ 0 < b.1.val ∧ a.1.val = b.1.val-1 := by omega
      simp only [if_neg he, h, false_and, if_false, zero_add, hd]
      try simp only [ite_self]
      split_ifs <;> first | rfl | tauto | omega

  have two_colour {R : Type} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
      (huckel k n x y).submatrix (colourEquiv k n) (colourEquiv k n) =
      Matrix.fromBlocks ((huckel k n x y).submatrix blueSite blueSite)
        (incidence (R := R) k n)ᵀ (incidence (R := R) k n) 0 := by
    ext (a|a) (b|b)
    · rfl
    · exact huckel_blue_red x y a b
    · exact huckel_red_blue x y a b
    · exact huckel_red_red x y a b

  have tail_diagonal {R : Type} [CommRing R] (k n : ℕ) (a : Red k n) :
      tailMatrix (R := R) k n a a = 1 := by
    rw [tailMatrix, incidence_apply]
    dsimp [horizontalRight]
    have h1 : a.2.val+1 ≠ a.2.val := by omega
    have hv : ¬(0 < a.1.val ∧ a.1.val = a.1.val-1 ∧ a.2.val+1 = a.2.val) := by omega
    simp [h1, hv]

  have tail_det {R : Type} [CommRing R] (k n : ℕ) :
      (tailMatrix (R := R) k n).det = 1 := by
    classical
    let key : Red k n → Lex (ℕ × ℕ) := fun a => toLex (a.1.val,a.2.val)
    have hinj : Function.Injective key := by
      rintro ⟨m,j⟩ ⟨t,v⟩ h
      have hm : m.val = t.val := congrArg (fun a => (ofLex a).1) h
      have hj : j.val = v.val := congrArg (fun a => (ofLex a).2) h
      have hmt : m = t := Fin.ext hm
      cases hmt
      congr 1
      exact Fin.ext hj
    letI : LinearOrder (Red k n) := LinearOrder.lift' key hinj
    have htri : (tailMatrix (R := R) k n).IsLowerTriangular := by
      intro a b h
      change key a < key b at h
      rw [Prod.Lex.toLex_lt_toLex] at h
      rw [tailMatrix, incidence_apply]
      dsimp [horizontalRight]
      have h1 : ¬(b.1.val = a.1.val ∧ b.2.val+1 = a.2.val) := by dsimp [key] at h; omega
      have h2 : ¬(b.1.val = a.1.val ∧ b.2.val+1 = a.2.val+1) := by dsimp [key] at h; omega
      have h3 : ¬(0 < a.1.val ∧ b.1.val = a.1.val-1 ∧ b.2.val+1 = a.2.val) := by
        dsimp [key] at h; omega
      simp [h1, h2, h3]
      intro hm hj
      dsimp at h
      omega
    rw [Matrix.det_of_isLowerTriangular _ htri]
    simp [tail_diagonal]

  have kernel_frame {R : Type} [CommRing R] (k n : ℕ) :
      (kernelLift (R := R) k n).submatrix (blueFrame k n) id =
      Matrix.fromRows 1 (kernelTail k n) := by
    ext (a|a) l
    · change liftEntry (a.val+k) 0 (l.val+k) = (1 : Matrix (Row k n) (Row k n) R) a l
      rw [lift_left,Matrix.one_apply]
      simp only [Fin.ext_iff,Nat.add_right_cancel_iff]
    · rfl

  have incidence_frame {R : Type} [CommRing R] (k n : ℕ) :
      (incidence (R := R) k n).submatrix id (blueFrame k n) =
      Matrix.fromCols (incidenceLeft k n) (tailMatrix k n) := by
    ext a (b|b) <;> rfl

  have frame_kernel_zero {R : Type} [CommRing R] (k n : ℕ) :
      incidenceLeft (R := R) k n + tailMatrix k n * kernelTail k n = 0 := by
    have h := Matrix.submatrix_mul_equiv (incidence (R := R) k n) (kernelLift k n)
      id (blueFrame k n) id
    rw [incidence_frame,kernel_frame,Matrix.fromCols_mul_fromRows,Matrix.mul_one,
      kernel_lift_zero] at h
    simpa using h

  have hyperbolic_inv {R q : Type} [CommRing R] [Fintype q] [DecidableEq q] (A : Matrix q q R) [Invertible (hyperbolic A)] :
      ⅟(hyperbolic A) = hyperbolicInverse A := by
    exact invOf_eq_right_inv (by simp [hyperbolic, hyperbolicInverse,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])

  have hyperbolic_det {R q : Type} [CommRing R] [Fintype q] [DecidableEq q] (A : Matrix q q R) :
      (hyperbolic A).det = (-1 : R) ^ Fintype.card q := by
    have hmul (T : Matrix q q R) :
        Matrix.fromBlocks 1 T 0 1 * hyperbolic (0 : Matrix q q R) = hyperbolic T := by
      simp [hyperbolic, Matrix.fromBlocks_multiply]
    have hdet (T : Matrix q q R) : (hyperbolic T).det = (hyperbolic (0 : Matrix q q R)).det := by
      rw [← hmul T, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
      simp
    rw [hdet A, ← hdet (1 : Matrix q q R)]
    simp [hyperbolic, Matrix.det_fromBlocks_one₁₁, Matrix.det_neg]

  have schur_hyperbolic {R p q : Type} [CommRing R] [Fintype p] [Fintype q]
      [DecidableEq p] [DecidableEq q] (C : Matrix p p R) (D : Matrix p q R)
      (E : Matrix q p R) (A : Matrix q q R) :
      (Matrix.fromBlocks C (Matrix.fromCols D 0) (Matrix.fromRows E 0)
        (hyperbolic A)).det = (-1 : R) ^ Fintype.card q * C.det := by
    letI := hyperbolicInvertible A
    rw [Matrix.det_fromBlocks₂₂, hyperbolic_det, hyperbolic_inv]
    congr 1
    have hzero : Matrix.fromCols D (0 : Matrix p q R) * hyperbolicInverse A *
        Matrix.fromRows E (0 : Matrix q p R) = 0 := by
      simp [hyperbolicInverse, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    rw [hzero, sub_zero]

  have schur_tail {R p q : Type} [CommRing R] [Fintype p] [Fintype q]
      [DecidableEq p] [DecidableEq q] (C : Matrix p p R) (D : Matrix p q R)
      (E : Matrix q p R) (A F : Matrix q q R) (hF : F.det = 1) :
      (Matrix.fromBlocks C (Matrix.fromCols D 0) (Matrix.fromRows E 0)
        (Matrix.fromBlocks A Fᵀ F 0)).det = (-1 : R) ^ Fintype.card q * C.det := by
    have hu : IsUnit F.det := by simp [hF]
    have hfi : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ hu
    have hfit : Fᵀ * (F⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hfi, Matrix.transpose_one]
    have hdi : F⁻¹.det = 1 := by
      have h := congrArg Matrix.det hfi
      simpa [Matrix.det_mul, hF] using h
    let P : Matrix (p ⊕ (q ⊕ q)) (p ⊕ (q ⊕ q)) R :=
      Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks 1 0 0 F⁻¹)
    let H := Matrix.fromBlocks C (Matrix.fromCols D (0 : Matrix p q R))
      (Matrix.fromRows E (0 : Matrix q p R)) (Matrix.fromBlocks A Fᵀ F 0)
    have hp : P.det = 1 := by
      simp [P, Matrix.det_fromBlocks_zero₂₁, hdi]
    have heq : P * H * Pᵀ = Matrix.fromBlocks C (Matrix.fromCols D 0)
        (Matrix.fromRows E 0) (hyperbolic A) := by
      simp [P, H, Matrix.fromBlocks_multiply, Matrix.fromBlocks_mul_fromRows,
        Matrix.fromCols_mul_fromBlocks, Matrix.fromBlocks_transpose,
        hfi, hfit, hyperbolic]
    have hd := congrArg Matrix.det heq
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hp, one_mul, mul_one] at hd
    exact hd.trans (schur_hyperbolic C D E A)

  have kernel_compression {R p q : Type} [CommRing R] [Fintype p] [Fintype q]
      [DecidableEq p] [DecidableEq q] (X : Matrix (p ⊕ q) (p ⊕ q) R)
      (K : Matrix q p R) (BL : Matrix q p R) (F : Matrix q q R)
      (hkernel : BL + F*K = 0) (hF : F.det = 1) :
      (Matrix.fromBlocks X (Matrix.fromCols BL F)ᵀ (Matrix.fromCols BL F) 0).det =
        (-1 : R)^Fintype.card q * ((Matrix.fromRows 1 K)ᵀ * X * Matrix.fromRows 1 K).det := by
    let Q : Matrix (p ⊕ q) (p ⊕ q) R := Matrix.fromBlocks 1 0 K 1
    let P : Matrix ((p ⊕ q) ⊕ q) ((p ⊕ q) ⊕ q) R := Matrix.fromBlocks Q 0 0 1
    let B := Matrix.fromCols BL F
    let H : Matrix ((p ⊕ q) ⊕ q) ((p ⊕ q) ⊕ q) R := Matrix.fromBlocks X Bᵀ B 0
    let Y := Qᵀ * X * Q
    have hP : P.det = 1 := by simp [P,Q,Matrix.det_fromBlocks_zero₂₁,Matrix.det_fromBlocks_zero₁₂]
    have hBQ : B * Q = Matrix.fromCols (0 : Matrix q p R) F := by
      simp [B,Q,Matrix.fromCols_mul_fromBlocks,hkernel]
    have hH : Pᵀ * H * P = Matrix.fromBlocks Y
        (Matrix.fromCols (0 : Matrix q p R) F)ᵀ (Matrix.fromCols 0 F) 0 := by
      simp [P,H,Y,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,
        ← Matrix.transpose_mul,hBQ,Matrix.mul_assoc]
    have hdet : H.det = (Matrix.fromBlocks Y
        (Matrix.fromCols (0 : Matrix q p R) F)ᵀ (Matrix.fromCols 0 F) 0).det := by
      have h := congrArg Matrix.det hH
      simpa [Matrix.det_mul,Matrix.det_transpose,hP] using h
    have hassoc : (Matrix.fromBlocks Y
        (Matrix.fromCols (0 : Matrix q p R) F)ᵀ (Matrix.fromCols 0 F) 0).submatrix
        (Equiv.sumAssoc p q q).symm (Equiv.sumAssoc p q q).symm =
        Matrix.fromBlocks Y.toBlocks₁₁ (Matrix.fromCols Y.toBlocks₁₂ 0)
          (Matrix.fromRows Y.toBlocks₂₁ 0) (Matrix.fromBlocks Y.toBlocks₂₂ Fᵀ F 0) := by
      ext (i | i | i) (j | j | j) <;> rfl
    have hC : Y.toBlocks₁₁ = (Matrix.fromRows 1 K)ᵀ * X * Matrix.fromRows 1 K := by
      dsimp [Y,Q]
      rw [← Matrix.fromBlocks_toBlocks X]
      simp [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,
        Matrix.transpose_fromRows,Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows]
    change H.det = _
    rw [hdet, ← Matrix.det_submatrix_equiv_self (Equiv.sumAssoc p q q).symm,
      hassoc,schur_tail,hC]
    exact hF

  have lift_right {R : Type} [CommRing R] (m l : ℕ) :
      liftEntry (R := R) m m l = (-1 : R)^m * (Nat.choose m l : R) := by
    by_cases h : l ≤ m
    · simp only [liftEntry, if_pos h]
      rw [Nat.choose_symm h]
    · have hz : Nat.choose m l = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [liftEntry, h, hz]

  have sign_twice {R : Type} [CommRing R] (m : ℕ) :
      (-1 : R)^m * (-1 : R)^m = 1 := by
    rw [← mul_pow]
    simp

  have sign_difference {R : Type} [CommRing R] (m l : ℕ) (h : l ≤ m) :
      (-1 : R)^m * (-1 : R)^l = (-1 : R)^(m-l) := by
    rw [← pow_add, show m+l = (m-l)+2*l by omega, pow_add, pow_mul]
    simp

  have pascal_identification {R : Type} [CommRing R] (k n : ℕ) (hkn : k ≤ n)
      (x y : ℕ → R) :
      (pascalCore k n x y * columnSigns k n).submatrix Fin.rev Fin.rev = reducedPascal k n x y := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    have hri : i.rev.val + k = n - i.val := by simp only [Fin.val_rev]; omega
    have hrj : j.rev.val + k = n - j.val := by simp only [Fin.val_rev]; omega
    simp only [Matrix.submatrix_apply, pascalCore, columnSigns, Matrix.add_mul,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.transpose_apply,
      pascalW, hri, hrj, reducedPascal]
    by_cases he : i = j
    · subst j
      simp [Nat.choose_self]
      have hs := sign_twice (R := R) (n-i.val)
      linear_combination (x (n-i.val)+y (n-i.val)) * hs
    · rw [if_neg he]
      by_cases hij : i.val < j.val
      · rw [if_pos hij]
        have hzero : Nat.choose (n-j.val) (n-i.val) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have hd : (n-i.val) - (n-j.val) = j.val - i.val := by omega
        have hs := sign_difference (R := R) (n-i.val) (n-j.val) (by omega)
        simp only [hzero, Nat.cast_zero, mul_zero, zero_mul, add_zero]
        have hc : Nat.choose (n-i.val) (n-j.val) = Nat.choose (n-i.val) (j.val-i.val) := by
          rw [← Nat.choose_symm (by omega : n-j.val ≤ n-i.val)]
          congr 1 <;> omega
        rw [hc, ← hd, ← hs]
        ring
      · rw [if_neg hij]
        have hji : j.val < i.val := by have hv : i.val ≠ j.val := fun h => he (Fin.ext h); omega
        have hzero : Nat.choose (n-i.val) (n-j.val) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp only [hzero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
        have hc : Nat.choose (n-j.val) (n-i.val) = Nat.choose (n-j.val) (i.val-j.val) := by
          rw [← Nat.choose_symm (by omega : n-i.val ≤ n-j.val)]
          congr 1 <;> omega
        rw [hc]
        have hs := sign_twice (R := R) (n-j.val)
        linear_combination (Nat.choose (n-j.val) (i.val-j.val) : R) * x (n-j.val) * hs

  have endpoint_left_kernel {R : Type} [CommRing R] (k n : ℕ) :
      (endpointLeft (R := R) k n)ᵀ * kernelLift (R := R) k n = 1 := by
    classical
    ext m l
    simp only [Matrix.mul_apply,Matrix.transpose_apply,endpointLeft,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simp [kernelLift,leftBlue,lift_left,Matrix.one_apply,Fin.ext_iff]

  have endpoint_right_kernel {R : Type} [CommRing R] (k n : ℕ) :
      (endpointRight (R := R) k n)ᵀ * kernelLift (R := R) k n = pascalW k n := by
    classical
    ext m l
    simp only [Matrix.mul_apply,Matrix.transpose_apply,endpointRight,ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    exact lift_right _ _

  have huckel_blue_blue {R : Type} [CommRing R] {k n : ℕ} (x y : ℕ → R)
      (a b : Blue k n) : huckel k n x y (blueSite a) (blueSite b) =
      (if a.1 = b.1 ∧ a.2.val = 0 ∧ b.2.val = a.1.val+k then y (a.1.val+k) else 0) +
      (if a.1 = b.1 ∧ a.2.val = a.1.val+k ∧ b.2.val = 0 then x (a.1.val+k) else 0) := by
    have ha := a.2.isLt
    have hb := b.2.isLt
    simp only [huckel,Matrix.submatrix_apply,sourceTriangle,blueSite,Fin.mk.injEq]
    by_cases h : a.1 = b.1
    · have hv : a.1.val+k = b.1.val+k := by simp [h]
      rw [if_pos hv,sourceT_blue_blue x y _ _ _ (by omega) (by omega)]
      simp [h]
    · have hv : a.1.val+k ≠ b.1.val+k := by intro he; apply h; apply Fin.ext; omega
      have hval : a.1.val ≠ b.1.val := fun he => h (Fin.ext he)
      simp [h,hval,sourceR]

  have boundary_factorization {R : Type} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
      (huckel k n x y).submatrix blueSite blueSite =
        endpointLeft k n * Matrix.diagonal (fun m : Row k n => y (m.val+k)) * (endpointRight k n)ᵀ +
        endpointRight k n * Matrix.diagonal (fun m : Row k n => x (m.val+k)) * (endpointLeft k n)ᵀ := by
    classical
    ext a b
    rw [Matrix.submatrix_apply,huckel_blue_blue]
    simp only [Matrix.add_apply]
    congr 1
    · rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply,endpointLeft,endpointRight,blue_eq_iff]
      rw [Finset.sum_eq_single a.1]
      · by_cases hrow : a.1 = b.1 <;> by_cases hj : a.2.val = 0 <;>
          by_cases he : b.2.val = a.1.val+k <;> simp [hrow, hj, he, eq_comm]
      · intro m hm hne
        have hneq : a.1 ≠ m := Ne.symm hne
        simp [hneq]
      · simp
    · rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply,endpointLeft,endpointRight,blue_eq_iff]
      rw [Finset.sum_eq_single a.1]
      · by_cases hrow : a.1 = b.1 <;> by_cases hj : a.2.val = a.1.val+k <;>
          by_cases he : b.2.val = 0 <;> simp [hrow, hj, he, eq_comm]
      · intro m hm hne
        have hneq : a.1 ≠ m := Ne.symm hne
        simp [hneq]
      · simp

  have compressed_boundary {R : Type} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
      (kernelLift (R := R) k n)ᵀ * (huckel k n x y).submatrix blueSite blueSite * kernelLift k n =
      pascalCore k n x y := by
    rw [boundary_factorization]
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc,pascalCore]
    have hL := endpoint_left_kernel (R := R) k n
    have hR := endpoint_right_kernel (R := R) k n
    have hLt : (kernelLift (R := R) k n)ᵀ * endpointLeft (R := R) k n = (1 : Matrix (Row k n) (Row k n) R) := by
      simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hL
    have hRt : (kernelLift (R := R) k n)ᵀ * endpointRight (R := R) k n = (pascalW k n)ᵀ := by
      simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hR
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hLt,Matrix.one_mul,hR]
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hRt,hL,Matrix.mul_one]

  have huckel_reduction {R : Type} [CommRing R] (k n : ℕ) (x y : ℕ → R) :
      (huckel k n x y).det = (-1 : R)^Fintype.card (Red k n) * (pascalCore k n x y).det := by
    classical
    let X := (huckel k n x y).submatrix blueSite blueSite
    let Xf := X.submatrix (blueFrame k n) (blueFrame k n)
    let B := incidence (R := R) k n
    let H := Matrix.fromBlocks X Bᵀ B (0 : Matrix (Red k n) (Red k n) R)
    let e := Equiv.sumCongr (blueFrame k n) (Equiv.refl (Red k n))
    have hh : (huckel k n x y).det = H.det := by
      rw [← Matrix.det_submatrix_equiv_self (colourEquiv k n),two_colour]
    have hframe : H.submatrix e e = Matrix.fromBlocks Xf
        (Matrix.fromCols (incidenceLeft k n) (tailMatrix k n))ᵀ
        (Matrix.fromCols (incidenceLeft k n) (tailMatrix k n)) 0 := by
      have hb := incidence_frame (R := R) k n
      ext (a|a) (b|b)
      · rfl
      · exact congrFun (congrFun hb b) a
      · exact congrFun (congrFun hb a) b
      · rfl
    have hc : (Matrix.fromRows 1 (kernelTail (R := R) k n))ᵀ * Xf * Matrix.fromRows 1 (kernelTail k n) =
        pascalCore k n x y := by
      rw [← kernel_frame]
      dsimp [Xf,X]
      rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
      exact compressed_boundary k n x y
    rw [hh,← Matrix.det_submatrix_equiv_self e,hframe,
      kernel_compression _ _ _ _ (frame_kernel_zero k n) (tail_det k n),hc]

  have column_sign_det {R : Type} [CommRing R] (k n : ℕ) :
      (columnSigns (R := R) k n).det = (-1 : R)^Fintype.card (Red k n) := by
    rw [columnSigns,Matrix.det_diagonal,Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Red,Fintype.card_sigma]

  intro R _ k n hkn x y
  rw [huckel_reduction]
  have hid := congrArg Matrix.det (pascal_identification k n hkn x y)
  let rev : Row k n ≃ Row k n := ⟨Fin.rev,Fin.rev,Fin.rev_rev,Fin.rev_rev⟩
  have hdet : (reducedPascal k n x y).det =
      (pascalCore k n x y).det * (columnSigns (R := R) k n).det := by
    rw [← hid]
    change ((pascalCore k n x y * columnSigns k n).submatrix rev rev).det = _
    rw [Matrix.det_submatrix_equiv_self,Matrix.det_mul]
  rw [hdet,column_sign_det]
  exact mul_comm _ _

end D5.S3.Combinatorics.Graph.HoneycombTrapeziumHuckelDeterminant
