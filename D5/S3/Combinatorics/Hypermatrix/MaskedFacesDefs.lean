/- GID: D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypermatrix/MaskedFacesDefs
   mirror-E: none(waiver:noncomputable-finite-field-enumeration)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Matrix faces, antitone masks and the integral coefficient determinant. -/

import D5.S3.Combinatorics.Permutation.CoupledRepairedWeight
import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs

abbrev Faces (F : Type*) (k : ℕ) :=
  Matrix (Fin (k + 1)) (Fin k) F × Matrix (Fin (k + 1)) (Fin k) F

def Respects {F : Type*} [Zero F] {k : ℕ}
    (lam mu : Fin k → ℕ) (T : Faces F k) : Prop :=
  (∀ r j, k + 1 - lam j ≤ r.val → T.1 r j = 0) ∧
  (∀ r j, k + 1 - mu j ≤ r.val → T.2 r j = 0)

def ClosureFullRank {F : Type*} [Field F] {k : ℕ} (T : Faces F k) : Prop :=
  ∀ a b : AlgebraicClosure F, a ≠ 0 ∨ b ≠ 0 →
    (a • T.1.map (algebraMap F (AlgebraicClosure F)) +
      b • T.2.map (algebraMap F (AlgebraicClosure F))).rank = k

def ActualCarrier (F : Type*) [Field F] (k : ℕ) (lam mu : Fin k → ℕ) :=
  {T : Faces F k // Respects lam mu T ∧ ClosureFullRank T}

def qBracket (q n : ℕ) : ℕ := ∑ e ∈ Finset.range n, q ^ e

def E0 (F : Type*) [Zero F] [One F] (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin k) F := fun r j => if r = j.castSucc then 1 else 0

def E1 (F : Type*) [Zero F] [One F] (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin k) F := fun r j => if r = j.succ then 1 else 0


abbrev XVariables {k : ℕ} (sigma : Equiv.Perm (Fin (k+1))) :=
  {ab : Fin (k+1) × Fin (k+1) // ab.1 < ab.2 ∧ sigma ab.2 < sigma ab.1}
abbrev YVariables {k : ℕ} (pi : Equiv.Perm (Fin k)) :=
  {ij : Fin k × Fin k // ij.1 < ij.2 ∧ pi ij.2 < pi ij.1}
abbrev CellVariables {k : ℕ} (sigma : Equiv.Perm (Fin (k+1)))
    (pi : Equiv.Perm (Fin k)) := XVariables sigma ⊕ YVariables pi

def cellA {F : Type*} [Zero F] [One F] {k : ℕ}
    (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
    (z : CellVariables sigma pi → F) : Matrix (Fin (k+1)) (Fin (k+1)) F := by
  classical
  exact fun r b =>
    let a := sigma.symm r
    if a = b then 1 else
      if h : a < b ∧ sigma b < sigma a then z (.inl ⟨(a,b),h⟩) else 0

def cellB {F : Type*} [Zero F] [One F] {k : ℕ}
    (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
    (z : CellVariables sigma pi → F) : Matrix (Fin k) (Fin k) F := by
  classical
  exact fun a i =>
    let j := pi.symm a
    if i = j then 1 else
      if h : i < j ∧ pi j < pi i then z (.inr ⟨(i,j),h⟩) else 0

def SEShape {F : Type*} [Zero F] [One F] {k : ℕ}
    (sigma : Equiv.Perm (Fin (k+1)))
    (A : Matrix (Fin (k+1)) (Fin (k+1)) F) : Prop :=
  ∀ a b, A (sigma a) b = if a = b then 1 else
    if a < b ∧ sigma b < sigma a then A (sigma a) b else 0

def NWRightShape {F : Type*} [Zero F] [One F] {k : ℕ}
    (pi : Equiv.Perm (Fin k)) (B : Matrix (Fin k) (Fin k) F) : Prop :=
  ∀ i j, B (pi j) i = if i = j then 1 else
    if i < j ∧ pi j < pi i then B (pi j) i else 0

def cellRead {F : Type*} {k : ℕ}
    (sigma : Equiv.Perm (Fin (k+1))) (pi : Equiv.Perm (Fin k))
    (A : Matrix (Fin (k+1)) (Fin (k+1)) F)
    (B : Matrix (Fin k) (Fin k) F) : CellVariables sigma pi → F :=
  Sum.elim (fun ab => A (sigma ab.val.1) ab.val.2)
    (fun ij => B (pi ij.val.2) ij.val.1)


abbrev CoeffIndex (k : ℕ) := Fin k × Fin (k + 1)
def coefficientMatrix {K : Type*} [Semiring K]
    {k : ℕ} (M0 M1 : Matrix (Fin (k + 1)) (Fin k) K) :
    Matrix (CoeffIndex k) (CoeffIndex k) K := fun row col =>
  (if row.2.val = col.1.val then M0 col.2 row.1 else 0) +
    (if row.2.val = col.1.val + 1 then M1 col.2 row.1 else 0)
def coefficientWeight {K : Type*} [Semiring K]
    {k : ℕ} (a b : K) (z : Fin k → K) : CoeffIndex k → K :=
  fun row => z row.1 * a ^ (k - row.2.val) * b ^ row.2.val


abbrev TensorVariable (k : ℕ) := Fin 2 × Fin (k+1) × Fin k
noncomputable def coefficientPolynomial (k : ℕ) : MvPolynomial (TensorVariable k) ℤ :=
  (coefficientMatrix
    (fun r j => MvPolynomial.X (0,r,j))
    (fun r j => MvPolynomial.X (1,r,j))).det


abbrev Factors (F : Type*) [Field F] (k : ℕ) := GL (Fin (k + 1)) F × GL (Fin k) F

def factorMap {F : Type*} [Field F] {k : ℕ} (g : Factors F k) : Faces F k :=
  (g.1.val * E0 F k * g.2.val, g.1.val * E1 F k * g.2.val)

def shift {F : Type*} [Field F] {k : ℕ} (g : Factors F k) (u : Fˣ) : Factors F k :=
  (g.1 * Matrix.GeneralLinearGroup.scalar (Fin (k + 1)) u,
    Matrix.GeneralLinearGroup.scalar (Fin k) u⁻¹ * g.2)

end D5.S3.Combinatorics.Hypermatrix.MaskedFacesDefs
