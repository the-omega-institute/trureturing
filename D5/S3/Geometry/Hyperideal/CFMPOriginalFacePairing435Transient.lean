import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import D5.S3.Geometry.Hyperideal.CFMPOriginalCellsOrientation435Transient
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

noncomputable section
open scoped Matrix BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace

namespace CFMPOriginalFacePairing435Transient

-- Temporary application preparation; no retained declaration is proposed.
def pairTable : Fin 30 → (Fin 20 × Fin 3) × (Fin 20 × Fin 3) :=
  ![((0,2),(19,1)),
    ((0,1),(15,1)),
    ((12,2),(16,2)),
    ((16,1),(17,2)),
    ((12,1),(13,2)),
    ((18,1),(19,2)),
    ((17,1),(18,2)),
    ((14,1),(15,2)),
    ((13,1),(14,2)),
    ((0,0),(11,1)),
    ((8,2),(19,0)),
    ((8,1),(9,2)),
    ((10,1),(11,2)),
    ((9,1),(10,2)),
    ((11,0),(15,0)),
    ((1,2),(16,0)),
    ((1,1),(12,0)),
    ((1,0),(7,1)),
    ((4,2),(17,0)),
    ((4,1),(5,2)),
    ((6,1),(7,2)),
    ((5,1),(6,2)),
    ((7,0),(13,0)),
    ((2,2),(18,0)),
    ((2,1),(8,0)),
    ((2,0),(4,0)),
    ((5,0),(9,0)),
    ((3,2),(14,0)),
    ((3,1),(10,0)),
    ((3,0),(6,0))]

def edge (l : Fin 6 → ℝ) (n : Fin 20) (j : Fin 3) : Fin 3 → ℝ :=
  fun k => vertices l n j.succ k.castSucc - vertices l n 0 k.castSucc

def orientation : Fin 20 → ℝ :=
  ![1,-1,1,-1,-1,-1,-1,-1,1,1,1,1,-1,-1,-1,-1,1,1,1,1]

def coefficient (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) : Fin 3 → ℝ :=
  orientation n • ![-(edge l n 1 ⨯₃ edge l n 2),
    edge l n 0 ⨯₃ edge l n 2, -(edge l n 0 ⨯₃ edge l n 1)] i

-- These are temporary exact checks of the original twenty tuples.
-- They neither define native surface measure nor prove geometric flux transfer.
def pairedOccurrence (p : Fin 30 × Bool) : Fin 20 × Fin 3 :=
  if p.2 then (pairTable p.1).2 else (pairTable p.1).1

example : Function.Bijective pairedOccurrence := by decide

def swapEndpoints : Fin 30 → Bool :=
  ![false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,true,true,true]

def faceVertices (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) : Fin 3 → V :=
  ![vertices l n 0, vertices l n (i.succAbove 0).succ,
    vertices l n (i.succAbove 1).succ]

def reverseFace : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2

theorem face_order (l : Fin 6 → ℝ) (p : Fin 30) :
    faceVertices l (pairTable p).1.1 (pairTable p).1.2 =
      (faceVertices l (pairTable p).2.1 (pairTable p).2.2) ∘
        (if swapEndpoints p then reverseFace else Equiv.refl _) := by
  fin_cases p <;> funext j <;> fin_cases j <;> rfl

private def direction (f : Fin 3 → V) (j : Fin 2) : Fin 3 → ℝ :=
  fun k => f j.succ k.castSucc - f 0 k.castSucc

private def faceSign : Fin 3 → ℝ := ![-1,1,-1]

private def faceWeight (n : Fin 20) (i : Fin 3) : ℝ :=
  orientation n * faceSign i

private theorem coefficient_eq_face (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) :
    coefficient l n i = faceWeight n i •
      (direction (faceVertices l n i) 0 ⨯₃ direction (faceVertices l n i) 1) := by
  fin_cases i
  · change orientation n • (-(edge l n 1 ⨯₃ edge l n 2)) =
      (orientation n * (-1)) • (edge l n 1 ⨯₃ edge l n 2)
    simp only [mul_neg, mul_one, neg_smul, smul_neg]
  · change orientation n • (edge l n 0 ⨯₃ edge l n 2) =
      (orientation n * 1) • (edge l n 0 ⨯₃ edge l n 2)
    simp only [mul_one]
  · change orientation n • (-(edge l n 0 ⨯₃ edge l n 1)) =
      (orientation n * (-1)) • (edge l n 0 ⨯₃ edge l n 1)
    simp only [mul_neg, mul_one, neg_smul, smul_neg]

private theorem faceWeight_parity (p : Fin 30) :
    if swapEndpoints p then
      faceWeight (pairTable p).1.1 (pairTable p).1.2 =
        faceWeight (pairTable p).2.1 (pairTable p).2.2
    else
      faceWeight (pairTable p).1.1 (pairTable p).1.2 =
        -faceWeight (pairTable p).2.1 (pairTable p).2.2 := by
  fin_cases p <;>
    norm_num [faceWeight, faceSign, orientation, swapEndpoints, pairTable]

private theorem abstract_face_cancel (f g : Fin 3 → V) (s t : ℝ) (b : Bool)
    (hfg : f = g ∘ (if b then reverseFace else Equiv.refl _))
    (hs : if b then s = t else s = -t) :
    s • (direction f 0 ⨯₃ direction f 1) +
      t • (direction g 0 ⨯₃ direction g 1) = 0 := by
  cases b
  · have hfg' : f = g := by simpa using hfg
    have hs' : s = -t := by simpa using hs
    rw [hfg', hs']
    simp
  · have hs' : s = t := by simpa using hs
    have h0 : direction f 0 = direction g 1 := by
      rw [hfg]
      rfl
    have h1 : direction f 1 = direction g 0 := by
      rw [hfg]
      rfl
    rw [h0, h1, hs', ← smul_add, cross_anticomm', smul_zero]

theorem paired_coefficients (l : Fin 6 → ℝ) (p : Fin 30) :
    coefficient l (pairTable p).1.1 (pairTable p).1.2 +
      coefficient l (pairTable p).2.1 (pairTable p).2.2 = 0 := by
  rw [coefficient_eq_face, coefficient_eq_face]
  exact abstract_face_cancel _ _ _ _ (swapEndpoints p)
    (face_order l p) (faceWeight_parity p)

example (l : Fin 6 → ℝ) (p : Fin 30) :
    convexHull ℝ (range (faceVertices l (pairTable p).1.1 (pairTable p).1.2)) =
      convexHull ℝ (range (faceVertices l (pairTable p).2.1 (pairTable p).2.2)) := by
  rw [face_order l p]
  split_ifs <;> simp only [EquivLike.range_comp]

example (l : Fin 6 → ℝ) :
    ∑ n : Fin 20, ∑ i : Fin 3, coefficient l n i = 0 := by
  let e : (Fin 30 × Bool) ≃ (Fin 20 × Fin 3) :=
    Equiv.ofBijective pairedOccurrence (by decide)
  calc
    _ = ∑ t : Fin 20 × Fin 3, coefficient l t.1 t.2 :=
      (Fintype.sum_prod_type _).symm
    _ = ∑ t : Fin 30 × Bool, coefficient l (e t).1 (e t).2 :=
      (Equiv.sum_comp e _).symm
    _ = ∑ p : Fin 30, (coefficient l (pairTable p).1.1 (pairTable p).1.2 +
        coefficient l (pairTable p).2.1 (pairTable p).2.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      simp [e, pairedOccurrence, Fintype.sum_bool, add_comm]
    _ = 0 := by simp_rw [paired_coefficients]; simp


-- Explicit original outward cofactor bridge, using the already checked orientation application.
example (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) (i : Fin 3) :
    CFMPOriginalCellsOrientation435Transient.coefficient
        (CFMPOriginalCellsOrientation435Transient.edges l n) i = coefficient l n i := by
  rw [CFMPOriginalCellsOrientation435Transient.coefficient_eq_area,
    CFMPOriginalCellsOrientation435Transient.abs_div_det_eq_sign l hl n]
  rfl

def faceParam (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) : V :=
  faceVertices l n i 0 +
    q 0 • (faceVertices l n i 1 - faceVertices l n i 0) +
    q 1 • (faceVertices l n i 2 - faceVertices l n i 0)

def pairedParam (p : Fin 30) (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if swapEndpoints p then ![q 1, q 0] else q

example (l : Fin 6 → ℝ) (p : Fin 30) (q : Fin 2 → ℝ) :
    faceParam l (pairTable p).1.1 (pairTable p).1.2 q =
      faceParam l (pairTable p).2.1 (pairTable p).2.2 (pairedParam p q) := by
  unfold faceParam
  simp only [face_order l p]
  by_cases h : swapEndpoints p = true
  · simp [pairedParam, h, reverseFace, Equiv.swap_apply_def,
      Function.comp_apply, add_assoc, add_comm, add_left_comm]
  · simp [pairedParam, h, Function.comp_apply]

example (p : Fin 30) (q : Fin 2 → ℝ) :
    (0 ≤ (pairedParam p q) 0 ∧ 0 ≤ (pairedParam p q) 1 ∧
      (pairedParam p q) 0 + (pairedParam p q) 1 ≤ 1) ↔
      (0 ≤ q 0 ∧ 0 ≤ q 1 ∧ q 0 + q 1 ≤ 1) := by
  dsimp [pairedParam]
  split_ifs <;> simp [and_left_comm, add_comm]

end CFMPOriginalFacePairing435Transient
