/- GID: D5/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/OrderedHyperbolicExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original ordered integral hyperbolic extension and actual Leech product. -/

import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.VertexAlgebra.LatticeActualProductKernel
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic

/-! The integral plane is the literal U in the order m,n, after the old
coordinates. Explicit real signature subspaces preserve these integral coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.OrderedHyperbolicExtension

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeRealNullFrame

/-- Old coordinates precede the two hyperbolic coordinates. -/
def indexEquiv (D : LatticeData) : Fin D.rank ⊕ Fin 2 ≃ Fin (D.rank + 2) :=
  finSumFinEquiv

def old (D : LatticeData) (i : Fin D.rank) : Fin (D.rank + 2) := Fin.castAdd 2 i
def new (D : LatticeData) (i : Fin 2) : Fin (D.rank + 2) := Fin.natAdd D.rank i

@[simp] theorem index_old (D : LatticeData) (i : Fin D.rank) :
    indexEquiv D (Sum.inl i) = old D i := rfl
@[simp] theorem index_new (D : LatticeData) (i : Fin 2) :
    indexEquiv D (Sum.inr i) = new D i := rfl
@[simp] theorem old_lt_old (D : LatticeData) (i j : Fin D.rank) :
    old D i < old D j ↔ i < j := Iff.rfl
@[simp] theorem old_lt_new (D : LatticeData) (i : Fin D.rank) (j : Fin 2) :
    old D i < new D j := by change i.val < D.rank + j.val; omega
@[simp] theorem not_new_lt_old (D : LatticeData) (i : Fin 2) (j : Fin D.rank) :
    ¬ new D i < old D j := by change ¬ D.rank + i.val < j.val; omega
@[simp] theorem new_lt_new (D : LatticeData) (i j : Fin 2) :
    new D i < new D j ↔ i < j := by
  change D.rank + i.val < D.rank + j.val ↔ i.val < j.val
  omega

def U : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

@[simp] theorem U_zero_zero : U 0 0 = 0 := rfl
@[simp] theorem U_zero_one : U 0 1 = 1 := rfl
@[simp] theorem U_one_zero : U 1 0 = 1 := rfl
@[simp] theorem U_one_one : U 1 1 = 0 := rfl
@[simp] theorem U_diagonal (i : Fin 2) : U i i = 0 := by fin_cases i <;> rfl

theorem U_symmetric (i j : Fin 2) : U i j = U j i := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem U_mul_U : U * U = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, U]

/-- Simultaneous reindexing is explicit; no integral diagonalization is used. -/
def gram (D : LatticeData) : Matrix (Fin (D.rank + 2)) (Fin (D.rank + 2)) ℤ :=
  Matrix.reindex (indexEquiv D) (indexEquiv D) (Matrix.fromBlocks D.G 0 0 U)

@[simp] theorem gram_index (D : LatticeData) (i j : Fin D.rank ⊕ Fin 2) :
    gram D (indexEquiv D i) (indexEquiv D j) = (Matrix.fromBlocks D.G 0 0 U) i j := by
  simp [gram, Matrix.reindex_apply]

@[simp] theorem gram_old_old (D : LatticeData) (i j : Fin D.rank) :
    gram D (old D i) (old D j) = D.G i j := by
  simpa only [index_old, Matrix.fromBlocks_apply₁₁] using gram_index D (.inl i) (.inl j)
@[simp] theorem gram_old_new (D : LatticeData) (i : Fin D.rank) (j : Fin 2) :
    gram D (old D i) (new D j) = 0 := by
  simpa only [index_old, index_new, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply] using
    gram_index D (.inl i) (.inr j)
@[simp] theorem gram_new_old (D : LatticeData) (i : Fin 2) (j : Fin D.rank) :
    gram D (new D i) (old D j) = 0 := by
  simpa only [index_old, index_new, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using
    gram_index D (.inr i) (.inl j)
@[simp] theorem gram_new_new (D : LatticeData) (i j : Fin 2) :
    gram D (new D i) (new D j) = U i j := by
  simpa only [index_new, Matrix.fromBlocks_apply₂₂] using gram_index D (.inr i) (.inr j)

theorem gram_symmetric (D : LatticeData) (i j : Fin (D.rank + 2)) :
    gram D i j = gram D j i := by
  obtain ⟨i, rfl⟩ := (indexEquiv D).surjective i
  obtain ⟨j, rfl⟩ := (indexEquiv D).surjective j
  rcases i with i | i <;> rcases j with j | j
  · simpa using D.symmetric i j
  · simp
  · simp
  · simpa using U_symmetric i j

theorem gram_even_diagonal (D : LatticeData) (i : Fin (D.rank + 2)) :
    Even (gram D i i) := by
  obtain ⟨i, rfl⟩ := (indexEquiv D).surjective i
  rcases i with i | i
  · simpa using D.even_diagonal i
  · simp

/-- The original LatticeData structure, extended by the ordered integral U. -/
abbrev extend (D : LatticeData) : LatticeData where
  rank := D.rank + 2
  G := gram D
  symmetric := gram_symmetric D
  even_diagonal := gram_even_diagonal D

/-- Splicing works over both the original integer carrier and scalar extensions. -/
def splice {A : Type*} (D : LatticeData) (a : Fin D.rank → A) (m n : A) :
    Fin (D.rank + 2) → A :=
  fun i => Sum.elim a ![m, n] ((indexEquiv D).symm i)

@[simp] theorem splice_old {A : Type*} (D : LatticeData)
    (a : Fin D.rank → A) (m n : A) (i : Fin D.rank) :
    splice D a m n (old D i) = a i := by
  simp [splice, old, indexEquiv]
@[simp] theorem splice_new_zero {A : Type*} (D : LatticeData)
    (a : Fin D.rank → A) (m n : A) : splice D a m n (new D 0) = m := by
  simp [splice, new, indexEquiv]
@[simp] theorem splice_new_one {A : Type*} (D : LatticeData)
    (a : Fin D.rank → A) (m n : A) : splice D a m n (new D 1) = n := by
  simp [splice, new, indexEquiv]

/-- A genuine linear split; its inverse is splice, not just an injective labeling. -/
def splitEquiv (D : LatticeData) {R : Type*} [CommRing R] :
    (Fin (D.rank + 2) → R) ≃ₗ[R] (Fin D.rank → R) × (R × R) where
  toFun v := (fun i => v (old D i), (v (new D 0), v (new D 1)))
  invFun v := splice D v.1 v.2.1 v.2.2
  left_inv v := by
    funext i
    obtain ⟨i, rfl⟩ := (indexEquiv D).surjective i
    rcases i with i | i
    · simp
    · fin_cases i <;> simp
  right_inv v := by rcases v with ⟨a, m, n⟩; simp
  map_add' v w := rfl
  map_smul' r v := rfl

@[simp] theorem split_splice (D : LatticeData) {R : Type*} [CommRing R]
    (a : Fin D.rank → R) (m n : R) :
    splitEquiv D (splice D a m n) = (a, (m, n)) := by
  change (fun i => splice D a m n (old D i),
    (splice D a m n (new D 0), splice D a m n (new D 1))) = _
  simp

@[simp] theorem split_symm_apply (D : LatticeData) {R : Type*} [CommRing R]
    (a : Fin D.rank → R) (m n : R) :
    (splitEquiv D).symm (a, (m, n)) = splice D a m n := rfl

@[simp] theorem splice_zero (D : LatticeData) {R : Type*} [CommRing R] :
    splice D (0 : Fin D.rank → R) 0 0 = 0 := by
  apply (splitEquiv D).injective
  simp only [split_splice, map_zero]
  rfl

/-- This sum formula remembers the actual Fin order. -/
theorem sum_ordered (D : LatticeData) {A : Type*} [AddCommMonoid A]
    (f : Fin (D.rank + 2) → A) :
    (∑ i, f i) = (∑ i, f (old D i)) + f (new D 0) + f (new D 1) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_two]
  exact (add_assoc _ _ _).symm

/-- Full integral pairing, for every charge and with no positivity restriction. -/
theorem bilinear_splice (D : LatticeData) (a b : Charge D) (m n r s : ℤ) :
    bilinear (extend D) (splice D a m n) (splice D b r s) =
      bilinear D a b + m * s + n * r := by
  simp [bilinear, sum_ordered D]

/-- Integer division is handled through the already proved even-norm identity. -/
theorem chargeEnergy_splice (D : LatticeData) (a : Charge D) (m n : ℤ) :
    chargeEnergy (extend D) (splice D a m n) = chargeEnergy D a + m * n := by
  have he := two_chargeEnergy (extend D) (splice D a m n)
  have ha := two_chargeEnergy D a
  rw [bilinear_splice] at he
  nlinarith

/-- Exact integer lower triangle: the new term is n*r, not m*s. -/
theorem lowerCocycleExponent_splice (D : LatticeData)
    (a b : Charge D) (m n r s : ℤ) :
    lowerCocycleExponent (extend D) (splice D a m n) (splice D b r s) =
      lowerCocycleExponent D a b + n * r := by
  classical
  simp only [lowerCocycleExponent, Finset.sum_filter]
  simp [sum_ordered D, halfDiagonal]
  ring

/-- Literal integral inverse: old inverse followed by the SAME U block. -/
def integerInverse (D : LatticeData) :
    Matrix (Fin (D.rank + 2)) (Fin (D.rank + 2)) ℤ :=
  Matrix.reindex (indexEquiv D) (indexEquiv D) (Matrix.fromBlocks D.G⁻¹ 0 0 U)

theorem integerInverse_left (D : LatticeData) (hD : IsUnit D.G.det) :
    integerInverse D * (extend D).G = 1 := by
  let F := Matrix.reindexRingEquiv ℤ (indexEquiv D)
  change F (Matrix.fromBlocks D.G⁻¹ 0 0 U) * F (Matrix.fromBlocks D.G 0 0 U) = 1
  rw [← F.map_mul]
  simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul D.G hD,
    Matrix.fromBlocks_one]

theorem integerInverse_right (D : LatticeData) (hD : IsUnit D.G.det) :
    (extend D).G * integerInverse D = 1 := by
  let F := Matrix.reindexRingEquiv ℤ (indexEquiv D)
  change F (Matrix.fromBlocks D.G 0 0 U) * F (Matrix.fromBlocks D.G⁻¹ 0 0 U) = 1
  rw [← F.map_mul]
  simp [Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv D.G hD,
    Matrix.fromBlocks_one]

/-- Casting the constructed integral inverse, rather than assuming inverse equations. -/
def complexInverse (D : LatticeData) :
    Matrix (Fin (D.rank + 2)) (Fin (D.rank + 2)) ℂ :=
  (integerInverse D).map (Int.castRingHom ℂ)

/-- The original supplier's full bilinear normalization, over the reals. -/
theorem g_R_splice (D : LatticeData) (a b : E_R D) (m n r s : ℝ) :
    g_R (extend D) (splice D a m n) (splice D b r s) =
      g_R D a b + m * s + n * r := by
  simp [g_R_apply, sum_ordered D]

theorem Q_R_splice (D : LatticeData) (a : E_R D) (m n : ℝ) :
    Q_R (extend D) (splice D a m n) = Q_R D a + 2 * m * n := by
  simp only [Q_R_apply, g_R_splice]
  ring

/-- The map parametrizing the actual subspace (x,t,t). -/
def positiveMap (D : LatticeData) : (E_R D × ℝ) →ₗ[ℝ] E_R (extend D) where
  toFun v := splice D v.1 v.2 v.2
  map_add' v w := by
    apply (splitEquiv D).injective
    simp only [map_add, split_splice]
    rfl
  map_smul' c v := by
    apply (splitEquiv D).injective
    simp only [map_smul, split_splice]
    rfl

/-- The map parametrizing the actual subspace (0,t,-t). -/
def negativeMap (D : LatticeData) : ℝ →ₗ[ℝ] E_R (extend D) where
  toFun t := splice D 0 t (-t)
  map_add' t s := by
    apply (splitEquiv D).injective
    simp only [map_add, split_splice]
    simp [add_comm]
  map_smul' c t := by
    apply (splitEquiv D).injective
    simp only [map_smul, split_splice]
    simp

@[simp] theorem positiveMap_apply (D : LatticeData) (v : E_R D × ℝ) :
    positiveMap D v = splice D v.1 v.2 v.2 := rfl
@[simp] theorem negativeMap_apply (D : LatticeData) (t : ℝ) :
    negativeMap D t = splice D 0 t (-t) := rfl

theorem positiveMap_injective (D : LatticeData) : Function.Injective (positiveMap D) := by
  intro v w h
  have h' := congrArg (fun z =>
    ((splitEquiv D (R := ℝ) z).1, (splitEquiv D (R := ℝ) z).2.1)) h
  simpa using h'

theorem negativeMap_injective (D : LatticeData) : Function.Injective (negativeMap D) := by
  intro t s h
  have h' := congrArg (fun z => (splitEquiv D (R := ℝ) z).2.1) h
  simpa using h'

def positiveSubspace (D : LatticeData) : Submodule ℝ (E_R (extend D)) :=
  (positiveMap D).range

def negativeSubspace (D : LatticeData) : Submodule ℝ (E_R (extend D)) :=
  (negativeMap D).range

theorem finrank_positiveSubspace (D : LatticeData) :
    Module.finrank ℝ (positiveSubspace D) = D.rank + 1 := by
  simpa [positiveSubspace, Module.finrank_prod] using
    (LinearMap.finrank_range_of_inj (positiveMap_injective D))

theorem finrank_negativeSubspace (D : LatticeData) :
    Module.finrank ℝ (negativeSubspace D) = 1 := by
  simpa [negativeSubspace] using
    (LinearMap.finrank_range_of_inj (negativeMap_injective D))

/-- Positive definiteness of the OLD matrix is the only signature premise. -/
theorem old_Q_positive (D : LatticeData)
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef) {x : E_R D} (hx : x ≠ 0) :
    0 < Q_R D x := by
  have h := hD.dotProduct_mulVec_pos hx
  simpa [Q_R_apply, g_R_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc] using h

theorem positiveSubspace_posDef (D : LatticeData)
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef) :
    ((Q_R (extend D)).restrict (positiveSubspace D)).PosDef := by
  rintro ⟨v, hv⟩ hne
  obtain ⟨⟨x, t⟩, rfl⟩ := hv
  change 0 < Q_R (extend D) (splice D x t t)
  rw [Q_R_splice]
  by_cases hx : x = 0
  · have ht : t ≠ 0 := by
      intro ht
      apply hne
      apply Subtype.ext
      simp [hx, ht]
    simp only [hx, Q_R_apply, g_R_zero_right]
    nlinarith [sq_pos_of_ne_zero ht]
  · have hp := old_Q_positive D hD hx
    nlinarith [sq_nonneg t]

theorem negativeSubspace_negDef (D : LatticeData) :
    ((-Q_R (extend D)).restrict (negativeSubspace D)).PosDef := by
  rintro ⟨v, hv⟩ hne
  obtain ⟨t, rfl⟩ := hv
  have ht : t ≠ 0 := by
    intro ht
    apply hne
    apply Subtype.ext
    simp [ht]
  change 0 < - Q_R (extend D) (splice D 0 t (-t))
  rw [Q_R_splice]
  simp only [Q_R_apply, g_R_zero_right]
  nlinarith [sq_pos_of_ne_zero ht]

/-- Both signature counts follow from the explicit subspaces and dimension bounds. -/
theorem signature_extend (D : LatticeData)
    (hD : (D.G.map (Int.castRingHom ℝ)).PosDef) :
    sigPos (Q_R (extend D)) = D.rank + 1 ∧ sigNeg (Q_R (extend D)) = 1 := by
  have hp := le_sigPos_of_posDef (Q_R (extend D)) (positiveSubspace_posDef D hD)
  have hn := le_sigNeg_of_negDef (Q_R (extend D)) (negativeSubspace_negDef D)
  have hup := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q_R (extend D)) (V := negativeSubspace D) (by
      intro x hx
      by_cases hzero : x = 0
      · simp [hzero]
      · have h := negativeSubspace_negDef D ⟨x, hx⟩ (by simpa using hzero)
        change 0 < -Q_R (extend D) x at h
        linarith)
  have hun := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := -Q_R (extend D)) (V := positiveSubspace D) (by
      intro x hx
      change -Q_R (extend D) x ≤ 0
      by_cases hzero : x = 0
      · simp [hzero]
      · have h := positiveSubspace_posDef D hD ⟨x, hx⟩ (by simpa using hzero)
        change 0 < Q_R (extend D) x at h
        linarith)
  rw [finrank_positiveSubspace] at hp hun
  rw [finrank_negativeSubspace] at hn hup
  rw [finrank_E_R] at hup hun
  change sigPos (Q_R (extend D)) + 1 ≤ D.rank + 2 at hup
  change sigNeg (Q_R (extend D)) + (D.rank + 1) ≤ D.rank + 2 at hun
  omega

end D5.S3.VertexAlgebra.OrderedHyperbolicExtension
