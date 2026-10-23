/- GID: D5/S3/Geometry/EvenSignTensorObstruction
   generality: G
   mirror-B: D5/B/S3/Geometry/EvenSignTensorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero rotation-equivariant antisymmetric bilinearity requires three coordinates. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.EvenSignTensorObstruction

open scoped BigOperators Matrix

/-- The diagonal signs of a half-turn in the plane of two coordinate axes. -/
def coordinateSign {I : Type*} [DecidableEq I] (p q r : I) : ℝ :=
  if r = p ∨ r = q then -1 else 1

/-- A third-order tensor vanishing on repeated first coordinates cannot survive all
pair-coordinate sign flips outside dimension three. -/
theorem tensor_eq_zero_of_card_ne_three {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → I → I → ℝ)
    (hdiag : ∀ i k, c i i k = 0)
    (hflip : ∀ p q, p ≠ q → ∀ i j k,
      c i j k = coordinateSign p q i * coordinateSign p q j *
        coordinateSign p q k * c i j k)
    (hdim : Fintype.card I ≠ 3) : c = 0 := by
  classical
  funext i j k
  change c i j k = 0
  by_cases hij : i = j
  · subst j
    exact hdiag i k
  by_cases hki : k = i
  · subst k
    have h := hflip i j hij i j i
    simp [coordinateSign] at h
    linarith
  by_cases hkj : k = j
  · subst k
    have h := hflip i j hij i j j
    simp [coordinateSign] at h
    linarith
  have hex : ∃ l : I, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
    by_contra h
    push Not at h
    apply hdim
    change (Finset.univ : Finset I).card = 3
    apply Finset.card_eq_three.mpr
    refine ⟨i, j, k, hij, (Ne.symm hki), (Ne.symm hkj), ?_⟩
    ext l
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hli : l = i
    · exact Or.inl hli
    by_cases hlj : l = j
    · exact Or.inr (Or.inl hlj)
    exact Or.inr (Or.inr (h l hli hlj))
  obtain ⟨l, hli, hlj, hlk⟩ := hex
  have h := hflip k l hlk.symm i j k
  simp [coordinateSign, (Ne.symm hki), (Ne.symm hkj), hli.symm, hlj.symm] at h
  linarith

private theorem diagonal_pair_sign_mem_specialOrthogonalGroup
    {I : Type*} [Fintype I] [DecidableEq I]
    (p q : I) (hpq : p ≠ q) :
    Matrix.diagonal (coordinateSign p q) ∈
      Matrix.specialOrthogonalGroup I ℝ := by
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  constructor
  · apply (Matrix.mem_orthogonalGroup_iff I ℝ).mpr
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    have hs : (fun r : I => coordinateSign p q r * coordinateSign p q r) =
        (fun _ : I => (1 : ℝ)) := by
      funext r
      by_cases h : r = p ∨ r = q <;> simp [coordinateSign, h]
    rw [hs, Matrix.diagonal_one]
  · rw [Matrix.det_diagonal]
    calc
      (∏ r : I, coordinateSign p q r) =
          ∏ r : I, if r ∈ ({p, q} : Finset I) then (-1 : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro r _
        simp [coordinateSign]
      _ = ∏ r ∈ ({p, q} : Finset I), (-1 : ℝ) :=
        Finset.prod_ite_mem_eq _ _
      _ = 1 := by simp [hpq]

/-- The dimension obstruction for the full standard special orthogonal action.
The existence and classification of operations in dimension three are separate. -/
theorem special_orthogonal_equivariant_bilinear_card_eq_three
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] (I → ℝ))
    (hskew : ∀ u v, B u v = -(B v u))
    (hequiv : ∀ R : Matrix.specialOrthogonalGroup I ℝ, ∀ u v,
      B ((R : Matrix I I ℝ) *ᵥ u) ((R : Matrix I I ℝ) *ᵥ v) =
        (R : Matrix I I ℝ) *ᵥ B u v)
    (hne : B ≠ 0) : Fintype.card I = 3 := by
  classical
  by_contra hdim
  apply hne
  let e := Pi.basisFun ℝ I
  let c : I → I → I → ℝ := fun i j k => B (e i) (e j) k
  have hc : c = 0 := by
    apply tensor_eq_zero_of_card_ne_three c ?_ ?_ hdim
    · intro i k
      have h := congrFun (hskew (e i) (e i)) k
      change c i i k = -(c i i k) at h
      linarith
    · intro p q hpq i j k
      let s : I → ℝ := coordinateSign p q
      have hDe (r : I) : Matrix.diagonal s *ᵥ e r = s r • e r := by
        simp only [e, Pi.basisFun_apply, Matrix.diagonal_mulVec_single]
        simpa only [smul_eq_mul] using (Pi.single_smul' r (s r) (1 : ℝ))
      have hbase := hequiv
        ⟨Matrix.diagonal s, diagonal_pair_sign_mem_specialOrthogonalGroup p q hpq⟩
        (e i) (e j)
      change B (Matrix.diagonal s *ᵥ e i) (Matrix.diagonal s *ᵥ e j) =
        Matrix.diagonal s *ᵥ B (e i) (e j) at hbase
      rw [hDe i, hDe j, LinearMap.map_smul₂, map_smul] at hbase
      have he := congrFun hbase k
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal] at he
      change s i * (s j * c i j k) = s k * c i j k at he
      have hsquare : s k * s k = 1 := by
        by_cases h : k = p ∨ k = q <;> simp [s, coordinateSign, h]
      change c i j k = s i * s j * s k * c i j k
      calc
        c i j k = (s k * s k) * c i j k := by rw [hsquare, one_mul]
        _ = s k * (s k * c i j k) := mul_assoc _ _ _
        _ = s k * (s i * (s j * c i j k)) := by rw [← he]
        _ = s i * s j * s k * c i j k := by ring
  apply LinearMap.ext_basis e e
  intro i j
  funext k
  exact congrFun (congrFun (congrFun hc i) j) k

#print axioms tensor_eq_zero_of_card_ne_three
#print axioms special_orthogonal_equivariant_bilinear_card_eq_three

end D5.S3.Geometry.EvenSignTensorObstruction
