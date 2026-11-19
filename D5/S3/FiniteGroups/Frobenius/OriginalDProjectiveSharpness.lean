/- GID: D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.projectivity_claim; result=D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.originalD_counterexample; claim=D5/S3/FiniteGroups/Frobenius/OriginalDProjectiveSharpness.projectivity_claim
   digest: A modular dihedral counterexample to dropping original-D invertibility. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Irreducible
import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder
import Mathlib.Tactic

/-!
# Original-D projectivity sharpness over F7

The explicit D42 representation satisfies every original-D hypothesis
except invertibility of the rotation order. Its actual group-algebra module
is not projective: restriction to the trivially acting subgroup of order
seven contradicts the general finite-trivial-subgroup projectivity obstruction.

The construction is the classical two-dimensional dihedral representation:
rotation acts by diag(2,4) over F7 and reflection exchanges the coordinates.
It factors through D6. The rotation subgroup N = C21 and the kernel H of the
projection D42 -> D6 are different subgroups; H is not called the Frobenius
kernel. No novelty claim is made for this classical example.
-/

noncomputable section

namespace D5.S3.FiniteGroups.OriginalDProjectiveSharpness

set_option backward.isDefEq.respectTransparency false

abbrev k := ZMod 7
abbrev G := DihedralGroup 21
abbrev V := Fin 2 → k

private instance prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

private def residue : ZMod 21 →+* ZMod 3 :=
  ZMod.castHom (by decide : 3 ∣ 21) (ZMod 3)

/-- Reduction of the rotation coordinate modulo three, preserving the tag. -/
def projection : G →* DihedralGroup 3 where
  toFun
    | .r i => .r (residue i)
    | .sr i => .sr (residue i)
  map_one' := congrArg DihedralGroup.r (map_zero residue)
  map_mul' := by
    rintro (i | i) (j | j)
    · exact congrArg DihedralGroup.r (map_add residue i j)
    · exact congrArg DihedralGroup.sr (map_sub residue j i)
    · exact congrArg DihedralGroup.sr (map_add residue i j)
    · exact congrArg DihedralGroup.r (map_sub residue j i)

/-- The full rotation subgroup, rather than the representation kernel. -/
def N : Subgroup G where
  carrier := {g | ∃ i : ZMod 21, g = DihedralGroup.r i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

instance normal_N : N.Normal where
  conj_mem := by
    rintro _ ⟨i, rfl⟩ (j | j)
    · refine ⟨i, ?_⟩
      change DihedralGroup.r (j + i + -j) = DihedralGroup.r i
      congr 1
      abel
    · refine ⟨-i, ?_⟩
      change DihedralGroup.r (j - (j + i)) = DihedralGroup.r (-i)
      congr 1
      abel

private def matrices : DihedralGroup 3 → Matrix (Fin 2) (Fin 2) k
  | .r i =>
      if i = 0 then !![1, 0; 0, 1]
      else if i = 1 then !![2, 0; 0, 4]
      else !![4, 0; 0, 2]
  | .sr i =>
      if i = 0 then !![0, 1; 1, 0]
      else if i = 1 then !![0, 4; 2, 0]
      else !![0, 2; 4, 0]

-- These are finite propositions about six explicit matrices. `decide` here
-- produces ordinary kernel-checkable proof terms, without native evaluation.
private def matrixHom : DihedralGroup 3 →* Matrix (Fin 2) (Fin 2) k where
  toFun := matrices
  map_one' := by decide
  map_mul' := by decide

private def smallRho : Representation k (DihedralGroup 3) V :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) k ≃ₐ[k]
    Module.End k V).toRingEquiv.toMonoidHom.comp matrixHom

/-- The explicit representation of D42, pulled back from the six matrices. -/
def rho : Representation k G V := smallRho.comp projection

/-- The actual kernel of the tag-preserving projection, of order seven. -/
def H : Subgroup G := projection.ker

private def e₀ : V := ![1, 0]
private def e₁ : V := ![0, 1]

private theorem rho_rotation (v : V) :
    rho (DihedralGroup.r 1) v = ![2 * v 0, 4 * v 1] := by
  have hp : projection (DihedralGroup.r 1) = DihedralGroup.r 1 := by decide
  change Matrix.toLinAlgEquiv' (matrices (projection (DihedralGroup.r 1))) v = _
  rw [hp, Matrix.toLinAlgEquiv'_apply]
  funext i
  fin_cases i <;> simp [matrices, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem rho_reflection (v : V) :
    rho (DihedralGroup.sr 0) v = ![v 1, v 0] := by
  have hp : projection (DihedralGroup.sr 0) = DihedralGroup.sr 0 := by decide
  change Matrix.toLinAlgEquiv' (matrices (projection (DihedralGroup.sr 0))) v = _
  rw [hp, Matrix.toLinAlgEquiv'_apply]
  funext i
  fin_cases i <;> simp [matrices, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem fixed_rotation_is_one :
    ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1 := by
  intro g hg n hn
  obtain ⟨i, hi⟩ := n.property
  cases g with
  | r j => exact (hg ⟨j, rfl⟩).elim
  | sr j =>
      have he : DihedralGroup.sr j * (n : G) * (DihedralGroup.sr j)⁻¹ = (n : G) :=
        congrArg (fun z : N => (z : G)) hn
      rw [hi] at he
      have he' : DihedralGroup.r (j - (j + i)) = DihedralGroup.r i := he
      have hneg : -i = i := by
        calc
          -i = j - (j + i) := by abel
          _ = i := DihedralGroup.r.inj he'
      have hii : i + i = 0 := by
        calc
          i + i = i + -i := congrArg (fun t => i + t) hneg.symm
          _ = 0 := add_neg_cancel i
      have hi0 : i = 0 :=
        (ZMod.add_self_eq_zero_iff_eq_zero (by decide : Odd 21)).mp hii
      apply Subtype.ext
      change (n : G) = 1
      rw [hi, hi0, DihedralGroup.r_zero]

private theorem rho_irreducible : rho.IsIrreducible := by
  classical
  refine
    { exists_pair_ne := ⟨⊥, ⊤, ?_⟩
      eq_bot_or_eq_top := ?_ }
  · intro h
    have he : (⊥ : Submodule k V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hmem : e₀ ∈ (⊥ : Submodule k V) := by
      rw [he]
      trivial
    have hz : e₀ = 0 := (Submodule.mem_bot k).mp hmem
    have hz0 := congrFun hz 0
    norm_num [e₀] at hz0
  · intro W
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    have hW' : W.toSubmodule ≠ ⊥ := by
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
    have hex : ∃ w : V, w ∈ W.toSubmodule ∧ w 0 ≠ 0 := by
      by_cases hx : v 0 = 0
      · have hy : v 1 ≠ 0 := by
          intro hy
          apply hv_ne
          funext i
          fin_cases i
          · exact hx
          · exact hy
        refine ⟨rho (DihedralGroup.sr 0) v,
          W.apply_mem_toSubmodule (DihedralGroup.sr 0) hv, ?_⟩
        simpa [rho_reflection] using hy
      · exact ⟨v, hv, hx⟩
    obtain ⟨w, hw, hw0⟩ := hex
    have hproject : rho (DihedralGroup.r 1) w - (4 : k) • w =
        ((5 : k) * w 0) • e₀ := by
      rw [rho_rotation]
      funext i
      fin_cases i
      · change (2 : k) * w 0 - 4 * w 0 = ((5 : k) * w 0) * 1
        rw [← sub_mul, show (2 : k) - 4 = 5 by decide, mul_one]
      · change (4 : k) * w 1 - 4 * w 1 = ((5 : k) * w 0) * 0
        simp
    have haxis : ((5 : k) * w 0) • e₀ ∈ W.toSubmodule := by
      rw [← hproject]
      exact W.toSubmodule.sub_mem
        (W.apply_mem_toSubmodule (DihedralGroup.r 1) hw)
        (W.toSubmodule.smul_mem 4 hw)
    have hc : (5 : k) * w 0 ≠ 0 := mul_ne_zero (by decide) hw0
    have he₀ : e₀ ∈ W.toSubmodule := by
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using
        W.toSubmodule.smul_mem (((5 : k) * w 0)⁻¹) haxis
    have he₁ : e₁ ∈ W.toSubmodule := by
      have h := W.apply_mem_toSubmodule (DihedralGroup.sr 0) he₀
      simpa [rho_reflection, e₀, e₁] using h
    apply Subrepresentation.toSubmodule_injective
    change W.toSubmodule = ⊤
    apply top_unique
    intro z _
    have hmem := W.toSubmodule.add_mem
      (W.toSubmodule.smul_mem (z 0) he₀)
      (W.toSubmodule.smul_mem (z 1) he₁)
    have heq : z 0 • e₀ + z 1 • e₁ = z := by
      funext i
      fin_cases i <;> simp [e₀, e₁, smul_eq_mul]
    exact heq ▸ hmem

private theorem rotation_restriction_nontrivial :
    ¬ Representation.IsTrivial (rho.comp N.subtype) := by
  intro ht
  let : Representation.IsTrivial (rho.comp N.subtype) := ht
  let n : N := ⟨DihedralGroup.r 1, ⟨1, rfl⟩⟩
  have he := Representation.isTrivial_apply (rho.comp N.subtype) n e₀
  change rho (DihedralGroup.r 1) e₀ = e₀ at he
  rw [rho_rotation] at he
  have he0 : (2 : k) = 1 := by simpa [e₀] using congrFun he 0
  exact (by decide : (2 : k) ≠ 1) he0

private theorem card_H : Nat.card H = 7 := by
  let : DecidablePred (fun g : G => g ∈ H) := fun g =>
    inferInstanceAs (Decidable (projection g = 1))
  rw [Nat.card_eq_fintype_card]
  decide

private theorem H_acts_trivially : Representation.IsTrivial (rho.comp H.subtype) where
  out h := by
    change smallRho (projection (h : G)) = 1
    rw [show projection (h : G) = 1 from h.property, map_one]

private theorem card_N : Nat.card N = 21 := by
  let : DecidablePred (fun g : G => g ∈ N) := fun g => by
    cases g with
    | r i => exact isTrue ⟨i, rfl⟩
    | sr i => exact isFalse (by rintro ⟨j, h⟩; cases h)
  rw [Nat.card_eq_fintype_card]
  decide

open scoped MonoidAlgebra

/-- A projective nonzero representation would force the trivially acting
subgroup's order seven to be a unit in F7. -/
private theorem rho_not_projective : ¬ Module.Projective k[G] rho.asModule := by
  intro hp
  have hunit :=
    D5.S3.FiniteGroups.GroupAlgebra.ProjectiveKernelOrder.isUnit_natCard_of_projective_of_isTrivial
      H rho hp H_acts_trivially
  rw [card_H, show ((7 : ℕ) : k) = 0 by decide] at hunit
  exact not_isUnit_zero hunit

/-- An actual nonprojective irreducible module satisfies every original-D
hypothesis other than invertibility of the full rotation order. -/
private theorem originalD_countermodel :
    Finite G ∧ Nat.card G = 42 ∧ FiniteDimensional k V ∧ rho.IsIrreducible ∧
    N.Normal ∧
    (∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1) ∧
    (¬ Representation.IsTrivial (rho.comp N.subtype)) ∧
    Finite H ∧ Nat.card H = 7 ∧ Representation.IsTrivial (rho.comp H.subtype) ∧
    Nat.card N = 21 ∧ ¬ IsUnit (Nat.card N : k) ∧
    ¬ Module.Projective k[G] rho.asModule := by
  refine ⟨inferInstance, DihedralGroup.nat_card, inferInstance, rho_irreducible,
    inferInstance, fixed_rotation_is_one, rotation_restriction_nontrivial,
    inferInstance, card_H, H_acts_trivially, card_N, ?_, rho_not_projective⟩
  rw [card_N, show ((21 : ℕ) : k) = 0 by decide]
  exact not_isUnit_zero

/-- The positive projectivity assertion for the actual constructed representation. -/
def projectivity_claim : Prop := Module.Projective k[G] rho.asModule

/-- The full thirteen-clause original-D countermodel refutes actual projectivity. -/
theorem originalD_counterexample : ¬ projectivity_claim := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnonproj⟩ := originalD_countermodel
  exact hnonproj

end D5.S3.FiniteGroups.OriginalDProjectiveSharpness
