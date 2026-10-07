/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentSylow
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentWidth

set_option autoImplicit false

/-! Actual PSL3 upper-unipotent coordinates. Native SL center recognition
and the accepted actual U3 carrier prove that central quotient is injective
on U3 over every field. No central-intersection hypothesis is used. -/
namespace NikolovSegal.PartIIPSL3Unipotent
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIISL3UnipotentSylow
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- The image of actual U3 in the literal native central quotient PSL3. -/
def projectiveUpperUnipotent : Subgroup PSL(3,F) :=
  (U3 (F := F)).map (QuotientGroup.mk' (Subgroup.center SL(3,F)))

/-- The actual accepted upper chart followed by the actual central quotient. -/
def projectiveUpper3 (a b c : F) : PSL(3,F) :=
  QuotientGroup.mk' (Subgroup.center SL(3,F)) (upper3 a b c)

/-- Native central-scalar recognition and the actual unit diagonal force
every central element of U3 to be the identity, in every characteristic. -/
theorem U3_center_trivial (A : SL(3,F)) (hA : A ∈ U3)
    (hc : A ∈ Subgroup.center SL(3,F)) : A = 1 := by
  have hs := scalar_eq_self_of_mem_center hc (0 : Fin 3)
  have hd := ((mem_U3_iff A).mp hA).2 0
  apply Subtype.ext
  change A.val = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← hs,hd]
  simp

/-- The actual quotient restriction on actual U3 is injective. -/
theorem quotient_U3_injective : Function.Injective
    (fun A : U3 (F := F) => QuotientGroup.mk' (Subgroup.center SL(3,F)) A.val) := by
  apply (injective_iff_map_eq_one
    ((QuotientGroup.mk' (Subgroup.center SL(3,F))).comp (U3 (F := F)).subtype)).mpr
  intro A hA
  have hc : A.val ∈ Subgroup.center SL(3,F) :=
    (QuotientGroup.eq_one_iff A.val).mp hA
  apply Subtype.ext
  exact U3_center_trivial A.val A.property hc

/-- The literal projective carrier retains all three actual upper3 coordinates. -/
theorem mem_projectiveUpperUnipotent (g : PSL(3,F)) :
    g ∈ projectiveUpperUnipotent ↔ ∃ a b c : F, projectiveUpper3 a b c = g := by
  constructor
  · intro hg
    obtain ⟨A,hA,hg⟩ := Subgroup.mem_map.mp hg
    obtain ⟨a,b,c,rfl⟩ := hA
    exact ⟨a,b,c,hg⟩
  · rintro ⟨a,b,c,rfl⟩
    exact Subgroup.mem_map.mpr ⟨upper3 a b c,⟨a,b,c,rfl⟩,rfl⟩

/-- A genuine group equivalence, given by the actual quotient on U3. -/
noncomputable def projectiveUpperEquiv :
    U3 (F := F) ≃* projectiveUpperUnipotent (F := F) := by
  let f := (QuotientGroup.mk' (Subgroup.center SL(3,F))).comp (U3 (F := F)).subtype
  have hf : ∀ A, f A ∈ projectiveUpperUnipotent := fun A =>
    Subgroup.mem_map.mpr ⟨A.val,A.property,rfl⟩
  apply MulEquiv.ofBijective (f.codRestrict projectiveUpperUnipotent hf)
  constructor
  · intro A B h
    apply quotient_U3_injective
    exact congrArg Subtype.val h
  · intro g
    obtain ⟨A,hA,hg⟩ := Subgroup.mem_map.mp g.property
    exact ⟨⟨A,hA⟩,Subtype.ext hg⟩

@[simp] theorem projectiveUpperEquiv_apply (A : U3 (F := F)) :
    (projectiveUpperEquiv A : PSL(3,F)) =
      QuotientGroup.mk' (Subgroup.center SL(3,F)) A.val := rfl

/-- Genuine three-field coordinates transported from the accepted actual
U3 chart; the nonabelian group structure is retained by projectiveUpperEquiv. -/
noncomputable def projectiveUpperCoordinate :
    (Fin 3 → F) ≃ projectiveUpperUnipotent (F := F) :=
  (upperCoordinateEquiv (F := F)).trans projectiveUpperEquiv.toEquiv

@[simp] theorem projectiveUpperCoordinate_apply (v : Fin 3 → F) :
    (projectiveUpperCoordinate v : PSL(3,F)) = projectiveUpper3 (v 0) (v 1) (v 2) := rfl

end NikolovSegal.PartIIPSL3Unipotent


set_option autoImplicit false

/-! Defining-characteristic Sylow descent to literal PSL3 and normalization
of every bare PSL3 automorphism. Native Sylow mapping and conjugacy are
directly reused; no automorphism lift, simplicity or size premise occurs. -/
namespace NikolovSegal.PartIIPSL3Unipotent
open NikolovSegal.PartIISL3UnipotentSylow
open scoped MatrixGroups Pointwise
universe u
variable {F : Type u} [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The accepted actual U3 Sylow mapped by the actual surjective central quotient. -/
def projectiveUpperSylow : Sylow p PSL(3,F) :=
  (U3Sylow (F := F) p).mapSurjective
    (f := QuotientGroup.mk' (Subgroup.center SL(3,F)))
    (QuotientGroup.mk'_surjective _)

@[simp] theorem projectiveUpperSylow_coe :
    (projectiveUpperSylow (F := F) p : Subgroup PSL(3,F)) = projectiveUpperUnipotent := rfl

include p in
/-- Genuine Sylow recognition for the literal projective subgroup. -/
theorem exists_projectiveUpper_sylow :
    ∃ P : Sylow p PSL(3,F), (P : Subgroup PSL(3,F)) = projectiveUpperUnipotent :=
  ⟨projectiveUpperSylow p,projectiveUpperSylow_coe p⟩

include p in
/-- For every bare beta, beta(V)=g V g⁻¹. No lift to SL3 is assumed. -/
theorem automorphism_projectiveUpper_conjugate (beta : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom =
      (projectiveUpperUnipotent (F := F)).map (MulAut.conj g).toMonoidHom := by
  let P := projectiveUpperSylow (F := F) p
  let Q := P.mapSurjective (f := beta.toMonoidHom) beta.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P Q
  refine ⟨g,?_⟩
  have he := congrArg (fun R : Sylow p PSL(3,F) => (R : Subgroup PSL(3,F))) hg
  change (projectiveUpperUnipotent (F := F)).map (MulAut.conj g).toMonoidHom =
    (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom at he
  exact he.symm

include p in
/-- Actual projective inner correction normalizes the literal subgroup.
Direction: beta(V)=g V g⁻¹, so (conj g⁻¹)*beta preserves V. -/
theorem automorphism_projectiveUpper_normalize (beta : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F),
      (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom =
        (projectiveUpperUnipotent (F := F)).map (MulAut.conj g).toMonoidHom ∧
      (projectiveUpperUnipotent (F := F)).map
        (MulAut.conj g⁻¹ * beta).toMonoidHom = projectiveUpperUnipotent := by
  obtain ⟨g,hg⟩ := automorphism_projectiveUpper_conjugate p beta
  refine ⟨g,hg,?_⟩
  have hcomp : (MulAut.conj g⁻¹ * beta).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp beta.toMonoidHom := by
    ext x
    rfl
  rw [hcomp,← Subgroup.map_map,hg,Subgroup.map_map]
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id PSL(3,F) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [hid,Subgroup.map_id]

end NikolovSegal.PartIIPSL3Unipotent


set_option autoImplicit false

/-! Every-field actual PSL3 alternating unipotent width. The accepted actual
SL3 Fin25 decomposition is transported by the genuine central quotient;
native list-product functoriality retains the exact order of all factors. -/
namespace NikolovSegal.PartIIPSL3UnipotentWidth
open NikolovSegal.PartIIPSL3Unipotent
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
local notation "π₃" => QuotientGroup.mk' (Subgroup.center SL(3,F))

/-- The actual image of the accepted literal lower-unitriangular SL3 subgroup. -/
def projectiveLowerUnipotent : Subgroup PSL(3,F) :=
  (NikolovSegal.PartIISL3UnipotentWidth.lowerUnipotent (F := F)).map π₃

/-- Literal lower-unitriangular representatives for the actual projective
lower subgroup; the upper zero entries and every unit diagonal are retained. -/
theorem mem_projectiveLowerUnipotent_iff (g : PSL(3,F)) :
    g ∈ projectiveLowerUnipotent ↔
      ∃ A : SL(3,F), π₃ A = g ∧
        ((∀ i j : Fin 3, i < j → A i j = 0) ∧ (∀ i : Fin 3, A i i = 1)) := by
  constructor
  · intro hg
    obtain ⟨A,hA,heq⟩ := Subgroup.mem_map.mp hg
    exact ⟨A,heq,(NikolovSegal.PartIISL3UnipotentWidth.mem_lowerUnipotent_iff A).mp hA⟩
  · rintro ⟨A,rfl,hA⟩
    exact Subgroup.mem_map.mpr
      ⟨A,(NikolovSegal.PartIISL3UnipotentWidth.mem_lowerUnipotent_iff A).mpr hA,rfl⟩

/-- Every actual PSL3 element over every field is an ordered product of
exactly 25 alternating actual projective upper/lower unipotent factors. -/
theorem alternating_unipotent_25 (g : PSL(3,F)) :
    ∃ u : Fin 25 → PSL(3,F),
      (∀ j, if Even j.val then u j ∈ projectiveUpperUnipotent
        else u j ∈ projectiveLowerUnipotent) ∧
      orderedProduct u = g := by
  obtain ⟨A,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) g
  obtain ⟨v,hv,hprod⟩ := NikolovSegal.PartIISL3UnipotentWidth.alternating_unipotent_25 A
  refine ⟨fun j => π₃ (v j),?_,?_⟩
  · intro j
    have hjv := hv j
    by_cases hj : Even j.val
    · simp only [if_pos hj] at hjv ⊢
      exact Subgroup.mem_map.mpr ⟨v j,hjv,rfl⟩
    · simp only [if_neg hj] at hjv ⊢
      exact (mem_projectiveLowerUnipotent_iff _).mpr
        ⟨v j,rfl,(NikolovSegal.PartIISL3UnipotentWidth.mem_lowerUnipotent_iff (v j)).mp hjv⟩
  · simpa only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] using
      congrArg π₃ hprod

end NikolovSegal.PartIIPSL3UnipotentWidth
