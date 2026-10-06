/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual upper-root Sylow maximality and automorphism conjugacy. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA1RootSupply
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

/-! The actual positive SL2 root is a Sylow subgroup in defining
characteristic. We consume the accepted `upper` definition and Mathlib's
p-group fixed-point theorem and Sylow conjugacy, without an SL2 order formula.
Conjugation is consistently `g * A * g⁻¹` (`MulAut.conj g`). -/
namespace NikolovSegal.PartIISL2RootSylow
open NikolovSegal.PartIIA1RootSupply Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
universe u
variable {F : Type u} [Field F]

/-- Additive field parameters mapped to the actual accepted upper matrices. -/
def upperHom : Multiplicative F →* SL(2,F) where
  toFun t := upper t.toAdd
  map_one' := transvection_coeff_zero zero_ne_one
  map_mul' t s := transvection_add zero_ne_one t.toAdd s.toAdd

/-- The literal upper-root subgroup `{upper(t) | t : F}`. -/
def upperRoot : Subgroup SL(2,F) := (upperHom (F := F)).range

theorem mem_upperRoot (A : SL(2,F)) : A ∈ upperRoot ↔ ∃ t : F, upper t = A := by
  change (∃ t : Multiplicative F, upper t.toAdd = A) ↔ _
  exact ⟨fun ⟨t,ht⟩ => ⟨t.toAdd,ht⟩,fun ⟨t,ht⟩ => ⟨Multiplicative.ofAdd t,ht⟩⟩

theorem upper_mem_upperRoot (t : F) : upper t ∈ upperRoot :=
  (mem_upperRoot _).mpr ⟨t,rfl⟩

theorem upperHom_injective : Function.Injective (upperHom (F := F)) := by
  intro t s h
  have he := congrArg (fun A : SL(2,F) => A 0 1) h
  simpa [upperHom,upper,transvection_coe] using he

/-- The pointwise stabilizer of the first basis vector is exactly the upper root. -/
theorem mem_upperRoot_iff_fix_first (A : SL(2,F)) :
    A ∈ upperRoot ↔ A • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 := by
  constructor
  · rintro h
    obtain ⟨t,rfl⟩ := (mem_upperRoot _).mp h
    exact transvection_smul_single_fst zero_ne_one t
  · intro h
    have h00 : A 0 0 = 1 := by
      simpa [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
        Matrix.mulVec,Fin.sum_univ_two] using congrFun h 0
    have h10 : A 1 0 = 0 := by
      simpa [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
        Matrix.mulVec,Fin.sum_univ_two] using congrFun h 1
    have h11 : A 1 1 = 1 := by
      have hd := A.property
      rw [Matrix.det_fin_two] at hd
      simpa only [h00,h10,one_mul,mul_zero,sub_zero] using hd
    apply (mem_upperRoot _).mpr
    refine ⟨A 0 1,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upper,transvection_coe,h00,h10,h11]

variable [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
theorem upperRoot_isPGroup : IsPGroup p (upperRoot (F := F)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F p
  have hfield : IsPGroup p (Multiplicative F) := IsPGroup.of_card (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_multiplicative] using hn)
  exact hfield.of_equiv (MonoidHom.ofInjective (upperHom_injective (F := F)))

/-- Every genuine p-subgroup has a nonzero common fixed vector in F².
This directly consumes the native orbit-count congruence theorem. -/
theorem pSubgroup_fixed_vector (H : Subgroup SL(2,F)) (hH : IsPGroup p H) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ A : H, (A : SL(2,F)) • v = v := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F p
  have hpF : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card,hn]
    exact dvd_pow_self p n.ne_zero
  have hpV : p ∣ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun,Nat.card_fin]
    exact hpF.trans (dvd_pow_self (Nat.card F) (by decide : 2 ≠ 0))
  have hz : (0 : Fin 2 → F) ∈ MulAction.fixedPoints H (Fin 2 → F) := by
    exact MulAction.mem_fixedPoints.mpr (fun _ => smul_zero _)
  obtain ⟨v,hv,hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 2 → F) hpV hz
  exact ⟨v,hne.symm,fun A => MulAction.mem_fixedPoints.mp hv A⟩

/-- Maximality uses the actual upper(1) action: its fixed vectors have second
coordinate zero, so any overgroup's nonzero fixed vector forces it to fix e₁. -/
theorem upperRoot_p_maximal {H : Subgroup SL(2,F)} (hH : IsPGroup p H)
    (hUH : upperRoot ≤ H) : H = upperRoot := by
  classical
  obtain ⟨v,hv,hfix⟩ := pSubgroup_fixed_vector p H hH
  have hu := hfix ⟨upper 1,hUH (upper_mem_upperRoot 1)⟩
  have hv1 : v 1 = 0 := by
    have h := congrFun hu 0
    simp [upper,Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      transvection_coe,Matrix.mulVec] at h
    exact h
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h,hv1]
  apply le_antisymm _ hUH
  intro A hA
  have h := hfix ⟨A,hA⟩
  have h00 : A 0 0 = 1 := by
    have hh := congrFun h 0
    simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      Matrix.mulVec,hv1] at hh
    exact (mul_right_cancel₀ hv0 (by simpa using hh))
  have h10 : A 1 0 = 0 := by
    have hh := congrFun h 1
    simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      Matrix.mulVec,hv1] at hh
    exact hh.resolve_right hv0
  apply (mem_upperRoot_iff_fix_first A).mpr
  ext i
  fin_cases i <;> simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
    Matrix.mulVec,h00,h10]

/-- A genuine Sylow object whose underlying subgroup is the actual upper root. -/
def upperSylow : Sylow p SL(2,F) where
  toSubgroup := upperRoot
  isPGroup' := upperRoot_isPGroup p
  is_maximal' := upperRoot_p_maximal p

include p in
/-- Every arbitrary SL2 automorphism carries the actual upper root to its
conjugate by a determinant-one matrix. Direction: beta(U) = g U g⁻¹. -/
theorem automorphism_upperRoot_conjugate (beta : MulAut SL(2,F)) :
    ∃ g : SL(2,F),
      (upperRoot (F := F)).map beta.toMonoidHom =
        (upperRoot (F := F)).map (MulAut.conj g).toMonoidHom := by
  let P := upperSylow (F := F) p
  let Q := P.mapSurjective (f := beta.toMonoidHom) beta.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) P Q
  refine ⟨g,?_⟩
  have he := congrArg (fun R : Sylow p SL(2,F) => (R : Subgroup SL(2,F))) hg
  change (upperRoot (F := F)).map (MulAut.conj g).toMonoidHom =
    (upperRoot (F := F)).map beta.toMonoidHom at he
  exact he.symm

end NikolovSegal.PartIISL2RootSylow
