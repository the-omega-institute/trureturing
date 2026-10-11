/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentSylow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentStructure

set_option autoImplicit false

/-! The actual SL3 upper-unitriangular subgroup is a defining-characteristic
Sylow subgroup. Maximality reduces the bottom two-dimensional action of any
p-overgroup to the accepted actual SL2 upper-root maximality theorem. -/
namespace NikolovSegal.PartIISL3UnipotentSylow
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIIA1RootSupply
  NikolovSegal.PartIISL2RootSylow Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
universe u
variable {F : Type u} [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
theorem U3_isPGroup : IsPGroup p (U3 (F := F)) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F p
  have hc : Nat.card F = p^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  apply IsPGroup.of_card (n := (n:ℕ)*3)
  rw [card_U3,hc,← pow_mul]

theorem pSubgroup_fixed_vector (H : Subgroup SL(3,F)) (hH : IsPGroup p H) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ ∀ A : H, (A : SL(3,F)) • v = v := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F p
  have hpF : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card,hn]
    exact dvd_pow_self p n.ne_zero
  have hpV : p ∣ Nat.card (Fin 3 → F) := by
    rw [Nat.card_fun,Nat.card_fin]
    exact hpF.trans (dvd_pow_self (Nat.card F) (by decide : 3 ≠ 0))
  have hz : (0 : Fin 3 → F) ∈ MulAction.fixedPoints H (Fin 3 → F) :=
    MulAction.mem_fixedPoints.mpr (fun _ => smul_zero _)
  obtain ⟨v,hv,hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 3 → F) hpV hz
  exact ⟨v,hne.symm,fun A => MulAction.mem_fixedPoints.mp hv A⟩

theorem p_overgroup_fix_first {H : Subgroup SL(3,F)} (hH : IsPGroup p H)
    (hUH : U3 ≤ H) :
    ∀ A : H, (A : SL(3,F)) • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1 := by
  classical
  obtain ⟨v,hv,hfix⟩ := pSubgroup_fixed_vector p H hH
  have hv1 : v 1 = 0 := by
    have hu := hfix ⟨upper3 1 0 0,hUH ⟨1,0,0,rfl⟩⟩
    change Matrix.mulVec (upper3 (1:F) 0 0).val v = v at hu
    have h := congrFun hu 0
    simpa [upper3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h
  have hv2 : v 2 = 0 := by
    have hu := hfix ⟨upper3 0 1 0,hUH ⟨0,1,0,rfl⟩⟩
    change Matrix.mulVec (upper3 (0:F) 1 0).val v = v at hu
    have h := congrFun hu 1
    simpa [upper3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h,hv1,hv2]
  intro A
  have h00 : A.val 0 0 = 1 := by
    have h := congrFun (hfix A) 0
    simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv1,hv2] at h
    exact mul_right_cancel₀ hv0 (by simpa using h)
  have h10 : A.val 1 0 = 0 := by
    have h := congrFun (hfix A) 1
    simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv1,hv2] at h
    exact h.resolve_right hv0
  have h20 : A.val 2 0 = 0 := by
    have h := congrFun (hfix A) 2
    simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv1,hv2] at h
    exact h.resolve_right hv0
  ext i
  fin_cases i <;> simp [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Pi.single_apply,h00,h10,h20]

theorem U3_p_maximal {H : Subgroup SL(3,F)} (hH : IsPGroup p H)
    (hUH : U3 ≤ H) : H = U3 := by
  classical
  have hH0 := p_overgroup_fix_first p hH hUH
  let f := bottomBlockHom H hH0
  have hI : IsPGroup p f.range :=
    hH.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hUI : upperRoot (F := F) ≤ f.range := by
    intro B hB
    obtain ⟨t,rfl⟩ := (mem_upperRoot B).mp hB
    refine ⟨⟨upper3 0 t 0,hUH ⟨0,t,0,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change bottomBlock (upper3 0 t 0) = (upper t).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bottomBlock,upper3,upper,transvection_coe]
  have hIR : f.range = upperRoot := upperRoot_p_maximal p hI hUI
  apply le_antisymm _ hUH
  intro A hA
  have hc := first_column_of_fix A (hH0 ⟨A,hA⟩)
  have hB : f ⟨A,hA⟩ ∈ upperRoot := by
    rw [← hIR]
    exact ⟨⟨A,hA⟩,rfl⟩
  obtain ⟨t,ht⟩ := (mem_upperRoot _).mp hB
  have h11 : A 1 1 = 1 := by
    have h := congrArg (fun B : SL(2,F) => B 0 0) ht
    change (upper t) 0 0 = A 1 1 at h
    simpa [upper,transvection_coe] using h.symm
  have h21 : A 2 1 = 0 := by
    have h := congrArg (fun B : SL(2,F) => B 1 0) ht
    change (upper t) 1 0 = A 2 1 at h
    simpa [upper,transvection_coe] using h.symm
  have h22 : A 2 2 = 1 := by
    have h := congrArg (fun B : SL(2,F) => B 1 1) ht
    change (upper t) 1 1 = A 2 2 at h
    simpa [upper,transvection_coe] using h.symm
  apply (mem_U3_iff A).mpr
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hc 1,hc 2]
  · intro i
    fin_cases i <;> simp [hc 0,h11,h22]

/-- Genuine actual SL3 upper-unitriangular Sylow recognition. -/
def U3Sylow : Sylow p SL(3,F) where
  toSubgroup := U3
  isPGroup' := U3_isPGroup p
  is_maximal' := U3_p_maximal p

include p in
theorem exists_U3_sylow : ∃ P : Sylow p SL(3,F), (P : Subgroup SL(3,F)) = U3 :=
  ⟨U3Sylow p,rfl⟩

include p in
/-- Every bare SL3 automorphism maps actual U3 to g U3 g⁻¹, including fields2/3. -/
theorem automorphism_U3_conjugate (beta : MulAut SL(3,F)) :
    ∃ g : SL(3,F), (U3 (F := F)).map beta.toMonoidHom =
      (U3 (F := F)).map (MulAut.conj g).toMonoidHom := by
  let P := U3Sylow (F := F) p
  let Q := P.mapSurjective (f := beta.toMonoidHom) beta.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F) P Q
  refine ⟨g,?_⟩
  have he := congrArg (fun R : Sylow p SL(3,F) => (R : Subgroup SL(3,F))) hg
  change (U3 (F := F)).map (MulAut.conj g).toMonoidHom =
    (U3 (F := F)).map beta.toMonoidHom at he
  exact he.symm

end NikolovSegal.PartIISL3UnipotentSylow
