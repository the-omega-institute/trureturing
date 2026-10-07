/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2RootAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Determinant-one alignment of distinct conjugate root pairs. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2RootNormalization
set_option autoImplicit false
/-! Actual inner alignment of two distinct conjugates of the A1 root.
Together with PartIISL2RootNormalization, this reconstructs field coordinates
and scalar corrections from genuine root-image conjugacy. The independent
Sylow proof needed to supply that conjugacy for arbitrary beta stays explicit. -/
namespace NikolovSegal.PartIIA1RootSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem conjugate_upper_of_lower_zero (A : SL(2,F)) (ha : A 1 0 = 0) (t : F) :
    MulAut.conj A (upper t) = upper ((A 0 0)^2*t) := by
  simp only [MulAut.conj_apply]
  apply Subtype.ext
  change A.val*(upper t).val*Matrix.adjugate A.val = (upper ((A 0 0)^2*t)).val
  rw [Matrix.adjugate_fin_two]
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  simp only [ha,mul_zero,sub_zero] at hd
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,ha]
  all_goals try ring
  all_goals linear_combination hd

private theorem conjugate_lower_of_upper_zero (A : SL(2,F)) (ha : A 0 0 = 0) (t : F) :
    MulAut.conj A (upper t) = lower (-(A 1 0)^2*t) := by
  simp only [MulAut.conj_apply]
  apply Subtype.ext
  change A.val*(upper t).val*Matrix.adjugate A.val = (lower (-(A 1 0)^2*t)).val
  rw [Matrix.adjugate_fin_two]
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  simp only [ha,zero_mul,zero_sub] at hd
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper,lower,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,ha]
  all_goals try ring
  all_goals linear_combination hd

private theorem lower_zero_upper_range (A : SL(2,F)) (ha : A 1 0 = 0) :
    Set.range (fun t => MulAut.conj A (upper t)) = Set.range upper := by
  have ha0 : A 0 0 ≠ 0 := by
    intro hz
    have hdet := A.property
    rw [Matrix.det_fin_two] at hdet
    simp [ha,hz] at hdet
  have hp : (A 0 0)^2 ≠ 0 := pow_ne_zero _ ha0
  apply Set.ext
  intro v
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨(A 0 0)^2*t,(conjugate_upper_of_lower_zero A ha t).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t/((A 0 0)^2),?_⟩
    change MulAut.conj A (upper (t/((A 0 0)^2))) = upper t
    rw [conjugate_upper_of_lower_zero A ha]
    congr 1
    field_simp

private theorem upper_zero_lower_range (A : SL(2,F)) (ha : A 0 0 = 0) :
    Set.range (fun t => MulAut.conj A (upper t)) = Set.range lower := by
  have ha1 : A 1 0 ≠ 0 := by
    intro hz
    have hdet := A.property
    rw [Matrix.det_fin_two] at hdet
    simp [ha,hz] at hdet
  have hp : -(A 1 0)^2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ha1)
  apply Set.ext
  intro v
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨-(A 1 0)^2*t,(conjugate_lower_of_upper_zero A ha t).symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨t/(-(A 1 0)^2),?_⟩
    change MulAut.conj A (upper (t/(-(A 1 0)^2))) = lower t
    rw [conjugate_lower_of_upper_zero A ha]
    congr 1
    field_simp

private theorem conjugate_range_comp (A B : SL(2,F)) (root : F → SL(2,F)) :
    MulAut.conj A '' Set.range (fun t => MulAut.conj B (root t)) =
      Set.range (fun t => MulAut.conj (A*B) (root t)) := by
  rw [← Set.range_comp']
  congr 1
  funext t
  simp only [MulAut.conj_apply,mul_inv_rev]
  group

/-- Actual ordered root-pair alignment: ANY two DISTINCT conjugates of the
positive root subgroup can be sent to the standard positive/negative pair
by ONE determinant-one matrix. No Sylow/classification premise is hidden. -/
private theorem root_pair_alignment (A B : SL(2,F))
    (hne : Set.range (fun t => MulAut.conj A (upper t)) ≠
      Set.range (fun t => MulAut.conj B (upper t))) :
    ∃ z : SL(2,F),
      Set.range (fun t => MulAut.conj (z*A) (upper t)) = Set.range upper ∧
      Set.range (fun t => MulAut.conj (z*B) (upper t)) = Set.range lower := by
  let C := A⁻¹*B
  have hc : C 1 0 ≠ 0 := by
    intro hc
    apply hne
    have he := lower_zero_upper_range C hc
    have hh := congrArg (fun V => MulAut.conj A '' V) he
    rw [conjugate_range_comp] at hh
    have hac : A*C = B := by dsimp [C]; group
    rw [hac] at hh
    rw [← Set.range_comp'] at hh
    exact hh.symm
  let v := upper (-(C 0 0)/(C 1 0))
  let z := v*A⁻¹
  have hza : z*A = v := by dsimp [z]; group
  have hzb : z*B = v*C := by dsimp [z,C]; group
  have hv : v 1 0 = 0 := by simp [v,upper,Matrix.SpecialLinearGroup.transvection_coe]
  have hvc : (v*C) 0 0 = 0 := by
    simp [v,upper,Matrix.SpecialLinearGroup.transvection_coe,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Fin.sum_univ_two]
    field_simp [hc]
    ring
  refine ⟨z,?_,?_⟩
  · rw [hza]
    exact lower_zero_upper_range v hv
  · rw [hzb]
    exact upper_zero_lower_range (v*C) hvc

/-- Genuine scalar supply once the images of the actual two roots are known
to be actual root conjugates. Alignment and semilinearity are constructed;
only the separate Sylow/root-conjugacy theorem is needed for arbitrary beta.
The combined scalar correction is fixed BEFORE every target. -/
theorem actual_root_conjugate_SL2_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (4*M) → MulAut SL(2,F)) (e : Fin (4*M) → ℕ)
    (A B : Fin (4*M) → SL(2,F))
    (hu : ∀ j, Set.range (fun t => beta j (upper t)) =
      Set.range (fun t => MulAut.conj (A j) (upper t)))
    (hl : ∀ j, Set.range (fun t => beta j (lower t)) =
      Set.range (fun t => MulAut.conj (B j) (upper t))) :
    PartIIScalarProductInput q (4*M) beta e := by
  classical
  have hne : ∀ j, Set.range (fun t => MulAut.conj (A j) (upper t)) ≠
      Set.range (fun t => MulAut.conj (B j) (upper t)) := by
    intro j h
    rw [← hu,← hl] at h
    have hm : beta j (upper 1) ∈ Set.range (fun t => beta j (lower t)) := by
      rw [← h]; exact ⟨1,rfl⟩
    obtain ⟨t,ht⟩ := hm
    have hh := (beta j).injective ht
    have hc := congrArg (fun g : SL(2,F) => g.val 0 1) hh
    simp [upper,lower,Matrix.SpecialLinearGroup.transvection_coe] at hc
  choose z hzu hzl using fun j => root_pair_alignment (A j) (B j) (hne j)
  let gamma := fun j => MulAut.conj (z j)*beta j
  have hgu : ∀ j, Set.range (fun t => gamma j (upper t)) = Set.range upper := by
    intro j
    change Set.range (fun t => MulAut.conj (z j) (beta j (upper t))) = _
    rw [Set.range_comp',hu,conjugate_range_comp,hzu]
  have hgl : ∀ j, Set.range (fun t => gamma j (lower t)) = Set.range lower := by
    intro j
    change Set.range (fun t => MulAut.conj (z j) (beta j (lower t))) = _
    rw [Set.range_comp',hl,conjugate_range_comp,hzl]
  intro he
  obtain ⟨y,hy⟩ := actual_root_stabilizing_SL2_scalar_product hq hM hF gamma e hgu hgl he
  let x := fun j => y j*((beta j).symm (z j))⁻¹
  have hx : ∀ j, beta j*MulAut.conj (x j)⁻¹ = gamma j*MulAut.conj (y j)⁻¹ := by
    intro j
    apply MulEquiv.ext
    intro s
    simp only [gamma,MulAut.mul_apply,MulAut.conj_apply]
    simp only [x,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  refine ⟨x,?_⟩
  intro target
  obtain ⟨c,hc⟩ := hy target
  refine ⟨c,?_⟩
  simpa only [hx] using hc
end NikolovSegal.PartIIA1RootSupply
