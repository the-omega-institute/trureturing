/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryCentralInnerTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryCentralInnerTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalSupply
set_option autoImplicit false
set_option maxHeartbeats 1400000
/-! Part II p255: the determinant-one ambient unitary diagonal subgroup
induces the full genuine diagonal-similitude action on the central SU.
Norm surjectivity removes the similitude multiplier; an explicit
quadratic Hilbert90 calculation absorbs the remaining determinant at the
two outer coordinates. All corrections precede every group target. -/
namespace NikolovSegal.PartIIUnitaryCentralInnerTorus
open Matrix PartIIUnitriangularActions PartIIUnitaryUpperTorus PartIICentralLevi
open UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

private theorem norm_one_divisor (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (c : Fˣ) (hc : (c:F)*ι (c:F)=1) :
    ∃ t : Fˣ, t/involutionUnit ι t=c := by
  classical
  have hic : ι (c:F)=(c:F)⁻¹ := eq_inv_of_mul_eq_one_right hc
  by_cases hneg : (c:F)=-1
  · have hex : ∃ x : F, ι x≠x := by
      by_contra he
      push_neg at he
      apply hne
      exact RingEquiv.ext he
    obtain ⟨x,hx⟩ := hex
    have ht : x-ι x≠0 := sub_ne_zero.mpr hx.symm
    let t : Fˣ := Units.mk0 (x-ι x) ht
    have hit : ι (t:F)= -(t:F) := by
      change ι (x-ι x)= -(x-ι x)
      rw [map_sub,hinv x]; ring
    refine ⟨t,Units.ext ?_⟩
    simp only [Units.val_div_eq_div_val,involutionUnit_val]
    rw [hit,hneg]
    field_simp
  · have ht : 1+(c:F)≠0 := by intro he; apply hneg; linear_combination he
    let t : Fˣ := Units.mk0 (1+(c:F)) ht
    refine ⟨t,Units.ext ?_⟩
    simp only [Units.val_div_eq_div_val,involutionUnit_val]
    change (1+(c:F))/ι (1+(c:F))=(c:F)
    have hit : ι (1+(c:F))≠0 := by simpa only [map_zero] using ι.injective.ne ht
    apply (div_eq_iff hit).mpr
    rw [map_add,map_one]
    linear_combination -hc

private def extendWeights (ι : RingAut F) (eta : Fin n → Fˣ) (t : Fˣ) : Fin (n+2) → Fˣ :=
  Fin.cons t (Fin.snoc eta (involutionUnit ι t)⁻¹)
private theorem extend_middle (ι : RingAut F) (eta : Fin n → Fˣ) (t : Fˣ) (i : Fin n) :
    extendWeights ι eta t (middle i)=eta i := by simp [extendWeights,middle]
private theorem extend_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (eta : Fin n → Fˣ) (heta : ∀ i, ι (eta i:F)*(eta i.rev:F)=1) (t : Fˣ)
    (i : Fin (n+2)) :
    ι (extendWeights ι eta t i:F)*(extendWeights ι eta t i.rev:F)=1 := by
  refine Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) i) i
  · simp [extendWeights,involutionUnit_val,Units.val_inv_eq_inv_val]
  · simp [extendWeights,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀,hinv (t:F)]
  · have he : j.castSucc.succ.rev=j.rev.castSucc.succ := by
      apply Fin.ext
      simp only [Fin.val_rev,Fin.val_succ,Fin.val_castSucc]; omega
    rw [he]
    change ι (extendWeights ι eta t (middle j):F)*(extendWeights ι eta t (middle j.rev):F)=1
    simpa only [extend_middle] using heta j

private theorem central_isometry_inner (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (eta : Fin n → Fˣ)
    (heta : ∀ i, ι (eta i:F)*(eta i.rev:F)=1) :
    ∃ h : SpecialLinearGroup (Fin (n+2)) F,
      (∀ i j : Fin (n+2), i≠j → h i j=0) ∧ steinberg ι h=h ∧
      ∀ g : SpecialLinearGroup (Fin n) F,
        (MulAut.conj h) (embed g)=embed ((unitOdd% diagonalAut) eta g) := by
  let P : Fˣ := ∏ i, eta i
  have hP : (P:F)*ι (P:F)=1 := by
    have hrev : ∏ i : Fin n, (eta i.rev:F)=∏ i : Fin n, (eta i:F) :=
      Equiv.prod_comp (Fin.revPerm : Fin n≃Fin n) (fun i : Fin n => (eta i:F))
    have he : (∏ i : Fin n, ι (eta i:F))*(∏ i : Fin n, (eta i.rev:F))=1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i hi => heta i)
    dsimp only [P]
    rw [Units.coe_prod,map_prod]
    simpa only [hrev,mul_comm] using he
  have hPinv : (P⁻¹:Fˣ)*involutionUnit ι P⁻¹=1 := by
    apply Units.ext
    simp only [Units.val_mul,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀,Units.val_one]
    rw [← mul_inv,hP,inv_one]
  obtain ⟨t,ht⟩ := norm_one_divisor ι hinv hne P⁻¹ (congrArg (fun z : Fˣ => (z:F)) hPinv)
  let w := extendWeights ι eta t
  have hw : ∏ i, w i=1 := by
    simp only [w,extendWeights,Fin.prod_cons,Fin.prod_snoc]
    change t*(P*(involutionUnit ι t)⁻¹)=1
    calc
      _ = (t/involutionUnit ι t)*P := by simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      _ = 1 := by rw [ht,inv_mul_cancel]
  let h := (radicalTorus% diagonalSL) w hw
  have hh : steinberg ι h=h := (unitaryTorus% diagonal_fixed) ι w hw (extend_unitary ι hinv eta heta t)
  refine ⟨h,?_,hh,?_⟩
  · intro i j hij
    change (Matrix.diagonal (fun i => (w i:F))) i j=0
    simp [Matrix.diagonal_apply,hij]
  · intro g
    rw [(radicalTorus% diagonalSL_action),centralKernel% diagonal_embed]
    have he : (fun i => w (middle i))=eta := funext (extend_middle ι eta t)
    rw [he]

/-- Full actual central unitary diagonal-similitude action, realized by
ONE determinant-one ambient UNITARY inner correction before ALL g.
The multiplier is a genuine fixed-field unit; the normalization and
determinant absorber are constructed, not supplied as a normal form. -/
theorem actual_unitary_central_diagonal_inner (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (eta : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (heta : ∀ i, ι (eta i:F)*(eta i.rev:F)=((c:fixedField ι):F)) :
    ∃ h : SpecialLinearGroup (Fin (n+2)) F,
      (∀ i j : Fin (n+2), i≠j → h i j=0) ∧ steinberg ι h=h ∧
      ∀ g : SpecialLinearGroup (Fin n) F,
        (MulAut.conj h) (embed g)=embed ((unitOdd% diagonalAut) eta g) := by
  obtain ⟨lambda,hlambda⟩ := norm_units_surjective ι hinv hne c⁻¹
  let eta' : Fin n → Fˣ := fun i => lambda*eta i
  have heta' : ∀ i, ι (eta' i:F)*(eta' i.rev:F)=1 := by
    intro i
    simp only [eta',Units.val_mul,map_mul]
    calc
      _ = ((lambda:F)*ι (lambda:F))*(ι (eta i:F)*(eta i.rev:F)) := by ring
      _ = 1 := by rw [hlambda,heta i]; simp
  obtain ⟨h,hh,hhu,hcover⟩ := central_isometry_inner ι hinv hne eta' heta'
  refine ⟨h,hh,hhu,?_⟩
  intro g
  rw [hcover]
  congr 1
  apply SpecialLinearGroup.ext
  intro i j
  rw [(unitOdd% diagonal_entry),(unitOdd% diagonal_entry)]
  simp only [eta',Units.val_mul,_root_.mul_inv_rev,Units.val_inv_eq_inv_val]
  field_simp

end NikolovSegal.PartIIUnitaryCentralInnerTorus
