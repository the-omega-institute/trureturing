/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALevi
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALevi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryCentralInnerTorus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
/-! Part II Definition6.8 and p255: the genuine type-A Levi in the
anti-diagonal unitary group. Its blocks are g and iota(g^-T), not two
independent matrices. The embedding is injective, determinant one and
Hermitian preserving, and its positive unipotent lies in actual U*. -/
namespace NikolovSegal.PartIIUnitaryTypeALevi
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIUnitaryUpperTorus PartIIUnitaryTorusSupply UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {d : ℕ}

private def lower (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F) : SpecialLinearGroup (Fin d) F :=
  SpecialLinearGroup.transpose (fieldAut ι g⁻¹)
private theorem lower_entry (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F) (i j : Fin d) :
    lower ι g i j=ι (g⁻¹ j i) := rfl
private theorem lower_mul (ι : RingAut F) (g h : SpecialLinearGroup (Fin d) F) :
    lower ι (g*h)=lower ι g*lower ι h := by
  apply Subtype.ext
  dsimp only [lower,SpecialLinearGroup.transpose]
  rw [_root_.mul_inv_rev,map_mul,SpecialLinearGroup.coe_mul,Matrix.transpose_mul]
  rfl

private def pairEmbed (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin d⊕Fin d) F where
  toFun g := ⟨fromBlocks g.val 0 0 (lower ι g).val,by
    rw [det_fromBlocks_zero₂₁,g.prop,(lower ι g).prop,mul_one]⟩
  map_one' := by
    apply Subtype.ext
    have hl : lower (d:=d) ι 1=1 := by apply SpecialLinearGroup.ext; intro i j; simp [lower_entry,Matrix.one_apply,eq_comm]
    simp [hl,fromBlocks_one]
  map_mul' g h := by
    apply Subtype.ext
    simp [lower_mul,SpecialLinearGroup.coe_mul,fromBlocks_multiply]

/-- Actual type-A Levi embedding, native Fin(2d) anti-diagonal coordinates. -/
def embed (ι : RingAut F) : SpecialLinearGroup (Fin d) F →*
    SpecialLinearGroup (Fin (2*d)) F :=
  (SLnUnipotentWidth.reindexSL (evenLabel d)).toMonoidHom.comp (pairEmbed ι)

theorem actual_typeA_levi_entry (ι : RingAut F) (g : SpecialLinearGroup (Fin d) F)
    (i j : Fin d⊕Fin d) :
    embed ι g (evenLabel d i) (evenLabel d j)=
      fromBlocks g.val 0 0 (lower ι g).val i j := by
  simp [embed,SLnUnipotentWidth.reindexSL,pairEmbed,Matrix.reindex_apply,Matrix.submatrix_apply]

theorem actual_typeA_levi_injective (ι : RingAut F) : Function.Injective (embed (d:=d) ι) := by
  intro g h he
  apply SpecialLinearGroup.ext
  intro i j
  have hh := congrArg (fun a : SpecialLinearGroup (Fin (2*d)) F =>
    a (evenLabel d (.inl i)) (evenLabel d (.inl j))) he
  simpa only [actual_typeA_levi_entry,fromBlocks_apply₁₁] using hh

theorem actual_typeA_levi_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) : steinberg ι (embed ι g)=embed ι g := by
  have he : ∀ i j : Fin d⊕Fin d,
      ι (pairEmbed ι g⁻¹ (pairSwap d j) (pairSwap d i))=pairEmbed ι g i j := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [pairEmbed,pairSwap,lower_entry,inv_inv] using hinv (g i j)
      | inr j => simp [pairEmbed,pairSwap]
    | inr i =>
      cases j with
      | inl j => simp [pairEmbed,pairSwap]
      | inr j => rfl
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  rw [steinberg_entry,← map_inv,← evenLabel_reflection,← evenLabel_reflection,
    actual_typeA_levi_entry,actual_typeA_levi_entry]
  exact he i j

private theorem label_inl_val (i : Fin d) : (evenLabel d (Sum.inl i)).val=i.val := rfl
private theorem label_inr_val (i : Fin d) :
    (evenLabel d (Sum.inr i)).val=d+(d-(i.val+1)) := rfl

/-- Actual positive type-A U maps into the positive UNITARY U.
Reversal of the second half is essential and is proved in the index law. -/
theorem actual_typeA_levi_upper (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin d) F) (hg : LayerDepth 1 (g.val-1)) :
    LayerDepth 1 ((embed ι g).val-1) ∧ steinberg ι (embed ι g)=embed ι g := by
  refine ⟨?_,actual_typeA_levi_unitary ι hinv g⟩
  have hgi := (unitLayer% inverse_unit_depth) g hg
  intro i j hij
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  simp only [Matrix.sub_apply,actual_typeA_levi_entry,Matrix.one_apply,(evenLabel d).injective.eq_iff]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := hg i j (by simpa only [label_inl_val] using hij)
      simpa only [fromBlocks_apply₁₁,Matrix.sub_apply,Matrix.one_apply,Sum.inl.injEq] using hh
    | inr j => simp
  | inr i =>
    cases j with
    | inl j => simp
    | inr j =>
      have hji : i.val<j.val+1 := by
        rw [label_inr_val,label_inr_val] at hij
        omega
      have hh := hgi j i hji
      simp only [fromBlocks_apply₂₂,lower_entry,Matrix.sub_apply,Matrix.one_apply,Sum.inr.injEq]
      have he : g⁻¹ j i=(1:Matrix (Fin d) (Fin d) F) j i := sub_eq_zero.mp hh
      rw [he]
      simp [Matrix.one_apply,eq_comm]

/-- Every finite-field automorphism restricts to the literal field action
on the type-A Levi, on ALL group elements. Commutation with the quadratic
involution is DERIVED from its actual Frobenius power, not assumed. -/
theorem actual_typeA_levi_field_action (ι phi : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (g : SpecialLinearGroup (Fin d) F) :
    fieldAut phi (embed ι g)=embed ι (fieldAut phi g) := by
  have hcomm : ∀ x : F, phi (ι x)=ι (phi x) := by
    intro x
    rw [involution_eq_pow ι hinv hne x,map_pow,involution_eq_pow ι hinv hne (phi x)]
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  change phi (embed ι g (evenLabel d i) (evenLabel d j))=_
  rw [actual_typeA_levi_entry,actual_typeA_levi_entry]
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => exact map_zero phi
  | inr i =>
    cases j with
    | inl j => exact map_zero phi
    | inr j =>
      simp only [fromBlocks_apply₂₂,lower_entry,← map_inv]
      exact hcomm (g⁻¹ j i)

private def pairedUnits (ι : RingAut F) (eta : Fin d → Fˣ) : Fin (2*d) → Fˣ :=
  fun i => Sum.elim eta (fun j => (involutionUnit ι (eta j))⁻¹) ((evenLabel d).symm i)

private theorem pairedUnits_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (eta : Fin d → Fˣ) (i : Fin (2*d)) :
    ι (pairedUnits ι eta i:F)*(pairedUnits ι eta i.rev:F)=1 := by
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  rw [← evenLabel_reflection]
  cases i with
  | inl i => simp [pairedUnits,pairSwap,involutionUnit_val,Units.val_inv_eq_inv_val]
  | inr i => simp [pairedUnits,pairSwap,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀,hinv (eta i:F)]

/-- A genuine diagonal action on the Levi, with the conjugate-inverse
second block DERIVED from the first; its actual matrix action is proved. -/
private theorem paired_diagonal_action (ι : RingAut F) (eta : Fin d → Fˣ)
    (g : SpecialLinearGroup (Fin d) F) :
    (unitOdd% diagonalAut) (pairedUnits ι eta) (embed ι g)=
      embed ι ((unitOdd% diagonalAut) eta g) := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (evenLabel d).surjective i
  obtain ⟨j,rfl⟩ := (evenLabel d).surjective j
  rw [(unitOdd% diagonal_entry),actual_typeA_levi_entry,actual_typeA_levi_entry]
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [pairedUnits,unitOdd% diagonal_entry]
    | inr j => simp
  | inr i =>
    cases j with
    | inl j => simp
    | inr j =>
      simp only [fromBlocks_apply₂₂,lower_entry,← map_inv]
      rw [unitOdd% diagonal_entry]
      simp only [pairedUnits,Equiv.symm_apply_apply,Sum.elim_inr,involutionUnit_val,
        inv_inv,Units.val_inv_eq_inv_val,map_mul,map_inv₀]
      ring

/-- The actual p255 ambient H induces ALL diagonal actions on the
type-A Levi inside central SU(2d). ONE genuine determinant-one ambient
unitary correction is constructed before ALL full Levi group targets. -/
theorem actual_typeA_levi_ambient_diagonal_inner (ι : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (eta : Fin d → Fˣ) :
    ∃ h : SpecialLinearGroup (Fin (2*d+2)) F,
      steinberg ι h=h ∧ ∀ g : SpecialLinearGroup (Fin d) F,
        (MulAut.conj h) (PartIICentralLevi.embed (embed ι g))=
          PartIICentralLevi.embed (embed ι ((unitOdd% diagonalAut) eta g)) := by
  obtain ⟨h,hh,hhu,hcover⟩ := PartIIUnitaryCentralInnerTorus.actual_unitary_central_diagonal_inner
    ι hinv hne (pairedUnits ι eta) 1 (pairedUnits_unitary ι hinv eta)
  refine ⟨h,hhu,?_⟩
  intro g
  rw [hcover,paired_diagonal_action]
end NikolovSegal.PartIIUnitaryTypeALevi
