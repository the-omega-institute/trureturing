/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicPrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryPrescribedLowerProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Actual subgroup automorphisms and the original right-inner q/e VALUE
interface. The accepted literal specialUnitary carrier is reused; the
prescribed D/Phi action is constructed from the genuine component law,
not assumed as an automorphism or a whole-group coverage premise. -/
namespace NikolovSegal.PartIIUnitaryIntrinsicPrescribedProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open UnitaryField UnitarySylow
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}
private theorem diagonal_steinberg (ι : RingAut F) (a : Fin n → Fˣ)
    (c : (fixedField ι)ˣ) (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F))
    (g : SpecialLinearGroup (Fin n) F) :
    steinberg ι ((unitOdd% diagonalAut) a g)=(unitOdd% diagonalAut) a (steinberg ι g) := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv,unitOdd% diagonal_entry,unitOdd% diagonal_entry,steinberg_entry]
  have hi : ι (a i.rev:F)=((c:fixedField ι):F)/(a i:F) := by
    apply (eq_div_iff (a i).ne_zero).mpr
    simpa only [Fin.rev_rev] using ha i.rev
  have hj : ι (a j.rev:F)=((c:fixedField ι):F)/(a j:F) := by
    apply (eq_div_iff (a j).ne_zero).mpr
    simpa only [Fin.rev_rev] using ha j.rev
  have hc : ((c:fixedField ι):F)≠0 := by
    intro he; apply c.ne_zero; exact Subtype.ext he
  simp only [Units.val_inv_eq_inv_val,map_mul,map_inv₀,hi,hj]
  field_simp [(a i).ne_zero,(a j).ne_zero,hc]
private theorem field_steinberg (ι phi : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (g : SpecialLinearGroup (Fin n) F) :
    steinberg ι (fieldAut phi g)=fieldAut phi (steinberg ι g) := by
  apply SpecialLinearGroup.ext
  intro i j
  rw [steinberg_entry,← map_inv]
  change ι (phi (g⁻¹ j.rev i.rev))=phi (steinberg ι g i j)
  rw [steinberg_entry,involution_eq_pow ι hinv hne,involution_eq_pow ι hinv hne,map_pow]
private theorem gamma_steinberg (ι phi : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F))
    (g : SpecialLinearGroup (Fin n) F) :
    steinberg ι (PartIIProposition6_5.diagonalFieldGraph a phi false g)=
      PartIIProposition6_5.diagonalFieldGraph a phi false (steinberg ι g) := by
  change steinberg ι ((unitOdd% diagonalAut) a (fieldAut phi g))=_
  rw [diagonal_steinberg ι a c ha,field_steinberg ι phi hinv hne]
  rfl

/-- Actual prescribed D/Phi automorphism of the LITERAL SU carrier.
Its inverse closure is derived from the actual Steinberg commutation. -/
def action (ι phi : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (a : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F)) : MulAut (specialUnitary n ι) where
  toFun g := ⟨PartIIProposition6_5.diagonalFieldGraph a phi false g.val,by
    change steinberg ι (PartIIProposition6_5.diagonalFieldGraph a phi false g.val) = _
    rw [gamma_steinberg ι phi hinv hne a c ha]
    exact congrArg _ g.prop⟩
  invFun g := ⟨(PartIIProposition6_5.diagonalFieldGraph a phi false).symm g.val,by
    change steinberg ι ((PartIIProposition6_5.diagonalFieldGraph a phi false).symm g.val) = _
    apply (PartIIProposition6_5.diagonalFieldGraph a phi false).injective
    rw [← gamma_steinberg ι phi hinv hne a c ha,MulEquiv.apply_symm_apply]
    exact g.prop⟩
  left_inv g := Subtype.ext ((PartIIProposition6_5.diagonalFieldGraph a phi false).left_inv g.val)
  right_inv g := Subtype.ext ((PartIIProposition6_5.diagonalFieldGraph a phi false).right_inv g.val)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem actual_action_entry (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F))
    (g : specialUnitary n ι) (i j : Fin n) :
    (action ι phi hinv hne a c ha g).val i j=(a i:F)*phi (g.val i j)*(((a j)⁻¹:Fˣ):F) := by
  change ((unitOdd% diagonalAut) a (fieldAut phi g.val)) i j=_
  rw [unitOdd% diagonal_entry]
  rfl

/-- Original scalar supplier correction convention, intrinsically on SU,
for ALL positive-U targets. N,C precede all fields/ranks/tuples; ONE y
precedes ALL targets. This is honest U coverage, not full scalar coverage. -/
theorem actual_uniform_intrinsic_positive_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, LayerDepth 1 (b.val.val-1) →
          ∃ x : Fin N → specialUnitary n ι,
            (∀ j, LayerDepth 1 ((x j).val.val-1)) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((action ι (phi j) hinv hne (a j) (c j) (ha j)*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hU⟩ := PartIIUnitaryPrescribedUProduct.actual_uniform_all_rank_unitary_U_prescribed_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  have hs : ∀ j, 0<q/e j ∧ q/e j∣q := fun j =>
    ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,Nat.div_dvd_of_dvd (he j).2⟩
  obtain ⟨h,hh,hcover⟩ := hU F hF ι hinv hne n hn a c ha phi (fun j => q/e j) hs
  let beta := fun j => action ι (phi j) hinv hne (a j) (c j) (ha j)
  let H : Fin N → specialUnitary n ι := fun j => ⟨h j,hh j⟩
  let y := fun j => ((beta j).symm (H j))⁻¹
  have step : ∀ j g, ((beta j*MulAut.conj (y j)⁻¹) g).val=
      (MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false) g.val := by
    intro j g
    simp only [beta,y,MulAut.mul_apply,MulAut.conj_apply,inv_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
    rfl
  have power : ∀ (j : Fin N) (t : ℕ) (g : specialUnitary n ι),
      (((beta j*MulAut.conj (y j)⁻¹)^t) g).val=
      ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^t) g.val := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih => intro g; rw [pow_succ',MulAut.mul_apply,step,ih,pow_succ',MulAut.mul_apply]; rfl
  refine ⟨y,?_⟩
  intro b hb
  obtain ⟨z,hz,heq⟩ := hcover b.val hb b.prop
  let x : Fin N → specialUnitary n ι := fun j => ⟨z j,(hz j).2⟩
  refine ⟨x,fun j => (hz j).1,?_⟩
  apply Subtype.ext
  have hp : (orderedProduct (fun j => (x j)⁻¹*((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))).val=
      orderedProduct (fun j => (z j)⁻¹*
        ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(q/e j)) (z j)) := by
    change (specialUnitary n ι).subtype ((List.ofFn (fun j => (x j)⁻¹*((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))).prod)=_
    rw [map_list_prod,List.map_ofFn]
    change (List.ofFn (fun j => (x j).val⁻¹ *
      (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j)).val)).prod = _
    simp only [power,x]
    rfl
  exact hp.trans heq
/-- Original scalar supplier correction convention, intrinsically on SU,
for ALL negative-U targets. N,C precede all fields/ranks/tuples; ONE y
precedes ALL targets. This is honest lower-U coverage, not full scalar coverage. -/
theorem actual_uniform_intrinsic_negative_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, SLnUnipotentWidth.Lower b.val →
          ∃ x : Fin N → specialUnitary n ι,
            (∀ j, SLnUnipotentWidth.Lower (x j).val) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((action ι (phi j) hinv hne (a j) (c j) (ha j)*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hU⟩ := PartIIUnitaryPrescribedLowerProduct.actual_uniform_all_rank_unitary_lower_prescribed_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  have hs : ∀ j, 0<q/e j ∧ q/e j∣q := fun j =>
    ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,Nat.div_dvd_of_dvd (he j).2⟩
  obtain ⟨h,hh,hcover⟩ := hU F hF ι hinv hne n hn a c ha phi (fun j => q/e j) hs
  let beta := fun j => action ι (phi j) hinv hne (a j) (c j) (ha j)
  let H : Fin N → specialUnitary n ι := fun j => ⟨h j,hh j⟩
  let y := fun j => ((beta j).symm (H j))⁻¹
  have step : ∀ j g, ((beta j*MulAut.conj (y j)⁻¹) g).val=
      (MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false) g.val := by
    intro j g
    simp only [beta,y,MulAut.mul_apply,MulAut.conj_apply,inv_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
    rfl
  have power : ∀ (j : Fin N) (t : ℕ) (g : specialUnitary n ι),
      (((beta j*MulAut.conj (y j)⁻¹)^t) g).val=
      ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^t) g.val := by
    intro j t
    induction t with
    | zero => intro g; rfl
    | succ t ih => intro g; rw [pow_succ',MulAut.mul_apply,step,ih,pow_succ',MulAut.mul_apply]; rfl
  refine ⟨y,?_⟩
  intro b hb
  obtain ⟨z,hz,heq⟩ := hcover b.val hb b.prop
  let x : Fin N → specialUnitary n ι := fun j => ⟨z j,(hz j).2⟩
  refine ⟨x,fun j => (hz j).1,?_⟩
  apply Subtype.ext
  have hp : (orderedProduct (fun j => (x j)⁻¹*((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))).val=
      orderedProduct (fun j => (z j)⁻¹*
        ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(q/e j)) (z j)) := by
    change (specialUnitary n ι).subtype ((List.ofFn (fun j => (x j)⁻¹*((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))).prod)=_
    rw [map_list_prod,List.map_ofFn]
    change (List.ofFn (fun j => (x j).val⁻¹ *
      (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (x j)).val)).prod = _
    simp only [power,x]
    rfl
  exact hp.trans heq
end NikolovSegal.PartIIUnitaryIntrinsicPrescribedProduct
