/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryProjectivePrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryProjectivePrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryIntrinsicPrescribedProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Actual center quotient of SU and transport of prescribed U/L products.
No arbitrary projective automorphism is lifted or classified here. -/
namespace NikolovSegal.PartIIUnitaryProjectivePrescribedProduct
open Matrix PartIIUnitriangularLayers UnitaryField UnitarySylow
open PartIIUnitaryIntrinsicPrescribedProduct
universe u
variable {F : Type u} [Field F] {n : ℕ}

abbrev projectiveSpecialUnitary (n : ℕ) (ι : RingAut F) :=
  (specialUnitary n ι) ⧸ Subgroup.center (specialUnitary n ι)

abbrev pi (ι : RingAut F) : specialUnitary n ι →* projectiveSpecialUnitary n ι :=
  QuotientGroup.mk' (Subgroup.center (specialUnitary n ι))

def projectiveAction (ι : RingAut F) (beta : MulAut (specialUnitary n ι)) :
    MulAut (projectiveSpecialUnitary n ι) :=
  QuotientGroup.congr _ _ beta (Subgroup.characteristic_iff_map_eq.mp inferInstance beta)

theorem action_pi (ι : RingAut F) (beta : MulAut (specialUnitary n ι))
    (g : specialUnitary n ι) : projectiveAction ι beta (pi ι g)=pi ι (beta g) := rfl

private theorem corrected_pi (ι : RingAut F) (beta : MulAut (specialUnitary n ι))
    (y g : specialUnitary n ι) :
    (projectiveAction ι beta*MulAut.conj ((pi ι y)⁻¹)) (pi ι g)=
      pi ι ((beta*MulAut.conj (y⁻¹)) g) := by
  simp only [MulAut.mul_apply,MulAut.conj_apply,← map_mul,← map_inv,action_pi]

theorem corrected_power_pi (ι : RingAut F) (beta : MulAut (specialUnitary n ι))
    (y : specialUnitary n ι) (d : ℕ) (g : specialUnitary n ι) :
    ((projectiveAction ι beta*MulAut.conj ((pi ι y)⁻¹))^d) (pi ι g)=
      pi ι (((beta*MulAut.conj (y⁻¹))^d) g) := by
  induction d generalizing g with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,ih,corrected_pi,pow_succ',MulAut.mul_apply]
    rfl

theorem ordered_corrected_values_pi (ι : RingAut F) {N : ℕ}
    (beta : Fin N → MulAut (specialUnitary n ι))
    (y x : Fin N → specialUnitary n ι) (d : Fin N → ℕ) :
    orderedProduct (fun j => (pi ι (x j))⁻¹ *
      ((projectiveAction ι (beta j)*MulAut.conj ((pi ι (y j))⁻¹))^(d j)) (pi ι (x j))) =
    pi ι (orderedProduct (fun j => (x j)⁻¹*((beta j*MulAut.conj (y j)⁻¹)^(d j)) (x j))) := by
  simp only [orderedProduct]
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [corrected_power_pi]
  simp only [Function.comp_def,map_mul,map_inv]

theorem actual_uniform_projective_positive_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → projectiveSpecialUnitary n ι,
        ∀ b : specialUnitary n ι, LayerDepth 1 (b.val.val-1) →
          ∃ x : Fin N → projectiveSpecialUnitary n ι,
            orderedProduct (fun j => (x j)⁻¹*
              ((projectiveAction ι (action ι (phi j) hinv hne (a j) (c j) (ha j))*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=pi ι b := by
  obtain ⟨N,C,hN,hSU⟩ := actual_uniform_intrinsic_positive_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  obtain ⟨y,hy⟩ := hSU F hF ι hinv hne n hn a c ha phi e he
  refine ⟨fun j => pi ι (y j),?_⟩
  intro b hb
  obtain ⟨x,hx,hprod⟩ := hy b hb
  refine ⟨fun j => pi ι (x j),?_⟩
  rw [ordered_corrected_values_pi]
  exact congrArg (pi ι) hprod

theorem actual_uniform_projective_negative_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → projectiveSpecialUnitary n ι,
        ∀ b : specialUnitary n ι, SLnUnipotentWidth.Lower b.val →
          ∃ x : Fin N → projectiveSpecialUnitary n ι,
            orderedProduct (fun j => (x j)⁻¹*
              ((projectiveAction ι (action ι (phi j) hinv hne (a j) (c j) (ha j))*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=pi ι b := by
  obtain ⟨N,C,hN,hSU⟩ := actual_uniform_intrinsic_negative_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  obtain ⟨y,hy⟩ := hSU F hF ι hinv hne n hn a c ha phi e he
  refine ⟨fun j => pi ι (y j),?_⟩
  intro b hb
  obtain ⟨x,hx,hprod⟩ := hy b hb
  refine ⟨fun j => pi ι (x j),?_⟩
  rw [ordered_corrected_values_pi]
  exact congrArg (pi ι) hprod

end NikolovSegal.PartIIUnitaryProjectivePrescribedProduct
