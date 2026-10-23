/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholePrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholePrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryIntrinsicBlockProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWholeGroupAbsoluteWidth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.PartIIUnitaryWholePrescribedProduct
open Matrix PartIIUnitriangularLayers UnitarySylow UnitaryField
open PartIIUnitaryIntrinsicPrescribedProduct PartIIUnitaryIntrinsicBlockProduct
open PrescribedProductComposition
open scoped Pointwise
universe u
variable {F : Type u} [Field F] {n : ℕ}

private theorem negative_width_is_lower (ι : RingAut F) (g : specialUnitary n ι)
    (h : UnitaryWholeGroupWidth.Negative g) : SLnUnipotentWidth.Lower g.val := by
  constructor
  · intro i j hij
    have he : i≠j := fun e => by subst j; omega
    have hh := h i j (by omega)
    simpa only [Matrix.sub_apply,Matrix.one_apply,he,ite_false,sub_zero] using hh
  · intro i
    have hh := h i i (by omega)
    exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply,Matrix.one_apply,ite_true] using hh)

/-- The separately proved absolute whole-SU width is genuinely consumed.
There is no factorization, scalar-coverage or action-existence premise.
This endpoint covers prescribed genuine D/Phi actions; recognition of
arbitrary bare SU automorphisms remains a separate mathematical leaf. -/
theorem actual_uniform_intrinsic_whole_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι)
      (hne : ι≠RingEquiv.refl F), ∀ n : ℕ, 6≤n →
      ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ),
      (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, ∃ x : Fin N → specialUnitary n ι,
          orderedProduct (fun j => (x j)⁻¹ *
            ((action ι (phi j) hinv hne (a j) (c j) (ha j) *
              MulAut.conj ((y j)⁻¹))^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_intrinsic_five_block_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  obtain ⟨y,hy⟩ := hcover F hF ι hinv hne n hn a c ha phi e he
  refine ⟨y,?_⟩
  intro b
  obtain ⟨u0,l0,u1,l1,u2,h0,h1,h2,h3,h4,hprod⟩ :=
    UnitaryWholeGroupWidth.five_factor hinv hne n b
  apply hy b
  refine ⟨u0,h0,l0*(u1*(l1*u2)),?_,?_⟩
  · refine ⟨l0,negative_width_is_lower ι l0 h1,u1*(l1*u2),?_,rfl⟩
    refine ⟨u1,h2,l1*u2,?_,rfl⟩
    exact ⟨l1,negative_width_is_lower ι l1 h3,u2,h4,rfl⟩
  · simpa only [mul_assoc] using hprod

end NikolovSegal.PartIIUnitaryWholePrescribedProduct
