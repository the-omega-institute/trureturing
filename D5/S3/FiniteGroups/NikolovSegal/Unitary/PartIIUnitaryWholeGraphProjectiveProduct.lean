/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryWholeGraphProjectiveProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryWholePrescribedProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryIntrinsicGraphProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryProjectivePrescribedProduct

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.PartIIUnitaryWholeGraphProjectiveProduct
open UnitarySylow UnitaryField PartIIUnitriangularLayers
open PartIIUnitaryIntrinsicPrescribedProduct PartIIUnitaryIntrinsicGraphProduct
open PartIIUnitaryProjectivePrescribedProduct PartIIUnitaryWholePrescribedProduct
universe u

/-- The actual raw graph is absorbed into the genuine field component.
No prescribed graph bit, divisor power, whole-SU target or global correction
is discarded; the same uniform constants work for all graph tuples. -/
theorem actual_uniform_intrinsic_whole_graph_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι)
      (hne : ι≠RingEquiv.refl F), ∀ n : ℕ, 6≤n →
      ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (eps : Fin N → Bool) (e : Fin N → ℕ),
      (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, ∃ x : Fin N → specialUnitary n ι,
          orderedProduct (fun j => (x j)⁻¹ *
            ((graphAction ι (phi j) hinv hne (a j) (c j) (ha j) (eps j) *
              MulAut.conj ((y j)⁻¹))^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_intrinsic_whole_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi eps e he
  exact hcover F hF ι hinv hne n hn a c ha
    (fun j => if eps j then ι.trans (phi j) else phi j) e he

/-- Every actual center-quotient target is covered. The quotient action is
constructed from the genuine SU action, and the quotient's surjectivity
is proved library mathematics, rather than a bare-automorphism lift premise. -/
theorem actual_uniform_projective_whole_graph_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι)
      (hne : ι≠RingEquiv.refl F), ∀ n : ℕ, 6≤n →
      ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (eps : Fin N → Bool) (e : Fin N → ℕ),
      (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → projectiveSpecialUnitary n ι,
        ∀ b : projectiveSpecialUnitary n ι,
          ∃ x : Fin N → projectiveSpecialUnitary n ι,
            orderedProduct (fun j => (x j)⁻¹ *
              ((projectiveAction ι (graphAction ι (phi j) hinv hne
                (a j) (c j) (ha j) (eps j)) *
                MulAut.conj ((y j)⁻¹))^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_intrinsic_whole_graph_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi eps e he
  obtain ⟨y,hy⟩ := hcover F hF ι hinv hne n hn a c ha phi eps e he
  refine ⟨fun j => pi ι (y j),?_⟩
  intro b
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (specialUnitary n ι)) b
  obtain ⟨x,hx⟩ := hy g
  refine ⟨fun j => pi ι (x j),?_⟩
  rw [ordered_corrected_values_pi]
  simpa only [map_inv] using congrArg (pi ι) hx

end NikolovSegal.PartIIUnitaryWholeGraphProjectiveProduct
