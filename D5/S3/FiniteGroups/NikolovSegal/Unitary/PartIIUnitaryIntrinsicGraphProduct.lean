/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicGraphProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicGraphProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryIntrinsicPrescribedProduct
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! The actual anti-diagonal graph on SU is the supplied field involution.
Thus every prescribed raw graph/field tuple is a genuine D/Phi tuple.
This proves the action law; bare automorphism recognition remains separate. -/
namespace NikolovSegal.PartIIUnitaryIntrinsicGraphProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitaryUpperTorus
open UnitaryField UnitarySylow PartIIUnitaryIntrinsicPrescribedProduct
universe u
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

theorem finite_field_automorphism_commutes (ι phi : RingAut F)
    (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F) (x : F) :
    ι (phi x)=phi (ι x) := by
  rw [involution_eq_pow ι hinv hne,involution_eq_pow ι hinv hne,map_pow]

theorem actual_raw_graph_is_field (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : specialUnitary n ι) : (unitAction% rawGraph) g.val=fieldAut ι g.val := by
  apply SpecialLinearGroup.ext
  intro i j
  have hs : steinberg ι g.val=g.val := g.prop
  have h := congrArg (fun z : SpecialLinearGroup (Fin n) F => z i j) hs
  change ι (g.val⁻¹ j.rev i.rev)=g.val i j at h
  have he := congrArg ι h
  change g.val⁻¹ j.rev i.rev=ι (g.val i j)
  exact (hinv (g.val⁻¹ j.rev i.rev)).symm.trans he

def graphAction (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F))
    (eps : Bool) : MulAut (specialUnitary n ι) :=
  action ι (if eps then ι.trans phi else phi) hinv hne a c ha

theorem actual_graph_action (ι phi : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (a : Fin n → Fˣ) (c : (fixedField ι)ˣ)
    (ha : ∀ i, ι (a i:F)*(a i.rev:F)=((c:fixedField ι):F))
    (eps : Bool) (g : specialUnitary n ι) :
    (graphAction ι phi hinv hne a c ha eps g).val =
      (((unitOdd% diagonalAut) a*fieldAut (n:=n) phi*
        (if eps then (unitAction% rawGraph) else 1) :
        MulAut (SpecialLinearGroup (Fin n) F))) g.val := by
  cases eps with
  | false => rfl
  | true =>
    simp only [Bool.true_eq,if_true,MulAut.mul_apply,actual_raw_graph_is_field ι hinv]
    apply SpecialLinearGroup.ext
    intro i j
    rw [unitOdd% diagonal_entry]
    exact actual_action_entry ι (ι.trans phi) hinv hne a c ha g i j

theorem actual_uniform_intrinsic_graph_positive_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (eps : Fin N → Bool) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, LayerDepth 1 (b.val.val-1) →
          ∃ x : Fin N → specialUnitary n ι,
            (∀ j, LayerDepth 1 ((x j).val.val-1)) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((graphAction ι (phi j) hinv hne (a j) (c j) (ha j) (eps j)*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_intrinsic_positive_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi eps e he
  exact hcover F hF ι hinv hne n hn a c ha
    (fun j => if eps j then ι.trans (phi j) else phi j) e he

theorem actual_uniform_intrinsic_graph_negative_q_over_e_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F),
      ∀ n : ℕ, 6≤n → ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (eps : Fin N → Bool) (e : Fin N → ℕ), (∀ j, 0<e j ∧ e j∣q) →
      ∃ y : Fin N → specialUnitary n ι,
        ∀ b : specialUnitary n ι, SLnUnipotentWidth.Lower b.val →
          ∃ x : Fin N → specialUnitary n ι,
            (∀ j, SLnUnipotentWidth.Lower (x j).val) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((graphAction ι (phi j) hinv hne (a j) (c j) (ha j) (eps j)*MulAut.conj (y j)⁻¹)^(q/e j)) (x j))=b := by
  obtain ⟨N,C,hN,hcover⟩ := actual_uniform_intrinsic_negative_q_over_e_product q hq
  refine ⟨N,C,hN,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi eps e he
  exact hcover F hF ι hinv hne n hn a c ha
    (fun j => if eps j then ι.trans (phi j) else phi j) e he

end NikolovSegal.PartIIUnitaryIntrinsicGraphProduct
