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

end NikolovSegal.PartIIUnitaryIntrinsicGraphProduct
