import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound copy-law audits retain the complete quantified statements. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.Support.NativeTimeProfile.LawEvidence
open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge TotalCopyNormalization NativeTimeProfile RegionFilterQExpressibility
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem region_univ (X : Bal) : regionReadout Set.univ X = q X.val := by
  simp [regionReadout, q, ComplementCharge.readout, charge]

private theorem input_word (X : Bal) : wordReadout [] X = q X.val := rfl

private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩
private def alternating : Region := {z | z.1 % 2 = 0}
private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

namespace PolynomialLaw
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Nat CopyTerm (fun _ => Int)

def actual : Realization signature := realize signature
  (fun _ _ N => q (zeroValue N).val) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ N => q (zeroValue N).val + 1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (r : Nat) (N : CopyTerm r), 0 < r → TemporalFree N →
    ∀ X : Bal, ∃ P : Polynomial Int,
      P.natDegree ≤ r ∧
      (∀ n : Nat, P.eval (n : Int) = q (value N (fun _ => copies n X)).val) ∧
      P.coeff 0 = F.readout () r N ∧
      P.coeff 1 = (∑ i : Fin r, q (value N (sliceAssignment i X)).val) -
        (r : Int) * q (zeroValue N).val
private theorem positive : arena.Law actual := copy_polynomial_law
private theorem negative : ¬ arena.Law bad := by
  intro h
  obtain ⟨P, _, he, hc, _⟩ := h 1 .input (by decide) trivial zero
  have h0 := he 0
  have heq : P.coeff 0 = q zero.val := by simpa [value, copies, eval, ← Polynomial.coeff_zero_eq_eval_zero] using h0
  change P.coeff 0 = q zero.val + 1 at hc
  omega

def evidence : Registration arena (type_of% (@copy_polynomial_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, bad, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad negative
  dependence := by
    intro i
    refine ⟨0, .param (ComplementFibers.balancedSection 3 0),
      .param (ComplementFibers.balancedSection 3 1), ?_⟩
    change q (ComplementFibers.balancedSection 3 0).val ≠
      q (ComplementFibers.balancedSection 3 1).val
    have h0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    omega

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_polynomial_law)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_polynomial_law
  realizationName := `Reg.Support.NativeTimeProfile.LawEvidence.PolynomialLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := some {
      owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
      name := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.CopyPolynomialLaw
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","arg","fn","arg","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end PolynomialLaw

namespace SaturationLaw
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    ((Fin 3 → Int) × Int × Int × Bal) (fun _ => Bal) (fun _ => Bool)

def actual : Realization signature := realize signature
  (fun _ p X => decide (SelectedVariant X p.2.2.2 p.1 p.2.1 p.2.2.1)) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {ι : Type} [Fintype ι] (w : ι → Word),
    (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) →
    ∃ c : Int, c ≤ 0 ∧ ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
      ∃ X Y : Bal, F.readout () ⟨p,t,t',Y⟩ X = true ∧
        ∀ i, wordReadout (w i) X = wordReadout (w i) Y
private theorem positive : arena.Law actual := by
  simpa only [actual, realize, decide_eq_true_eq] using @copy_saturation_law
private theorem negative : ¬ arena.Law bad := by
  intro h
  obtain ⟨c, _, hc⟩ := h (ι := Fin 0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨X,Y,hxy,_⟩ := hc (fun _ => 0) (c-1) (c-1) (by omega) (by omega)
  change false = true at hxy
  cases hxy

def evidence : Registration arena (type_of% (@copy_saturation_law)) where
  actual := actual
  bridge := by simp only [CopySaturationLaw, actual, realize, decide_eq_true_eq]
  variation := ⟨positive, bad, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad negative
  dependence := by
    intro i
    obtain ⟨c, _, hc⟩ := copy_saturation_law (ι := Fin 0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    obtain ⟨X,Y,hxy,_⟩ := hc (fun _ => 0) (c-1) (c-1) (by omega) (by omega)
    refine ⟨⟨(fun _ => 0),c-1,c-1,Y⟩, X, zero, ?_⟩
    have hn : ¬ SelectedVariant zero Y (fun _ => 0) (c-1) (c-1) := by
      rintro ⟨h, _⟩
      have he := h.exceptional.property
      exact Finset.notMem_empty h.exceptional.val
        (zero_empty.1 ▸ he : h.exceptional.val ∈ (∅ : Finset _))
    change decide (SelectedVariant X Y _ _ _) ≠ decide (SelectedVariant zero Y _ _ _)
    simp only [hxy, hn, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_saturation_law)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_saturation_law
  realizationName := `Reg.Support.NativeTimeProfile.LawEvidence.SaturationLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := some {
      owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
      name := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.CopySaturationLaw
      path := #[] }
    coordinates := #[5,6,7,11]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body","body","body","body","body","arg","body","arg","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","fn","fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end SaturationLaw

namespace SliceLaw
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ n : Nat, (Fin n → Word) × Fin n) (fun _ => Bal) (fun _ => Int)

def actual : Realization signature := realize signature
  (fun _ p X => wordReadout (p.2.1 p.2.2) X) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (R : Region) (n : Nat) (C : CopyTerm n), 0 < n →
    DiagonalTotal C →
    (∀ X : Bal, ∃ Y : Bal, evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X) →
    ∃ w : Fin n → Word,
      (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) ∧
      ∀ X : Bal, regionReadout R X = ∑ i, F.readout () ⟨n,w,i⟩ X
private theorem positive : arena.Law actual := copy_slice_readout_law
private theorem negative : ¬ arena.Law bad := by
  intro h
  obtain ⟨w, _, hw⟩ := h Set.univ 1 .input (by decide)
    (fun X => ⟨X,rfl⟩) (fun X => ⟨X,rfl,(region_univ X).symm⟩)
  have he := hw (ComplementFibers.balancedSection 3 1)
  simp only [bad, realize, Finset.sum_const_zero, region_univ,
    ] at he
  have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
    ComplementFibers.balancedSection_readout 3 1
  omega

def evidence : Registration arena (type_of% (@copy_slice_readout_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, bad, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad negative
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ => []), 0⟩, ComplementFibers.balancedSection 3 0,
      ComplementFibers.balancedSection 3 1, ?_⟩
    change wordReadout [] (ComplementFibers.balancedSection 3 0) ≠
      wordReadout [] (ComplementFibers.balancedSection 3 1)
    rw [input_word, input_word]
    have h0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    omega

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_slice_readout_law)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_slice_readout_law
  realizationName := `Reg.Support.NativeTimeProfile.LawEvidence.SliceLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := some {
      owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
      name := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.CopySliceReadoutLaw
      path := #[] }
    coordinates := #[1,6,8]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","body","arg","arg","body"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end SliceLaw

namespace SumLaw
@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Region) (fun _ => Bool)

def actual : Realization signature := realize signature
  (fun _ _ R => decide (Tail R)) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (R : Region) {ι : Type} [Fintype ι] (w : ι → Word),
    (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) →
    (∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X) →
    F.readout () () R = true
private theorem positive : arena.Law actual := by
  simpa only [actual, realize, decide_eq_true_eq] using @sum_word_readouts_implies_tail
private theorem negative : ¬ arena.Law bad := by
  intro h
  have he := h ∅ (ι := Fin 0) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun X => by simp [regionReadout])
  change false = true at he
  cases he

def evidence : Registration arena (type_of% (@sum_word_readouts_implies_tail)) where
  actual := actual
  bridge := by simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨positive, bad, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad negative
  dependence := by
    intro i
    refine ⟨(), ∅, alternating, ?_⟩
    change decide (Tail ∅) ≠ decide (Tail alternating)
    simp only [empty_tail, alternating_not_tail, decide_true, decide_false,
      ne_eq, Bool.true_eq_false, not_false_eq_true]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.sum_word_readouts_implies_tail)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.sum_word_readouts_implies_tail
  realizationName := `Reg.Support.NativeTimeProfile.LawEvidence.SumLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end SumLaw

end
end Reg.Support.NativeTimeProfile.LawEvidence
