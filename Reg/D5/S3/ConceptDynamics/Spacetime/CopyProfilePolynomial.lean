import D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge TotalCopyNormalization NativeTimeProfile CopyProfilePolynomial
open scoped BigOperators
noncomputable section
open Classical

@[reducible] def signature : Signature where
  Params := Σ r : Nat, CopyTerm r × B
  State p := Fin p.1 → Nat
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Profile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p v => if i = 0 then gamma (value p.2.1 (fun j => copies (v j) p.2.2)).val
    else ∑ J : Finset (Fin p.1),
      (∏ j ∈ J, (v j : Int)) • profileCoefficients p.2.1 p.2.2 J)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (r : Nat) (N : CopyTerm r), TemporalFree N → ∀ (X : B) (v : Fin r → Nat),
    F.readout 0 ⟨r,N,X⟩ v = F.readout 1 ⟨r,N,X⟩ v
private theorem positive : arena.Law actual :=
  fun _ N h X v => profile_multiaffine N h X v

private def delta : Profile := gamma (ComplementFibers.balancedSection 3 1).val
private theorem readout_delta : NativeTimeProfile.readout delta = 1 := by
  rw [delta, readout_gamma]
  exact ComplementFibers.balancedSection_readout 3 1

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p v => if j = i then actual.readout j p v + delta else actual.readout j p v)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let X := ComplementFibers.balancedSection 3 1
  have h := congrArg NativeTimeProfile.readout (law 1 .input trivial X (fun _ => 0))
  have hp := congrArg NativeTimeProfile.readout (positive 1 .input trivial X (fun _ => 0))
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp only [changed, realize, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, map_add, readout_delta] at h <;> omega

private theorem input_readout (X : B) (n : Nat) :
    NativeTimeProfile.readout (actual.readout 0 ⟨1,.input,X⟩ (fun _ => n)) =
      (n : Int) * q X.val := by
  change NativeTimeProfile.readout (gamma (copies n X).val) = _
  induction n with
  | zero =>
    rw [copies, readout_gamma]
    simpa [zero] using (show q (ComplementFibers.balancedSection 3 0).val = 0 from
      ComplementFibers.balancedSection_readout 3 0)
  | succ n ih =>
    rw [copies, gamma_parallel, map_add, ih, readout_gamma]
    push_cast
    ring

def evidence : Registration arena (type_of% (@profile_multiaffine)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p v
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    let X := ComplementFibers.balancedSection 3 1
    refine ⟨⟨1,.input,X⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have h0 := positive 1 .input trivial X (fun _ => 0)
    have h1 := positive 1 .input trivial X (fun _ => 1)
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 ⟨1,.input,X⟩ (fun _ => 0) =
        actual.readout 0 ⟨1,.input,X⟩ (fun _ => 1) := by
      rcases hi with rfl | rfl
      · exact h
      · exact h0.trans (h.trans h1.symm)
    have hh' := congrArg NativeTimeProfile.readout hh
    rw [input_readout, input_readout] at hh'
    have hX : q X.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [hX] at hh'
    norm_num at hh'

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial.profile_multiaffine)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial.profile_multiaffine
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial.evidence
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
    owner := `D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
