import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Words.AdmissibleWords.UncrossingFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Endpoint

open _root_.D5.S1.Words.AdmissibleWords.UncrossingFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Data coordinates from the scope of the selected final invariant. -/
abbrev Parameters := Sigma (fun n : Nat => Fin n)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Multiset (Fin p.1 → Bool)) (fun _ => Nat)

/-- The original occupancy, before Phi, of an actual native word multiset. -/
def actual : Realization signature :=
  realize.{0, 0, 0, 0, 0} signature
    (fun _ p X => occupancyCount X p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize.{0, 0, 0, 0, 0} signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Only the left occupancy in the final reachable-state invariant is replaced.
The outer quantifier still includes n=0, independently of Parameters. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Nat} {M N : Multiset (Fin n → Bool)}
    (_hM : NativeRows M) (_hN : NativeRows N) (_hc : M.card = N.card)
    (_hm : ∀ i, occupancyCount M i = occupancyCount N i),
    NativePath M N ∧ nativeCanonical M = nativeCanonical N ∧
      (∃ k, 2 * k + energy (phiRows M) ≤ M.card * n ^ 2 ∧ k ≤ M.card * n ^ 2 / 2 ∧
        ForwardRoute (phiRows M) (phiRows (nativeCanonical M)) k ∧
        NativePath M (nativeCanonical M)) ∧
      (∀ X, NativePath M X → NativeRows X ∧ X.card = M.card ∧
        ∀ i, R.readout () ⟨n, i⟩ X = occupancyCount M i)

/-- Both directions concern the complete original theorem type. -/
theorem statement_bridge :
    (type_of% (@adm_phi_fiber_common_endpoint)) ↔ arena.Law actual :=
  Iff.rfl

theorem actual_law : arena.Law actual :=
  statement_bridge.mp (@adm_phi_fiber_common_endpoint)

/-- The last invariant is a separate fourth conjunct. Its path premise is met
by reflexivity at the empty multiset; the bounded-route conjunct stays in Law. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h0 : NativeRows (0 : Multiset (Fin 1 → Bool)) := by
    intro w hw
    simp at hw
  have hfull := law (n := 1) (M := 0) (N := 0) h0 h0 rfl (fun _ => rfl)
  have hpath : NativePath (0 : Multiset (Fin 1 → Bool)) 0 := .refl
  have hbad := (hfull.2.2.2 (0 : Multiset (Fin 1 → Bool)) hpath).2.2 (0 : Fin 1)
  have h10 : (1 : Nat) = 0 := by
    simpa [rejected, realize, occupancyCount] using hbad
  cases h10

theorem actual_variation : Variation arena actual :=
  ⟨actual_law, rejected, rejected_law⟩

theorem actual_sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law

/-- Empty versus one true word at n=1, i=0 distinguishes actual outputs. -/
theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨⟨1, 0⟩, (0 : Multiset (Fin 1 → Bool)),
    ((fun _ : Fin 1 => true) ::ₘ 0), ?_⟩
  change occupancyCount (0 : Multiset (Fin 1 → Bool)) (0 : Fin 1) ≠
    occupancyCount ((fun _ : Fin 1 => true) ::ₘ 0) (0 : Fin 1)
  simp [occupancyCount]

/-- Inner typed obligations, authored against the pinned original statement. -/
def registration : Registration arena (type_of% (@adm_phi_fiber_common_endpoint)) where
  actual := actual
  bridge := statement_bridge
  variation := actual_variation
  sensitivity := actual_sensitivity
  dependence := actual_dependence

/-- Raw path and ordinals come from the preserved statement-v1 compiler material.
The exact X operand is abstracted because the coordinate i occurs after X. -/
def sourceSelection : Contract.SourceSelection where
  owner := `D5.S1.Words.AdmissibleWords.UncrossingFiber
  definition := none
  coordinates := #[0, 9]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "arg", "body", "body", "arg", "arg", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := some #["fn", "arg"]
    booleanPredicate := false }]

/-- Source-bound registration with the enrolled dependent-family template. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@adm_phi_fiber_common_endpoint)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ p X => occupancyCount X p.2) (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S1.Words.AdmissibleWords.UncrossingFiber.adm_phi_fiber_common_endpoint.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Endpoint.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p X => occupancyCount X p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some sourceSelection
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.AdmissibleWords.UncrossingFiber.Endpoint
