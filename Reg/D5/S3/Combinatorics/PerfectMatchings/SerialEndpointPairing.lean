import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete original-carrier serial criterion. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
open _root_.D5.S3.Combinatorics.PerfectMatchings
open SerialEndpointPairing SerialEndpointPairing.CutModule
open FiniteEndpointPairing FiniteBandSwitch.FourEndpoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv LeanInformationAudit
noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n → Perm (Fin 2)
  State p := Fin (p.1 + 1) → CutModule.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Perm (Fin 4)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => (serialOn p.1 M p.2).pairing) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => thirdPairing) (fun e => nomatch e)

/-- The entire original telescope and all action laws are retained. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (n : ℕ) (M : Fin (n + 1) → CutModule.{u}) (c : Fin n → Perm (Fin 2)),
    (∀ i x, (serialOn n M c).corner ⟨i, x⟩ = ⟨i, (M i).corner x⟩) ∧
    (∀ i x, (M i).band x ≠ x → (serialOn n M c).band ⟨i, x⟩ = ⟨i, (M i).band x⟩) ∧
    (∀ (i : Fin n) (a : Fin 2),
      (serialOn n M c).band ⟨i.castSucc, ((M i.castSucc).ports (a.natAdd 2) : _)⟩ =
        ⟨i.succ, ((M i.succ).ports ((c i a).castAdd 2) : _)⟩) ∧
    (∀ a : Fin 2, ((serialOn n M c).ports (a.castAdd 2) : (serialOn n M c).Carrier) =
      ⟨0, ((M 0).ports (a.castAdd 2) : _)⟩) ∧
    (∀ a : Fin 2, ((serialOn n M c).ports (a.natAdd 2) : (serialOn n M c).Carrier) =
      ⟨Fin.last n, ((M (Fin.last n)).ports (a.natAdd 2) : _)⟩) ∧
    (R.readout () ⟨n, c⟩ M ≠ thirdPairing ↔ ∀ i, (M i).pairing ≠ thirdPairing)

private def toy (P : Perm (Fin 4)) (hP : Function.Involutive P)
    (hf : ∀ i, P i ≠ i) : CutModule.{u} where
  Carrier := ULift.{u} (Fin 4)
  finite := inferInstance
  corner := Equiv.ulift.symm.permCongr P
  band := 1
  corner_involutive := by intro x; apply ULift.ext; exact hP x.down
  band_involutive := fun _ => rfl
  corner_free := by
    intro x h
    exact hf x.down (congrArg ULift.down h)
  ports := {
    toFun := fun i => ⟨⟨i⟩, rfl⟩
    invFun := fun x => x.val.down
    left_inv := fun _ => rfl
    right_inv := by intro x; apply Subtype.ext; rfl }

private theorem toy_pairing (P : Perm (Fin 4)) (hP : Function.Involutive P)
    (hf : ∀ i, P i ≠ i) : (toy.{u} P hP hf).pairing = P := by
  let T := toy.{u} P hP hf
  apply Equiv.ext
  intro i
  apply T.ports.injective
  change endpointPairing T.corner T.band T.corner_involutive T.band_involutive
      (T.ports i) = T.ports (P i)
  apply Subtype.ext
  have hn : FirstVisit (T.corner * T.band) {x | T.band x = x} (T.ports i) 1 := by
    refine ⟨by omega, rfl, ?_⟩
    intro k hk hkn
    omega
  change (nextVisit (T.corner * T.band) {x | T.band x = x} (T.ports i) : T.Carrier) = _
  exact (next_visit_eq_of_first_visit (T.ports i) hn).trans (by rfl)

private def dead : CutModule.{u} := toy thirdPairing
  (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> decide)

private def through : CutModule.{u} := toy J0
  (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> decide)

private theorem dead_pairing : dead.{u}.pairing = thirdPairing := toy_pairing _ _ _
private theorem through_pairing : through.{u}.pairing ≠ thirdPairing := by
  rw [through, toy_pairing]
  decide

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hc := (h 0 (fun _ => through.{u}) (fun i => Fin.elim0 i)).2.2.2.2.2
  exact (hc.mpr (fun _ => through_pairing)) rfl

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let c : Fin 0 → Perm (Fin 2) := fun i => Fin.elim0 i
  let md : Fin 1 → CutModule.{u} := fun _ => dead
  let mt : Fin 1 → CutModule.{u} := fun _ => through
  refine ⟨⟨0, c⟩, md, mt, ?_⟩
  have hd : (serialOn 0 md c).pairing = thirdPairing := by
    by_contra hn
    have h := (serial_endpoint_pairing 0 md c).2.2.2.2.2.mp hn 0
    exact h dead_pairing
  have ht : (serialOn 0 mt c).pairing ≠ thirdPairing :=
    (serial_endpoint_pairing 0 mt c).2.2.2.2.2.mpr (fun _ => through_pairing)
  intro h
  exact ht (h.symm.trans hd)

def source_registration : Registration arena.{u} (type_of% @serial_endpoint_pairing.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨serial_endpoint_pairing, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@serial_endpoint_pairing.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
