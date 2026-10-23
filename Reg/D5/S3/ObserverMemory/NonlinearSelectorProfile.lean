import D5.S3.ObserverMemory.NonlinearSelectorProfile
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.ObserverMemory.NonlinearSelectorProfile
open _root_.D5.S3.ObserverMemory.NonlinearSelectorProfile
open _root_.D5.S3.ObserverMemory.StrictAnchoredBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (Set (List Bool))
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : Realization signature := realize signature
  (fun _ m k => residualSet (selectorRelation m) k) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Nat) (hm : 1 ≤ m),
    (∀ w ∈ selectorRelation m, w.length = 3*m+1) ∧
    (selectorRelation m).Nonempty ∧ (selectorRelation m).Finite ∧
    (∀ k, k ≤ 2*m →
      ((R.readout () m) k).Finite ∧
      Nat.card ((R.readout () m) k) = 2^k) ∧
    (∀ ell, ell ≤ m →
      (R.readout () m) (2*m+1+ell) =
        Set.range (fun r : List.Vector Bool (m-ell) => ({r.val} : Set (List Bool))) ∧
      ((R.readout () m) (2*m+1+ell)).Finite ∧
      Nat.card ((R.readout () m) (2*m+1+ell)) = 2^(m-ell)) ∧
    (∀ k, 1 ≤ k → k ≤ 2*m →
      (image (selectorRelation m) (k,1)).Finite ∧
      Nat.card (image (selectorRelation m) (k,1)) = 2^k) ∧
    (image (selectorRelation m) (2*m+1,1) =
      Set.range (fun p : (List.Vector Bool m × List.Vector Bool m) × Bool =>
        (({false :: p.1.1.val,true :: p.1.2.val} : Set (List Bool)),[p.2]))) ∧
    (image (selectorRelation m) (2*m+1,1)).Finite ∧
    Nat.card (image (selectorRelation m) (2*m+1,1)) = 2*(2^m)^2 ∧
    (∀ ell, 1 ≤ ell → ell ≤ m →
      image (selectorRelation m) (2*m+1+ell,1) =
        Set.range (fun ar : Bool × List.Vector Bool (m-ell) =>
          (({ar.1 :: ar.2.val} : Set (List Bool)),[ar.1])) ∧
      (image (selectorRelation m) (2*m+1+ell,1)).Finite ∧
      Nat.card (image (selectorRelation m) (2*m+1+ell,1)) = 2^(m-ell+1)) ∧
    (∀ k, k ≤ 3*m+1 →
      (image (selectorRelation m) (k,0)).Finite ∧
      Nat.card (image (selectorRelation m) (k,0)) =
        Nat.card ((R.readout () m) k)) ∧
    forwardPeak m = (2^m)^2 ∧ oneCreditPeak m = 2*(2^m)^2 ∧
    Nat.clog 2 (forwardPeak m) = 2*m ∧
    Nat.clog 2 (oneCreditPeak m) = 2*m+1 ∧
    Nat.clog 2 (oneCreditPeak m) - Nat.clog 2 (forwardPeak m) = 1 ∧
    Nat.clog 2 (Nat.card ((R.readout () m) (2*m+1))) = m ∧
    Nat.clog 2 (Nat.card (image (selectorRelation m) (2*m+1,1))) = 2*m+1 ∧
    Nat.clog 2 (Nat.card (image (selectorRelation m) (2*m+1,1))) -
      Nat.clog 2 (Nat.card ((R.readout () m) (2*m+1))) = m+1

def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 le_rfl).2.2.2.1 0 (by omega)
  have hc := bad.2
  change Nat.card (∅ : Set (Set (List Bool))) = 2^0 at hc
  simp at hc

def sourceRegistration : Registration arena (arena.Law actualReadout) where
  actual := actualReadout
  bridge := Iff.rfl
  variation := ⟨exact_selector_family_profile,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1,0,1,?_⟩
    intro he
    have hc := congrArg (fun S : Set (Set (List Bool)) => Nat.card S) he
    change Nat.card (residualSet (selectorRelation 1) 0) =
      Nat.card (residualSet (selectorRelation 1) 1) at hc
    have hp := (exact_selector_family_profile 1 le_rfl).2.2.2.1
    rw [(hp 0 (by omega)).2,(hp 1 (by omega)).2] at hc
    norm_num at hc

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ObserverMemory.NonlinearSelectorProfile.exact_selector_family_profile)
    (type_of% (realize signature
      (fun _ m k => residualSet (selectorRelation m) k) (fun e => nomatch e)))
    (Type) Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.NonlinearSelectorProfile.exact_selector_family_profile.__information_unit,
  realizationName := `Reg.D5.S3.ObserverMemory.NonlinearSelectorProfile.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := {stage := .evidence, objectStage := .evidence},
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ m k => residualSet (selectorRelation m) k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sourceRegistration
end
end Reg.D5.S3.ObserverMemory.NonlinearSelectorProfile
