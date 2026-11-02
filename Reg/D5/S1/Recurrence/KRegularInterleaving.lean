import D5.S1.Recurrence.KRegularInterleaving
import Reg.D5.S1.Recurrence.KRegularAffineSubsequence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-!
# Source-family audit for finite interleaving

The observation is the integer value s(n), with the original sequence retained
as a parameter and n as state. The law retains every base, width and residue
stream hypothesis of interleaving closure. An existing affine-closure
variation supplies a nonregular integer sequence for the rejected family.
-/

noncomputable section

namespace Reg.D5.S1.Recurrence.KRegularInterleaving

open _root_.D5.S1.Recurrence.KRegularInterleaving
open _root_.D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions (kKernel IsKRegular)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev Params := ℕ → ℤ

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℤ)

abbrev actual : Realization signature :=
  realize signature (fun _ s n => s n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k a : ℕ) (s : ℕ → ℤ) (_hk : 2 ≤ k) (_ha : 1 ≤ a)
    (_hs : ∀ i : ℕ, i < a → IsKRegular k (fun n => s (a * n + i))),
    IsKRegular k (R.readout () s)

private theorem exists_bad_pair :
    ∃ p : ℕ × (ℕ → ℤ), 2 ≤ p.1 ∧ ¬ IsKRegular p.1 p.2 := by
  obtain ⟨bad, hbad⟩ :=
    _root_.Reg.D5.S1.Recurrence.KRegularAffineSubsequence.Closure.family.variation.2
  by_contra h
  push_neg at h
  apply hbad
  intro k a b s hk ha hs
  exact h (k, bad.readout () ⟨a, b, s⟩) hk

private def badPair : ℕ × (ℕ → ℤ) := Classical.choose exists_bad_pair

abbrev rejected : Realization signature :=
  realize signature (fun _ _ n => badPair.2 n) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := Classical.choose_spec exists_bad_pair
  change 2 ≤ badPair.1 ∧ ¬ IsKRegular badPair.1 badPair.2 at hp
  have hz : IsKRegular badPair.1 (fun _ => (0 : ℤ)) := by
    apply Submodule.fg_span
    apply (Set.finite_singleton (fun _ : ℕ => (0 : ℤ))).subset
    rintro f ⟨e, r, hr, rfl⟩
    rfl
  exact hp.2 (h badPair.1 1 (fun _ => 0) hp.1 (by decide) (by
    intro i hi
    exact hz))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun n : ℕ => (n : ℤ)), 0, 1, ?_⟩
  change (0 : ℤ) ≠ 1
  decide

def family : Registration arena (type_of% (@is_k_regular_interleaving)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨is_k_regular_interleaving, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@is_k_regular_interleaving) (Realization signature) (Type) Unit where
  unitName := `D5.S1.Recurrence.KRegularInterleaving.is_k_regular_interleaving.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.KRegularInterleaving.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s n => s n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.KRegularInterleaving
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.KRegularInterleaving

end
