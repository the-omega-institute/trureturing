import D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound information registration for Kepler’s graphwise count. -/

open LeanInformationAudit
open D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

abbrev actual : Realization signature :=
  realize signature (fun _ _ count => 2 * count) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

universe u

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (α : ℝ),
    Nat.card (SupportPairs G α) = classPairSum (classSetoid G α) ∧
    Nat.card (SignedEigenvectors G α) = R.readout () () (classPairSum (classSetoid G α))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 2)) := ⊥
  let v0 : ULift.{u} (Fin 2) := ⟨0⟩
  let v1 : ULift.{u} (Fin 2) := ⟨1⟩
  have hne : v0 ≠ v1 := by decide
  have hvec : IsSignedEigenvector G 0 (signedPair v0 v1) := by
    constructor
    · refine ⟨v0, v1, hne, ?_, ?_, ?_⟩
      · simp [signedPair, hne]
      · simp [signedPair, hne.symm]
      · intro w hw0 hw1
        simp [signedPair, hw0, hw1]
    · exact ⟨0, by simp [bAlpha, G, SimpleGraph.lapMatrix_bot]⟩
  have hfinite : Finite (SignedEigenvectors G 0) :=
    Finite.of_injective (directedRealization G 0).symm (directedRealization G 0).symm.injective
  have hpos := Nat.card_pos_iff.mpr ⟨⟨⟨_, hvec⟩⟩, hfinite⟩
  have hzero : Nat.card (SignedEigenvectors G 0) = 0 := (h G 0).2
  exact (Nat.ne_of_gt hpos) hzero

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (2 : ℕ) * 0 ≠ 2 * 1
  decide

def family : Registration arena (type_of% (@graphwise_count)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@graphwise_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@graphwise_count) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo.graphwise_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ count => 2 * count) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      booleanPredicate := false
      stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.KeplerSupportTwo
