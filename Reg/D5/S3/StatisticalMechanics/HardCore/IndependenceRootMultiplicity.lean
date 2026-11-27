import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the native corona helpers. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open LeanInformationAudit Polynomial

private abbrev Parameters := Σ _ : ℕ, ℕ

namespace Connected

private abbrev GraphFamily := (t k : ℕ) → SimpleGraph (Vertex t k)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun _ => GraphFamily) (fun p => SimpleGraph (Vertex p.1 p.2))

def actual : Realization signature :=
  realize signature (fun _ p F => F p.1 p.2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t k : ℕ}, 0 < t → (R.readout () ⟨t, k⟩ corona).Connected

private theorem disconnected_bottom : ¬ (⊥ : SimpleGraph (Vertex 2 0)).Connected :=
  SimpleGraph.not_connected_bot

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact disconnected_bottom (@h 2 0 (by decide))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 0⟩, corona, (fun _ _ => ⊥), ?_⟩
  change corona 2 0 ≠ ⊥
  intro h
  exact disconnected_bottom (h ▸ @corona_connected 2 0 (by decide))

def evidence : Registration arena (type_of% @corona_connected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@corona_connected, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end Connected

namespace Factorization

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Finset (Vertex p.1 p.2)) (fun _ => Polynomial ℤ)

def actual : Realization signature :=
  realize signature (fun _ p V => independencePolynomial (corona p.1 p.2) V)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t k : ℕ}, 0 < t →
    R.readout () ⟨t, k⟩ Finset.univ =
      (1 + X) ^ ((t - 1) * k) * ((1 + X) ^ k + (t : Polynomial ℤ) * X)

private theorem value_at_one_zero :
    independencePolynomial (corona 1 0) Finset.univ = 1 + X := by
  simpa using @corona_factorization 1 0 (by decide)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq := @h 1 0 (by decide)
  change (0 : Polynomial ℤ) = _ at heq
  have hcoeff := congrArg (fun q : Polynomial ℤ => q.coeff 0) heq
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X] at hcoeff

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0⟩, Finset.univ, ∅, ?_⟩
  change independencePolynomial (corona 1 0) Finset.univ ≠
    independencePolynomial (corona 1 0) ∅
  rw [value_at_one_zero, independencePolynomial, partition_empty]
  intro h
  have hcoeff := congrArg (fun q : Polynomial ℤ => q.coeff 1) h
  simp [Polynomial.coeff_add] at hcoeff

def evidence : Registration arena (type_of% @corona_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@corona_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end Factorization

namespace RootMultiplicity

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => Polynomial ℤ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ q => rootMultiplicity (-1 : ℤ) q) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {t k : ℕ}, 0 < t → 0 < k →
    R.readout () ⟨t, k⟩ (independencePolynomial (corona t k) Finset.univ) = (t - 1) * k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad : (0 : ℕ) = 1 := @h 2 1 (by decide) (by decide)
  exact Nat.zero_ne_one hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, independencePolynomial (corona 2 1) Finset.univ, C 1, ?_⟩
  change rootMultiplicity (-1 : ℤ) (independencePolynomial (corona 2 1) Finset.univ) ≠
    rootMultiplicity (-1 : ℤ) (C 1)
  rw [@corona_rootMultiplicity 2 1 (by decide) (by decide), rootMultiplicity_C]
  decide

def evidence : Registration arena (type_of% @corona_rootMultiplicity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@corona_rootMultiplicity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

end RootMultiplicity

namespace Connected

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@corona_connected)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.Connected.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.Connected.evidence
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
    owner := `D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Connected

namespace Factorization

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@corona_factorization)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.Factorization.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.Factorization.evidence
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
    owner := `D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Factorization

namespace RootMultiplicity

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@corona_rootMultiplicity)
    (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.RootMultiplicity.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity.RootMultiplicity.evidence
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
    owner := `D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RootMultiplicity

end Reg.D5.S3.StatisticalMechanics.HardCore.IndependenceRootMultiplicity
