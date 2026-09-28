import D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p o =>
    _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
      p.2.1 p.2.2 p.1 p.2.1 p.2.2 o) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (r a b o : ℝ), 1 < r → 1 < a → 1 < b → 1 < o →
    R.readout () ⟨r, a, b⟩ o ≤ -1 →
    a > b ∧ Real.sqrt ((r + 1) * (o + 1)) ≤ a - b

theorem actual_law : arena.Law actual := by
  intro r a b o hr ha hb ho hchosen
  exact flat_transverse_gap_of_chosen r a b o hr ha hb ho hchosen

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [rejected, realize])
  norm_num at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(8 : ℝ), 3, 3⟩, (8 : ℝ), (47 / 2 : ℝ), ?_⟩
  norm_num [actual, realize,
    _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine,
    _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.numerator,
    _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.rad]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.flat_transverse_gap_of_chosen
  in arena
  readout via (realize signature (fun _ p o =>
    _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
      p.2.1 p.2.2 p.1 p.2.1 p.2.2 o) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.flat_transverse_gap_of_chosen
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "One-premise flat gap registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "One-premise flat gap lacks validated source-bound four-slot evidence"
  | .declaredUnresolved diagnostic =>
      throwError "One-premise flat gap registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "One-premise flat gap registration is undeclared"

#print axioms registration

end

end Reg.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
