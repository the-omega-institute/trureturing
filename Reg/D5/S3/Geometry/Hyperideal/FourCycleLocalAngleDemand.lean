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


namespace Reg.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.Original

open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
noncomputable section

namespace Demand

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-2 * Real.pi)) (fun e => nomatch e)

/-- Every hypothesis of the original angle demand remains in the Law. -/
def arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law ρ := ∀
    (r a b o : ℝ)
    (_hr : 1 < r) (_ha : 1 < a) (_hb : 1 < b) (_ho : 1 < o)
    (_hdom : 1 + a + b ≤ r)
    (_ht : -1 < cosine r a b o a b ∧ cosine r a b o a b < 1)
    (_hbeta : -1 < cosine a b r a b o ∧ cosine a b r a b o < 1)
    (_hdelta : -1 < cosine b a r b a o ∧ cosine b a r b a o < 1),
    ρ.readout () () (Real.arccos (cosine r a b o a b)) +
      Real.arccos (cosine a b r a b o) +
        Real.arccos (cosine b a r b a o) > Real.pi

private theorem witness_axis : cosine 5 2 2 2 2 2 = 0 := by
  norm_num [cosine, numerator, rad]

private theorem witness_transverse :
    -1 < cosine 2 2 5 2 2 2 ∧ cosine 2 2 5 2 2 2 < 1 := by
  have hs : 0 < Real.sqrt (1944 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1944)
  have hgt : (36 : ℝ) < Real.sqrt 1944 := by nlinarith
  norm_num [cosine, numerator, rad, div_div,
    ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 27)]
  constructor
  · exact lt_trans (by norm_num : (-1 : ℝ) < 0) (div_pos (by norm_num) hs)
  · exact (div_lt_one hs).2 hgt

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 5 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [witness_axis]; norm_num)
    witness_transverse witness_transverse
  change -2 * Real.pi + Real.arccos (cosine 2 2 5 2 2 2) +
    Real.arccos (cosine 2 2 5 2 2 2) > Real.pi at hb
  have hu := Real.arccos_le_pi (cosine 2 2 5 2 2 2)
  linarith [Real.pi_pos]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@paired_angle_demand, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.paired_angle_demand
  in arena
  readout via (realize signature (fun _ _ x => 2 * x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let target := `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.paired_angle_demand
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == target &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Missing original CFMP registration"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome && certificate.sourceBinding.isSome &&
          row.escape.bridgeKind == "source-equivalence" &&
          row.escape.continuation.any (·.kind == "open") do
        throwError "Original CFMP registration lacks four-slot source evidence"
  | .declaredUnresolved diagnostic => throwError "Original CFMP unresolved: {diagnostic}"
  | .undeclared => throwError "Original CFMP registration is undeclared"

#print axioms registration

end Demand

namespace FlatGap

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (4 : ℝ)) (fun e => nomatch e)

/-- Both flat-gap conjuncts and all three flat guards are retained. -/
def arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law ρ := ∀
    (r a b o : ℝ)
    (_hr : 1 < r) (_ha : 1 < a) (_hb : 1 < b) (_ho : 1 < o)
    (_haxis : 1 ≤ cosine r a b o a b)
    (_hchosen : cosine a b r a b o ≤ -1)
    (_hother : 1 ≤ cosine b a r b a o),
    a > b ∧ ρ.readout () () ((r + 1) * (o + 1)) ≤ a - b

private theorem witness_cosines :
    cosine 2 5 2 2 5 2 = 1 ∧ cosine 5 2 2 5 2 2 = -1 ∧
      cosine 2 5 2 2 5 2 = 1 := by
  norm_num [cosine, numerator, rad, div_div, ← pow_two,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 72)]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hw := witness_cosines
  have hb := h 2 5 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hw.1]) (by rw [hw.2.1]) (by rw [hw.2.2])
  change (5 : ℝ) > 2 ∧ 4 ≤ 5 - 2 at hb
  norm_num at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@flat_transverse_gap, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.flat_transverse_gap
  in arena
  readout via (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg",
        "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let target := `D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.flat_transverse_gap
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == target &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Missing original CFMP registration"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome && certificate.sourceBinding.isSome &&
          row.escape.bridgeKind == "source-equivalence" &&
          row.escape.continuation.any (·.kind == "open") do
        throwError "Original CFMP registration lacks four-slot source evidence"
  | .declaredUnresolved diagnostic => throwError "Original CFMP unresolved: {diagnostic}"
  | .undeclared => throwError "Original CFMP registration is undeclared"

#print axioms registration

end FlatGap

end
end Reg.D5.S3.Geometry.Hyperideal.FourCycleLocalAngleDemand.Original
