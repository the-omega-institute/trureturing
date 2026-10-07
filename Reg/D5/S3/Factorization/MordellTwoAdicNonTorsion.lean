import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.MordellTwoAdicNonTorsion
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion

open _root_.D5.S3.Factorization.MordellTwoAdicNonTorsion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)

def rejectedX : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def rejectedY : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem torsion_example :
    ∃ h : (mordellCurve (-1)).Nonsingular (1 : ℚ) 0,
      IsOfFinAddOrder (.some 1 0 h : (mordellCurve (-1)).Point) := by
  have hns : (mordellCurve (-1)).Nonsingular (1 : ℚ) 0 := by
    apply ((mordellCurve (-1)).nonsingular_iff' _ _).2
    constructor
    · apply ((mordellCurve (-1)).equation_iff _ _).2
      norm_num [mordellCurve]
    · left
      norm_num [mordellCurve]
  refine ⟨hns, isOfFinAddOrder_iff_nsmul_eq_zero.mpr ?_⟩
  refine ⟨2, by decide, ?_⟩
  have hdouble :
      (.some 1 0 hns : (mordellCurve (-1)).Point) +
        (.some 1 0 hns : (mordellCurve (-1)).Point) = 0 :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      (W := mordellCurve (-1)) (by norm_num [mordellCurve, WeierstrassCurve.Affine.negY])
  simpa only [two_nsmul] using hdouble

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℚ), (2 : ℚ), ?_⟩
  change padicValRat 2 (1 : ℚ) ≠ padicValRat 2 (2 : ℚ)
  rw [padicValRat.one]
  change (0 : ℤ) ≠ padicValRat 2 ((2 : ℕ) : ℚ)
  rw [padicValRat.of_nat]
  norm_num [padicValNat_self]

def xArena : Arena where
  signature := signature
  Law r := ∀ (b : ℤ) {x y : ℚ} (h : (mordellCurve b).Nonsingular x y),
    r.readout () () x < 0 →
      ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point)

private theorem rejected_x_law : ¬ xArena.Law rejectedX := by
  intro h
  obtain ⟨hns, htor⟩ := torsion_example
  have hbad := h (-1) (x := 1) (y := 0) hns (by norm_num [rejectedX, realize])
  exact hbad htor

def xRegistration : Registration xArena (xArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_add_order_of_negative_two_adic_x, rejectedX, rejected_x_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedX, ?_, rfl, rejected_x_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "MordellTwoAdicNonTorsion") "infinite_add_order_of_negative_two_adic_x") "Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion/Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(xArena)⟩,
  objectArena := .source ⟨(xArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (xArena) ⟨(xRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "domain", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.observationFact0, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.anchorEnumeration }


def yArena : Arena where
  signature := signature
  Law r := ∀ (b : ℤ) {x y : ℚ} (h : (mordellCurve b).Nonsingular x y)
    (hx0 : x ≠ 0) (hx : padicValRat 2 x = 0),
    0 < r.readout () () y →
      ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point)

private theorem rejected_y_law : ¬ yArena.Law rejectedY := by
  intro h
  obtain ⟨hns, htor⟩ := torsion_example
  have hbad := h (-1) (x := 1) (y := 0) hns (by norm_num)
    (by simp [padicValRat.one]) (by norm_num [rejectedY, realize])
  exact hbad htor

def yRegistration : Registration yArena (yArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_add_order_of_unit_x_positive_two_adic_y, rejectedY, rejected_y_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedY, ?_, rfl, rejected_y_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "MordellTwoAdicNonTorsion") "infinite_add_order_of_unit_x_positive_two_adic_y") "Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion/Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(yArena)⟩,
  objectArena := .source ⟨(yArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (yArena) ⟨(yRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ q => padicValRat 2 q) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "domain", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalArenaFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.sourceBridgeFact, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.observationFact0, `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.anchorEnumeration }


#print axioms xRegistration
#print axioms yRegistration

end Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion


noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yArena
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yArena
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xArena
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xArena
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yArena) (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).actual

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_unit_x_positive_two_adic_y\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).bridge

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.observation0 : (b : Int) →
  {x y : Rat} →
    (h :
        @WeierstrassCurve.Affine.Nonsingular.{0} Rat Rat.commRing
          (D5.S3.Factorization.MordellTwoAdicNonTorsion.mordellCurve b) x y) →
      (hx0 : @Ne.{1} Rat x (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) →
        (hx :
            @Eq.{1} Int (padicValRat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
              (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (b : Int) {x y : Rat}
    (h :
      @WeierstrassCurve.Affine.Nonsingular.{0} Rat Rat.commRing
        (D5.S3.Factorization.MordellTwoAdicNonTorsion.mordellCurve b) x y)
    (hx0 : @Ne.{1} Rat x (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (hx :
      @Eq.{1} Int (padicValRat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.signature Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.actual
    PUnit.unit.{1} PUnit.unit.{1} y

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_unit_x_positive_two_adic_y\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y, part := .type, path := [.body, .body, .body, .body, .body, .body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_unit_x_positive_two_adic_y\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_unit_x_positive_two_adic_y, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).actual (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).variation.2.choose (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).variation.1 (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"yRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.yRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xArena) (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).actual

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_negative_two_adic_x\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).bridge

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.observation0 : (b : Int) →
  {x y : Rat} →
    (h :
        @WeierstrassCurve.Affine.Nonsingular.{0} Rat Rat.commRing
          (D5.S3.Factorization.MordellTwoAdicNonTorsion.mordellCurve b) x y) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (b : Int) {x y : Rat}
    (h :
      @WeierstrassCurve.Affine.Nonsingular.{0} Rat Rat.commRing
        (D5.S3.Factorization.MordellTwoAdicNonTorsion.mordellCurve b) x y) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.signature Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.actual
    PUnit.unit.{1} PUnit.unit.{1} x

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_negative_two_adic_x\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"domain\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x, part := .type, path := [.body, .body, .body, .body, .domain, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"infinite_add_order_of_negative_two_adic_x\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `D5.S3.Factorization.MordellTwoAdicNonTorsion.infinite_add_order_of_negative_two_adic_x, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).actual (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).variation.2.choose (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).variation.1 (Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"MordellTwoAdicNonTorsion\",\"xRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion, declaration := `Reg.D5.S3.Factorization.MordellTwoAdicNonTorsion.xRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
