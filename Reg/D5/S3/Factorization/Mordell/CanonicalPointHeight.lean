import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.CanonicalPointHeight
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

namespace Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight

open Height Filter Topology
open WeierstrassCurve WeierstrassCurve.Affine
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 𝓝 (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : Type u} [Field F] {W : Affine F}
    [AdmissibleAbsValues F] [DecidableEq F] [W.toAffine.IsElliptic],
    (∀ P : W.Point, Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n))
      atTop (R.readout () () P.canonicalHeight)) ∧
    (∃ D, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight / 2| ≤ D) ∧
    (∀ P Q : W.Point, (P + Q).canonicalHeight + (P - Q).canonicalHeight =
      2 * (P.canonicalHeight + Q.canonicalHeight))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} ℚ
  letI : NumberField F := NumberField.of_ringEquiv ℚ F
    (ULift.ringEquiv : F ≃+* ℚ).symm
  letI : AdmissibleAbsValues F := inferInstance
  let W : Affine F := ⟨0, 0, 0, -1, 0⟩
  letI : W.toAffine.IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hbad := (h (F := F) (W := W)).1 (0 : W.Point)
  have hgood : Tendsto
      (fun n : ℕ => ((2 ^ n) • (0 : W.Point)).naiveHeight / (2 * 4 ^ n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [Point.naiveHeight, Point.xRep_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  change Tendsto _ atTop (𝓝 (1 : ℝ)) at hbad
  have hf := tendsto_nhds_unique hgood hbad
  norm_num at hf

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Point.canonicalHeight_properties.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change 𝓝 (0 : ℝ) ≠ 𝓝 (1 : ℝ)
    intro h
    have hf := nhds_injective h
    norm_num at hf

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.WeierstrassCurve.Affine.Point.canonicalHeight_properties.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 𝓝 x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "WeierstrassCurve") "Affine") "Point") "canonicalHeight_properties") "Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight/Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `WeierstrassCurve.Affine.Point.canonicalHeight_properties, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.observationFact0, `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.anchorEnumeration }


#print axioms registration


end
end Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight


noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
      Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.actual)
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1})

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"WeierstrassCurve\",\"Affine\",\"Point\",\"canonicalHeight_properties\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `WeierstrassCurve.Affine.Point.canonicalHeight_properties, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.arena.{u_1}
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.actual)
  Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1})

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.observation0.{u_1} : {F : Type u_1} →
  [inst : Field.{u_1} F] →
    {W : WeierstrassCurve.Affine.{u_1} F} →
      [@Height.AdmissibleAbsValues.{u_1} F inst] →
        [DecidableEq.{u_1 + 1} F] →
          [@WeierstrassCurve.IsElliptic.{u_1} F (@Field.toCommRing.{u_1} F inst)
                (@WeierstrassCurve.toAffine.{u_1} F W)] →
            (P : @WeierstrassCurve.Affine.Point.{u_1} F (@Field.toCommRing.{u_1} F inst) W) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {F : Type u_1} [inst : Field.{u_1} F] {W : WeierstrassCurve.Affine.{u_1} F}
    [inst_1 : @Height.AdmissibleAbsValues.{u_1} F inst] [inst_2 : DecidableEq.{u_1 + 1} F]
    [@WeierstrassCurve.IsElliptic.{u_1} F (@Field.toCommRing.{u_1} F inst) (@WeierstrassCurve.toAffine.{u_1} F W)]
    (P : @WeierstrassCurve.Affine.Point.{u_1} F (@Field.toCommRing.{u_1} F inst) W) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.signature
    Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.actual PUnit.unit.{1} PUnit.unit.{1}
    (@WeierstrassCurve.Affine.Point.canonicalHeight.{u_1} F inst W inst_1 inst_2 P)

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"WeierstrassCurve\",\"Affine\",\"Point\",\"canonicalHeight_properties\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `WeierstrassCurve.Affine.Point.canonicalHeight_properties, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"WeierstrassCurve\",\"Affine\",\"Point\",\"canonicalHeight_properties\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `WeierstrassCurve.Affine.Point.canonicalHeight_properties, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1}).actual (Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1}).variation.2.choose (Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1}).variation.1 (Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Mordell\",\"CanonicalPointHeight\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight, declaration := `Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
