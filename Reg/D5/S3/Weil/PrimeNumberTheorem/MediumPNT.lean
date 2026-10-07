import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Reg.Support.DependentFamily
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT

open Filter Asymptotics
open scoped Topology Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Chebyshev.psi x - x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ c > 0,
    (fun x => r.readout () () x) =O[atTop]
      fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change ∃ c > 0, (id : ℝ → ℝ) =O[atTop]
    fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) at h
  obtain ⟨c, hc, hBigO⟩ := h
  have hPow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hExponent : Tendsto
      (fun x : ℝ => -c * (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -c < 0)).2 hPow
  have hDecay : Tendsto
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hExponent
  have hDecayLittleO :
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hDecay
  have hWeightedLittleO :
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =o[atTop] (fun x : ℝ => x) := by
    simpa only [Pi.mul_apply, Pi.one_apply, mul_one] using
      (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hDecayLittleO
  have hSelf : (id : ℝ → ℝ) =o[atTop] (id : ℝ → ℝ) :=
    hBigO.trans_isLittleO hWeightedLittleO
  obtain ⟨x, hx, hpos⟩ :=
    ((hSelf.bound (by norm_num : 0 < (1 : ℝ) / 2)).and
      (eventually_gt_atTop (0 : ℝ))).exists
  change ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ at hx
  rw [Real.norm_eq_abs, abs_of_pos hpos] at hx
  linarith

def registration : Registration arena
    (∃ c > 0, (Chebyshev.psi - (id : ℝ → ℝ)) =O[atTop]
      fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.MediumPNT, rejected, rejected_law⟩
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
    change Chebyshev.psi 0 - 0 ≠ Chebyshev.psi 1 - 1
    norm_num [Chebyshev.psi_zero, Chebyshev.psi_one]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.MediumPNT) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ x => Chebyshev.psi x - x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "MediumPNT") "Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT/Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ x => Chebyshev.psi x - x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `MediumPNT, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.anchorEnumeration }


end

end Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.arena) (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).actual

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"MediumPNT\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `MediumPNT, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).bridge

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.observation0 : (c : Real) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
      Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.signature PUnit.unit.{1} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (c : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.signature Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.actual
    PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"MediumPNT\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `MediumPNT, part := .type, path := [.argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"MediumPNT\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `MediumPNT, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MediumPNT\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
