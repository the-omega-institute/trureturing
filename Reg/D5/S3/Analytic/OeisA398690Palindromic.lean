import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OeisA398690Palindromic
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Analytic.OeisA398690Palindromic

open Polynomial
open _root_.D5.S3.Analytic.OeisA398690Palindromic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n q => simplifiedVerlinde (n + 3) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ∃ p : ℝ[X], p.natDegree = n ∧
    PowerSeries.mk (fun q => R.readout () n q) *
      (1 - PowerSeries.X) ^ (n + 1) = (p : PowerSeries ℝ) ∧
    ∀ j ≤ n, p.coeff j = p.coeff (n - j)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hdeg, hseries, _⟩ := h 1
  have hzero : PowerSeries.mk (fun _ : ℕ => (0 : ℝ)) = 0 := by
    ext q
    simp
  have hpseries : (p : PowerSeries ℝ) = 0 := by
    change PowerSeries.mk (fun _ : ℕ => (0 : ℝ)) *
      (1 - PowerSeries.X) ^ 2 = (p : PowerSeries ℝ) at hseries
    rw [hzero, zero_mul] at hseries
    exact hseries.symm
  have hp : p = 0 := by
    exact (Polynomial.coe_injective ℝ) hpseries
  simp [hp] at hdeg

private theorem source_at_zero : simplifiedVerlinde 4 0 = 1 := by
  norm_num [simplifiedVerlinde, Finset.sum_range_succ, Real.sin_pi_div_two]

private theorem source_at_one : simplifiedVerlinde 4 1 = 3 := by
  have h3 : Real.sin (3 * Real.pi / 6) = 1 := by
    convert Real.sin_pi_div_two using 1 <;> ring
  have h5 : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  norm_num [simplifiedVerlinde, Finset.sum_range_succ,
    Real.sin_pi_div_six, h3, h5]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ p : ℕ, ∃ x y : ℕ,
      simplifiedVerlinde (p + 3) x ≠ simplifiedVerlinde (p + 3) y
    refine ⟨1, 0, 1, ?_⟩
    change simplifiedVerlinde 4 0 ≠ simplifiedVerlinde 4 1
    rw [source_at_zero, source_at_one]
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Analytic.OeisA398690Palindromic.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ n q => simplifiedVerlinde (n + 3) q) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Analytic") "OeisA398690Palindromic") "result") "Reg.D5.S3.Analytic.OeisA398690Palindromic/Reg.D5.S3.Analytic.OeisA398690Palindromic.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration,
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
    (fun _ n q => simplifiedVerlinde (n + 3) q) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Analytic.OeisA398690Palindromic, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "body"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Analytic.OeisA398690Palindromic, declaration := `D5.S3.Analytic.OeisA398690Palindromic.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalArenaFact, `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.sourceBridgeFact, `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.observationFact0, `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Analytic.OeisA398690Palindromic


noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Analytic.OeisA398690Palindromic.arena
noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Analytic.OeisA398690Palindromic.arena
noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Analytic.OeisA398690Palindromic.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Analytic.OeisA398690Palindromic.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Analytic.OeisA398690Palindromic.arena Reg.D5.S3.Analytic.OeisA398690Palindromic.actual)
    Reg.D5.S3.Analytic.OeisA398690Palindromic.registration)

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Analytic.OeisA398690Palindromic, declaration := `D5.S3.Analytic.OeisA398690Palindromic.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Analytic.OeisA398690Palindromic.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Analytic.OeisA398690Palindromic.arena Reg.D5.S3.Analytic.OeisA398690Palindromic.actual)
  Reg.D5.S3.Analytic.OeisA398690Palindromic.registration)

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.observation0 : (n : Nat) →
  (r : @Polynomial.{0} Real Real.semiring) →
    (q : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Analytic.OeisA398690Palindromic.signature PUnit.unit.{1} n :=
  fun (n : Nat) (r : @Polynomial.{0} Real Real.semiring) (q : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Analytic.OeisA398690Palindromic.signature Reg.D5.S3.Analytic.OeisA398690Palindromic.actual PUnit.unit.{1}
    n q

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Analytic.OeisA398690Palindromic, declaration := `D5.S3.Analytic.OeisA398690Palindromic.result, part := .type, path := [.body, .argument, .body, .argument, .function, .argument, .function, .argument, .function, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Analytic.OeisA398690Palindromic, declaration := `D5.S3.Analytic.OeisA398690Palindromic.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Analytic.OeisA398690Palindromic.registration).actual (Reg.D5.S3.Analytic.OeisA398690Palindromic.registration).variation.2.choose (Reg.D5.S3.Analytic.OeisA398690Palindromic.registration).variation.1 (Reg.D5.S3.Analytic.OeisA398690Palindromic.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Analytic\",\"OeisA398690Palindromic\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Analytic.OeisA398690Palindromic, declaration := `Reg.D5.S3.Analytic.OeisA398690Palindromic.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
