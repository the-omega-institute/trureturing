import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.IntegerCharacterCoercivity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Metric Set
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Fourier.IntegerCharacterCoercivity
universe u

abbrev Params := Σ q : ℕ, Σ I : Type u, I → Fin q → ℤ

abbrev signature : Signature where
  Params := Params.{u}
  State p := EuclideanSpace ℝ (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Squared distance to the full simultaneous integer-character zero set. -/
def actual : Realization signature.{u} :=
  realize signature (fun _ p x =>
    (infDist x {y : EuclideanSpace ℝ (Fin p.1) |
      ∀ a, ∃ k : ℤ, (∑ i, (p.2.2 a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law r := ∀ (q : ℕ) {I : Type u} [Fintype I] (lam : I → Fin q → ℤ),
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin q),
      c * r.readout () ⟨q, I, lam⟩ x ≤
        ∑ a, (1 - Real.cos (∑ i, (lam a i : ℝ) * x i))

/-- The original zero-dimensional, empty-family boundary rejects constant one. -/
theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  obtain ⟨c, hc, hx⟩ := h 0 (I := ULift.{u} Empty) (fun a => nomatch a.down)
  have hh := hx 0
  have : c ≤ 0 := by simpa [rejected, realize] using hh
  exact (not_le_of_gt hc) this

/-- Dependence is witnessed by the closed cosine-one fiber at zero and pi. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let U : Set (EuclideanSpace ℝ (Fin 1)) :=
    {y | ∀ _ : ULift.{u} Unit, ∃ k : ℤ, (∑ j, ((1 : ℤ) : ℝ) * y j) = 2 * Real.pi * k}
  have hU : U = {y : EuclideanSpace ℝ (Fin 1) | Real.cos (y 0) = 1} := by
    ext y
    simp only [U, mem_setOf_eq, Int.cast_one, one_mul, Fin.sum_univ_one]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h ⟨()⟩
      rw [hk, mul_comm (2 * Real.pi), Real.cos_int_mul_two_pi]
    · intro h a
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (y 0)).mp h
      exact ⟨k, by linarith⟩
  have hclosed : IsClosed U := by
    rw [hU]
    exact isClosed_eq (Real.continuous_cos.comp (PiLp.continuous_apply 2 _ 0)) continuous_const
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ U := by simp [hU]
  let y : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => Real.pi)
  have hy : y ∉ U := by norm_num [hU, y]
  have hd : 0 < infDist y U := (hclosed.notMem_iff_infDist_pos ⟨0, hzero⟩).mp hy
  refine ⟨⟨1, ULift.{u} Unit, fun _ _ => 1⟩, 0, y, ?_⟩
  change (infDist 0 U)^2 ≠ (infDist y U)^2
  rw [infDist_zero_of_mem hzero, zero_pow (by decide : 2 ≠ 0)]
  exact ne_of_lt (sq_pos_of_pos hd)

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity.{u_1}) (type_of% (realize.{u_1 + 1, 0, 0, 0, 0} signature.{u_1} (fun _ p x =>
    (infDist.{0} x {y : EuclideanSpace.{0, 0} ℝ (Fin p.1) |
      ∀ a, ∃ k : ℤ, (∑ i, (p.2.2 a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "IntegerCharacterCoercivity") "integer_character_global_coercivity") "Reg.D5.S3.Fourier.IntegerCharacterCoercivity/Reg.D5.S3.Fourier.IntegerCharacterCoercivity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, 0, 0, 0, 0} signature.{u_1} (fun _ p x =>
    (infDist.{0} x {y : EuclideanSpace.{0, 0} ℝ (Fin p.1) |
      ∀ a, ∃ k : ℤ, (∑ i, (p.2.2 a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.IntegerCharacterCoercivity, definition := none, coordinates := #[0, 1, 3], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.observationFact0, `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Fourier.IntegerCharacterCoercivity


noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.IntegerCharacterCoercivity.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.IntegerCharacterCoercivity.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, 0, 0, 0, 0} (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.arena.) (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"integer_character_global_coercivity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.observation0.{u_1} : (q : Nat) →
  {I : Type u_1} →
    [Fintype.{u_1} I] →
      (lam : I → Fin q → Int) →
        (c : Real) →
          (x : EuclideanSpace.{0, 0} Real (Fin q)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, 0, 0, 0, 0}
              Reg.D5.S3.Fourier.IntegerCharacterCoercivity.signature.{u_1} PUnit.unit.{1}
              (@Sigma.mk.{0, u_1 + 1} Nat
                (fun (q : Nat) => @Sigma.{u_1 + 1, u_1} (Type u_1) fun (I : Type u_1) => I → Fin q → Int) q
                (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (I : Type u_1) => I → Fin q → Int) I lam)) :=
  fun (q : Nat) {I : Type u_1} [Fintype.{u_1} I] (lam : I → Fin q → Int) (c : Real)
    (x : EuclideanSpace.{0, 0} Real (Fin q)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.IntegerCharacterCoercivity.signature.{u_1}
    Reg.D5.S3.Fourier.IntegerCharacterCoercivity.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{0, u_1 + 1} Nat
      (fun (q : Nat) => @Sigma.{u_1 + 1, u_1} (Type u_1) fun (I : Type u_1) => I → Fin q → Int) q
      (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (I : Type u_1) => I → Fin q → Int) I lam))
    x

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"integer_character_global_coercivity\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .body, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"integer_character_global_coercivity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).actual (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).variation.2.choose (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).variation.1 (Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"IntegerCharacterCoercivity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity, declaration := `Reg.D5.S3.Fourier.IntegerCharacterCoercivity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
