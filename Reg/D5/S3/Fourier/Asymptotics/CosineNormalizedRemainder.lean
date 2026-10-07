import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
import Reg.Support.DependentFamily

open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ))
    (fun e => nomatch e)

/-- A perturbation of the literal summand with unbounded total error N².
A bounded perturbation alone would not contradict the uniform existential constant. -/
def rejected : Realization signature :=
  realize signature (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ) +
    if k = 1 then (p.2 : ℝ) ^ 2 else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ, 1 ≤ N →
    |(∑ k ∈ Finset.Icc 1 N, r.readout () ⟨θ, N⟩ k) -
      (-Real.log θ + cosineIntegral ((N : ℝ) * θ))| ≤
      C * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ))))

theorem rejected_sum (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, rejected.readout () ⟨θ, N⟩ k) =
      (∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) + (N : ℝ) ^ 2 := by
  simp [rejected, realize, Finset.sum_add_distrib, hN]

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, hC, h⟩
  obtain ⟨K, hK, hactual⟩ :=
    _root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (C + K) + 1)
  have hn1 : (1 : ℝ) < N := by linarith
  have hn : 1 ≤ N := by exact_mod_cast hn1.le
  have hn0 : (0 : ℝ) < N := by linarith
  have hbad := h 1 zero_lt_one le_rfl N hn
  have hgood := hactual 1 zero_lt_one le_rfl N hn
  rw [rejected_sum 1 N hn] at hbad
  simp only [Real.log_one, neg_zero, zero_add, mul_one, one_mul] at hbad hgood
  have he : (N : ℝ) ^ 2 ≤
      (C + K) * (1 / (N : ℝ) + (1 + max 0 (Real.log (N : ℝ)))) := by
    have hb := (abs_le.mp hbad).2
    have hg := (abs_le.mp hgood).1
    nlinarith
  have hinv : 1 / (N : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1.le
  have hw : 1 / (N : ℝ) + (1 + max 0 (Real.log (N : ℝ))) ≤ 2 * N := by
    have hl : max 0 (Real.log (N : ℝ)) ≤ (N : ℝ) - 1 :=
      max_le (by linarith) (Real.log_le_sub_one_of_pos hn0)
    linarith
  have he' := he.trans (mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ C + K))
  nlinarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 2⟩, (1 : ℕ), (2 : ℕ), ?_⟩
    norm_num only [actual, realize, Nat.cast_one, Nat.cast_ofNat, mul_one, div_one]
    intro h
    have hn : Real.cos 2 / 2 < 0 :=
      div_neg_of_neg_of_pos Real.cos_two_neg (by norm_num)
    exact (not_lt_of_ge Real.cos_one_pos.le) (h.symm ▸ hn)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "Asymptotics") "CosineNormalizedRemainder") "result") "Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder/Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration,
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
    (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, definition := none, coordinates := #[1, 4], readouts := #[{ path := #["arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg", "body"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.observationFact0, `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.arena
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.arena) (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).actual

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).bridge

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.observation0 : (C θ : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) θ →
    @LE.le.{0} Real Real.instLE θ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      (N : Nat) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N →
          (k : Nat) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) θ N) :=
  fun (C θ : Real)
    (a : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) θ)
    (a_1 : @LE.le.{0} Real Real.instLE θ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (N : Nat) (a_2 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
    (k : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.signature
    Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) θ N) k

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result, part := .type, path := [.argument, .body, .argument, .body, .body, .body, .body, .body, .function, .argument, .argument, .function, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).actual (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).variation.2.choose (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).variation.1 (Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"Asymptotics\",\"CosineNormalizedRemainder\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder, declaration := `Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
