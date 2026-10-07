import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open _root_.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness
open Filter Lean Elab Command LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Topology

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ε => ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      let C : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 0
      let E0 : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 1
      let E1 : Matrix (Fin 3) (Fin 3) ℂ := basisProjector 2
      let rhoM : Matrix (Fin 3) (Fin 3) ℂ := diagonalState (fun i =>
        if i = 0 then 1 - ε else if i = 1 then ε else 0)
      let sigmaM : Matrix (Fin 3) (Fin 3) ℂ := diagonalState (fun i =>
        if i = 0 then 1 - ε else if i = 2 then ε else 0)
      let P : Matrix (Fin 3) (Fin 3) ℂ := E0 + E1
      ∃ ρ σ : DensityState (Fin 3), ∃ Pm K : Matrix (Fin 3) (Fin 3) ℂ,
        CStarMatrix.ofMatrix.symm ρ.val = rhoM ∧
        CStarMatrix.ofMatrix.symm σ.val = sigmaM ∧
        Pm = P ∧ K = C ∧
        Pmᴴ * Pm + Kᴴ * K = 1 ∧
        Pmᴴ * Pm ≤ 1 ∧
        traceDistance ρ σ = R.readout () () ε ∧
        (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re = ε ∧
        (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re = ε ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) = E0 ∧
        (1 / ε : ℝ) •
            (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ) = E1 ∧
        traceNorm (E0 - E1) / 2 = 1 ∧
        max ε ε * (traceNorm (
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
          (1 / ε : ℝ) • (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2) =
          traceDistance ρ σ) ∧
    ¬ ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ ρ σ : DensityState (Fin 3),
        ∀ Pm : Matrix (Fin 3) (Fin 3) ℂ,
          Pmᴴ * Pm ≤ 1 →
          0 < (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re →
          0 < (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re →
          traceNorm (
            (1 / (CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm ρ.val * Pmᴴ) -
            (1 / (CStarMatrix.ofMatrix.symm σ.val * Pmᴴ * Pm).trace.re : ℝ) •
              (Pm * CStarMatrix.ofMatrix.symm σ.val * Pmᴴ)) / 2 ≤
            f (traceDistance ρ σ)

theorem actual_law : arena.Law actual := by
  simpa [arena, actual, realize, signature] using
    rare_branch_conditional_error_sharpness

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change _ ∧ _ at h
  have hcase := h.1 (1 / 2 : ℝ) (by norm_num) (by norm_num)
  dsimp only at hcase
  obtain ⟨ρ, σ, Pm, K, _hρ, _hσ, _hP, _hK, _hinst, _hbound, hD,
    _hp, _hq, hcondρ, hcondσ, hunit, hw⟩ := hcase
  have hweight := hw
  rw [hcondρ, hcondσ, hunit, hD] at hweight
  simp [rejected, realize, signature] at hweight

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(), (1 : ℝ), (2 : ℝ), by
      change (1 : ℝ) ≠ 2
      norm_num⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ε => ε) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "RareBranchConditionalErrorSharpness") "rare_branch_conditional_error_sharpness") "Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness/Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ε => ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law

end Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness


noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.arena) (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"rare_branch_conditional_error_sharpness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.observation0 : (ε : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      (ρ σ :
          @D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        (Pm K :
            Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (ε : Real)
    (a : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (a_1 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  have C :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)));
  have E0 :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)));
  have E1 :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.basisProjector.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2)));
  have rhoM :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @ite.{1} Real
        (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) i
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
        (@ite.{1} Real
          (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) i
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1))))
          ε (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)));
  have sigmaM :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics.diagonalState.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @ite.{1} Real
        (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) i
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
        (@ite.{1} Real
          (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) i
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2))))
          ε (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)));
  have P :
    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex :=
    @HAdd.hAdd.{0, 0, 0}
      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
      (@instHAdd.{0}
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex)
        (@Matrix.add.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex Complex.instAdd))
      E0 E1;
  fun
    (ρ σ :
      @D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{0}
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (Pm K :
      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.signature
    Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.actual PUnit.unit.{1} PUnit.unit.{1} ε

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"rare_branch_conditional_error_sharpness\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness, part := .type, path := [.function, .argument, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .argument, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"rare_branch_conditional_error_sharpness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.rare_branch_conditional_error_sharpness, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).actual (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"RareBranchConditionalErrorSharpness\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness, declaration := `Reg.D5.S3.Quantum.Measurement.RareBranchConditionalErrorSharpness.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
