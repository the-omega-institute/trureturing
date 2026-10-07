import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
open _root_.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
open _root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant

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
  realize signature (fun _ _ x => x⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law W := ∀
    {d : ℕ} (hd : 2 ≤ d) (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosDef),
    let h0 : 0 < d := by omega
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp h0
    (∀ ρ σ : DensityState (Fin d),
      W.readout () () (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ ≤
        traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ∧
      traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ≤
        (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ) ∧
      (∀ ρ : DensityState (Fin d),
        leastEigenvalue R hR = greatestEigenvalue R hR →
          conditionedState h0 R hR ρ = ρ) ∧
      IsLUB {x : ℝ | ∃ ρ σ : DensityState (Fin d),
        ρ ≠ σ ∧
          x = traceDistance (conditionedState h0 R hR ρ)
              (conditionedState h0 R hR σ) /
            traceDistance ρ σ} (greatestEigenvalue R hR / leastEigenvalue R hR)

theorem actual_law : arena.Law actual := by
  exact conditioning_trace_distance_constant

private theorem identity_extremes :
    leastEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one =
      greatestEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one := by
  let hR : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef := Matrix.PosDef.one
  have heigs : hR.isHermitian.eigenvalues = fun _ => (1 : ℝ) := by
    funext i
    have hi : hR.isHermitian.eigenvalues i ∈
        spectrum ℝ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact ⟨i, rfl⟩
    simpa only [spectrum.one_eq, Set.mem_singleton_iff] using hi
  change Finset.univ.inf' Finset.univ_nonempty hR.isHermitian.eigenvalues =
    Finset.univ.sup' Finset.univ_nonempty hR.isHermitian.eigenvalues
  rw [heigs]
  simp

private def projector (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

private theorem projector_psd (i : Fin 2) : (projector i).PosSemidef := by
  rw [projector, Matrix.single_eq_single_vecMulVec_single]
  simpa using Matrix.posSemidef_vecMulVec_self_star (Pi.single i (1 : ℂ))

private theorem projector_trace (i : Fin 2) : (projector i).trace = 1 := by
  simp [projector, Matrix.trace]

private def basisState (i : Fin 2) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (projector i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (projector_psd i).nonneg,
    projector_trace i⟩

private theorem basis_distance : traceDistance (basisState 0) (basisState 1) = 1 := by
  have hstar : (projector 0)ᴴ = projector 0 := (projector_psd 0).isHermitian.eq
  have hid : projector 0 * projector 0 = projector 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projector, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  have horth : projector 1 * projector 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projector, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]
  have hcomp : 1 - projector 0 = projector 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [projector, Matrix.single_apply, Matrix.one_apply]
  let K : Unit → Matrix (Fin 2) (Fin 2) ℂ := fun _ => projector 0
  have hB : (∑ i, (K i)ᴴ * K i) ≤ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [K, Finset.univ_unique, Finset.sum_singleton, hstar, hid]
    apply sub_nonneg.mp
    rw [hcomp]
    exact (projector_psd 1).nonneg
  have hb := (branch_conditioned_trace_distance (projector 0) (projector 1) K
    (projector_psd 0) (projector_trace 0)
    (projector_psd 1) (projector_trace 1) hB).1
  have hlower : 1 ≤ traceDistance (basisState 0) (basisState 1) := by
    change 1 ≤ traceNorm (projector 0 - projector 1) / 2
    simpa [K, hstar, hid, horth, projector_trace] using hb
  exact le_antisymm (traceDistance_le_one _ _) hlower

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfixed (ρ : DensityState (Fin 2)) :
      conditionedState (by omega) (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one ρ = ρ :=
    (conditioning_trace_distance_constant (by omega)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one).2.1 ρ identity_extremes
  have impossible := (h (d := 2) (by omega)
    (1 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.PosDef.one).1 (basisState 0) (basisState 1) |>.1
  change 2 * traceDistance (basisState 0) (basisState 1) ≤
    traceDistance (conditionedState _ _ _ (basisState 0))
      (conditionedState _ _ _ (basisState 1)) at impossible
  rw [hfixed, hfixed, basis_distance] at impossible
  norm_num at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℝ)⁻¹ ≠ 1⁻¹; norm_num⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x⁻¹) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "ConditioningTraceDistanceConstant") "conditioning_trace_distance_constant") "Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant/Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => x⁻¹) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant


noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.arena) (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"conditioning_trace_distance_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.observation0 : {d : Nat} →
  (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d) →
    (R : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
      (hR : @Matrix.PosDef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing R) →
        (ρ σ :
            @D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{0} (Fin d) (Fin.fintype d)
              (instDecidableEqFin d)) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {d : Nat} (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
    (R : Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (hR : @Matrix.PosDef.{0, 0} (Fin d) Complex Complex.instRing Complex.partialOrder Complex.instStarRing R) =>
  have h0 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d :=
    @Decidable.byContradiction
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
      fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)) =>
      @D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant._proof_1 d hd a;
  fun
    (ρ σ :
      @D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState.{0} (Fin d) (Fin.fintype d) (instDecidableEqFin d)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.signature
    Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.actual PUnit.unit.{1} PUnit.unit.{1}
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.greatestEigenvalue.{0} (Fin d) (Fin.fintype d)
        (instDecidableEqFin d)
        (@Iff.mp (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
          (Nonempty.{1} (Fin d)) (@Fin.pos_iff_nonempty d) h0)
        R hR)
      (@D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.leastEigenvalue.{0} (Fin d) (Fin.fintype d)
        (instDecidableEqFin d)
        (@Iff.mp (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d)
          (Nonempty.{1} (Fin d)) (@Fin.pos_iff_nonempty d) h0)
        R hR))

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"conditioning_trace_distance_constant\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"letBody\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant, part := .type, path := [.body, .body, .body, .body, .letBody, .function, .argument, .body, .body, .function, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"conditioning_trace_distance_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditioning_trace_distance_constant, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).actual (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ConditioningTraceDistanceConstant\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant, declaration := `Reg.D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
