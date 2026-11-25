import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.QubitGibbsDeficit

/-! The scalar equality readout for the physical reducing Gibbs deficit. -/

noncomputable section
open LeanInformationAudit
open scoped CStarAlgebra BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open _root_.D5.S3.Quantum.Recovery.QubitGibbsDeficit

namespace Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] [DecidableEq E] [Nonempty E]
    (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i))
    (ρ : DensityState (Fin 2 × E)),
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    R.readout () () (m - gibbsValue B ρ)
      (conditionalLoss ρ (qubitBlockReference (blockGibbs B hB)) +
        ∑ i, (CStarMatrix.ofMatrix.symm (retainedMarginal ρ).1 i i).re * (m - g i))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let B : Fin 2 → CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  have hB (i : Fin 2) : IsSelfAdjoint (B i) := by simp [B, IsSelfAdjoint]
  exact h B hB (qubitBlockReference (blockGibbs B hB))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : ((0 : ℝ) = 0) = ((1 : ℝ) = 0) := congrFun h 0
  exact one_ne_zero (Eq.mp hh rfl)

def family : Registration arena.{u} (type_of% @reducing_qubit_gibbs_deficit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reducing_qubit_gibbs_deficit.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reducing_qubit_gibbs_deficit.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.QubitGibbsDeficit.reducing_qubit_gibbs_deficit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.QubitGibbsDeficit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Argmax

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] [DecidableEq E] [Nonempty E]
    (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i)),
    let γ := blockGibbs B hB
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    IsGreatest (Set.range (gibbsValue B)) m ∧
      (∀ i, g i = m →
        gibbsValue B (gibbsEndpoint B hB i) = m ∧
          CStarMatrix.ofMatrix.symm (retainedMarginal (gibbsEndpoint B hB i)).1 =
            Matrix.single i i 1) ∧
      ∀ ρ, let P := CStarMatrix.ofMatrix.symm (retainedMarginal ρ).1
        R.readout () () (gibbsValue B ρ) m ↔
          (∀ i, (P i i).re = 0 ∨ g i = m) ∧
          (CStarMatrix.ofMatrix.symm ρ.1 =
              retainedBlock (fun i => (P i i).re • CStarMatrix.ofMatrix.symm (γ i).1) ∨
            (γ 0 = γ 1 ∧ CStarMatrix.ofMatrix.symm ρ.1 =
              Matrix.kronecker P (CStarMatrix.ofMatrix.symm (γ 0).1)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let B : Fin 2 → CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  have hB (i : Fin 2) : IsSelfAdjoint (B i) := by simp [B, IsSelfAdjoint]
  obtain ⟨ρ, hρ⟩ := (reducing_qubit_gibbs_argmax B hB).1.1
  exact ((h B hB).2.2 ρ).mpr (((reducing_qubit_gibbs_argmax B hB).2.2 ρ).mp hρ)

def family : Registration arena.{u} (type_of% @reducing_qubit_gibbs_argmax.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reducing_qubit_gibbs_argmax.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reducing_qubit_gibbs_argmax.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.QubitGibbsDeficit.reducing_qubit_gibbs_argmax.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit.Argmax.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.QubitGibbsDeficit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Argmax

namespace SupportingLine

open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private log_reference marginal_reference block_apply block_sub from
  D5.S3.Quantum.Recovery.QubitGibbsDeficit
open private log_smul_faithful from D5.S3.Quantum.Recovery.BKMFlagRefinement

local notation "mat" => CStarMatrix.ofMatrix.symm

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] [DecidableEq E] [Nonempty E]
    (σ : DensityState (Fin 2 × E)) (Y : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (r : ℝ)
    (B : Fin 2 → CStarMatrix E E ℂ) (_hB : ∀ i, IsSelfAdjoint (B i))
    (_hred : ordinaryPetzField σ Y r = retainedBlock (fun i => mat (B i))),
    let m := max (Real.log (partitionFunction (B 0))) (Real.log (partitionFunction (B 1)))
    let z := ordinaryPetzScore σ Y
    let F := fun t ρ => t * z ρ - conditionalLoss ρ σ
    ∃ ρ : DensityState (Fin 2 × E),
      (∃ v : EuclideanSpace ℂ (Fin 2), ‖v‖ = 1 ∧
        mat (retainedMarginal ρ).1 = Matrix.vecMulVec v.ofLp (star v.ofLp)) ∧
      R.readout () () (F r ρ) m ∧ (∀ τ, F r τ ≤ m) ∧
      (∀ τ, F r τ = m → z τ ≤ z ρ) ∧
      (∀ s, F s ρ = m + (s - r) * z ρ) ∧
      ∀ C : ℝ, 0 < C → z ρ ^ 2 ≤ C * conditionalLoss ρ σ →
        ∀ s, m + (s - r) * z ρ ≤ C * s ^ 2 / 4

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := ULift.{u} Unit
  let A : Fin 2 → CStarMatrix E E ℂ := fun _ => 0
  have hA (i : Fin 2) : IsSelfAdjoint (A i) := by simp [A, IsSelfAdjoint]
  let σ := qubitBlockReference (blockGibbs A hA)
  let l := Real.log (1 / 2)
  let B : Fin 2 → CStarMatrix E E ℂ :=
    fun i => CStarMatrix.ofMatrix ((l - Real.log (partitionFunction (A i)) - l) • (1 : Matrix E E ℂ))
  have hB (i : Fin 2) : IsSelfAdjoint (B i) := by
    change IsSelfAdjoint (CStarMatrix.ofMatrixStarAlgEquiv _)
    exact ((IsSelfAdjoint.all (l - Real.log (partitionFunction (A i)) - l)).smul
      (IsSelfAdjoint.one (Matrix E E ℂ))).map CStarMatrix.ofMatrixStarAlgEquiv
  have hfield : ordinaryPetzField σ 0 0 = retainedBlock (fun i => mat (B i)) := by
    unfold ordinaryPetzField
    rw [zero_smul, add_zero, log_reference A hA, marginal_reference,
      log_smul_faithful Matrix.PosDef.one (by norm_num), CFC.log_one, add_zero]
    have hlift : (l • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ (1 : Matrix E E ℂ) =
        retainedBlock (fun _ => l • (1 : Matrix E E ℂ)) := by
      ext ⟨i, e⟩ ⟨j, f⟩
      by_cases hij : i = j <;>
        simp [Matrix.kronecker_apply, Matrix.smul_apply, Matrix.one_apply, block_apply, hij]
    change _ - ((l • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ _) = _
    rw [hlift, ← block_sub]
    apply congrArg retainedBlock
    funext i
    change (0 : Matrix E E ℂ) - (Real.log (partitionFunction (A i)) - l) • 1 - l • 1 =
      (l - Real.log (partitionFunction (A i)) - l) • 1
    rw [zero_sub, ← neg_smul, neg_sub, ← sub_smul]
  obtain ⟨ρ, _, hFalse, _⟩ := h σ 0 0 B hB hfield
  exact hFalse

def family : Registration arena.{u} (type_of% @ordinary_petz_reducing_supporting_line.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_reducing_supporting_line.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ordinary_petz_reducing_supporting_line.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.QubitGibbsDeficit.ordinary_petz_reducing_supporting_line.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit.SupportingLine.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.QubitGibbsDeficit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportingLine

end Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit
