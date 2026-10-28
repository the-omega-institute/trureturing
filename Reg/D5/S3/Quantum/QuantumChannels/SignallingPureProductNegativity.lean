import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
import Reg.Support.DependentFamily

/-! Source-bound audit of strict positivity of pure-product PDM negativity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity

open _root_.D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation (matrixAction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u₁ u₂ u₃ u₄

/-- Observe the strict order relation between zero and the PDM negativity. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Every source binder and both unit-vector constraints remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α₁ : Type u₁} {β₁ : Type u₂} {α₂ : Type u₃} {β₂ : Type u₄}
    [Fintype α₁] [DecidableEq α₁] [Fintype β₁] [DecidableEq β₁]
    [Fintype α₂] [DecidableEq α₂] [Fintype β₂] [DecidableEq β₂]
    [Nonempty α₁] [Nonempty β₁] [Nonempty α₂] [Nonempty β₂]
    (p : QuantumChannel (α₁ × β₁) (α₂ × β₂)) (_hp : IsSignallingBA p),
    ∃ (a : α₁ → ℂ) (b : β₁ → ℂ), star a ⬝ᵥ a = 1 ∧ star b ⬝ᵥ b = 1 ∧
      R.readout () () 0 (traceNorm (pdmBA p a b)ᴴ - 1)

private theorem sum_ulift.{v,w} {n : Type v} [Fintype n] (f : ULift.{w} n → ℂ) :
    (∑ i, f i) = ∑ i, f (ULift.up i) :=
  ((Equiv.ulift : ULift.{w} n ≃ n).symm.sum_comp f).symm

/-- Moving a classical bit from B to A cannot factor through the input A marginal. -/
private theorem exists_signalling :
    ∃ p : QuantumChannel
      (ULift.{u₁} Unit × ULift.{u₂} (Fin 2))
      (ULift.{u₃} (Fin 2) × ULift.{u₄} Unit), IsSignallingBA p := by
  let V : Matrix (ULift.{u₃} (Fin 2) × ULift.{u₄} Unit)
      (ULift.{u₁} Unit × ULift.{u₂} (Fin 2)) ℂ :=
    fun i j => if i.1.down = j.2.down then 1 else 0
  have hV : Vᴴ * V = 1 := by
    ext ⟨⟨⟩, ⟨i⟩⟩ ⟨⟨⟩, ⟨j⟩⟩
    fin_cases i <;> fin_cases j <;>
      simp [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, sum_ulift, Fin.sum_univ_two]
  obtain ⟨p, hp⟩ := finite_kraus_quantum_channel (fun _ : Unit => V)
    (by simpa using hV)
  have haction (X : Matrix (ULift.{u₁} Unit × ULift.{u₂} (Fin 2)) _ ℂ) :
      matrixAction p.toCompletelyPositiveMap X = V * X * Vᴴ := by
    change CStarMatrix.ofMatrix.symm
      (p.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
    simpa using hp X
  refine ⟨p, ?_⟩
  rintro ⟨t, ht⟩
  let X₀ : Matrix (ULift.{u₁} Unit × ULift.{u₂} (Fin 2)) _ ℂ :=
    single (ULift.up (), ULift.up (0 : Fin 2)) (ULift.up (), ULift.up (0 : Fin 2)) 1
  let X₁ : Matrix (ULift.{u₁} Unit × ULift.{u₂} (Fin 2)) _ ℂ :=
    single (ULift.up (), ULift.up (1 : Fin 2)) (ULift.up (), ULift.up (1 : Fin 2)) 1
  have hm : partialTraceRight X₀ = partialTraceRight X₁ := by
    ext ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [X₀, X₁, partialTraceRight, Matrix.single_apply]
  have he := (ht X₀).trans ((congrArg (matrixAction t.toCompletelyPositiveMap) hm).trans
    (ht X₁).symm)
  rw [haction, haction] at he
  have hentry := congrArg (fun M => M ⟨0⟩ ⟨0⟩) he
  norm_num [partialTraceRight, V, X₀, X₁, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply,
    Fintype.sum_prod_type, sum_ulift, Fin.sum_univ_two] at hentry

private theorem rejected_law : ¬ arena.{u₁,u₂,u₃,u₄}.Law rejected := by
  intro h
  obtain ⟨p, hp⟩ := exists_signalling.{u₁,u₂,u₃,u₄}
  obtain ⟨a, b, _, _, hfalse⟩ := h p hp
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  have hpos : (0 : ℝ) < 1 := by norm_num
  exact (lt_irrefl (1 : ℝ)) (Eq.mp he hpos)

def source_registration : Registration arena.{u₁,u₂,u₃,u₄}
    (type_of% (@result.{u₁,u₂,u₃,u₄})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result.{u₁,u₂,u₃,u₄}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.SignallingPureProductNegativity
