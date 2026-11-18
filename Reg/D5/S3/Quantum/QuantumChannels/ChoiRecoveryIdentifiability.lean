import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
import D5.S3.Quantum.Foundation.FinitePreparationChannel

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
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
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law T := ∀ {d : ℕ} [NeZero d] (M N : Matrix (Q d) (Q d) ℝ) (L : ℝ)
    (hM : ∀ a x, 0 ≤ M a x) (hrow : M *ᵥ 1 = 1)
    (hcol : ∀ x, ∑ a, M a x = 1) (hNM : N * M = 1)
    (hL : ∀ a c b, N c a - N b a ≤ L)
    (R : QuantumChannel (B d) (Bout d)),
    (∀ u v, output M R u v =
      CStarMatrix.ofMatrix.symm (R.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (fun b b' => initializer M (u.1,b) (v.1,b')))) u.2 v.2) ∧
    inputMarginal (target (d := d)) = uniformInput ∧
    ((∀ x c, 0 ≤ born R x c) ∧ born R *ᵥ 1 = 1) ∧
    ((∀ x, (conditional R x).PosSemidef ∧ (conditional R x).trace = 1) ∧
      ((inputMarginal (output M R)).PosSemidef ∧
        (inputMarginal (output M R)).trace = 1) ∧
      (∀ a a' b b' c c',
        inputMarginal (output M R) (a,(b,c)) (a',(b',c')) =
          if a = a' then (1 / (d : ℂ)) * ∑ x, (M a x : ℂ) *
            ∑ bo : Q d, ∑ co : Q d,
              recovered R x ((b,bo),(c,co)) ((b',bo),(c',co)) else 0)) ∧
    (∀ a x a' x' c c',
      (∑ bi : Q d, ∑ bo : Q d, ∑ co : Q d,
        output M R ((a,x),((bi,bo),(c,co))) ((a',x'),((bi,bo),(c',co)))) =
      if a = a' ∧ x = x' then (M a x : ℂ) / d * conditional R x c c' else 0) ∧
    (T.readout () () (1 - 1 / (d : ℝ))
      (traceDistance (outputState M hM hcol R) targetState + L * inputDefect M R)) ∧
    (inputMarginal (output M R) = uniformInput →
      (∀ x, conditional R x = omega) ∧ 1 - 1 / (d : ℝ) ≤ fullError M R)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let rho : DensityState (Bout 1) := ⟨1, zero_le_one, by
    simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]⟩
  obtain ⟨R, _⟩ := finite_preparation_quantum_channel (fun _ : B 1 => rho)
  have hh := h (d := 1) 1 1 0 (by intro a x; simp only [Matrix.one_apply]; split_ifs <;> norm_num)
    (by simp) (by intro x; fin_cases x; norm_num [Matrix.one_apply, Fin.sum_univ_one]) (by simp)
    (by
      intro a c b
      have hc : c = a := Subsingleton.elim _ _
      have hb : b = a := Subsingleton.elim _ _
      simp [Matrix.one_apply, hc, hb]) R
  exact hh.2.2.2.2.2.1

def family : Registration arena (type_of% (@arbitrary_cptp_choi_bridge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@arbitrary_cptp_choi_bridge, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change ((0 : ℝ) ≤ 0) = (1 ≤ 0) at hh
    have : (1 : ℝ) ≤ 0 := Eq.mp hh (by norm_num)
    norm_num at this

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@arbitrary_cptp_choi_bridge)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Reg.D5.S3.Quantum.QuantumChannels.ChoiRecoveryIdentifiability
