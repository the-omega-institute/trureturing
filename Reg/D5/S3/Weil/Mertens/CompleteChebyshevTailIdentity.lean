import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
import Reg.Support.DependentFamily

/-! A source-bound audit of the complete actual Chebyshev tail identity. -/

namespace Reg.D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
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

-- One readout replaces psi in the premise, integral and endpoint term together.
def arena : Arena where
  signature := signature
  Law R := ∀ (h : IntegrableOn
      (fun u : ℝ => (R.readout () () u - u) / u ^ 2) (Ioi 1))
      {t : ℝ} (ht : 2 ≤ t),
    (∫ u in Ioi t, (R.readout () () u - u) / u ^ 2) =
      R.readout () () t / t -
        (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
          Real.log t - 1 - Real.eulerMascheroniConstant

def actual : Realization signature :=
  realize signature (fun _ _ u => Chebyshev.psi u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ u => u) (fun e => nomatch e)

private theorem prefix_two :
    (∑ n ∈ Finset.Ioc 0 ⌊(2 : ℝ)⌋₊,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) = Real.log 2 / 2 := by
  norm_num [show Finset.Ioc 0 2 = {1, 2} by decide,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : IntegrableOn (fun u : ℝ => (u - u) / u ^ 2) (Ioi 1) := by
    simp
  have ht := h hz (t := 2) (by norm_num)
  change (∫ u in Ioi (2 : ℝ), (u - u) / u ^ 2) =
    (2 : ℝ) / 2 - _ + Real.log 2 - 1 - Real.eulerMascheroniConstant at ht
  rw [prefix_two] at ht
  simp only [sub_self, zero_div, integral_zero] at ht
  have hl : Real.log 2 < 1 := by
    have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith only [hlog]
  have hg := Real.one_half_lt_eulerMascheroniConstant
  linarith

def family : Registration arena (type_of% complete_chebyshev_tail_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_chebyshev_tail_identity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change Chebyshev.psi 1 ≠ Chebyshev.psi 2
    rw [Chebyshev.psi_one]
    exact Ne.symm (by simp)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    complete_chebyshev_tail_identity
    (type_of% (realize signature
      (fun _ _ u => Chebyshev.psi u) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => Chebyshev.psi u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["domain", "fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
