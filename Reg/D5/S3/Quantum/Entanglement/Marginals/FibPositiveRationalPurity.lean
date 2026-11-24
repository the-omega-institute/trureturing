import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
import Reg.Support.DependentFamily

/-! Source registration for the Gaussian norm readout in the degenerate positive-occupation case. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity

open LeanInformationAudit
open Matrix Complex
open scoped ComplexOrder Matrix
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def rejectAll : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (u v w : ℂ) (L R : Matrix Bool Bool ℂ),
    0 < b → (∀ i j, RationalEntry (L i j)) → (∀ i j, RationalEntry (R i j)) →
    RationalEntry u → RationalEntry v → RationalEntry w →
    (∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ)) →
    ((∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ) ∧
      ∀ i j, RationalEntry (rankOneDensity ψ i j)) ↔
      v ≠ 0 ∨ w ≠ 0 ∨ ∃ z, RationalEntry z ∧ Y.readout () () (normSq z) (b * (L true true).re))

private theorem rejected_law : ¬ arena.Law rejectAll := by
  intro h
  let L : Matrix Bool Bool ℂ := 0
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext i
    rcases i with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  have hL : L = partialTraceRight (correction 1 (middleRow 0 0 0 0)) := by
    rw [hrow]
    ext i j : 1
    simp [L, partialTraceRight, correction, Matrix.vecMulVec_apply]
  have hR : L = partialTraceLeft (correction 1 (middleRow 0 0 0 0)) := by
    rw [hrow]
    ext i j : 1
    simp [L, partialTraceLeft, correction, Matrix.vecMulVec_apply]
  obtain ⟨ρ, ⟨ψ, rfl⟩, hψ⟩ :=
    (pure_coherent_iff 1 L L 0 0 0 0 one_ne_zero).1.mpr ⟨by simp [L], hL, hR⟩
  have ordinary : ∃ (z : ℂ) (ψ : Word → ℂ),
      MatchesCoherentData 1 L L 0 0 0 z (rankOneDensity ψ) := ⟨0, ψ, hψ⟩
  have q (i j : Bool) : RationalEntry (L i j) := rationalComplex.zero_mem
  have h0 : RationalEntry 0 := rationalComplex.zero_mem
  have positive : (0 : ℝ) < 1 := zero_lt_one
  have hQ := (positive_rational_purity_iff 1 0 0 0 L L positive q q h0 h0 h0 ordinary).mpr
    (Or.inr (Or.inr ⟨0, h0, by simp [L]⟩))
  rcases (h 1 0 0 0 L L positive q q h0 h0 h0 ordinary).mp hQ with hz | hz | ⟨_, _, hfalse⟩
  · exact hz rfl
  · exact hz rfl
  · exact hfalse

def family : Registration arena (type_of% @positive_rational_purity_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_rational_purity_iff, rejectAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejectAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_rational_purity_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity.positive_rational_purity_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
