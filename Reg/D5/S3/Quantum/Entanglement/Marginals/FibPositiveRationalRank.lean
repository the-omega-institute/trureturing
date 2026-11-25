import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank
import Reg.Support.DependentFamily

/-! Source registration for the rational global rank bound. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank

open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor)

private def rejectAll : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (u v w : ℂ) (L R : Matrix Bool Bool ℂ), 0 < b →
    (∀ i j, RationalEntry (L i j)) → (∀ i j, RationalEntry (R i j)) →
    RationalEntry u → RationalEntry v → RationalEntry w →
    (∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ)) →
    ∃ (z : ℂ) (ρ : Matrix Word Word ℂ),
      ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      Y.readout () () ρ.rank 2 ∧ ∀ i j, RationalEntry (ρ i j)

private theorem rejected_law : ¬ arena.Law rejectAll := by
  intro h
  let L : Matrix Bool Bool ℂ := 0
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext i
    rcases i with ⟨i, j⟩
    cases i <;> cases j <;> rfl
  have hL : L = partialTraceRight (correction 1 (middleRow 0 0 0 0)) := by
    rw [hrow]
    ext i j : 1
    simp [L, partialTraceRight, correction]
  have hR : L = partialTraceLeft (correction 1 (middleRow 0 0 0 0)) := by
    rw [hrow]
    ext i j : 1
    simp [L, partialTraceLeft, correction]
  obtain ⟨_, ⟨ψ, rfl⟩, hψ⟩ :=
    (pure_coherent_iff 1 L L 0 0 0 0 one_ne_zero).1.mpr ⟨by simp [L], hL, hR⟩
  have q (i j : Bool) : RationalEntry (L i j) := rationalComplex.zero_mem
  have q0 : RationalEntry 0 := rationalComplex.zero_mem
  obtain ⟨_, _, _, _, hfalse, _⟩ :=
    h 1 0 0 0 L L zero_lt_one q q q0 q0 q0 ⟨0, ψ, hψ⟩
  exact hfalse

def family : Registration arena (type_of% @positive_rational_rank_le_two_of_pure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_rational_rank_le_two_of_pure, rejectAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejectAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact (Nat.not_succ_le_zero 0) (Eq.mp (congrFun h 0) (Nat.le_refl 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_rational_rank_le_two_of_pure) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank.rank_bound_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank
