import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
import Reg.Support.DependentFamily

/-! Source-equivalence registration for the positive extension criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped ComplexOrder

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

private abbrev arena : Arena where
  signature := signature
  Law A := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ),
    0 < b → L.trace + (b : ℂ) = 1 → R.trace = L.trace →
    (∀ i j, RationalEntry (L i j)) → (∀ i j, RationalEntry (R i j)) →
    RationalEntry u → RationalEntry v → RationalEntry w → RationalEntry z →
    let C := correction b (middleRow u v w z)
    let X := L - partialTraceRight C
    let Y := R - partialTraceLeft C
    (∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j)) ↔
    X.PosSemidef ∧ Y.PosSemidef ∧ A.readout () () X.det Y.det ∧
      ∃ a : ℂ, RationalEntry a ∧ (Complex.normSq a : ℂ) = X.det

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let L : Matrix Bool Bool ℂ := 0
  have ht : L.trace + (1 : ℂ) = 1 := by simp [L]
  have qL (i j : Bool) : RationalEntry (L i j) := rationalComplex.zero_mem
  have q0 : RationalEntry 0 := rationalComplex.zero_mem
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext p
    rcases p with ⟨i,j⟩
    cases i <;> cases j <;> rfl
  have hX : L - partialTraceRight (correction 1 (middleRow 0 0 0 0)) = 0 := by
    rw [hrow]
    ext i j
    simp [L, partialTraceRight, correction]
  have hY : L - partialTraceLeft (correction 1 (middleRow 0 0 0 0)) = 0 := by
    rw [hrow]
    ext i j
    simp [L, partialTraceLeft, correction]
  have he := (rational_rank_le_two_at_iff 1 L L 0 0 0 0
    zero_lt_one (by simpa using ht) rfl qL qL q0 q0 q0 q0).mpr (by
      rw [hX, hY]
      exact ⟨.zero, .zero, rfl, 0, q0, by simp⟩)
  exact ((h 1 L L 0 0 0 0 zero_lt_one (by simpa using ht) rfl
    qL qL q0 q0 q0 q0).mp he).2.2.1

def family : Registration arena (type_of% @rational_rank_le_two_at_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_rank_le_two_at_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_rank_le_two_at_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank.rational_rank_le_two_at_iff.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentRank
