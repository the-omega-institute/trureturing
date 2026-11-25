import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
import Reg.Support.DependentFamily

/-! Registration of the rank readout for the boundary classification theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open private disk from D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
open scoped ComplexOrder

noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := Matrix Word Word ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ ρ => ρ.rank) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law AReadout := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ),
    0 < b → (∀ i j, RationalEntry (L i j)) → (∀ i j, RationalEntry (R i j)) →
    RationalEntry u → RationalEntry v → RationalEntry w →
    CoherentExtendible b L R u v w →
    let A := edgeDisk b L u v w
    let B := edgeDisk b R u w v
    (∃ (z : ℂ) (ρ : Matrix Word Word ℂ), ρ.PosSemidef ∧
      MatchesCoherentData b L R u v w z ρ ∧ AReadout.readout () () ρ ≤ 3 ∧
      (∀ i j, RationalEntry (ρ i j)) ∧
      (Complex.normSq (z - A.1) = A.2 ∨ Complex.normSq (z - B.1) = B.2)) ↔
      RationalBoundaryCriterion A.1 B.1 A.2 B.2

private theorem occupiedMiddle : CoherentExtendible 1 0 0 0 0 0 := by
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext p
    obtain ⟨i, j⟩ := p
    cases i <;> cases j <;> rfl
  have hleft : partialTraceRight (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceRight]
  have hright : partialTraceLeft (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceLeft]
  exact (coherent_extendible_iff 1 0 0 0 0 0).mpr
    ⟨zero_le_one, by simp, rfl, 0, fun _ => hrow,
      by simpa [hrow, correction, hleft] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ)),
      by simpa [hrow, correction, hright] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ))⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have q0 : RationalEntry 0 := rationalComplex.zero_mem
  have qL (i j : Bool) : RationalEntry ((0 : Matrix Bool Bool ℂ) i j) := q0
  have hzero : edgeDisk 1 0 0 0 0 = (0, 0) := by
    simp [edgeDisk, disk]
  have hcriterion : RationalBoundaryCriterion (edgeDisk 1 0 0 0 0).1 (edgeDisk 1 0 0 0 0).1
      (edgeDisk 1 0 0 0 0).2 (edgeDisk 1 0 0 0 0).2 := by
    rw [hzero]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, 0, q0, by simp⟩))
  obtain ⟨_, _, _, _, hrank, _⟩ :=
    (h 1 0 0 0 0 0 zero_lt_one qL qL q0 q0 q0 occupiedMiddle).mpr hcriterion
  change 4 ≤ 3 at hrank
  exact (by decide : ¬ (4 : ℕ) ≤ 3) hrank

def family : Registration arena (type_of% @rational_rank_three_boundary_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_rank_three_boundary_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Matrix Word Word ℂ).rank ≠ (1 : Matrix Word Word ℂ).rank
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_rank_three_boundary_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary.rational_rank_three_boundary_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ρ => ρ.rank) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "arg", "body", "arg", "body", "arg", "arg", "fn",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibRationalBoundary
