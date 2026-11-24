import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
import Reg.Support.DependentFamily

/-! Source-equivalence registration for the positive extension criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
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

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ),
    CoherentExtendible b L R u v w ↔
      0 ≤ b ∧ Y.readout () () (L.trace + (b : ℂ)) 1 ∧ R.trace = L.trace ∧
      (b = 0 → middleRow u v w (selectedCoupling b L R u v w) = 0) ∧
      (L - partialTraceRight
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef ∧
      (R - partialTraceLeft
        (correction b (middleRow u v w (selectedCoupling b L R u v w)))).PosSemidef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : middleRow 0 0 0 0 = 0 := by
    funext x
    rcases x with ⟨l, r⟩
    cases l <;> cases r <;> rfl
  have hleft : partialTraceRight (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceRight]
  have hright : partialTraceLeft (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceLeft]
  have he : CoherentExtendible 1 0 0 0 0 0 := (coherent_extendible_iff 1 0 0 0 0 0).mpr (by
    refine ⟨zero_le_one, by simp, rfl, 0, fun _ => hr, ?_, ?_⟩
    · simpa [hr, correction, hleft] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ))
    · simpa [hr, correction, hright] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ)))
  exact ((h 1 0 0 0 0 0).mp he).2.1

def family : Registration arena (type_of% @extendible_iff_selected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extendible_iff_selected, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extendible_iff_selected) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks.extendible_iff_selected.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace RationalCoordinates

open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension (RationalEntry rationalComplex)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word edgeTrace)


private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w : ℂ)
    (_ : ∀ i j, RationalEntry (L i j)) (_ : ∀ i j, RationalEntry (R i j))
    (_ : RationalEntry u) (_ : RationalEntry v) (_ : RationalEntry w),
    CoherentExtendible b L R u v w ↔
      ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧
        Y.readout () () ρ.trace 1 ∧ edgeTrace ρ 1 2 = coherentEdge b L u v ∧
        edgeTrace ρ 2 1 = coherentEdge b R u w ∧
        ρ (.inl 0) (.inr true) = selectedCoupling b L R u v w ∧
        ∀ i j, RationalEntry (ρ i j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext i
    rcases i with ⟨l, r⟩
    cases l <;> cases r <;> rfl
  have hleft : partialTraceRight (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceRight]
  have hright : partialTraceLeft (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceLeft]
  have he : CoherentExtendible 1 0 0 0 0 0 := (coherent_extendible_iff 1 0 0 0 0 0).mpr (by
    refine ⟨zero_le_one, by simp, rfl, 0, fun _ => hrow, ?_, ?_⟩
    · simpa [hrow, correction, hleft] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ))
    · simpa [hrow, correction, hright] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ)))
  have hq : ∀ i j, RationalEntry ((0 : Matrix Bool Bool ℂ) i j) := fun _ _ =>
    rationalComplex.zero_mem
  obtain ⟨ρ, _, hread, _⟩ := (h 1 0 0 0 0 0 hq hq
    rationalComplex.zero_mem rationalComplex.zero_mem rationalComplex.zero_mem).mp he
  exact hread

def family : Registration arena (type_of% @rational_coherent_extendible_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_coherent_extendible_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_coherent_extendible_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks.rational_coherent_extendible_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks.RationalCoordinates.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "body", "arg", "fn",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RationalCoordinates

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentDisks
