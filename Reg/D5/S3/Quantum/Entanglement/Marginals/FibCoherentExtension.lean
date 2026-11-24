import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
import Reg.Support.DependentFamily

/-! Source-equivalence registration for the positive extension criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
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
      ∃ z : ℂ, (b = 0 → middleRow u v w z = 0) ∧
        (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef ∧
        (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef

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

def family : Registration arena (type_of% @coherent_extendible_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coherent_extendible_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coherent_extendible_iff) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.coherent_extendible_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
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


namespace ScalarPivot

universe u

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
  realize signature (fun _ _ lower value => lower ≤ value) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ {n : Type u} [Fintype n] (b : ℝ) (v : n → ℂ) (T : Matrix n n ℂ),
    (assemble b v T).PosSemidef ↔
      Y.readout () () 0 b ∧ (b = 0 → v = 0) ∧ (T - correction b v).PosSemidef

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero : (assemble (n := PUnit.{u+1}) 0 0 0).PosSemidef := by
    apply (block_psd 0 0 0).mpr
    simp [correction, Matrix.PosSemidef.zero]
  exact ((h 0 0 0).mp hzero).1

def family : Registration arena.{u} (type_of% @block_psd.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@block_psd.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact (not_le.mpr zero_lt_one : ¬ (1 : ℝ) ≤ 0)
      (Eq.mp (congrFun h 0) (le_refl 0))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@block_psd.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.block_psd.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.ScalarPivot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lower value => lower ≤ value)
    (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScalarPivot

namespace PureExtension

open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ) (_ : b ≠ 0),
    ((∃ ρ : Matrix Word Word ℂ,
      (∃ ψ : Word → ℂ, ρ = rankOneDensity ψ) ∧ MatchesCoherentData b L R u v w z ρ) ↔
      Y.readout () () (L.trace + (b : ℂ)) 1 ∧
        L = partialTraceRight (correction b (middleRow u v w z)) ∧
        R = partialTraceLeft (correction b (middleRow u v w z))) ∧
    (∀ (ψ : Word → ℂ) (ρ : Matrix Word Word ℂ),
      MatchesCoherentData b L R u v w z (rankOneDensity ψ) →
      ρ.PosSemidef → MatchesCoherentData b L R u v w z ρ → ρ = rankOneDensity ψ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hrow : middleRow 0 0 0 0 = 0 := by
    funext i
    rcases i with ⟨a, c⟩
    cases a <;> cases c <;> rfl
  have hleft : partialTraceRight (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceRight]
  have hright : partialTraceLeft (0 : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 0 := by
    ext i j
    simp [partialTraceLeft]
  have he := (pure_coherent_iff 1 0 0 0 0 0 0 one_ne_zero).1.mpr (by
    simp [hrow, correction, hleft, hright])
  exact ((h 1 0 0 0 0 0 0 one_ne_zero).1.mp he).1

def family : Registration arena (type_of% @pure_coherent_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pure_coherent_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pure_coherent_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.pure_coherent_iff.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.PureExtension.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PureExtension

namespace RationalCoordinates

open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension (RationalEntry rationalComplex)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word edgeTrace)


private def acceptAll : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (b : ℝ) (L R : Matrix Bool Bool ℂ) (u v w z : ℂ)
    (_ : 0 ≤ b) (_ : Y.readout () () (L.trace + (b : ℂ)) 1) (_ : R.trace = L.trace)
    (_ : b = 0 → middleRow u v w z = 0)
    (_ : (L - partialTraceRight (correction b (middleRow u v w z))).PosSemidef)
    (_ : (R - partialTraceLeft (correction b (middleRow u v w z))).PosSemidef)
    (_ : ∀ i j, RationalEntry (L i j)) (_ : ∀ i j, RationalEntry (R i j))
    (_ : RationalEntry u) (_ : RationalEntry v) (_ : RationalEntry w) (_ : RationalEntry z),
    ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ∀ i j, RationalEntry (ρ i j)

private theorem rejected_law : ¬ arena.Law acceptAll := by
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
  have hL : ((0 : Matrix Bool Bool ℂ) -
      partialTraceRight (correction 0 (middleRow 0 0 0 0))).PosSemidef := by
    simpa [hrow, correction, hleft] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ))
  have hR : ((0 : Matrix Bool Bool ℂ) -
      partialTraceLeft (correction 0 (middleRow 0 0 0 0))).PosSemidef := by
    simpa [hrow, correction, hright] using (Matrix.PosSemidef.zero (n := Bool) (R := ℂ))
  have hq : ∀ i j, RationalEntry ((0 : Matrix Bool Bool ℂ) i j) := fun _ _ =>
    rationalComplex.zero_mem
  obtain ⟨ρ, hp, hdata, _⟩ := h 0 0 0 0 0 0 0 le_rfl trivial rfl (fun _ => hrow)
    hL hR hq hq rationalComplex.zero_mem rationalComplex.zero_mem
    rationalComplex.zero_mem rationalComplex.zero_mem
  obtain ⟨ht, hl, hr, _⟩ := hdata
  have hc : CoherentExtendible 0 0 0 0 0 0 := ⟨ρ, hp, ht, hl, hr⟩
  simpa using ((coherent_extendible_iff _ _ _ _ _ _).mp hc).2.1

def family : Registration arena (type_of% @rational_extension_at) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_extension_at, acceptAll, rejected_law⟩
  sensitivity := ⟨fun i => ⟨acceptAll, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_extension_at) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.rational_extension_at.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.RationalCoordinates.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RationalCoordinates

namespace ZeroOccupation

open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

private abbrev arena : Arena where
  signature := signature
  Law Y := ∀ (L R : Matrix Bool Bool ℂ) (u v w z : ℂ),
    (∃ ψ : Word → ℂ, MatchesCoherentData 0 L R u v w z (rankOneDensity ψ)) ↔
      u = 0 ∧ v = 0 ∧ w = 0 ∧ z = 0 ∧
        L.PosSemidef ∧ R.PosSemidef ∧ Y.readout () () L.trace 1 ∧
        R.trace = 1 ∧ L.det = R.det

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let L : Matrix Bool Bool ℂ := Matrix.diagonal fun i => if i then 0 else 1
  have hL : L.PosSemidef := Matrix.PosSemidef.diagonal fun i => by
    cases i <;> simp
  have ht : L.trace = 1 := by
    simp [L, Matrix.trace, Matrix.diag_apply, Fintype.univ_bool]
  have he := (pure_coherent_zero_iff L L 0 0 0 0).mpr
    ⟨rfl, rfl, rfl, rfl, hL, hL, ht, ht, rfl⟩
  exact ((h L L 0 0 0 0).mp he).2.2.2.2.2.2.1

def family : Registration arena (type_of% @pure_coherent_zero_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pure_coherent_zero_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pure_coherent_zero_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.pure_coherent_zero_iff.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension.ZeroOccupation.family
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
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ZeroOccupation

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
