import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit Complex Filter Topology
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeInvolution LatticeHalfFockChargedTensorCoefficients LatticeAllStateField
open LatticeHalfFockCharacter LatticeHalfFockGradedTrace
open _root_.D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open _root_.D5.S3.VertexAlgebra.LatticeThetaCharacter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem zeroHG : (1 : Matrix (Fin zeroLattice.rank) (Fin zeroLattice.rank) ℂ) *
    gramComplex zeroLattice = 1 := by
  ext i j
  exact Fin.elim0 i
private theorem zeroGH : gramComplex zeroLattice *
    (1 : Matrix (Fin zeroLattice.rank) (Fin zeroLattice.rank) ℂ) = 1 := by
  ext i j
  exact Fin.elim0 i
private theorem zeroPositive : Matrix.PosDef (zeroLattice.G.map (Int.cast : ℤ → ℝ)) := by
  constructor
  · ext i; exact Fin.elim0 i
  · intro x hx
    apply False.elim
    apply hx
    ext i
    exact Fin.elim0 i

abbrev equalitySignature : Signature where
  Params := Type
  State α := α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual : Realization equalitySignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def equalityRejected : Realization equalitySignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro i
  refine ⟨ℕ, 0, 1, ?_⟩
  intro h
  have he : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

abbrev finiteSignature : Signature where
  Params := Unit
  State _ := Type
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize _ (fun _ _ α => Finite α) (fun e => nomatch e)
def finiteRejected : Realization finiteSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem finiteDependence : ObservationalDependence finiteSignature finiteActual := by
  intro i
  refine ⟨(), Unit, ℕ, ?_⟩
  intro h
  haveI : Finite ℕ := Eq.mp h (show Finite Unit from inferInstance)
  exact not_finite ℕ

namespace FiniteIndex
abbrev arena : Arena where
  signature := finiteSignature
  Law a := ∀ (D : LatticeData) (C : Finset (Charge D)) (n : ℤ),
    a.readout () () (CutoffIndex D C n)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoffIndex_finite)) ↔
    arena.Law finiteActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law finiteRejected := by
  intro h
  exact h zeroLattice ∅ 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoffIndex_finite)) where
  actual := finiteActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp cutoffIndex_finite, finiteRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := finiteDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoffIndex_finite) (Realization finiteSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FiniteIndex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FiniteIndex.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature finiteActual.readout finiteActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiniteIndex


namespace DiagonalTrace
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C)
    [Fintype (CutoffIndex D C n)],
    a.readout () (ℂ) (LinearMap.trace ℂ (cutoffActualGrade D H C n)
        (thetaRestriction D H hHG hGH C n hCsym)) (∑ i : CutoffIndex D C n,
        if i.1.1 = 0 then (-1 : ℂ) ^ (occurrences D i.1.2).length else 0)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_theta_trace_neutral_sum)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  letI : Finite (CutoffIndex zeroLattice ∅ 0) := cutoffIndex_finite _ _ _
  letI : Fintype (CutoffIndex zeroLattice ∅ 0) := Fintype.ofFinite _
  exact h zeroLattice 1 zeroHG zeroGH ∅ 0 (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_theta_trace_neutral_sum)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp cutoff_theta_trace_neutral_sum, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_theta_trace_neutral_sum) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.DiagonalTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.DiagonalTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DiagonalTrace

namespace CutoffTrace
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (hCsym : ∀ a, a ∈ C → -a ∈ C) (n : ℤ),
    a.readout () (ℂ) (cutoffThetaTrace D H hHG hGH C n hCsym) (if (0 : Charge D) ∈ C then
        (if hn : 0 ≤ n then signedThetaCoefficient D n.toNat else 0)
      else 0)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_actual_theta_trace)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice 1 zeroHG zeroGH ∅ (by simp) 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_actual_theta_trace)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp cutoff_actual_theta_trace, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.cutoff_actual_theta_trace) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.CutoffTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.CutoffTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CutoffTrace

namespace NeutralTrace
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (N : ℕ),
    a.readout () (ℂ) (neutralThetaTrace D H hHG hGH N) (signedThetaCoefficient D N)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.neutral_actual_theta_trace)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice 1 zeroHG zeroGH 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.neutral_actual_theta_trace)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp neutral_actual_theta_trace, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.neutral_actual_theta_trace) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.NeutralTrace.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.NeutralTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NeutralTrace

namespace Series
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    {q : ℂ} (hq : ‖q‖ < 1),
    (∀ N : ℕ, a.readout () ℂ (neutralThetaTrace D H hHG hGH N) (signedThetaCoefficient D N)) ∧
    Summable (fun N : ℕ => ‖signedThetaCoefficient D N * q ^ N‖) ∧
    HasSum (fun N : ℕ => signedThetaCoefficient D N * q ^ N)
      (∑' d : Exponent D, signedIntegerMonomial q d)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_trace_series)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice 1 zeroHG zeroGH (q := 0) (by norm_num)).1 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_trace_series)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actual_theta_trace_series, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_trace_series) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.Series.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.Series.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Series

namespace Eta
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun N : ℕ => ‖exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (neutralThetaTrace D H hHG hGH N * exp (2 * Real.pi * I * τ) ^ N)‖) ∧
    HasSum (fun N : ℕ => exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (neutralThetaTrace D H hHG hGH N * exp (2 * Real.pi * I * τ) ^ N))
      ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ D.rank) ∧
    a.readout () ℂ (actualThetaCharacter D H hHG hGH τ)
      ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ D.rank)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_eta)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice 1 zeroHG zeroGH I (by norm_num)).2.2

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_eta)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actual_theta_character_eta, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_eta) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.Eta.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.Eta.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Eta

namespace ModularS
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (τ : ℂ) (hτ : 0 < τ.im),
    a.readout () ℂ (actualThetaCharacter D H hHG hGH (-1 / τ)) ((2 : ℂ) ^ ((D.rank : ℂ) / 2) *
        (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank) ∧
    (∀ hu : IsUnit D.G.det,
      actualInsertedCharacter D hu (LinearMap.id : Module.End ℂ (ActualGround D hu))
        (-1 / τ) = actualThetaCharacter D H hHG hGH τ ∧
      actualThetaCharacter D H hHG hGH (-1 / τ) =
        actualInsertedCharacter D hu (LinearMap.id : Module.End ℂ (ActualGround D hu)) τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_S)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice 1 zeroHG zeroGH I (by norm_num)).1

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_S)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actual_theta_character_S, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.actual_theta_character_S) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.ModularS.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.ModularS.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ModularS

namespace FullGrade
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ),
    a.readout () (Submodule ℂ (Carrier D)) ((sugawaraMode D H 0).eigenspace (n : ℂ)) (cutoffActualGrade D H (positiveChargeCutoff D hD n) n)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_grade_eq_cutoff)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice 1 zeroHG zeroGH zeroPositive 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_grade_eq_cutoff)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp positive_full_grade_eq_cutoff, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_grade_eq_cutoff) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FullGrade.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FullGrade.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FullGrade

namespace FullCharacter
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {q : ℂ} (hq : ‖q‖ < 1),
    (∀ n : ℤ, a.readout () ℂ (positiveFullThetaTrace D H hHG hGH hD n)
      (if 0 ≤ n then signedThetaCoefficient D n.toNat else 0)) ∧
    Summable (fun N : ℕ => ‖positiveFullThetaTrace D H hHG hGH hD N * q ^ N‖) ∧
    HasSum (fun N : ℕ => positiveFullThetaTrace D H hHG hGH hD N * q ^ N)
      (∑' d : Exponent D, signedIntegerMonomial q d) ∧
    (∀ (τ : ℂ) (_ : 0 < τ.im),
      Summable (fun N : ℕ => ‖exp (-2 * Real.pi * I * τ * D.rank / 24) *
        (positiveFullThetaTrace D H hHG hGH hD N * exp (2 * Real.pi * I * τ) ^ N)‖) ∧
      HasSum (fun N : ℕ => exp (-2 * Real.pi * I * τ * D.rank / 24) *
        (positiveFullThetaTrace D H hHG hGH hD N * exp (2 * Real.pi * I * τ) ^ N))
        ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ D.rank) ∧
      positiveFullThetaCharacter D H hHG hGH hD τ = actualThetaCharacter D H hHG hGH τ ∧
      positiveFullThetaCharacter D H hHG hGH hD (-1 / τ) =
        (2 : ℂ) ^ ((D.rank : ℂ) / 2) *
          (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_theta_character)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice 1 zeroHG zeroGH zeroPositive (q := 0) (by norm_num)).1 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_theta_character)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp positive_full_theta_character, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeThetaCharacter.positive_full_theta_character) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FullCharacter.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter.FullCharacter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FullCharacter


end Reg.D5.S3.VertexAlgebra.LatticeThetaCharacter
