import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open _root_.D5.S3.Fourier.MatrixGaussian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; simp
  even_diagonal := by intros; simp

private theorem zeroPositive : (gramReal zeroLattice).PosDef := by
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

namespace Dissection
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    a.readout () ℂ (theta (gramReal D)⁻¹ τ) (∑ c : Discriminant D, sectorTheta D c τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_dissection)) ↔
    arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive Complex.I (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_dissection)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp inverse_theta_dissection, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_dissection) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Dissection.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Dissection.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
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
end Dissection

namespace ZeroS
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    a.readout () ℂ (sectorTheta D 0 (-1 / τ))
      ((-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
        (Real.sqrt (gramReal D).det : ℂ) * ∑ c : Discriminant D, sectorTheta D c τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.zero_sector_S)) ↔
    arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive Complex.I (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.zero_sector_S)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp zero_sector_S, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.zero_sector_S) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.ZeroS.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.ZeroS.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
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
end ZeroS

namespace Translation
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im),
    a.readout () ℂ (sectorTheta D c (τ+1))
      (phase (quadraticClass D c) * sectorTheta D c τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_T)) ↔
    arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive 0 Complex.I (by simp)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_T)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp sector_T, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_T) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Translation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Translation.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
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
end Translation

namespace DualRealization
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef),
    a.readout () (Submodule ℤ (Fin D.rank → ℚ))
      ((gramRat D).toBilin'.dualSubmodule (integerLattice D)) (dualLattice D) ∧
    Nat.card (Discriminant D) = D.G.det.natAbs ∧
    (Nat.card (Discriminant D) : ℝ) = (gramReal D).det ∧
    (∀ x : Fin D.rank → ℝ,
      (∀ n : Charge D, ∃ z : ℤ,
        x ⬝ᵥ gramReal D *ᵥ (fun i => (n i : ℝ)) = (z : ℝ)) ↔
      ∃ r : Charge D, shift D r = x)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.dual_lattice_realization)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice zeroPositive).1

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.dual_lattice_realization)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp dual_lattice_realization, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.dual_lattice_realization) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.DualRealization.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.DualRealization.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DualRealization

namespace Quadratic
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef),
    (∀ c d : Discriminant D,
      a.readout () QmodZ (quadraticClass D (c+d))
        (quadraticClass D c + quadraticClass D d + pairing D c d)) ∧
    (∀ (c : Discriminant D) (k : ℤ), quadraticClass D (k • c) = k^2 • quadraticClass D c) ∧
    (∀ c : Discriminant D, (∀ d, pairing D c d = 0) → c = 0) ∧
    Function.Injective phase

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.discriminant_quadratic)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice zeroPositive).1 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.discriminant_quadratic)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp discriminant_quadratic, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.discriminant_quadratic) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Quadratic.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Quadratic.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Quadratic

namespace Representative
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) (r : Charge D) (hr : classOf D r = c)
    (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun n : Charge D => ‖Complex.exp (Real.pi * Complex.I * τ *
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ))‖) ∧
    a.readout () ℂ (sectorTheta D c τ) (representativeTheta D r τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_summable_representative)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice zeroPositive 0 0 rfl Complex.I (by simp)).2

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_summable_representative)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp sector_summable_representative, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.sector_summable_representative) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Representative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Representative.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Representative

namespace Fourier
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    (∀ c : Discriminant D,
      Summable (fun k : Charge D => ‖pairingCharacter D hD c (-classOf D k) *
        Complex.exp (Real.pi * Complex.I * τ *
          (quadratic (gramReal D)⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) ∧
      a.readout () ℂ (inverseCoefficient D hD c τ) (∑ d : Discriminant D,
        pairingCharacter D hD c (-d) * sectorTheta D d τ)) ∧
    (∀ d : Discriminant D, (D.G.det.natAbs : ℂ) * sectorTheta D d τ =
      ∑ c : Discriminant D, pairingCharacter D hD c d * inverseCoefficient D hD c τ)

private theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_fourier)) ↔
    arena.Law equalityActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact ((h zeroLattice zeroPositive Complex.I (by simp)).1 0).2

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_fourier)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp inverse_theta_fourier, equalityRejected, rejectedLaw⟩
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
    (@D5.S3.VertexAlgebra.LatticeDiscriminantTheta.inverse_theta_fourier) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Fourier.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta.Fourier.family
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
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Fourier

end Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
