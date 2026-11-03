import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.LatticeModTwoTheta

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Matrix LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open _root_.D5.S3.VertexAlgebra.LatticeModTwoTheta
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.LatticeModTwoTheta

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

private theorem zeroUnit : IsUnit zeroLattice.G.det := by
  norm_num [zeroLattice]

-- The varying readout is the source's integral determinant equality.
abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
-- Genuine intervention: replace determinant equality by determinant inequality.
def rejected : Realization signature :=
  realize _ (fun _ _ x y => x ≠ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef),
    ∃ h2 : (gramReal (Gram2G D)).PosDef,
      r.readout () () D.G.det 1 ∧
      (gramReal (Gram2G D)).det = (2 : ℝ) ^ D.rank ∧
      (∀ p : Charge D,
        phi D hu (reduceCharge D p) = classOf (Gram2G D) (gramMap D p)) ∧
      (∀ p : Charge D,
        dualVector (Gram2G D) (gramMap D p) = fun i => (p i : ℚ) / 2) ∧
      (∀ a : ModTwoCharge D, -(phi D hu a) = phi D hu a) ∧
      (∀ a b : ModTwoCharge D,
        pairingCharacter (Gram2G D) h2 (phi D hu a) (-(phi D hu b)) =
          _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset.fourierSign D a b) ∧
      (∀ a : ModTwoCharge D,
        phase (quadraticClass (Gram2G D) (phi D hu a)) =
          _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset.quadraticSign D a) ∧
      (∀ a : ModTwoCharge D,
        ∃ e : Charge D ≃ {p : Charge D // reduceCharge D p = a},
          ∀ n : Charge D, (e n).val = fun i => 2 * n i + chargeLift D a i) ∧
      (∀ (τ : ℂ), 0 < τ.im → ∀ a : ModTwoCharge D,
        Summable (fun p : {p : Charge D // reduceCharge D p = a} =>
          ‖Complex.exp ((Real.pi * Complex.I * τ / 2) * (bilinear D p.val p.val : ℂ))‖) ∧
        parityTheta D a τ = sectorTheta (Gram2G D) (phi D hu a) τ ∧
        parityTheta D a (-1 / τ) = (-Complex.I * τ) ^ ((D.rank : ℂ) / 2) /
          (Real.sqrt ((2 : ℝ) ^ D.rank) : ℂ) * ∑ b : ModTwoCharge D,
            _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset.fourierSign D a b * parityTheta D b τ) ∧
      (∀ (τ : ℂ), 0 < τ.im → ∀ a : ModTwoCharge D,
        parityTheta D a (τ + 1) =
          _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset.quadraticSign D a * parityTheta D a τ)

private theorem sourceBridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeModTwoTheta.original_modTwo_theta_bridge)) ↔
      arena.Law actual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨h2, hdet, rest⟩ := h zeroLattice zeroUnit zeroPositive
  apply hdet
  norm_num [zeroLattice]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, -1, ?_⟩
  intro h
  have he : (-1 : ℤ) = 1 := Eq.mp (congrFun h 1) rfl
  omega

def family : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeModTwoTheta.original_modTwo_theta_bridge)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp original_modTwo_theta_bridge, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeModTwoTheta.original_modTwo_theta_bridge)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeModTwoTheta.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeModTwoTheta.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeModTwoTheta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.VertexAlgebra.LatticeModTwoTheta
