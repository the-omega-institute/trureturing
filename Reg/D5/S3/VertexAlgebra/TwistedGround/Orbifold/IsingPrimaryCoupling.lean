import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling
import D5.S3.VertexAlgebra.Lattice.LeechFrame.ActualLeechNormFourFrame

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeInvolution (FixedCarrier fixedMode fixedVacuum fixedSpace)
open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open HalfFock.NormFourFirstGradeSpectrum (normFourFixedSource)
open TwistedGround.Orbifold.FixedSourceIsing (oddAxisMode originalI_ising_primary_selection)
open TwistedGround.OriginalFourMChargeCoset (originalI)

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

local instance (D : LatticeData) : Module ℂ (FixedCarrier D) :=
  (fixedSpace D).module

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) := (paritySpace D hu (-1)).addCommGroup

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    Module ℂ (paritySpace D hu (-1)) := (paritySpace D hu (-1)).module

private abbrev signature : Signature where
  Params := Σ D : LatticeData, FixedCarrier D →ₗ[ℂ] ℂ
  State p := FixedCarrier p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p z => p.2 z) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : LatticeData} {hu : IsUnit D.G.det}
      {hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))}
      {a : Charge D} {s : ℂ} (_ : D.rank = 24) (ell : FixedCarrier D →ₗ[ℂ] ℂ)
      {h3 : ℂ}
      (_ : ∀ z : FixedCarrier D, ell (fixedMode D (normFourFixedSource D a s) 1 z) = h3 * ell z)
      (_ : ∀ k : ℤ, k < 0 →
        ∀ z : FixedCarrier D, ell (fixedMode D (normFourFixedSource D a s) (k + 1) z) = 0)
      (_ : bilinear D a a = 4) (_ : s ^ 2 = 1)
      (n : ℤ) (u v : paritySpace D hu (-1)) {h1 h2 : ℂ}
      (_ : oddAxisMode D hu a s 0 u = h1 • u)
      (_ : oddAxisMode D hu a s 0 v = h2 • v)
      (_ : ∀ k : ℤ, 0 < k → oddAxisMode D hu a s k u = 0)
      (_ : ∀ k : ℤ, 0 < k → oddAxisMode D hu a s k v = 0)
      (_ : h1 = 0 ∨ h1 = 1/2 ∨ h1 = 1/16)
      (_ : h2 = 0 ∨ h2 = 1/2 ∨ h2 = 1/16)
      (_ : h3 = 0 ∨ h3 = 1/2 ∨ h3 = 1/16)
      (_ : R.readout () ⟨D, ell⟩ (originalI D hu hD n u v) ≠ 0),
    (h1 = 0 ∧ h3 = h2) ∨ (h2 = 0 ∧ h3 = h1) ∨
    (h1 = 1/2 ∧ h2 = 1/2 ∧ h3 = 0) ∨
    (((h1 = 1/2 ∧ h2 = 1/16) ∨ (h1 = 1/16 ∧ h2 = 1/2)) ∧ h3 = 1/16) ∨
    (h1 = 1/16 ∧ h2 = 1/16 ∧ (h3 = 0 ∨ h3 = 1/2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p : ActualLeechNormFourFrame.Index := (0, false)
  let a := ActualLeechNormFourFrame.charge p
  have ha : bilinear leechData a a = 4 := by
    simpa [a] using ActualLeechNormFourFrame.charge_pairing p p
  have bad := @law leechData leech_spec.2.1 leech_spec.2.2.1 a 1 leech_spec.1 0 (1/2)
    (by simp) (by simp) ha (by norm_num) 0 0 0 0 0
    (by simp) (by simp) (by simp) (by simp) (Or.inl rfl) (Or.inl rfl)
    (Or.inr (Or.inl rfl)) (by change (1 : ℂ) ≠ 0; exact one_ne_zero)
  norm_num at bad

def detectorFamily : Registration arena (type_of% @originalI_ising_primary_selection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@originalI_ising_primary_selection, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    have hvac : fixedVacuum leechData ≠ 0 := by
      intro he
      have hz := congrArg (fun z : FixedCarrier leechData => z.val 0) he
      simpa [fixedVacuum, LatticeAllStateField.vacuum] using hz
    obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one ℂ hvac
    refine ⟨⟨leechData, ell⟩, fixedVacuum leechData, 0, ?_⟩
    change ell (fixedVacuum leechData) ≠ ell 0
    rw [hell, map_zero]
    exact one_ne_zero

def detectorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@originalI_ising_primary_selection) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing.originalI_ising_primary_selection.__information_unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling.detectorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨detectorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => p.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.Orbifold.IsingPrimaryCoupling
