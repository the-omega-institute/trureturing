import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities

set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Lattices.Golay GolayEncoder IntegerLeech
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeInvolution Lattice.NormFourVirasoroVector
open Lattice.LeechPeirceMultiplicities

namespace Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Fin 4 → ℕ) (fun _ => (Fin 4 → ℕ) → Prop)

def actual : Realization signature := realize signature
  (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D),
      D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      (∀ b c : Charge D, (bilinear D b c : ℝ) =
        RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space)) ∧
      (∀ b : Charge D, bilinear D b b ≠ 2) ∧
      (e a : RealLeech.Space) = RealLeech.castLinear
        (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) ∧
      bilinear D a a = 4 ∧
      let U := fixedSpace D ⊓
        (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
      (∀ v ∈ U, mode D a 1 0 v ∈ U) ∧ Module.finrank ℂ U = 98580 ∧
      ∃ T : Module.End ℂ U,
        (∀ v : U, (T v : Carrier D) = mode D a 1 0 (v : Carrier D)) ∧
        LinearMap.trace ℂ U T = (8215 / 2 : ℂ) ∧
        iSupIndep (fun i : Fin 4 => U ⊓ (mode D a 1 0).eigenspace
          (![0, 1/16, 1/2, 2] i)) ∧
        (⨆ i : Fin 4, U ⊓ (mode D a 1 0).eigenspace
          (![0, 1/16, 1/2, 2] i)) = U ∧
        R.readout () ()
          (fun i : Fin 4 => Module.finrank ℂ ↥(U ⊓ (mode D a 1 0).eigenspace
            (![0, 1/16, 1/2, 2] i))) ![49152, 47104, 2323, 1]

private theorem bridge : (type_of% (@actual_leech_peirce_multiplicities)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨D, e, a, hr, hu, hpos, hp, hroot, haxis, ha, hinv, hdim,
    T, hinc, htrace, hi, hsum, hdims⟩
  exact hdims

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h (0 : Fin 4 → ℕ)
  change ((0 : Fin 4 → ℕ) = 0) = ((1 : Fin 4 → ℕ) = 0) at hh
  have hc : (1 : ℕ) = 0 := congrFun (Eq.mp hh rfl) (0 : Fin 4)
  exact Nat.one_ne_zero hc

def family : Registration arena (type_of% (@actual_leech_peirce_multiplicities)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp actual_leech_peirce_multiplicities, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_leech_peirce_multiplicities) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities.family
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
    owner := `D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "arg", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.VertexAlgebra.Lattice.LeechPeirceMultiplicities
