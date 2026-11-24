import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient

/-! Dependence of the occupation coefficients on the multinomial normalization. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open _root_.D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient
open _root_.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass (coordinateBox)
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n.factorial : ℂ) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J] {q : ℕ} [NeZero q]
      (d : ℕ) (a : J → ZMod q) (w : J → ℝ) (R : Finset (ZMod q)),
    let scale := fun n : ℕ => V.readout () () n
    let Q (k : ZMod q) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
      ∏ j, ∑ p ∈ coordinateBox d,
        AddMonoidAlgebra.single p
          ((w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) : ℝ) *
            ZMod.stdAddChar (-(((p.1 : ℤ) • a j - (p.2 : ℤ) • a j) * k)))
    (q : ℂ) * (∑ r ∈ R, (↑(∑ p ∈ (piAntidiag univ d ×ˢ piAntidiag univ d).filter
      (fun p : (J → ℕ) × (J → ℕ) =>
        (∀ j, p.1 j = 0 ∨ p.2 j = 0) ∧
        (∑ j, ((p.1 j : ℤ) • a j - (p.2 j : ℤ) • a j)) = r),
      monomialWeight w p.1 * monomialWeight w p.2) : ℂ)) =
       scale d *
        ∑ k : ZMod q, (Q k).coeff (d, d) * ∑ r ∈ R, ZMod.stdAddChar (k * r)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := law (J := ULift.{u} (Fin 0)) (q := 1) 0 (fun _ => 0) (fun _ => 0) {0}
  norm_num [rejected, realize, monomialWeight, Nat.multinomial] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 2, ?_⟩
  change (Nat.factorial 0 : ℂ) ^ 2 ≠ (Nat.factorial 2 : ℂ) ^ 2
  norm_num [Nat.factorial]

def evidence : Registration arena.{u} (type_of% @cyclic_disjoint_band_product.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_disjoint_band_product.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclic_disjoint_band_product.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n.factorial : ℂ) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient
