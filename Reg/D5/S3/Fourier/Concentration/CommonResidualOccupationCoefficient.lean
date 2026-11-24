import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient

/-! Dependence of the occupation coefficients on the multinomial normalization. -/

namespace Reg.D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open _root_.D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient
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
      (p h : ℕ) (a : J → ZMod q) (w : J → ℝ) (R : Finset (ZMod q)),
    let scale := fun n : ℕ => V.readout () () n
    let S := fun _ : J => range (p + 1) ×ˢ range (p + 1)
    let degree := fun (_ : J) (v : ℕ × ℕ) => (v.1, v.2, min v.1 v.2)
    let gap := fun (j : J) (v : ℕ × ℕ) => (v.1 : ℤ) • a j - (v.2 : ℤ) • a j
    let weight := fun (j : J) (v : ℕ × ℕ) =>
      w j ^ (v.1 + v.2) / ((v.1.factorial : ℝ) * (v.2.factorial : ℝ))
    let Q (k : ZMod q) : AddMonoidAlgebra ℂ (ℕ × ℕ × ℕ) :=
      ∏ j, ∑ v ∈ S j, AddMonoidAlgebra.single (degree j v)
        ((weight j v : ℂ) * ZMod.stdAddChar (-(k * gap j v)))
    (q : ℂ) * (∑ r ∈ R, (↑(∑ u ∈ (piAntidiag univ p ×ˢ piAntidiag univ p).filter
      (fun u : (J → ℕ) × (J → ℕ) => (∑ j, min (u.1 j) (u.2 j)) = h ∧
        (∑ j, ((u.1 j : ℤ) • a j - (u.2 j : ℤ) • a j)) = r),
      monomialWeight w u.1 * monomialWeight w u.2) : ℂ)) =
      scale p * ∑ k : ZMod q,
        (Q k).coeff (p, p, h) * ∑ r ∈ R, ZMod.stdAddChar (k * r)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := law (J := ULift.{u} (Fin 0)) (q := 1) 0 0 (fun _ => 0) (fun _ => 0) {0}
  norm_num [rejected, realize, monomialWeight, Nat.multinomial] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 2, ?_⟩
  change (Nat.factorial 0 : ℂ) ^ 2 ≠ (Nat.factorial 2 : ℂ) ^ 2
  norm_num [Nat.factorial]

def evidence : Registration arena.{u} (type_of% @common_residual_band.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_residual_band.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@common_residual_band.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient.evidence
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
    owner := `D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient
