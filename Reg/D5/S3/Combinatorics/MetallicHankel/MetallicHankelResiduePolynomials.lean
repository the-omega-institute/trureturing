import D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Exact dependent-family evidence for the full metallic residue-polynomial statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials

open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries

def claimAt (n : ℕ) : Prop :=
  (∃ Φ : PowerSeries ℤ, IsMetallic n Φ) ∧
  ∀ Φ : PowerSeries ℤ, IsMetallic n Φ →
    ∀ ℓ : ℕ, n + 3 ≤ ℓ →
      let ρ : ℕ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
      ∃ Q : Fin ρ → Polynomial ℚ,
        (∀ r : Fin ρ, ∀ z : ℤ, ∃ w : ℤ,
          Polynomial.eval (z : ℚ) (Q r) = (w : ℚ)) ∧
        ∀ r : Fin ρ, ∀ m : ℕ,
          (shiftedHankel Φ ℓ (r.val + m * ρ) : ℚ) =
            Polynomial.eval (m : ℚ) (Q r)

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ n => claimAt n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n → r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hzero : ¬ claimAt 0 := by
    rintro ⟨⟨Φ, hΦ⟩, _⟩
    have hc := congrArg (constantCoeff : PowerSeries ℤ →+* ℤ) hΦ.2
    norm_num [linearCoeff, hΦ.1, map_ofNat] at hc
  apply hzero
  exact Eq.mpr h (result 1 (by omega))

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => claimAt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms result
#print axioms family
#print axioms registration

end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials
