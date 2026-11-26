import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.HardCore.FerrersResultant
import Reg.Support.SingleDependentReadout

/-! Source-bound polynomial coefficients for the Ferrers stability criterion. -/

namespace Reg.D5.S3.StatisticalMechanics.HardCore.FerrersResultant

open Finset Polynomial LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.HardCore.FerrersResultant
open _root_.D5.S3.StatisticalMechanics.HardCore.FerrersGraphCount
  (graph coeff_independencePolynomial_eq_card_indepSetFinset)
open _root_.D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
  (independencePolynomial)
open _root_.D5.S3.Analytic.Polynomial.PairSumStability (sumResultant)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℤ[X]) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ j p ↦ p.coeff j) (fun e ↦ nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ j p ↦ p.coeff j + 1) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (rowLength : Fin (k + 1) → ℕ),
    Antitone rowLength → (∀ i, 0 < rowLength i) →
    let m := rowLength 0
    let G := graph m rowLength
    let p := independencePolynomial G univ
    let d := degreeBound m rowLength
    let r := sumResultant (explicitPolynomial m rowLength)
    p = explicitPolynomial m rowLength ∧
      (∀ j : ℕ, R.readout () j p = (G.indepSetFinset j).card) ∧
      (G.indepSetFinset 0).card = 1 ∧
      (∀ j : ℕ, (G.indepSetFinset (j + 1)).card =
        m.choose (j + 1) + ∑ i, (rowExponent m rowLength i).choose j) ∧
      0 < d ∧ p.natDegree = d ∧ 0 < p.leadingCoeff ∧
      r.natDegree = d ^ 2 ∧ r.leadingCoeff = p.leadingCoeff ^ (2 * d) ∧
      ((∀ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 → z.re ≤ 0) ↔
        ∀ j : Fin (d ^ 2 + 1), 0 ≤ r.coeff j.val) ∧
      ((∀ j : Fin (d ^ 2 + 1), 0 ≤ r.coeff j.val) →
        (r.coeff 0 = 0 ↔ ∃ z : ℂ, p.eval₂ (Int.castRingHom ℂ) z = 0 ∧ z.re = 0)) ∧
      p.coeff 0 = 1

private theorem shifted_zero_ne_card {k : ℕ} (rowLength : Fin (k + 1) → ℕ) :
    let G := graph (rowLength 0) rowLength
    let p := independencePolynomial G univ
    shifted.readout () 0 p ≠ (G.indepSetFinset 0).card := by
  intro G p hbad
  have hcoeff := coeff_independencePolynomial_eq_card_indepSetFinset G 0
  change p.coeff 0 + 1 = (G.indepSetFinset 0).card at hbad
  change p.coeff 0 = (G.indepSetFinset 0).card at hcoeff
  omega

private theorem shifted_law : ¬ arena.Law shifted := by
  intro h
  let rows : Fin 1 → ℕ := fun _ ↦ 1
  have hrow : Antitone rows := fun _ _ _ ↦ le_rfl
  have hpos : ∀ i, 0 < rows i := fun _ ↦ by decide
  exact shifted_zero_ne_card rows ((h 0 rows hrow hpos).2.1 0)

private theorem single_row_coeff (m : ℕ) (hm : 0 < m) :
    (independencePolynomial (graph m (fun _ : Fin 1 ↦ m)) univ).coeff 1 = (m : ℤ) + 1 := by
  have h := result 0 (fun _ ↦ m) (fun _ _ _ ↦ le_rfl) (fun _ ↦ hm)
  rw [h.2.1 1, h.2.2.2.1 0]
  simp

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, independencePolynomial (graph 1 (fun _ : Fin 1 ↦ 1)) univ,
    independencePolynomial (graph 2 (fun _ : Fin 1 ↦ 2)) univ, ?_⟩
  change (independencePolynomial (graph 1 (fun _ : Fin 1 ↦ 1)) univ).coeff 1 ≠
    (independencePolynomial (graph 2 (fun _ : Fin 1 ↦ 2)) univ).coeff 1
  rw [single_row_coeff 1 (by decide), single_row_coeff 2 (by decide)]
  decide

def evidence : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, shifted, shifted_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted shifted_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.FerrersResultant.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HardCore.FerrersResultant.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HardCore.FerrersResultant
    definition := some {
      owner := `D5.S3.StatisticalMechanics.HardCore.FerrersResultant
      name := `D5.S3.StatisticalMechanics.HardCore.FerrersResultant.claim
      path := #[] }
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.HardCore.FerrersResultant
