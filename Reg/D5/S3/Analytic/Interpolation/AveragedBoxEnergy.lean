import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.AveragedBoxEnergy
import Reg.Support.DependentFamily

/-! Typed family evidence for the entire finite-type averaged energy law.
A Contract.Registration still needs exact compiled source-selection evidence. -/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AveragedBoxEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Analytic.Interpolation.AveragedBoxEnergy

abbrev Parameters := Σ ι : Type u, Fintype ι

def signature : Signature where
  Params := Parameters.{u}
  State p := (p.1 → ℝ) × (p.1 → ℂ) × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def energy (p : Parameters.{u}) (state : signature.State p) : ℝ := by
  letI : Fintype p.1 := p.2
  exact ∫ s : ℝ in Icc state.2.2 (2 * state.2.2),
    ∫ v : ℝ, Complex.normSq (boxSum state.1 state.2.1 s v)

def actual : Realization signature.{u} :=
  realize signature (fun _ p state => energy p state) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [hι : Fintype ι] (x : ι → ℝ) (c : ι → ℂ) {g a : ℝ},
    0 < g → g ≤ a → (∀ i j, i ≠ j → g ≤ |x i - x j|) →
    a * g / 16 * (∑ i, Complex.normSq (c i)) ≤ R.readout () ⟨ι, hι⟩ (x, c, a)

private theorem actual_law : arena.{u}.Law actual := by
  intro ι hι x c g a hg hga hsep
  have h := averaged_box_energy_lower_bound x c hg hga hsep
  simpa only [actual, realize, energy] using h

private theorem bridge : (type_of% @averaged_box_energy_lower_bound.{u}) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h ι hι x c g a hg hga hsep
    have hh := @h ι hι x c g a hg hga hsep
    simpa only [actual, realize, energy] using hh
  · intro h ι hι x c g a hg hga hsep
    have hh := @h ι hι x c g a hg hga hsep
    simpa only [actual, realize, energy] using hh

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} (Fin 0)) inferInstance (fun _ => 0) (fun _ => 0)
    1 1 (by norm_num) le_rfl (by intro i; exact Fin.elim0 i.down)
  simpa [rejected, realize] using hh

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let ι := ULift.{u} (Fin 1)
  let p : Parameters.{u} := ⟨ι, inferInstance⟩
  let x : ι → ℝ := fun _ => 0
  let zeroState : signature.State p := (x, (fun _ => 0), 1)
  let unitState : signature.State p := (x, (fun _ => 1), 1)
  refine ⟨p, zeroState, unitState, ?_⟩
  have hz : actual.readout i p zeroState = 0 := by
    simp [actual, realize, energy, zeroState, boxSum]
  have hb : (1 / 16 : ℝ) ≤ actual.readout i p unitState := by
    have hh := averaged_box_energy_lower_bound x (fun _ => (1 : ℂ))
      (g := 1) (a := 1) (by norm_num) le_rfl
      (by intro j k hjk; exact (hjk (Subsingleton.elim _ _)).elim)
    simpa [actual, realize, energy, unitState, p, ι] using hh
  intro he
  rw [← he, hz] at hb
  norm_num at hb

/-- The full original telescope is retained, including the empty family and
unbounded finite cardinalities. Compiled occurrence ties are a separate obligation. -/
def family : Registration arena.{u} (type_of% @averaged_box_energy_lower_bound.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

#print axioms family

end Reg.D5.S3.Analytic.Interpolation.AveragedBoxEnergy
