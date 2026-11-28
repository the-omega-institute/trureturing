import Reg.Support.PlanarThetaFoundation
import D5.S3.Fourier.HexagonalThetaStability

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.HexagonalThetaStability
noncomputable section

abbrev orbitSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def orbitActual : Realization orbitSignature :=
  realize orbitSignature (fun _ h a => orbitGap h a) (fun e => nomatch e)

def orbitRejected : Realization orbitSignature :=
  realize orbitSignature (fun _ h a => orbitGap h a - 1) (fun e => nomatch e)

def orbitArena : Arena where
  signature := orbitSignature
  Law R := ∀ {h : ℝ},
    (∀ b a : ℝ, 0 < b → b ≤ a → a / b * cubicGap h b ≤ R.readout () h a) ∧
    (∀ a : ℝ, escapeGap h a ≤ orbitGap h a)

private theorem orbit_rejected : ¬ orbitArena.Law orbitRejected := by
  intro h
  have hh := (h (h := 0)).1 1 1 (by norm_num) le_rfl
  norm_num [orbitRejected, realize, cubicGap, orbitGap, threePointGap, gapAmplitude] at hh

private theorem orbit_dependence : ObservationalDependence orbitSignature orbitActual := by
  intro i
  refine ⟨-2, 0, 1, ?_⟩
  change orbitGap (-2) 0 ≠ orbitGap (-2) 1
  norm_num [orbitGap, threePointGap, gapAmplitude]
  have he : 1 < Real.exp (2 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  linarith

def orbitRegistration : Registration orbitArena (type_of% (@orbitGap_lower)) where
  actual := orbitActual
  bridge := Iff.rfl
  variation := ⟨@orbitGap_lower, orbitRejected, orbit_rejected⟩
  sensitivity := ⟨fun i => ⟨orbitRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, orbit_rejected⟩, fun e => nomatch e⟩
  dependence := orbit_dependence

open Reg.Support.PlanarThetaFoundation

def stabilityRejected : Realization thetaSignature :=
  realize thetaSignature (fun _ p t => F t p.1 p.2 - 1) (fun e => nomatch e)

def stabilityArena : Arena where
  signature := thetaSignature
  Law R := ∀ {t x y : ℝ}, 0 < t → 0 < y →
    Summable (fun v : ℤ × ℤ =>
      orbitGap (hexGap x y) (Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) *
        Real.exp (-Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v)) ∧
    1 / 3 * ∑' v : ℤ × ℤ,
      orbitGap (hexGap x y) (Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) *
        Real.exp (-Real.pi * t * Q (1 / 2) (Real.sqrt 3 / 2) v) ≤
      R.readout () ⟨x, y⟩ t - F t (1 / 2) (Real.sqrt 3 / 2)

private theorem stability_rejected : ¬ stabilityArena.Law stabilityRejected := by
  intro h
  have hh := (h (t := 1) (x := 1 / 2) (y := Real.sqrt 3 / 2)
    (by norm_num) (by positivity)).2
  norm_num [stabilityRejected, realize, hexGap, orbitGap, threePointGap, gapAmplitude] at hh


def stabilityRegistration : Registration stabilityArena
    (type_of% (@hexagonal_theta_stability)) where
  actual := thetaActual
  bridge := Iff.rfl
  variation := ⟨@hexagonal_theta_stability, stabilityRejected, stability_rejected⟩
  sensitivity := ⟨fun i => ⟨stabilityRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, stability_rejected⟩, fun e => nomatch e⟩
  dependence := theta_dependence

abbrev hexFormSignature : Signature where
  Params := Unit
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def hexFormActual : Realization hexFormSignature :=
  realize hexFormSignature (fun _ _ v => Q (1 / 2) (Real.sqrt 3 / 2) v)
    (fun e => nomatch e)

def hexFormRejected : Realization hexFormSignature :=
  realize hexFormSignature (fun _ _ _ => 0) (fun e => nomatch e)

def turnArena : Arena where
  signature := hexFormSignature
  Law R := ∀ v : ℤ × ℤ,
    Q (1 / 2) (Real.sqrt 3 / 2) (hexTurn v) = R.readout () () v

private theorem turn_rejected : ¬ turnArena.Law hexFormRejected := by
  intro h
  have hh := h (1, 0)
  rw [hex_q_turn] at hh
  have hp : 0 < Q (1 / 2) (Real.sqrt 3 / 2) (1, 0) := by
    dsimp [Q]
    positivity
  change Q (1 / 2) (Real.sqrt 3 / 2) (1, 0) = 0 at hh
  linarith

private theorem turn_dependence : ObservationalDependence hexFormSignature hexFormActual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  change Q (1 / 2) (Real.sqrt 3 / 2) (0, 0) ≠ Q (1 / 2) (Real.sqrt 3 / 2) (1, 0)
  have hz : Q (1 / 2) (Real.sqrt 3 / 2) (0, 0) = 0 := by simp [Q]
  rw [hz]
  apply ne_of_lt
  dsimp [Q]
  positivity

def turnRegistration : Registration turnArena (type_of% (@hex_q_turn)) where
  actual := hexFormActual
  bridge := Iff.rfl
  variation := ⟨@hex_q_turn, hexFormRejected, turn_rejected⟩
  sensitivity := ⟨fun i => ⟨hexFormRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, turn_rejected⟩, fun e => nomatch e⟩
  dependence := turn_dependence

end
end Reg.Support.HexagonalThetaStability
