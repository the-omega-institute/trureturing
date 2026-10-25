import CFMPOriginalAngleWindow501Transient
import CFMPOriginalEndpointCaps460Transient
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option autoImplicit false
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (cosine)
open CFMPOriginalForward390 (angle)
open CFMPOriginalAngleWindow501Transient (adjacentSlot)
open private flat_product_bound from D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPOriginalDualWitness508Transient

def Witness (X : ℝ) : Prop := ∃ y : Fin 6 → ℝ,
  (∀ q, 1 < y q) ∧ (∀ q, -1 < rawCos y q ∧ rawCos y q < 1) ∧ y 0 = X ∧
    ((angle y 0 + angle y 1 + angle y 2 ≤ Real.pi/2 ∧
      angle y 0 + angle y 4 + angle y 5 ≤ Real.pi/2) ∨
     (angle y 0 ≤ Real.pi/5 ∧ ∃ j : Fin 4,
      (∀ i : Fin 4, i ≠ j → angle y (adjacentSlot i) ≤ Real.pi/5) ∧
      angle y (adjacentSlot j) ≤ Real.pi/3))

theorem original_common_length_dual_witness {E : Type*}
    (x : E → ℝ) (hx : ∀ e, 1 < x e) (localEdges : Fin 6 → E)
    (hw0 : Witness (x (localEdges 0))) (hw3 : Witness (x (localEdges 3))) :
    ¬ cosine (x (localEdges 0)) (x (localEdges 1)) (x (localEdges 2))
        (x (localEdges 3)) (x (localEdges 4)) (x (localEdges 5)) ≤ -1 := by
  have hshort (X : ℝ) (hw : Witness X) : X < 3 := by
    obtain ⟨y,hy,hc,he,hcap | hwindow⟩ := hw
    · have h := (CFMPOriginalEndpointCaps444Transient.original_equal_endpoint_caps
        y hy hc (Real.pi/2) hcap.1 hcap.2 le_rfl).2
      simpa only [he, Real.cos_pi_div_two, sub_zero, add_zero, div_one] using h
    · obtain ⟨h0,j,hs,hm⟩ := hwindow
      have h := CFMPOriginalAngleWindow501Transient.original_window y hy hc h0 j hs hm
      rw [he] at h
      exact h.1.trans h.2
  have h0 := hshort _ hw0
  have h3 := hshort _ hw3
  intro hflat
  have hb := flat_product_bound _ _ _ _ _ _
    (hx _) (hx _) (hx _) (hx _) (hx _) (hx _) hflat
  have hab : 1 < x (localEdges 1) * x (localEdges 2) := by
    nlinarith only [hx (localEdges 1), hx (localEdges 2),
      mul_pos (sub_pos.mpr (hx (localEdges 1))) (sub_pos.mpr (hx (localEdges 2)))]
  have habc : 1 < x (localEdges 1) * x (localEdges 2) * x (localEdges 4) := by
    nlinarith only [hab,hx (localEdges 4),mul_pos (sub_pos.mpr hab) (sub_pos.mpr (hx (localEdges 4)))]
  have habcd : 1 < x (localEdges 1) * x (localEdges 2) * x (localEdges 4) * x (localEdges 5) := by
    nlinarith only [habc,hx (localEdges 5),mul_pos (sub_pos.mpr habc) (sub_pos.mpr (hx (localEdges 5)))]
  have hs0 : (x (localEdges 0)-1)^2 < 4 := by nlinarith only [hx (localEdges 0),h0]
  have hs3 : (x (localEdges 3)-1)^2 < 4 := by nlinarith only [hx (localEdges 3),h3]
  have hu : (x (localEdges 0)-1)^2 * (x (localEdges 3)-1)^2 < 16 := calc
    _ ≤ 4 * (x (localEdges 3)-1)^2 := mul_le_mul_of_nonneg_right hs0.le (sq_nonneg _)
    _ < 16 := by nlinarith only [hs3]
  nlinarith only [hb,habcd,hu]

end CFMPOriginalDualWitness508Transient

run_cmd do
  let name := ``CFMPOriginalDualWitness508Transient.original_common_length_dual_witness
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP508 checked target missing"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP508 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP508 CHECKED {name} axioms={axioms}"
