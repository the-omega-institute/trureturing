import CFMPOriginalDualWitness508Transient
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option autoImplicit false
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos rawNum leftRad rightRad)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (opposite)
open CFMPOriginalForward390 (angle)
open CFMPOriginalAngleWindow501Transient (adjacentSlot)
open CFMPOriginalDualWitness508Transient (Witness)
open private square_gap num_frame delta_frame denominator_sq denominator_pos raw_quotient
  frame_properties from D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPOriginalRelabel517Transient

theorem rawCos_frame (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q) (t j : Fin 6) :
    rawCos (x ∘ frame t) j = rawCos x (frame t j) := by
  have hy (q : Fin 6) : 1 < (x ∘ frame t) q := hx _
  have h1 := square_gap (x ∘ frame t) j
  have h2 := square_gap x (frame t j)
  simp only [num_frame,delta_frame,Function.comp_apply] at h1
  have hrad : leftRad (x ∘ frame t) j * rightRad (x ∘ frame t) j =
      leftRad x (frame t j) * rightRad x (frame t j) := by
    linarith only [h1,h2]
  have hden : Real.sqrt (leftRad (x ∘ frame t) j) * Real.sqrt (rightRad (x ∘ frame t) j) =
      Real.sqrt (leftRad x (frame t j)) * Real.sqrt (rightRad x (frame t j)) := by
    have hsq1 := denominator_sq (x ∘ frame t) hy j
    have hsq2 := denominator_sq x hx (frame t j)
    rw [hrad] at hsq1
    apply (sq_eq_sq₀ (denominator_pos (x ∘ frame t) hy j).le
      (denominator_pos x hx (frame t j)).le).mp
    exact hsq1.trans hsq2.symm
  rw [raw_quotient,raw_quotient,num_frame,hden]

theorem angle_frame (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q) (t j : Fin 6) :
    angle (x ∘ frame t) j = angle x (frame t j) := by
  exact congrArg Real.arccos (rawCos_frame x hx t j)

theorem original_window_any_target (x : Fin 6 → ℝ)
    (hx : ∀ q, 1 < x q) (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1)
    (t : Fin 6) (h0 : angle x t ≤ Real.pi/5) (j : Fin 4)
    (hs : ∀ i : Fin 4, i ≠ j → angle x (frame t (adjacentSlot i)) ≤ Real.pi/5)
    (hm : angle x (frame t (adjacentSlot j)) ≤ Real.pi/3) :
    x t < Real.sqrt ((237620:ℝ)/28431) ∧ Real.sqrt ((237620:ℝ)/28431) < 3 := by
  have hframe := (frame_properties t).1
  have hc' (q : Fin 6) : -1 < rawCos (x ∘ frame t) q ∧ rawCos (x ∘ frame t) q < 1 := by
    rw [rawCos_frame x hx t q]
    exact hc _
  have h0' : angle (x ∘ frame t) 0 ≤ Real.pi/5 := by
    rw [angle_frame x hx t 0,hframe]
    exact h0
  have hs' (i : Fin 4) (hi : i ≠ j) :
      angle (x ∘ frame t) (adjacentSlot i) ≤ Real.pi/5 := by
    rw [angle_frame x hx]
    exact hs i hi
  have hm' : angle (x ∘ frame t) (adjacentSlot j) ≤ Real.pi/3 := by
    rw [angle_frame x hx]
    exact hm
  have h := CFMPOriginalAngleWindow501Transient.original_window (x ∘ frame t)
    (fun q => hx _) hc' h0' j hs' hm'
  simpa only [Function.comp_apply,hframe] using h

theorem witness_of_actual_occurrence (y : Fin 6 → ℝ)
    (hy : ∀ q, 1 < y q) (hc : ∀ q, -1 < rawCos y q ∧ rawCos y q < 1)
    (t : Fin 6)
    (hw : (angle y t + angle y (frame t 1) + angle y (frame t 2) ≤ Real.pi/2 ∧
        angle y t + angle y (frame t 4) + angle y (frame t 5) ≤ Real.pi/2) ∨
      (angle y t ≤ Real.pi/5 ∧ ∃ j : Fin 4,
        (∀ i : Fin 4, i ≠ j → angle y (frame t (adjacentSlot i)) ≤ Real.pi/5) ∧
        angle y (frame t (adjacentSlot j)) ≤ Real.pi/3)) :
    Witness (y t) := by
  have hframe := (frame_properties t).1
  refine ⟨y ∘ frame t,(fun q => hy _),?_,?_,?_⟩
  · intro q
    rw [rawCos_frame y hy t q]
    exact hc _
  · simpa only [Function.comp_apply,hframe]
  · rcases hw with hcap | ⟨h0,j,hs,hm⟩
    · left
      simpa only [angle_frame y hy,hframe] using hcap
    · right
      refine ⟨?_,j,?_,?_⟩
      · simpa only [angle_frame y hy,hframe] using h0
      · simpa only [angle_frame y hy] using hs
      · simpa only [angle_frame y hy] using hm

theorem original_common_length_dual_witness_any_flat_slot {E : Type*}
    (x : E → ℝ) (hx : ∀ e, 1 < x e) (localEdges : Fin 6 → E) (t : Fin 6)
    (hw0 : Witness (x (localEdges t)))
    (hw3 : Witness (x (localEdges (opposite t)))) :
    ¬ rawCos (x ∘ localEdges) t ≤ -1 := by
  have hf := frame_properties t
  have h0 : Witness (x ((localEdges ∘ frame t) 0)) := by
    simpa only [Function.comp_apply,hf.1] using hw0
  have h3 : Witness (x ((localEdges ∘ frame t) 3)) := by
    simpa only [Function.comp_apply,hf.2.1] using hw3
  have h := CFMPOriginalDualWitness508Transient.original_common_length_dual_witness
    x hx (localEdges ∘ frame t) h0 h3
  simpa only [rawCos,Function.comp_apply] using h

end CFMPOriginalRelabel517Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalRelabel517Transient.rawCos_frame,
      ``CFMPOriginalRelabel517Transient.original_window_any_target,
      ``CFMPOriginalRelabel517Transient.witness_of_actual_occurrence,
      ``CFMPOriginalRelabel517Transient.original_common_length_dual_witness_any_flat_slot] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP517 target missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP517 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP517 CHECKED {name} axioms={axioms}"
