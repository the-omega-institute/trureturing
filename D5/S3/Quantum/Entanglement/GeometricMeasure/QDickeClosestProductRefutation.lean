/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim; result=D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result; claim=D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim
   digest: A q-Dicke state has no closest product vector in its q-symmetric subspace. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option linter.style.longLine false

/-! Ordinary product overlaps and the q-symmetric span for three qubits. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation

def dicke0 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  EuclideanSpace.single (0, 0, 0) 1

def dicke3 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  EuclideanSpace.single (1, 1, 1) 1

def dicke1 (q : ℝ) : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p =>
    (if p = (0, 0, 1) then (Real.sqrt q : ℂ)
     else if p = (0, 1, 0) then 1
     else if p = (1, 0, 0) then (Real.sqrt q : ℂ)⁻¹ else 0) /
      (Real.sqrt (q + 1 + q⁻¹) : ℂ)

def dicke2 (q : ℝ) : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p =>
    (if p = (0, 1, 1) then (Real.sqrt q : ℂ)
     else if p = (1, 0, 1) then 1
     else if p = (1, 1, 0) then (Real.sqrt q : ℂ)⁻¹ else 0) /
      (Real.sqrt (q + 1 + q⁻¹) : ℂ)

def symQ (q : ℝ) : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)) :=
  Submodule.span ℂ {dicke0, dicke1 q, dicke2 q, dicke3}

def prod (a b c : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p => a p.1 * b p.2.1 * c p.2.2

def IsClosestProduct (q : ℝ) (a b c : EuclideanSpace ℂ (Fin 2)) : Prop :=
  ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1 ∧
    ∀ a' b' c' : EuclideanSpace ℂ (Fin 2), ‖a'‖ = 1 → ‖b'‖ = 1 → ‖c'‖ = 1 →
      ‖inner ℂ (dicke1 q) (prod a' b' c')‖ ≤ ‖inner ℂ (dicke1 q) (prod a b c)‖

def claim : Prop :=
  ∀ q : ℝ, 0 < q → ∃ a b c, IsClosestProduct q a b c ∧ prod a b c ∈ symQ q

private lemma unit_coordinates (a : EuclideanSpace ℂ (Fin 2)) (ha : ‖a‖ = 1) :
    ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq a
  simpa [Fin.sum_univ_two, ha] using h.symm

private lemma scalar_cs (x y u v : ℂ) :
    ‖x * u + y * v‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have ht : ‖x * u + y * v‖ ≤ ‖x‖ * ‖u‖ + ‖y‖ * ‖v‖ := by
    simpa only [norm_mul] using norm_add_le (x * u) (y * v)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    ![‖x‖, ‖y‖] ![‖u‖, ‖v‖]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 ht |>.trans hs

private lemma overlap_four (a b c : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (dicke1 4) (prod a b c) =
      (4 * a 0 * b 0 * c 1 + (2 * a 0 * b 1 + a 1 * b 0) * c 0) /
        (Real.sqrt 21 : ℂ) := by
  sorry

private lemma overlap_bound (a b c : EuclideanSpace ℂ (Fin 2))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    21 * ‖inner ℂ (dicke1 4) (prod a b c)‖ ^ 2 ≤
      5 * ‖a 0‖ ^ 2 + 5 * ‖b 0‖ ^ 2 + 6 * (‖a 0‖ ^ 2 * ‖b 0‖ ^ 2) := by
  sorry

private lemma basis_attains :
    ‖inner ℂ (dicke1 4) (prod (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1))‖ ^ 2 = 16 / 21 := by
  sorry

private lemma closest_coordinates (a b c : EuclideanSpace ℂ (Fin 2))
    (h : IsClosestProduct 4 a b c) :
    a 1 = 0 ∧ b 1 = 0 ∧ c 0 = 0 ∧ a 0 * b 0 * c 1 ≠ 0 := by
  sorry

private lemma span_relation (v : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
    (hv : v ∈ symQ 4) : v (0, 0, 1) = 2 * v (0, 1, 0) := by
  sorry

private lemma no_closest_in_span (a b c : EuclideanSpace ℂ (Fin 2))
    (h : IsClosestProduct 4 a b c) : prod a b c ∉ symQ 4 := by
  obtain ⟨ha, hb, hc, hn⟩ := closest_coordinates a b c h
  intro hv
  have he := span_relation (prod a b c) hv
  change a 0 * b 0 * c 1 = 2 * (a 0 * b 1 * c 0) at he
  rw [hb, mul_zero, zero_mul, mul_zero] at he
  exact hn he

theorem result : ¬ claim := by
  intro h
  obtain ⟨a, b, c, hp, hs⟩ := h 4 (by norm_num)
  exact no_closest_in_span a b c hp hs

end D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation
