/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim; result=D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.result; claim=D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation.claim
   digest: A q-Dicke state has no closest product vector in its q-symmetric subspace. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
import D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness

/-! Ordinary product overlaps and the q-symmetric span for three qubits. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.QDickeClosestProductRefutation

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
  Submodule.span ℂ {EuclideanSpace.single (0, 0, 0) 1,
    dicke1 q, dicke2 q, EuclideanSpace.single (1, 1, 1) 1}

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
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Measurement.DelayedRemoteControlDimensionWitness.unit_coordinates a.ofLp ha

private lemma scalar_cs (x y u v : ℂ) :
    ‖x * u + y * v‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simpa [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq
      ![conj x, conj y] ![u, v]

private lemma overlap_four (a b c : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (dicke1 4) (prod a b c) =
      (4 * a 0 * b 0 * c 1 + (2 * a 0 * b 1 + a 1 * b 0) * c 0) /
        (Real.sqrt 21 : ℂ) := by
  have hd : Real.sqrt (4 + 1 + (4 : ℝ)⁻¹) = Real.sqrt 21 / 2 := by
    rw [show 4 + 1 + (4 : ℝ)⁻¹ = 21 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    norm_num
  delta dicke1 prod
  norm_num [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hd, RCLike.inner_apply, map_ofNat]
  ring

private lemma overlap_sq (a b c : EuclideanSpace ℂ (Fin 2)) :
    21 * ‖inner ℂ (dicke1 4) (prod a b c)‖ ^ 2 =
      ‖4 * a 0 * b 0 * c 1 + (2 * a 0 * b 1 + a 1 * b 0) * c 0‖ ^ 2 := by
  rw [overlap_four, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (by norm_num)]
  ring

private lemma overlap_bound (a b c : EuclideanSpace ℂ (Fin 2))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    21 * ‖inner ℂ (dicke1 4) (prod a b c)‖ ^ 2 ≤
      5 * ‖a 0‖ ^ 2 + 5 * ‖b 0‖ ^ 2 + 6 * (‖a 0‖ ^ 2 * ‖b 0‖ ^ 2) := by
  have ha' := unit_coordinates a ha
  have hb' := unit_coordinates b hb
  have hc' := unit_coordinates c hc
  have hs := scalar_cs (4 * a 0 * b 0) (2 * a 0 * b 1 + a 1 * b 0) (c 1) (c 0)
  have ht := scalar_cs 2 1 (a 0 * b 1) (a 1 * b 0)
  norm_num only [norm_mul, Complex.norm_ofNat, norm_one, one_pow, one_mul] at hs ht
  rw [show ‖c 1‖ ^ 2 + ‖c 0‖ ^ 2 = 1 by linarith, mul_one] at hs
  rw [overlap_sq]
  simp only [mul_assoc, mul_pow] at hs ht ⊢
  rw [show ‖a 1‖ ^ 2 = 1 - ‖a 0‖ ^ 2 by linarith,
    show ‖b 1‖ ^ 2 = 1 - ‖b 0‖ ^ 2 by linarith] at ht
  nlinarith

private lemma basis_attains :
    ‖inner ℂ (dicke1 4) (prod (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1))‖ ^ 2 = 16 / 21 := by
  have h := overlap_sq (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 1 1)
  norm_num [PiLp.single_apply] at h ⊢
  linarith

private lemma closest_coordinates (a b c : EuclideanSpace ℂ (Fin 2))
    (h : IsClosestProduct 4 a b c) :
    a 1 = 0 ∧ b 1 = 0 ∧ c 0 = 0 ∧ a 0 * b 0 * c 1 ≠ 0 := by
  obtain ⟨ha, hb, hc, hm⟩ := h
  have ha' := unit_coordinates a ha
  have hb' := unit_coordinates b hb
  have hc' := unit_coordinates c hc
  have hl := hm (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 1 1) (by simp only [PiLp.norm_single, norm_one])
    (by simp only [PiLp.norm_single, norm_one]) (by simp only [PiLp.norm_single, norm_one])
  have hl' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hl
  rw [basis_attains] at hl'
  have hu := overlap_bound a b c ha hb hc
  have ha0 : ‖a 0‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖a 1‖]
  have hb0 : ‖b 0‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖b 1‖]
  have hab : ‖a 0‖ ^ 2 * ‖b 0‖ ^ 2 ≤ 1 := by
    calc
      _ ≤ 1 * ‖b 0‖ ^ 2 := mul_le_mul_of_nonneg_right ha0 (sq_nonneg _)
      _ ≤ 1 := by simpa using hb0
  have hae : ‖a 0‖ ^ 2 = 1 := by nlinarith
  have hbe : ‖b 0‖ ^ 2 = 1 := by nlinarith
  have ha1 : a 1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (a 1)])
  have hb1 : b 1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (b 1)])
  have he := overlap_sq a b c
  simp only [ha1, hb1, mul_zero, zero_mul, add_zero, norm_mul, Complex.norm_ofNat,
    mul_pow, hae, hbe] at he
  have hc1 : ‖c 1‖ ^ 2 = 1 := by nlinarith [sq_nonneg ‖c 0‖]
  refine ⟨ha1, hb1, norm_eq_zero.mp (by nlinarith [norm_nonneg (c 0)]), ?_⟩
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro hz; simp [hz] at hae
    · intro hz; simp [hz] at hbe
  · intro hz; simp [hz] at hc1

private lemma span_relation (v : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2))
    (hv : v ∈ symQ 4) : v (0, 0, 1) = 2 * v (0, 1, 0) := by
  let f : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) →ₗ[ℂ] ℂ :=
    EuclideanSpace.projₗ (0, 0, 1) - (2 : ℂ) • EuclideanSpace.projₗ (0, 1, 0)
  have hs : symQ 4 ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · change (EuclideanSpace.single (0, 0, 0) (1 : ℂ)) (0, 0, 1) -
        2 * (EuclideanSpace.single (0, 0, 0) (1 : ℂ)) (0, 1, 0) = 0
      norm_num [PiLp.single_apply]
    · change dicke1 4 (0, 0, 1) - 2 * dicke1 4 (0, 1, 0) = 0
      delta dicke1
      norm_num
      ring
    · change dicke2 4 (0, 0, 1) - 2 * dicke2 4 (0, 1, 0) = 0
      delta dicke2
      norm_num
    · change (EuclideanSpace.single (1, 1, 1) (1 : ℂ)) (0, 0, 1) -
        2 * (EuclideanSpace.single (1, 1, 1) (1 : ℂ)) (0, 1, 0) = 0
      norm_num [PiLp.single_apply]
  exact sub_eq_zero.mp (hs hv)

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
