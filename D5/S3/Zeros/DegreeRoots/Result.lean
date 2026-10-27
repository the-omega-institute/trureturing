/- GID: D5/S3/Zeros/DegreeRoots/Result
   generality: I
   mirror-B: D5/B/S3/Zeros/DegreeRoots/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Brown and George degree roots satisfy the argument-dependent modulus bound. -/

/-
admission_basis: open-problem-resolution (#19987; Proved)
Direct frozen dependencies: none.
The definitions degreePolynomial and claim use the expressions in issue #19987.
degreePolynomial: proof_shape: bind-only; escape_witness: none; consumers: claim, inverse_degree_sum, result.
claim: proof_shape: bind-only; escape_witness: none; consumer: result.
inverse_degree_sum: proof_shape: bind-only; escape_witness: none; consumer: inverse_degree_split.
inverse_degree_split: proof_shape: bind-only; escape_witness: none; consumer: graph_exterior_bound.
degree_count_mass: proof_shape: bind-only; escape_witness: none; consumer: graph_exterior_bound.
graph_exterior_bound: proof_shape: content; escape_witness: EscapeWitness.damped_trig_bound; consumer: result.
result: proof_shape: content; escape_witness: EscapeWitness.damped_trig_bound; consumer: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20929
-/

import D5.S3.Zeros.DegreeRoots.EscapeWitness
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.DegreeRoots.Result

open scoped BigOperators
open Classical
open Polynomial
open D5.S3.Zeros.DegreeRoots.EscapeWitness

open Classical in
/-- The degree polynomial `D(G; x) = Σ_{v ∈ V(G)} x^{deg(v)}` of a graph on `n` vertices. -/
noncomputable def degreePolynomial {n : ℕ} (G : SimpleGraph (Fin n)) : ℂ[X] :=
  ∑ v, X ^ G.degree v

/-- Conjecture 4.1: every nonzero degree root `z` of a graph of order `n ≥ 1` satisfies
`‖z‖ ≤ (n − 1)^{|arg z| / π}`, with Mathlib's `Complex.arg` taking values in `(−π, π]`. -/
def claim : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (G : SimpleGraph (Fin n)) (z : ℂ), z ≠ 0 → (degreePolynomial G).eval z = 0 →
    ‖z‖ ≤ ((n : ℝ) - 1) ^ (|Complex.arg z| / Real.pi)

private lemma inverse_degree_sum {n : ℕ} (G : SimpleGraph (Fin n)) (z : ℂ)
    (hz : z ≠ 0) (hroot : (degreePolynomial G).eval z = 0) :
    ∑ v, (z⁻¹) ^ (G.maxDegree - G.degree v) = 0 := by
  have hsum : ∑ v, z ^ G.degree v = 0 := by
    simpa [degreePolynomial, Polynomial.eval_finsetSum] using hroot
  have hterm (v : Fin n) :
      (z⁻¹) ^ (G.maxDegree - G.degree v) = z ^ G.degree v * (z⁻¹) ^ G.maxDegree := by
    rw [inv_pow, inv_pow, pow_sub₀ z hz (G.degree_le_maxDegree v)]
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, zero_mul]

private lemma inverse_degree_split {n : ℕ} (G : SimpleGraph (Fin n)) (z : ℂ)
    (hz : z ≠ 0) (hroot : (degreePolynomial G).eval z = 0) :
    (((Finset.univ.filter fun v => G.degree v = G.maxDegree).card : ℕ) : ℂ) +
      ∑ v ∈ Finset.univ.filter (fun v => G.degree v ≠ G.maxDegree),
        (z⁻¹) ^ (G.maxDegree - G.degree v) = 0 := by
  have hs := inverse_degree_sum G z hz hroot
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun v => G.degree v = G.maxDegree)
    (f := fun v => (z⁻¹) ^ (G.maxDegree - G.degree v))
  have hlead : (∑ v ∈ Finset.univ.filter (fun v => G.degree v = G.maxDegree),
      (z⁻¹) ^ (G.maxDegree - G.degree v)) =
      (((Finset.univ.filter fun v => G.degree v = G.maxDegree).card : ℕ) : ℂ) := by
    calc
      _ = ∑ v ∈ Finset.univ.filter (fun v => G.degree v = G.maxDegree), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [(Finset.mem_filter.mp hv).2]
      _ = _ := by simp
  rw [hlead, hs] at hsplit
  exact hsplit

private lemma degree_count_mass {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    1 ≤ (Finset.univ.filter fun v => G.degree v = G.maxDegree).card ∧
    (Finset.univ.filter fun v => G.degree v = G.maxDegree).card +
      (Finset.univ.filter fun v => G.degree v ≠ G.maxDegree).card = n := by
  constructor
  · letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    apply Finset.one_le_card.mpr
    exact ⟨v, by simp [hv]⟩
  · simpa using Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun v => G.degree v = G.maxDegree)
      (f := fun _ => (1 : ℕ))

private lemma graph_exterior_bound {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) (z : ℂ) (hz : z ≠ 0)
    (hnorm : 1 < ‖z‖)
    (hroot : (degreePolynomial G).eval z = 0) :
    ‖z‖ ≤ ((n : ℝ) - 1) ^ (|z.arg| / Real.pi) := by
  let S := Finset.univ.filter fun v => G.degree v ≠ G.maxDegree
  let m := (Finset.univ.filter fun v => G.degree v = G.maxDegree).card
  have hcount := degree_count_mass hn G
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcount.1
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have heq : (m : ℂ) + ∑ v : S, (1 : ℂ) * (z⁻¹ ^ (G.maxDegree - G.degree v)) = 0 := by
    simp only [one_mul]
    rw [Finset.sum_coe_sort S (fun v : Fin n => z⁻¹ ^ (G.maxDegree - G.degree v))]
    exact inverse_degree_split G z hz hroot
  have hbound := normalized_escape_bound (fun _ : S => (1 : ℝ))
    (fun v : S => G.maxDegree - G.degree v) (m : ℝ) z
    (fun _ => zero_le_one) hmpos hnorm (by simpa using heq)
  have hbound' : ‖z‖ ≤ ((S.card : ℝ) / (m : ℝ)) ^ (|z.arg| / Real.pi) := by
    simpa using hbound
  have hcounts : (m : ℝ) + (S.card : ℝ) = (n : ℝ) := by exact_mod_cast hcount.2
  have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbase : 0 ≤ (n : ℝ) - 1 := by exact sub_nonneg_of_le hncast
  have hA : (S.card : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hprod : (n : ℝ) - 1 ≤ ((n : ℝ) - 1) * (m : ℝ) := by
    exact le_mul_of_one_le_right hbase hm1
  have hratio : (S.card : ℝ) / (m : ℝ) ≤ (n : ℝ) - 1 :=
    (div_le_iff₀ hmpos).2 (hA.trans hprod)
  exact hbound'.trans (Real.rpow_le_rpow
    (div_nonneg (Nat.cast_nonneg _) hmpos.le) hratio (div_nonneg (abs_nonneg _) Real.pi_pos.le))

theorem result : claim := by
  classical
  intro n hn G z hz hroot
  by_cases hnorm : ‖z‖ ≤ 1
  · by_cases hn1 : n = 1
    · subst n
      have hfalse : (1 : ℂ) = 0 := by
        simpa [degreePolynomial, Polynomial.eval_finsetSum] using hroot
      norm_num at hfalse
    · have hn2 : 2 ≤ n := by omega
      have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hbase : 1 ≤ (n : ℝ) - 1 := by linarith
      have hexp : 0 ≤ |Complex.arg z| / Real.pi := by positivity
      exact hnorm.trans (Real.one_le_rpow hbase hexp)
  · exact graph_exterior_bound hn G z hz (lt_of_not_ge hnorm) hroot

end D5.S3.Zeros.DegreeRoots.Result
