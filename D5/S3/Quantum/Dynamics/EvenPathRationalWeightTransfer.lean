/- GID: D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No end transfer at time pi on rational paths with 4 mod 8 or 6, 10 mod 16 vertices. -/

/-
proof_shape: result: content; escape_witness: the public conclusion itself (the preregistered
theorem of research line #14293, node 3), produced on the live path, through the private step
no_phase_one_transfer, by D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_moments (ρ times
the middle-edge moments are the integer nodal moments C p of the two spectral classes), the
bind-only Gram identity D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_gram (hence C 0 * C
2 - C 1 ^ 2 = (2 ρ r')^2 with ρ, r' the middle weight and the next one) and nodalMoment_det_mod_four
(this integer is 3 or 2 modulo 4), ending in the contradiction that an integer which is the square
of a rational number is 0 or 1 modulo 4.
proof_shape: nodalMoment_det_mod_four: content; escape_witness: the public conclusion itself (form
2; the preregistered residue of the second Hankel determinant): for k + 1 even and k + 1 odd integer
nodes, C 0 * C 2 - C 1 ^ 2 is 3 modulo 4 when k + 1 = 2 (mod 4) and 2 modulo 4 when k + 1 = 3, 5
(mod 8), by the reduction of the nodal polynomials to X^k (X + c) and (X + 1)^k (X + 1 + d) in (ZMod
4)[X] with c^2 = d^2 = 0, the remainder coefficient modulo X^k (X + c), the reflected polynomial (1
- c X) (1 + X)^k (1 + X + d X) and the period 8 of the binomial coefficients C(k, j), j ≤ 3, modulo
4; no Mathlib or frozen declaration states it. consumer: no_phase_one_transfer.
Private helpers:
proof_shape: no_phase_one_transfer: content (escape witnesses as for result); consumer: result.
proof_shape: prod_add_mul_of_sq_zero: content (induction on a nonempty finite set); consumer:
map_nodal_of_parity.
proof_shape: map_nodal_of_parity: content (reduction modulo 4 of the nodal polynomial of integers of
one parity); consumer: nodalMoment_det_mod_four, for the even and for the odd nodes.
proof_shape: coeff_modByMonic_X_pow_mul: bind-only (monic division and degree facts, the
nilpotent ring identity and coefficient rewrites); consumer: nodalMoment_det_mod_four.
proof_shape: coeff_top_eq_coeff_reflect: bind-only (Mathlib reflection, coefficient formulas,
binomial symmetry and index normalization); consumer: nodalMoment_det_mod_four.
proof_shape: coeff_reflected: bind-only (ring and Mathlib coefficient rewrites); consumer:
nodalMoment_det_mod_four.
proof_shape: choose_add_eight: content (Vandermonde identity with 4 | C(8, i), 1 ≤ i ≤ 3); consumer:
nodalMoment_det_mod_four, through Function.Periodic.map_mod_nat.
proof_shape: det_residue: bind-only (evaluation by decide over ZMod 4 for the four residues of k
modulo 8); consumer: nodalMoment_det_mod_four.
admission_basis: escape-witness (research line #14293, node 3; partial progress on the rational
weights conjecture of arXiv:1708.03283: the conjecture is settled for n = 2m vertices with m = 2
(mod 4) or m = 3, 5 (mod 8), that is n = 4 (mod 8) and n = 6, 10 (mod 16); it remains open for n = 0
(mod 8) and n = 2, 14 (mod 16)).
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian
  statement_id sha256:2a698170a16b6888380fcc8f26eb4e7fe06d99129518c7579da37d4ef440257a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST
  statement_id sha256:757dd0796ec75540b7989b0cc8ff7b30e16f838075ebdaf9dafec9866abcd80e.
Same-delivery dependency:
  D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.reversal_invariant
  D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.no_end_transfer_of_no_phase_one
  D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.pairMoment
  D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.nodalMoment
  D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_moments
  D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments.middle_edge_gram
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: the claim quantifies over every m in three residue classes and all real weights and
potentials; the evaluation det_residue ranges over the residues of a general statement.
-/

import D5.S3.Quantum.Dynamics.OddPathRationalWeightTransfer
import D5.S3.Quantum.Dynamics.PathMiddleEdgeMoments
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.EvenPathRationalWeightTransfer

open Matrix Polynomial Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.PathMiddleVertexMoments
open D5.S3.Quantum.Dynamics.PathMiddleEdgeMoments
open D5.S3.Quantum.Dynamics.OddPathRationalWeightTransfer

section Residues

/-- If `c * c = 0`, a product of factors `y + c * e l` over a nonempty finite set is
`y ^ (n - 1) * (y + c * Σ e l)`, with `n` the number of factors. -/
private theorem prod_add_mul_of_sq_zero {ι R : Type*} [CommRing R] (y c : R) (hc : c * c = 0)
    (e : ι → R) (S : Finset ι) (hS : S.Nonempty) :
    ∏ l ∈ S, (y + c * e l) = y ^ (S.card - 1) * (y + c * ∑ l ∈ S, e l) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    obtain ⟨t, ht⟩ : ∃ t, s.card = t + 1 := ⟨s.card - 1, by have := hs.card_pos; omega⟩
    rw [Finset.prod_cons, ih, Finset.sum_cons, Finset.card_cons, ht]
    simp only [Nat.add_sub_cancel]
    linear_combination (e a * (∑ l ∈ s, e l) * y ^ t) * hc

/-- Modulo `4`, the nodal polynomial of `k + 1` integers congruent to `a` modulo `2` is
`(X - a) ^ k * (X - a + c)` with `c * c = 0`. -/
private theorem map_nodal_of_parity {ι : Type*} (z : ι → ℤ) (S : Finset ι) (k : ℕ) (a : ℤ)
    (hS : S.card = k + 1) (hz : ∀ l ∈ S, (2 : ℤ) ∣ z l - a) :
    ∃ c : ZMod 4, c * c = 0 ∧
      (∏ l ∈ S, (X - C (z l))).map (Int.castRingHom (ZMod 4)) =
        (X - C (a : ZMod 4)) ^ k * (X - C (a : ZMod 4) + C c) := by
  have h22 : (C (2 : ZMod 4) : (ZMod 4)[X]) * C 2 = 0 := by
    rw [← C_mul, show (2 : ZMod 4) * 2 = 0 from by decide, C_0]
  have h4 : ∀ s : ZMod 4, 2 * s * (2 * s) = 0 := by decide
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hz' : ∀ l ∈ S, ∃ μ : ℤ, z l = a + 2 * μ := fun l hl => by
    obtain ⟨μ, hμ⟩ := hz l hl
    exact ⟨μ, by linarith⟩
  choose! μ hμ using hz'
  have hfac : ∀ l ∈ S, (X - C (z l)).map (Int.castRingHom (ZMod 4)) =
      X - C (a : ZMod 4) + C 2 * C (-(μ l : ZMod 4)) := by
    intro l hl
    rw [Polynomial.map_sub, map_X, map_C, eq_intCast, hμ l hl, ← C_mul, sub_add, ← C_sub]
    congr 2
    push_cast
    ring
  refine ⟨2 * ∑ l ∈ S, -(μ l : ZMod 4), h4 _, ?_⟩
  rw [Polynomial.map_prod, Finset.prod_congr rfl hfac,
    prod_add_mul_of_sq_zero (X - C (a : ZMod 4)) (C 2) h22 _ S hne, hS, Nat.add_sub_cancel, C_mul,
    map_sum]

/-- If `c * c = 0`, the coefficient of degree `k` of the remainder of `g` modulo
`X ^ k * (X + c)` is the coefficient of degree `k + 1` of `(X - c) * g`. -/
private theorem coeff_modByMonic_X_pow_mul {R : Type*} [CommRing R] (k : ℕ) (c : R)
    (hc : c * c = 0) (g : R[X]) :
    (g %ₘ (X ^ k * (X + C c))).coeff k = ((X - C c) * g).coeff (k + 1) := by
  nontriviality R
  have hPm : (X ^ k * (X + C c) : R[X]).Monic := (monic_X_pow k).mul (monic_X_add_C c)
  have hkill : (X - C c) * (X ^ k * (X + C c)) = X ^ (k + 2) := by
    have hcc : (C c : R[X]) * C c = 0 := by rw [← C_mul, hc, C_0]
    linear_combination (-(X : R[X]) ^ k) * hcc
  have hdeg : (g %ₘ (X ^ k * (X + C c))).coeff (k + 1) = 0 := by
    refine coeff_eq_zero_of_degree_lt ?_
    calc (g %ₘ (X ^ k * (X + C c))).degree < (X ^ k * (X + C c)).degree :=
          degree_modByMonic_lt _ hPm
      _ = ((k + 1 : ℕ) : WithBot ℕ) := by
        rw [degree_eq_natDegree hPm.ne_zero, (monic_X_pow k).natDegree_mul (monic_X_add_C c),
          natDegree_X_pow, natDegree_X_add_C]
  have h1 : ((X - C c) * (g %ₘ (X ^ k * (X + C c)))).coeff (k + 1) =
      (g %ₘ (X ^ k * (X + C c))).coeff k := by
    rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, hdeg, mul_zero, sub_zero]
  have h2 : ((X - C c) * (X ^ k * (X + C c) * (g /ₘ (X ^ k * (X + C c))))).coeff (k + 1) = 0 := by
    rw [← mul_assoc, hkill, coeff_X_pow_mul', if_neg (by omega)]
  have h3 : ((X - C c) * g).coeff (k + 1) =
      ((X - C c) * (g %ₘ (X ^ k * (X + C c)))).coeff (k + 1) +
        ((X - C c) * (X ^ k * (X + C c) * (g /ₘ (X ^ k * (X + C c))))).coeff (k + 1) := by
    rw [← coeff_add, ← mul_add, modByMonic_add_div]
  rw [h3, h1, h2, add_zero]

/-- The coefficient of degree `k + 1` of `(X - c) * X ^ p * (X + 1) ^ k * (X + 1 + d)` is the
coefficient of degree `p + 1` of the reflected polynomial
`(1 - c X) * (X + 1) ^ k * (1 + X + d X)`. -/
private theorem coeff_top_eq_coeff_reflect {R : Type*} [CommRing R] (k p : ℕ) (hp : p ≤ k + 1)
    (c d : R) :
    ((X - C c) * (X ^ p * ((X + 1) ^ k * (X + 1 + C d)))).coeff (k + 1) =
      ((1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X))).coeff (p + 1) := by
  have hpal : reflect k ((X + 1 : R[X]) ^ k) = (X + 1) ^ k := by
    ext i
    rw [coeff_reflect, coeff_X_add_one_pow, coeff_X_add_one_pow]
    rcases le_or_gt i k with h | h
    · rw [revAt_le h, Nat.choose_symm h]
    · rw [revAt_eq_self_of_lt h]
  have h1 : reflect 1 (X - C c : R[X]) = 1 - C c * X := by
    rw [reflect_sub, reflect_one_X, reflect_C, pow_one]
  have h2 : reflect 1 (X + 1 + C d : R[X]) = 1 + X + C d * X := by
    rw [reflect_add, reflect_add, reflect_one_X, reflect_one, reflect_C, pow_one]
  have hX1 : (X + 1 : R[X]).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le natDegree_X_le (by rw [natDegree_one]; exact Nat.zero_le 1)
  have hd1 : (X - C c : R[X]).natDegree ≤ 1 := natDegree_X_sub_C_le c
  have hd2 : ((X + 1 : R[X]) ^ k).natDegree ≤ k := by
    have h := natDegree_pow_le_of_le k hX1
    rwa [mul_one] at h
  have hd3 : (X + 1 + C d : R[X]).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le hX1 (by rw [natDegree_C]; exact Nat.zero_le 1)
  have hrefl : reflect (1 + (k + 1)) ((X - C c) * ((X + 1) ^ k * (X + 1 + C d))) =
      (1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X)) := by
    rw [reflect_mul _ _ hd1 (natDegree_mul_le_of_le hd2 hd3), reflect_mul _ _ hd2 hd3, h1, hpal,
      h2]
  rw [← hrefl, coeff_reflect, revAt_le (by omega), mul_left_comm (X - C c) (X ^ p),
    coeff_X_pow_mul', if_pos hp]
  congr 1
  omega

/-- The coefficients of degrees `1` and `j + 2` of `(1 - c X) * (X + 1) ^ k * (1 + X + d X)`. -/
private theorem coeff_reflected {R : Type*} [CommRing R] (k : ℕ) (c d : R) :
    (∀ j : ℕ, ((1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X))).coeff (j + 2) =
        (k.choose (j + 2) : R) + (1 + d - c) * (k.choose (j + 1) : R) -
          c * (1 + d) * (k.choose j : R)) ∧
      ((1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X))).coeff 1 =
        (k.choose 1 : R) + (1 + d - c) * (k.choose 0 : R) := by
  have hexp : (1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X)) =
      (X + 1) ^ k + C (1 + d - c) * (X * (X + 1) ^ k) -
        C (c * (1 + d)) * (X ^ 2 * (X + 1) ^ k) := by
    simp only [C_add, C_sub, C_mul, C_1]
    ring
  rw [hexp]
  refine ⟨fun j => ?_, ?_⟩
  · rw [coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul,
      coeff_X_add_one_pow, coeff_X_add_one_pow, coeff_X_add_one_pow]
  · rw [coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul',
      if_neg (by norm_num), mul_zero, sub_zero, coeff_X_add_one_pow, coeff_X_add_one_pow]

/-- Modulo `4`, the binomial coefficients `C(n, j)` with `j ≤ 3` have period `8` in `n`. -/
private theorem choose_add_eight (n j : ℕ) (hj : j ≤ 3) :
    (((n + 8).choose j : ℕ) : ZMod 4) = ((n.choose j : ℕ) : ZMod 4) := by
  have h8 : ∀ i : ℕ, i ≤ 3 → i ≠ 0 → (((8).choose i : ℕ) : ZMod 4) = 0 := by
    intro i hi h0
    interval_cases i
    · exact absurd rfl h0
    all_goals decide
  rw [Nat.add_choose_eq, Nat.cast_sum, Finset.sum_eq_single (j, 0)]
  · simp
  · rintro ⟨u, w⟩ huw hne
    have hsum : u + w = j := Finset.HasAntidiagonal.mem_antidiagonal.mp huw
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hsum, add_zero])
    rw [Nat.cast_mul, h8 w (by omega) hw0, mul_zero]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero j)) h

/-- The determinant of the three reflected coefficients for the four residues of `k` modulo
`8`. -/
private theorem det_residue (K : ℕ) (hK : K = 1 ∨ K = 5 ∨ K = 2 ∨ K = 4) :
    ∀ c d : ZMod 4, c * c = 0 → d * d = 0 →
      ((K.choose 1 : ZMod 4) + (1 + d - c) * (K.choose 0 : ZMod 4)) *
          ((K.choose 3 : ZMod 4) + (1 + d - c) * (K.choose 2 : ZMod 4) -
            c * (1 + d) * (K.choose 1 : ZMod 4)) -
        ((K.choose 2 : ZMod 4) + (1 + d - c) * (K.choose 1 : ZMod 4) -
          c * (1 + d) * (K.choose 0 : ZMod 4)) ^ 2 = if K % 4 = 1 then 3 else 2 := by
  rcases hK with rfl | rfl | rfl | rfl <;> decide

/-- **Residue modulo `4` of the second Hankel determinant of the nodal moments.** Let `z` be
integers, even on a set `A` of `k + 1` indices and odd on a set `B` of `k + 1` indices, and let
`C p` be the nodal moments of `A` against `B`. If `k + 1 ≡ 2 (mod 4)` then
`C 0 * C 2 - C 1 ^ 2 ≡ 3 (mod 4)`, and if `k + 1 ≡ 3, 5 (mod 8)` then
`C 0 * C 2 - C 1 ^ 2 ≡ 2 (mod 4)`. -/
theorem nodalMoment_det_mod_four {ι : Type*} (z : ι → ℤ) (A B : Finset ι) (k : ℕ)
    (hA : A.card = k + 1) (hB : B.card = k + 1) (heven : ∀ l ∈ A, Even (z l))
    (hodd : ∀ l ∈ B, Odd (z l))
    (hk : (k + 1) % 4 = 2 ∨ (k + 1) % 8 = 3 ∨ (k + 1) % 8 = 5) :
    ((nodalMoment z A B k 0 * nodalMoment z A B k 2 - nodalMoment z A B k 1 ^ 2 : ℤ) : ZMod 4) =
      if (k + 1) % 4 = 2 then 3 else 2 := by
  have hPAm : (∏ l ∈ A, (X - C (z l))).Monic :=
    monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  obtain ⟨c, hc, hmapA⟩ := map_nodal_of_parity z A k 0 hA fun l hl => by
    rw [sub_zero]
    exact even_iff_two_dvd.mp (heven l hl)
  obtain ⟨d, hd, hmapB⟩ := map_nodal_of_parity z B k (-1) hB fun l hl => by
    rw [sub_neg_eq_add]
    exact even_iff_two_dvd.mp (hodd l hl).add_one
  rw [Int.cast_zero, C_0, sub_zero] at hmapA
  rw [Int.cast_neg, Int.cast_one, C_neg, C_1, sub_neg_eq_add] at hmapB
  have hmom : ∀ p ≤ 2, ((nodalMoment z A B k p : ℤ) : ZMod 4) =
      ((1 - C c * X) * ((X + 1) ^ k * (1 + X + C d * X))).coeff (p + 1) := by
    intro p hp
    unfold nodalMoment
    rw [← eq_intCast (Int.castRingHom (ZMod 4)), ← coeff_map, map_modByMonic _ hPAm, hmapA,
      Polynomial.map_mul, Polynomial.map_pow, map_X, hmapB, coeff_modByMonic_X_pow_mul k c hc,
      coeff_top_eq_coeff_reflect k p (by omega) c d]
  obtain ⟨hGj, hG1⟩ := coeff_reflected k c d
  have h0 := (hmom 0 (by norm_num)).trans hG1
  have h1 := (hmom 1 (by norm_num)).trans (hGj 0)
  have h2 := (hmom 2 (by norm_num)).trans (hGj 1)
  have hper : ∀ j ≤ 3, ((k.choose j : ℕ) : ZMod 4) = (((k % 8).choose j : ℕ) : ZMod 4) :=
    fun j hj => (Function.Periodic.map_mod_nat (f := fun n => ((n.choose j : ℕ) : ZMod 4))
      (fun n => choose_add_eight n j hj) k).symm
  have hk8 : k % 8 = 1 ∨ k % 8 = 5 ∨ k % 8 = 2 ∨ k % 8 = 4 := by omega
  rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, h0, h1, h2, hper 0 (by norm_num),
    hper 1 (by norm_num), hper 2 (by norm_num), hper 3 (by norm_num),
    det_residue (k % 8) hk8 c d hc hd]
  exact if_congr (by omega) rfl rfl

end Residues

/-- **Rational weights rule out perfect state transfer at time `π` on paths with `2m` vertices,
`m ≡ 2 (mod 4)` or `m ≡ 3, 5 (mod 8)`.** For such `m ≥ 2`, a path on `2m` vertices with positive
rational edge weights and arbitrary real potentials has no perfect state transfer between its end
vertices at time `π`. -/
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m → (m % 4 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5) →
    ∀ (r : Fin (2 * m - 1) → ℝ) (q : Fin (2 * m - 1 + 1) → ℝ),
      (∀ j, ∃ x : ℚ, r j = x) → (∀ j, 0 < r j) →
        ¬ HasPST (pathHamiltonian r q) Real.pi 0 (Fin.last (2 * m - 1)) ∧
          ¬ HasPST (pathHamiltonian r q) Real.pi (Fin.last (2 * m - 1)) 0

/-- On a path with `2k + 2` vertices, `k + 1 ≡ 2 (mod 4)` or `k + 1 ≡ 3, 5 (mod 8)`, and positive
rational weights, the propagator at time `π` does not have the entry `1` at the last and first
vertices. -/
private theorem no_phase_one_transfer {n k : ℕ} (hn : n = 2 * k + 1)
    (hk : (k + 1) % 4 = 2 ∨ (k + 1) % 8 = 3 ∨ (k + 1) % 8 = 5) (r : Fin n → ℝ)
    (q : Fin (n + 1) → ℝ) (hrat : ∀ j, ∃ x : ℚ, r j = x) (hpos : ∀ j, 0 < r j) :
    hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last n) 0 ≠ 1 := by
  subst hn
  intro hU
  have hk1 : 1 ≤ k := by omega
  obtain ⟨z, A, hA, hB, hzA, hzB, hmom⟩ :=
    middle_edge_moments r q hpos hU ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl rfl ⟨k, by omega⟩ rfl
  have hgram := middle_edge_gram r q (reversal_invariant r q hpos hU) ⟨k, by omega⟩
    ⟨k + 1, by omega⟩ rfl rfl ⟨k + 1, by omega⟩ rfl
  have hres := nodalMoment_det_mod_four z A Aᶜ k hA hB hzA hzB hk
  obtain ⟨x, hx⟩ := hrat ⟨k, by omega⟩
  obtain ⟨y, hy⟩ := hrat ⟨k + 1, by omega⟩
  have hxc : ((x : ℚ) : ℂ) = ((r ⟨k, by omega⟩ : ℝ) : ℂ) := by rw [hx]; norm_cast
  have hyc : ((y : ℚ) : ℂ) = ((r ⟨k + 1, by omega⟩ : ℝ) : ℂ) := by rw [hy]; norm_cast
  have hD : ((nodalMoment z A Aᶜ k 0 * nodalMoment z A Aᶜ k 2 - nodalMoment z A Aᶜ k 1 ^ 2 : ℤ) :
      ℚ) = (2 * x * y) ^ 2 := by
    have h : (((nodalMoment z A Aᶜ k 0 * nodalMoment z A Aᶜ k 2 -
        nodalMoment z A Aᶜ k 1 ^ 2 : ℤ) : ℚ) : ℂ) = (((2 * x * y) ^ 2 : ℚ) : ℂ) := by
      push_cast
      rw [← hmom 0, ← hmom 1, ← hmom 2, hxc, hyc]
      linear_combination (r ⟨k, by omega⟩ : ℂ) ^ 2 * hgram
    exact_mod_cast h
  obtain ⟨t, ht⟩ : IsSquare
      (nodalMoment z A Aᶜ k 0 * nodalMoment z A Aᶜ k 2 - nodalMoment z A Aᶜ k 1 ^ 2) :=
    Rat.isSquare_intCast_iff.mp ⟨2 * x * y, by rw [hD]; ring⟩
  rw [ht, Int.cast_mul] at hres
  have hno : ∀ s : ZMod 4, s * s ≠ 3 ∧ s * s ≠ 2 := by decide
  split_ifs at hres
  · exact (hno _).1 hres
  · exact (hno _).2 hres

theorem result : claim := fun m _ hmod r q hrat hpos =>
  no_end_transfer_of_no_phase_one r
    (fun q' => no_phase_one_transfer (k := m - 1) (by omega) (by omega) r q' hrat hpos) q

end D5.S3.Quantum.Dynamics.EvenPathRationalWeightTransfer
