/- GID: D5/S3/Zeros/LeeYang/TreePairStability
   generality: G
   mirror-B: D5/B/S3/Zeros/LeeYang/TreePairStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical pair zero exclusion and its allocation polynomial infrastructure. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Homogenize

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace FiolArbitraryTreePair

/- Bilinear complexification: no conjugates occur in these squares. -/
theorem rank_one_minus_squares_nonzero {J : Type*} [Fintype J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (l : ℂ) (t : J → ℂ) (K : ℝ)
    (hK : 0 ≤ K)
    (ha : 0 < l.re ^ 2 / 2 - ∑ j, w j * (t j).re ^ 2) :
    l ^ 2 / 2 - ∑ j, (w j : ℂ) * t j ^ 2 + (K : ℂ) ≠ 0 := by
  intro hz
  have hA : 0 ≤ ∑ j, w j * (t j).re ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hl : l.re ≠ 0 := by
    intro h
    rw [h] at ha
    norm_num at ha
    linarith
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.zero_re, Complex.zero_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add] at hre him
  let r : ℝ := l.im / l.re
  have hr : r * l.re = l.im := by dsimp [r]; field_simp
  have hcross : ∑ j, w j * ((t j).re * (t j).im) = l.re * l.im / 2 := by
    have he (j : J) : w j * ((t j).re * (t j).im + (t j).im * (t j).re) =
        2 * (w j * ((t j).re * (t j).im)) := by ring
    simp_rw [he, ← Finset.mul_sum] at him
    nlinarith
  have hs : 0 ≤ ∑ j, w j * ((t j).im - r * (t j).re) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have he : (∑ j, w j * ((t j).im - r * (t j).re) ^ 2) =
      (∑ j, w j * (t j).im ^ 2) -
      2 * r * (∑ j, w j * ((t j).re * (t j).im)) +
      r ^ 2 * (∑ j, w j * (t j).re ^ 2) := by
    simp_rw [show ∀ j, w j * ((t j).im - r * (t j).re) ^ 2 =
      w j * (t j).im ^ 2 - 2 * r * (w j * ((t j).re * (t j).im)) +
      r ^ 2 * (w j * (t j).re ^ 2) by intro j; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he, hcross] at hs
  have hm : r ^ 2 * (l.re ^ 2 / 2 - ∑ j, w j * (t j).re ^ 2) ≥ 0 :=
    mul_nonneg (sq_nonneg _) (le_of_lt ha)
  have hsq : l.im * l.im = r ^ 2 * l.re ^ 2 := by rw [← hr]; ring
  have hprod : r * (l.re * l.im) = l.im ^ 2 := by rw [← hr]; ring
  simp_rw [mul_sub] at hre
  rw [Finset.sum_sub_distrib] at hre
  simp_rw [← pow_two] at hre
  nlinarith [hsq, hprod]

def kappa {R : Type*} [Field R] (d : ℕ) : R := (d : R) ^ 2 * ((d : R) ^ 2 - 1) / 24

def center {R : Type*} [Field R] (d : ℕ) : R := ((d : R) ^ 2 - 3) / (4 * ((d : R) - 1))

def remainder {R : Type*} [Field R] (d : ℕ) : R :=
  (d : R) * ((d : R) ^ 2 - 1) * ((d : R) - 3) / 96 +
  (d : R) * ((d : R) + 1) * (2 * (d : R) - 3) /
    (16 * ((d : R) - 1))

theorem remainder_pos (d : ℕ) (hd : 2 ≤ d) : 0 < (remainder d : ℝ) := by
  rcases eq_or_lt_of_le hd with rfl | hd
  · norm_num [remainder]
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    unfold remainder
    have hfirst : 0 ≤ (d : ℝ) * ((d : ℝ) ^ 2 - 1) * ((d : ℝ) - 3) / 96 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (mul_nonneg (by positivity) (by nlinarith)) (by linarith)
    have hsecond : 0 < (d : ℝ) * ((d : ℝ) + 1) * (2 * (d : ℝ) - 3) /
        (16 * ((d : ℝ) - 1)) := by
      apply div_pos
      · apply mul_pos
        · exact mul_pos (by linarith) (by linarith)
        · linarith
      · exact mul_pos (by norm_num) (by linarith)
    linarith

def leafRemainder {R : Type*} [Field R] (d : ℕ) : R := if d = 1 then 13 / 48 else remainder d

theorem leafRemainder_pos (d : ℕ) (hd : 1 ≤ d) : 0 < (leafRemainder d : ℝ) := by
  by_cases h : d = 1
  · simp [leafRemainder, h]
  · simp only [leafRemainder, if_neg h]
    exact remainder_pos d (by omega)

/- This identity includes the leaf compensation: when d=1, t=2z/3. -/
theorem vertex_square_identity {R : Type*} [Field R] [CharZero R] (d : ℕ) (hd : 1 ≤ d) (z t : R)
    (hleaf : d = 1 → t = 2 * z / 3) :
    (d : R) ^ 2 * t ^ 2 / 2 - z * ((d : R) * ((d : R) ^ 2 - 1) * t) / 4 +
        kappa d * z ^ 2 =
      (d : R) * ((d : R) - 1) / 2 * (t - center d * z) ^ 2 +
      (d : R) * t ^ 2 / 2 - z * ((d : R) * t) / 2 +
      ((d : R) / 16 + leafRemainder d) * z ^ 2 := by
  by_cases h : d = 1
  · subst d
    rw [hleaf rfl]
    norm_num [kappa, leafRemainder]
    ring
  · have hd2 : 2 ≤ d := by omega
    have hne : (d : R) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast (show d ≠ 1 by omega)
    simp only [leafRemainder, if_neg h]
    unfold kappa center remainder
    field_simp [hne]
    <;> ring

section FiniteGraph
variable {V R : Type*} [Fintype V] [Field R] [CharZero R]

def graphH (d : V → ℕ) (a : V → V → R) (z : R) (t : V → R) : R :=
    (∑ v, (d v : R) ^ 2 * t v ^ 2) / 2 +
    (∑ u, ∑ v, a u v * t u * t v) / 2 -
    z * (∑ v, (d v : R) * ((d v : R) ^ 2 - 1) * t v) / 4 +
    (∑ v, kappa (d v)) * z ^ 2

private theorem row_sum_left (d : V → ℕ) (a : V → V → R)
    (hrow : ∀ u, ∑ v, a u v = (d u : R)) (f : V → R) :
    (∑ u, ∑ v, a u v * f u) = ∑ u, (d u : R) * f u := by
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, hrow u]

private theorem row_sum_right (d : V → ℕ) (a : V → V → R)
    (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : R)) (f : V → R) :
    (∑ u, ∑ v, a u v * f v) = ∑ v, (d v : R) * f v := by
  rw [Finset.sum_comm]
  simp_rw [hsymm]
  exact row_sum_left d a hrow f

private theorem edge_square_expansion (d : V → ℕ) (a : V → V → R)
    (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : R)) (z : R) (t : V → R) :
    (∑ u, ∑ v, a u v * (t u + t v - z / 2) ^ 2) =
      2 * (∑ v, (d v : R) * t v ^ 2) +
      2 * (∑ u, ∑ v, a u v * t u * t v) -
      2 * z * (∑ v, (d v : R) * t v) + (∑ v, (d v : R)) * z ^ 2 / 4 := by
  have he (u v : V) : a u v * (t u + t v - z / 2) ^ 2 =
      a u v * t u ^ 2 + a u v * t v ^ 2 +
      2 * (a u v * t u * t v) - z * (a u v * t u) -
      z * (a u v * t v) + a u v * (z ^ 2 / 4) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [row_sum_left d a hrow (fun u => t u ^ 2),
    row_sum_right d a hsymm hrow (fun u => t u ^ 2),
    row_sum_left d a hrow t, row_sum_right d a hsymm hrow t]
  have hc : (∑ u, ∑ v, a u v * (z ^ 2 / 4)) =
      (∑ u, (d u : R)) * z ^ 2 / 4 := by
    simp only [← Finset.sum_mul, hrow]
    ring
  rw [hc]
  ring

theorem graph_sum_of_squares (d : V → ℕ) (a : V → V → R)
    (hd : ∀ v, 1 ≤ d v) (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : R)) (z : R) (t : V → R)
    (hleaf : ∀ v, d v = 1 → t v = 2 * z / 3) :
    graphH d a z t =
      (∑ v, (d v : R) * ((d v : R) - 1) / 2 *
        (t v - center (d v) * z) ^ 2) +
      (∑ u, ∑ v, a u v * (t u + t v - z / 2) ^ 2) / 4 +
      (∑ v, leafRemainder (d v)) * z ^ 2 := by
  have hv := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun v _ => vertex_square_identity (d v) (hd v) z (t v) (hleaf v))
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul] at hv
  rw [edge_square_expansion d a hsymm hrow]
  unfold graphH
  simp only [div_eq_mul_inv]
  linear_combination hv

end FiniteGraph

section QuadraticIdentity
variable {V R : Type*} [Fintype V] [DecidableEq V] [Field R] [CharZero R]

def pairWeight (d : V → ℕ) (a : V → V → R) (u v : V) : R :=
  (d u : R) * (d v : R) * ((d u : R) * (d v : R) - a u v) / 9

def pairQuadratic (d : V → ℕ) (a : V → V → R) (z : R) (eta : V → R) : R :=
  (∑ u, ∑ v, if u = v then 0 else pairWeight d a u v * (z + eta u) * (z + eta v)) / 2 +
  ∑ v, kappa (d v) * (z ^ 2 + 2 * z * eta v)

def vertexCoordinate (d : V → ℕ) (z : R) (eta : V → R) (v : V) : R :=
  (d v : R) * (z + eta v) / 3

def linearCoordinate (d : V → ℕ) (t : V → R) : R := ∑ v, (d v : R) * t v

private theorem sum_off_diagonal (f : V → V → R) :
    (∑ u, ∑ v, if u = v then 0 else f u v) = (∑ u, ∑ v, f u v) - ∑ u, f u u := by
  classical
  have h (u v : V) : (if u = v then 0 else f u v) =
      f u v - (if u = v then f u v else 0) := by split_ifs <;> simp
  simp_rw [h, Finset.sum_sub_distrib]
  simp

theorem pairQuadratic_rank_one (d : V → ℕ) (a : V → V → R)
    (hdiag : ∀ v, a v v = 0) (z : R) (eta : V → R) :
    pairQuadratic d a z eta =
      linearCoordinate d (vertexCoordinate d z eta) ^ 2 / 2 -
      graphH d a z (vertexCoordinate d z eta) := by
  classical
  let t := vertexCoordinate d z eta
  have hp (u v : V) : pairWeight d a u v * (z + eta u) * (z + eta v) =
      ((d u : R) * (d v : R) - a u v) * t u * t v := by
    dsimp [pairWeight, t, vertexCoordinate]
    ring
  have hv (v : V) : kappa (d v) * (z ^ 2 + 2 * z * eta v) =
      z * ((d v : R) * ((d v : R) ^ 2 - 1) * t v) / 4 - kappa (d v) * z ^ 2 := by
    dsimp [kappa, t, vertexCoordinate]
    ring
  have hdiag' : (∑ u, ((d u : R) * (d u : R) - a u u) * t u * t u) =
      ∑ u, (d u : R) ^ 2 * t u ^ 2 := by
    apply Finset.sum_congr rfl
    intro u _
    rw [hdiag u]
    ring
  have hL : linearCoordinate d t ^ 2 =
      ∑ u, ∑ v, (d u : R) * (d v : R) * t u * t v := by
    unfold linearCoordinate
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  unfold pairQuadratic
  simp_rw [hp, hv]
  rw [sum_off_diagonal, hdiag']
  change _ = linearCoordinate d t ^ 2 / 2 - graphH d a z t
  rw [hL]
  unfold graphH
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end QuadraticIdentity

def cayley (w : ℂ) : ℂ := (1 - w) / (1 + w)

theorem cayley_re (w : ℂ) :
    (cayley w).re = (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 := by
  unfold cayley
  rw [Complex.div_re, Complex.normSq_eq_norm_sq, ← add_div]
  congr 1
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
    Complex.add_im, Complex.one_im, zero_sub, zero_add]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem cayley_denominator_ne_zero (w : ℂ) (hw : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro h
  have he : w = -1 := by linear_combination h
  rw [he] at hw
  norm_num at hw

theorem cayley_re_pos (w : ℂ) (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  rw [cayley_re]
  apply div_pos
  · nlinarith [norm_nonneg w]
  · exact sq_pos_of_pos (norm_pos_iff.mpr (cayley_denominator_ne_zero w hw))

theorem cayley_vertex_local (X w : ℂ) (hX : X ≠ 1) (hw : 1 + w ≠ 0) :
    (1 - X) / 2 * ((1 + X) / (1 - X) + cayley w) * (1 + w) = 1 + w * X ∧
    ((1 - X) / 2) ^ 2 * (((1 + X) / (1 - X)) ^ 2 +
      2 * ((1 + X) / (1 - X)) * cayley w + 1) * (1 + w) = 1 + w * X ^ 2 := by
  have hXm : 1 - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hX)
  unfold cayley
  constructor <;> field_simp [hXm, hw] <;> ring

end FiolArbitraryTreePair

open scoped BigOperators

namespace FiolArbitraryTreePair

private lemma center_cast (d : ℕ) : (center d : ℂ) = ((center d : ℝ) : ℂ) := by
  simp [center]
private lemma remainder_cast (d : ℕ) : (remainder d : ℂ) = ((remainder d : ℝ) : ℂ) := by
  simp [remainder]
private lemma leafRemainder_cast (d : ℕ) : (leafRemainder d : ℂ) = ((leafRemainder d : ℝ) : ℂ) := by
  by_cases h : d = 1 <;> simp [leafRemainder, h, remainder_cast]

abbrev CertificateIndex (V : Type*) := Sum V (Sum (V × V) Unit)

def certificateWeight {V : Type*} [Fintype V] (d : V → ℕ) (a : V → V → ℝ) :
    CertificateIndex V → ℝ
  | .inl v => (d v : ℝ) * ((d v : ℝ) - 1) / 2
  | .inr (.inl (u,v)) => a u v / 4
  | .inr (.inr _) => ∑ v, leafRemainder (d v)

def certificateValue {V R : Type*} [Fintype V] [Field R]
    (d : V → ℕ) (z : R) (t : V → R) : CertificateIndex V → R
  | .inl v => t v - center (d v) * z
  | .inr (.inl (u,v)) => t u + t v - z / 2
  | .inr (.inr _) => z

theorem certificateWeight_nonneg {V : Type*} [Fintype V]
    (d : V → ℕ) (a : V → V → ℝ) (hd : ∀ v, 1 ≤ d v) (ha : ∀ u v, 0 ≤ a u v)
    (j : CertificateIndex V) : 0 ≤ certificateWeight d a j := by
  rcases j with v | (⟨u,v⟩ | ⟨⟩)
  · dsimp [certificateWeight]
    have : (1 : ℝ) ≤ d v := by exact_mod_cast hd v
    positivity
  · exact div_nonneg (ha u v) (by norm_num)
  · exact Finset.sum_nonneg fun v _ => le_of_lt (leafRemainder_pos _ (hd v))

private theorem certificate_sum_real {V : Type*} [Fintype V]
    (d : V → ℕ) (a : V → V → ℝ) (z : ℝ) (t : V → ℝ) :
    (∑ j, certificateWeight d a j * certificateValue d z t j ^ 2) =
      (∑ v, (d v : ℝ) * ((d v : ℝ) - 1) / 2 * (t v - center (d v) * z) ^ 2) +
      (∑ u, ∑ v, a u v * (t u + t v - z / 2) ^ 2) / 4 +
      (∑ v, leafRemainder (d v)) * z ^ 2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    certificateWeight, certificateValue]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

private theorem certificate_sum_complex {V : Type*} [Fintype V]
    (d : V → ℕ) (a : V → V → ℝ) (z : ℂ) (t : V → ℂ) :
    (∑ j, (certificateWeight d a j : ℂ) * certificateValue d z t j ^ 2) =
      (∑ v, (d v : ℂ) * ((d v : ℂ) - 1) / 2 * (t v - center (d v) * z) ^ 2) +
      (∑ u, ∑ v, (a u v : ℂ) * (t u + t v - z / 2) ^ 2) / 4 +
      (∑ v, (leafRemainder (d v) : ℂ)) * z ^ 2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    certificateWeight, certificateValue]
  push_cast
  simp only [← center_cast, ← leafRemainder_cast]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

theorem pairQuadratic_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : ℝ)) (hdiag : ∀ v, a v v = 0)
    (z : ℂ) (eta : V → ℂ) (hleaf : ∀ v, d v = 1 → eta v = z) :
    pairQuadratic d (fun u v => (a u v : ℂ)) z eta =
      linearCoordinate d (vertexCoordinate d z eta) ^ 2 / 2 -
      ∑ j, (certificateWeight d a j : ℂ) *
        certificateValue d z (vertexCoordinate d z eta) j ^ 2 := by
  have hrowC (u : V) : (∑ v, (a u v : ℂ)) = (d u : ℂ) := by
    rw [← Complex.ofReal_sum, hrow]
    simp
  rw [pairQuadratic_rank_one d _ (fun v => by simp [hdiag])]
  rw [certificate_sum_complex]
  congr 1
  apply graph_sum_of_squares d _ hd (fun u v => by rw [hsymm]) hrowC
  intro v hv
  simp [vertexCoordinate, hv, hleaf v hv]
  ring

theorem pairQuadratic_pos {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (a : V → V → ℝ) (hd : ∀ v, 1 ≤ d v)
    (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1) (hi : ∃ v, 2 ≤ d v)
    (z : ℝ) (eta : V → ℝ) (hz : 0 < z) (heta : ∀ v, 0 < eta v) :
    0 < pairQuadratic d a z eta := by
  classical
  have hk (v : V) : 0 ≤ (kappa (d v) : ℝ) := by
    have hv : (1 : ℝ) ≤ d v := by exact_mod_cast hd v
    unfold kappa
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) (by norm_num)
  have hp (u v : V) : 0 ≤ pairWeight d a u v := by
    have hu : (1 : ℝ) ≤ d u := by exact_mod_cast hd u
    have hv : (1 : ℝ) ≤ d v := by exact_mod_cast hd v
    have hm : 1 ≤ (d u : ℝ) * d v := by nlinarith
    unfold pairWeight
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (by have := (ha u v).2; linarith)) (by norm_num)
  have hpair : 0 ≤ (∑ u, ∑ v, if u = v then 0 else
      pairWeight d a u v * (z + eta u) * (z + eta v)) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (hp u v) (le_of_lt (add_pos hz (heta u))))
        (le_of_lt (add_pos hz (heta v)))
  obtain ⟨v, hv⟩ := hi
  have hdv : (2 : ℝ) ≤ d v := by exact_mod_cast hv
  have hkv : 0 < (kappa (d v) : ℝ) := by
    unfold kappa
    apply div_pos _ (by norm_num)
    exact mul_pos (by positivity) (by nlinarith)
  have ht (u : V) : 0 < z ^ 2 + 2 * z * eta u := by
    exact add_pos (sq_pos_of_pos hz) (mul_pos (mul_pos (by norm_num) hz) (heta u))
  have hsum : 0 < ∑ v, (kappa (d v) : ℝ) * (z ^ 2 + 2 * z * eta v) := by
    exact lt_of_lt_of_le (mul_pos hkv (ht v))
      (Finset.single_le_sum (fun u _ => mul_nonneg (hk u) (le_of_lt (ht u)))
        (Finset.mem_univ v))
  unfold pairQuadratic
  linarith

theorem pairQuadratic_certificate_real {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : ℝ)) (hdiag : ∀ v, a v v = 0)
    (z : ℝ) (eta : V → ℝ) (hleaf : ∀ v, d v = 1 → eta v = z) :
    pairQuadratic d a z eta =
      linearCoordinate d (vertexCoordinate d z eta) ^ 2 / 2 -
      ∑ j, certificateWeight d a j *
        certificateValue d z (vertexCoordinate d z eta) j ^ 2 := by
  rw [pairQuadratic_rank_one d a hdiag, certificate_sum_real]
  congr 1
  apply graph_sum_of_squares d a hd hsymm hrow
  intro v hv
  simp [vertexCoordinate, hv, hleaf v hv]
  ring

private theorem linearCoordinate_re {V : Type*} [Fintype V]
    (d : V → ℕ) (t : V → ℂ) :
    (linearCoordinate d t).re = linearCoordinate d (fun v => (t v).re) := by
  simp [linearCoordinate, Complex.re_sum, Complex.mul_re]

private theorem vertexCoordinate_re {V : Type*} [Fintype V]
    (d : V → ℕ) (z : ℂ) (eta : V → ℂ) :
    (fun v => (vertexCoordinate d z eta v).re) =
      vertexCoordinate d z.re (fun v => (eta v).re) := by
  funext v
  simp [vertexCoordinate, Complex.mul_re, Complex.div_ofNat_re]

private theorem certificateValue_re {V : Type*} [Fintype V]
    (d : V → ℕ) (z : ℂ) (t : V → ℂ) (j : CertificateIndex V) :
    (certificateValue d z t j).re =
      certificateValue d z.re (fun v => (t v).re) j := by
  rcases j with v | (⟨u,v⟩ | ⟨⟩)
  · simp [certificateValue, center_cast, Complex.mul_re]
  · simp [certificateValue, Complex.div_ofNat_re]
  · rfl

theorem pairQuadratic_add_constant_nonzero {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1)
    (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : ℝ)) (hdiag : ∀ v, a v v = 0)
    (hi : ∃ v, 2 ≤ d v) (z : ℂ) (eta : V → ℂ)
    (hz : 0 < z.re) (heta : ∀ v, 0 < (eta v).re)
    (hleaf : ∀ v, d v = 1 → eta v = z) (K : ℝ) (hK : 0 ≤ K) :
    pairQuadratic d (fun u v => (a u v : ℂ)) z eta + (K : ℂ) ≠ 0 := by
  rw [pairQuadratic_certificate d a hd hsymm hrow hdiag z eta hleaf]
  apply rank_one_minus_squares_nonzero _
    (certificateWeight_nonneg d a hd (fun u v => (ha u v).1)) _ _ K hK
  simp_rw [linearCoordinate_re, certificateValue_re]
  rw [vertexCoordinate_re]
  rw [← pairQuadratic_certificate_real d a hd hsymm hrow hdiag z.re
    (fun v => (eta v).re) (fun v hv => by rw [hleaf v hv])]
  exact pairQuadratic_pos d a hd ha hi z.re _ hz heta

def physicalEta {V : Type*} (d : V → ℕ) (X : ℂ) (v : V) : ℂ :=
  cayley ((-1 : ℂ) ^ d v * X ^ d v)

theorem physicalEta_re_pos {V : Type*} (d : V → ℕ) (hd : ∀ v, 1 ≤ d v)
    (X : ℂ) (hX : ‖X‖ < 1) (v : V) : 0 < (physicalEta d X v).re := by
  apply cayley_re_pos
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  exact pow_lt_one₀ (norm_nonneg X) hX (by have := hd v; omega)

theorem physical_pairQuadratic_nonzero {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1)
    (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : ℝ)) (hdiag : ∀ v, a v v = 0)
    (hi : ∃ v, 2 ≤ d v) (X : ℂ) (hX : ‖X‖ < 1) (K : ℝ) (hK : 0 ≤ K) :
    pairQuadratic d (fun u v => (a u v : ℂ)) (cayley (-X))
      (physicalEta d X) + (K : ℂ) ≠ 0 := by
  apply pairQuadratic_add_constant_nonzero d a hd ha hsymm hrow hdiag hi
    _ _ (cayley_re_pos (-X) (by simpa using hX))
    (physicalEta_re_pos d hd X hX) _ K hK
  intro v hv
  simp [physicalEta, hv]

end FiolArbitraryTreePair



open scoped BigOperators
open Polynomial

namespace FiolArbitraryTreePair

def vertexFactor (d r : ℕ) : ℝ[X] := 1 + C ((-1 : ℝ) ^ d) * X ^ (d + r)

def allocationPolynomial {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) : ℝ[X] :=
  ∑ a, C (w a) * ∏ v, vertexFactor (d v) (r a v)

theorem vertexFactor_zero (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).coeff 0 = 1 := by
  have hm : d + r ≠ 0 := by omega
  rw [vertexFactor, coeff_add, coeff_C_mul_X_pow]
  simp only [coeff_one]
  simp [hm, Ne.symm hm, Nat.ne_of_gt hd]

theorem vertexFactor_degree (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).natDegree = d + r := by
  unfold vertexFactor
  rw [natDegree_one_add, natDegree_C_mul_X_pow _ _ (pow_ne_zero _ (by norm_num))]

theorem vertexFactor_ne_zero (d r : ℕ) (hd : 0 < d) : vertexFactor d r ≠ 0 := by
  intro h
  have := vertexFactor_zero d r hd
  rw [h] at this
  norm_num at this

theorem vertexFactor_leadingCoeff (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).leadingCoeff = (-1 : ℝ) ^ d := by
  rw [← coeff_natDegree, vertexFactor_degree d r hd]
  have hm : d + r ≠ 0 := by omega
  rw [vertexFactor, coeff_add, coeff_C_mul_X_pow]
  simp only [coeff_one]
  simp [hm, Ne.symm hm, Nat.ne_of_gt hd]

theorem allocation_constant {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (hd : ∀ v, 0 < d v) :
    (allocationPolynomial d r w).coeff 0 = ∑ a, w a := by
  classical
  simp [allocationPolynomial, coeff_zero_prod, vertexFactor_zero, hd]

theorem allocation_degree_and_leading {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v)) :
    (allocationPolynomial d r w).natDegree = N ∧
      (allocationPolynomial d r w).leadingCoeff = ∑ a, w a ∧
      allocationPolynomial d r w ≠ 0 := by
  classical
  have hterm (a : A) : (C (w a) * ∏ v, vertexFactor (d v) (r a v)).natDegree = N := by
    rw [natDegree_C_mul (ne_of_gt (hw a)), natDegree_prod]
    · simpa only [vertexFactor_degree, hd] using hmass a
    · intro v _
      exact vertexFactor_ne_zero _ _ (hd v)
  have hlead (a : A) : (C (w a) * ∏ v, vertexFactor (d v) (r a v)).leadingCoeff = w a := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_prod]
    simp_rw [vertexFactor_leadingCoeff _ _ (hd _)]
    rw [Finset.prod_pow_eq_pow_sum]
    simp [hparity.neg_one_pow]
  have hcoeff : (allocationPolynomial d r w).coeff N = ∑ a, w a := by
    unfold allocationPolynomial
    rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hterm a, coeff_natDegree, hlead]
  have hpos : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  have hle : (allocationPolynomial d r w).natDegree ≤ N := by
    apply natDegree_sum_le_of_forall_le
    intro a _
    exact le_of_eq (hterm a)
  have hge : N ≤ (allocationPolynomial d r w).natDegree :=
    le_natDegree_of_ne_zero (by rw [hcoeff]; exact ne_of_gt hpos)
  have hdeg := le_antisymm hle hge
  refine ⟨hdeg, ?_, ?_⟩
  · rw [← coeff_natDegree, hdeg, hcoeff]
  · intro h
    rw [h, coeff_zero] at hcoeff
    linarith

def quotientVertexFactor (d r : ℕ) : ℝ[X] :=
  if Odd d then ∑ i ∈ Finset.range (d + r), X ^ i else vertexFactor d r

def oddCount {V : Type*} [Fintype V] (d : V → ℕ) : ℕ :=
  (Finset.univ.filter fun v => Odd (d v)).card

def allocationQuotient {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) : ℝ[X] :=
  ∑ a, C (w a) * ∏ v, quotientVertexFactor (d v) (r a v)

theorem vertex_factor_at_one (d r : ℕ) :
    vertexFactor d r = (if Odd d then 1 - X else 1) * quotientVertexFactor d r := by
  classical
  by_cases h : Odd d
  · simp only [quotientVertexFactor, if_pos h, vertexFactor, h.neg_one_pow, C_neg, C_1,
      neg_one_mul]
    have he := geom_sum_mul_neg (X : ℝ[X]) (d + r)
    simpa [mul_comm, sub_eq_add_neg] using he.symm
  · simp [quotientVertexFactor, h]

theorem allocation_factor_at_one {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) :
    allocationPolynomial d r w = (1 - X) ^ oddCount d * allocationQuotient d r w := by
  classical
  unfold allocationPolynomial allocationQuotient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [vertex_factor_at_one, Finset.prod_mul_distrib]
  have he : (∏ v, if Odd (d v) then (1 - X : ℝ[X]) else 1) = (1 - X) ^ oddCount d := by
    simp [oddCount, Finset.prod_ite, Finset.prod_const]
  rw [he]
  ring

theorem allocation_quotient_at_one_pos {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a) :
    0 < (allocationQuotient d r w).eval 1 := by
  classical
  unfold allocationQuotient
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro a _
  apply mul_pos (hw a)
  apply Finset.prod_pos
  intro v _
  unfold quotientVertexFactor
  split_ifs with h
  · simp only [eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (show 0 < d v + r a v by have := hd v; omega)
  · have he : Even (d v) := Nat.not_odd_iff_even.mp h
    norm_num [vertexFactor, he.neg_one_pow]

theorem allocation_multiplicity_one {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a) :
    (allocationPolynomial d r w).rootMultiplicity 1 = oddCount d := by
  have hQ : allocationQuotient d r w ≠ 0 := by
    intro h
    have := allocation_quotient_at_one_pos d r w hd hw
    rw [h, eval_zero] at this
    linarith
  have hroot : (allocationQuotient d r w).rootMultiplicity 1 = 0 := by
    apply rootMultiplicity_eq_zero
    exact ne_of_gt (allocation_quotient_at_one_pos d r w hd hw)
  rw [allocation_factor_at_one]
  have hf : (1 - X : ℝ[X]) = C (-1) * (X - C 1) := by simp
  rw [hf, mul_pow]
  have hne : C (-1 : ℝ) ^ oddCount d * allocationQuotient d r w ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by simp)) hQ
  have he : C (-1 : ℝ) ^ oddCount d * (X - C 1) ^ oddCount d *
      allocationQuotient d r w =
      (C (-1) ^ oddCount d * allocationQuotient d r w) * (X - C 1) ^ oddCount d := by ring
  rw [he, rootMultiplicity_mul_X_sub_C_pow hne]
  have hc : (C (-1 : ℝ) ^ oddCount d).rootMultiplicity 1 = 0 := by
    apply rootMultiplicity_eq_zero
    simp [Polynomial.IsRoot]
  rw [rootMultiplicity_mul hne, hc, hroot]
  simp

def complexEval (p : ℝ[X]) (x : ℂ) : ℂ := p.eval₂ (algebraMap ℝ ℂ) x

theorem vertexFactor_eval (d r : ℕ) (x : ℂ) :
    complexEval (vertexFactor d r) x = 1 + (-1 : ℂ) ^ d * x ^ (d + r) := by
  simp [complexEval, vertexFactor]

theorem vertexFactor_reciprocal (d r : ℕ) (x : ℂ) (hx : x ≠ 0) :
    x ^ (d + r) * complexEval (vertexFactor d r) x⁻¹ =
      (-1 : ℂ) ^ d * complexEval (vertexFactor d r) x := by
  rw [vertexFactor_eval, vertexFactor_eval]
  have hs : ((-1 : ℂ) ^ d) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [inv_pow]
  calc
    x ^ (d + r) * (1 + (-1 : ℂ) ^ d * (x ^ (d + r))⁻¹) =
        x ^ (d + r) + (-1 : ℂ) ^ d := by field_simp
    _ = (-1 : ℂ) ^ d * (1 + (-1 : ℂ) ^ d * x ^ (d + r)) := by
      linear_combination -(x ^ (d + r)) * hs

theorem allocation_reciprocal {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v))
    (x : ℂ) (hx : x ≠ 0) :
    x ^ N * complexEval (allocationPolynomial d r w) x⁻¹ =
      complexEval (allocationPolynomial d r w) x := by
  classical
  simp only [allocationPolynomial, complexEval, eval₂_finsetSum, eval₂_mul, eval₂_C,
    eval₂_finsetProd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he := congrArg (fun q : V → ℂ => ∏ v, q v)
    (funext fun v => vertexFactor_reciprocal (d v) (r a v) x hx)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hmass a,
    hparity.neg_one_pow, one_mul, complexEval] at he
  rw [mul_left_comm, he]

theorem allocation_roots_on_circle {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v))
    (hdisk : ∀ x : ℂ, ‖x‖ < 1 → complexEval (allocationPolynomial d r w) x ≠ 0)
    (x : ℂ) (hx : complexEval (allocationPolynomial d r w) x = 0) : ‖x‖ = 1 := by
  have hn : ¬ ‖x‖ < 1 := by intro h; exact hdisk x h hx
  have hpos : 0 < ‖x‖ := by linarith
  by_contra hne
  have hgt : 1 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
  have hi : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hgt
  have hrec := allocation_reciprocal d r w N hmass hparity x
    (norm_pos_iff.mp hpos)
  rw [hx] at hrec
  exact hdisk x⁻¹ hi ((mul_eq_zero.mp hrec).resolve_left
    (pow_ne_zero _ (norm_pos_iff.mp hpos)))

theorem vertexFactor_eval_neg_one (d r : ℕ) :
    (vertexFactor d r).eval (-1) = 1 + (-1 : ℝ) ^ r := by
  simp only [vertexFactor, eval_add, eval_one, eval_mul, eval_C, eval_pow, eval_X, pow_add]
  have hs : (-1 : ℝ) ^ d * (-1 : ℝ) ^ d = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← mul_assoc, hs, one_mul]

end FiolArbitraryTreePair

open scoped BigOperators
open Polynomial

namespace FiolArbitraryTreePair

theorem homogenize_axis_scaled {R : Type*} [CommSemiring R]
    (p : R[X]) (N : ℕ) (x : R) :
    MvPolynomial.eval ![x,0] (p.homogenize N) = p.coeff N * x ^ N := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simpa [add_mul] using congrArg₂ (fun a b : R => a + b) ihp ihq
  | monomial k c =>
    rcases le_or_gt k N with hk | hk
    · rw [homogenize_monomial hk]
      by_cases h : k = N
      · subst k
        simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
      · have hn : N - k ≠ 0 := by omega
        simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
          hn, coeff_monomial, h, Ne.symm h]
    · rw [homogenize_monomial_of_lt hk]
      simp [coeff_monomial, Nat.ne_of_gt hk, Ne.symm (Nat.ne_of_gt hk)]

theorem homogenize_axis {R : Type*} [CommSemiring R] (p : R[X]) (N : ℕ) :
    MvPolynomial.eval ![(1 : R),0] (p.homogenize N) = p.coeff N := by
  simpa using homogenize_axis_scaled p N 1

theorem complexEval_real (p : ℝ[X]) (x : ℝ) :
    complexEval p (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [complexEval] using congrArg₂ (fun a b : ℂ => a + b) hp hq
  | monomial k c => simp [complexEval]

theorem homogenize_complex_eval (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N)
    (x : Fin 2 → ℂ) (hx : x 1 ≠ 0) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) x (p.homogenize N) =
      complexEval p (x 0 / x 1) * x 1 ^ N := by
  rw [MvPolynomial.eval₂_eq_eval_map, ← homogenize_map]
  rw [eval_homogenize ((natDegree_map_le).trans hN) x hx]
  simp only [Polynomial.eval_map,complexEval]

theorem homogenize_complex_infinity (p : ℝ[X]) (N : ℕ) (x : ℂ) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) ![x,0] (p.homogenize N) =
      (p.coeff N : ℂ) * x ^ N := by
  rw [MvPolynomial.eval₂_eq_eval_map, ← homogenize_map, homogenize_axis_scaled]
  simp

theorem allocation_quotient_degree {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a)
    (hdegree : (allocationPolynomial d r w).natDegree = N) :
    (allocationQuotient d r w).natDegree = N - oddCount d := by
  have hQ : allocationQuotient d r w ≠ 0 := by
    intro h
    have := allocation_quotient_at_one_pos d r w hd hw
    rw [h, eval_zero] at this
    linarith
  have hf : (1 - X : ℝ[X]) = C (-1) * (X - C 1) := by simp
  have hfne : (1 - X : ℝ[X]) ≠ 0 := by rw [hf]; exact mul_ne_zero (by simp) (X_sub_C_ne_zero 1)
  have hdeg : (1 - X : ℝ[X]).natDegree = 1 := by
    rw [hf, natDegree_C_mul (by norm_num), natDegree_X_sub_C]
  have he := congrArg Polynomial.natDegree (allocation_factor_at_one d r w)
  rw [hdegree, natDegree_mul (pow_ne_zero _ hfne) hQ] at he
  simp only [natDegree_pow, hdeg, mul_one, one_mul] at he
  omega

end FiolArbitraryTreePair
