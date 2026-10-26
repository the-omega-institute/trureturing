/- GID: D5/S3/Zeros/LeeYang/TreePairStability
   generality: G
   mirror-B: D5/B/S3/Zeros/LeeYang/TreePairStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical Cayley substitution excludes zeros in the disk. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

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

private lemma kappa_cast (d : ℕ) : (kappa d : ℂ) = ((kappa d : ℝ) : ℂ) := by
  simp [kappa]
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
