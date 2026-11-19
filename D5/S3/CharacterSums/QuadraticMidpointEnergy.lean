/- GID: D5/S3/CharacterSums/QuadraticMidpointEnergy
   generality: G
   mirror-B: D5/B/S3/CharacterSums/QuadraticMidpointEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite quadratic character energy with arbitrary linear twists. -/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-! The finite cancellation estimate behind the midpoint-phase average.
The linear twist is allowed to depend on the quadratic coefficient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexConjugate
open Finset Complex

namespace D5.S3.CharacterSums.QuadraticMidpointEnergy

private theorem triangle_sum_by_lag {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range i, f i j) =
      ∑ h ∈ range n, ∑ j ∈ range (n - (h + 1)), f (j + h + 1) j := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x ↦ ⟨x.1 - x.2 - 1, x.2⟩)
    (fun x ↦ ⟨x.2 + x.1 + 1, x.2⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [mem_sigma, mem_range, Sigma.forall]
    omega
  · simp only [mem_sigma, mem_range, Sigma.forall]
    omega
  · intro x hx
    simp only [mem_sigma, mem_range] at hx
    apply Sigma.ext <;> simp only [heq_eq_eq] <;> omega
  · intro x hx
    simp only [mem_sigma, mem_range] at hx
    apply Sigma.ext <;> simp only [heq_eq_eq] <;> omega
  · intro x hx
    simp only [mem_sigma, mem_range] at hx
    change f x.1 x.2 = f (x.2 + (x.1 - x.2 - 1) + 1) x.2
    congr 1
    omega

private theorem sum_mul_conj_decomposition (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ range n, f j) * conj (∑ j ∈ range n, f j) =
      (∑ j ∈ range n, f j * conj (f j)) +
      (∑ i ∈ range n, ∑ j ∈ range i, f i * conj (f j)) +
      conj (∑ i ∈ range n, ∑ j ∈ range i, f i * conj (f j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, map_add]
    rw [add_mul, mul_add, mul_add]
    rw [show (∑ j ∈ range n, f j) * conj (∑ j ∈ range n, f j) = _ from ih]
    simp only [mul_add, add_mul, mul_sum, sum_mul, map_sum, map_mul, conj_conj]
    simp only [mul_comm]
    abel

/-- A finite differencing estimate. The norm is taken after summing each
fixed-lag correlation, preserving the cancellation within that correlation. -/
private theorem norm_sum_sq_le_correlations (f : ℕ → ℂ) (n : ℕ) :
    ‖∑ j ∈ range n, f j‖ ^ 2 ≤
      (∑ j ∈ range n, ‖f j‖ ^ 2) +
      2 * ∑ h ∈ range n,
        ‖∑ j ∈ range (n - (h + 1)), f (j + h + 1) * conj (f j)‖ := by
  have heq := congrArg Complex.re (sum_mul_conj_decomposition f n)
  simp only [Complex.mul_conj', Complex.add_re, Complex.conj_re,
    Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] at heq
  rw [triangle_sum_by_lag] at heq
  calc
    _ = (∑ j ∈ range n, ‖f j‖ ^ 2) +
        2 * ∑ h ∈ range n,
          (∑ j ∈ range (n - (h + 1)), f (j + h + 1) * conj (f j)).re := by
      simp only [Complex.re_sum]
      linarith
    _ ≤ _ := by
      gcongr with h hh
      exact Complex.re_le_norm _

private theorem norm_geometric_sum_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖∑ j ∈ range n, z ^ j‖ ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ j ∈ range n, ‖z ^ j‖ := norm_sum_le _ _
    _ = _ := by simp [norm_pow, hz]

private theorem norm_geometric_sum_le_chord {z : ℂ} (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (n : ℕ) :
    ‖∑ j ∈ range n, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [norm_pow, hz]; norm_num

/-- The truncated geometric majorant, including its resonant value at zero. -/
def geometricMajorant (p Z : ℕ) [NeZero p] (a : ZMod p) : ℝ :=
  if a = 0 then (Z : ℝ) else
    min (Z : ℝ) (2 / ‖ZMod.stdAddChar a - 1‖)

private theorem geometricMajorant_nonneg (p Z : ℕ) [NeZero p] (a : ZMod p) :
    0 ≤ geometricMajorant p Z a := by
  unfold geometricMajorant
  split_ifs <;> positivity

private theorem norm_character_geometric_sum_le (p Z n : ℕ) [NeZero p]
    (hn : n ≤ Z) (a : ZMod p) :
    ‖∑ j ∈ range n, (ZMod.stdAddChar a) ^ j‖ ≤ geometricMajorant p Z a := by
  have hnorm : ‖ZMod.stdAddChar a‖ = 1 := by
    simp [ZMod.stdAddChar_apply]
  have htriv := (norm_geometric_sum_le hnorm n).trans
    (show (n : ℝ) ≤ (Z : ℝ) by exact_mod_cast hn)
  unfold geometricMajorant
  split_ifs with ha
  · exact htriv
  · apply le_min htriv
    apply norm_geometric_sum_le_chord hnorm
    intro h
    apply ha
    exact ZMod.injective_stdAddChar (by simpa using h)

/-- A quadratic additive phase with an arbitrary point of the complex unit
circle as linear twist, and an arbitrary residue as interval origin. -/
def quadraticTerm {p : ℕ} [NeZero p] (a m : ZMod p) (w : ℂ) (j : ℕ) : ℂ :=
  ZMod.stdAddChar (a * (m + (j : ZMod p)) ^ 2) * w ^ j

private theorem norm_quadraticTerm {p : ℕ} [NeZero p]
    (a m : ZMod p) {w : ℂ} (hw : ‖w‖ = 1) (j : ℕ) :
    ‖quadraticTerm a m w j‖ = 1 := by
  simp [quadraticTerm, norm_mul, norm_pow, hw, ZMod.stdAddChar_apply]

private theorem quadraticTerm_shift {p : ℕ} [NeZero p]
    (a m : ZMod p) (w : ℂ) (j d : ℕ) :
    quadraticTerm a m w (j + d) =
      (ZMod.stdAddChar (a * (2 * m * (d : ZMod p) + (d : ZMod p) ^ 2)) * w ^ d) *
      (ZMod.stdAddChar (2 * a * (d : ZMod p))) ^ j * quadraticTerm a m w j := by
  have hpoly : a * (m + ((j + d : ℕ) : ZMod p)) ^ 2 =
      a * (2 * m * (d : ZMod p) + (d : ZMod p) ^ 2) +
      j • (2 * a * (d : ZMod p)) + a * (m + (j : ZMod p)) ^ 2 := by
    simp only [Nat.cast_add, nsmul_eq_mul]
    ring
  simp only [quadraticTerm, hpoly, AddChar.map_add_eq_mul,
    AddChar.map_nsmul_eq_pow, pow_add]
  ring

private theorem norm_quadratic_correlation_le {p Z : ℕ} [NeZero p]
    (a m : ZMod p) {w : ℂ} (hw : ‖w‖ = 1) (n d : ℕ) (hn : n ≤ Z) :
    ‖∑ j ∈ range n, quadraticTerm a m w (j + d) *
      conj (quadraticTerm a m w j)‖ ≤ geometricMajorant p Z (2 * a * (d : ZMod p)) := by
  let c := ZMod.stdAddChar
    (a * (2 * m * (d : ZMod p) + (d : ZMod p) ^ 2)) * w ^ d
  have hc : ‖c‖ = 1 := by
    simp [c, norm_mul, norm_pow, hw, ZMod.stdAddChar_apply]
  have hterm (j : ℕ) : quadraticTerm a m w (j + d) *
      conj (quadraticTerm a m w j) =
      c * (ZMod.stdAddChar (2 * a * (d : ZMod p))) ^ j := by
    rw [quadraticTerm_shift]
    calc
      _ = c * (ZMod.stdAddChar (2 * a * (d : ZMod p))) ^ j *
          (quadraticTerm a m w j * conj (quadraticTerm a m w j)) := by
            dsimp [c]
            ring
      _ = _ := by rw [Complex.mul_conj', norm_quadraticTerm a m hw]; simp
  simp_rw [hterm]
  rw [← mul_sum, norm_mul, hc, one_mul]
  exact norm_character_geometric_sum_le p Z n hn _

/-- The differencing majorant is independent of interval origin, length below
Z, and arbitrary linear twist. This uniformity is needed before averaging. -/
private theorem quadratic_energy_le_geometric_majorant {p Z : ℕ} [NeZero p]
    (a m : ZMod p) {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) (hn : n ≤ Z) :
    ‖∑ j ∈ range n, quadraticTerm a m w j‖ ^ 2 ≤
      (Z : ℝ) + 2 * ∑ h ∈ range Z,
        geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p)) := by
  calc
    _ ≤ (∑ j ∈ range n, ‖quadraticTerm a m w j‖ ^ 2) +
        2 * ∑ h ∈ range n,
          ‖∑ j ∈ range (n - (h + 1)), quadraticTerm a m w (j + h + 1) *
            conj (quadraticTerm a m w j)‖ := norm_sum_sq_le_correlations _ _
    _ ≤ (Z : ℝ) + 2 * ∑ h ∈ range n,
        geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p)) := by
      simp only [norm_quadraticTerm a m hw, one_pow, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      gcongr with h hh
      exact norm_quadratic_correlation_le a m hw (n - (h + 1)) (h + 1)
        ((Nat.sub_le _ _).trans hn)
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact sum_le_sum_of_subset_of_nonneg (range_mono hn)
        (fun h _ _ ↦ geometricMajorant_nonneg p Z _)

private theorem character_chord_eq_sine (p : ℕ) [NeZero p] (a : ZMod p) :
    ‖ZMod.stdAddChar a - 1‖ = 2 * Real.sin (Real.pi * (a.val : ℝ) / p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hv : (a.val : ℝ) < p := by exact_mod_cast ZMod.val_lt a
  have hx0 : 0 ≤ Real.pi * (a.val : ℝ) / p := by positivity
  have hx1 : Real.pi * (a.val : ℝ) / p ≤ Real.pi := by
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_pos]
  have heq : ZMod.stdAddChar a =
      Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / p : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * (a.val : ℝ) / p) / 2 =
      Real.pi * (a.val : ℝ) / p := by ring
  rw [hhalf, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx1)

private theorem character_chord_lower_half (p : ℕ) [NeZero p] (a : ZMod p)
    (ha : 2 * a.val ≤ p) :
    4 * (a.val : ℝ) / p ≤ ‖ZMod.stdAddChar a - 1‖ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp
  have hav : (2 : ℝ) * a.val ≤ p := by exact_mod_cast ha
  have hx : Real.pi * (a.val : ℝ) / p ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin (x := Real.pi * (a.val : ℝ) / p) (by positivity) hx
  rw [character_chord_eq_sine]
  have hi : (2 / Real.pi) * (Real.pi * (a.val : ℝ) / p) =
      2 * (a.val : ℝ) / p := by
    field_simp
  rw [hi] at hs
  convert mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

private theorem character_chord_neg (p : ℕ) [NeZero p] (a : ZMod p) :
    ‖ZMod.stdAddChar (-a) - 1‖ = ‖ZMod.stdAddChar a - 1‖ := by
  rw [AddChar.map_neg_eq_conj]
  simpa using norm_conj (ZMod.stdAddChar a - 1)

private theorem chord_reciprocal_le_half (p : ℕ) [NeZero p] (a : ZMod p)
    (ha : a ≠ 0) (hhalf : 2 * a.val ≤ p) :
    2 / ‖ZMod.stdAddChar a - 1‖ ≤ (p : ℝ) / (2 * (a.val : ℝ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hv : (0 : ℝ) < a.val := by exact_mod_cast ZMod.val_pos.mpr ha
  have hlo := character_chord_lower_half p a hhalf
  have hd : 0 < ‖ZMod.stdAddChar a - 1‖ := lt_of_lt_of_le (by positivity) hlo
  apply (div_le_iff₀ hd).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (a.val : ℝ))).2
  nlinarith [(div_le_iff₀ hp).1 hlo]

private theorem geometricMajorant_le_reciprocals (p Z : ℕ) [NeZero p]
    (a : ZMod p) (ha : a ≠ 0) :
    geometricMajorant p Z a ≤ (p : ℝ) / 2 *
      (((a.val : ℝ))⁻¹ + (((-a).val : ℝ))⁻¹) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hv : (0 : ℝ) < a.val := by exact_mod_cast ZMod.val_pos.mpr ha
  have hn : (0 : ℝ) < (-a).val := by
    exact_mod_cast ZMod.val_pos.mpr (neg_ne_zero.mpr ha)
  have htriv : geometricMajorant p Z a ≤ 2 / ‖ZMod.stdAddChar a - 1‖ := by
    simp only [geometricMajorant, if_neg ha]
    exact min_le_right _ _
  by_cases hh : 2 * a.val ≤ p
  · apply htriv.trans
    apply (chord_reciprocal_le_half p a ha hh).trans
    have heq : (p : ℝ) / (2 * (a.val : ℝ)) =
        (p : ℝ) / 2 * (a.val : ℝ)⁻¹ := by field_simp
    rw [heq]
    have hpos : 0 ≤ (p : ℝ) / 2 * ((-a).val : ℝ)⁻¹ := by positivity
    nlinarith
  · have hh' : 2 * (-a).val ≤ p := by
      rw [ZMod.neg_val, if_neg ha]
      have := ZMod.val_lt a
      omega
    rw [← character_chord_neg p a] at htriv
    apply htriv.trans
    apply (chord_reciprocal_le_half p (-a) (neg_ne_zero.mpr ha) hh').trans
    have heq : (p : ℝ) / (2 * ((-a).val : ℝ)) =
        (p : ℝ) / 2 * ((-a).val : ℝ)⁻¹ := by field_simp
    rw [heq]
    have hpos : 0 ≤ (p : ℝ) / 2 * (a.val : ℝ)⁻¹ := by positivity
    nlinarith

private theorem sum_reciprocal_residues (p : ℕ) [NeZero p] :
    (∑ a : ZMod p, (a.val : ℝ)⁻¹) = (harmonic (p - 1) : ℝ) := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change (∑ a : Fin (n + 1), (a.val : ℝ)⁻¹) = (harmonic n : ℝ)
    rw [← Finset.sum_range (fun j : ℕ ↦ (j : ℝ)⁻¹), sum_range_succ']
    simp [harmonic, Rat.cast_sum, Rat.cast_inv]

/-- The whole finite geometric majorant has harmonic rather than linear
average size. Both sides include the resonant residue. -/
private theorem sum_geometricMajorant_le (p Z : ℕ) [NeZero p] :
    (∑ a : ZMod p, geometricMajorant p Z a) ≤
      (Z : ℝ) + p * (harmonic (p - 1) : ℝ) := by
  have hpoint (a : ZMod p) : geometricMajorant p Z a ≤
      (if a = 0 then (Z : ℝ) else 0) +
      (p : ℝ) / 2 * ((a.val : ℝ)⁻¹ + ((-a).val : ℝ)⁻¹) := by
    by_cases ha : a = 0
    · simp [ha, geometricMajorant]
    · simpa [ha] using geometricMajorant_le_reciprocals p Z a ha
  have hneg : (∑ a : ZMod p, ((-a).val : ℝ)⁻¹) =
      ∑ a : ZMod p, (a.val : ℝ)⁻¹ := by
    simpa using Equiv.sum_comp (Equiv.neg (ZMod p)) (fun a : ZMod p ↦ (a.val : ℝ)⁻¹)
  calc
    _ ≤ ∑ a : ZMod p, ((if a = 0 then (Z : ℝ) else 0) +
        (p : ℝ) / 2 * ((a.val : ℝ)⁻¹ + ((-a).val : ℝ)⁻¹)) :=
      sum_le_sum (fun a _ ↦ hpoint a)
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, sum_add_distrib, hneg, sum_reciprocal_residues]
      simp
      ring

private theorem sum_differencing_majorants_le_harmonic (p Z : ℕ) [Fact p.Prime]
    (hp : 2 < p) (hZ : Z < p) :
    (∑ a : ZMod p, ((Z : ℝ) + 2 * ∑ h ∈ range Z,
      geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p)))) ≤
      (p : ℝ) * Z * (3 + 2 * (harmonic (p - 1) : ℝ)) := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro heq
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp heq
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
    omega
  have hperm (h : ℕ) (hh : h ∈ range Z) :
      (∑ a : ZMod p, geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p))) =
        ∑ a : ZMod p, geometricMajorant p Z a := by
    have hcast : ((h + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro heq
      have hdiv : p ∣ h + 1 := (ZMod.natCast_eq_zero_iff (h + 1) p).mp heq
      have := Nat.le_of_dvd (by omega : 0 < h + 1) hdiv
      have := mem_range.mp hh
      omega
    let c : ZMod p := 2 * ((h + 1 : ℕ) : ZMod p)
    have hc : c ≠ 0 := mul_ne_zero htwo hcast
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using
      Equiv.sum_comp (Equiv.mulRight₀ c hc) (geometricMajorant p Z)
  calc
    _ = (p : ℝ) * Z + 2 * Z * ∑ a : ZMod p, geometricMajorant p Z a := by
      rw [sum_add_distrib]
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      rw [← mul_sum, sum_comm]
      rw [sum_congr rfl (fun h hh ↦ hperm h hh)]
      simp
      ring
    _ ≤ (p : ℝ) * Z + 2 * Z * ((Z : ℝ) + p * (harmonic (p - 1) : ℝ)) := by
      gcongr
      exact sum_geometricMajorant_le p Z
    _ ≤ _ := by
      have hzp : (Z : ℝ) ≤ p := by exact_mod_cast hZ.le
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ Z by positivity) (sub_nonneg.mpr hzp)]

/-- The supremum of the squared quadratic-sum norm over every interval origin,
every unit complex linear twist and every length at most Z. -/
def quadraticMaximalEnergy (p Z : ℕ) [NeZero p] (a : ZMod p) : ℝ :=
  sSup {r : ℝ | ∃ m : ZMod p, ∃ w : ℂ, ‖w‖ = 1 ∧
    ∃ n : ℕ, n ≤ Z ∧ r = ‖∑ j ∈ range n, quadraticTerm a m w j‖ ^ 2}

/-- The averaged maximal incomplete quadratic energy has size p Z log p,
uniformly over interval origins and all linear twists, including twists
chosen independently for each quadratic coefficient. -/
theorem quadratic_maximal_energy_average_le (p Z : ℕ) [Fact p.Prime]
    (hp : 2 < p) (hZ : Z < p) :
    (∑ a : ZMod p, quadraticMaximalEnergy p Z a) ≤
      (p : ℝ) * Z * (5 + 2 * Real.log p) := by
  have hpoint (a : ZMod p) : quadraticMaximalEnergy p Z a ≤
      (Z : ℝ) + 2 * ∑ h ∈ range Z,
        geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p)) := by
    apply csSup_le
    · refine ⟨0, 0, 1, by simp, 0, Nat.zero_le _, ?_⟩
      simp
    · rintro r ⟨m, w, hw, n, hn, rfl⟩
      exact quadratic_energy_le_geometric_majorant a m hw n hn
  have hlog : Real.log (p - 1 : ℕ) ≤ Real.log p := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < p - 1)
    · exact_mod_cast Nat.sub_le p 1
  have hharm : (harmonic (p - 1) : ℝ) ≤ 1 + Real.log p :=
    (harmonic_le_one_add_log (p - 1)).trans (add_le_add le_rfl hlog)
  calc
    _ ≤ ∑ a : ZMod p, ((Z : ℝ) + 2 * ∑ h ∈ range Z,
        geometricMajorant p Z (2 * a * ((h + 1 : ℕ) : ZMod p))) :=
      sum_le_sum (fun a _ ↦ hpoint a)
    _ ≤ (p : ℝ) * Z * (3 + 2 * (harmonic (p - 1) : ℝ)) :=
      sum_differencing_majorants_le_harmonic p Z hp hZ
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (p : ℝ) * Z)
      linarith

end D5.S3.CharacterSums.QuadraticMidpointEnergy
