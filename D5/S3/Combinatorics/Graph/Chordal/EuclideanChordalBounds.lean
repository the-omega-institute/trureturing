/- GID: D5/S3/Combinatorics/Graph/Chordal/EuclideanChordalBounds
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-order Euclidean reconstruction bounds on chordal graphs. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.EuclideanChordalScalar
import D5.S3.Combinatorics.Graph.Chordal.EuclideanChordalGaussian
import Mathlib.MeasureTheory.Integral.Pi

compile_only_with_mathlib

/-! Omega original.

 # Global and finite-order Euclidean chordal reconstruction

Every finite chordal graph with `n ≥ 3` vertices admits reconstruction with constants
`((n-2)/n) (4/π)` in the Euclidean plane and `((n-2)/n) (3/2)` in Euclidean three-space.
The statements allow disconnected graphs, arbitrary antisymmetric gains, and arbitrary
nonnegative triangle-defect bounds.
-/

open MeasureTheory Real Set Module
open scoped RealInnerProductSpace

namespace SimpleGraph.EuclideanChordal

private theorem gaussian_half_moment (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * exp (-t ^ 2)) =
      (1 / 2 : ℝ) * Gamma (((k : ℝ) + 1) / 2) := by
  simpa only [rpow_natCast, rpow_two] using integral_rpow_mul_exp_neg_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (by norm_num) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)

private theorem gaussian_abs_moment : (∫ t : ℝ, |t| * exp (-t ^ 2)) = 1 := by
  have hh : (fun t : ℝ => |t| * exp (-t ^ 2)) =
      (fun t : ℝ => (fun r => r * exp (-r ^ 2)) |t|) := by
    ext t
    simp
  rw [hh, integral_comp_abs (f := fun r : ℝ => r * exp (-r ^ 2))]
  have hi := gaussian_half_moment 1
  norm_num [Gamma_one] at hi
  linarith

private theorem gaussian_coordinate_moment {n : ℕ} (i : Fin n) :
    (∫ y : EuclideanSpace ℝ (Fin n), |y i| * exp (-‖y‖ ^ 2)) =
      (√π) ^ (n - 1) := by
  have hh := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (fun y : EuclideanSpace ℝ (Fin n) => |y i| * exp (-‖y‖ ^ 2))
  rw [← hh]
  have heq (x : Fin n → ℝ) :
      |(WithLp.toLp 2 x) i| * exp (-‖WithLp.toLp 2 x‖ ^ 2) =
        ∏ j : Fin n, (if j = i then |x j| * exp (-x j ^ 2) else exp (-x j ^ 2)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [← Finset.sum_neg_distrib, exp_sum]
    rw [show (∏ j : Fin n, if j = i then |x j| * exp (-x j ^ 2) else exp (-x j ^ 2)) =
      (∏ j : Fin n, if j = i then |x j| else 1) * ∏ j : Fin n, exp (-x j ^ 2) by
        rw [← Finset.prod_mul_distrib]
        congr 1
        ext j
        split_ifs <;> simp]
    simp
  simp_rw [heq]
  rw [integral_fintype_prod_volume_eq_prod (fun (j : Fin n) (x : ℝ) =>
    if j = i then |x| * exp (-x ^ 2) else exp (-x ^ 2))]
  have hi (j : Fin n) :
      (∫ x : ℝ, if j = i then |x| * exp (-x ^ 2) else exp (-x ^ 2)) =
        if j = i then 1 else √π := by
    split_ifs
    · exact gaussian_abs_moment
    · simpa using integral_gaussian (1 : ℝ)
  simp_rw [hi]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true, one_mul]
  have hs : ∀ j ∈ Finset.univ.erase i, (if j = i then (1 : ℝ) else √π) = √π := by
    intro j hj
    simp [(Finset.mem_erase.mp hj).1]
  rw [Finset.prod_congr rfl hs, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

private theorem radialMoment_two : radialMoment (EuclideanSpace ℝ (Fin 2)) = π * √π / 2 := by
  rw [radialMoment, integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2))) (f := fun r : ℝ => r * exp (-r ^ 2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  have hi : (∫ t : ℝ in Ioi 0, t * (t * exp (-t ^ 2))) = √π / 4 := by
    have hh := gaussian_half_moment 2
    have hg : Gamma ((3 : ℝ) / 2) = (1 / 2 : ℝ) * √π := by
      convert Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
        norm_num [Gamma_one_half_eq]
    norm_num [hg] at hh
    have heq : (fun t : ℝ => t * (t * exp (-t ^ 2))) =
        (fun t : ℝ => t ^ 2 * exp (-t ^ 2)) := by funext t; ring
    rw [heq]
    linarith [hh]
  rw [hi]
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = π := by
    simp [Measure.real, pi_pos.le]
  rw [hv]
  ring

private theorem radialMoment_three : radialMoment (EuclideanSpace ℝ (Fin 3)) = 2 * π := by
  rw [radialMoment, integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3))) (f := fun r : ℝ => r * exp (-r ^ 2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  have hi : (∫ t : ℝ in Ioi 0, t ^ 2 * (t * exp (-t ^ 2))) = (1 / 2 : ℝ) := by
    have hh := gaussian_half_moment 3
    have hg : Gamma (2 : ℝ) = 1 := by
      simp
    norm_num [hg] at hh
    have heq : (fun t : ℝ => t ^ 2 * (t * exp (-t ^ 2))) =
        (fun t : ℝ => t ^ 3 * exp (-t ^ 2)) := by funext t; ring
    rw [heq]
    exact hh
  rw [hi]
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1) = π * 4 / 3 := by
    simp [Measure.real]
    positivity
  rw [hv]
  ring

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The full `n`-vertex planar bound, with no restriction on the clique number. -/
theorem exists_plane_potential (hG : G.IsChordal) (hn : 3 ≤ Fintype.card V)
    (g : V → V → EuclideanSpace ℝ (Fin 2)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ q : V → EuclideanSpace ℝ (Fin 2), ∀ a b, G.Adj a b →
      ‖g a b - (q b - q a)‖ ≤ orderFactor (Fintype.card V) * (4 / π) * δ := by
  obtain ⟨f, hf, ⟨B, hB, hgrowth⟩, herror⟩ :=
    exists_continuous_directional_potential hG hn g hδ hrev htri
  let e := EuclideanSpace.basisFun (Fin 2) ℝ 0
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0
  obtain ⟨q, hq⟩ := gaussian_averaging g f hf hB hgrowth G.Adj
    (mul_nonneg (orderFactor_nonneg hn) hδ)
    (fun y a b hab => by simpa [mul_assoc] using herror y a b hab) e he
    (by rw [radialMoment_two]; positivity)
  refine ⟨q, fun a b hab => ?_⟩
  have hh := hq a b hab
  have hK : (∫ y : EuclideanSpace ℝ (Fin 2), |⟪y, e⟫| * exp (-‖y‖ ^ 2)) = √π := by
    change (∫ y : EuclideanSpace ℝ (Fin 2),
      |⟪y, (EuclideanSpace.basisFun (Fin 2) ℝ) 0⟫| * exp (-‖y‖ ^ 2)) = √π
    simp_rw [EuclideanSpace.inner_basisFun_real]
    simpa using gaussian_coordinate_moment (0 : Fin 2)
  rw [hK, radialMoment_two] at hh
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hh
  have hc : (2 : ℝ) / (π * √π / 2) * √π = 4 / π := by
    field_simp; norm_num
  rw [hc] at hh
  simpa [norm_sub_rev, mul_comm, mul_left_comm, mul_assoc] using hh

/-- The full `n`-vertex three-dimensional bound, with no restriction on the clique number. -/
theorem exists_space_potential (hG : G.IsChordal) (hn : 3 ≤ Fintype.card V)
    (g : V → V → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ q : V → EuclideanSpace ℝ (Fin 3), ∀ a b, G.Adj a b →
      ‖g a b - (q b - q a)‖ ≤ orderFactor (Fintype.card V) * (3 / 2) * δ := by
  obtain ⟨f, hf, ⟨B, hB, hgrowth⟩, herror⟩ :=
    exists_continuous_directional_potential hG hn g hδ hrev htri
  let e := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0
  obtain ⟨q, hq⟩ := gaussian_averaging g f hf hB hgrowth G.Adj
    (mul_nonneg (orderFactor_nonneg hn) hδ)
    (fun y a b hab => by simpa [mul_assoc] using herror y a b hab) e he
    (by rw [radialMoment_three]; positivity)
  refine ⟨q, fun a b hab => ?_⟩
  have hh := hq a b hab
  have hK : (∫ y : EuclideanSpace ℝ (Fin 3), |⟪y, e⟫| * exp (-‖y‖ ^ 2)) = π := by
    change (∫ y : EuclideanSpace ℝ (Fin 3),
      |⟪y, (EuclideanSpace.basisFun (Fin 3) ℝ) 0⟫| * exp (-‖y‖ ^ 2)) = π
    simp_rw [EuclideanSpace.inner_basisFun_real]
    simpa [sq_sqrt pi_pos.le] using gaussian_coordinate_moment (0 : Fin 3)
  rw [hK, radialMoment_three] at hh
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hh
  have hc : (3 : ℝ) / (2 * π) * π = 3 / 2 := by field_simp
  rw [hc] at hh
  simpa [norm_sub_rev, mul_comm, mul_left_comm, mul_assoc] using hh

private theorem exact_potential_small {E : Type*} [AddCommGroup E]
    (hn : Fintype.card V ≤ 2) (g : V → V → E)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b) :
    ∃ q : V → E, ∀ a b, G.Adj a b → g a b = q b - q a := by
  have hA : G.IsAcyclic := IsAcyclic.of_card_le_two (by
    rw [ENat.card_eq_coe_fintype_card]
    exact_mod_cast hn)
  obtain ⟨p, hp⟩ := hA.exists_gain_potential
    (fun a b => Multiplicative.ofAdd (g a b)) (fun a b hab => hrev a b hab)
  refine ⟨fun v => Multiplicative.toAdd (p v), fun a b hab => ?_⟩
  have hh := congrArg Multiplicative.toAdd (hp a b hab)
  change g a b = -Multiplicative.toAdd (p a) + Multiplicative.toAdd (p b) at hh
  simpa [sub_eq_add_neg, add_comm] using hh

/-- The global planar coefficient `4/π`. -/
theorem exists_plane_potential_global (hG : G.IsChordal)
    (g : V → V → EuclideanSpace ℝ (Fin 2)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ q : V → EuclideanSpace ℝ (Fin 2), ∀ a b, G.Adj a b →
      ‖g a b - (q b - q a)‖ ≤ (4 / π) * δ := by
  by_cases hn : 3 ≤ Fintype.card V
  · obtain ⟨q, hq⟩ := exists_plane_potential hG hn g hδ hrev htri
    refine ⟨q, fun a b hab => (hq a b hab).trans ?_⟩
    have hh := mul_le_mul_of_nonneg_right (orderFactor_le_one hn)
      (mul_nonneg (by positivity : 0 ≤ (4 : ℝ) / π) hδ)
    simpa [mul_assoc] using hh
  · obtain ⟨q, hq⟩ := exact_potential_small (by omega) g hrev
    refine ⟨q, fun a b hab => ?_⟩
    rw [hq a b hab, sub_self, norm_zero]
    positivity

/-- The global three-dimensional coefficient `3/2`. -/
theorem exists_space_potential_global (hG : G.IsChordal)
    (g : V → V → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ q : V → EuclideanSpace ℝ (Fin 3), ∀ a b, G.Adj a b →
      ‖g a b - (q b - q a)‖ ≤ (3 / 2 : ℝ) * δ := by
  by_cases hn : 3 ≤ Fintype.card V
  · obtain ⟨q, hq⟩ := exists_space_potential hG hn g hδ hrev htri
    refine ⟨q, fun a b hab => (hq a b hab).trans ?_⟩
    have hh := mul_le_mul_of_nonneg_right (orderFactor_le_one hn)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hδ)
    simpa [mul_assoc] using hh
  · obtain ⟨q, hq⟩ := exact_potential_small (by omega) g hrev
    refine ⟨q, fun a b hab => ?_⟩
    rw [hq a b hab, sub_self, norm_zero]
    positivity

end SimpleGraph.EuclideanChordal
