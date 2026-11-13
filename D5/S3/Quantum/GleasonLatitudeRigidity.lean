/- GID: D5/S3/Quantum/GleasonLatitudeRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/GleasonLatitudeRigidity
   mirror-E: none(waiver:finite-dimensional-algebraic-proof)
   anchors: []
   utility: none
   digest: Bounded frame identities force affine latitude values. -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/notes/gleason1957measures.md. Authors: Zayn Blore.
Adapted from zblore/csd-lean4 at 07e2273b0180e69b4cb8f84e9d2200faa19fe07d.
Imports, source grouping and exact-supplier applications use the receiving Mathlib pin.
The adopted elementary real core (Sphere through General) follows Cooke, Keane,
Moran (1985), Math. Proc. Cambridge Philos. Soc. 98, 117–128.
Retire this transplant when the receiving pinned Mathlib supplies equivalent declarations.
-/

module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Basic
public import D5.S3.Quantum.GleasonFrameGeometry
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

namespace Gleason
theorem additive_bounded_linear (g : ℝ → ℝ) (hadd : ∀ s t : ℝ, g (s + t) = g s + g t)
    {M : ℝ} (hM : ∀ t : ℝ, |t| ≤ 1 → |g t| ≤ M) (x : ℝ) : g x = x * g 1 := by
  let G : ℝ →+ ℝ :=
    { toFun := g
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        linarith
      map_add' := hadd }
  have hc : Continuous G := G.continuous_of_isBounded_nhds_zero
    (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)) (by
      apply (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := M)).subset
      rintro _ ⟨t, ht, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      change |g t| ≤ M
      exact hM t (by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using ht))
  simpa [G] using map_real_smul G hc x 1
end Gleason
namespace Gleason
theorem eq_self_of_monotone_sum_eq_one {C : Set ℝ} (hC : C.Countable) (hC1 : C ⊆ Set.Ioo 0 1)
    {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hmono : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → b ∉ C →
      a < b → f a ≤ f b)
    (hsum : ∀ a b c : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      c ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → b ∉ C → c ∉ C → a + b + c = 1 → f a + f b + f c = 1) :
    ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → f a = a := by
  have h0C : (0 : ℝ) ∉ C := fun h => by simpa using (hC1 h).1
  have h1C : (1 : ℝ) ∉ C := fun h => by simpa using (hC1 h).2
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hf1 : f 1 = 1 := by
    have := hsum 1 0 0 h1I h0I h0I h1C h0C h0C (by ring)
    linarith
  set Ct : Set ℝ := ((fun p : ℝ × ℚ => p.1 / (p.2 : ℝ)) '' (C ×ˢ Set.univ)) ∪
    ((fun p : ℝ × ℚ => (1 - p.1) / (p.2 : ℝ)) '' (C ×ˢ Set.univ)) with hCt
  have hCt_count : Ct.Countable :=
    ((hC.prod Set.countable_univ).image _).union ((hC.prod Set.countable_univ).image _)
  have hIoo : ¬ (Set.Ioo (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  obtain ⟨a₀, ha₀I, ha₀⟩ : ∃ a₀, a₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ a₀ ∉ Ct := by
    by_contra hcon
    push Not at hcon
    exact hIoo (hCt_count.mono fun x hx => hcon x hx)
  have ha₀0 : 0 < a₀ := ha₀I.1
  have ha₀1 : a₀ < 1 := ha₀I.2
  have ha₀C : a₀ ∉ C := fun h => ha₀ (Or.inl ⟨(a₀, 1), ⟨h, Set.mem_univ _⟩, by simp⟩)
  have good : ∀ r : ℚ, 0 ≤ r → (r : ℝ) * a₀ ≤ 1 → (r : ℝ) * a₀ ∉ C ∧ 1 - (r : ℝ) * a₀ ∉ C := by
    intro r hr hr1
    constructor
    · intro hmem
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hmem
        exact h0C hmem
      have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      apply ha₀
      refine Or.inl ⟨((r : ℝ) * a₀, r), ⟨hmem, Set.mem_univ _⟩, ?_⟩
      simp only
      field_simp
    · intro hmem
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hmem
        exact h1C hmem
      have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
      apply ha₀
      refine Or.inr ⟨(1 - (r : ℝ) * a₀, r), ⟨hmem, Set.mem_univ _⟩, ?_⟩
      simp only
      field_simp
      ring
  have hadd : ∀ r r' : ℚ, 0 ≤ r → 0 ≤ r' → ((r + r' : ℚ) : ℝ) * a₀ ≤ 1 →
      f (((r + r' : ℚ) : ℝ) * a₀) = f ((r : ℝ) * a₀) + f ((r' : ℝ) * a₀) := by
    intro r r' hr hr' hrr'
    have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
    have hr'0 : (0 : ℝ) ≤ r' := by exact_mod_cast hr'
    have hs : ((r + r' : ℚ) : ℝ) = (r : ℝ) + r' := by push_cast; ring
    rw [hs] at hrr' ⊢
    have hra : (r : ℝ) * a₀ ≤ 1 := by nlinarith
    have hr'a : (r' : ℝ) * a₀ ≤ 1 := by nlinarith
    obtain ⟨g1, -⟩ := good r hr hra
    obtain ⟨g2, -⟩ := good r' hr' hr'a
    obtain ⟨g3, g4⟩ := good (r + r') (by positivity) (by rw [hs]; exact hrr')
    rw [hs] at g3 g4
    have e1 := hsum ((r : ℝ) * a₀) ((r' : ℝ) * a₀) (1 - ((r : ℝ) + r') * a₀)
      ⟨by positivity, hra⟩ ⟨by positivity, hr'a⟩ ⟨by linarith, by nlinarith⟩ g1 g2 g4 (by ring)
    have e2 := hsum (((r : ℝ) + r') * a₀) 0 (1 - ((r : ℝ) + r') * a₀)
      ⟨by positivity, hrr'⟩ h0I ⟨by linarith, by nlinarith⟩ g3 h0C g4 (by ring)
    linarith
  have hnat : ∀ (n : ℕ) (r : ℚ), 0 ≤ r → ((n * r : ℚ) : ℝ) * a₀ ≤ 1 →
      f (((n * r : ℚ) : ℝ) * a₀) = n * f ((r : ℝ) * a₀) := by
    intro n r hr
    induction n with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast hr
      have hcast : (((k + 1 : ℕ) * r : ℚ) : ℝ) = ((k * r + r : ℚ) : ℝ) := by push_cast; ring
      rw [hcast, hadd (k * r) r (by positivity) hr (by rw [← hcast]; exact hk)]
      have hk' : ((k * r : ℚ) : ℝ) * a₀ ≤ 1 := by
        have h1 : (((k + 1 : ℕ) * r : ℚ) : ℝ) = ((k * r : ℚ) : ℝ) + (r : ℝ) := by push_cast; ring
        rw [h1] at hk
        nlinarith
      rw [ih hk']
      push_cast
      ring
  have hrat : ∀ r : ℚ, 0 ≤ r → (r : ℝ) * a₀ ≤ 1 → f ((r : ℝ) * a₀) = r * f a₀ := by
    intro r hr hr1
    set n : ℕ := r.den with hn
    set m : ℕ := r.num.toNat with hm
    have hnpos : (0 : ℚ) < n := by rw [hn]; exact_mod_cast r.den_pos
    have hmr : (m : ℚ) = r.num := by
      rw [hm, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)]
    have hr_eq : r = m * (1 / n) := by
      rw [hmr, hn, mul_one_div, Rat.num_div_den]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcast1 : ((n * (1 / n : ℚ) : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    have hunit : f ((((1 : ℚ) / n : ℚ) : ℝ) * a₀) = f a₀ / n := by
      have h := hnat n (1 / n) (by positivity) (by rw [hcast1]; linarith)
      rw [hcast1, one_mul] at h
      field_simp
      linarith
    have h := hnat m (1 / n) (by positivity) (by rw [← hr_eq]; exact hr1)
    rw [← hr_eq] at h
    rw [h, hunit, hr_eq]
    push_cast
    field_simp
  have hfa₀ : 0 ≤ f a₀ := by
    have := hmono 0 a₀ h0I ⟨ha₀0.le, ha₀1.le⟩ h0C ha₀C ha₀0
    linarith
  set κ : ℝ := f a₀ / a₀ with hκ
  have hsq : ∀ a, a ∈ Set.Icc (0 : ℝ) 1 → a ∉ C → a < 1 → f a = κ * a := by
    intro a ha haC ha1
    have hfa0 : 0 < f a₀ + 1 := by linarith
    apply le_antisymm
    ·
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hlt : a / a₀ < min (1 / a₀) (a / a₀ + ε / (f a₀ + 1)) := by
        refine lt_min ?_ ?_
        · exact div_lt_div_of_pos_right ha1 ha₀0
        · have : 0 < ε / (f a₀ + 1) := by positivity
          linarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have hr1' : a < (r : ℝ) * a₀ := by
        rw [div_lt_iff₀ ha₀0] at hr1; linarith
      have hr2a : (r : ℝ) < 1 / a₀ := lt_of_lt_of_le hr2 (min_le_left _ _)
      have hr2b : (r : ℝ) < a / a₀ + ε / (f a₀ + 1) := lt_of_lt_of_le hr2 (min_le_right _ _)
      have hra1 : (r : ℝ) * a₀ < 1 := by
        rw [lt_div_iff₀ ha₀0] at hr2a; linarith
      have hr0 : (0 : ℝ) ≤ r := by
        have : 0 ≤ a / a₀ := div_nonneg ha.1 ha₀0.le
        linarith
      have hr0' : 0 ≤ r := by exact_mod_cast hr0
      obtain ⟨g1, -⟩ := good r hr0' hra1.le
      have hm := hmono a ((r : ℝ) * a₀) ha ⟨mul_nonneg hr0 ha₀0.le, hra1.le⟩ haC g1 hr1'
      rw [hrat r hr0' hra1.le] at hm
      calc f a ≤ (r : ℝ) * f a₀ := hm
        _ ≤ (a / a₀ + ε / (f a₀ + 1)) * f a₀ := by
          exact mul_le_mul_of_nonneg_right hr2b.le hfa₀
        _ = κ * a + ε * (f a₀ / (f a₀ + 1)) := by
          rw [hκ]; field_simp
        _ ≤ κ * a + ε := by
          have : f a₀ / (f a₀ + 1) ≤ 1 := by
            rw [div_le_one hfa0]; linarith
          nlinarith
    ·
      rcases eq_or_lt_of_le ha.1 with rfl | ha0
      · rw [hf0]; simp
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hlt : max 0 (a / a₀ - ε / (f a₀ + 1)) < a / a₀ := by
        refine max_lt (by positivity) ?_
        have : 0 < ε / (f a₀ + 1) := by positivity
        linarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have hr0 : (0 : ℝ) ≤ r := le_trans (le_max_left _ _) hr1.le
      have hr0' : 0 ≤ r := by exact_mod_cast hr0
      have hr1b : a / a₀ - ε / (f a₀ + 1) < r := lt_of_le_of_lt (le_max_right _ _) hr1
      have hra : (r : ℝ) * a₀ < a := by
        rw [lt_div_iff₀ ha₀0] at hr2; linarith
      have hra1 : (r : ℝ) * a₀ ≤ 1 := by linarith [ha.2]
      obtain ⟨g1, -⟩ := good r hr0' hra1
      have hm := hmono ((r : ℝ) * a₀) a ⟨mul_nonneg hr0 ha₀0.le, hra1⟩ ha g1 haC hra
      rw [hrat r hr0' hra1] at hm
      have key : κ * a - ε ≤ f a := by
        calc κ * a - ε ≤ κ * a - ε * (f a₀ / (f a₀ + 1)) := by
              have : f a₀ / (f a₀ + 1) ≤ 1 := by
                rw [div_le_one hfa0]; linarith
              nlinarith
          _ = (a / a₀ - ε / (f a₀ + 1)) * f a₀ := by
              rw [hκ]; field_simp
          _ ≤ (r : ℝ) * f a₀ := mul_le_mul_of_nonneg_right hr1b.le hfa₀
          _ ≤ f a := hm
      linarith
  have hκ1 : κ = 1 := by
    have hq : ((1 / 4 : ℚ) : ℝ) = 1 / 4 := by norm_num
    obtain ⟨g1, -⟩ := good (1 / 4) (by norm_num) (by rw [hq]; linarith)
    obtain ⟨-, g2⟩ := good (1 / 2) (by norm_num) (by norm_num; linarith)
    rw [hq] at g1
    rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at g2
    have e := hsum (1 / 4 * a₀) (1 / 4 * a₀) (1 - 1 / 2 * a₀) ⟨by positivity, by linarith⟩
      ⟨by positivity, by linarith⟩ ⟨by linarith, by linarith⟩ g1 g1 g2 (by ring)
    rw [hsq _ ⟨by positivity, by linarith⟩ g1 (by linarith),
      hsq _ ⟨by linarith, by linarith⟩ g2 (by linarith)] at e
    linarith
  intro a ha haC
  rcases eq_or_lt_of_le ha.2 with rfl | ha1
  · exact hf1
  · rw [hsq a ha haC ha1, hκ1, one_mul]
end Gleason
open Matrix Real
open scoped Matrix InnerProductSpace
namespace Gleason
section Latitude
variable {p s : EuclideanSpace ℝ (Fin 3)}
lemma latitude_nonneg (p s : EuclideanSpace ℝ (Fin 3)) : 0 ≤ latitude p s := sq_nonneg _
lemma latitude_le_one (hp : ‖p‖ = 1) (hs : ‖s‖ = 1) : latitude p s ≤ 1 := by
  rw [latitude, ← sq_abs]
  calc |⟪p, s⟫_ℝ| ^ 2 ≤ (‖p‖ * ‖s‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm p s) 2
    _ = 1 := by rw [hp, hs]; norm_num
lemma latitude_self (hp : ‖p‖ = 1) : latitude p p = 1 := by
  rw [latitude, real_inner_self_eq_norm_sq, hp]; norm_num
lemma latitude_neg (p s : EuclideanSpace ℝ (Fin 3)) : latitude p (-s) = latitude p s := by
  rw [latitude, latitude, inner_neg_right, neg_sq]
lemma pole_mem_northern (hp : ‖p‖ = 1) : p ∈ northern p :=
  ⟨hp, by rw [real_inner_self_eq_norm_sq, hp]; norm_num⟩
lemma eq_pole_of_latitude_eq_one (hp : ‖p‖ = 1) (hs : s ∈ northern p)
    (hl : latitude p s = 1) : s = p := by
  have h1 : ⟪p, s⟫_ℝ = 1 := by
    have h2 : (⟪p, s⟫_ℝ - 1) * (⟪p, s⟫_ℝ + 1) = 0 := by
      rw [latitude] at hl; linear_combination hl
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith [hs.2]
  have h3 : ‖p - s‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hp, hs.1, h1]; norm_num
  exact (sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))).symm
lemma mem_equator_of_latitude_eq_zero (hs : s ∈ northern p) (hl : latitude p s = 0) :
    s ∈ equator p :=
  ⟨hs.1, pow_eq_zero_iff two_ne_zero |>.mp hl⟩
lemma sub_inner_smul_ne_zero (hp : ‖p‖ = 1) (hs : s ∈ northern p) (hsp : s ≠ p) :
    p - ⟪p, s⟫_ℝ • s ≠ 0 := by
  intro h
  have hps : p = ⟪p, s⟫_ℝ • s := sub_eq_zero.mp h
  have h1 : ‖p‖ = ‖⟪p, s⟫_ℝ • s‖ := by conv_lhs => rw [hps]
  rw [hp, norm_smul, hs.1, mul_one, Real.norm_eq_abs, abs_of_nonneg hs.2] at h1
  rw [← h1, one_smul] at hps
  exact hsp hps.symm
lemma norm_coldest (hp : ‖p‖ = 1) (hs : s ∈ northern p) (hsp : s ≠ p) :
    ‖coldest p s‖ = 1 := by
  have h := norm_pos_iff.mpr (sub_inner_smul_ne_zero hp hs hsp)
  rw [coldest, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_cancel₀ h.ne']
lemma inner_pole_cross_coldest (p s : EuclideanSpace ℝ (Fin 3)) :
    ⟪p, cross s (coldest p s)⟫_ℝ = 0 := by
  have h : ⟪p, cross s (coldest p s)⟫_ℝ = ⟪coldest p s, cross p s⟫_ℝ := by
    rw [real_inner_eq_dotProduct, real_inner_eq_dotProduct, coe_cross, coe_cross,
      triple_product_permutation (⇑p) (⇑s) (⇑(coldest p s)),
      triple_product_permutation (⇑s) (⇑(coldest p s)) (⇑p)]
  rw [h, coldest, inner_smul_left, inner_sub_left, inner_smul_left, inner_cross_left,
    inner_cross_right]
  simp
end Latitude
namespace IsFrameFunction
variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W m : ℝ} {p : EuclideanSpace ℝ (Fin 3)}
theorem equator_le (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) : m ≤ f u := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht, hpt, hft⟩ := hf.exists_orthogonal_lt hM (m := f u)
    (fun δ hδ => ⟨u, hu, by linarith⟩) (ξ := m - f u) hp (by linarith)
  have := hE t ⟨ht, hpt⟩
  linarith
theorem equator_lt_add (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) {M ξ : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) (hpξ : M - ξ < f p)
    (hE : ∀ e ∈ equator p, f e = m) {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    m - ξ < f u := by
  by_contra hle
  push Not at hle
  obtain ⟨t, ht, hpt, hft⟩ := hf.exists_orthogonal_lt hM (m := f u)
    (fun δ hδ => ⟨u, hu, by linarith⟩) (ξ := ξ) hp hpξ
  have := hE t ⟨ht, hpt⟩
  linarith
theorem descent_le (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {s s' : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (hsp : s ≠ p)
    (hs' : s' ∈ descent p s) : f s' ≤ f s := by
  have hc1 : ‖coldest p s‖ = 1 := norm_coldest hp hs hsp
  have hsc : ⟪s, coldest p s⟫_ℝ = 0 := inner_coldest_self p hs.1
  have hs'c : ⟪s', coldest p s⟫_ℝ = 0 := hs'.2
  have hs'1 : ‖s'‖ = 1 := hs'.1.1
  have ht : ‖cross s (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs.1 hc1 hsc
  have ht' : ‖cross s' (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs'1 hc1 hs'c
  have h4 := hf.four_point hc1 hs.1 ht hs'1 ht' hsc
    (by rw [real_inner_comm]; exact inner_cross_right s _) hs'c
    (by rw [real_inner_comm]; exact inner_cross_right s' _) (inner_cross_left s _)
    (inner_cross_left s' _)
  have htE : f (cross s (coldest p s)) = m := hE _ ⟨ht, inner_pole_cross_coldest p s⟩
  have ht'm : m ≤ f (cross s' (coldest p s)) := hf.equator_le hp hM hE ht'
  linarith
theorem descent_lt_add (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) {M ξ : ℝ}
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ M) (hpξ : M - ξ < f p)
    (hE : ∀ e ∈ equator p, f e = m)
    {s s' : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (hsp : s ≠ p)
    (hs' : s' ∈ descent p s) : f s' - ξ < f s := by
  have hc1 : ‖coldest p s‖ = 1 := norm_coldest hp hs hsp
  have hsc : ⟪s, coldest p s⟫_ℝ = 0 := inner_coldest_self p hs.1
  have hs'c : ⟪s', coldest p s⟫_ℝ = 0 := hs'.2
  have hs'1 : ‖s'‖ = 1 := hs'.1.1
  have ht : ‖cross s (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs.1 hc1 hsc
  have ht' : ‖cross s' (coldest p s)‖ = 1 := norm_cross_of_orthonormal hs'1 hc1 hs'c
  have h4 := hf.four_point hc1 hs.1 ht hs'1 ht' hsc
    (by rw [real_inner_comm]; exact inner_cross_right s _) hs'c
    (by rw [real_inner_comm]; exact inner_cross_right s' _) (inner_cross_left s _)
    (inner_cross_left s' _)
  have htE : f (cross s (coldest p s)) = m := hE _ ⟨ht, inner_pole_cross_coldest p s⟩
  have ht'm : m - ξ < f (cross s' (coldest p s)) := hf.equator_lt_add hp hM hpξ hE ht'
  linarith
theorem le_of_latitude_lt (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m)
    {s t : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) (ht : t ∈ northern p)
    (hl : latitude p s < latitude p t) : f s ≤ f t := by
  rcases eq_or_ne t p with rfl | htp
  · exact hM s hs.1
  have hsp : s ≠ p := by
    rintro rfl
    have := latitude_le_one hp ht.1
    rw [latitude_self hp] at hl
    linarith
  obtain ⟨n, c, -, hc⟩ := exists_descent_chain hp ht htp hs hsp hl
  have key : ∀ i, i ≤ n → f (c i) ≤ f (c 0) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      exact (hf.descent_le hp hM hE (hc.mem k (by omega)).1 (hc.mem k (by omega)).2
        (hc.step k (by omega))).trans (ih (by omega))
  have := key n le_rfl
  rwa [hc.head, hc.last] at this
end IsFrameFunction
lemma exists_frame_of_latitudes {p : EuclideanSpace ℝ (Fin 3)} (hp : ‖p‖ = 1) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    ∃ q : Fin 3 → EuclideanSpace ℝ (Fin 3), Orthonormal ℝ q ∧ (∀ j, q j ∈ northern p) ∧
      latitude p (q 0) = a ∧ latitude p (q 1) = b ∧ latitude p (q 2) = c := by
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      ⇑B = ![p, e₁, cross p e₁] :=
    ⟨orthonormalBasisOfTriple (orthonormal_cross hp he₁ hpe₁), coe_orthonormalBasisOfTriple _⟩
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 3),
      v = WithLp.toLp 2 ![Real.sqrt a, Real.sqrt b, Real.sqrt c] := ⟨_, rfl⟩
  have hv1 : ‖v‖ = 1 := by
    rw [hv, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sq_sqrt hc, habc]
  obtain ⟨w, hw, hvw⟩ := exists_unit_orthogonal v
  obtain ⟨V, hV⟩ : ∃ V : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      ⇑V = ![v, w, cross v w] :=
    ⟨orthonormalBasisOfTriple (orthonormal_cross hv1 hw hvw), coe_orthonormalBasisOfTriple _⟩
  have hV0 : V 0 = v := by rw [hV]; rfl
  have hB0 : B 0 = p := by rw [hB]; rfl
  have hinner : ∀ j k : Fin 3,
      ⟪∑ i, (V i) j • B i, ∑ i, (V i) k • B i⟫_ℝ = if j = k then 1 else 0 := by
    intro j k
    rw [B.orthonormal.inner_sum]
    have h := congrFun (congrFun (colMatrix_mul_conjTranspose_of_orthonormalBasis V) j) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colMatrix, Matrix.of_apply, star_trivial,
      Matrix.one_apply] at h
    simpa [RCLike.conj_to_real] using h
  have hq : Orthonormal ℝ fun j : Fin 3 => ∑ i, (V i) j • B i := orthonormal_iff_ite.mpr hinner
  have hpq : ∀ j, ⟪p, ∑ i, (V i) j • B i⟫_ℝ = (V 0) j := by
    intro j
    rw [← hB0]
    exact B.orthonormal.inner_right_sum _ (Finset.mem_univ 0)
  have hv0 : ∀ j, 0 ≤ (V 0) j := by
    intro j
    rw [hV0, hv]
    fin_cases j <;> simp [Real.sqrt_nonneg]
  refine ⟨fun j => ∑ i, (V i) j • B i, hq, fun j => ⟨hq.norm_eq_one j, ?_⟩, ?_, ?_, ?_⟩
  · rw [hpq]; exact hv0 j
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt ha]
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt hb]
  · rw [latitude, hpq, hV0, hv]; simp [Real.sq_sqrt hc]
def parallelValues (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ) (l : ℝ) :
    Set ℝ :=
  f '' {s | s ∈ northern p ∧ latitude p s = l}
noncomputable def parallelSup (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (l : ℝ) : ℝ :=
  sSup (parallelValues p f l)
noncomputable def parallelInf (p : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (l : ℝ) : ℝ :=
  sInf (parallelValues p f l)
section Parallels
variable {p : EuclideanSpace ℝ (Fin 3)} {f : EuclideanSpace ℝ (Fin 3) → ℝ} {l : ℝ}
lemma mem_parallelValues {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    f s ∈ parallelValues p f (latitude p s) :=
  ⟨s, ⟨hs, rfl⟩, rfl⟩
lemma parallelValues_nonempty (hp : ‖p‖ = 1) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    (parallelValues p f l).Nonempty := by
  obtain ⟨q, -, hqN, hq0, -, -⟩ := exists_frame_of_latitudes hp hl.1
    (by linarith [hl.2] : 0 ≤ 1 - l) le_rfl (by ring)
  exact ⟨f (q 0), q 0, ⟨hqN 0, hq0⟩, rfl⟩
lemma bddAbove_parallelValues (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) :
    BddAbove (parallelValues p f l) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h1 s hs.1
lemma bddBelow_parallelValues (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u) :
    BddBelow (parallelValues p f l) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h0 s hs.1
lemma le_parallelSup (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    f s ≤ parallelSup p f (latitude p s) :=
  le_csSup (bddAbove_parallelValues h1) (mem_parallelValues hs)
lemma parallelInf_le (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    {s : EuclideanSpace ℝ (Fin 3)} (hs : s ∈ northern p) :
    parallelInf p f (latitude p s) ≤ f s :=
  csInf_le (bddBelow_parallelValues h0) (mem_parallelValues hs)
lemma parallelSup_le_one (hp : ‖p‖ = 1) (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1)
    (hl : l ∈ Set.Icc (0 : ℝ) 1) : parallelSup p f l ≤ 1 := by
  refine csSup_le (parallelValues_nonempty hp hl) ?_
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h1 s hs.1
lemma parallelInf_nonneg (hp : ‖p‖ = 1)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ parallelInf p f l := by
  refine le_csInf (parallelValues_nonempty hp hl) ?_
  rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
  exact h0 s hs.1
lemma parallelInf_le_parallelSup (hp : ‖p‖ = 1)
    (h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u)
    (h1 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    parallelInf p f l ≤ parallelSup p f l := by
  obtain ⟨x, hx⟩ := parallelValues_nonempty (f := f) hp hl
  exact (csInf_le (bddBelow_parallelValues h0) hx).trans (le_csSup (bddAbove_parallelValues h1) hx)
lemma parallelSup_le_parallelInf (hp : ‖p‖ = 1)
    (hmono : ∀ s t : EuclideanSpace ℝ (Fin 3), s ∈ northern p → t ∈ northern p →
      latitude p s < latitude p t → f s ≤ f t)
    {l' : ℝ} (hl : 0 ≤ l) (hl' : l' ≤ 1) (hll' : l < l') :
    parallelSup p f l ≤ parallelInf p f l' := by
  refine csSup_le (parallelValues_nonempty hp ⟨hl, by linarith⟩) ?_
  rintro _ ⟨s, ⟨hs, hsl⟩, rfl⟩
  refine le_csInf (parallelValues_nonempty hp ⟨by linarith, hl'⟩) ?_
  rintro _ ⟨t, ⟨ht, htl⟩, rfl⟩
  exact hmono s t hs ht (by rw [hsl, htl]; exact hll')
lemma parallelValues_zero (hE : ∀ e ∈ equator p, f e = 0) :
    parallelValues p f 0 = {0} := by
  obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
  ext x
  constructor
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    exact hE s (mem_equator_of_latitude_eq_zero hs hl)
  · rintro rfl
    exact ⟨e₁, ⟨⟨he₁, hpe₁.ge⟩, by rw [latitude, hpe₁]; norm_num⟩, hE e₁ ⟨he₁, hpe₁⟩⟩
lemma parallelValues_one (hp : ‖p‖ = 1) : parallelValues p f 1 = {f p} := by
  ext x
  constructor
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    rw [eq_pole_of_latitude_eq_one hp hs hl]
    rfl
  · rintro rfl
    exact ⟨p, ⟨pole_mem_northern hp, latitude_self hp⟩, rfl⟩
lemma parallelSup_zero (hE : ∀ e ∈ equator p, f e = 0) : parallelSup p f 0 = 0 := by
  rw [parallelSup, parallelValues_zero hE, csSup_singleton]
lemma parallelInf_zero (hE : ∀ e ∈ equator p, f e = 0) : parallelInf p f 0 = 0 := by
  rw [parallelInf, parallelValues_zero hE, csInf_singleton]
lemma parallelSup_one (hp : ‖p‖ = 1) : parallelSup p f 1 = f p := by
  rw [parallelSup, parallelValues_one hp, csSup_singleton]
lemma parallelInf_one (hp : ‖p‖ = 1) : parallelInf p f 1 = f p := by
  rw [parallelInf, parallelValues_one hp, csInf_singleton]
end Parallels
namespace IsFrameFunction
variable {f : EuclideanSpace ℝ (Fin 3) → ℝ} {W m : ℝ} {p : EuclideanSpace ℝ (Fin 3)}
theorem eq_latitude_of_normalised (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1) (hfp : f p = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ 1) (hE : ∀ e ∈ equator p, f e = 0) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → f s = latitude p s := by
  have hMp : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p := fun u hu => hfp ▸ hM u hu
  have h0 : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → 0 ≤ f u :=
    fun u hu => hf.equator_le hp hMp hE hu
  have hmono : ∀ s t : EuclideanSpace ℝ (Fin 3), s ∈ northern p → t ∈ northern p →
      latitude p s < latitude p t → f s ≤ f t :=
    fun s t hs ht hl => hf.le_of_latitude_lt hp hMp hE hs ht hl
  have hW : W = 1 := by
    obtain ⟨e₁, he₁, hpe₁⟩ := exists_unit_orthogonal p
    have h := hf.eq_of_triple (orthonormal_cross hp he₁ hpe₁)
    rw [hfp, hE e₁ ⟨he₁, hpe₁⟩,
      hE (cross p e₁) ⟨norm_cross_of_orthonormal hp he₁ hpe₁, inner_cross_left p e₁⟩] at h
    linarith
  obtain ⟨C, hC⟩ : ∃ C : Set ℝ,
      C = {l | l ∈ Set.Ioo (0 : ℝ) 1 ∧ parallelInf p f l < parallelSup p f l} := ⟨_, rfl⟩
  have hCsub : C ⊆ Set.Ioo 0 1 := by rw [hC]; exact fun l hl => hl.1
  have hagree : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ∉ C →
      parallelInf p f l = parallelSup p f l := by
    intro l hl hlC
    rcases eq_or_lt_of_le hl.1 with rfl | hl0
    · rw [parallelInf_zero hE, parallelSup_zero hE]
    rcases eq_or_lt_of_le hl.2 with rfl | hl1
    · rw [parallelInf_one hp, parallelSup_one hp]
    refine le_antisymm (parallelInf_le_parallelSup hp h0 hM hl) ?_
    by_contra hlt
    push Not at hlt
    exact hlC (by rw [hC]; exact ⟨⟨hl0, hl1⟩, hlt⟩)
  have hCc : C.Countable := by
    have hdisj : C.PairwiseDisjoint fun l => Set.Ioo (parallelInf p f l) (parallelSup p f l) := by
      intro l hl l' hl' hne
      have hl2 := hCsub hl
      have hl'2 := hCsub hl'
      rcases lt_or_gt_of_ne hne with h | h
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        have := parallelSup_le_parallelInf hp hmono hl2.1.le hl'2.2.le h
        linarith [hx.2, hx'.1]
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        have := parallelSup_le_parallelInf hp hmono hl'2.1.le hl2.2.le h
        linarith [hx.1, hx'.2]
    exact hdisj.countable_of_isOpen (fun l _ => isOpen_Ioo)
      (fun l hl => Set.nonempty_Ioo.mpr (by rw [hC] at hl; exact hl.2))
  have hwarm : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ∉ C → parallelSup p f l = l := by
    refine eq_self_of_monotone_sum_eq_one hCc hCsub (parallelSup_zero hE) ?_ ?_
    · intro a b ha hb _ _ hab
      exact (parallelSup_le_parallelInf hp hmono ha.1 hb.2 hab).trans
        (parallelInf_le_parallelSup hp h0 hM hb)
    · intro a b c ha hb hc haC hbC hcC habc
      obtain ⟨q, hq, hqN, hqa, hqb, hqc⟩ := exists_frame_of_latitudes hp ha.1 hb.1 hc.1 habc
      have hsum := hf.sum_triple hq
      rw [Fin.sum_univ_three, hW] at hsum
      have e0 : f (q 0) = parallelSup p f a := by
        have h1 := le_parallelSup hM (hqN 0)
        have h2 := parallelInf_le h0 (hqN 0)
        rw [hqa] at h1 h2
        rw [hagree a ha haC] at h2
        exact le_antisymm h1 h2
      have e1 : f (q 1) = parallelSup p f b := by
        have h1 := le_parallelSup hM (hqN 1)
        have h2 := parallelInf_le h0 (hqN 1)
        rw [hqb] at h1 h2
        rw [hagree b hb hbC] at h2
        exact le_antisymm h1 h2
      have e2 : f (q 2) = parallelSup p f c := by
        have h1 := le_parallelSup hM (hqN 2)
        have h2 := parallelInf_le h0 (hqN 2)
        rw [hqc] at h1 h2
        rw [hagree c hc hcC] at h2
        exact le_antisymm h1 h2
      linarith
  have hsup_le : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → parallelSup p f l ≤ l := by
    intro l hl
    rcases eq_or_lt_of_le hl.2 with rfl | hl1
    · exact parallelSup_le_one hp hM ⟨zero_le_one, le_rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l', hl'⟩ : ∃ l', l' ∈ Set.Ioo l (min 1 (l + ε)) ∧ l' ∉ C := by
      by_contra hcon
      push Not at hcon
      have h := hCc.mono fun x hx => hcon x hx
      rw [Cardinal.Real.Ioo_countable_iff] at h
      exact absurd h (not_le.mpr (lt_min hl1 (by linarith)))
    have hl'I : l' ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hl.1.trans hl'.1.1.le, hl'.1.2.le.trans (min_le_left _ _)⟩
    calc parallelSup p f l ≤ parallelInf p f l' :=
          parallelSup_le_parallelInf hp hmono hl.1 hl'I.2 hl'.1.1
      _ = parallelSup p f l' := hagree l' hl'I hl'.2
      _ = l' := hwarm l' hl'I hl'.2
      _ ≤ l + ε := hl'.1.2.le.trans (min_le_right _ _)
  have hle_inf : ∀ l, l ∈ Set.Icc (0 : ℝ) 1 → l ≤ parallelInf p f l := by
    intro l hl
    rcases eq_or_lt_of_le hl.1 with rfl | hl0
    · exact parallelInf_nonneg hp h0 ⟨le_rfl, zero_le_one⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨l'', hl''⟩ : ∃ l'', l'' ∈ Set.Ioo (max 0 (l - ε)) l ∧ l'' ∉ C := by
      by_contra hcon
      push Not at hcon
      have h := hCc.mono fun x hx => hcon x hx
      rw [Cardinal.Real.Ioo_countable_iff] at h
      exact absurd h (not_le.mpr (max_lt hl0 (by linarith)))
    have hl''I : l'' ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(le_max_left _ _).trans hl''.1.1.le, hl''.1.2.le.trans hl.2⟩
    have h1 : l - ε < l'' := lt_of_le_of_lt (le_max_right _ _) hl''.1.1
    have h2 := parallelSup_le_parallelInf hp hmono hl''I.1 hl.2 hl''.1.2
    rw [hwarm l'' hl''I hl''.2] at h2
    linarith
  have hN : ∀ s : EuclideanSpace ℝ (Fin 3), s ∈ northern p → f s = latitude p s := by
    intro s hs
    have hl : latitude p s ∈ Set.Icc (0 : ℝ) 1 := ⟨latitude_nonneg p s, latitude_le_one hp hs.1⟩
    exact le_antisymm ((le_parallelSup hM hs).trans (hsup_le _ hl))
      ((hle_inf _ hl).trans (parallelInf_le h0 hs))
  intro s hs
  rcases le_or_gt 0 ⟪p, s⟫_ℝ with h | h
  · exact hN s ⟨hs, h⟩
  · have := hN (-s) ⟨by rw [norm_neg, hs], by rw [inner_neg_right]; linarith⟩
    rwa [hf.neg_apply hs, latitude_neg] at this
theorem eq_add_mul_latitude (hf : IsFrameFunction ℝ f W) (hp : ‖p‖ = 1)
    (hM : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → f u ≤ f p) (hE : ∀ e ∈ equator p, f e = m) :
    ∀ s : EuclideanSpace ℝ (Fin 3), ‖s‖ = 1 → f s = m + (f p - m) * latitude p s := by
  have hmin : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 → m ≤ f u :=
    fun u hu => hf.equator_le hp hM hE hu
  rcases eq_or_lt_of_le (hmin p hp) with hmp | hmp
  · intro s hs
    have h1 := hM s hs
    have h2 := hmin s hs
    rw [← hmp, sub_self, zero_mul, add_zero]
    linarith
  have hne : f p - m ≠ 0 := by linarith
  have hpos : 0 < f p - m := by linarith
  have hg : IsFrameFunction ℝ (fun u => (f p - m)⁻¹ * (f u - m)) ((f p - m)⁻¹ * (W - 3 * m)) := by
    have := (hf.sub (IsFrameFunction.const (𝕜 := ℝ) (n := 3) m)).smul (f p - m)⁻¹
    simpa using this
  have key := hg.eq_latitude_of_normalised hp (by simp [inv_mul_cancel₀ hne])
    (fun u hu => by
      rw [inv_mul_le_iff₀ hpos, mul_one]
      linarith [hM u hu])
    (fun e he => by simp [hE e he])
  intro s hs
  have h := key s hs
  rw [← h]
  field_simp
  ring
end IsFrameFunction
end Gleason

end
