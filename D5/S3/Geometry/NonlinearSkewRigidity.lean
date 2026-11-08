/- GID: D5/S3/Geometry/NonlinearSkewRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/NonlinearSkewRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.LinearMap]
   utility: none
   digest: A local acute patch forces rigidity of an initially arbitrary inner-product map. -/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic

/-! Rigidity from a product identity on an arbitrary real inner product space. -/

@[expose] public section
noncomputable section

open Set Metric Topology Filter
open scoped InnerProductSpace

namespace D5.S3.Geometry.NonlinearSkewRigidity

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem inner_open_separates {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    {q : W} (h : ∀ b ∈ U, ⟪b, q⟫_ℝ = 0) : q = 0 := by
  let L : W →ₗ[ℝ] ℝ := (innerSL ℝ q).toLinearMap
  have hsub : U ⊆ (L.ker : Set W) := by
    intro b hb
    change ⟪q, b⟫_ℝ = 0
    rw [real_inner_comm]
    exact h b hb
  have ht : L.ker = ⊤ :=
    L.ker.eq_top_of_nonempty_interior' (hne.mono (interior_maximal hsub hU))
  have hq : q ∈ L.ker := by rw [ht]; trivial
  exact inner_self_eq_zero.mp hq

private theorem inner_open_ext {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    {p q : W} (h : ∀ b ∈ U, ⟪b, p⟫_ℝ = ⟪b, q⟫_ℝ) : p = q := by
  apply sub_eq_zero.mp
  apply inner_open_separates hU hne
  intro b hb
  rw [inner_sub_right, h b hb, sub_self]

private theorem small_scale (w : W) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖t • w‖ < ε := by
  let t := ε / (‖w‖ + 1)
  have hd : 0 < ‖w‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hd
  have he : t * (‖w‖ + 1) = ε := div_mul_cancel₀ _ hd.ne'
  refine ⟨t, ht, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith

private theorem acute_ball {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {v : W} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
      r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hp : 0 < ⟪v, v⟫_ℝ - r ^ 2 * ‖v‖ * ‖v‖ := by
    rw [real_inner_self_eq_norm_sq]
    have hr2 : r ^ 2 < 1 := by nlinarith
    have := mul_pos (sub_pos.mpr hr2) (sq_pos_of_pos hvp)
    nlinarith only [this]
  have hc : Continuous (fun p : W × W =>
      ⟪p.1, p.2⟫_ℝ - r ^ 2 * ‖p.1‖ * ‖p.2‖) := by fun_prop
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hc.tendsto (v, v)).eventually (Ioi_mem_nhds hp))
  refine ⟨δ / 3, by positivity, ?_⟩
  intro b hb c hcc
  have hh : (b, c) ∈ ball (v, v) δ := by
    rw [← ball_prod_same]
    constructor
    · simpa only [show 3 * (δ / 3) = δ by ring] using hb
    · simpa only [show 3 * (δ / 3) = δ by ring] using hcc
  have := hball hh
  dsimp at this
  linarith

private theorem skew_of_acute {r : ℝ} (F : W → W)
    (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0)
    {b c : W} (hacute : r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ) :
    ⟪b, F c⟫_ℝ = -⟪F b, c⟫_ℝ := by
  have hbound := neg_le_abs (⟪F b, F c⟫_ℝ)
  have hcs := abs_real_inner_le_norm (F b) (F c)
  rw [hnorm, hnorm] at hcs
  have hfirst : 0 < ⟪b, c⟫_ℝ + ⟪F b, F c⟫_ℝ := by nlinarith
  have hsecond := (mul_eq_zero.mp (hprod b c)).resolve_left hfirst.ne'
  linarith

/-- A strict acute neighborhood gives an exact difference identity on the original carrier. -/
private theorem exists_acute_skew_difference {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (F : W → W) (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0)
    {v : W} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
        r ^ 2 * ‖b‖ * ‖c‖ < ⟪b, c⟫_ℝ) ∧
      (∀ b ∈ ball v (3 * ε), ∀ c ∈ ball v (3 * ε),
        ⟪b, F c⟫_ℝ = -⟪F b, c⟫_ℝ) ∧
      (∀ h, ‖h‖ < ε → ∀ b ∈ ball v ε,
        ⟪b, F (v + h) - F v⟫_ℝ = -⟪F b, h⟫_ℝ) := by
  obtain ⟨ε, hε, ha⟩ := acute_ball hr hr1 hv
  have hs := fun b hb c hc => skew_of_acute F hnorm hprod (ha b hb c hc)
  refine ⟨ε, hε, ha, hs, ?_⟩
  intro h hh b hb
  have hb' : b ∈ ball v (3 * ε) := ball_subset_ball (by linarith) hb
  have hv' : v ∈ ball v (3 * ε) := mem_ball_self (by linarith)
  have hsum : v + h ∈ ball v (3 * ε) := by
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hh.trans (by linarith : ε < 3 * ε)
  have h1 := hs b hb' (v + h) hsum
  have h2 := hs b hb' v hv'
  simp only [inner_sub_right, inner_add_right] at h1 h2 ⊢
  linarith

private theorem linear_open_zero (L : W →ₗ[ℝ] ℝ) {U : Set W}
    (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ b ∈ U, L b = 0) : L = 0 := by
  have ht : L.ker = ⊤ := L.ker.eq_top_of_nonempty_interior'
    (hne.mono (interior_maximal (by intro b hb; exact h b hb) hU))
  ext b
  have hb : b ∈ L.ker := by rw [ht]; trivial
  exact hb

/-- The local difference identity constructs a genuine linear map before imposing any
regularity on the original function. -/
private theorem exists_local_linear_model {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (F : W → W) (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0)
    {v : W} (hv : v ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : W →ₗ[ℝ] W,
      (∀ b ∈ ball v ε, F b = T b) ∧
      (∀ y z, ⟪T y, z⟫_ℝ = -⟪y, T z⟫_ℝ) := by
  classical
  obtain ⟨ε, hε, _, hs, hg⟩ := exists_acute_skew_difference hr hr1 F hnorm hprod hv
  have hne : (ball v ε).Nonempty := ⟨v, mem_ball_self hε⟩
  have hex (w : W) : ∃ q : W, ∀ b ∈ ball v ε, ⟪b, q⟫_ℝ = -⟪F b, w⟫_ℝ := by
    obtain ⟨t, ht, hsmall⟩ := small_scale w hε
    refine ⟨t⁻¹ • (F (v + t • w) - F v), ?_⟩
    intro b hb
    rw [real_inner_smul_right, hg _ hsmall b hb, real_inner_smul_right]
    field_simp
  choose f hf using hex
  let T : W →ₗ[ℝ] W :=
    { toFun := f
      map_add' := by
        intro x y
        apply inner_open_ext isOpen_ball hne
        intro b hb
        simp only [inner_add_right, hf _ b hb]
        ring
      map_smul' := by
        intro a x
        apply inner_open_ext isOpen_ball hne
        intro b hb
        simp only [RingHom.id_apply, real_inner_smul_right, hf _ b hb]
        ring }
  have hT (w b : W) (hb : b ∈ ball v ε) : ⟪b, T w⟫_ℝ = -⟪F b, w⟫_ℝ := hf w b hb
  have hlocal : ∀ b ∈ ball v ε, F b = T b := by
    intro c hc
    apply inner_open_ext isOpen_ball hne
    intro b hb
    rw [hT _ _ hb]
    exact hs b (ball_subset_ball (by linarith) hb) c (ball_subset_ball (by linarith) hc)
  refine ⟨ε, hε, T, hlocal, ?_⟩
  intro y z
  let L : W →ₗ[ℝ] ℝ := ((innerSL ℝ z).toLinearMap.comp T) +
    (innerSL ℝ (T z)).toLinearMap
  have hL : L = 0 := linear_open_zero L isOpen_ball hne (by
    intro b hb
    change ⟪z, T b⟫_ℝ + ⟪T z, b⟫_ℝ = 0
    rw [real_inner_comm (T b) z, real_inner_comm b (T z), hT _ _ hb, hlocal b hb]
    ring)
  have hh := congrArg (fun k : W →ₗ[ℝ] ℝ => k y) hL
  change ⟪z, T y⟫_ℝ + ⟪T z, y⟫_ℝ = 0 at hh
  rw [real_inner_comm (T y) z, real_inner_comm y (T z)] at hh
  linarith

private theorem norm_of_local_agreement {r : ℝ} (hr : 0 ≤ r) (F : W → W)
    (hnorm : ∀ y, ‖F y‖ = r * ‖y‖) (T : W →ₗ[ℝ] W)
    {v : W} {ε : ℝ} (hε : 0 < ε) (hlocal : ∀ b ∈ ball v ε, F b = T b) :
    ∀ w, ‖T w‖ = r * ‖w‖ := by
  have hn (b : W) (hb : b ∈ ball v ε) : ‖T b‖ ^ 2 = r ^ 2 * ‖b‖ ^ 2 := by
    rw [← hlocal b hb, hnorm]
    ring
  intro w
  obtain ⟨t, ht, hsmall⟩ := small_scale w hε
  have hp : v + t • w ∈ ball v ε := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hsmall
  have hm : v - t • w ∈ ball v ε := by
    simpa only [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hsmall
  have hplus := hn _ hp
  have hminus := hn _ hm
  have hzero := hn v (mem_ball_self hε)
  rw [map_add, norm_add_sq_real, norm_add_sq_real] at hplus
  rw [map_sub, norm_sub_sq_real, norm_sub_sq_real] at hminus
  have hsmallnorm : ‖T (t • w)‖ ^ 2 = r ^ 2 * ‖t • w‖ ^ 2 := by
    nlinarith only [hplus, hminus, hzero]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsmallnorm
  have he : t ^ 2 * ‖T w‖ ^ 2 = t ^ 2 * (r ^ 2 * ‖w‖ ^ 2) := by
    calc
      _ = r ^ 2 * (t ^ 2 * ‖w‖ ^ 2) := hsmallnorm
      _ = _ := by ring
  have hsq := mul_left_cancel₀ (pow_ne_zero 2 ht.ne') he
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  nlinarith only [hsq]

private theorem product_inner_open {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    {p q : W} (hp : p ≠ 0) (h : ∀ b ∈ U, ⟪b, p⟫_ℝ * ⟪b, q⟫_ℝ = 0) : q = 0 := by
  classical
  have hex : ∃ b ∈ U, ⟪b, p⟫_ℝ ≠ 0 := by
    by_contra! hn
    exact hp (inner_open_separates hU hne hn)
  obtain ⟨b, hb, hbp⟩ := hex
  have hopen : IsOpen {c : W | c ∈ U ∧ ⟪c, p⟫_ℝ ≠ 0} :=
    hU.inter (isOpen_ne.preimage (by fun_prop))
  apply inner_open_separates hopen ⟨b, hb, hbp⟩
  intro c hc
  exact (mul_eq_zero.mp (h c hc.1)).resolve_left hc.2

/-- The same original total map is real linear, skew, and squares to minus the
norm scale squared. No completeness or dimension assumption is required. -/
theorem nonlinear_skew_rigidity (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (F : W → W) (_horth : ∀ y, ⟪y, F y⟫_ℝ = 0)
    (hnorm : ∀ y, ‖F y‖ = r * ‖y‖)
    (hprod : ∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0) :
    (∀ y z, F (y + z) = F y + F z) ∧
    (∀ (a : ℝ) y, F (a • y) = a • F y) ∧
    (∀ y z, ⟪F y, z⟫_ℝ = -⟪y, F z⟫_ℝ) ∧
    (∀ y, F (F y) = -(r ^ 2) • y) := by
  classical
  rcases subsingleton_or_nontrivial W with hzero | hnonzero
  · let := hzero
    refine ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _, ?_,
      fun _ => Subsingleton.elim _ _⟩
    intro y z
    have hy : y = 0 := Subsingleton.elim _ _
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hy, hz]
  let := hnonzero
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨ε, hε, T, hlocal, hskew⟩ := exists_local_linear_model hr hr1 F hnorm hprod hv
  have hTnorm := norm_of_local_agreement hr.le F hnorm T hε hlocal
  have hF (z : W) : F z = T z := by
    by_cases hz : z = 0
    · subst z
      rw [map_zero]
      apply norm_eq_zero.mp
      simpa only [norm_zero, mul_zero] using hnorm (0 : W)
    have hnormal : z - T (F z) ≠ 0 := by
      intro he
      have heq : z = T (F z) := sub_eq_zero.mp he
      have hh : ‖z‖ = r ^ 2 * ‖z‖ := by
        calc
          ‖z‖ = ‖T (F z)‖ := congrArg norm heq
          _ = r ^ 2 * ‖z‖ := by rw [hTnorm, hnorm]; ring
      have hr2 : r ^ 2 < 1 := by nlinarith
      have hp := mul_pos (sub_pos.mpr hr2) (norm_pos_iff.mpr hz)
      nlinarith only [hh, hp]
    apply sub_eq_zero.mp
    apply product_inner_open isOpen_ball ⟨v, mem_ball_self hε⟩ hnormal
    intro b hb
    have hh := hprod b z
    rw [hlocal b hb, hskew b (F z), hskew b z] at hh
    simpa only [inner_sub_right, inner_add_right, inner_neg_right, sub_eq_add_neg] using hh
  have hnormsq (w : W) : ‖T w‖ ^ 2 = r ^ 2 * ‖w‖ ^ 2 := by
    rw [hTnorm]
    ring
  have hpolar (y z : W) : ⟪T y, T z⟫_ℝ = r ^ 2 * ⟪y, z⟫_ℝ := by
    have hh := norm_add_sq_real (T y) (T z)
    rw [← map_add, hnormsq, hnormsq, hnormsq, norm_add_sq_real] at hh
    nlinarith only [hh]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y z
    simp only [hF, map_add]
  · intro a y
    simp only [hF, map_smul]
  · intro y z
    simpa only [hF] using hskew y z
  · intro y
    simp only [hF]
    apply ext_inner_right ℝ
    intro z
    rw [hskew, hpolar, real_inner_smul_left]
    ring

end D5.S3.Geometry.NonlinearSkewRigidity
