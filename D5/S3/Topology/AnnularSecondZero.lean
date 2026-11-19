/- GID: D5/S3/Topology/AnnularSecondZero
   generality: G
   mirror-B: D5/B/S3/Topology/AnnularSecondZero
   mirror-E: none(waiver:abstract-topology-without-experimental-evidence)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Equiv]
   utility: none
   digest: A regular zero forces another zero under constant-exterior or annular boundary data. -/

import D5.S3.Topology.TauCeti.AlgebraicTopology.Sphere.Contractible
import D5.S3.Topology.TauCeti.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Complex.Basic

/-! A local invertible real derivative and a constant exterior force a second zero.
The obstruction is the noncontractibility of the unit sphere. -/

set_option autoImplicit false

open Metric NormedSpace Set Filter
open scoped Topology unitInterval

noncomputable section

namespace D5.S3.Topology.AnnularSecondZero

private theorem second_zero_of_identity_estimate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : E → E) (a c : E) (M ε : ℝ) (hp : Continuous p) (hc : c ≠ 0)
    (hext : ∀ x, M ≤ ‖x‖ → p x = c) (hε : 0 < ε)
    (herr : ∀ h, ‖h‖ ≤ ε → ‖p (a + h) - h‖ ≤ ‖h‖ / 2) :
    ∃ b, b ≠ a ∧ p b = 0 := by
  classical
  by_contra! huniq
  have hp0 : ∀ x, x ≠ a → p x ≠ 0 := fun x hx => huniq x hx
  let S := sphere (0 : E) 1
  have hu : ∀ u : S, ‖(u : E)‖ = 1 := fun u => mem_sphere_zero_iff_norm.mp u.property
  let v : C(S, E) := ⟨fun u => ε • (u : E), continuous_const.smul continuous_subtype_val⟩
  let w : C(S, E) := ⟨fun u => p (a + ε • (u : E)),
    hp.comp (continuous_const.add (continuous_const.smul continuous_subtype_val))⟩
  have hvnorm : ∀ u : S, ‖v u‖ = ε := by
    intro u
    simp [v, norm_smul, hu u, abs_of_pos hε]
  have hseg : ∀ z : I × S, (1 - (z.1 : ℝ)) • v z.2 + (z.1 : ℝ) • w z.2 ≠ 0 := by
    rintro ⟨t, u⟩ hz
    have he := herr (v u) (le_of_eq (hvnorm u))
    change ‖w u - v u‖ ≤ ‖v u‖ / 2 at he
    have hid : (1 - (t : ℝ)) • v u + (t : ℝ) • w u - v u =
        (t : ℝ) • (w u - v u) := by module
    have hbound : ‖(1 - (t : ℝ)) • v u + (t : ℝ) • w u - v u‖ ≤ ε / 2 := by
      rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      calc
        (t : ℝ) * ‖w u - v u‖ ≤ 1 * ‖w u - v u‖ :=
          mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
        _ ≤ ε / 2 := by simpa [hvnorm u] using he
    rw [hz, zero_sub, norm_neg, hvnorm u] at hbound
    linarith
  let K := TauCeti.normalizeToSphere
    (fun z : I × S => (1 - (z.1 : ℝ)) • v z.2 + (z.1 : ℝ) • w z.2)
    (by fun_prop) hseg
  have hw0 : ∀ u : S, w u ≠ 0 := by
    intro u
    have := hseg (1, u)
    simpa using this
  let W := TauCeti.normalizeToSphere w w.continuous hw0
  let K' : (ContinuousMap.id S).Homotopy W :=
    { toContinuousMap := K
      map_zero_left := by
        intro u
        apply Subtype.ext
        change normalize ((1 - (0 : ℝ)) • v u + (0 : ℝ) • w u) = (u : E)
        simp only [sub_zero, one_smul, zero_smul, add_zero]
        exact (normalize_smul_of_pos hε (u : E)).trans
          (normalize_eq_self_of_norm_eq_one (hu u))
      map_one_left := by
        intro u
        apply Subtype.ext
        change normalize ((1 - (1 : ℝ)) • v u + (1 : ℝ) • w u) = normalize (w u)
        simp }
  let T := max M 0 + ‖a‖ + ε + 1
  have hT : ε < T := by
    dsimp [T]
    have := le_max_right M 0
    have := norm_nonneg a
    linarith
  let s : I → ℝ := fun t => (1 - (t : ℝ)) * ε + (t : ℝ) * T
  have hs : ∀ t, 0 < s t := by
    intro t
    have ht0 := t.property.1
    have ht1 := t.property.2
    dsimp [s]
    nlinarith
  let F : I × S → E := fun z => p (a + s z.1 • (z.2 : E))
  have hF : Continuous F := by dsimp [F, s]; fun_prop
  have hF0 : ∀ z, F z ≠ 0 := by
    intro z
    apply hp0
    intro heq
    have hzero : s z.1 • (z.2 : E) = 0 := by simpa using heq
    have := norm_smul (s z.1) (z.2 : E)
    rw [hzero, norm_zero, hu z.2, mul_one, Real.norm_eq_abs, abs_of_pos (hs z.1)] at this
    linarith [hs z.1]
  let H := TauCeti.normalizeToSphere F hF hF0
  let C : S := ⟨normalize c, mem_sphere_zero_iff_norm.mpr (norm_normalize hc)⟩
  have hlarge : ∀ u : S, p (a + T • (u : E)) = c := by
    intro u
    apply hext
    have hb := norm_sub_le (a + T • (u : E)) a
    have heq : a + T • (u : E) - a = T • (u : E) := by abel
    rw [heq, norm_smul, hu u, mul_one, Real.norm_eq_abs,
      abs_of_pos (lt_trans hε hT)] at hb
    have := le_max_left M 0
    dsimp [T] at hb
    linarith
  let H' : W.Homotopy (ContinuousMap.const S C) :=
    { toContinuousMap := H
      map_zero_left := by
        intro u
        apply Subtype.ext
        change normalize (p (a + s 0 • (u : E))) = normalize (w u)
        simp [s, w]
      map_one_left := by
        intro u
        apply Subtype.ext
        change normalize (p (a + s 1 • (u : E))) = normalize c
        simpa [s] using congrArg (NormedSpace.normalize : E → E) (hlarge u) }
  exact TauCeti.not_contractibleSpace_sphere
    ((contractible_iff_id_nullhomotopic S).mpr ⟨C, ⟨K'.trans H'⟩⟩)

/-- A continuous map constant outside a bounded set cannot have exactly one zero at which
its ordinary real derivative is an invertible continuous linear map. -/
theorem constantExterior_second_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (q : E → E) (a c : E) (M : ℝ) (L : E ≃L[ℝ] E)
    (hq : Continuous q) (hc : c ≠ 0) (hext : ∀ x, M ≤ ‖x‖ → q x = c)
    (ha : q a = 0) (hd : HasFDerivAt q (L : E →L[ℝ] E) a) :
    ∃ b, b ≠ a ∧ q b = 0 := by
  let p : E → E := fun x => L.symm (q x)
  have hp : Continuous p := L.symm.continuous.comp hq
  have hpa : p a = 0 := by simp [p, ha]
  have hpd : HasFDerivAt p (ContinuousLinearMap.id ℝ E) a := by
    simpa [p, Function.comp_def] using L.symm.hasFDerivAt.comp a hd
  have hevent : ∀ᶠ h in 𝓝 (0 : E), ‖p (a + h) - h‖ ≤ ‖h‖ / 2 := by
    simpa [hpa, div_eq_mul_inv, mul_comm] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp hpd).bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨b, hba, hb⟩ := second_zero_of_identity_estimate p a (L.symm c) M (δ / 2) hp
    (by simpa using hc) (fun x hx => by simp [p, hext x hx]) (by linarith)
    (fun h hh => hball (by
      rw [mem_ball, dist_zero_right]
      linarith))
  refine ⟨b, hba, ?_⟩
  exact L.symm.injective (by simpa [p] using hb)

private def cutoff (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem cutoff_bounds (t : ℝ) : 0 ≤ cutoff t ∧ cutoff t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem cutoff_eq_zero {t : ℝ} (ht : t ≤ 0) : cutoff t = 0 := by
  exact max_eq_left (le_trans (min_le_right _ _) ht)

private theorem cutoff_eq_one {t : ℝ} (ht : 1 ≤ t) : cutoff t = 1 := by
  simp [cutoff, min_eq_left ht]

private def collarWeight (r R : ℝ) (z : ℂ) : ℝ :=
  cutoff (2 * ‖z‖ / r - 1) * cutoff (R + 1 - ‖z‖)

private def annularClamp (r R : ℝ) (z : ℂ) : ℂ :=
  (max r (min R ‖z‖) / ‖z‖) • z

private def collar (f : ℂ → ℂ) (r R : ℝ) (z : ℂ) : ℂ :=
  collarWeight r R z • f (annularClamp r R z) +
    (1 - collarWeight r R z) • (-1 : ℂ)

private theorem collarWeight_bounds (r R : ℝ) (z : ℂ) :
    0 ≤ collarWeight r R z ∧ collarWeight r R z ≤ 1 := by
  have hi := cutoff_bounds (2 * ‖z‖ / r - 1)
  have ho := cutoff_bounds (R + 1 - ‖z‖)
  constructor
  · exact mul_nonneg hi.1 ho.1
  · exact (mul_le_mul hi.2 ho.2 ho.1 (by norm_num)).trans_eq (one_mul 1)

private theorem collarWeight_inner {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ≤ r / 2) : collarWeight r R z = 0 := by
  have hi : 2 * ‖z‖ / r - 1 ≤ 0 := by
    have : 2 * ‖z‖ / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  simp [collarWeight, cutoff_eq_zero hi]

private theorem collarWeight_outer {r R : ℝ} {z : ℂ}
    (hz : R + 1 ≤ ‖z‖) : collarWeight r R z = 0 := by
  simp [collarWeight, cutoff_eq_zero (show R + 1 - ‖z‖ ≤ 0 by linarith)]

private theorem annularClamp_norm {r R : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ≠ 0) : ‖annularClamp r R z‖ = max r (min R ‖z‖) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hm : 0 < max r (min R ‖z‖) := hr.trans_le (le_max_left _ _)
  simp only [annularClamp, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hm hn)]
  exact div_mul_cancel₀ _ hn.ne'

private theorem annularClamp_mem {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {z : ℂ} (hz : z ≠ 0) :
    annularClamp r R z ∈ closedBall (0 : ℂ) R \ ball 0 r := by
  rw [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right,
    annularClamp_norm hr hz]
  exact ⟨max_le hrR (min_le_left _ _), not_lt.mpr (le_max_left _ _)⟩

private theorem collar_eq_on_annulus {f : ℂ → ℂ} {r R : ℝ} (hr : 0 < r)
    {z : ℂ} (hzr : r ≤ ‖z‖) (hzR : ‖z‖ ≤ R) : collar f r R z = f z := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hzr)
  have hi : 1 ≤ 2 * ‖z‖ / r - 1 := by
    have : 2 ≤ 2 * ‖z‖ / r := (le_div_iff₀ hr).mpr (by linarith)
    linarith
  have ho : 1 ≤ R + 1 - ‖z‖ := by linarith
  have hw : collarWeight r R z = 1 := by
    simp [collarWeight, cutoff_eq_one hi, cutoff_eq_one ho]
  have hv : annularClamp r R z = z := by
    simp [annularClamp, min_eq_right hzR, max_eq_right hzr, hn]
  simp [collar, hw, hv]

private theorem collar_continuous {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hf : ContinuousOn f (closedBall (0 : ℂ) R \ ball 0 r)) :
    Continuous (collar f r R) := by
  have hw : Continuous (collarWeight r R) := by
    change Continuous (fun z : ℂ => max 0 (min 1 (2 * ‖z‖ / r - 1)) *
      max 0 (min 1 (R + 1 - ‖z‖)))
    fun_prop
  have hv : ContinuousOn (annularClamp r R) ({0}ᶜ : Set ℂ) := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hz)
    change ContinuousAt (fun w : ℂ => (max r (min R ‖w‖) / ‖w‖) • w) z
    fun_prop
  have hfv : ContinuousOn (fun z => f (annularClamp r R z)) ({0}ᶜ : Set ℂ) :=
    hf.comp' hv (fun z hz => annularClamp_mem hr hrR (by simpa using hz))
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    apply (continuousAt_const : ContinuousAt (fun _ : ℂ => (-1 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [continuous_norm.continuousAt.eventually
      (gt_mem_nhds (show ‖(0 : ℂ)‖ < r / 2 by simpa using half_pos hr))] with z hz
    change collar f r R z = (-1 : ℂ)
    simp [collar, collarWeight_inner hr hz.le]
  · have hfc : ContinuousAt (fun z => f (annularClamp r R z)) z :=
      hfv.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hz))
    exact (hw.continuousAt.smul hfc).add
      ((continuousAt_const.sub hw.continuousAt).smul continuousAt_const)

private theorem collar_zero_interior {f : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hb : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → (f z).re < 0)
    {z : ℂ} (hz : collar f r R z = 0) : r < ‖z‖ ∧ ‖z‖ < R := by
  have hwi := collarWeight_bounds r R z
  have hnonzero : ∀ (hboundary : ‖annularClamp r R z‖ = r ∨
      ‖annularClamp r R z‖ = R), False := by
    intro hboundary
    have hfneg := hb (annularClamp r R z) hboundary
    have hre := congrArg Complex.re hz
    simp only [collar, Complex.add_re, Complex.smul_re, Complex.neg_re,
      Complex.one_re, Complex.zero_re, smul_eq_mul] at hre
    by_cases hw : collarWeight r R z = 0
    · rw [hw] at hre
      norm_num at hre
    · have hpos := mul_pos (lt_of_le_of_ne hwi.1 (Ne.symm hw)) (neg_pos.mpr hfneg)
      nlinarith
  constructor
  · by_contra! hzr
    by_cases hzsmall : ‖z‖ ≤ r / 2
    · simp [collar, collarWeight_inner hr hzsmall] at hz
    · have hn : z ≠ 0 := by intro hz0; simp [hz0] at hzsmall; linarith
      apply hnonzero
      left
      rw [annularClamp_norm hr hn, min_eq_right (hzr.trans hrR.le),
        max_eq_left hzr]
  · by_contra! hzR
    have hn : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((hr.trans hrR).trans_le hzR))
    apply hnonzero
    right
    rw [annularClamp_norm hr hn, min_eq_left hzR, max_eq_right hrR.le]

/-- A continuous annulus map whose two boundary circles lie in the strict left half-plane
has a second interior zero whenever one interior zero has an invertible ordinary real derivative.
No complex differentiability or regularity of any other zero is assumed. -/
theorem annular_second_zero (f : ℂ → ℂ) (a : ℂ) (r R : ℝ)
    (L : ℂ ≃L[ℝ] ℂ) (hr : 0 < r) (har : r < ‖a‖) (haR : ‖a‖ < R)
    (hf : ContinuousOn f (closedBall (0 : ℂ) R \ ball 0 r))
    (ha : f a = 0) (hd : HasFDerivAt f (L : ℂ →L[ℝ] ℂ) a)
    (hb : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = R → (f z).re < 0) :
    ∃ b : ℂ, r < ‖b‖ ∧ ‖b‖ < R ∧ b ≠ a ∧ f b = 0 := by
  have hrR : r < R := har.trans haR
  have heq : collar f r R =ᶠ[𝓝 a] f := by
    filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds har),
      continuous_norm.continuousAt.eventually (gt_mem_nhds haR)] with z hzr hzR
    exact collar_eq_on_annulus hr hzr.le hzR.le
  obtain ⟨b, hba, hb0⟩ := constantExterior_second_zero (collar f r R) a (-1) (R + 1) L
    (collar_continuous hr hrR.le hf) (by norm_num)
    (fun z hz => by simp [collar, collarWeight_outer hz])
    (by rw [collar_eq_on_annulus hr har.le haR.le, ha])
    (hd.congr_of_eventuallyEq heq)
  obtain ⟨hbr, hbR⟩ := collar_zero_interior hr hrR hb hb0
  exact ⟨b, hbr, hbR, hba, (collar_eq_on_annulus hr hbr.le hbR.le).symm.trans hb0⟩

end D5.S3.Topology.AnnularSecondZero
