/- GID: D5/S1/Dynamics/Shadowing/LocalEquiconnection
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LocalEquiconnection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.Normalize]
   utility: none
   digest: Explicit normalized sphere connectors and their transport through arbitrary homeomorphisms. -/

import D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
import Mathlib.Analysis.Normed.Module.Normalize

/-! Coherent local connectors use normalized chords and transfer through homeomorphisms. -/

noncomputable section
open Set Topology

namespace D5.S1.Dynamics.Shadowing

open VerticalSuspensionSelector (LocalEquiconnection)

namespace LocalEquiconnection

/-- Transport the actual domain and all three identities, without any dynamical compatibility. -/
def transport {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (H : LocalEquiconnection Y) : LocalEquiconnection X where
  domain := {p | (e p.1, e p.2) ∈ H.domain}
  isOpen_domain := H.isOpen_domain.preimage
    ((e.continuous.comp continuous_fst).prodMk (e.continuous.comp continuous_snd))
  diagonal x := H.diagonal (e x)
  connect z := e.symm (H.connect (⟨(e z.1.1.1, e z.1.1.2), z.1.2⟩, z.2))
  continuous_connect := e.symm.continuous.comp (H.continuous_connect.comp
    (((e.continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))).prodMk
      (e.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
      |>.prodMk continuous_snd))
  left p := by simp only [H.left, e.symm_apply_apply]
  right p := by simp only [H.right, e.symm_apply_apply]
  refl x t := by simp only [H.refl, e.symm_apply_apply]

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The subtype sphere has the inherited topology and no chosen differentiable structure. -/
abbrev UnitSphere := Metric.sphere (0 : V) 1

private theorem unit_norm (p : UnitSphere V) : ‖(p : V)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using p.2

private def chord (p q : UnitSphere V) (s : Icc (0 : ℝ) 1) : V :=
  (1 - (s : ℝ)) • (p : V) + (s : ℝ) • (q : V)

private theorem chord_ne_zero (p q : UnitSphere V) (hpq : (q : V) ≠ -(p : V))
    (s : Icc (0 : ℝ) 1) : chord V p q s ≠ 0 := by
  intro hz
  have he : (1 - (s : ℝ)) • (p : V) = -((s : ℝ) • (q : V)) :=
    eq_neg_of_add_eq_zero_left hz
  have hn := congrArg norm he
  rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr s.2.2), abs_of_nonneg s.2.1,
    unit_norm, unit_norm, mul_one, mul_one] at hn
  have hs : (s : ℝ) = 1 / 2 := by linarith
  have hpq0 : (p : V) + (q : V) = 0 := by
    have hh := congrArg (fun v : V => (2 : ℝ) • v) hz
    dsimp [chord] at hh
    simpa only [hs, smul_add, smul_smul, smul_zero, show (2 : ℝ) * (1 - 1 / 2) = 1 by norm_num,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using hh
  exact hpq (eq_neg_of_add_eq_zero_right hpq0)

/-- Normalized straight interpolation on exactly the open nonantipodal-pair domain. -/
def sphere : LocalEquiconnection (UnitSphere V) where
  domain := {p | (p.2 : V) ≠ -(p.1 : V)}
  isOpen_domain := isOpen_ne_fun (continuous_subtype_val.comp continuous_snd)
    (continuous_subtype_val.comp continuous_fst |>.neg)
  diagonal p := by
    intro hh
    have hz : (p : V) = 0 := by
      have ha : (p : V) + (p : V) = 0 := eq_neg_iff_add_eq_zero.mp hh
      have htwo : (2 : ℝ) • (p : V) = 0 := by simpa [two_smul ℝ] using ha
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have := unit_norm V p
    rw [hz, norm_zero] at this
    norm_num at this
  connect z := ⟨NormedSpace.normalize (chord V z.1.1.1 z.1.1.2 z.2), by
    simp only [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (chord_ne_zero V _ _ z.1.2 _)⟩
  continuous_connect := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : {p : UnitSphere V × UnitSphere V |
        (p.2 : V) ≠ -(p.1 : V)} × Icc (0 : ℝ) 1 =>
        chord V z.1.1.1 z.1.1.2 z.2) := by
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)))).add
        ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))))
    exact (hc.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (chord_ne_zero V _ _ z.1.2 _))).smul hc
  left p := by
    apply Subtype.ext
    simp only [chord, sub_zero, one_smul, zero_smul, add_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (unit_norm V _)
  right p := by
    apply Subtype.ext
    simp only [chord, sub_self, zero_smul, one_smul, zero_add]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (unit_norm V _)
  refl p s := by
    apply Subtype.ext
    have he : chord V p p s = (p : V) := by
      rw [chord, ← add_smul]
      simp
    change NormedSpace.normalize (chord V p p s) = _
    rw [he]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (unit_norm V _)

end LocalEquiconnection
end D5.S1.Dynamics.Shadowing
