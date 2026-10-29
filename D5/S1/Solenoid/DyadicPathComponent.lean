/- GID: D5/S1/Solenoid/DyadicPathComponent
   generality: I
   mirror-B: D5/B/S1/Solenoid/DyadicPathComponent
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Unique real-flow time classifies paths in the actual dyadic solenoid. -/

import D5.S1.Solenoid.DyadicTimeSeparation
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

/-! Covering lifts identify the paths of the inherited dyadic inverse limit. -/

noncomputable section

namespace D5.S1.Solenoid.DyadicSolenoid

private theorem flow_injective : Function.Injective realFlow := by
  apply (injective_iff_map_eq_zero realFlow).2
  intro t ht
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt |t| (show (1 : ℝ) < 2 by norm_num)
  have hcoordinate := congrArg (fun x : DyadicSolenoid => x.1 n) ht
  change (((t / (2 : ℝ)^n : ℝ) : AddCircle (1 : ℝ)) = 0) at hcoordinate
  rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoordinate with ⟨z, hz⟩
  have hzreal : (z : ℝ) = t / (2 : ℝ)^n := by
    simpa [zsmul_eq_mul] using hz
  have hzabs : |(z : ℝ)| < 1 := by
    rw [hzreal, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2^n)]
    exact (div_lt_one (by positivity : (0 : ℝ) < 2^n)).2 hn
  have hz0 : z = 0 := by
    apply Int.abs_lt_one_iff.mp
    exact_mod_cast hzabs
  rw [hz0, Int.cast_zero] at hzreal
  exact (div_eq_zero_iff.mp hzreal.symm).resolve_right (pow_ne_zero _ (by norm_num))

private theorem coordinate_power (x : DyadicSolenoid) (n : ℕ) :
    (2 ^ n : ℕ) • x.1 n = x.1 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, x.2 n]
    exact ih

/-- On the inherited dyadic inverse-limit topology, two points are joined precisely
when a unique real-flow time translates the first point to the second. -/
theorem dyadic_path_orbit_classification (x y : DyadicSolenoid) :
    Joined x y ↔ ∃! t : ℝ, y = realFlow t + x := by
  constructor
  · rintro ⟨γ⟩
    let δ : C(unitInterval, DyadicSolenoid) :=
      ⟨fun u => γ u - x, γ.continuous.sub continuous_const⟩
    have hδ0 : δ 0 = 0 := by simp [δ, γ.source]
    have hδ1 : δ 1 = y - x := by simp [δ, γ.target]
    let c : C(unitInterval, AddCircle (1 : ℝ)) :=
      ⟨fun u => (δ u).1 0,
        (continuous_apply 0).comp (continuous_subtype_val.comp δ.continuous)⟩
    obtain ⟨a, ha, ha0⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).exists_path_lifts c 0
      (by change (δ 0).1 0 = _; simp [hδ0])
    have hcoord (n : ℕ) (u : unitInterval) :
        (δ u).1 n = ((a u / (2 : ℝ)^n : ℝ) : AddCircle (1 : ℝ)) := by
      have : NeZero (2 ^ n : ℕ) := ⟨pow_ne_zero _ (by norm_num)⟩
      have hcover := (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero
        (1 : ℝ) (2 ^ n)).isCoveringMap
      have heq := hcover.eq_of_comp_eq
        ((continuous_apply n).comp (continuous_subtype_val.comp δ.continuous))
        ((AddCircle.continuous_mk' (1 : ℝ)).comp (a.continuous.div_const ((2 : ℝ)^n)))
        (by
          funext v
          change (2 ^ n : ℕ) • (δ v).1 n =
            (2 ^ n : ℕ) • ((a v / (2 : ℝ)^n : ℝ) : AddCircle (1 : ℝ))
          rw [coordinate_power, ← AddCircle.coe_nsmul, nsmul_eq_mul]
          push_cast
          rw [mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num))]
          exact (congr_fun ha v).symm)
        0 (by simp [hδ0, ha0])
      exact congr_fun heq u
    have hend : y - x = realFlow (a 1) := by
      rw [← hδ1]
      ext n
      exact hcoord n 1
    refine ⟨a 1, (sub_eq_iff_eq_add).mp hend, ?_⟩
    intro t ht
    apply flow_injective
    exact add_right_cancel (ht.symm.trans ((sub_eq_iff_eq_add).mp hend))
  · rintro ⟨t, rfl, _⟩
    refine ⟨Path.mk
      ⟨fun u => realFlow ((u : ℝ) * t) + x,
        (dyadic_time_separation.2.2.1.comp
          (continuous_subtype_val.mul continuous_const)).add continuous_const⟩ ?_ ?_⟩
    · simp
    · simp

end D5.S1.Solenoid.DyadicSolenoid
