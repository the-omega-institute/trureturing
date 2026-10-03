/- GID: D5/S3/Geometry/Polygons/BalancedPlanarClosure
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/BalancedPlanarClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.Connected]
   utility: none
   digest: Balanced finite nonnegative lengths admit actual closed complex-plane vectors. -/

/- proof_shape: result: content
   admission_basis: escape-witness
   escape_witness: the local attainable-resultant induction constructs vectors for
     every nonnegative r bounded by the total length and satisfying all deficit
     inequalities. Sphere connectedness supplies each actual two-vector attainment.
   Direct frozen dependencies: none (pinned Mathlib only).
   The planar closure criterion is classical; no originality claim is made. -/

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

open scoped BigOperators
open Complex

set_option autoImplicit false

namespace D5.S3.Geometry.Polygons.BalancedPlanarClosure

/-- Nonnegative balanced lengths admit a closed configuration in the complex plane.
Includes the empty family, zero lengths, and equality in the balance condition. -/
theorem result (m : ℕ) (L : Fin m → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hbal : ∀ i, 2 * L i ≤ ∑ j, L j) :
    ∃ v : Fin m → ℂ, (∀ i, ‖v i‖ = L i) ∧ ∑ i, v i = 0 := by
  classical
  -- Actual endpoint configurations and the intermediate value theorem fill the circle image.
  have two (z : ℂ) (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r)
      (hlo : |‖z‖ - t| ≤ r) (hhi : r ≤ ‖z‖ + t) :
      ∃ w : ℂ, ‖w‖ = t ∧ ‖z + w‖ = r := by
    by_cases hz : z = 0
    · subst z
      have hrt : r = t := by
        simp only [norm_zero, zero_sub, abs_neg, abs_of_nonneg ht, zero_add] at hlo hhi
        linarith
      exact ⟨(t : ℂ), by simp [abs_of_nonneg ht], by simp [hrt, abs_of_nonneg ht]⟩
    have hs : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let u : ℂ := z / (‖z‖ : ℂ)
    have hu : ‖u‖ = 1 := by simp [u, ne_of_gt hs]
    have hzu : z = (‖z‖ : ℂ) * u := by
      dsimp [u]
      have hc : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
      field_simp
    have hn (a : ℝ) : ‖(a : ℂ) * u‖ = |a| := by
      rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hem : ‖z + ((-t : ℝ) : ℂ) * u‖ = |‖z‖ - t| := by
      conv_lhs => rw [hzu]
      rw [← add_mul, ← Complex.ofReal_add, hn]; congr 1
    have hep : ‖z + (t : ℂ) * u‖ = ‖z‖ + t := by
      conv_lhs => rw [hzu]
      rw [← add_mul, ← Complex.ofReal_add, hn, abs_of_nonneg (by positivity)]
    have hc : IsPreconnected (Metric.sphere (0 : ℂ) t) :=
      (isConnected_sphere (by simp [Complex.rank_real_complex]) 0 ht).isPreconnected
    obtain ⟨w, hw, hwr⟩ := hc.intermediate_value
      (a := ((-t : ℝ) : ℂ) * u) (b := (t : ℂ) * u)
      (by simp [hu, abs_of_nonneg ht])
      (by simp [hu, abs_of_nonneg ht])
      (f := fun w : ℂ => ‖z + w‖) (by fun_prop)
      (show r ∈ Set.Icc _ _ by rw [hem, hep]; exact ⟨hlo, hhi⟩)
    exact ⟨w, by simpa [Metric.mem_sphere, dist_zero_right] using hw, hwr⟩
  -- The sufficient direction of the complete attainable-resultant criterion.
  have attain : ∀ (n : ℕ) (l : Fin n → ℝ), (∀ i, 0 ≤ l i) →
      ∀ r : ℝ, 0 ≤ r → r ≤ ∑ i, l i → (∀ i, 2 * l i ≤ (∑ j, l j) + r) →
      ∃ v : Fin n → ℂ, (∀ i, ‖v i‖ = l i) ∧ ‖∑ i, v i‖ = r := by
    intro n
    induction n with
    | zero =>
      intro l hl r hr hrS hb
      have : r = 0 := by simpa using le_antisymm hrS hr
      subst r
      exact ⟨Fin.elim0, by simp, by simp⟩
    | succ n ih =>
      intro l hl r hr hrS hb
      let t := l 0
      let S := ∑ i : Fin n, l i.succ
      -- This choice satisfies both the old deficit bounds and the new triangle bounds.
      let s := min S (r + t)
      have ht : 0 ≤ t := hl 0
      have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hl i.succ
      have hsum : ∑ i, l i = t + S := Fin.sum_univ_succ l
      have hs : 0 ≤ s := le_min hS (add_nonneg hr ht)
      have hsS : s ≤ S := min_le_left _ _
      have hsr : s ≤ r + t := min_le_right _ _
      have hrt : r - t ≤ s := le_min (by rw [hsum] at hrS; linarith) (by linarith)
      have htr : t - r ≤ s := le_min (by
        have h := hb 0
        rw [hsum] at h
        change 2 * t ≤ t + S + r at h
        linarith) (by linarith)
      have hb' : ∀ i : Fin n, 2 * l i.succ ≤ S + s := by
        intro i
        have hiS : l i.succ ≤ S := Finset.single_le_sum (fun j _ => hl j.succ) (Finset.mem_univ i)
        have hi := hb i.succ
        rw [hsum] at hi
        dsimp [s]
        rcases le_total S (r + t) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      obtain ⟨v, hv, hvS⟩ := ih (fun i => l i.succ) (fun i => hl i.succ) s hs hsS hb'
      obtain ⟨w, hw, hwr⟩ := two (∑ i, v i) t r ht hr
        (by rw [hvS, abs_le]; constructor <;> linarith) (by rw [hvS]; linarith)
      refine ⟨Fin.cons w v, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun j => ?_) i
        · exact hw
        · exact hv j
      · simpa [Fin.sum_univ_succ, add_comm] using hwr
  obtain ⟨v, hv, hsum⟩ := attain m L hL 0 le_rfl (Finset.sum_nonneg fun i _ => hL i)
    (by simpa using hbal)
  exact ⟨v, hv, norm_eq_zero.mp hsum⟩

end D5.S3.Geometry.Polygons.BalancedPlanarClosure
