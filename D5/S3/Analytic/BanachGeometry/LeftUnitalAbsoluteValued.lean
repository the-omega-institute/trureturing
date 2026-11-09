/- GID: D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued
   generality: G
   mirror-B: D5/B/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.Connected]
   utility: none
   digest: A left unit makes nonzero left multipliers invertible for arbitrary Banach norms. -/

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Connected.Clopen

/-!
The product is an arbitrary real bilinear map, with no associativity or right
unit assumed. This is the Banach-space intermediate of ΩQ020 Lemma 3.3.
It does not construct the original seminorm quotient or its completion.

proof_shape: content for exists_left_multiplier_equiv. The escape candidate
is the clopen propagation of invertibility on the punctured real space.
All scalar/operator norm calculations reuse Mathlib homothety results.
utility none: this is an arbitrary-dimensional structural theorem, not a
finite computation, checker, numeric reduction or certified finite instance.
-/

noncomputable section
open Set
open scoped Topology

namespace D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]

/-- Every nonzero left multiplication is a bounded linear equivalence with
the exact forward and inverse similarity norms, using only a left unit. -/
theorem exists_left_multiplier_equiv
    (m : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hm : ∀ x y : E, ‖m x y‖ = ‖x‖ * ‖y‖)
    (e : E) (he : ∀ y : E, m e y = y)
    (x : E) (hx : x ≠ 0) :
    ∃ T : E ≃L[ℝ] E, (∀ y : E, T y = m x y) ∧
      ‖(T : E →L[ℝ] E)‖ = ‖x‖ ∧
      ‖(T.symm : E →L[ℝ] E)‖ = ‖x‖⁻¹ := by
  classical
  let L : E →L[ℝ] E →L[ℝ] E :=
    m.mkContinuous₂ 1 (fun a b => by simpa using (hm a b).le)
  have hL (a b : E) : L a b = m a b := rfl
  have hn (a b : E) : ‖L a b‖ = ‖a‖ * ‖b‖ := hm a b
  have hop (a : E) : ‖L a‖ = ‖a‖ := (L a).homothety_norm (hn a)
  have hinj (a : E) (ha : a ≠ 0) : Function.Injective (L a) := by
    intro z w hzw
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hz' : ‖a‖ * ‖z - w‖ = 0 := by
      rw [← hn a (z - w), map_sub, hzw, sub_self, norm_zero]
    exact (mul_eq_zero.mp hz').resolve_left (norm_ne_zero_iff.mpr ha)
  have hunitnorm (a : E) (ha : a ≠ 0) (u : (E →L[ℝ] E)ˣ)
      (hu : (u : E →L[ℝ] E) = L a) :
      ‖(↑u⁻¹ : E →L[ℝ] E)‖ = ‖a‖⁻¹ := by
    apply ContinuousLinearMap.homothety_norm
    intro z
    apply (eq_inv_mul_iff_mul_eq₀ (norm_ne_zero_iff.mpr ha)).mpr
    have h := hn a ((↑u⁻¹ : E →L[ℝ] E) z)
    rw [← hu] at h
    simpa only [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self] using h.symm
  have hunit (a : E) (ha : a ≠ 0) : IsUnit (L a) := by
    by_cases hd : 1 < Module.rank ℝ E
    · let P := {a : E // a ≠ 0}
      let G : Set P := {a | IsUnit (L a.val)}
      have hconn : ConnectedSpace P := by
        apply isConnected_iff_connectedSpace.mp
        have hset : {a : E | a ≠ 0} = ({0}ᶜ : Set E) := by ext a; simp
        change IsConnected {a : E | a ≠ 0}
        rw [hset]
        exact isConnected_compl_singleton_of_one_lt_rank hd (0 : E)
      let : ConnectedSpace P := hconn
      have hopen : IsOpen G :=
        Units.isOpen.preimage (L.continuous.comp continuous_subtype_val)
      have hclosed : IsClosed G := by
        apply isClosed_of_closure_subset
        intro b hb
        obtain ⟨c, hc, hcb⟩ := Metric.mem_closure_iff.mp hb (‖b.val‖ / 2)
          (half_pos (norm_pos_iff.mpr b.property))
        obtain ⟨u, hu⟩ := hc
        have hdist : ‖b.val - c.val‖ < ‖b.val‖ / 2 := by
          change dist b.val c.val < ‖b.val‖ / 2 at hcb
          rwa [dist_eq_norm] at hcb
        have hnear : ‖b.val - c.val‖ < ‖c.val‖ := by
          have htri' : ‖b.val‖ ≤ ‖b.val - c.val‖ + ‖c.val‖ :=
            norm_le_norm_sub_add _ _
          linarith
        have hpert : ‖L b.val - (u : E →L[ℝ] E)‖ <
            ‖(↑u⁻¹ : E →L[ℝ] E)‖⁻¹ := by
          rw [hu, ← map_sub, hop, hunitnorm c.val c.property u hu, inv_inv]
          exact hnear
        exact (u.ofNearby (L b.val) hpert).isUnit
      have he0 : e ≠ 0 := by
        intro he0
        obtain ⟨z, hz⟩ := exists_ne (0 : E)
        have h := he z
        simp [he0] at h
        exact hz h.symm
      have hLe : L e = 1 := by ext z; exact he z
      have hne : G.Nonempty := ⟨⟨e, he0⟩, by change IsUnit (L e); rw [hLe]; exact isUnit_one⟩
      have hall : G = univ := (show IsClopen G from ⟨hclosed, hopen⟩).eq_univ hne
      have : (⟨a, ha⟩ : P) ∈ G := by rw [hall]; trivial
      exact this
    · have hr : Module.rank ℝ E = 1 := le_antisymm (le_of_not_gt hd)
          (Cardinal.one_le_iff_ne_zero.mpr
            (ne_of_gt (Module.rank_pos_of_free (R := ℝ) (M := E))))
      let : Module.Finite ℝ E := Module.finite_of_rank_eq_one hr
      exact ContinuousLinearMap.isUnit_iff_bijective.mpr
        ⟨hinj a ha, (L a).toLinearMap.injective_iff_surjective.mp (hinj a ha)⟩
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit x hx)
  let T : E ≃L[ℝ] E := ContinuousLinearEquiv.ofHomothety
    (LinearEquiv.ofBijective (m x) hbij) ‖x‖ (norm_pos_iff.mpr hx) (hm x)
  refine ⟨T, fun _ => rfl, ?_, ?_⟩
  · exact (T : E →L[ℝ] E).homothety_norm (hm x)
  · exact (T.symm : E →L[ℝ] E).homothety_norm
      (ContinuousLinearEquiv.homothety_inverse ‖x‖ (norm_pos_iff.mpr hx)
        (LinearEquiv.ofBijective (m x) hbij) (hm x))

#print axioms exists_left_multiplier_equiv

end D5.S3.Analytic.BanachGeometry.LeftUnitalAbsoluteValued
