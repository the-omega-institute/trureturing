/- GID: D5/S3/Quantum/Foundation/ReciprocalEndpointExposure
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ReciprocalEndpointExposure
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: One-sided original pure comparison exposes its fixed endpoint. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import Mathlib.Analysis.SpecificLimits.Basic

/-! The entire original proper interval and normalized base are retained.
The relative-interior construction uses the compact zero-effect section itself;
it applies also when that section has zero span.

The public endpoint theorem has proof_shape: content and admission_basis:
escape-witness. Its live construction combines uniform original zero-effect
domination with penalized pure maximizers and actual normalized confirming
effects to contradict a nonsingleton zero fibre. The resulting positive-gap
estimate is not a specialization of a frozen or pinned endpoint theorem.
The private relative-interior and maximum-face helpers are consumed directly by
that proof; their compactness, separation and extreme-point API bindings are
not counted as independent new mathematical content. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
open CircuitBalancedConfirmation ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem zero_effect_domination {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u) :
    ∃ h : V →L[ℝ] ℝ, proper C u h.toLinearMap ∧ h p = 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ g : V →L[ℝ] ℝ,
        proper C u g.toLinearMap → g p = 0 → ∀ y ∈ C, g y ≤ c * h y := by
  let G : Set (V →L[ℝ] ℝ) := effects C u ∩ {g | g p = 0}
  have hu (x : V) (hx : x ∈ C) : 0 ≤ u x := by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hs x hx hz).le
  have hzero : (0 : V →L[ℝ] ℝ) ∈ G := by
    exact ⟨fun x hx => ⟨by simp, by simpa using hu x hx⟩, by simp⟩
  have hconv : Convex ℝ G := by
    intro f hf g hg a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro x hx
      change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ u x
      have hf' : 0 ≤ f x ∧ f x ≤ u x := hf.1 x hx
      have hg' : 0 ≤ g x ∧ g x ≤ u x := hg.1 x hx
      constructor
      · exact add_nonneg (mul_nonneg ha hf'.1) (mul_nonneg hb hg'.1)
      · calc
          a * f x + b * g x ≤ a * u x + b * u x := by
            exact add_le_add (mul_le_mul_of_nonneg_left hf'.2 ha)
              (mul_le_mul_of_nonneg_left hg'.2 hb)
          _ = u x := by rw [← add_mul, hab, one_mul]
    · change a * f p + b * g p = 0
      rw [hf.2, hg.2]; ring
  have hcompact : IsCompact G := (effects_compact hs hg).inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨h, hh⟩ := Set.Nonempty.intrinsicInterior hconv ⟨0, hzero⟩
  have hhG : h ∈ G := intrinsicInterior_subset hh
  obtain ⟨hA, hAi, he⟩ := mem_intrinsicInterior.mp hh
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hAi)
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  let a : ℝ := ε / (|R| + 1)
  have ha : 0 < a := div_pos hε (by positivity)
  refine ⟨h, hhG.1, hhG.2, a⁻¹, inv_pos.mpr ha, ?_⟩
  intro g hgp hgz y hy
  have hgG : g ∈ G := ⟨hgp, hgz⟩
  have haff : affineSpan ℝ G = (Submodule.span ℝ G).toAffineSubspace :=
    affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ G hzero)
  have hm : h - a • g ∈ affineSpan ℝ G := by
    rw [haff]
    exact (Submodule.span ℝ G).sub_mem (Submodule.subset_span hhG)
      ((Submodule.span ℝ G).smul_mem a (Submodule.subset_span hgG))
  have hd : dist (⟨h - a • g, hm⟩ : affineSpan ℝ G) hA < ε := by
    rw [Subtype.dist_eq, he, dist_eq_norm]
    have hn : ‖(h - a • g) - h‖ = a * ‖g‖ := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    rw [hn]
    have hRg := hR g hgG
    have hlt : ‖g‖ < |R| + 1 := lt_of_le_of_lt hRg (by linarith [le_abs_self R])
    dsimp [a]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < |R| + 1)]
    exact mul_lt_mul_of_pos_left hlt hε
  have hmem : h - a • g ∈ G := hball hd
  have hnonneg := (hmem.1 y hy).1
  change 0 ≤ h y - a * g y at hnonneg
  exact (le_inv_mul_iff₀ ha).mpr (by linarith)

omit [FiniteDimensional ℝ V] in
private theorem pure_maximizer {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u)) (p : pure C u) (l : V →L[ℝ] ℝ) :
    ∃ x : pure C u, ∀ y ∈ base C u, l y ≤ l x := by
  let F := l.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn ⟨p, pure_mem p⟩ l.continuous.continuousOn
  obtain ⟨x, hx⟩ := (hex.isCompact hK).extremePoints_nonempty ⟨z, hz, hm⟩
  exact ⟨⟨x, hex.isExtreme.extremePoints_subset_extremePoints hx⟩, hx.1.2⟩

/-- The one-sided endpoint comparison alone exposes the fixed original pure
point. The witness and its complement are actual effects on the whole cone. -/
theorem reciprocal_endpoint_exposure {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (p : pure C u)
    (hrec : ∀ x : pure C u, comparison C u p x ≤ comparison C u x p) :
    ∃ h : V →ₗ[ℝ] ℝ, proper C u h ∧
      {y | y ∈ base C u ∧ h y = 0} = {(p : V)} ∧
      confirms C u p (u - h) ∧
      {y | y ∈ base C u ∧ (u - h) y = 1} = {(p : V)} ∧
      IsExposed ℝ (base C u) {(p : V)} := by
  classical
  have hK := base_compact hc hs
  have hp := pure_mem p
  have hu (x : V) (hx : x ∈ C) : 0 ≤ u x := by
    by_cases hz : x = 0
    · simp [hz]
    · exact (hs x hx hz).le
  have hunit (q : V) (hq : u q = 1) : confirms C u q u :=
    ⟨fun x hx => ⟨hu x hx, le_rfl⟩, hq⟩
  obtain ⟨h, hh, hhp, c, hcpos, hdom⟩ := zero_effect_domination hs hg p
  have hlower (y : V) (hy : y ∈ base C u) :
      1 - c * h y ≤ comparison C u p y := by
    change 1 - c * h y ≤ sInf {r | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f y = r}
    have hne : ({r | ∃ f : V →ₗ[ℝ] ℝ, confirms C u p f ∧ f y = r} : Set ℝ).Nonempty :=
      ⟨u y, u, hunit p hp.2, rfl⟩
    apply le_csInf hne
    rintro r ⟨f, hf, rfl⟩
    let g := (u - f).toContinuousLinearMap
    have hgproper : proper C u g.toLinearMap := by
      intro x hx
      have hf' := hf.1 x hx
      change 0 ≤ u x - f x ∧ u x - f x ≤ u x
      constructor <;> linarith
    have hgp : g p = 0 := by simp [g, hp.2, hf.2]
    have hd := hdom g hgproper hgp y hy.1
    change u y - f y ≤ c * h y at hd
    rw [hy.2] at hd
    linarith
  have hsingle : {y | y ∈ base C u ∧ h y = 0} = {(p : V)} := by
    apply Set.Subset.antisymm ?_ ?_
    · rintro y ⟨hy, hhy⟩
      by_contra hne
      have hyp : y ≠ (p : V) := by simpa using hne
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℝ (sub_ne_zero.mpr hyp)
      let ell := l.toContinuousLinearMap
      have hly : ell p < ell y := by
        have he : l y - l p = 1 := by simpa only [map_sub] using hl
        change l p < l y
        linarith
      let Z : Set V := {z | z ∈ base C u ∧ h z = 0}
      have hZ : IsCompact Z := hK.inter_right (isClosed_eq h.continuous continuous_const)
      obtain ⟨z, hz, hmaxZ⟩ := hZ.exists_isMaxOn ⟨y, hy, hhy⟩ ell.continuous.continuousOn
      let α := ell z
      have hδ : 0 < α - ell p := by
        have hh' : ell y ≤ ell z := hmaxZ (show y ∈ Z from ⟨hy, hhy⟩)
        dsimp [α]; linarith
      obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn ⟨p, hp⟩ ell.continuous.continuousOn
      obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn ⟨p, hp⟩ ell.continuous.continuousOn
      let A := ell b - ell a
      have hA : 0 ≤ A := sub_nonneg.mpr (hmax ha)
      let t (n : ℕ) : ℝ := n + 1
      have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
      let L (n : ℕ) : V →L[ℝ] ℝ := ell - t n • h
      choose x hx using fun n => pure_maximizer hK p (L n)
      have hxK (n : ℕ) : (x n : V) ∈ base C u := pure_mem (x n)
      have hxα (n : ℕ) : α ≤ L n (x n) := by
        have hz' := hx n z hz.1
        simpa [L, hz.2, α] using hz'
      have hpen (n : ℕ) : t n * h (x n) ≤ ell (x n) - α := by
        have hh' := hxα n
        change α ≤ ell (x n) - t n * h (x n) at hh'
        linarith
      have hsmall (n : ℕ) : h (x n) ≤ A / t n := by
        apply (le_div_iff₀ (ht n)).mpr
        have hm := hmax (hxK n)
        have hzmin := hmin hz.1
        have hpn := hpen n
        dsimp [A, α] at *
        nlinarith
      have hbound (n : ℕ) : α - ell p ≤
          c * (A * h (x n) + ell (x n) - α) := by
        obtain ⟨w, hw, hwmin⟩ := hK.exists_isMinOn ⟨p, hp⟩
          (L n).continuous.continuousOn
        let m := L n (x n)
        let d := m - L n w
        have hmα : α ≤ m := hxα n
        have hLp : L n p = ell p := by simp [L, hhp]
        have hd : 0 < d := by
          have hwle : L n w ≤ L n p := hwmin hp
          rw [hLp] at hwle
          dsimp [d]; linarith
        let e : V →ₗ[ℝ] ℝ := d⁻¹ • ((L n).toLinearMap - (L n w) • u)
        have hep : proper C u e := cone_bound hK hs (by
          intro q
          have hlo := hwmin (pure_mem q)
          have hhi := hx n q (pure_mem q)
          change 0 ≤ d⁻¹ * (L n q - L n w * u q) ∧
            d⁻¹ * (L n q - L n w * u q) ≤ 1
          rw [(pure_mem q).2, mul_one]
          constructor
          · exact mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr hlo)
          · rw [← div_eq_inv_mul, div_le_one hd]
            dsimp [d, m]; linarith)
        have hex : e (x n) = 1 := by
          change d⁻¹ * (L n (x n) - L n w * u (x n)) = 1
          rw [(hxK n).2, mul_one]
          exact inv_mul_cancel₀ hd.ne'
        have hcomp : comparison C u (x n) p ≤ e p :=
          csInf_le ⟨0, by rintro r ⟨f, hf, rfl⟩; exact (hf.1 p hp.1).1⟩
            ⟨e, ⟨hep, hex⟩, rfl⟩
        have heplower : 1 - c * h (x n) ≤ e p :=
          (hlower _ (hxK n)).trans ((hrec (x n)).trans hcomp)
        have hepval : d * (1 - e p) = m - ell p := by
          change d * (1 - d⁻¹ * (L n p - L n w * u p)) = m - ell p
          rw [hp.2, mul_one, hLp]
          field_simp
          dsimp [d]
          ring
        have hdA : d ≤ A + t n := by
          have hmup : ell (x n) ≤ ell b := hmax (hxK n)
          have hwlo : ell a ≤ ell w := hmin hw
          have hhx : 0 ≤ h (x n) := (hh (x n) (hxK n).1).1
          have hhw : h w ≤ u w := (hh w hw.1).2
          rw [hw.2] at hhw
          dsimp [d, m, L, A]
          simp only [sub_apply, smul_apply, smul_eq_mul]
          nlinarith [ht n]
        have hhn : 0 ≤ h (x n) := (hh (x n) (hxK n).1).1
        have hstep : α - ell p ≤ c * (A + t n) * h (x n) := by
          calc
            α - ell p ≤ d * (1 - e p) := by rw [hepval]; linarith
            _ ≤ d * (c * h (x n)) := mul_le_mul_of_nonneg_left (by linarith) hd.le
            _ ≤ (A + t n) * (c * h (x n)) :=
              mul_le_mul_of_nonneg_right hdA (mul_nonneg hcpos.le hhn)
            _ = c * (A + t n) * h (x n) := by ring
        have hpn := hpen n
        nlinarith
      obtain ⟨v, hv, φ, hφ, hvlim⟩ := hK.tendsto_subseq hxK
      have hzeroLim : Tendsto (fun n => h (x (φ n))) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ => A / t n) atTop (𝓝 0) := by
          simpa [t, div_eq_mul_inv] using
            (tendsto_const_nhds (x := A)).mul
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        apply squeeze_zero (fun n => (hh _ (hxK (φ n)).1).1)
          (fun n => hsmall (φ n)) (hinv.comp hφ.tendsto_atTop)
      have hvh : h v = 0 := tendsto_nhds_unique
        (h.continuous.tendsto v |>.comp hvlim) hzeroLim
      have hαv : ell v = α := by
        apply le_antisymm (hmaxZ ⟨hv, hvh⟩)
        have hn (n : ℕ) : α ≤ ell (x (φ n)) := by
          have hpn := hpen (φ n)
          have hhn : 0 ≤ h (x (φ n)) := (hh _ (hxK (φ n)).1).1
          nlinarith [ht (φ n)]
        exact ge_of_tendsto (ell.continuous.tendsto v |>.comp hvlim) (Eventually.of_forall hn)
      have hlim : Tendsto (fun n => c * (A * h (x (φ n)) + ell (x (φ n)) - α))
          atTop (𝓝 0) := by
        convert (tendsto_const_nhds (x := c)).mul
          (((tendsto_const_nhds (x := A)).mul hzeroLim).add
            (ell.continuous.tendsto v |>.comp hvlim) |>.sub_const α) using 1 <;>
          simp [hαv]
      have hbad : α - ell p ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => hbound (φ n))
      exact (not_le_of_gt hδ) hbad
    · rintro y rfl
      exact ⟨hp, hhp⟩
  have hcompl : confirms C u p (u - h.toLinearMap) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      have hh' : 0 ≤ h y ∧ h y ≤ u y := hh y hy
      change 0 ≤ u y - h y ∧ u y - h y ≤ u y
      constructor <;> linarith
    · simp [hp.2, hhp]
  have hfibre : {y | y ∈ base C u ∧ (u - h.toLinearMap) y = 1} = {(p : V)} := by
    rw [← hsingle]
    ext y
    constructor <;> rintro ⟨hy, he⟩ <;> refine ⟨hy, ?_⟩
    · change u y - h y = 1 at he
      rw [hy.2] at he; linarith
    · change u y - h y = 1
      rw [hy.2, he]; ring
  refine ⟨h.toLinearMap, hh, hsingle, hcompl, hfibre, ?_⟩
  intro _
  refine ⟨(u - h.toLinearMap).toContinuousLinearMap, ?_⟩
  rw [← hfibre]
  ext y
  constructor
  · rintro ⟨hy, he⟩
    refine ⟨hy, fun z hz => ?_⟩
    change (u - h.toLinearMap) z ≤ (u - h.toLinearMap) y
    rw [he]
    simpa only [hz.2] using (hcompl.1 z hz.1).2
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, le_antisymm ?_ ?_⟩
    · simpa [hy.2] using (hcompl.1 y hy.1).2
    · have hle := hmax p hp
      change (u - h.toLinearMap) p ≤ (u - h.toLinearMap) y at hle
      rw [hcompl.2] at hle
      exact hle

end D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
