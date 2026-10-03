/- GID: D5/S3/Arith/AbsoluteValues/Heights/PrekopaLeindler
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/PrekopaLeindler
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean volume satisfies the Prekopa-Leindler inequality. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

open MeasureTheory Set Pointwise

/-- The one-dimensional Brunn–Minkowski inequality for compact sets: translate `s` by `sInf t` and
`t` by `sSup s`; the two translates lie in `s + t` and meet only at `sSup s + sInf t`. -/
private theorem Real.volume_add_volume_le_volume_add_of_isCompact {s t : Set ℝ} (hs : IsCompact s)
    (ht : IsCompact t) (hsne : s.Nonempty) (htne : t.Nonempty) :
    volume s + volume t ≤ volume (s + t) := by
  set a := sSup s with hadef
  set b := sInf t with hbdef
  have ha : a ∈ s := hs.sSup_mem hsne
  have hb : b ∈ t := ht.sInf_mem htne
  set A : Set ℝ := (· + b) '' s with hA
  set B : Set ℝ := (a + ·) '' t with hB
  have hBm : MeasurableSet B := (ht.image (by fun_prop)).measurableSet
  have hAsub : A ⊆ s + t := by rintro _ ⟨u, hu, rfl⟩; exact Set.add_mem_add hu hb
  have hBsub : B ⊆ s + t := by rintro _ ⟨v, hv, rfl⟩; exact Set.add_mem_add ha hv
  have hinter : A ∩ B ⊆ {a + b} := by
    rintro x ⟨⟨u, hu, rfl⟩, ⟨v, hv, hx⟩⟩
    have hx' : a + v = u + b := hx
    have h1 : u ≤ a := le_csSup hs.bddAbove hu
    have h2 : b ≤ v := csInf_le ht.bddBelow hv
    change u + b = a + b
    linarith
  have h0 : volume (A ∩ B) = 0 := measure_mono_null hinter (measure_singleton _)
  have hvol : volume (A ∪ B) + volume (A ∩ B) = volume A + volume B :=
    measure_union_add_inter A hBm
  have hAv : volume A = volume s := by simp [hA]
  have hBv : volume B = volume t := by simp [hB]
  calc volume s + volume t = volume A + volume B := by rw [hAv, hBv]
    _ = volume (A ∪ B) := by rw [← hvol, h0, add_zero]
    _ ≤ volume (s + t) := measure_mono (union_subset hAsub hBsub)

/-- **The one-dimensional Brunn–Minkowski inequality.** For nonempty measurable sets `s`, `t ⊆ ℝ`,
`volume s + volume t ≤ volume (s + t)`. The sumset need not be measurable: `volume` is applied to
it as an outer measure. -/
theorem Real.volume_add_volume_le_volume_add {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hsne : s.Nonempty) (htne : t.Nonempty) :
    volume s + volume t ≤ volume (s + t) := by
  obtain ⟨x₀, hx₀⟩ := hsne
  obtain ⟨y₀, hy₀⟩ := htne
  rcases eq_or_ne (volume (s + t)) ⊤ with hst | hst
  · simp [hst]
  have hsv : volume s ≠ ⊤ := by
    intro h
    refine hst (top_le_iff.mp ?_)
    have hle : volume ((· + y₀) '' s) ≤ volume (s + t) :=
      measure_mono (by rintro _ ⟨u, hu, rfl⟩; exact Set.add_mem_add hu hy₀)
    simpa [h] using hle
  have htv : volume t ≠ ⊤ := by
    intro h
    refine hst (top_le_iff.mp ?_)
    have hle : volume ((x₀ + ·) '' t) ≤ volume (s + t) :=
      measure_mono (by rintro _ ⟨v, hv, rfl⟩; exact Set.add_mem_add hx₀ hv)
    simpa [h] using hle
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hhalf : (ε : ENNReal) / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hε.ne']
  obtain ⟨K, hKs, hKc, hK⟩ := hs.exists_isCompact_lt_add hsv hhalf
  obtain ⟨L, hLt, hLc, hL⟩ := ht.exists_isCompact_lt_add htv hhalf
  set K' : Set ℝ := insert x₀ K with hK'
  set L' : Set ℝ := insert y₀ L with hL'
  have hKK' : volume K ≤ volume K' := measure_mono (Set.subset_insert _ _)
  have hLL' : volume L ≤ volume L' := measure_mono (Set.subset_insert _ _)
  have hcomp := Real.volume_add_volume_le_volume_add_of_isCompact (hKc.insert x₀) (hLc.insert y₀)
    ⟨x₀, Set.mem_insert _ _⟩ ⟨y₀, Set.mem_insert _ _⟩
  have hsub : K' + L' ⊆ s + t :=
    Set.add_subset_add (Set.insert_subset hx₀ hKs) (Set.insert_subset hy₀ hLt)
  calc volume s + volume t ≤ (volume K + (ε : ENNReal) / 2) + (volume L + (ε : ENNReal) / 2) :=
        add_le_add hK.le hL.le
    _ = (volume K + volume L) + ((ε : ENNReal) / 2 + (ε : ENNReal) / 2) := by ring
    _ ≤ (volume K' + volume L') + (ε : ENNReal) := by
        rw [ENNReal.add_halves]
        exact add_le_add (add_le_add hKK' hLL') le_rfl
    _ ≤ volume (K' + L') + (ε : ENNReal) := add_le_add hcomp le_rfl
    _ ≤ volume (s + t) + (ε : ENNReal) := add_le_add (measure_mono hsub) le_rfl

/-- **The layer cake formula for `ℝ≥0∞`-valued functions.** Mathlib's `Layercake` file states this
for real-valued functions; the `ℝ≥0∞` form is what the Prékopa–Leindler proof needs, since the
level sets there may well have infinite measure. -/
theorem MeasureTheory.lintegral_eq_lintegral_measure_ofReal_lt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
  have hS : MeasurableSet {p : α × ℝ | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst))
  set F : α → ℝ → ENNReal := fun x t =>
    Set.indicator {p : α × ℝ | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1} 1 (x, t) with hF
  have hFm : Measurable (Function.uncurry F) := measurable_one.indicator hS
  have hvol (c : ENNReal) :
      volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c} = c := by
    rcases eq_or_ne c ⊤ with hc | hc
    · subst hc
      have h : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ⊤} = Ioi (0 : ℝ) := by
        ext t; simp [ENNReal.ofReal_lt_top]
      rw [h, Real.volume_Ioi]
    · have h : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < c} = Ioo 0 c.toReal := by
        ext t
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (ENNReal.ofReal_lt_iff_lt_toReal h1.le hc).mp h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (ENNReal.ofReal_lt_iff_lt_toReal h1.le hc).mpr h2⟩
      rw [h, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]
  have h1 : ∀ x, ∫⁻ t, F x t = f x := by
    intro x
    have he : (fun t => F x t) = Set.indicator {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} 1 := by
      ext t; simp [hF, Set.indicator_apply]
    have hm : MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    rw [he, lintegral_indicator_one hm, hvol]
  have h2 : ∀ t : ℝ, 0 < t → ∫⁻ x, F x t ∂μ = μ {x | ENNReal.ofReal t < f x} := by
    intro t ht
    have he : (fun x => F x t) = Set.indicator {x | ENNReal.ofReal t < f x} 1 := by
      ext x; simp [hF, Set.indicator_apply, ht]
    rw [he, lintegral_indicator_one (measurableSet_lt measurable_const hf)]
  have h3 : ∀ t : ℝ, t ≤ 0 → ∫⁻ x, F x t ∂μ = 0 := by
    intro t ht
    have he : (fun x => F x t) = fun _ => (0 : ENNReal) := by
      ext x; simp [hF, Set.indicator_apply, not_lt.mpr ht]
    rw [he, lintegral_zero]
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, (∫⁻ t, F x t) ∂μ := by simp_rw [h1]
    _ = ∫⁻ t, (∫⁻ x, F x t ∂μ) := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun t => ?_
        rcases lt_or_ge 0 t with ht | ht
        · rw [h2 t ht, Set.indicator_of_mem (mem_Ioi.mpr ht)]
        · rw [h3 t ht, Set.indicator_of_notMem (by simpa using ht)]

/-- Prékopa–Leindler on `ℝ` for functions normalized to have supremum `1`, in the stronger
*arithmetic mean* form `a * ∫⁻ f + b * ∫⁻ g ≤ ∫⁻ h`. This is where the one-dimensional
Brunn–Minkowski inequality and the layer cake formula are used; everything else in the file is
bookkeeping around it. -/
private theorem Real.prekopaLeindler_of_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) {f g h : ℝ → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfne : ∀ t : ℝ, 0 < t → t < 1 → {x | ENNReal.ofReal t < f x}.Nonempty)
    (hgne : ∀ t : ℝ, 0 < t → t < 1 → {y | ENNReal.ofReal t < g y}.Nonempty)
    (key : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    ENNReal.ofReal a * (∫⁻ x, f x) + ENNReal.ofReal b * (∫⁻ y, g y) ≤ ∫⁻ z, h z := by
  have hstep : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal a * volume {x | ENNReal.ofReal t < f x}
        + ENNReal.ofReal b * volume {y | ENNReal.ofReal t < g y}
        ≤ volume {z | ENNReal.ofReal t < h z} := by
    intro t ht
    rcases lt_or_ge t 1 with ht1 | ht1
    · have hAm : MeasurableSet {x | ENNReal.ofReal t < f x} := measurableSet_lt measurable_const hf
      have hBm : MeasurableSet {y | ENNReal.ofReal t < g y} := measurableSet_lt measurable_const hg
      obtain ⟨x₀, hx₀⟩ := hfne t ht ht1
      obtain ⟨y₀, hy₀⟩ := hgne t ht ht1
      have hc0 : ENNReal.ofReal t ≠ 0 := by simp [ENNReal.ofReal_eq_zero, not_le.mpr ht]
      have hcT : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
      have hcpos : 0 < ENNReal.ofReal t := pos_iff_ne_zero.mpr hc0
      have hsub : a • {x | ENNReal.ofReal t < f x} + b • {y | ENNReal.ofReal t < g y}
          ⊆ {z | ENNReal.ofReal t < h z} := by
        rintro z ⟨p, hp, q, hq, rfl⟩
        obtain ⟨u, hu, rfl⟩ := hp
        obtain ⟨v, hv, rfl⟩ := hq
        change ENNReal.ofReal t < h (a • u + b • v)
        refine lt_of_lt_of_le ?_ (key u v)
        have hsplit : ENNReal.ofReal t = ENNReal.ofReal t ^ a * ENNReal.ofReal t ^ b := by
          rw [← ENNReal.rpow_add _ _ hc0 hcT, hab, ENNReal.rpow_one]
        rw [hsplit]
        have h1 : ENNReal.ofReal t ^ a < f u ^ a := ENNReal.rpow_lt_rpow hu ha
        have h2 : ENNReal.ofReal t ^ b ≤ g v ^ b := ENNReal.rpow_le_rpow hv.le hb.le
        calc ENNReal.ofReal t ^ a * ENNReal.ofReal t ^ b
            = ENNReal.ofReal t ^ b * ENNReal.ofReal t ^ a := mul_comm _ _
          _ < ENNReal.ofReal t ^ b * f u ^ a :=
              ENNReal.mul_lt_mul_right (ENNReal.rpow_pos hcpos hcT).ne'
                (ENNReal.rpow_ne_top_of_nonneg hb.le hcT) h1
          _ = f u ^ a * ENNReal.ofReal t ^ b := mul_comm _ _
          _ ≤ f u ^ a * g v ^ b := by gcongr
      have hBM := Real.volume_add_volume_le_volume_add (hAm.const_smul₀ a) (hBm.const_smul₀ b)
        ⟨a • x₀, ⟨x₀, hx₀, rfl⟩⟩ ⟨b • y₀, ⟨y₀, hy₀, rfl⟩⟩
      have hvA : volume (a • {x | ENNReal.ofReal t < f x})
          = ENNReal.ofReal a * volume {x | ENNReal.ofReal t < f x} := by
        rw [Measure.addHaar_smul]; simp [abs_of_pos ha]
      have hvB : volume (b • {y | ENNReal.ofReal t < g y})
          = ENNReal.ofReal b * volume {y | ENNReal.ofReal t < g y} := by
        rw [Measure.addHaar_smul]; simp [abs_of_pos hb]
      calc ENNReal.ofReal a * volume {x | ENNReal.ofReal t < f x}
            + ENNReal.ofReal b * volume {y | ENNReal.ofReal t < g y}
          = volume (a • {x | ENNReal.ofReal t < f x})
            + volume (b • {y | ENNReal.ofReal t < g y}) := by rw [hvA, hvB]
        _ ≤ volume (a • {x | ENNReal.ofReal t < f x} + b • {y | ENNReal.ofReal t < g y}) := hBM
        _ ≤ volume {z | ENNReal.ofReal t < h z} := measure_mono hsub
    · have h1t : (1 : ENNReal) ≤ ENNReal.ofReal t := ENNReal.one_le_ofReal.mpr ht1
      have hAe : {x | ENNReal.ofReal t < f x} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
          absurd hx (not_lt.mpr (le_trans (hf1 x) h1t))
      have hBe : {y | ENNReal.ofReal t < g y} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
          absurd hy (not_lt.mpr (le_trans (hg1 y) h1t))
      simp [hAe, hBe]
  rw [MeasureTheory.lintegral_eq_lintegral_measure_ofReal_lt volume hf,
    MeasureTheory.lintegral_eq_lintegral_measure_ofReal_lt volume hg,
    MeasureTheory.lintegral_eq_lintegral_measure_ofReal_lt volume hh,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (le_lintegral_add _ _) (lintegral_mono_ae ?_)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact hstep t ht

/-- Prékopa–Leindler on `ℝ` for functions bounded by `M` and `N` whose suprema are `M` and `N`:
normalize by `M` and `N` and appeal to `Real.prekopaLeindler_of_le_one`. -/
private theorem Real.prekopaLeindler_of_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {f g h : ℝ → ENNReal} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {M N : ENNReal} (hM0 : M ≠ 0) (hMT : M ≠ ⊤) (hN0 : N ≠ 0) (hNT : N ≠ ⊤)
    (hfM : ∀ x, f x ≤ M) (hgN : ∀ y, g y ≤ N)
    (hfsup : ∀ t : ℝ, 0 < t → t < 1 → ∃ x, ENNReal.ofReal t * M < f x)
    (hgsup : ∀ t : ℝ, 0 < t → t < 1 → ∃ y, ENNReal.ofReal t * N < g y)
    (key : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z := by
  have hMi : M⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMT
  have hMiT : M⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hM0
  have hNi : N⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hNT
  have hNiT : N⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hN0
  have hMa0 : M ^ a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hM0) hMT).ne'
  have hMaT : M ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha.le hMT
  have hNb0 : N ^ b ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hN0) hNT).ne'
  have hNbT : N ^ b ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hb.le hNT
  set c : ENNReal := (M ^ a * N ^ b)⁻¹ with hc
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top hMaT hNbT)
  have hcT : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp [hMa0, hNb0])
  have hcomp : ∀ u v : ENNReal, (M⁻¹ * u) ^ a * (N⁻¹ * v) ^ b = c * (u ^ a * v ^ b) := by
    intro u v
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le, ENNReal.mul_rpow_of_nonneg _ _ hb.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hc, ENNReal.mul_inv (Or.inl hMa0) (Or.inl hMaT)]
    ring
  have hunit := Real.prekopaLeindler_of_le_one ha hb hab (f := fun x => M⁻¹ * f x)
    (g := fun y => N⁻¹ * g y) (h := fun z => c * h z)
    (measurable_const.mul hf) (measurable_const.mul hg) (measurable_const.mul hh)
    (fun x => by
      calc M⁻¹ * f x ≤ M⁻¹ * M := by gcongr; exact hfM x
        _ = 1 := ENNReal.inv_mul_cancel hM0 hMT)
    (fun y => by
      calc N⁻¹ * g y ≤ N⁻¹ * N := by gcongr; exact hgN y
        _ = 1 := ENNReal.inv_mul_cancel hN0 hNT)
    (fun t ht ht1 => by
      obtain ⟨x, hx⟩ := hfsup t ht ht1
      refine ⟨x, ?_⟩
      have hlt : M⁻¹ * (ENNReal.ofReal t * M) < M⁻¹ * f x :=
        ENNReal.mul_lt_mul_right hMi hMiT hx
      calc ENNReal.ofReal t = M⁻¹ * (ENNReal.ofReal t * M) := by
            rw [mul_comm (ENNReal.ofReal t) M, ← mul_assoc, ENNReal.inv_mul_cancel hM0 hMT,
              one_mul]
        _ < M⁻¹ * f x := hlt)
    (fun t ht ht1 => by
      obtain ⟨y, hy⟩ := hgsup t ht ht1
      refine ⟨y, ?_⟩
      have hlt : N⁻¹ * (ENNReal.ofReal t * N) < N⁻¹ * g y :=
        ENNReal.mul_lt_mul_right hNi hNiT hy
      calc ENNReal.ofReal t = N⁻¹ * (ENNReal.ofReal t * N) := by
            rw [mul_comm (ENNReal.ofReal t) N, ← mul_assoc, ENNReal.inv_mul_cancel hN0 hNT,
              one_mul]
        _ < N⁻¹ * g y := hlt)
    (fun x y => by rw [hcomp]; gcongr; exact key x y)
  rw [lintegral_const_mul' _ _ hMiT, lintegral_const_mul' _ _ hNiT,
    lintegral_const_mul' _ _ hcT] at hunit
  have hAM : ∀ p₁ p₂ : ENNReal,
      p₁ ^ a * p₂ ^ b ≤ ENNReal.ofReal a * p₁ + ENNReal.ofReal b * p₂ := by
    intro p₁ p₂
    have hc₁ : ENNReal.ofReal a ≠ 0 := by simp [ENNReal.ofReal_eq_zero, not_le.mpr ha]
    have hc₂ : ENNReal.ofReal b ≠ 0 := by simp [ENNReal.ofReal_eq_zero, not_le.mpr hb]
    rcases eq_or_ne p₁ ⊤ with hp | hp
    · rw [hp]
      simp [ENNReal.mul_top hc₁]
    rcases eq_or_ne p₂ ⊤ with hp' | hp'
    · rw [hp']
      simp [ENNReal.mul_top hc₂]
    lift p₁ to NNReal using hp
    lift p₂ to NNReal using hp'
    have e₁ : (a.toNNReal : ℝ) = a := Real.coe_toNNReal a ha.le
    have e₂ : (b.toNNReal : ℝ) = b := Real.coe_toNNReal b hb.le
    have hsum : a.toNNReal + b.toNNReal = 1 := by
      apply NNReal.coe_injective
      push_cast [e₁, e₂]
      exact hab
    have hmain := NNReal.geom_mean_le_arith_mean2_weighted a.toNNReal b.toNNReal p₁ p₂ hsum
    rw [← ENNReal.coe_rpow_of_nonneg _ ha.le, ← ENNReal.coe_rpow_of_nonneg _ hb.le]
    calc ((p₁ ^ a : NNReal) : ENNReal) * ((p₂ ^ b : NNReal) : ENNReal)
        = ((p₁ ^ a * p₂ ^ b : NNReal) : ENNReal) := (ENNReal.coe_mul _ _).symm
      _ ≤ ((a.toNNReal * p₁ + b.toNNReal * p₂ : NNReal) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          calc p₁ ^ a * p₂ ^ b
              = p₁ ^ (a.toNNReal : ℝ) * p₂ ^ (b.toNNReal : ℝ) := by rw [e₁, e₂]
            _ ≤ a.toNNReal * p₁ + b.toNNReal * p₂ := hmain
      _ = ENNReal.ofReal a * p₁ + ENNReal.ofReal b * p₂ := by
          rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul]
          rfl
  specialize hAM (M⁻¹ * ∫⁻ x, f x) (N⁻¹ * ∫⁻ y, g y)
  rw [hcomp] at hAM
  exact (ENNReal.mul_le_mul_iff_right hc0 hcT).mp (hAM.trans hunit)

/-- **The Prékopa–Leindler inequality on `ℝ`.** -/
theorem Real.prekopaLeindler {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {f g h : ℝ → ENNReal} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (key : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z := by
  rcases eq_or_ne (∫⁻ x, f x) 0 with hF0 | hF0
  · rw [hF0, ENNReal.zero_rpow_of_pos ha, zero_mul]; exact zero_le
  rcases eq_or_ne (∫⁻ y, g y) 0 with hG0 | hG0
  · rw [hG0, ENNReal.zero_rpow_of_pos hb, mul_zero]; exact zero_le
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hF0 (by simp [hcon])
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, g y₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hG0 (by simp [hcon])
  set F : ℕ → ℝ → ENNReal := fun n x => min (f x) ((n : ENNReal) + 1) with hFdef
  set G : ℕ → ℝ → ENNReal := fun n y => min (g y) ((n : ENNReal) + 1) with hGdef
  have htopsup : ⨆ n : ℕ, ((n : ENNReal) + 1) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← ENNReal.iSup_natCast]
    exact iSup_mono fun n => le_self_add
  have hFlim : ∀ x, ⨆ n, F n x = f x := by
    intro x
    refine le_antisymm (iSup_le fun n => min_le_left _ _) (le_of_forall_lt fun c hc => ?_)
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp (htopsup ▸ lt_of_lt_of_le hc le_top :
      c < ⨆ n : ℕ, ((n : ENNReal) + 1))
    exact lt_of_lt_of_le (lt_min hc hn) (le_iSup (fun n => F n x) n)
  have hGlim : ∀ y, ⨆ n, G n y = g y := by
    intro y
    refine le_antisymm (iSup_le fun n => min_le_left _ _) (le_of_forall_lt fun c hc => ?_)
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp (htopsup ▸ lt_of_lt_of_le hc le_top :
      c < ⨆ n : ℕ, ((n : ENNReal) + 1))
    exact lt_of_lt_of_le (lt_min hc hn) (le_iSup (fun n => G n y) n)
  have hFmono : Monotone F := fun n m hnm x => by
    simp only [hFdef]
    exact min_le_min le_rfl (by gcongr)
  have hGmono : Monotone G := fun n m hnm y => by
    simp only [hGdef]
    exact min_le_min le_rfl (by gcongr)
  have hFmeas : ∀ n, Measurable (F n) := fun n => hf.min measurable_const
  have hGmeas : ∀ n, Measurable (G n) := fun n => hg.min measurable_const
  have hFint : (∫⁻ x, f x) = ⨆ n, ∫⁻ x, F n x := by
    rw [← lintegral_iSup hFmeas hFmono]
    exact lintegral_congr fun x => (hFlim x).symm
  have hGint : (∫⁻ y, g y) = ⨆ n, ∫⁻ y, G n y := by
    rw [← lintegral_iSup hGmeas hGmono]
    exact lintegral_congr fun y => (hGlim y).symm
  have hbdd : ∀ n : ℕ, (∫⁻ x, F n x) ^ a * (∫⁻ y, G n y) ^ b ≤ ∫⁻ z, h z := by
    intro n
    set M : ENNReal := ⨆ x, F n x with hM
    set N : ENNReal := ⨆ y, G n y with hN
    have hMT : M ≠ ⊤ := by
      refine ne_top_of_le_ne_top (by simp) (iSup_le fun x => ?_ : M ≤ (n : ENNReal) + 1)
      exact min_le_right _ _
    have hNT : N ≠ ⊤ := by
      refine ne_top_of_le_ne_top (by simp) (iSup_le fun y => ?_ : N ≤ (n : ENNReal) + 1)
      exact min_le_right _ _
    have hM0 : M ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le ?_ (le_iSup (fun x => F n x) x₀))
      simp only [hFdef, lt_min_iff, pos_iff_ne_zero]
      exact ⟨hx₀, by simp⟩
    have hN0 : N ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le ?_ (le_iSup (fun y => G n y) y₀))
      simp only [hGdef, lt_min_iff, pos_iff_ne_zero]
      exact ⟨hy₀, by simp⟩
    refine Real.prekopaLeindler_of_le ha hb hab (hFmeas n) (hGmeas n) hh hM0 hMT hN0 hNT
      (fun x => le_iSup (fun x => F n x) x) (fun y => le_iSup (fun y => G n y) y)
      (fun t ht ht1 => ?_) (fun t ht ht1 => ?_) (fun x y => ?_)
    · have hlt : ENNReal.ofReal t * M < M := by
        calc ENNReal.ofReal t * M = M * ENNReal.ofReal t := mul_comm _ _
          _ < M * 1 := ENNReal.mul_lt_mul_right hM0 hMT (ENNReal.ofReal_lt_one.mpr ht1)
          _ = M := mul_one M
      exact lt_iSup_iff.mp hlt
    · have hlt : ENNReal.ofReal t * N < N := by
        calc ENNReal.ofReal t * N = N * ENNReal.ofReal t := mul_comm _ _
          _ < N * 1 := ENNReal.mul_lt_mul_right hN0 hNT (ENNReal.ofReal_lt_one.mpr ht1)
          _ = N := mul_one N
      exact lt_iSup_iff.mp hlt
    · refine le_trans ?_ (key x y)
      gcongr
      · exact min_le_left _ _
      · exact min_le_left _ _
  have hSupRpow (u : ℕ → ENNReal) {p : ℝ} (hp : 0 < p) :
      (⨆ i, u i) ^ p = ⨆ i, u i ^ p := by
    have h := (ENNReal.orderIsoRpow p hp).map_iSup u
    simpa only [ENNReal.orderIsoRpow_apply] using h
  rw [hFint, hGint, hSupRpow _ ha, hSupRpow _ hb, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  refine le_trans ?_ (hbdd (max n m))
  gcongr
  · exact hFmono (le_max_left n m) _
  · exact hGmono (le_max_right n m) _

/-- `HasPrekopaLeindler μ` says that the Prékopa–Leindler inequality holds for the measure `μ` on
the real vector space `E`: whenever `f x ^ a * g y ^ b ≤ h (a • x + b • y)` pointwise, with
`a, b > 0` and `a + b = 1`, the same inequality holds for the integrals. -/
@[expose] def HasPrekopaLeindler {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) : Prop :=
  ∀ (a b : ℝ), 0 < a → 0 < b → a + b = 1 → ∀ (f g h : E → ENNReal),
    Measurable f → Measurable g → Measurable h →
      (∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) →
      (∫⁻ x, f x ∂μ) ^ a * (∫⁻ y, g y ∂μ) ^ b ≤ ∫⁻ z, h z ∂μ

/-- **Prékopa–Leindler tensorizes.** Integrating out the second factor turns the hypothesis on
`E × F` into the hypothesis on `E` for the three marginals, and Tonelli's theorem identifies the
marginals' integrals with the original ones. -/
theorem HasPrekopaLeindler.prod {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {μ : Measure E} {ν : Measure F}
    [SFinite ν] (hE : HasPrekopaLeindler μ) (hF : HasPrekopaLeindler ν) :
    HasPrekopaLeindler (μ.prod ν) := by
  intro a b ha hb hab f g h hf hg hh key
  have hkey1 : ∀ x₁ y₁ : E, (∫⁻ x₂, f (x₁, x₂) ∂ν) ^ a * (∫⁻ y₂, g (y₁, y₂) ∂ν) ^ b
      ≤ ∫⁻ z₂, h (a • x₁ + b • y₁, z₂) ∂ν := by
    intro x₁ y₁
    refine hF a b ha hb hab _ _ _ (hf.comp measurable_prodMk_left)
      (hg.comp measurable_prodMk_left) (hh.comp measurable_prodMk_left) fun x₂ y₂ => ?_
    exact key (x₁, x₂) (y₁, y₂)
  have hmf : Measurable fun x₁ => ∫⁻ x₂, f (x₁, x₂) ∂ν := hf.lintegral_prod_right'
  have hmg : Measurable fun y₁ => ∫⁻ y₂, g (y₁, y₂) ∂ν := hg.lintegral_prod_right'
  have hmh : Measurable fun z₁ => ∫⁻ z₂, h (z₁, z₂) ∂ν := hh.lintegral_prod_right'
  have hmain := hE a b ha hb hab _ _ _ hmf hmg hmh hkey1
  rwa [← lintegral_prod _ hf.aemeasurable, ← lintegral_prod _ hg.aemeasurable,
    ← lintegral_prod _ hh.aemeasurable] at hmain

/-- Prékopa–Leindler transports along a measure-preserving linear equivalence. -/
theorem HasPrekopaLeindler.of_measurePreserving {E F : Type*} [MeasurableSpace E]
    [AddCommGroup E] [Module ℝ E] [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]
    {μ : Measure E} {ν : Measure F} (e : E ≃ₗ[ℝ] F)
    (he : MeasurePreserving e μ ν) (hsymm : Measurable e.symm)
    (hF : HasPrekopaLeindler ν) : HasPrekopaLeindler μ := by
  intro a b ha hb hab f g h hf hg hh key
  have htrans : ∀ u : E → ENNReal, Measurable u →
      ∫⁻ x : F, (u ∘ e.symm) x ∂ν = ∫⁻ x : E, u x ∂μ := by
    intro u hu
    rw [← he.lintegral_comp (hu.comp hsymm)]
    exact lintegral_congr fun x => by simp
  have hkey : ∀ u v : F, (f ∘ e.symm) u ^ a * (g ∘ e.symm) v ^ b
      ≤ (h ∘ e.symm) (a • u + b • v) := by
    intro u v
    have hlin : e.symm (a • u + b • v) = a • e.symm u + b • e.symm v := by
      simp [map_add, map_smul]
    simpa [Function.comp_apply, hlin] using key (e.symm u) (e.symm v)
  have hmain := hF a b ha hb hab (f ∘ e.symm) (g ∘ e.symm) (h ∘ e.symm) (hf.comp hsymm)
    (hg.comp hsymm) (hh.comp hsymm) hkey
  rwa [htrans f hf, htrans g hg, htrans h hh] at hmain

/-- The Prékopa–Leindler inequality on Euclidean space in every finite dimension. -/
theorem hasPrekopaLeindler_euclideanSpace (n : ℕ) :
    HasPrekopaLeindler (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hPi : ∀ m : ℕ, HasPrekopaLeindler (volume : Measure (Fin m → ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro a b ha hb hab f g h _ _ _ key
      have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [volume_pi, Measure.pi_univ]; simp
      have hint : ∀ u : (Fin 0 → ℝ) → ENNReal, ∫⁻ x, u x = u 0 := by
        intro u
        have hc : (fun x : Fin 0 → ℝ => u x) = fun _ => u 0 :=
          funext fun x => congrArg u (funext fun i => i.elim0)
        rw [hc, lintegral_const, hvol, mul_one]
      rw [hint f, hint g, hint h]
      simpa using key 0 0
    | succ n ih =>
      have hprod : HasPrekopaLeindler (volume : Measure (ℝ × (Fin n → ℝ))) := by
        rw [Measure.volume_eq_prod]
        have hreal : HasPrekopaLeindler (volume : Measure ℝ) :=
          fun _ _ ha hb hab _ _ _ hf hg hh key =>
            Real.prekopaLeindler ha hb hab hf hg hh key
        exact hreal.prod ih
      refine HasPrekopaLeindler.of_measurePreserving
        (Fin.consLinearEquiv ℝ (fun _ : Fin (n + 1) => ℝ)).symm ?_ ?_ hprod
      · exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) _ _)
      · simp only [LinearEquiv.symm_symm]
        refine measurable_pi_iff.2 fun i => ?_
        induction i using Fin.cases with
        | zero => exact measurable_fst
        | succ j => exact (measurable_pi_apply j).comp measurable_snd
  exact HasPrekopaLeindler.of_measurePreserving (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
    (PiLp.volume_preserving_ofLp (Fin n)) (PiLp.volume_preserving_toLp (Fin n)).measurable
    (hPi n)

end
