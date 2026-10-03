/- GID: D5/S3/Arith/AbsoluteValues/Heights/MinkowskiSecond
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/MinkowskiSecond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minkowski's second theorem bounds the product of successive minima times convex-body volume. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import D5.S3.Arith.AbsoluteValues.Heights.QuotientFubini
public import D5.S3.Arith.AbsoluteValues.Heights.SuccessiveMinima
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

public section

open Metric Module MeasureTheory Set

open scoped ENNReal Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}

namespace ZLattice

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E}

/-- **Minkowski's second theorem, the upper bound** (Cassels, Chapter VIII, Theorem V, the
inequality (12) of VIII.1): `(∏ i < n, λ i) * volume B ≤ 2 ^ n * covolume L`. This is the
substantial half, the one Layer 5 and 6.3 consume.

The proof is Weyl's, through Cassels' Theorem IV, which is
`ZLattice.pow_mul_measure_inter_add_le`. Write `S t` for the image of the open dilate
`{gauge B < t}` in `E ⧸ L`. At `t = λ 0 / 2` the dilate injects into the quotient, so
`m (S t) = t ^ n * volume B`; and for `1 ≤ J < n` and `s = λ J / λ (J - 1)` the estimate gives
`m (S (s t)) ≥ s ^ (n - J) * m (S t)` at `t = λ (J - 1) / 2`, because there congruence modulo `L`
inside the dilate is congruence modulo `L ∩ span (v 0, …, v (J - 1))`, a sublattice of `ℤ`-rank at
most `J`. Chaining and bounding `m (S (λ (n - 1) / 2))` by the covolume multiplies `volume B` by
the telescoping product `λ 0 ^ n * ∏_{J = 1}^{n - 1} (λ J / λ (J - 1)) ^ (n - J) = ∏ i < n, λ i`.

⚠ **The chain runs on open dilates, and that is what removes closedness.** For a closed body the
dilate contains points of gauge exactly `t`, and the separation hypothesis would hold only for
`2 t < λ J` strictly; for `{gauge B < t}` it holds at `2 t = λ J`, which is where the chain needs
it. The body and its interior have the same measure because a convex set has null frontier.

⚠ **Cassels' Lemma 2 is not used.** He needs the adapted basis because he works in coordinates:
the integrality of the first `J` coordinates is how he sees that the translation stays in the
sublattice. Coordinate-free the sublattice `L ∩ span (v 0, …, v (J - 1))` is at hand and the only
thing wanted of it is its rank, which is the `ℝ`-dimension of its span by
`ZLattice.finrank_int_eq_finrank_real`. -/
theorem prod_successiveMinimum_mul_measure_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure] (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    (∏ i ∈ Finset.range (finrank ℝ E), successiveMinimum L B i) * (μ B).toReal ≤
      2 ^ finrank ℝ E * covolume L μ := by
  classical
  have hFundamental :
      ∃ F : Set E, MeasurableSet F ∧ (∀ x : E, ∃! v : L, (v : E) + x ∈ F) ∧ μ F ≠ ⊤ ∧
        (μ F).toReal = covolume L μ := by
    have hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    have hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
    set bZ := Module.Free.chooseBasis ℤ L with hbZ
    set bR := bZ.ofZLatticeBasis ℝ L with hbR
    have key : ∀ x : E, ∃! w : L, (w : E) + x ∈ ZSpan.fundamentalDomain bR := fun x ↦
      Eq.rec
        (motive := fun (N : Submodule ℤ E)
            (_ : Submodule.span ℤ (Set.range bR) = N) ↦
          ∃! w : N, (w : E) + x ∈ ZSpan.fundamentalDomain bR)
        (ZSpan.exist_unique_vadd_mem_fundamentalDomain bR x)
        (bZ.ofZLatticeBasis_span ℝ)
    refine ⟨ZSpan.fundamentalDomain bR, ZSpan.fundamentalDomain_measurableSet bR, key,
      (ZSpan.fundamentalDomain_isBounded bR).measure_lt_top.ne, ?_⟩
    rw [covolume_eq_measure_fundamentalDomain L μ (F := ZSpan.fundamentalDomain bR)
      (MeasureTheory.IsAddFundamentalDomain.mk'
        (ZSpan.fundamentalDomain_measurableSet bR).nullMeasurableSet key), measureReal_def]
  have hFlagRank {m : ℕ} (w : Fin m → E) (j : ℕ) :
      finrank ℝ (Submodule.span ℝ (w '' {i : Fin m | (i : ℕ) < j})) ≤ j := by
    have himg : w '' {i : Fin m | (i : ℕ) < j}
        = (((Finset.univ.filter (fun i : Fin m ↦ (i : ℕ) < j)).image w : Finset E) : Set E) := by
      ext x
      simp [Set.mem_image]
    rw [himg]
    refine le_trans (finrank_span_finset_le_card _) (le_trans Finset.card_image_le ?_)
    refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin m ↦ (i : ℕ))
      (fun i hi ↦ Finset.mem_range.2 (by simpa using hi)) Fin.val_injective.injOn) ?_
    simp
  obtain ⟨FL, hFLm, hFLfd, hFLfin, hFLcov⟩ := hFundamental
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  set lam : ℕ → ℝ := successiveMinimum L B
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hn0 | hnpos
  · -- a zero-dimensional space: the body and the fundamental domain are both the whole of `E`
    have hsub : Subsingleton E := by
      rw [← Module.finrank_zero_iff (R := ℝ)]
      exact hn0
    obtain ⟨w, hw, -⟩ := hFLfd 0
    have h0F : (0 : E) ∈ FL := by
      rwa [show (w : E) + (0 : E) = 0 from Subsingleton.elim _ _] at hw
    have hBF : B ⊆ FL := fun x _ ↦ by
      rwa [show x = (0 : E) from Subsingleton.elim _ _]
    rw [hn0]
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, pow_zero]
    rw [← hFLcov]
    exact ENNReal.toReal_mono hFLfin (measure_mono hBF)
  -- the open body, its dilates, and its measure
  have hCm : MeasurableSet (interior B) := isOpen_interior.measurableSet
  have hCc : Convex ℝ (interior B) := hB₀.interior
  have hmemC : ∀ t : ℝ, 0 < t → ∀ x : E, x ∈ t • interior B ↔ gauge B x < t := by
    intro t ht x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', ← gauge_lt_one_iff_mem_interior hB₀ h₀,
      gauge_smul_of_nonneg (inv_nonneg.2 ht.le), smul_eq_mul, inv_mul_lt_one₀ ht]
  have hvol : μ (interior B) = μ B := by
    refine le_antisymm (measure_mono interior_subset) ?_
    calc μ B ≤ μ (interior B ∪ frontier B) :=
          measure_mono fun x hx ↦ (em (x ∈ interior B)).imp id fun h ↦ ⟨subset_closure hx, h⟩
      _ ≤ μ (interior B) + μ (frontier B) := measure_union_le _ _
      _ = μ (interior B) := by rw [hB₀.addHaar_frontier μ, add_zero]
  have hAm : ∀ t : ℝ, MeasurableSet (t • interior B) := fun t ↦ hCm.const_smul₀ t
  -- positivity and monotonicity of the minima
  have hpos : ∀ i, i < finrank ℝ E → 0 < lam i :=
    fun i hi ↦ successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ hi
  have hmono : ∀ i j : ℕ, i ≤ j → j < finrank ℝ E → lam i ≤ lam j :=
    fun i j hij hj ↦ successiveMinimum_le_of_le hij hj hB₀ hB₁ hB₂
  -- the sublattices cut out by the flag of the family realizing the minima
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℕ → Submodule ℤ E, ∀ j, Λ j =
      L ⊓ (Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j})).restrictScalars ℤ :=
    ⟨_, fun _ ↦ rfl⟩
  have hΛle : ∀ j, Λ j ≤ L := fun j ↦ (hΛ j).le.trans inf_le_left
  have hΛdisc : ∀ j, DiscreteTopology (Λ j) := fun j ↦ by
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : Λ j ↦ (⟨(x : E), hΛle j x.2⟩ : L))
      (continuous_subtype_val.subtype_mk _) fun x y hxy ↦ ?_
    exact Subtype.ext (congrArg (fun z : L ↦ (z : E)) hxy)
  have hΛrank : ∀ j, finrank ℤ (Λ j) ≤ j := by
    intro j
    have hdisc : DiscreteTopology (Submodule.span ℤ (Λ j : Set E)) := by
      rw [Submodule.span_eq]
      exact hΛdisc j
    have hrank := Real.finrank_eq_int_finrank_of_discrete hdisc
    rw [Set.finrank, Set.finrank, Submodule.span_eq] at hrank
    rw [← hrank]
    refine le_trans (Submodule.finrank_mono ?_) (hFlagRank v j)
    refine Submodule.span_le.2 fun x hx ↦ ?_
    rw [hΛ j] at hx
    exact (Submodule.mem_inf.1 hx).2
  have hΛ0 : Λ 0 = ⊥ := by
    rw [hΛ 0]
    simp
  -- the separation hypothesis, straight from the dependence half of Cassels' Lemma 1
  have hsep : ∀ (j : ℕ) (t : ℝ), 0 < t → 2 * t ≤ lam j →
      ∀ x ∈ t • interior B, ∀ y ∈ t • interior B, x - y ∈ L → x - y ∈ Λ j := by
    intro j t ht hlt x hx y hy hxy
    have hgx : gauge B x < t := (hmemC t ht x).1 hx
    have hgy : gauge B y < t := (hmemC t ht y).1 hy
    have hadd := gauge_add_le hB₀ (absorbent_nhds_zero h₀) x (-y)
    rw [gauge_neg hB₁] at hadd
    have hg : gauge B (x - y) < lam j := by
      rw [sub_eq_add_neg]
      linarith
    have hspan : x - y ∈ Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) :=
      by
        by_contra hnot
        rcases le_or_gt (finrank ℝ E) j with hj | hj
        · change gauge B (x - y) < successiveMinimum L B j at hg
          have hempty : {t : ℝ | 0 < t ∧ ∃ w : Fin (j + 1) → E,
              (∀ k, w k ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ w} = ∅ := by
            ext t
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            rintro -
            rintro ⟨w, -, hind⟩
            have hcard := hind.fintype_card_le_finrank
            simp only [Fintype.card_fin] at hcard
            omega
          change gauge B (x - y) < sInf {t : ℝ | 0 < t ∧ ∃ w : Fin (j + 1) → E,
            (∀ k, w k ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ w} at hg
          rw [hempty, Real.sInf_empty] at hg
          exact absurd hg (not_lt.2 (gauge_nonneg _))
        · exact absurd
            (successiveMinimum_le_gauge_of_notMem_span L hB₀ hB₁ hB₂ hvL hvind hvg
              j hj.le (x - y) hxy hnot) (not_le.2 hg)
    rw [hΛ j]
    exact Submodule.mem_inf.2 ⟨hxy, (Submodule.restrictScalars_mem ℤ _ _).2 hspan⟩
  -- the quotient measure of the dilates, one per minimum
  have hLcount : Countable L := (open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] [instE3 : FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] => (show Countable Λ from by
      letI hdisc : DiscreteTopology (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective
      letI hzl : IsZLattice ℝ (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        ⟨(open scoped ENNReal Pointwise Real in (open MeasureTheory Measure Module Set ENNReal ZLattice in (fun {E : Type _} [instE1 : NormedAddCommGroup E] [instE2 : NormedSpace ℝ E] (Λ : Submodule ℤ E) => (show Submodule.span ℝ ((ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :
                Set ↥(Submodule.span ℝ (Λ : Set E))) = ⊤ from by exact (Submodule.span_span_coe_preimage (R := ℝ) (s := (Λ : Set E))))))) Λ⟩
      letI : Countable (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype) :=
        _root_.instCountable_of_discrete_submodule _
      exact Countable.of_equiv (ZLattice.comap ℝ Λ (Submodule.span ℝ (Λ : Set E)).subtype)
        (Submodule.comapSubtypeEquivOfLe (show Λ ≤ (Submodule.span ℝ (Λ : Set E)).restrictScalars ℤ from fun _ hx ↦ Submodule.subset_span hx)).toEquiv)))) L
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℝ≥0∞, ∀ j,
      M j = μ (FL ∩ ((lam j / 2) • interior B + (L : Set E))) := ⟨_, fun _ ↦ rfl⟩
  have hbotfd : ∀ x : E, ∃! w : (⊥ : Submodule ℤ E), (w : E) + x ∈ (univ : Set E) :=
    fun _ ↦ ⟨0, Set.mem_univ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  -- the base: below the first minimum the dilate injects into the quotient
  have hbase : M 0 = ENNReal.ofReal ((lam 0 / 2) ^ finrank ℝ E) * μ (interior B) := by
    have h0 : 0 < lam 0 := hpos 0 hnpos
    have hsep0 : ∀ x ∈ (lam 0 / 2) • interior B, ∀ y ∈ (lam 0 / 2) • interior B,
        x - y ∈ L → x - y ∈ (⊥ : Submodule ℤ E) := by
      intro x hx y hy hxy
      rw [← hΛ0]
      exact hsep 0 (lam 0 / 2) (by positivity) (by linarith) x hx y hy hxy
    have heq := measure_inter_add_eq_of_separated μ (bot_le : (⊥ : Submodule ℤ E) ≤ L)
      hbotfd hFLfd MeasurableSet.univ hFLm hFLfin (hAm (lam 0 / 2)) hsep0
    have hz : (lam 0 / 2) • interior B + ((⊥ : Submodule ℤ E) : Set E)
        = (lam 0 / 2) • interior B := by simp
    rw [hM, ← heq, Set.univ_inter, hz, Measure.addHaar_smul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (lam 0 / 2) ^ finrank ℝ E)]
  -- the inductive step: Cassels' Theorem IV applied at the `j`-th minimum
  have hstep : ∀ j, 1 ≤ j → j < finrank ℝ E →
      ENNReal.ofReal ((lam j / lam (j - 1)) ^ (finrank ℝ E - j)) * M (j - 1) ≤ M j := by
    intro j hj1 hjn
    have hjm : j - 1 < finrank ℝ E := by omega
    have hp1 : 0 < lam (j - 1) := hpos _ hjm
    have hpj : 0 < lam j := hpos _ hjn
    have hle : lam (j - 1) ≤ lam j := hmono _ _ (by omega) hjn
    have hs1 : 1 ≤ lam j / lam (j - 1) := (one_le_div hp1).2 hle
    have hsA : (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B)
        = (lam j / 2) • interior B := by
      rw [smul_smul]
      congr 1
      field_simp
    have hd : DiscreteTopology (Λ j) := hΛdisc j
    have hsepA : ∀ x ∈ (lam (j - 1) / 2) • interior B, ∀ y ∈ (lam (j - 1) / 2) • interior B,
        x - y ∈ L → x - y ∈ Λ j :=
      hsep j (lam (j - 1) / 2) (by positivity) (by linarith)
    have hsepB : ∀ x ∈ (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B),
        ∀ y ∈ (lam j / lam (j - 1)) • ((lam (j - 1) / 2) • interior B),
        x - y ∈ L → x - y ∈ Λ j := by
      rw [hsA]
      exact hsep j (lam j / 2) (by positivity) (by linarith)
    have hkey := pow_mul_measure_inter_add_le μ (hΛle j) hFLfd hFLm hFLfin
      (hAm (lam (j - 1) / 2)) (hCc.smul _) hs1 hsepA hsepB
    rw [hsA] at hkey
    rw [hM (j - 1), hM j]
    refine le_trans (mul_le_mul_left ?_ _) hkey
    have hrk := hΛrank j
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hs1 (by omega))
  -- the chain, carrying `λ 0 ⋯ λ j * λ j ^ (n - 1 - j)` up the minima
  have hchain : ∀ j, j < finrank ℝ E →
      ENNReal.ofReal ((∏ i ∈ Finset.range (j + 1), lam i) * lam j ^ (finrank ℝ E - 1 - j)) *
          μ (interior B) ≤ ENNReal.ofReal (2 ^ finrank ℝ E) * M j := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : 0 < lam 0 := hpos 0 hnpos
      have hlhs : lam 0 * lam 0 ^ (finrank ℝ E - 1 - 0)
          = 2 ^ finrank ℝ E * (lam 0 / 2) ^ finrank ℝ E := by
        rw [Nat.sub_zero, ← pow_succ', show finrank ℝ E - 1 + 1 = finrank ℝ E from by omega,
          div_pow]
        field_simp
      rw [hbase, Finset.prod_range_one, hlhs, ENNReal.ofReal_mul (by positivity), mul_assoc]
    | succ k ih =>
      intro hk
      have hkn : k < finrank ℝ E := by omega
      have hkpos : 0 < lam k := hpos k hkn
      have hk1pos : 0 < lam (k + 1) := hpos (k + 1) hk
      have hprodnn : (0:ℝ) ≤ ∏ i ∈ Finset.range (k + 1), lam i :=
        Finset.prod_nonneg fun i hi ↦ (hpos i (by have := Finset.mem_range.1 hi; omega)).le
      have e2 : finrank ℝ E - 1 - (k + 1) + 1 = finrank ℝ E - (k + 1) := by omega
      have hL2 : (∏ i ∈ Finset.range (k + 1 + 1), lam i) *
            lam (k + 1) ^ (finrank ℝ E - 1 - (k + 1))
          = (∏ i ∈ Finset.range (k + 1), lam i) * lam (k + 1) ^ (finrank ℝ E - (k + 1)) := by
        rw [Finset.prod_range_succ, mul_assoc, ← pow_succ', e2]
      have hR2 : ((∏ i ∈ Finset.range (k + 1), lam i) * lam k ^ (finrank ℝ E - 1 - k)) *
            (lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1))
          = (∏ i ∈ Finset.range (k + 1), lam i) * lam (k + 1) ^ (finrank ℝ E - (k + 1)) := by
        rw [show finrank ℝ E - 1 - k = finrank ℝ E - (k + 1) from by omega, div_pow]
        field_simp
      have hQ : (∏ i ∈ Finset.range (k + 1 + 1), lam i) *
            lam (k + 1) ^ (finrank ℝ E - 1 - (k + 1))
          = ((∏ i ∈ Finset.range (k + 1), lam i) * lam k ^ (finrank ℝ E - 1 - k)) *
            (lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1)) := hL2.trans hR2.symm
      have hstep' : ENNReal.ofReal ((lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1))) * M k
          ≤ M (k + 1) := by simpa using hstep (k + 1) (by omega) hk
      calc ENNReal.ofReal ((∏ i ∈ Finset.range (k + 1 + 1), lam i) *
              lam (k + 1) ^ (finrank ℝ E - 1 - (k + 1))) * μ (interior B)
          = ENNReal.ofReal ((lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1))) *
              (ENNReal.ofReal ((∏ i ∈ Finset.range (k + 1), lam i) *
                lam k ^ (finrank ℝ E - 1 - k)) * μ (interior B)) := by
            rw [hQ, ENNReal.ofReal_mul (by positivity)]
            ring
        _ ≤ ENNReal.ofReal ((lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1))) *
              (ENNReal.ofReal (2 ^ finrank ℝ E) * M k) := mul_le_mul_right (ih hkn) _
        _ = ENNReal.ofReal (2 ^ finrank ℝ E) *
              (ENNReal.ofReal ((lam (k + 1) / lam k) ^ (finrank ℝ E - (k + 1))) * M k) := by ring
        _ ≤ ENNReal.ofReal (2 ^ finrank ℝ E) * M (k + 1) := mul_le_mul_right hstep' _
  -- reading the chain off at the last minimum, against the covolume
  have hfin := hchain (finrank ℝ E - 1) (by omega)
  rw [show finrank ℝ E - 1 + 1 = finrank ℝ E from by omega, Nat.sub_self, pow_zero, mul_one] at hfin
  have hMle : M (finrank ℝ E - 1) ≤ μ FL := by
    rw [hM]
    exact measure_mono Set.inter_subset_left
  have hprodnn : (0:ℝ) ≤ ∏ i ∈ Finset.range (finrank ℝ E), lam i :=
    Finset.prod_nonneg fun i hi ↦ (hpos i (Finset.mem_range.1 hi)).le
  have hle2 : ENNReal.ofReal (∏ i ∈ Finset.range (finrank ℝ E), lam i) * μ B
      ≤ ENNReal.ofReal (2 ^ finrank ℝ E) * μ FL := by
    rw [← hvol]
    exact le_trans hfin (mul_le_mul_right hMle _)
  have hBfin : μ B ≠ ⊤ := hB₃.measure_lt_top.ne
  have hcalc := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFLfin) hle2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hprodnn,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 ^ finrank ℝ E), hFLcov] at hcalc
  exact hcalc

end ZLattice

section Examples

end Examples
