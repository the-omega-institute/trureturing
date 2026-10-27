/- GID: D5/S3/Topology/Measures/ClopenDisjointization
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/ClopenDisjointization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonmetric clopen disjointization by regularization and finite-history selection -/

import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Clopen
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Clopen disjointization of disjointly carried probabilities

The cluster probability obtained from compactness need not be regular. We
represent its continuous integral functional by a regular finite measure
before testing clopens. The selection only intersects finitely many large
sets at each stage. Its state records the actual preceding union.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal CompactlySupported Function

namespace D5.S3.Topology.Measures.ClopenDisjointization

universe u

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

private theorem exists_regular_clopen_cluster (μ : ℕ → ProbabilityMeasure K) :
    ∃ ρ : Measure K, ρ.Regular ∧ IsProbabilityMeasure ρ ∧
      ∀ P : Set K, IsClopen P →
        Tendsto (fun n => (μ n : Measure K).real P)
          (hyperfilter ℕ : Filter ℕ) (𝓝 (ρ.real P)) := by
  classical
  obtain ⟨ν, -, hν⟩ :=
    (isCompact_univ : IsCompact (univ : Set (ProbabilityMeasure K))).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map μ) (by exact Filter.univ_mem)
  have hlim : Tendsto μ (hyperfilter ℕ : Filter ℕ) (𝓝 ν) := by
    simpa only [Tendsto, Ultrafilter.coe_map] using hν
  let L : C_c(K, ℝ) →ₚ[ℝ] ℝ := CompactlySupportedContinuousMap.integralPositiveLinearMap (ν : Measure K)
  let ρ : Measure K := RealRMK.rieszMeasure L
  letI : ρ.Regular := inferInstance
  -- RMK is finite on compacts, and K is compact, before evaluating one.
  letI : IsFiniteMeasure ρ := inferInstance
  let one : C_c(K, ℝ) :=
    (CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ))
      (1 : C(K, ℝ))
  have hconst : (fun x : K => one x) = fun _ => (1 : ℝ) := rfl
  have hmassReal : ρ.real univ = 1 := by
    have h := RealRMK.integral_rieszMeasure L one
    change (∫ x, one x ∂ρ) = ∫ x, one x ∂(ν : Measure K) at h
    rw [hconst] at h
    simpa only [integral_const, smul_eq_mul, mul_one, Measure.real, measure_univ,
      ENNReal.toReal_one] using h
  have hmass : ρ univ = 1 := by
    calc
      ρ univ = ENNReal.ofReal (ρ.real univ) :=
        (ENNReal.ofReal_toReal (measure_ne_top ρ univ)).symm
      _ = 1 := by rw [hmassReal]; norm_num
  letI : IsProbabilityMeasure ρ := ⟨hmass⟩
  refine ⟨ρ, inferInstance, inferInstance, ?_⟩
  intro P hP
  let f : C(K, ℝ) := ⟨P.indicator (fun _ => 1), hP.continuous_indicator continuous_const⟩
  let g : C_c(K, ℝ) :=
    (CompactlySupportedContinuousMap.continuousMapEquiv (α := K) (β := ℝ)) f
  have htest : (ν : Measure K).real P = ρ.real P := by
    have h := RealRMK.integral_rieszMeasure L g
    change (∫ x, P.indicator (fun _ => (1 : ℝ)) x ∂ρ) =
      ∫ x, P.indicator (fun _ => (1 : ℝ)) x ∂(ν : Measure K) at h
    simpa only [integral_indicator_const _ hP.isOpen.measurableSet, smul_eq_mul,
      mul_one] using h.symm
  have h := (ProbabilityMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp hlim
  change Tendsto (fun n => ∫ x, P.indicator (fun _ => (1 : ℝ)) x ∂(μ n : Measure K))
    (hyperfilter ℕ : Filter ℕ)
    (𝓝 (∫ x, P.indicator (fun _ => (1 : ℝ)) x ∂(ν : Measure K))) at h
  simpa only [integral_indicator_const _ hP.isOpen.measurableSet, smul_eq_mul,
    mul_one, htest] using h

private theorem selection_step [ZeroDimensionalSpace K]
    (μ : ℕ → ProbabilityMeasure K) (hreg : ∀ n, (μ n : Measure K).Regular)
    (E : ℕ → Set K) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Disjoint on E)) (hcarry : ∀ n, (μ n : Measure K) (E n) = 1)
    (ρ : Measure K) [ρ.Regular] [IsProbabilityMeasure ρ]
    (hlim : ∀ P : Set K, IsClopen P →
      Tendsto (fun n => (μ n : Measure K).real P)
        (hyperfilter ℕ : Filter ℕ) (𝓝 (ρ.real P)))
    {η : ℝ} (hη : 0 < η) (hηone : η < 1)
    (P : Set K) (hP : IsClopen P) (hbudget : ρ.real P < η / 8) (m : ℕ) :
    ∃ n : ℕ, ∃ W : Set K, m ≤ n ∧ IsClopen W ∧ W.Nonempty ∧
      Disjoint P W ∧ 1 - η / 2 < (μ n : Measure K).real W ∧
      ρ.real (P ∪ W) < η / 8 := by
  classical
  let δ : ℝ := (η / 8 - ρ.real P) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsmallE : Tendsto (fun n => ρ.real (E n)) atTop (𝓝 0) :=
    (summable_measure_toReal hE hdisj).tendsto_atTop_zero
  have hA : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (μ n : Measure K).real P < η / 4 :=
    (hlim P hP).eventually (eventually_lt_nhds (by linarith : ρ.real P < η / 4))
  have hB : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), ρ.real (E n) < δ :=
    (hsmallE.eventually (eventually_lt_nhds hδ)).filter_mono Nat.hyperfilter_le_atTop
  have hT : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), m ≤ n :=
    (eventually_ge_atTop m).filter_mono Nat.hyperfilter_le_atTop
  obtain ⟨n, hnP, hnE, hmn⟩ := (hA.and (hB.and hT)).exists
  letI : (μ n : Measure K).Regular := hreg n
  have hEreal : (μ n : Measure K).real (E n) = 1 := by
    simp only [Measure.real, hcarry n, ENNReal.toReal_one]
  have hcore : 1 - η / 2 < (μ n : Measure K).real (E n \ P) := by
    have h := le_measureReal_sdiff (μ := (μ n : Measure K)) (s₁ := E n) (s₂ := P)
    rw [hEreal] at h
    linarith
  have hthreshold : 0 ≤ 1 - η / 2 := by linarith
  have hcore' : ENNReal.ofReal (1 - η / 2) < (μ n : Measure K) (E n \ P) :=
    (ENNReal.ofReal_lt_iff_lt_toReal hthreshold
      (measure_ne_top (μ n : Measure K) _)).2 hcore
  obtain ⟨C, hCE, hC, hCmass⟩ :=
    ((hE n).diff hP.isOpen.measurableSet).exists_lt_isCompact_of_ne_top
      (μ := (μ n : Measure K)) (measure_ne_top _ _) hcore'
  have hρC : ρ C < ENNReal.ofReal δ := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top ρ C) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hδ.le]
    exact (measureReal_mono (fun x hx => (hCE hx).1) (measure_ne_top ρ _)).trans_lt hnE
  obtain ⟨O, hCO, hO, hOmass⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := ρ) C (ENNReal.ofReal δ) hρC
  obtain ⟨W, hW, hCW, hWO⟩ :=
    exists_clopen_of_closed_subset_open hC.isClosed (hO.sdiff hP.isClosed)
      (fun x hx => ⟨hCO hx, (hCE hx).2⟩)
  have hmassW : 1 - η / 2 < (μ n : Measure K).real W := by
    have hCmassReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal hthreshold
        (measure_ne_top (μ n : Measure K) C)).1 hCmass
    exact hCmassReal.trans_le (measureReal_mono hCW (measure_ne_top _ _))
  have hWnonempty : W.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measureReal_empty] at hmassW
    linarith
  have hρW : ρ.real W < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top ρ O) ENNReal.ofReal_ne_top).2 hOmass
    rw [ENNReal.toReal_ofReal hδ.le] at h
    exact (measureReal_mono (fun x hx => (hWO hx).1) (measure_ne_top ρ O)).trans_lt h
  refine ⟨n, W, hmn, hW, hWnonempty, ?_, hmassW, ?_⟩
  · exact Set.disjoint_left.mpr (fun x hxP hxW => (hWO hxW).2 hxP)
  · have h := measureReal_union_le (μ := ρ) P W
    dsimp [δ] at hρW
    linarith

/-- Disjoint Borel carriers of regular probabilities admit an increasing
subsequence with pairwise disjoint nonempty clopen sets retaining mass
strictly greater than `1 - η / 2`. No countability hypothesis is imposed on K. -/
theorem exists_clopen_disjointization [ZeroDimensionalSpace K]
    (μ : ℕ → ProbabilityMeasure K) (hreg : ∀ n, (μ n : Measure K).Regular)
    (E : ℕ → Set K) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Disjoint on E)) (hcarry : ∀ n, (μ n : Measure K) (E n) = 1)
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∃ n : ℕ → ℕ, ∃ W : ℕ → Set K, StrictMono n ∧
      Pairwise (Disjoint on W) ∧
      ∀ k, IsClopen (W k) ∧ (W k).Nonempty ∧
        1 - η / 2 < (μ (n k) : Measure K).real (W k) := by
  classical
  obtain ⟨ρ, hρreg, hρprob, hlim⟩ := exists_regular_clopen_cluster μ
  letI : ρ.Regular := hρreg
  letI : IsProbabilityMeasure ρ := hρprob
  let S := {s : ℕ × Set K // IsClopen s.2 ∧ ρ.real s.2 < η / 8}
  have step (s : S) :
      ∃ n : ℕ, ∃ W : Set K, s.val.1 ≤ n ∧ IsClopen W ∧ W.Nonempty ∧
        Disjoint s.val.2 W ∧ 1 - η / 2 < (μ n : Measure K).real W ∧
        ρ.real (s.val.2 ∪ W) < η / 8 :=
    selection_step μ hreg E hE hdisj hcarry ρ hlim hη hηone
      s.val.2 s.property.1 s.property.2 s.val.1
  choose ix ws hindex hclopen hnonempty hdisjoint hmass hbudget using step
  let next : S → S := fun s =>
    ⟨(ix s + 1, s.val.2 ∪ ws s), s.property.1.union (hclopen s), hbudget s⟩
  let start : S := ⟨(0, ∅), isClopen_empty, by
    simpa only [measureReal_empty] using (div_pos hη (by norm_num : (0 : ℝ) < 8))⟩
  let z : ℕ → S := fun k => Nat.rec start (fun _ s => next s) k
  let n : ℕ → ℕ := fun k => ix (z k)
  let W : ℕ → Set K := fun k => ws (z k)
  let P : ℕ → Set K := fun k => (z k).val.2
  have hPstep (k : ℕ) : P (k + 1) = P k ∪ W k := rfl
  have hNstep (k : ℕ) : (z (k + 1)).val.1 = n k + 1 := rfl
  have hn : StrictMono n := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h := hindex (z (k + 1))
    rw [hNstep k] at h
    exact (Nat.lt_succ_self (n k)).trans_le h
  have hPmono : Monotone P := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hPstep]
    exact subset_union_left
  have hsep (i j : ℕ) (hij : i < j) : Disjoint (W i) (W j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hxi' : x ∈ P (i + 1) := by
      rw [hPstep]
      exact Or.inr hxi
    exact Set.disjoint_left.mp (hdisjoint (z j))
      (hPmono (Nat.succ_le_of_lt hij) hxi') hxj
  refine ⟨n, W, hn, ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hsep i j h
    · exact (hsep j i h).symm
  · intro k
    exact ⟨hclopen (z k), hnonempty (z k), hmass (z k)⟩

private theorem totalVariation_restrict (v : SignedMeasure K) {W : Set K}
    (hW : MeasurableSet W) :
    SignedMeasure.totalVariation (v.restrict W) = v.totalVariation.restrict W := by
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_restrict hW]

private theorem totalVariation_smul_real (v : SignedMeasure K) (c : ℝ) (A : Set K) :
    (c • v).totalVariation.real A = |c| * v.totalVariation.real A := by
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
    measureReal_nnreal_smul_apply, coe_nnnorm, Real.norm_eq_abs]

private theorem normalized_restriction (v : SignedMeasure K)
    (hreg : v.totalVariation.Regular) (hv : v.totalVariation.real univ = 1)
    {W : Set K} (hW : IsClopen W) (hq : 0 < v.totalVariation.real W) :
    let q := v.totalVariation.real W
    let t : SignedMeasure K := q⁻¹ • v.restrict W
    q ≤ 1 ∧ t.totalVariation.Regular ∧ t.totalVariation.real univ = 1 ∧
      t.totalVariation Wᶜ = 0 ∧
      (t - v).totalVariation.real univ = 2 * (1 - q) := by
  let q := v.totalVariation.real W
  let t : SignedMeasure K := q⁻¹ • v.restrict W
  change q ≤ 1 ∧ t.totalVariation.Regular ∧ t.totalVariation.real univ = 1 ∧
    t.totalVariation Wᶜ = 0 ∧ (t - v).totalVariation.real univ = 2 * (1 - q)
  have hqpos : 0 < q := hq
  have hqle : q ≤ 1 := by
    calc
      q ≤ v.totalVariation.real univ := measureReal_mono (subset_univ _) (measure_ne_top _ _)
      _ = 1 := hv
  have htv : t.totalVariation = ‖q⁻¹‖₊ • v.totalVariation.restrict W := by
    dsimp [t]
    rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
      ← SignedMeasure.totalVariation_eq_variation, totalVariation_restrict v hW.isOpen.measurableSet]
  have htreg : t.totalVariation.Regular := by
    letI : v.totalVariation.Regular := hreg
    letI : (v.totalVariation.restrict W).Regular :=
      Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)
    rw [htv]
    infer_instance
  have htnorm : t.totalVariation.real univ = 1 := by
    dsimp [t]
    rw [totalVariation_smul_real, abs_of_pos (inv_pos.mpr hqpos),
      totalVariation_restrict v hW.isOpen.measurableSet,
      measureReal_restrict_apply_univ]
    exact inv_mul_cancel₀ hqpos.ne'
  have htcarry : t.totalVariation Wᶜ = 0 := by
    rw [htv, Measure.smul_apply, Measure.restrict_apply hW.isOpen.measurableSet.compl]
    simp
  have hdW : (t - v).restrict W = (q⁻¹ - 1) • v.restrict W := by
    dsimp [t]
    rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_restrict v hW.isOpen.measurableSet hW.isOpen.measurableSet,
      inter_self, sub_smul, one_smul]
  have hdWc : (t - v).restrict Wᶜ = -v.restrict Wᶜ := by
    dsimp [t]
    rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_restrict v hW.isOpen.measurableSet.compl hW.isOpen.measurableSet,
      compl_inter_self, VectorMeasure.restrict_empty, smul_zero, zero_sub]
  have hcoeff : 0 ≤ q⁻¹ - 1 := by
    have h := (one_le_inv₀ hqpos).2 hqle
    linarith
  have hdiffW : (t - v).totalVariation.real W = (q⁻¹ - 1) * q := by
    calc
      (t - v).totalVariation.real W =
          (SignedMeasure.totalVariation ((t - v).restrict W)).real univ := by
        rw [totalVariation_restrict _ hW.isOpen.measurableSet,
          measureReal_restrict_apply_univ]
      _ = (SignedMeasure.totalVariation ((q⁻¹ - 1) • v.restrict W)).real univ := by rw [hdW]
      _ = (q⁻¹ - 1) * q := by
        rw [totalVariation_smul_real, abs_of_nonneg hcoeff,
          totalVariation_restrict v hW.isOpen.measurableSet,
          measureReal_restrict_apply_univ]
  have hdiffWc : (t - v).totalVariation.real Wᶜ = 1 - q := by
    calc
      (t - v).totalVariation.real Wᶜ =
          (SignedMeasure.totalVariation ((t - v).restrict Wᶜ)).real univ := by
        rw [totalVariation_restrict _ hW.isOpen.measurableSet.compl,
          measureReal_restrict_apply_univ]
      _ = (SignedMeasure.totalVariation (-v.restrict Wᶜ)).real univ := by rw [hdWc]
      _ = 1 - q := by
        rw [SignedMeasure.totalVariation_neg,
          totalVariation_restrict v hW.isOpen.measurableSet.compl,
          measureReal_restrict_apply_univ, measureReal_compl hW.isOpen.measurableSet, hv]
  refine ⟨hqle, htreg, htnorm, htcarry, ?_⟩
  rw [← measureReal_add_measureReal_compl hW.isOpen.measurableSet, hdiffW, hdiffWc]
  rw [sub_mul, inv_mul_cancel₀ hqpos.ne']
  ring

private theorem exists_common_sign (t : ℕ → SignedMeasure K)
    (ht : ∀ k, (t k).totalVariation.real univ = 1) :
    ∃ s : ℝ, ∃ j : ℕ → ℕ, (s = 1 ∨ s = -1) ∧ StrictMono j ∧
      ∀ k, (1 / 2 : ℝ) ≤ (s • t (j k)).toJordanDecomposition.posPart.real univ := by
  classical
  let p : ℕ → ℝ := fun k => (t k).toJordanDecomposition.posPart.real univ
  let n : ℕ → ℝ := fun k => (t k).toJordanDecomposition.negPart.real univ
  have hsum (k : ℕ) : p k + n k = 1 := by
    have h := ht k
    rw [SignedMeasure.totalVariation, measureReal_add_apply] at h
    exact h
  by_cases h : ∀ N : ℕ, ∃ k > N, (1 / 2 : ℝ) ≤ p k
  · obtain ⟨j, hj, hp⟩ := Nat.exists_strictMono_subsequence h
    exact ⟨1, j, Or.inl rfl, hj, by simpa only [one_smul] using hp⟩
  · push Not at h
    obtain ⟨N, hN⟩ := h
    have hneg : ∀ M : ℕ, ∃ k > M, (1 / 2 : ℝ) ≤ n k := by
      intro M
      refine ⟨max M N + 1, lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _), ?_⟩
      have hp := hN (max M N + 1)
        (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))
      linarith [hsum (max M N + 1)]
    obtain ⟨j, hj, hn⟩ := Nat.exists_strictMono_subsequence hneg
    refine ⟨-1, j, Or.inr rfl, hj, ?_⟩
    intro k
    simpa only [neg_one_smul, SignedMeasure.toJordanDecomposition_neg,
      JordanDecomposition.neg_posPart] using hn k

/-- The real signed consumer uses total variation for both carrying and
normalization. The common sign acts on the approximant and the original
together. No weak-star convergence of the approximants is asserted. -/
theorem exists_signed_clopen_disjointization [ZeroDimensionalSpace K]
    (v : ℕ → SignedMeasure K) (hreg : ∀ n, (v n).totalVariation.Regular)
    (hnorm : ∀ n, (v n).totalVariation.real univ = 1)
    (E : ℕ → Set K) (hE : ∀ n, MeasurableSet (E n))
    (hdisj : Pairwise (Disjoint on E))
    (hcarry : ∀ n, (v n).totalVariation (E n)ᶜ = 0)
    {η : ℝ} (hη : 0 < η) (hηone : η < 1) :
    ∃ n : ℕ → ℕ, ∃ W : ℕ → Set K, ∃ t : ℕ → SignedMeasure K,
      StrictMono n ∧ Pairwise (Disjoint on W) ∧
      (∀ k, let q := (v (n k)).totalVariation.real (W k)
        IsClopen (W k) ∧ (W k).Nonempty ∧ 1 - η < q ∧ 0 < q ∧ q ≤ 1 ∧
          t k = q⁻¹ • (v (n k)).restrict (W k) ∧
          (t k).totalVariation.Regular ∧ (t k).totalVariation.real univ = 1 ∧
          (t k).totalVariation (W k)ᶜ = 0 ∧
          (t k - v (n k)).totalVariation.real univ = 2 * (1 - q) ∧
          (t k - v (n k)).totalVariation.real univ < 2 * η) ∧
      ∃ s : ℝ, ∃ j : ℕ → ℕ, (s = 1 ∨ s = -1) ∧ StrictMono j ∧
        StrictMono (n ∘ j) ∧
        ∀ k, (s • t (j k)).totalVariation = (t (j k)).totalVariation ∧
          (s • v (n (j k))).totalVariation = (v (n (j k))).totalVariation ∧
          (1 / 2 : ℝ) ≤ (s • t (j k)).toJordanDecomposition.posPart.real univ ∧
          (s • t (j k) - s • v (n (j k))).totalVariation.real univ =
            2 * (1 - (v (n (j k))).totalVariation.real (W (j k))) := by
  classical
  have hprob (k : ℕ) : IsProbabilityMeasure (v k).totalVariation := by
    constructor
    calc
      (v k).totalVariation univ =
          ENNReal.ofReal ((v k).totalVariation.real univ) := (ofReal_measureReal).symm
      _ = 1 := by rw [hnorm k]; norm_num
  let μ : ℕ → ProbabilityMeasure K := fun k => ⟨(v k).totalVariation, hprob k⟩
  have hμE (k : ℕ) : (μ k : Measure K) (E k) = 1 := by
    letI : IsProbabilityMeasure (v k).totalVariation := hprob k
    change (v k).totalVariation (E k) = 1
    have h := measure_add_measure_compl (μ := (v k).totalVariation) (hE k)
    rw [hcarry k, add_zero, measure_univ] at h
    exact h
  obtain ⟨n, W, hn, hWdisj, hW⟩ :=
    exists_clopen_disjointization μ hreg E hE hdisj hμE hη hηone
  let q : ℕ → ℝ := fun k => (v (n k)).totalVariation.real (W k)
  let t : ℕ → SignedMeasure K := fun k => (q k)⁻¹ • (v (n k)).restrict (W k)
  have hq (k : ℕ) : 0 < q k := by
    have h := (hW k).2.2
    change 1 - η / 2 < q k at h
    linarith
  have hnormt (k : ℕ) : (t k).totalVariation.real univ = 1 :=
    (normalized_restriction (v (n k)) (hreg (n k)) (hnorm (n k)) (hW k).1 (hq k)).2.2.1
  obtain ⟨s, j, hs, hj, hhalf⟩ := exists_common_sign t hnormt
  refine ⟨n, W, t, hn, hWdisj, ?_, s, j, hs, hj, hn.comp hj, ?_⟩
  · intro k
    obtain ⟨hqle, htreg, htnorm, htcarry, herror⟩ :=
      normalized_restriction (v (n k)) (hreg (n k)) (hnorm (n k)) (hW k).1 (hq k)
    have hmass := (hW k).2.2
    change 1 - η / 2 < q k at hmass
    change (t k - v (n k)).totalVariation.real univ = 2 * (1 - q k) at herror
    refine ⟨(hW k).1, (hW k).2.1, by linarith, hq k, hqle, rfl,
      htreg, htnorm, htcarry, herror, ?_⟩
    rw [herror]
    linarith
  · intro k
    have htv (w : SignedMeasure K) : (s • w).totalVariation = w.totalVariation := by
      rcases hs with rfl | rfl
      · rw [one_smul]
      · rw [neg_one_smul, SignedMeasure.totalVariation_neg]
    refine ⟨htv _, htv _, hhalf k, ?_⟩
    rw [← smul_sub, totalVariation_smul_real]
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [habs, one_mul]
    exact (normalized_restriction (v (n (j k))) (hreg (n (j k))) (hnorm (n (j k)))
      (hW (j k)).1 (hq (j k))).2.2.2.2

end D5.S3.Topology.Measures.ClopenDisjointization
