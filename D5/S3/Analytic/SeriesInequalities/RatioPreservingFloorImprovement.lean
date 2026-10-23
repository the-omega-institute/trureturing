/- GID: D5/S3/Analytic/SeriesInequalities/RatioPreservingFloorImprovement
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/RatioPreservingFloorImprovement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable floors admit unbounded amplification with the same adjacent ratio. -/

/- All three theorems concern arbitrary infinite real sequences and a common
   noncomputable construction. They do not enumerate a bounded domain, supply
   a checker, perform a numeric reduction, or certify a finite instance. The
   computational-content kind is none; its other utility fields do not apply. -/

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter Finset
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement

/-- Flatten a floor above the height of its `N`th entry. -/
def cappedFloor (η : ℕ → ℝ) (N k : ℕ) : ℝ := min (η k) (η N)

private lemma cappedFloor_summable {η : ℕ → ℝ}
    (hpos : ∀ k, 0 < η k) (hs : Summable η) (N : ℕ) :
    Summable (cappedFloor η N) :=
  Summable.of_nonneg_of_le (fun k => le_min (hpos k).le (hpos N).le)
    (fun _ => min_le_left _ _) hs

private lemma cappedFloor_mass_tendsto_zero {η : ℕ → ℝ}
    (hpos : ∀ k, 0 < η k) (hs : Summable η) :
    Tendsto (fun N => ∑' k, cappedFloor η N k) atTop (𝓝 0) := by
  have hterm (k : ℕ) :
      Tendsto (fun N => cappedFloor η N k) atTop (𝓝 0) := by
    simpa only [cappedFloor, min_eq_right (hpos k).le] using
      (tendsto_const_nhds.min hs.tendsto_atTop_zero :
        Tendsto (fun N => min (η k) (η N)) atTop (𝓝 (min (η k) 0)))
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖cappedFloor η N k‖ ≤ η k :=
    Eventually.of_forall fun N k => by
      rw [cappedFloor, Real.norm_eq_abs, abs_of_nonneg (le_min (hpos k).le (hpos N).le)]
      exact min_le_left _ _
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs hterm hbound

private lemma cappedFloor_adjacent {η : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k)
    (hratio : ∀ k, η k ≤ R * η (k + 1)) (N k : ℕ) :
    cappedFloor η N k ≤ R * cappedFloor η N (k + 1) := by
  unfold cappedFloor
  by_cases h : η (k + 1) ≤ η N
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (hratio k)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans (by nlinarith [hpos N])

/-- A single new floor has arbitrarily small total mass, keeps the original
adjacent-ratio bound, dominates a positive fixed multiple of the old floor
at every index, and dominates every fixed multiple on a sufficiently late tail.
The same floor works for all the tail multiples. -/
theorem exists_ratio_preserving_improvement {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1)) (hε : 0 < ε) :
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < θ k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) := by
  classical
  let budget : ℕ → ℝ := fun j => (ε / 2) * (1 / 2 : ℝ) ^ j
  have hbudget : Summable budget :=
    (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left _
  have hbudget_sum : (∑' j, budget j) = ε := by
    change (∑' j, (ε / 2) * (1 / 2 : ℝ) ^ j) = ε
    rw [tsum_mul_left]
    rw [tsum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)]
    ring
  have hsmall : ∀ j, ∃ N, (∑' k, cappedFloor η N k) ≤ budget j := by
    intro j
    have hb : 0 < budget j := by dsimp [budget]; positivity
    obtain ⟨N, hN⟩ := ((tendsto_order.1
      (cappedFloor_mass_tendsto_zero hpos hs)).2 _ hb).exists
    exact ⟨N, hN.le⟩
  choose N hN using hsmall
  let f : ℕ → ℕ → ℝ := fun j k => cappedFloor η (N j) k
  have hfpos : ∀ j k, 0 < f j k := fun j k => lt_min (hpos k) (hpos (N j))
  have hfrow : ∀ j, Summable (f j) := fun j => cappedFloor_summable hpos hs _
  have hrows : Summable (fun j => ∑' k, f j k) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun k => (hfpos j k).le))
      hN hbudget
  have hprod : Summable (fun p : ℕ × ℕ => f p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => (hfpos p.1 p.2).le)).2 ⟨hfrow, hrows⟩
  have hswap : Summable (fun p : ℕ × ℕ => f p.2 p.1) :=
    hprod.comp_injective (Equiv.prodComm ℕ ℕ).injective
  have hcols : (∀ k, Summable (fun j => f j k)) ∧
      Summable (fun k => ∑' j, f j k) :=
    (summable_prod_of_nonneg (fun p => (hfpos p.2 p.1).le)).1 hswap
  let θ : ℕ → ℝ := fun k => ∑' j, f j k
  have hθsum : Summable θ := hcols.2
  have hmass : (∑' k, θ k) ≤ ε := by
    calc
      (∑' k, θ k) = ∑' j, ∑' k, f j k := hprod.tsum_comm
      _ ≤ ∑' j, budget j := hrows.tsum_le_tsum hN hbudget
      _ = ε := hbudget_sum
  have hθpos : ∀ k, 0 < θ k := fun k =>
    (hfpos 0 k).trans_le ((hcols.1 k).le_tsum 0 (fun j _ => (hfpos j k).le))
  refine ⟨θ, hθpos, ?_, hθsum, hmass, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact (hcols.1 l).tsum_le_tsum
      (fun j => min_le_min_right _ (hanti hkl)) (hcols.1 k)
  · intro k
    exact (hθsum.le_tsum k (fun i _ => (hθpos i).le)).trans hmass
  · intro k
    calc
      θ k ≤ ∑' j, R * f j (k + 1) :=
        (hcols.1 k).tsum_le_tsum (fun j => cappedFloor_adjacent hR hpos hratio _ _)
          ((hcols.1 (k + 1)).mul_left R)
      _ = R * θ (k + 1) := (hcols.1 (k + 1)).tsum_mul_left R
  · let c₀ : ℝ := η (N 0) / η 0
    have hc₀pos : 0 < c₀ := div_pos (hpos _) (hpos _)
    have hc₀le : c₀ ≤ 1 := (div_le_one (hpos 0)).2 (hanti (Nat.zero_le _))
    refine ⟨c₀, hc₀pos, fun k => ?_⟩
    have hcap : c₀ * η k ≤ f 0 k := by
      change c₀ * η k ≤ min (η k) (η (N 0))
      refine le_min ?_ ?_
      · nlinarith [hpos k]
      · calc
          c₀ * η k ≤ c₀ * η 0 := mul_le_mul_of_nonneg_left
            (hanti (Nat.zero_le k)) hc₀pos.le
          _ = η (N 0) := div_mul_cancel₀ _ (ne_of_gt (hpos 0))
    exact hcap.trans ((hcols.1 k).le_tsum 0 (fun j _ => (hfpos j k).le))
  · intro B hB
    obtain ⟨J, hJ⟩ := exists_nat_gt B
    let L : ℕ := (range J).sup N
    refine ⟨L, fun k hk => ?_⟩
    have heq : ∀ j ∈ range J, f j k = η k := by
      intro j hj
      exact min_eq_left (hanti ((le_sup hj).trans hk))
    calc
      B * η k ≤ (J : ℝ) * η k := mul_le_mul_of_nonneg_right hJ.le (hpos k).le
      _ = ∑ j ∈ range J, f j k := by
        rw [sum_congr rfl heq]
        simp only [sum_const, card_range, nsmul_eq_mul]
      _ ≤ θ k := (hcols.1 k).sum_le_tsum (range J) (fun j _ => (hfpos j k).le)

/-- The extended nonnegative power profile allows an infinite supremum. -/
def powerProfile (η w : ℕ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (w k * η k ^ (-s))

/-- The same improved floor controls an entire positive exponent interval.
For each tail amplification `H`, the finite-prefix constant is independent
of the exponent and of every choice of weights in `[0,1]`. -/
theorem exists_uniform_profile_improvement {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1))
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < θ k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) ∧
      (∀ a sLo : ℝ, 0 < sLo → sLo ≤ a → ∀ H : ℝ, 1 ≤ H →
        ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, sLo ≤ s → s ≤ a →
          ∀ w : ℕ → ℝ, (∀ k, 0 ≤ w k ∧ w k ≤ 1) →
            powerProfile θ w s ≤
              max (ENNReal.ofReal C)
                (ENNReal.ofReal (H ^ (-sLo)) * powerProfile η w s)) := by
  classical
  obtain ⟨θ, hθpos, hθanti, hθsum, hθmass, hθle, hθratio, hθglobal, hθtail⟩ :=
    exists_ratio_preserving_improvement hR hpos hanti hs hratio hε
  refine ⟨θ, hθpos, hθanti, hθsum, hθmass, hθle, hθratio, hθglobal, hθtail, ?_⟩
  intro a sLo hsLo _ H hH
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  obtain ⟨L, hL⟩ := hθtail H hHpos
  let C : ℝ := 1 + ∑ k ∈ range L, θ k ^ (-a)
  have hC : 0 < C := by
    have hsum := sum_nonneg (fun k (_ : k ∈ range L) =>
      (Real.rpow_pos_of_pos (hθpos k) (-a)).le)
    dsimp [C]
    linarith
  refine ⟨C, hC, fun s hslo hshi w hw => ?_⟩
  refine iSup_le fun k => ?_
  by_cases hk : k < L
  · have hexp : θ k ^ (-s) ≤ θ k ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_ge (hθpos k) ((hθle k).trans hεone)
        (neg_le_neg hshi)
    have hterm : θ k ^ (-a) ≤ ∑ i ∈ range L, θ i ^ (-a) :=
      single_le_sum (fun i _ => (Real.rpow_pos_of_pos (hθpos i) (-a)).le)
        (mem_range.mpr hk)
    have hpre : w k * θ k ^ (-s) ≤ C := by
      calc
        w k * θ k ^ (-s) ≤ θ k ^ (-s) :=
          mul_le_of_le_one_left (Real.rpow_pos_of_pos (hθpos k) (-s)).le (hw k).2
        _ ≤ θ k ^ (-a) := hexp
        _ ≤ C := by dsimp [C]; linarith
    exact (ENNReal.ofReal_le_ofReal hpre).trans (le_max_left _ _)
  · have hscale : θ k ^ (-s) ≤ H ^ (-sLo) * η k ^ (-s) := by
      calc
        θ k ^ (-s) ≤ (H * η k) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hHpos (hpos k))
            (hL k (Nat.le_of_not_gt hk)) (by linarith)
        _ = H ^ (-s) * η k ^ (-s) := Real.mul_rpow hHpos.le (hpos k).le
        _ ≤ H ^ (-sLo) * η k ^ (-s) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hH (neg_le_neg hslo))
            (Real.rpow_pos_of_pos (hpos k) (-s)).le
    have hweighted : w k * θ k ^ (-s) ≤ H ^ (-sLo) * (w k * η k ^ (-s)) := by
      calc
        w k * θ k ^ (-s) ≤ w k * (H ^ (-sLo) * η k ^ (-s)) :=
          mul_le_mul_of_nonneg_left hscale (hw k).1
        _ = H ^ (-sLo) * (w k * η k ^ (-s)) := by ring
    calc
      ENNReal.ofReal (w k * θ k ^ (-s)) ≤
          ENNReal.ofReal (H ^ (-sLo) * (w k * η k ^ (-s))) :=
        ENNReal.ofReal_le_ofReal hweighted
      _ = ENNReal.ofReal (H ^ (-sLo)) * ENNReal.ofReal (w k * η k ^ (-s)) :=
        ENNReal.ofReal_mul (Real.rpow_pos_of_pos hHpos (-sLo)).le
      _ ≤ ENNReal.ofReal (H ^ (-sLo)) * powerProfile η w s :=
        mul_le_mul le_rfl (le_iSup (fun i => ENNReal.ofReal (w i * η i ^ (-s))) k)
          zero_le zero_le
      _ ≤ max (ENNReal.ofReal C)
          (ENNReal.ofReal (H ^ (-sLo)) * powerProfile η w s) := le_max_right _ _

/-- The numerical near-critical profile on one fixed grid. This definition
does not assert any relation to the costs of an actual sampling procedure. -/
def geometricProfile (η n : ℕ → ℝ) (a u : ℝ) : ℝ≥0∞ :=
  powerProfile η (fun k => n k ^ (-u)) (a - u)

private lemma geometricProfile_toReal_tendsto_atTop {η n : ℕ → ℝ} {a : ℝ}
    (hpos : ∀ k, 0 < η k) (hs : Summable η)
    (hn : ∀ k, 1 ≤ n k) (ha : 0 < a)
    (hfinite : ∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile η n a u ≠ ⊤) :
    Tendsto (fun u => (geometricProfile η n a u).toReal) (𝓝[>] (0 : ℝ)) atTop := by
  have hη : Tendsto η atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs.tendsto_atTop_zero, Eventually.of_forall hpos⟩
  have hpow : Tendsto (fun k => η k ^ (-a)) atTop atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr ha)).comp hη
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨k, hk⟩ := (tendsto_atTop.1 hpow (B + 1)).exists
  have hnpos : 0 < n k := zero_lt_one.trans_le (hn k)
  have hterm : Tendsto (fun u : ℝ => n k ^ (-u) * η k ^ (-(a - u)))
      (𝓝[>] (0 : ℝ)) (𝓝 (η k ^ (-a))) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℝ => n k)
      (𝓝[>] (0 : ℝ)) (𝓝 (n k))).rpow hu.neg (Or.inl hnpos.ne')
    have hexp : Tendsto (fun u : ℝ => -(a - u)) (𝓝[>] (0 : ℝ)) (𝓝 (-a)) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a)
        (𝓝[>] (0 : ℝ)) (𝓝 a)).sub hu).neg
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℝ => η k)
      (𝓝[>] (0 : ℝ)) (𝓝 (η k))).rpow hexp (Or.inl (hpos k).ne')
    simpa using h₁.mul h₂
  have hlarge : ∀ᶠ u in 𝓝[>] (0 : ℝ), B < n k ^ (-u) * η k ^ (-(a - u)) :=
    (tendsto_order.1 hterm).1 B (by linarith)
  filter_upwards [hfinite, hlarge] with u hfin hlarge
  have hnonneg : 0 ≤ n k ^ (-u) * η k ^ (-(a - u)) :=
    (mul_pos (Real.rpow_pos_of_pos hnpos _) (Real.rpow_pos_of_pos (hpos k) _)).le
  have hle : ENNReal.ofReal (n k ^ (-u) * η k ^ (-(a - u))) ≤
      geometricProfile η n a u := le_iSup
        (fun i => ENNReal.ofReal (n i ^ (-u) * η i ^ (-(a - u)))) k
  exact hlarge.le.trans (by
    simpa only [ENNReal.toReal_ofReal hnonneg] using ENNReal.toReal_mono hfin hle)

/-- One improved floor works for every fixed grid and every near-critical
exponent. Whenever the old numerical profile is eventually finite, so is
the new one, and their ratio tends to zero with a positive finite denominator.
The construction is independent of the grid, the exponent, and the limit parameter. -/
theorem exists_strict_profile_improvement {η : ℕ → ℝ} {R ε : ℝ}
    (hR : 1 ≤ R) (hpos : ∀ k, 0 < η k) (hanti : Antitone η)
    (hs : Summable η) (hratio : ∀ k, η k ≤ R * η (k + 1))
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ θ : ℕ → ℝ,
      (∀ k, 0 < θ k) ∧ Antitone θ ∧ Summable θ ∧
      (∑' k, θ k) ≤ ε ∧ (∀ k, θ k ≤ ε) ∧
      (∀ k, θ k ≤ R * θ (k + 1)) ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ * η k ≤ θ k) ∧
      (∀ B : ℝ, 0 < B → ∃ L : ℕ, ∀ k, L ≤ k → B * η k ≤ θ k) ∧
      (∀ n : ℕ → ℝ, (∀ k, 1 ≤ n k) → ∀ a : ℝ, 0 < a →
        (∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile η n a u ≠ ⊤) →
          (∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile θ n a u ≠ ⊤) ∧
          (∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < (geometricProfile η n a u).toReal) ∧
          Tendsto (fun u => (geometricProfile θ n a u).toReal /
            (geometricProfile η n a u).toReal) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  obtain ⟨θ, hθpos, hθanti, hθsum, hθmass, hθle, hθratio, hθglobal, hθtail, hprof⟩ :=
    exists_uniform_profile_improvement hR hpos hanti hs hratio hε hεone
  refine ⟨θ, hθpos, hθanti, hθsum, hθmass, hθle, hθratio, hθglobal, hθtail, ?_⟩
  intro n hn a ha hfinite
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u ∧ u < a / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_order.1 hu).2 (a / 2) (half_pos ha)] with u hupos hult
    exact ⟨hupos, hult⟩
  have hweights (u : ℝ) (hupos : 0 < u) (k : ℕ) :
      0 ≤ n k ^ (-u) ∧ n k ^ (-u) ≤ 1 :=
    ⟨Real.rpow_nonneg (zero_le_one.trans (hn k)) _,
      Real.rpow_le_one_of_one_le_of_nonpos (hn k) (neg_nonpos.mpr hupos.le)⟩
  have hdiverge := geometricProfile_toReal_tendsto_atTop hpos hs hn ha hfinite
  have hdenpos : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < (geometricProfile η n a u).toReal := by
    filter_upwards [tendsto_atTop.1 hdiverge 1] with u huone
    exact zero_lt_one.trans_le huone
  obtain ⟨C₁, hC₁, hbound₁⟩ := hprof a (a / 2) (half_pos ha) (by linarith) 1 le_rfl
  have hnewfinite : ∀ᶠ u in 𝓝[>] (0 : ℝ), geometricProfile θ n a u ≠ ⊤ := by
    filter_upwards [hsmall, hfinite] with u hu hfin
    have hbound := hbound₁ (a - u) (by linarith [hu.2]) (by linarith [hu.1])
      (fun k => n k ^ (-u)) (hweights u hu.1)
    have hmax : max (ENNReal.ofReal C₁) (geometricProfile η n a u) ≠ ⊤ :=
      lt_top_iff_ne_top.1 (max_lt ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin))
    exact ne_top_of_le_ne_top hmax
      (by simpa only [geometricProfile, Real.one_rpow, ENNReal.ofReal_one, one_mul]
        using hbound)
  refine ⟨hnewfinite, hdenpos, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro b hb
    exact Eventually.of_forall fun u => hb.trans_le
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  · intro β hβ
    have hHsmall : ∀ᶠ H : ℝ in atTop, H ^ (-(a / 2)) < β / 2 :=
      (tendsto_order.1 (tendsto_rpow_neg_atTop (half_pos ha))).2 (β / 2) (half_pos hβ)
    obtain ⟨H, hH, hHpow⟩ := (eventually_ge_atTop 1).and hHsmall |>.exists
    obtain ⟨C, hC, hbound⟩ := hprof a (a / 2) (half_pos ha) (by linarith) H hH
    have hHpos : 0 < H := zero_lt_one.trans_le hH
    filter_upwards [hsmall, hfinite, hnewfinite, hdenpos,
      tendsto_atTop.1 hdiverge (2 * C / β)] with u hu hfin hnew hden hlarge
    have hcost : C ≤ (β / 2) * (geometricProfile η n a u).toReal := by
      have := (div_le_iff₀ hβ).1 hlarge
      nlinarith
    have hboundu := hbound (a - u) (by linarith [hu.2]) (by linarith [hu.1])
      (fun k => n k ^ (-u)) (hweights u hu.1)
    have hprod : ENNReal.ofReal (H ^ (-(a / 2))) * geometricProfile η n a u ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have hmax : max (ENNReal.ofReal C)
        (ENNReal.ofReal (H ^ (-(a / 2))) * geometricProfile η n a u) ≠ ⊤ :=
      lt_top_iff_ne_top.1 (max_lt ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hprod))
    have hreal : (geometricProfile θ n a u).toReal ≤
        (β / 2) * (geometricProfile η n a u).toReal := by
      calc
        (geometricProfile θ n a u).toReal ≤
            (max (ENNReal.ofReal C)
              (ENNReal.ofReal (H ^ (-(a / 2))) * geometricProfile η n a u)).toReal :=
          ENNReal.toReal_mono hmax hboundu
        _ = max C (H ^ (-(a / 2)) * (geometricProfile η n a u).toReal) := by
          rw [ENNReal.toReal_max ENNReal.ofReal_ne_top hprod,
            ENNReal.toReal_ofReal hC.le, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hHpos _).le]
        _ ≤ (β / 2) * (geometricProfile η n a u).toReal :=
          max_le hcost (mul_le_mul_of_nonneg_right hHpow.le ENNReal.toReal_nonneg)
    exact ((div_le_iff₀ hden).2 hreal).trans_lt (by linarith)

end D5.S3.Analytic.SeriesInequalities.RatioPreservingFloorImprovement
