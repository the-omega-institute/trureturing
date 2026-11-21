/- GID: D5/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinPrescribedMesh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unattainment gives both signed Robin limits on any power-saving mesh. -/

import D5.S3.Arith.Robin.PriceRecord.PolynomialCanonicalRecordCriterion
import D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
import D5.S3.Arith.Robin.PriceRecord.RobinMarginModulus
import D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap

/-! Two-sided oscillation of literal canonical Robin margins on prescribed integer meshes. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.PriceRecord.RobinPrescribedMesh

open Filter Set
open scoped Topology
open D5.S3.Arith.Robin.ActualTwoPriceDefect
  (clock integerAt price price_pos strictInteger strictInteger_pos strictInteger_counts)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa zero_real_parts_nonempty)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open ActualBalancedCutoff (firstLayerPrice)
open PolynomialCanonicalRecordCriterion
  (canonicalPriceCutoff canonical_price_cutoff_spec le_canonical_price_cutoff clock_power)
open PolynomialMeshBounds (mesh_atTop mesh_bracket_of_strictMono record_weight W_factor W_pos)
open CanonicalThresholdWindowTransfer (normalizedMargin)

private lemma prescribed_mesh_ratio {N : ℕ → ℕ} (hN : StrictMono N)
    {G eta : ℝ} (heta : 0 < eta)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * (N k : ℝ) ^ (1 - eta)) :
    Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1) := by
  have htop := mesh_atTop hN
  have hsmall : Tendsto (fun k => G * (N k : ℝ) ^ (-eta)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop heta).comp htop).const_mul G
  have hpos := htop.eventually_gt_atTop (0 : ℝ)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro r hr
    filter_upwards [hpos] with k hk
    have hmono : (N k : ℝ) ≤ N (k + 1) :=
      Nat.cast_le.mpr (hN.monotone (Nat.le_succ k))
    exact hr.trans_le ((one_le_div hk).mpr hmono)
  · intro r hr
    filter_upwards [hpos, hgap, hsmall.eventually_lt_const (sub_pos.mpr hr)] with k hk hg hs
    have hexp : (1 - eta) - 1 = -eta := by ring
    have hdiv :
        (N (k + 1) : ℝ) / (N k : ℝ) - 1 =
          ((N (k + 1) : ℝ) - (N k : ℝ)) / (N k : ℝ) := by
      rw [sub_div, div_self hk.ne']
    have hscaled : ((N (k + 1) : ℝ) - (N k : ℝ)) / (N k : ℝ) ≤
        G * (N k : ℝ) ^ (-eta) := by
      calc
        _ ≤ (G * (N k : ℝ) ^ (1 - eta)) / (N k : ℝ) :=
          div_le_div_of_nonneg_right hg hk.le
        _ = _ := by rw [mul_div_assoc, ← Real.rpow_sub_one hk.ne', hexp]
    linarith only [hdiv, hscaled, hs]

/-- The weighted increment of the literal canonical Robin margin is uniformly
bounded on each late closed cell. The endpoint square-root terms set the
effective gap exponent to `min eta (1 / 2)`. -/
private theorem canonical_robin_margin_normalized_cell_bound {N : ℕ → ℕ}
    (hN : StrictMono N) {G eta a epsilon : ℝ} (hG : 0 ≤ G)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * (N k : ℝ) ^ (1 - eta))
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1))
    (hepsilon : 0 < epsilon) (hbeta : 1 / 2 ≤ zeroAbscissa + epsilon) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, N k ≤ j → j ≤ N (k + 1) →
      |(N k : ℝ) ^ a * Real.log (N k : ℝ) *
        (robinLogMargin (strictInteger (firstLayerPrice ((j : ℝ) + 1))) -
          robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))))| ≤
        K * (N k : ℝ) ^ (a + (zeroAbscissa + epsilon) - 1 - min eta (1 / 2)) *
          Real.log (N k : ℝ) := by
  let beta : ℝ := zeroAbscissa + epsilon
  let eta' : ℝ := min eta (1 / 2)
  have hBetaNonneg : 0 ≤ beta := by
    change 0 ≤ zeroAbscissa + epsilon
    linarith only [hbeta]
  have hEtaHalf : eta' ≤ 1 / 2 := min_le_right _ _
  have hEtaExp : 0 ≤ 1 - eta' := by linarith only [hEtaHalf]
  obtain ⟨C, hC, hclock⟩ := clock_power epsilon hepsilon hbeta
  obtain ⟨T, hT, hgrowth⟩ :=
    EulerLayerInventoryGrowth.strict_inventory_uniform_growth (1 / 2) (by norm_num)
  obtain ⟨A, hA, hcell⟩ := RobinMarginModulus.canonical_robin_margin_cell_bound
  let C' : ℝ := C * (4 : ℝ) ^ beta
  have hC' : 0 ≤ C' := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  let E : ℝ := 2 * (G + 2) + 4 * A
  let K : ℝ := 16 * (C' + 2) * E
  have hK : 0 < K := by
    dsimp only [K, E]
    exact mul_pos (mul_pos (by norm_num) (by linarith only [hC']))
      (by linarith only [hG, hA])
  refine ⟨K, hK, ?_⟩
  filter_upwards [(mesh_atTop hN).eventually_ge_atTop (max T 12), hgap,
    hratio.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with k hk hkGap hkRatio
  intro j hjlo hjhi
  let X : ℝ := (N k : ℝ)
  have hX12 : 12 ≤ X := (le_max_right T 12).trans hk
  have hX0 : 0 < X := by linarith only [hX12]
  have hX1 : 1 ≤ X := by linarith only [hX12]
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith only [hX12])
  have hlogXone : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr
      (Real.exp_one_lt_three.le.trans (by linarith only [hX12]))
  have hnext : (N (k + 1) : ℝ) ≤ 2 * X := ((div_lt_iff₀ hX0).mp hkRatio).le
  have hk12 : 12 ≤ N k := by
    change (12 : ℝ) ≤ (N k : ℝ) at hX12
    exact_mod_cast hX12
  have hcut (m : ℕ) (hm : N k ≤ m) :
      (m : ℝ) + 1 ≤ canonicalPriceCutoff m ∧
        canonicalPriceCutoff m ≤ (m : ℝ) + 1 + 1 / 2 ∧
        price (canonicalPriceCutoff m) = firstLayerPrice ((m : ℝ) + 1) := by
    obtain ⟨hlo, hhi, hprice⟩ := canonical_price_cutoff_spec (hk12.trans hm)
    exact ⟨hlo.le, hhi.le, hprice⟩
  have hgeom (m : ℕ) (hmlo : N k ≤ m) (hmhi : m ≤ N (k + 1)) :
      X ≤ canonicalPriceCutoff m ∧ canonicalPriceCutoff m ≤ 4 * X := by
    have hlo : X ≤ (m : ℝ) := Nat.cast_le.mpr hmlo
    have hhi : (m : ℝ) ≤ N (k + 1) := Nat.cast_le.mpr hmhi
    exact ⟨hlo.trans (le_canonical_price_cutoff m),
      by linarith only [(hcut m hmlo).2.1, hhi, hnext, hX12]⟩
  have hclockGeom (m : ℕ) (hmlo : N k ≤ m) (hmhi : m ≤ j) :
      X ≤ canonicalPriceCutoff m ∧ X / 2 ≤ clock (canonicalPriceCutoff m) ∧
        |clock (canonicalPriceCutoff m) - canonicalPriceCutoff m| ≤ C' * X ^ beta := by
    obtain ⟨hmX, hm4X⟩ := hgeom m hmlo (hmhi.trans hjhi)
    have hmT := ((le_max_left T 12).trans hk).trans hmX
    have hm1 := hT.trans_le hmT
    have hq := price_pos hm1
    have hU : 0 < integerAt (canonicalPriceCutoff m) := strictInteger_pos hq
    have hnear : |clock (canonicalPriceCutoff m) / canonicalPriceCutoff m - 1| < 1 / 2 :=
      hgrowth _ hmT _ hU (fun p _ => strictInteger_counts hq p)
    have hhalf : (1 / 2 : ℝ) < clock (canonicalPriceCutoff m) / canonicalPriceCutoff m := by
      linarith only [(abs_lt.mp hnear).1]
    have hmclock := (lt_div_iff₀ (hX0.trans_le hmX)).mp hhalf
    have hmPow : canonicalPriceCutoff m ^ beta ≤ (4 : ℝ) ^ beta * X ^ beta :=
      (Real.rpow_le_rpow (hX0.le.trans hmX) hm4X hBetaNonneg).trans_eq
        (Real.mul_rpow (by norm_num) hX0.le)
    refine ⟨hmX, by linarith only [hmX, hmclock], ?_⟩
    rw [abs_sub_comm]
    calc
      _ ≤ C * canonicalPriceCutoff m ^ beta :=
        hclock _ (by linarith only [hX12, hmX])
      _ ≤ C * ((4 : ℝ) ^ beta * X ^ beta) := mul_le_mul_of_nonneg_left hmPow hC
      _ = _ := by dsimp only [C']; rw [mul_assoc]
  have hraw := hcell (t := canonicalPriceCutoff) (X := X) (C := C') (β := beta)
    hjlo (by linarith only [hX12]) hC' hBetaNonneg (fun m hm _ => hcut m hm) hclockGeom
  obtain ⟨hiX, hi4X⟩ := hgeom (N k) le_rfl (hjlo.trans hjhi)
  obtain ⟨hjX, hj4X⟩ := hgeom j hjlo hjhi
  have hjCast : (j : ℝ) ≤ N (k + 1) := Nat.cast_le.mpr hjhi
  have hpower : 1 ≤ X ^ (1 - eta') := Real.one_le_rpow hX1 hEtaExp
  have hgap' : (N (k + 1) : ℝ) - X ≤ G * X ^ (1 - eta') :=
    hkGap.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (sub_le_sub_left (min_le_left eta (1 / 2)) 1)) hG)
  have hlength : canonicalPriceCutoff j - canonicalPriceCutoff (N k) + 1 ≤
      (G + 2) * X ^ (1 - eta') := by
    have htwo := mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [(hcut j hjlo).2.1, (hcut (N k) le_rfl).1, hjCast, hgap', htwo,
      add_mul G 2 (X ^ (1 - eta'))]
  have hjlog : Real.log (canonicalPriceCutoff j) ≤ 2 * Real.log X := by
    have h4X : 4 * X ≤ X * X :=
      mul_le_mul_of_nonneg_right (by linarith only [hX12]) hX0.le
    calc
      _ ≤ Real.log (X * X) := Real.log_le_log (hX0.trans_le hjX) (hj4X.trans h4X)
      _ = _ := by rw [Real.log_mul hX0.ne' hX0.ne']; ring
  have hroot4 : Real.sqrt (4 * X) = 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hrootPow : Real.sqrt X ≤ X ^ (1 - eta') := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hEtaHalf])
  have hroot : Real.sqrt (canonicalPriceCutoff (N k)) + Real.sqrt (canonicalPriceCutoff j) ≤
      4 * X ^ (1 - eta') := by
    linarith only [Real.sqrt_le_sqrt hi4X, Real.sqrt_le_sqrt hj4X, hroot4, hrootPow]
  have hlinear : (canonicalPriceCutoff j - canonicalPriceCutoff (N k) + 1) *
      Real.log (canonicalPriceCutoff j) ≤ 2 * (G + 2) * X ^ (1 - eta') * Real.log X := by
    calc
      _ ≤ ((G + 2) * X ^ (1 - eta')) * (2 * Real.log X) :=
        mul_le_mul hlength hjlog (Real.log_nonneg (hX1.trans hjX))
          (mul_nonneg (by linarith only [hG]) (Real.rpow_nonneg hX0.le _))
      _ = _ := by ring
  have hrootTerm : A * (Real.sqrt (canonicalPriceCutoff (N k)) +
      Real.sqrt (canonicalPriceCutoff j)) ≤ 4 * A * X ^ (1 - eta') * Real.log X := by
    calc
      _ ≤ A * (4 * X ^ (1 - eta')) := mul_le_mul_of_nonneg_left hroot hA.le
      _ ≤ (A * (4 * X ^ (1 - eta'))) * Real.log X :=
        le_mul_of_one_le_right
          (mul_nonneg hA.le (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le _))) hlogXone
      _ = _ := by ring
  have hbracket : (canonicalPriceCutoff j - canonicalPriceCutoff (N k) + 1) *
      Real.log (canonicalPriceCutoff j) +
        A * (Real.sqrt (canonicalPriceCutoff (N k)) + Real.sqrt (canonicalPriceCutoff j)) ≤
      E * X ^ (1 - eta') * Real.log X := by
    calc
      _ ≤ 2 * (G + 2) * X ^ (1 - eta') * Real.log X +
          4 * A * X ^ (1 - eta') * Real.log X := add_le_add hlinear hrootTerm
      _ = _ := by dsimp only [E]; ring
  have hcoef : 0 ≤ 16 * (C' + 2) * X ^ (beta - 2) / Real.log X :=
    div_nonneg (mul_nonneg (by linarith only [hC']) (Real.rpow_nonneg hX0.le _)) hlogX.le
  have hweight : 0 ≤ X ^ a * Real.log X := mul_nonneg (Real.rpow_nonneg hX0.le _) hlogX.le
  rw [abs_mul, abs_of_nonneg hweight]
  refine (mul_le_mul_of_nonneg_left
    (hraw.trans (mul_le_mul_of_nonneg_left hbracket hcoef)) hweight).trans_eq ?_
  change X ^ a * Real.log X *
    ((16 * (C' + 2) * X ^ (beta - 2) / Real.log X) *
      (E * X ^ (1 - eta') * Real.log X)) =
    K * X ^ (a + beta - 1 - eta') * Real.log X
  have hpow : (X ^ a * X ^ (beta - 2)) * X ^ (1 - eta') = X ^ (a + beta - 1 - eta') := by
    rw [← Real.rpow_add hX0 a (beta - 2),
      ← Real.rpow_add hX0 (a + (beta - 2)) (1 - eta'),
      show a + (beta - 2) + (1 - eta') = a + beta - 1 - eta' by ring]
  rw [← hpow]
  dsimp only [K]
  field_simp [hlogX.ne']

/-- Choose a lighter normalization and an actual zero. The cell increment
has power exponent strictly below the zero's exponent, with room for the
logarithm and the lighter normalization. -/
theorem exists_canonical_robin_margin_cell_bound_below_zero {N : ℕ → ℕ}
    (hN : StrictMono N) {G eta alpha : ℝ} (hG : 0 ≤ G) (heta : 0 < eta)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * (N k : ℝ) ^ (1 - eta))
    (halpha : 1 - zeroAbscissa < alpha) (halphaHalf : alpha ≤ 1 / 2) :
    ∃ (a epsilon K : ℝ) (rho : ℂ), 0 < a ∧ a < alpha ∧ 0 < epsilon ∧ 0 < K ∧
      IsNontrivialZero rho ∧ zeroAbscissa + epsilon - min eta (1 / 2) < 1 - a ∧
      1 - a < rho.re ∧
      ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, N k ≤ j → j ≤ N (k + 1) →
        |(N k : ℝ) ^ a * Real.log (N k : ℝ) *
          (robinLogMargin (strictInteger (firstLayerPrice ((j : ℝ) + 1))) -
            robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))))| ≤
          K * (N k : ℝ) ^ (a + (zeroAbscissa + epsilon) - 1 - min eta (1 / 2)) *
            Real.log (N k : ℝ) := by
  let eta' : ℝ := min eta (1 / 2)
  have hEta' : 0 < eta' := lt_min heta (by norm_num)
  have hThetaHalf : 1 / 2 < zeroAbscissa := by linarith only [halpha, halphaHalf]
  have hThetaOne : zeroAbscissa ≤ 1 := by
    change sSup (Complex.re '' {z : ℂ | IsNontrivialZero z}) ≤ 1
    apply csSup_le zero_real_parts_nonempty
    rintro x ⟨z, hz, rfl⟩
    exact hz.2.2.le
  let delta : ℝ := min (alpha - (1 - zeroAbscissa)) eta' / 4
  have hdelta : 0 < delta := div_pos (lt_min (sub_pos.mpr halpha) hEta') (by norm_num)
  have hdeltaAlpha : 4 * delta ≤ alpha - (1 - zeroAbscissa) := by
    dsimp only [delta]
    linarith only [min_le_left (alpha - (1 - zeroAbscissa)) eta']
  have hdeltaGap : 4 * delta ≤ eta' := by
    dsimp only [delta]
    linarith only [min_le_right (alpha - (1 - zeroAbscissa)) eta']
  let a : ℝ := 1 - zeroAbscissa + delta
  let beta : ℝ := zeroAbscissa + delta
  have haPos : 0 < a := by dsimp only [a]; linarith only [hThetaOne, hdelta]
  have haTheta : 1 - zeroAbscissa < a := by dsimp only [a]; linarith only [hdelta]
  have haAlpha : a < alpha := by dsimp only [a]; linarith only [hdeltaAlpha, hdelta]
  have hbeta : 1 / 2 ≤ beta := by dsimp only [beta]; linarith only [hThetaHalf, hdelta]
  have hrate : beta - eta' < 1 - a := by
    dsimp only [a, beta]
    linarith only [hdeltaGap, hdelta]
  have hrho : ∃ rho : ℂ, IsNontrivialZero rho ∧ 1 - a < rho.re := by
    have hr : 1 - a < sSup (Complex.re '' {z : ℂ | IsNontrivialZero z}) := by
      change 1 - a < zeroAbscissa
      linarith only [haTheta]
    obtain ⟨_, ⟨rho, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup zero_real_parts_nonempty hr
    exact ⟨rho, hz, hlt⟩
  obtain ⟨rho, hz, hlt⟩ := hrho
  obtain ⟨K, hK, hbound⟩ := canonical_robin_margin_normalized_cell_bound (a := a) hN hG hgap
    (prescribed_mesh_ratio hN heta hgap) hdelta hbeta
  exact ⟨a, delta, K, rho, haPos, haAlpha, hdelta, hK, hz, hrate, hlt, hbound⟩

/-- Below the mesh's first point, only the upper endpoint is needed. On the
mesh's tail, the least crossing supplies the cell and lies after every
index whose mesh point is at most `n`. -/
private theorem exists_mesh_cell {M : ℕ → ℕ} (hM : StrictMono M) (n : ℕ) :
    ∃ k : ℕ, (∀ K : ℕ, M K ≤ n → K ≤ k) ∧
      (M 0 ≤ n → M k ≤ n) ∧ n < M (k + 1) := by
  have index_le {k K : ℕ} (hupper : n < M (k + 1)) (hK : M K ≤ n) : K ≤ k := by
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge ((hM.monotone (Nat.succ_le_of_lt hlt)).trans hK)) hupper
  by_cases hzero : M 0 ≤ n
  · have hcast : StrictMono (fun i : ℕ => (M i : ℝ)) :=
      fun _ _ h => Nat.cast_lt.mpr (hM h)
    obtain ⟨k, _, hlo, hhi⟩ :=
      mesh_bracket_of_strictMono hcast (mesh_atTop hM) 0 (Nat.cast_le.mpr hzero)
    have hupper : n < M (k + 1) := Nat.cast_lt.mp hhi
    exact ⟨k, fun _ => index_le hupper, fun _ => Nat.cast_le.mp hlo, hupper⟩
  · have hupper : n < M (0 + 1) :=
      (lt_of_not_ge hzero).trans_le (hM.monotone (Nat.zero_le _))
    exact ⟨0, fun _ => index_le hupper, id, hupper⟩

private theorem exists_mesh_subseq_atTop {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) {G : ℕ → ℝ}
    {M W : ℕ → ℕ} (hM : StrictMono M) (hW : StrictMono W)
    (hratio : Tendsto (fun k => (M (k + 1) : ℝ) / (M k : ℝ)) atTop (𝓝 1))
    (herror : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, M k ≤ n → n < M (k + 1) →
      |(M k : ℝ) ^ a * Real.log (M k : ℝ) * (G n - G (M k))| ≤ 1)
    (hlimit : Tendsto (fun j => normalizedMargin a G (W j)) atTop atTop) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      Tendsto (fun j => normalizedMargin a G (M (q j))) atTop atTop := by
  let cell (n : ℕ) : ℕ := Classical.choose (exists_mesh_cell hM n)
  have hcell (n : ℕ) : (∀ K : ℕ, M K ≤ n → K ≤ cell n) ∧
      (M 0 ≤ n → M (cell n) ≤ n) ∧ n < M (cell n + 1) :=
    Classical.choose_spec (exists_mesh_cell hM n)
  have hcellTop : Tendsto (fun j => cell (W j)) atTop atTop := by
    refine tendsto_atTop.mpr fun K => ?_
    filter_upwards [hW.tendsto_atTop.eventually_ge_atTop (M K)] with j hj
    exact (hcell (W j)).1 K hj
  have hMRealTop := mesh_atTop hM
  have hgeometry : ∀ᶠ k : ℕ in atTop,
      2 ≤ (M k : ℝ) ∧ (M (k + 1) : ℝ) ≤ 2 * (M k : ℝ) := by
    filter_upwards [hMRealTop.eventually_ge_atTop 2,
      hratio.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with k hk hr
    have hk0 : (0 : ℝ) < (M k : ℝ) := (by norm_num : (0 : ℝ) < 2).trans_le hk
    exact ⟨hk, ((div_lt_iff₀ hk0).mp hr).le⟩
  let w (n : ℕ) : ℝ := (n : ℝ) ^ a * Real.log (n : ℝ)
  have hFour : (0 : ℝ) < 4 := by norm_num
  have htransfer : Tendsto (fun j => normalizedMargin a G (M (cell (W j)))) atTop atTop := by
    refine tendsto_atTop.mpr fun L => ?_
    let B : ℝ := max L 0 + 2
    have hB : 0 < B := by
      dsimp only [B]
      linarith only [le_max_right L (0 : ℝ)]
    filter_upwards [hcellTop.eventually hgeometry, hcellTop.eventually herror,
      hW.tendsto_atTop.eventually_ge_atTop (M 0), hlimit.eventually_ge_atTop (4 * B)]
      with j hjGeometry hjError hjW hjLarge
    let k := cell (W j)
    have hnlo : M k ≤ W j := (hcell (W j)).2.1 hjW
    have hnhi : W j < M (k + 1) := (hcell (W j)).2.2
    have hnhiCast : (W j : ℝ) < (M (k + 1) : ℝ) := Nat.cast_lt.mpr hnhi
    have hnhiReal : (W j : ℝ) ≤ 2 * (M k : ℝ) := hnhiCast.le.trans hjGeometry.2
    have hnOne : (1 : ℝ) < (W j : ℝ) :=
      (by norm_num : (1 : ℝ) < 2).trans_le (hjGeometry.1.trans (Nat.cast_le.mpr hnlo))
    have hweight : w (W j) ≤ 4 * w (M k) :=
      record_weight ha haOne hnOne hjGeometry.1 hnhiReal
    change 4 * B ≤ w (W j) * G (W j) at hjLarge
    have hG : 0 < G (W j) :=
      pos_of_mul_pos_right ((mul_pos hFour hB).trans_le hjLarge) (W_pos a hnOne).le
    have hscaled : B ≤ w (M k) * G (W j) := by
      refine le_of_mul_le_mul_left ?_ hFour
      calc
        4 * B ≤ w (W j) * G (W j) := hjLarge
        _ ≤ (4 * w (M k)) * G (W j) := mul_le_mul_of_nonneg_right hweight hG.le
        _ = 4 * (w (M k) * G (W j)) := mul_assoc _ _ _
    have habs : |w (M k) * (G (W j) - G (M k))| ≤ 1 := hjError (W j) hnlo hnhi
    have herr : w (M k) * G (W j) - w (M k) * G (M k) ≤ 1 := by
      rw [← mul_sub]
      exact (abs_le.mp habs).2
    change L ≤ w (M k) * G (M k)
    dsimp only [B] at hscaled
    linarith only [le_max_left L (0 : ℝ), hscaled, herr]
  obtain ⟨φ, hφ, hmono⟩ := strictMono_subseq_of_tendsto_atTop hcellTop
  exact ⟨fun j => cell (W (φ j)), hmono, htransfer.comp hφ.tendsto_atTop⟩

/-- A uniform normalized error of at most one on late cells preserves both
signed limits along increasing subsequences of the prescribed mesh. For the
literal Robin margin, use `robinLogMargin (strictInteger (firstLayerPrice
((N : ℝ) + 1)))` as `G N`. The witness sequences come from
`RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes`. -/
private theorem exists_two_signed_mesh_subseqs {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (G : ℕ → ℝ)
    (M W_pos W_neg : ℕ → ℕ) (hM : StrictMono M)
    (hW_pos : StrictMono W_pos) (hW_neg : StrictMono W_neg)
    (hratio : Tendsto (fun k => (M (k + 1) : ℝ) / (M k : ℝ)) atTop (𝓝 1))
    (herror : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, M k ≤ n → n < M (k + 1) →
      |(M k : ℝ) ^ a * Real.log (M k : ℝ) * (G n - G (M k))| ≤ 1)
    (hpos : Tendsto (fun j => normalizedMargin a G (W_pos j)) atTop atTop)
    (hneg : Tendsto (fun j => normalizedMargin a G (W_neg j)) atTop atBot) :
    ∃ q_pos q_neg : ℕ → ℕ, StrictMono q_pos ∧ StrictMono q_neg ∧
      Tendsto (fun j => normalizedMargin a G (M (q_pos j))) atTop atTop ∧
      Tendsto (fun j => normalizedMargin a G (M (q_neg j))) atTop atBot := by
  obtain ⟨q_pos, hq_pos, hposMesh⟩ :=
    exists_mesh_subseq_atTop ha haOne hM hW_pos hratio herror hpos
  have herrorNeg : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, M k ≤ n → n < M (k + 1) →
      |(M k : ℝ) ^ a * Real.log (M k : ℝ) * (-G n - (-G (M k)))| ≤ 1 := by
    filter_upwards [herror] with k hk
    intro n hlo hhi
    have hdiff : -G n - (-G (M k)) = -(G n - G (M k)) := by ring
    rw [hdiff, mul_neg, abs_neg]
    exact hk n hlo hhi
  have hnegTop : Tendsto (fun j => normalizedMargin a (fun n => -G n) (W_neg j)) atTop atTop := by
    simpa only [Function.comp_def, normalizedMargin, mul_neg] using
      tendsto_neg_atBot_atTop.comp hneg
  obtain ⟨q_neg, hq_neg, hnegMesh⟩ :=
    exists_mesh_subseq_atTop ha haOne hM hW_neg hratio herrorNeg hnegTop
  refine ⟨q_pos, q_neg, hq_pos, hq_neg, hposMesh, ?_⟩
  simpa only [Function.comp_def, normalizedMargin, mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp hnegMesh

private abbrev canonicalMargin (n : ℕ) : ℝ :=
  robinLogMargin (strictInteger (firstLayerPrice ((n : ℝ) + 1)))

/-- If the supremum of the real parts of the nontrivial zeta zeros is unattained,
every prescribed increasing natural mesh with a power-saving gap has increasing
index subsequences on which the literal normalized margins tend to opposite infinities. -/
theorem actual_canonical_two_signed_subsequences_of_power_saving_gaps {N : ℕ → ℕ}
    (hN : StrictMono N) {G eta alpha : ℝ} (hG : 0 ≤ G) (heta : 0 < eta)
    (hgap : ∀ᶠ k : ℕ in atTop,
      (N (k + 1) : ℝ) - (N k : ℝ) ≤ G * (N k : ℝ) ^ (1 - eta))
    (halpha : 1 - zeroAbscissa < alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hun : ∀ z : ℂ, IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ qpos qneg : ℕ → ℕ, StrictMono qpos ∧ StrictMono qneg ∧
      Tendsto (fun k => (N (qpos k) : ℝ) ^ alpha * Real.log (N (qpos k) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (qpos k) : ℝ) + 1)))) atTop atTop ∧
      Tendsto (fun k => (N (qneg k) : ℝ) ^ alpha * Real.log (N (qneg k) : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N (qneg k) : ℝ) + 1)))) atTop atBot := by
  obtain ⟨a, epsilon, K, rho, ha, haAlpha, _, _, hz, hrate, hlt, hbound⟩ :=
    exists_canonical_robin_margin_cell_bound_below_zero hN hG heta hgap halpha halphaHalf
  have haTheta : 1 - zeroAbscissa < a := by
    linarith only [hlt, D5.S3.Arith.Robin.ForwardKernel.KappaGap.zero_re_le_abscissa hz]
  obtain ⟨Wpos, Wneg, hWpos, hWneg, _, _, hpos, hneg⟩ :=
    RobinVanishingRelativeGap.actual_canonical_two_signed_ratio_one_meshes
      haTheta (haAlpha.trans_le halphaHalf) hun
  have hcell : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, N k ≤ n → n < N (k + 1) →
      |(N k : ℝ) ^ a * Real.log (N k : ℝ) *
        (canonicalMargin n - canonicalMargin (N k))| ≤ 1 := by
    let b : ℝ := 1 - a - (zeroAbscissa + epsilon - min eta (1 / 2))
    have hb : 0 < b := sub_pos.mpr hrate
    have hdecay : Tendsto (fun x : ℝ => K * (Real.log x / x ^ b)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero.const_mul K
    have hX := mesh_atTop hN
    filter_upwards [hbound, (hdecay.comp hX).eventually_lt_const zero_lt_one,
      hX.eventually_gt_atTop (0 : ℝ)] with k hk hsmall hposX n hlo hhi
    have hnegExp : a + (zeroAbscissa + epsilon) - 1 - min eta (1 / 2) = -b := by
      dsimp only [b]
      ring
    have hform : K * ((N k : ℝ) ^ b)⁻¹ * Real.log (N k : ℝ) =
        K * (Real.log (N k : ℝ) / (N k : ℝ) ^ b) := by
      rw [div_eq_mul_inv]
      ring
    have hn := hk n hlo hhi.le
    rw [hnegExp, Real.rpow_neg hposX.le, hform] at hn
    exact hn.trans hsmall.le
  obtain ⟨qpos, qneg, hqpos, hqneg, hposMesh, hnegMesh⟩ :=
    exists_two_signed_mesh_subseqs ha.le (haAlpha.le.trans (halphaHalf.trans (by norm_num)))
      canonicalMargin N Wpos Wneg hN hWpos hWneg (prescribed_mesh_ratio hN heta hgap) hcell hpos hneg
  have hexp : 0 < alpha - a := sub_pos.mpr haAlpha
  have hscale {q : ℕ → ℕ} (hq : StrictMono q) :
      Tendsto (fun k => (N (q k) : ℝ) ^ (alpha - a)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp (mesh_atTop (hN.comp hq))
  have hweight {q : ℕ → ℕ} (hq : StrictMono q) :
      (fun k => (N (q k) : ℝ) ^ (alpha - a) * normalizedMargin a canonicalMargin (N (q k)))
        =ᶠ[atTop] (fun k => normalizedMargin alpha canonicalMargin (N (q k))) := by
    filter_upwards [(mesh_atTop (hN.comp hq)).eventually_gt_atTop (0 : ℝ)] with k hk
    change 0 < (N (q k) : ℝ) at hk
    unfold normalizedMargin
    simpa only [Real.rpow_eq_pow, mul_assoc] using
      congrArg (fun w : ℝ => w * canonicalMargin (N (q k))) (W_factor alpha a hk).symm
  exact ⟨qpos, qneg, hqpos, hqneg,
    ((hscale hqpos).atTop_mul_atTop₀ hposMesh).congr' (hweight hqpos),
    ((hscale hqneg).atTop_mul_atBot₀ hnegMesh).congr' (hweight hqneg)⟩

#print axioms exists_canonical_robin_margin_cell_bound_below_zero
#print axioms actual_canonical_two_signed_subsequences_of_power_saving_gaps

end D5.S3.Arith.Robin.PriceRecord.RobinPrescribedMesh
