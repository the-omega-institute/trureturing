/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact-uniform convergence of original cutoffs and signed inverses. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteTrace
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! Analytic identities for the original signed Gaussian operator and its literal cutoffs. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff

open OriginalGaussianMatrix OriginalGaussianResolvent
open OriginalGaussianDeterminant OriginalGaussianFiniteTrace

private lemma traceTerm_uniform_bound {ρ : ℝ} (hρ : 0 ≤ ρ)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) (p : ℕ × ℕ) :
    ‖term z p‖ ≤ unit1Geo ρ p := by
  rw [term, norm_smul]
  calc
    _ ≤ ‖matrixEntry z (p.1 + 1) (p.2 + 1)‖ * 1 := by
      gcongr
      exact rankOne_norm_le _ _
    _ ≤ ‖z‖ ^ ((p.1 + 1) + (p.2 + 1)) := by
      simpa using entry_bound z (p.1 + 1) (p.2 + 1) (by omega) (by omega)
    _ ≤ ρ ^ ((p.1 + 1) + (p.2 + 1)) :=
      pow_le_pow_left₀ (norm_nonneg z) hz _
    _ = _ := by rw [pow_add]; rfl

/-- Uniform operator-norm convergence of the ACTUAL principal square cutoffs. -/
theorem sectionOp_tendstoUniformlyOn {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn sectionOp operator atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  have h := tendstoUniformlyOn_tsum (f := fun (p : ℕ × ℕ) (z : ℂ) => term z p)
    (s := {z : ℂ | ‖z‖ ≤ ρ}) (unit1Geo_summable hρ hρ1)
    (fun p z hz => traceTerm_uniform_bound hρ hz p)
  have hp := tendsto_finset_range.prodMk tendsto_finset_range
  rw [prod_atTop_atTop_eq] at hp
  have hc := tendsto_finsetProd_atTop.comp hp
  have hh : TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), term z p)
      (fun z => ∑' p : ℕ × ℕ, term z p) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    intro u hu
    exact hc.eventually (h u hu)
  change TendstoUniformlyOn
    (fun N z => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, term z (n, m))
    (fun z => ∑' p : ℕ × ℕ, term z p) atTop {z : ℂ | ‖z‖ ≤ ρ}
  simpa only [Finset.sum_product] using hh

def traceWeightedTerm (r : ℝ) (n : ℕ) : H :=
  lp.single 2 n ((n + 1 : ℂ) * sourceValue r n)

/-- Coordinate truncation on the same H, retaining the original source signs. -/
def weightedCutoff (N : ℕ) (r : ℝ) : H :=
  ∑ n ∈ Finset.range N, traceWeightedTerm r n

private lemma traceWeightedTerm_bound {r R : ℝ} (hrR : r ≤ R) (n : ℕ) :
    ‖traceWeightedTerm r n‖ ≤ traceWeightBound R n := by
  rw [traceWeightedTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact traceWeightValue_bound hrR n

private lemma traceWeightedTerm_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖traceWeightedTerm r n‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (traceWeightedTerm_bound le_rfl) (traceWeightBound_summable hr hr1)

lemma traceWeightedTerm_tsum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, traceWeightedTerm r n) = weightedSource r hr hr1 := by
  ext n
  change (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
    (∑' i : ℕ, traceWeightedTerm r i) = (n + 1 : ℂ) * sourceValue r n
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum
    (traceWeightedTerm_summable hr hr1).of_norm]
  rw [tsum_eq_single n]
  · change (lp.single 2 n ((n + 1 : ℂ) * sourceValue r n) : H) n = _
    simp [lp.single_apply]
  · intro i hi
    change (lp.single 2 i ((i + 1 : ℂ) * sourceValue r i) : H) n = 0
    simp [lp.single_apply, hi]

/-- Uniform l2 convergence, with the literal weightedSource as limit.
    A subtype keeps proof arguments explicit without inventing an exterior extension. -/
theorem weightedCutoff_tendstoUniformly {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    TendstoUniformly
      (fun N : ℕ => fun r : Set.Icc (0 : ℝ) R => weightedCutoff N r.val)
      (fun r : Set.Icc (0 : ℝ) R =>
        weightedSource r.val r.property.1 (r.property.2.trans_lt hR1)) atTop := by
  have h := tendstoUniformly_tsum_nat (traceWeightBound_summable hR hR1)
    (fun n (r : Set.Icc (0 : ℝ) R) => traceWeightedTerm_bound r.property.2 n)
  have he : (fun r : Set.Icc (0 : ℝ) R => ∑' n : ℕ, traceWeightedTerm r.val n) =
      (fun r : Set.Icc (0 : ℝ) R =>
        weightedSource r.val r.property.1 (r.property.2.trans_lt hR1)) := by
    funext r
    exact traceWeightedTerm_tsum r.property.1 (r.property.2.trans_lt hR1)
  simpa only [weightedCutoff, he] using h

/-- Uniform cutoff norm bound consumed by the scalar-moment passage. -/
theorem weightedCutoff_norm_le (N : ℕ) {r R : ℝ} (hrR : r ≤ R)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    ‖weightedCutoff N r‖ ≤ traceWeightMass R := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖traceWeightedTerm r n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, traceWeightBound R n :=
      Finset.sum_le_sum (fun n _ => traceWeightedTerm_bound hrR n)
    _ ≤ _ := (traceWeightBound_summable hR hR1).sum_le_tsum _
      (fun n _ => by dsimp [traceWeightBound]; positivity)

private def traceNeumann (T : H →L[ℂ] H) : H →L[ℂ] H := ∑' n : ℕ, T ^ n

lemma traceNeumann_norm_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {T : H →L[ℂ] H} (hT : ‖T‖ ≤ q) :
    ‖traceNeumann T‖ ≤ (1 - q)⁻¹ := by
  have hgeom := summable_geometric_of_lt_one hq hq1
  have hnorm : Summable (fun n : ℕ => ‖T ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => (norm_pow_le T n).trans
        (pow_le_pow_left₀ (norm_nonneg T) hT n)) hgeom
  calc
    _ ≤ ∑' n : ℕ, ‖T ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, q ^ n := hnorm.tsum_le_tsum
      (fun n => (norm_pow_le T n).trans
        (pow_le_pow_left₀ (norm_nonneg T) hT n)) hgeom
    _ = _ := tsum_geometric_of_lt_one hq hq1

private lemma traceNeumann_sub {X Y : H →L[ℂ] H}
    (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    traceNeumann X - traceNeumann Y =
      traceNeumann X * (X - Y) * traceNeumann Y := by
  have hx : traceNeumann X * (1 - X) = 1 :=
    (summable_geometric_of_norm_lt_one hX).tsum_pow_mul_one_sub
  have hy : (1 - Y) * traceNeumann Y = 1 :=
    (summable_geometric_of_norm_lt_one hY).one_sub_mul_tsum_pow
  symm
  calc
    _ = traceNeumann X * ((1 - Y) * traceNeumann Y) -
        (traceNeumann X * (1 - X)) * traceNeumann Y := by noncomm_ring
    _ = _ := by rw [hx, hy, mul_one, one_mul]

private lemma traceNeumann_sub_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {X Y : H →L[ℂ] H} (hX : ‖X‖ ≤ q) (hY : ‖Y‖ ≤ q) :
    ‖traceNeumann X - traceNeumann Y‖ ≤
      (1 - q)⁻¹ ^ 2 * ‖X - Y‖ := by
  rw [traceNeumann_sub (hX.trans_lt hq1) (hY.trans_lt hq1)]
  calc
    _ ≤ (‖traceNeumann X‖ * ‖X - Y‖) * ‖traceNeumann Y‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((1 - q)⁻¹ * ‖X - Y‖) * (1 - q)⁻¹ := by
      gcongr
      · exact traceNeumann_norm_le hq hq1 hX
      · exact traceNeumann_norm_le hq hq1 hY
    _ = _ := by ring

/-- The genuine signed finite Neumann inverse, embedded on H. -/
def sectionSignedResolvent (N : ℕ) (σ z : ℂ) : H →L[ℂ] H :=
  ∑' n : ℕ, (σ • sectionOp N z) ^ n

private lemma traceSigned_operator_bounds {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z σ : ℂ} (hz : ‖z‖ ≤ ρ) (hσ : ‖σ‖ = 1) (N : ℕ) :
    ‖σ • sectionOp N z‖ ≤ ρ ^ 2 ∧ ‖σ • operator z‖ ≤ ρ ^ 2 := by
  have hz1 : ‖z‖ < 1 := hz.trans_lt hρ1
  constructor
  · rw [norm_smul, hσ, one_mul]
    exact (sectionOp_norm_le N hz1).trans
      (pow_le_pow_left₀ (norm_nonneg z) hz 2)
  · rw [norm_smul, hσ, one_mul]
    exact (operator_norm_le hz1).trans
      (pow_le_pow_left₀ (norm_nonneg z) hz 2)

/-- Resolvent-identity estimate, uniform in N and z on a smaller disk.
    sigma=1 and sigma=-1 are respectively the genuine Rminus and Rplus. -/
theorem sectionSignedResolvent_error {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z σ : ℂ} (hz : ‖z‖ ≤ ρ) (hσ : ‖σ‖ = 1) (N : ℕ) :
    ‖sectionSignedResolvent N σ z - (∑' n : ℕ, (σ • operator z) ^ n)‖ ≤
      (1 - ρ ^ 2)⁻¹ ^ 2 * ‖sectionOp N z - operator z‖ := by
  have hq : ρ ^ 2 < 1 := pow_lt_one₀ hρ hρ1 (by norm_num : (2 : ℕ) ≠ 0)
  have hb := traceSigned_operator_bounds hρ hρ1 hz hσ N
  have h := traceNeumann_sub_bound (sq_nonneg ρ) hq hb.1 hb.2
  simpa only [traceNeumann, sectionSignedResolvent, ← smul_sub, norm_smul,
    hσ, one_mul] using h

private lemma trace_uniform_of_error {α E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {u : ℕ → α → E} {v : α → E} {f : ℕ → α → F} {g : α → F} {s : Set α}
    {C : ℝ} (hC : 0 ≤ C) (h : TendstoUniformlyOn u v atTop s)
    (hb : ∀ N x, x ∈ s → ‖f N x - g x‖ ≤ C * ‖u N x - v x‖) :
    TendstoUniformlyOn f g atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  have ht := (Metric.tendstoUniformlyOn_iff.mp h)
    (ε / (C + 1)) hδ
  filter_upwards [ht] with N hN x hx
  rw [dist_comm, dist_eq_norm]
  calc
    _ ≤ C * ‖u N x - v x‖ := hb N x hx
    _ < ε := by
      have he := hN x hx
      rw [dist_comm, dist_eq_norm] at he
      calc
        _ ≤ (C + 1) * ‖u N x - v x‖ := by
          nlinarith [norm_nonneg (u N x - v x)]
        _ < (C + 1) * (ε / (C + 1)) :=
          mul_lt_mul_of_pos_left he (by positivity)
        _ = ε := by field_simp [ne_of_gt (by positivity : 0 < C + 1)]

/-- Actual uniform convergence of both signed inverses, with all norm bounds paid. -/
theorem sectionSignedResolvent_tendstoUniformlyOn {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    TendstoUniformlyOn (fun N => sectionSignedResolvent N σ)
      (fun z => ∑' n : ℕ, (σ • operator z) ^ n)
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  exact trace_uniform_of_error (sq_nonneg _) (sectionOp_tendstoUniformlyOn hρ hρ1)
    (fun N z hz => sectionSignedResolvent_error hρ hρ1 hz hσ N)

private lemma trace_square_sub_bound {q : ℝ} (hq : 0 ≤ q)
    {X Y : H →L[ℂ] H} (hX : ‖X‖ ≤ q) (hY : ‖Y‖ ≤ q) :
    ‖X ^ 2 - Y ^ 2‖ ≤ 2 * q * ‖X - Y‖ := by
  have he : X ^ 2 - Y ^ 2 = X * (X - Y) + (X - Y) * Y := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖X * (X - Y)‖ + ‖(X - Y) * Y‖ := norm_add_le _ _
    _ ≤ ‖X‖ * ‖X - Y‖ + ‖X - Y‖ * ‖Y‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ q * ‖X - Y‖ + ‖X - Y‖ * q := by gcongr
    _ = _ := by ring

/-- Squaring is AFTER cutoff; this controls (1-(P_N A P_N)^2)^(-1).
    It never replaces this square by P_N A^2 P_N. -/
theorem sectionSquareResolvent_error {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ ρ) (N : ℕ) :
    ‖(∑' n : ℕ, (sectionOp N z ^ 2) ^ n) -
        (∑' n : ℕ, (operator z ^ 2) ^ n)‖ ≤
      ((1 - ρ ^ 4)⁻¹ ^ 2 * (2 * ρ ^ 2)) * ‖sectionOp N z - operator z‖ := by
  have hb := traceSigned_operator_bounds hρ hρ1 hz (by simp : ‖(1 : ℂ)‖ = 1) N
  simp only [one_smul] at hb
  have hq : ρ ^ 4 < 1 := pow_lt_one₀ hρ hρ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hx : ‖sectionOp N z ^ 2‖ ≤ ρ ^ 4 := by
    calc
      _ ≤ ‖sectionOp N z‖ ^ 2 := norm_pow_le _ _
      _ ≤ (ρ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb.1 2
      _ = _ := by ring
  have hy : ‖operator z ^ 2‖ ≤ ρ ^ 4 := by
    calc
      _ ≤ ‖operator z‖ ^ 2 := norm_pow_le _ _
      _ ≤ (ρ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb.2 2
      _ = _ := by ring
  exact (traceNeumann_sub_bound (by positivity) hq hx hy).trans
    (by
      have hs := trace_square_sub_bound (sq_nonneg ρ) hb.1 hb.2
      change (1 - ρ ^ 4)⁻¹ ^ 2 * ‖sectionOp N z ^ 2 - operator z ^ 2‖ ≤ _
      calc
        _ ≤ (1 - ρ ^ 4)⁻¹ ^ 2 * (2 * ρ ^ 2 * ‖sectionOp N z - operator z‖) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg _)
        _ = _ := by ring)

/-- Uniform convergence of the actual finite-square inverses, not just a norm bound. -/
theorem sectionSquareResolvent_tendstoUniformlyOn {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    TendstoUniformlyOn
      (fun N z => ∑' n : ℕ, (sectionOp N z ^ 2) ^ n)
      (fun z => ∑' n : ℕ, (operator z ^ 2) ^ n)
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  exact trace_uniform_of_error (by positivity) (sectionOp_tendstoUniformlyOn hρ hρ1)
    (fun N z hz => sectionSquareResolvent_error hρ hρ1 hz N)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianUniformCutoff
