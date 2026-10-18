/- GID: D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/QuditPartialEstimationTradeoff
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every qudit partial-estimation frontier is attained and bounds all seeds. -/
/-
admission_basis: open-problem-resolution (#16777; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17100
Seeds on larger carriers use IsometricCompression.compress directly.
The PSD-seed model takes the source covariance reduction as input.
Occupation carriers and binomial dimensions are written as their original expressions.
The generic block positivity and real-root facts are shared with their earlier owners.
Direct frozen dependencies (declaration statement_id, not module pins):
F1: D5/S3/Quantum/Entanglement/OccupancyWordSectors.Word; statement_id=sha256:ca13ed0bb809eb9e0bcec28de917d6e1af84494bf87b4d48233eeb00ad8f61f7
F2: D5/S3/Quantum/Entanglement/OccupancyWordSectors.congr_simp; statement_id=sha256:fde6b05c0193a0ab22b642b2c553977e0270aaae7ff7a76712ab5b54f29e057d
F3: D5/S3/Quantum/Entanglement/OccupancyWordSectors.multiplicity; statement_id=sha256:7c95391e2ce98772f6771433c83507214f8702b7375e87a301f597e0d6fd7c38
F4: D5/S3/Quantum/Entanglement/OccupancyWordSectors.occupation; statement_id=sha256:7a25f213e509fae5658b7cd5566e2226a6cc4a14df4b9b97298939adea75b3ed
F5: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sectorVector; statement_id=sha256:c4dab226f71c3ad5ed5c4eb62405a22f1872b1682872934b1e1e2e37e8b62a8e
F6: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sectorWords; statement_id=sha256:7f5b56ebac6db0a78ce4980b924ba8756a829b7fa55f021a4fec28a1b7666a81
F7: D5/S3/Quantum/Entanglement/OccupancyWordSectors.sector_gram; statement_id=sha256:2a5b5263698f977e9ae50a4d420406bbe1e6d5d9d15826bc51217f0752d5ed99
F8: D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sector_head; statement_id=sha256:ae76e3812486d02dae11ae68fdacc58f4ca9ebbae9a4b6ddcf7339046797e7b6
F9: D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.coordinateMatrix; statement_id=sha256:e85e69e792099ffe8c0d08f7d1375c64a4254b4383eb49769f43139c90952c84
F10: D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.coordinate_gram; statement_id=sha256:857c2de8c9657c1da63ee97e99376c777f091f0396c8db669d70e72d94eff0a7
F11: D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight; statement_id=sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
F12: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef; statement_id=sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6
F13: D5/S3/Quantum/Reduction/IsometricCompression.compress; statement_id=sha256:ece129ea3121d41eb72b96831bf50f675e9fccf3bae2b5d39dc556c28adb9beb
F14: D5/S3/Quantum/BlockNorm/EssentiallyHermitian.outer_pairing_trace; statement_id=sha256:2f6ff99658f9bfd4b0133be5a045e802d88859875afca10c58b08804f5b66196
escape_witness: none
proof_shape: support: bind-only; consumer: Scores.seed_support_bound, result, support_scaled; escape_witness: none; Direct frozen dependencies: none. | proof_shape: support_scaled: bind-only; consumer: Scores.seed_support_bound, result; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Curve.seedF: bind-only; consumer: Attainment.frontierSeed_scores, Conjugate.curve_seed_parameters, Curve.seed_curve_identity, ScalarAssembly.scalar_frontier, result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Curve.seedG: bind-only; consumer: Attainment.frontierSeed_scores, Conjugate.curve_seed_parameters, Curve.seed_curve_identity, ScalarAssembly.scalar_frontier, result; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Curve.seed_curve_identity: bind-only; consumer: Conjugate.curve_seed_parameters; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Curve.slopeDenominator: bind-only; consumer: Conjugate.slope_top_eigenvalue, Curve.slopeDenominator_minus_r, Curve.slope_parameter_range, ScalarAssembly.scalar_frontier, ScalarAssembly.slope_quadratic_identity; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Curve.slopeDenominator_minus_r: bind-only; consumer: Curve.slope_parameter_range; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Curve.slope_parameter_range: bind-only; consumer: Conjugate.slope_top_eigenvalue, ScalarAssembly.scalar_frontier; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Conjugate.topRoot_eq_of_certificate: bind-only; consumer: Conjugate.slope_top_eigenvalue; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Conjugate.slope_top_eigenvalue: bind-only; consumer: ScalarAssembly.scalar_frontier; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Conjugate.curve_seed_parameters: bind-only; consumer: ScalarAssembly.scalar_frontier, result; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Endpoint.topRoot_gap_upper: bind-only; consumer: Endpoint.endpoint_from_support_family; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Endpoint.endpoint_from_support_family: bind-only; consumer: ScalarAssembly.scalar_frontier; escape_witness: none; Direct frozen dependencies: none. | proof_shape: ScalarAssembly.slope_quadratic_identity: bind-only; consumer: ScalarAssembly.scalar_frontier; escape_witness: none; Direct frozen dependencies: none. | proof_shape: ScalarAssembly.scalar_frontier: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Seed.rankOneSeed: bind-only; consumer: Attainment.frontierSeed, Attainment.frontierSeed_scaled_scores, Attainment.frontierSeed_trace, Inclusion.includedSeed_psd, Inclusion.includedSeed_score, Inclusion.includedSeed_trace, Seed.rankOneSeed_score, Seed.rankOneSeed_trace; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Seed.rankOneSeed_psd: bind-only; consumer: Inclusion.includedSeed_psd; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Seed.rankOneSeed_trace: bind-only; consumer: Inclusion.includedSeed_trace; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Seed.rankOneSeed_score: bind-only; consumer: Inclusion.includedSeed_score; escape_witness: none; Direct frozen dependencies: F14. | proof_shape: Inclusion.inclusion_compression: bind-only; consumer: Inclusion.includedSeed_score; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Inclusion.inclusion_gram: bind-only; consumer: Inclusion.includedSeed_trace; escape_witness: none; Direct frozen dependencies: F9, F10.
proof_shape: Inclusion.includedSeed_psd: bind-only; consumer: Attainment.frontierSeed_psd; escape_witness: none; Direct frozen dependencies: F13. | proof_shape: Inclusion.includedSeed_trace: bind-only; consumer: Attainment.frontierSeed_trace; escape_witness: none; Direct frozen dependencies: F9, F10, F13. | proof_shape: Inclusion.includedSeed_score: bind-only; consumer: Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: F14, F13.
proof_shape: Scores.score_A_scale: bind-only; consumer: Attainment.frontierSeed_scores, Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: F5. | proof_shape: Scores.score_C_scale: bind-only; consumer: Attainment.frontierSeed_scores, Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: F5, F11. | proof_shape: Trace.trace_upper_bound: bind-only; consumer: Trace.weighted_trace_upper_bound; escape_witness: none; Direct frozen dependencies: F12.
proof_shape: Trace.weighted_trace_upper_bound: bind-only; consumer: Scores.seed_support_bound; escape_witness: none; Direct frozen dependencies: F12. | proof_shape: Scores.seed_support_bound: content; consumer: result; escape_witness: D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.GlobalBound.global_operator_bound; Direct frozen dependencies: F1, F3, F4, F5, F2, F6, F7, F8, F11, F12. | proof_shape: Attainment.distinguishedOcc: bind-only; consumer: Attainment.distinguished_overlap, Attainment.frontierSeed, Attainment.frontierSeed_psd, Attainment.frontierSeed_scaled_scores, Attainment.frontierSeed_trace; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Attainment.frontierVector: bind-only; consumer: Attainment.distinguished_overlap, Attainment.frontierSeed, Attainment.frontierSeed_psd, Attainment.frontierSeed_scaled_scores, Attainment.frontierSeed_trace, Attainment.frontierVector_norm; escape_witness: none; Direct frozen dependencies: none. | proof_shape: Attainment.frontierSeed: bind-only; consumer: Attainment.frontierSeed_scaled_scores, Attainment.frontierSeed_scores, Attainment.frontierSeed_trace, result; escape_witness: none; Direct frozen dependencies: F13. | proof_shape: Attainment.frontierVector_norm: bind-only; consumer: Attainment.frontierSeed_scaled_scores, Attainment.frontierSeed_trace; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Attainment.frontierSeed_psd: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: F13. | proof_shape: Attainment.frontierSeed_trace: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: F9, F10, F13. | proof_shape: Attainment.distinguished_overlap: bind-only; consumer: Attainment.frontierSeed_scaled_scores; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Attainment.frontierSeed_scaled_scores: bind-only; consumer: Attainment.frontierSeed_scores; escape_witness: none; Direct frozen dependencies: F14, F1, F3, F4, F5, F2, F6, F7, F8, F11, F13. | proof_shape: Attainment.frontierSeed_scores: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: F14, F1, F3, F4, F5, F2, F6, F7, F8, F11, F13. | proof_shape: curve: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: claim: bind-only; consumer: result; escape_witness: none; Direct frozen dependencies: F5, F11. | proof_shape: result: content; consumer: none; escape_witness: D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.GlobalBound.global_operator_bound; Direct frozen dependencies: F14, F1, F3, F4, F5, F2, F6, F7, F8, F9, F10, F11, F13, F12.
-/
import D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import D5.S3.Quantum.Reduction.IsometricCompression
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
open scoped BigOperators Matrix ComplexOrder
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
private def support (N d : ℕ) (p : ℝ) : ℝ :=
  (2 * N + 1 + p * ((d : ℝ) - N) +
    Real.sqrt ((1 - p * ((d : ℝ) - N)) ^ 2 + 4 * p ^ 2 * N * ((d : ℝ) - 1))) /
    (2 * ((N : ℝ) + d))
private theorem support_scaled (N d : ℕ) (hd : 1 ≤ d) (p : ℝ) :
    ((N : ℝ)+d)*support N d p =
      topRoot ((N : ℝ)+1) (p*Real.sqrt ((N : ℝ)*(d-1)))
        ((N : ℝ)+p*((d : ℝ)-N)) := by
  have hnon : 0 ≤ (N : ℝ)*((d : ℝ)-1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hd))
  have he : (((N : ℝ)+1)-((N : ℝ)+p*((d : ℝ)-N)))^2+
      4*(p*Real.sqrt ((N : ℝ)*(d-1)))^2 =
      (1-p*((d : ℝ)-N))^2+4*p^2*N*((d : ℝ)-1) := by
    rw [mul_pow,Real.sq_sqrt hnon]
    ring
  unfold support topRoot
  rw [he]
  field_simp
  ring
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
private def seedF (n k α β : ℝ) : ℝ :=
  (1+(Real.sqrt n*α+Real.sqrt k*β)^2)/(n+k+1)
private def seedG (n k α : ℝ) : ℝ := (n+α^2)/(n+k+1)
private theorem seed_curve_identity (n k α β : ℝ) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hunit : α^2+β^2=1) :
    (1/(n+k+1) + (Real.sqrt (k*((n+1)/(n+k+1)-(seedG n k α))) + Real.sqrt (n*((seedG n k α)-n/(n+k+1))))^2) = seedF n k α β := by
  let S := n+k+1
  have hS : 0 < S := by dsimp [S]; linarith
  have hrS : (Real.sqrt S)^2=S := Real.sq_sqrt hS.le
  have hkS : k*((n+1)/S-(n+α^2)/S) = (Real.sqrt k*β/Real.sqrt S)^2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hk, hrS]
    field_simp
    nlinarith
  have hnS : n*((n+α^2)/S-n/S) = (Real.sqrt n*α/Real.sqrt S)^2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hn, hrS]
    field_simp
    ring
  have hpβ : 0 ≤ Real.sqrt k*β/Real.sqrt S := by positivity
  have hpα : 0 ≤ Real.sqrt n*α/Real.sqrt S := by positivity
  change 1/S+(Real.sqrt (k*((n+1)/S-(n+α^2)/S)) +
    Real.sqrt (n*((n+α^2)/S-n/S)))^2 = _
  rw [hkS, hnS, Real.sqrt_sq hpβ, Real.sqrt_sq hpα]
  change _ = (1+(Real.sqrt n*α+Real.sqrt k*β)^2)/S
  rw [← add_div, div_pow, hrS]
  ring
-- The parameter choice used to support every nonendpoint point of the frontier.
private def slopeDenominator (n k r : ℝ) : ℝ :=
  Real.sqrt (n*k)*(1-r^2)+(k+1-n)*r
private theorem slopeDenominator_minus_r (n k r : ℝ) (hn : 0 < n) (hk : 0 < k) :
    slopeDenominator n k r-r =
      Real.sqrt (n*k)*(Real.sqrt (k/n)-r)*(r+1/Real.sqrt (k/n)) := by
  have hkn : 0 < k/n := div_pos hk hn
  have hs0 : Real.sqrt (k/n) ≠ 0 := (Real.sqrt_pos.mpr hkn).ne'
  have hsq : (Real.sqrt (k/n))^2 = k/n := Real.sq_sqrt hkn.le
  have hprod : Real.sqrt (n*k)*Real.sqrt (k/n)=k := by
    rw [← Real.sqrt_mul (mul_nonneg hn.le hk.le)]
    have he : (n*k)*(k/n)=k^2 := by field_simp <;> ring
    rw [he, Real.sqrt_sq hk.le]
  have hquot : Real.sqrt (n*k)/Real.sqrt (k/n)=n := by
    apply (div_eq_iff hs0).mpr
    have h : n*(Real.sqrt (k/n))^2=k := by rw [hsq]; field_simp
    have hp := Real.sqrt_nonneg (n*k)
    nlinarith [hprod]
  unfold slopeDenominator
  calc
    _ = Real.sqrt (n*k)*Real.sqrt (k/n)*r + Real.sqrt (n*k) -
        Real.sqrt (n*k)*r^2 - (Real.sqrt (n*k)/Real.sqrt (k/n))*r := by
      rw [hprod,hquot]; ring
    _ = _ := by field_simp <;> ring
private theorem slope_parameter_range (n k r : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hr : 0 < r) (hrmax : r ≤ Real.sqrt (k/n)) :
    0 < r/slopeDenominator n k r ∧ r/slopeDenominator n k r ≤ 1 := by
  have he := slopeDenominator_minus_r n k r hn hk
  have hfac : 0 ≤ Real.sqrt (n*k)*(Real.sqrt (k/n)-r)*(r+1/Real.sqrt (k/n)) := by positivity
  have hD : r ≤ slopeDenominator n k r := by linarith
  have hDp : 0 < slopeDenominator n k r := lt_of_lt_of_le hr hD
  exact ⟨div_pos hr hDp, (div_le_one hDp).mpr hD⟩
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve
private theorem topRoot_eq_of_certificate (a b c μ : ℝ)
    (hleft : a ≤ μ) (hright : c ≤ μ) (hdet : (μ-a)*(μ-c)=b^2) :
    topRoot a b c=μ := by
  have hs : 0 ≤ 2*μ-a-c := by linarith
  have he : (a-c)^2+4*b^2=(2*μ-a-c)^2 := by nlinarith [hdet]
  unfold topRoot
  rw [he,Real.sqrt_sq hs]
  ring
private theorem slope_top_eigenvalue (n k r : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hr : 0 < r) (hrmax : r ≤ Real.sqrt (k/n)) :
    let p := r/slopeDenominator n k r
    topRoot (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n)) =
      n+1+p*Real.sqrt (n*k)*r := by
  dsimp
  let p := r/slopeDenominator n k r
  let s := Real.sqrt (n*k)
  have hp : 0 < p := (slope_parameter_range n k r hn hk hr hrmax).1
  have hD : 0 < slopeDenominator n k r :=
    (div_pos_iff_of_pos_left hr).mp hp
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hn hk)
  have hpe : p*slopeDenominator n k r=r := div_mul_cancel₀ _ hD.ne'
  have hsecond : p*s+(n+p*(k+1-n))*r=(n+1+p*s*r)*r := by
    dsimp [slopeDenominator] at hpe
    change p*(s*(1-r^2)+(k+1-n)*r)=r at hpe
    nlinarith
  change topRoot (n+1) (p*s) (n+p*(k+1-n))=n+1+p*s*r
  apply topRoot_eq_of_certificate
  · nlinarith [mul_pos hp hs, mul_pos (mul_pos hp hs) hr]
  ·
    nlinarith
  · have he : ((n+1+p*s*r)-(n+1))*((n+1+p*s*r)-(n+p*(k+1-n))) =
        p*s*((n+1+p*s*r)*r-(n+p*(k+1-n))*r) := by ring
    rw [he,← hsecond]
    ring
-- Every point in the stated interval has a normalized nonnegative seed pair.
private theorem curve_seed_parameters (n k G : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hlower : n/(n+k) ≤ G) (hupper : G ≤ (n+1)/(n+k+1)) :
    let α := Real.sqrt ((n+k+1)*G-n)
    let β := Real.sqrt (n+1-(n+k+1)*G)
    0 < α ∧ 0 ≤ β ∧ α^2+β^2=1 ∧ seedG n k α=G ∧
      (1/(n+k+1) + (Real.sqrt (k*((n+1)/(n+k+1)-G)) + Real.sqrt (n*(G-n/(n+k+1))))^2)=seedF n k α β ∧ β/α ≤ Real.sqrt (k/n) := by
  let S := n+k+1
  have hS : 0 < S := by dsimp [S]; linarith
  have hnk : 0 < n+k := add_pos hn hk
  have hl : n ≤ G*(n+k) := (div_le_iff₀ hnk).mp hlower
  have hu : G*S ≤ n+1 := (le_div_iff₀ hS).mp hupper
  have hα : 0 < S*G-n := by nlinarith
  have hβ : 0 ≤ n+1-S*G := by nlinarith
  have hαsq := Real.sq_sqrt hα.le
  have hβsq := Real.sq_sqrt hβ
  let α := Real.sqrt (S*G-n)
  let β := Real.sqrt (n+1-S*G)
  have hαp : 0 < α := Real.sqrt_pos.mpr hα
  have hβp : 0 ≤ β := Real.sqrt_nonneg _
  have hunit : α^2+β^2=1 := by dsimp [α,β]; linarith
  have hg : seedG n k α=G := by
    change (n+α^2)/S=G
    apply (div_eq_iff hS.ne').mpr
    dsimp [α]
    linarith
  have hcurve : (1/(n+k+1) + (Real.sqrt (k*((n+1)/(n+k+1)-G)) + Real.sqrt (n*(G-n/(n+k+1))))^2)=seedF n k α β := by
    rw [← hg]
    exact seed_curve_identity n k α β hn.le hk.le hαp.le hβp hunit
  have hratio : β/α ≤ Real.sqrt (k/n) := by
    apply (div_le_iff₀ hαp).mpr
    have hs := Real.sq_sqrt (div_nonneg hk.le hn.le)
    have he : (k/n)*α^2-β^2 ≥ 0 := by
      apply (mul_nonneg_iff_of_pos_left hn).mp
      dsimp [α,β]
      rw [hαsq,hβsq]
      field_simp
      nlinarith
    have hrnonneg : 0 ≤ Real.sqrt (k/n)*α := by positivity
    nlinarith
  change 0 < α ∧ 0 ≤ β ∧ α^2+β^2=1 ∧ _ ∧ _ ∧ _
  exact ⟨hαp,hβp,hunit,hg,hcurve,hratio⟩
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar
private theorem topRoot_gap_upper (a b c : ℝ) (hgap : 1/2 ≤ a-c) :
    topRoot a b c-a ≤ 2*b^2 := by
  have hleft := (topRoot_bounds a b c).1
  have hdet := topRoot_determinant a b c
  have hμc : 1/2 ≤ topRoot a b c-c := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hμc)]
-- At maximum estimation fidelity, a family of small positive supporting weights
-- bounds F; the p=0 objective alone does not.
private theorem endpoint_from_support_family (n k F : ℝ) (hn : 0 < n) (hk : 0 < k)
    (h : ∀ p : ℝ, 0 < p → p ≤ 1 →
      p*F+(1-p)*(n+1) ≤ topRoot (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n))) :
    F ≤ n+1 := by
  by_contra hF
  have hFp : 0 < F-(n+1) := by linarith
  let B := |k+1-n|+1
  let p := min (1/(2*B)) ((F-(n+1))/(4*n*k))
  have hp : 0 < p := lt_min (by positivity) (by positivity)
  have hpB : p ≤ 1/(2*B) := min_le_left _ _
  have hpF : p ≤ (F-(n+1))/(4*n*k) := min_le_right _ _
  have hp1 : p ≤ 1 := by
    have hB1 : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg (k+1-n)]
    have h : 1/(2*B) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact hpB.trans h
  have hmulB : p*(2*B) ≤ 1 := (le_div_iff₀ (by positivity)).mp hpB
  have hdelta : k+1-n ≤ B := by dsimp [B]; linarith [le_abs_self (k+1-n)]
  have hgap : 1/2 ≤ (n+1)-(n+p*(k+1-n)) := by
    nlinarith
  have hup := topRoot_gap_upper (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n)) hgap
  rw [mul_pow,Real.sq_sqrt (mul_pos hn hk).le] at hup
  have hs := h p hp hp1
  have hpFm : p*(4*n*k) ≤ F-(n+1) := (le_div_iff₀ (by positivity)).mp hpF
  nlinarith
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.ScalarAssembly
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Endpoint
-- An abstract scalar assembly, with the actual matrix support and seed-attainment
-- obligations kept explicit rather than assumed as part of a redefined claim.
private theorem slope_quadratic_identity (n k α β r p : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hunit : α^2+β^2=1) (hαr : α*r=β) (hpD : p*slopeDenominator n k r=r) :
    p*(1+(Real.sqrt n*α+Real.sqrt k*β)^2)+(1-p)*(n+α^2)=
      n+1+p*Real.sqrt (n*k)*r := by
  have hnroot := Real.sq_sqrt hn.le
  have hkroot := Real.sq_sqrt hk.le
  have hprod : Real.sqrt n*Real.sqrt k=Real.sqrt (n*k) := (Real.sqrt_mul hn.le k).symm
  have hsecond : p*Real.sqrt (n*k)+(n+p*(k+1-n))*r=(n+1+p*Real.sqrt (n*k)*r)*r := by
    unfold slopeDenominator at hpD
    nlinarith
  let s := Real.sqrt (n*k)
  let μ := n+1+p*s*r
  have hfirst : (n+1)*α+p*s*β=μ*α := by dsimp [μ]; rw [← hαr]; ring
  have hsecond' : p*s*α+(n+p*(k+1-n))*β=μ*β := by
    calc
      _ = (p*s+(n+p*(k+1-n))*r)*α := by rw [← hαr]; ring
      _ = (μ*r)*α := by rw [hsecond]
      _ = _ := by rw [← hαr]; ring
  have hquadratic : (n+1)*α^2+2*p*s*α*β+(n+p*(k+1-n))*β^2=μ := by
    calc
      _ = ((n+1)*α+p*s*β)*α+(p*s*α+(n+p*(k+1-n))*β)*β := by ring
      _ = μ*(α^2+β^2) := by rw [hfirst,hsecond']; ring
      _ = μ := by rw [hunit,mul_one]
  calc
    _ = p*(1+n*α^2+2*s*α*β+k*β^2)+(1-p)*(n+α^2) := by
      change _ = p*(1+n*α^2+2*Real.sqrt (n*k)*α*β+k*β^2)+(1-p)*(n+α^2)
      have hsq : (Real.sqrt n*α+Real.sqrt k*β)^2=
          n*α^2+2*Real.sqrt (n*k)*α*β+k*β^2 := by
        calc
          _ = (Real.sqrt n)^2*α^2+2*(Real.sqrt n*Real.sqrt k)*α*β+(Real.sqrt k)^2*β^2 := by ring
          _ = _ := by rw [hnroot,hkroot,hprod]
      rw [hsq]
      ring
    _ = (n+1)*α^2+2*p*s*α*β+(n+p*(k+1-n))*β^2 := by
      linear_combination -(n+p-p*n)*hunit
    _ = _ := hquadratic
private theorem scalar_frontier (n k F G : ℝ) (hn : 0 < n) (hk : 0 < k)
    (hlower : n/(n+k) ≤ G) (hupper : G ≤ (n+1)/(n+k+1))
    (hsupport : ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      p*((n+k+1)*F)+(1-p)*((n+k+1)*G) ≤
        topRoot (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n))) :
    F ≤ (1/(n+k+1) + (Real.sqrt (k*((n+1)/(n+k+1)-G)) + Real.sqrt (n*(G-n/(n+k+1))))^2) := by
  let S := n+k+1
  have hS : 0 < S := by dsimp [S]; linarith
  let α := Real.sqrt (S*G-n)
  let β := Real.sqrt (n+1-S*G)
  have hpairs := curve_seed_parameters n k G hn hk hlower hupper
  change 0 < α ∧ 0 ≤ β ∧ α^2+β^2=1 ∧ seedG n k α=G ∧
    (1/(n+k+1) + (Real.sqrt (k*((n+1)/(n+k+1)-G)) + Real.sqrt (n*(G-n/(n+k+1))))^2)=seedF n k α β ∧ β/α ≤ Real.sqrt (k/n) at hpairs
  rcases hpairs with ⟨hα,hβ,hunit,hg,hcurve,hrmax⟩
  by_cases hb0 : β=0
  · have hG : S*G=n+1 := by
      have h := Real.sq_sqrt (show 0 ≤ n+1-S*G by
        have hu := (le_div_iff₀ hS).mp hupper; linarith)
      change β^2=n+1-S*G at h
      rw [hb0] at h
      nlinarith
    have he := endpoint_from_support_family n k (S*F) hn hk
      (fun p hp hp1 => by simpa only [← hG] using hsupport p hp.le hp1)
    rw [hcurve]
    unfold seedF
    have hαsq : α^2=1 := by rw [hb0] at hunit; nlinarith
    rw [hb0,mul_zero,add_zero,mul_pow,Real.sq_sqrt hn.le,hαsq,mul_one]
    exact (le_div_iff₀ hS).mpr (by nlinarith)
  · have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hb0)
    let r := β/α
    have hr : 0 < r := div_pos hβp hα
    let p := r/slopeDenominator n k r
    have hp := slope_parameter_range n k r hn hk hr hrmax
    have he := slope_top_eigenvalue n k r hn hk hr hrmax
    change topRoot (n+1) (p*Real.sqrt (n*k)) (n+p*(k+1-n))=
      n+1+p*Real.sqrt (n*k)*r at he
    have hbound := hsupport p hp.1.le hp.2
    rw [he] at hbound
    have hαr : α*r=β := by dsimp [r]; field_simp
    have hpD : p*slopeDenominator n k r=r := by
      have hDp : 0 < slopeDenominator n k r := (div_pos_iff_of_pos_left hr).mp hp.1
      dsimp [p]
      exact div_mul_cancel₀ _ hDp.ne'
    have hμ := slope_quadratic_identity n k α β r p hn hk hunit hαr hpD
    have hgscaled : S*G=n+α^2 := by
      change (n+α^2)/S=G at hg
      have h := (div_eq_iff hS.ne').mp hg
      nlinarith
    rw [← hμ, hgscaled] at hbound
    have hF : S*F ≤ 1+(Real.sqrt n*α+Real.sqrt k*β)^2 := by
      exact (mul_le_mul_iff_right₀ hp.1).mp ((add_le_add_iff_right _).mp hbound)
    rw [hcurve]
    exact (le_div_iff₀ hS).mpr (by simpa [seedF,S,mul_comm] using hF)
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.ScalarAssembly
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Seed
open scoped BigOperators Matrix ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private def rankOneSeed (D : ℝ) (w : ι → ℂ) : Matrix ι ι ℂ :=
  (D : ℂ) • Matrix.vecMulVec w (star w)
private theorem rankOneSeed_psd (D : ℝ) (w : ι → ℂ) (hD : 0 ≤ D) :
    (rankOneSeed D w).PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star w).smul (by exact_mod_cast hD)
private theorem rankOneSeed_trace (D : ℝ) (w : ι → ℂ) :
    (rankOneSeed D w).trace = ((D*∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [rankOneSeed,Matrix.trace_smul,Matrix.trace_vecMulVec,dotProduct,
    Pi.star_apply,Complex.ofReal_mul,Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.mul_conj (w i)
private theorem rankOneSeed_score (D : ℝ) (w : ι → ℂ) (B : Matrix ι ι ℂ) :
    (rankOneSeed D w*B).trace = (D : ℂ)*(star w ⬝ᵥ (B*ᵥw)) := by
  rw [rankOneSeed, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  calc
    _ = B *ᵥ w ⬝ᵥ star w := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
        WithLp.ofLp_toLp] using
        D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace B (WithLp.toLp 2 w)
    _ = _ := dotProduct_comm _ _
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Seed
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Inclusion
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Seed
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
private theorem inclusion_compression (f : ι → κ) (B : Matrix κ κ ℂ) :
    (((1 : Matrix κ κ ℂ).submatrix id f))ᴴ * B *
      ((1 : Matrix κ κ ℂ).submatrix id f) = B.submatrix f f := by
  rw [Matrix.conjTranspose_submatrix]
  simp only [Matrix.conjTranspose_one]
  have hl : ((1 : Matrix κ κ ℂ).submatrix f id) * B = B.submatrix f id :=
    Matrix.one_submatrix_mul f (Equiv.refl κ) B
  have hr : B.submatrix f id * ((1 : Matrix κ κ ℂ).submatrix id f) = B.submatrix f f :=
    Matrix.mul_submatrix_one (Equiv.refl κ) f (B.submatrix f id)
  rw [hl]
  exact hr
private theorem inclusion_gram (f : ι → κ) (hf : Function.Injective f) :
    (((1 : Matrix κ κ ℂ).submatrix id f))ᴴ *
      ((1 : Matrix κ κ ℂ).submatrix id f) = 1 := by
  have he : ((1 : Matrix κ κ ℂ).submatrix id f) =
      D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix
        (⟨f, hf⟩ : ι ↪ κ) := by
    ext x i
    simp [D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix,
      Matrix.one_apply, eq_comm]
  rw [he]
  exact D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinate_gram _
private theorem includedSeed_psd (f : ι → κ) (D : ℝ) (w : ι → ℂ) (hD : 0 ≤ D) :
    (D5.S3.Quantum.Reduction.IsometricCompression.compress
      (((1 : Matrix κ κ ℂ).submatrix id f)ᴴ) (rankOneSeed D w)).PosSemidef := by
  simpa only [D5.S3.Quantum.Reduction.IsometricCompression.compress,
    Matrix.conjTranspose_conjTranspose] using
    (rankOneSeed_psd D w hD).mul_mul_conjTranspose_same (((1 : Matrix κ κ ℂ).submatrix id f))
private theorem includedSeed_trace (f : ι → κ) (hf : Function.Injective f) (D : ℝ) (w : ι → ℂ) :
    (D5.S3.Quantum.Reduction.IsometricCompression.compress
      (((1 : Matrix κ κ ℂ).submatrix id f)ᴴ) (rankOneSeed D w)).trace=((D*∑ i, Complex.normSq (w i):ℝ):ℂ) := by
  simp only [D5.S3.Quantum.Reduction.IsometricCompression.compress,
    Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,inclusion_gram f hf,Matrix.one_mul]
  exact rankOneSeed_trace D w
private theorem includedSeed_score (f : ι → κ) (D : ℝ) (w : ι → ℂ) (B : Matrix κ κ ℂ) :
    (D5.S3.Quantum.Reduction.IsometricCompression.compress
      (((1 : Matrix κ κ ℂ).submatrix id f)ᴴ) (rankOneSeed D w)*B).trace=(D:ℂ)*(star w ⬝ᵥ (B.submatrix f f*ᵥw)) := by
  simp only [D5.S3.Quantum.Reduction.IsometricCompression.compress,
    Matrix.conjTranspose_conjTranspose]
  calc
    _ = ((((1 : Matrix κ κ ℂ).submatrix id f)*rankOneSeed D w)*((((1 : Matrix κ κ ℂ).submatrix id f))ᴴ*B)).trace := by rw [Matrix.mul_assoc]
    _ = (((((1 : Matrix κ κ ℂ).submatrix id f))ᴴ*B)*(((1 : Matrix κ κ ℂ).submatrix id f)*rankOneSeed D w)).trace := Matrix.trace_mul_comm _ _
    _ = (((((1 : Matrix κ κ ℂ).submatrix id f))ᴴ*B*((1 : Matrix κ κ ℂ).submatrix id f))*rankOneSeed D w).trace := by simp only [Matrix.mul_assoc]
    _ = (rankOneSeed D w*((((1 : Matrix κ κ ℂ).submatrix id f))ᴴ*B*((1 : Matrix κ κ ℂ).submatrix id f))).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [inclusion_compression,rankOneSeed_score]
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Inclusion
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
private theorem score_A_scale {N d : ℕ} (χ : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ) :
    (χ*A N d).trace.re=(((N + d - 1).choose (d - 1)):ℝ)*((N:ℝ)+d)*(χ*RF N d).trace.re := by
  simp only [A,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,sub_zero,add_zero,zero_add,Nat.cast_add]
private theorem score_C_scale {N d : ℕ} (χ : Matrix ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ((({n : Fin d → ℕ // ∑ i, n i = N}) × Fin d)) ℂ) :
    (χ*C N d).trace.re=(((N + d - 1).choose (d - 1)):ℝ)*((N:ℝ)+d)*(χ*RG N d).trace.re := by
  simp only [C,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.natCast_re,Complex.natCast_im,zero_mul,mul_zero,sub_zero,add_zero,zero_add,Nat.cast_add]
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Trace
open scoped BigOperators Matrix ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem trace_upper_bound (χ B : Matrix ι ι ℂ) (μ D : ℝ)
    (hχ : χ.PosSemidef) (htr : χ.trace=(D:ℂ))
    (hB : ((μ:ℂ) • (1 : Matrix ι ι ℂ)-B).PosSemidef) :
    (χ*B).trace.re ≤ μ*D := by
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hχ hB
  change 0 ≤ (χ*((μ:ℂ) • (1 : Matrix ι ι ℂ)-B)).trace.re at h
  simp only [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,
    Matrix.trace_smul,smul_eq_mul,htr,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at h
  change 0 ≤ μ*D-(χ*B).trace.re at h
  linarith
private theorem weighted_trace_upper_bound (χ A C : Matrix ι ι ℂ) (p μ D : ℝ)
    (hχ : χ.PosSemidef) (htr : χ.trace=(D:ℂ))
    (hB : ((μ:ℂ) • (1 : Matrix ι ι ℂ)-((p:ℂ) • A+((1-p:ℝ):ℂ) • C)).PosSemidef) :
    p*(χ*A).trace.re+(1-p)*(χ*C).trace.re ≤ μ*D := by
  have h := trace_upper_bound χ ((p:ℂ) • A+((1-p:ℝ):ℂ) • C) μ D hχ htr hB
  simpa only [Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
    smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero] using h
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Trace
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Scalar D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Complex D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Global D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.GlobalBound D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Trace
private theorem seed_support_bound {K k : ℕ} (hk : 1 ≤ k)
    (χ : Matrix ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ℂ)
    (hχ : χ.PosSemidef) (htr : χ.trace=((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℂ))
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p*(((K:ℝ)+1+k+1)*(χ*RF (K+1) (k+1)).trace.re)+
      (1-p)*(((K:ℝ)+1+k+1)*(χ*RG (K+1) (k+1)).trace.re) ≤
      (((K+1 : ℕ) : ℝ)+(k+1 : ℕ))*support (K+1) (k+1) p := by
  rw [support_scaled (K+1) (k+1) (Nat.le_add_right_of_le hk) p]
  have hd : 1 ≤ k+1 := Nat.le_add_right_of_le hk
  have hD : 0 < ((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ) := by exact_mod_cast dimension_pos (N:=K+1) hd
  have h := weighted_trace_upper_bound χ (A (K+1) (k+1)) (C (K+1) (k+1)) p
    (blockMaximum ((K:ℝ)+k+1) p ((K:ℝ)+1)) ((((K+1) + (k+1) - 1).choose ((k+1) - 1))) hχ htr
    (by simpa only [AffineMap.lineMap_apply_module, Complex.ofReal_sub, Complex.ofReal_one, add_comm]
      using global_operator_bound (K := K) hk p hp hp1)
  rw [score_A_scale,score_C_scale] at h
  have he : p*(((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)*(((K+1:ℕ):ℝ)+(k+1:ℕ))*(χ*RF (K+1) (k+1)).trace.re)+
      (1-p)*(((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)*(((K+1:ℕ):ℝ)+(k+1:ℕ))*(χ*RG (K+1) (k+1)).trace.re) =
      ((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)*(p*((((K+1:ℕ):ℝ)+(k+1:ℕ))*(χ*RF (K+1) (k+1)).trace.re)+
        (1-p)*((((K+1:ℕ):ℝ)+(k+1:ℕ))*(χ*RG (K+1) (k+1)).trace.re)) := by ring
  rw [he,mul_comm (blockMaximum _ _ _)] at h
  have hc := (mul_le_mul_iff_right₀ hD).mp h
  rw [show (K:ℝ)+k+1=((K:ℝ)+1)+k by ring,
    distinguished_block_identity ((K:ℝ)+1) k p (by positivity)] at hc
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two,add_sub_cancel_right] using hc
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.Blocks D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.CEntries D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockMatrices
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.BlockSpectral D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Inclusion D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores
private def distinguishedOcc (K k : ℕ) : ({n : Fin (k+1) → ℕ // ∑ i, n i = K}) :=
  ⟨Pi.single 0 K, by simp⟩
private def frontierVector (k : ℕ) (α β : ℝ) : Fin (k+1) → ℂ :=
  Fin.cons (α : ℂ) (fun _ => ((β / Real.sqrt k : ℝ) : ℂ))
private def frontierSeed (K k : ℕ) (α β : ℝ) :
    Matrix ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ℂ :=
  D5.S3.Quantum.Reduction.IsometricCompression.compress
    (((1 : Matrix
      ({n : Fin (k+1) → ℕ // ∑ i, n i = K+1} × Fin (k+1))
      ({n : Fin (k+1) → ℕ // ∑ i, n i = K+1} × Fin (k+1)) ℂ).submatrix
      id (blockIndex (distinguishedOcc K k)))ᴴ)
    (Seed.rankOneSeed ((((K+1) + (k+1) - 1).choose ((k+1) - 1))) (frontierVector k α β))
private theorem frontierVector_norm {k : ℕ} (hk : 1 ≤ k) (α β : ℝ) :
    ∑ i, Complex.normSq (frontierVector k α β i)=α^2+β^2 := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  rw [Fin.sum_univ_succ]
  simp only [frontierVector,Fin.cons_zero,Fin.cons_succ,Fin.succ_ne_zero,if_false,if_pos rfl,if_true,Complex.normSq_ofReal,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [← pow_two]
  rw [div_pow,Real.sq_sqrt hkp.le]
  field_simp
private theorem frontierSeed_psd (K k : ℕ) (α β : ℝ) : (frontierSeed K k α β).PosSemidef :=
  includedSeed_psd _ _ _ (by positivity)
private theorem frontierSeed_trace {K k : ℕ} (hk : 1 ≤ k) (α β : ℝ) (hu : α^2+β^2=1) :
    (frontierSeed K k α β).trace=((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℂ) := by
  rw [frontierSeed,includedSeed_trace _ (by
    intro i j h
    exact congrArg Prod.snd h),frontierVector_norm hk,hu,mul_one]
  norm_cast
private theorem distinguished_overlap {K k : ℕ} (hk : 1 ≤ k) (α β : ℝ) :
    ∑ i, (blockVector (distinguishedOcc K k) i:ℂ)*frontierVector k α β i =
      ((Real.sqrt ((K:ℝ)+1)*α+Real.sqrt (k:ℝ)*β:ℝ):ℂ) := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  rw [Fin.sum_univ_succ]
  simp only [blockVector,distinguishedOcc,frontierVector,Pi.single_apply,Fin.cons_zero,Fin.cons_succ,Fin.succ_ne_zero,if_false,if_pos rfl,if_true,
    Nat.cast_zero,zero_add,Real.sqrt_one,Complex.ofReal_one,one_mul,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have he : (k:ℝ)*(β/Real.sqrt (k:ℝ))=Real.sqrt (k:ℝ)*β := by
    field_simp
    rw [Real.sq_sqrt hkp.le]
    ring
  push_cast
  have hec := congrArg (fun t : ℝ => (t:ℂ)) he
  push_cast at hec
  rw [hec]
-- Scores are first computed for the scaled literal operators A and C.
private theorem frontierSeed_scaled_scores {K k : ℕ} (hk : 1 ≤ k)
    (α β : ℝ) (hu : α^2+β^2=1) :
    ((frontierSeed K k α β*A (K+1) (k+1)).trace =
      (((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)*(1+(Real.sqrt ((K:ℝ)+1)*α+Real.sqrt (k:ℝ)*β)^2):ℝ)) ∧
    ((frontierSeed K k α β*C (K+1) (k+1)).trace =
      (((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)*((K:ℝ)+1+α^2):ℝ)) := by
  have hd : 1 ≤ k+1 := Nat.le_add_right_of_le hk
  let m := distinguishedOcc K k
  let w := frontierVector k α β
  have hn : ∑ i, Complex.normSq (w i)=1 := by rw [frontierVector_norm hk,hu]
  have hA : (A (K+1) (k+1)).submatrix (blockIndex m) (blockIndex m)=
      blockOperator (blockVector m) 0 ((K:ℝ)+1) 1 := by
    simpa [m,distinguishedOcc] using weighted_block hd m 1
  have hC : (C (K+1) (k+1)).submatrix (blockIndex m) (blockIndex m)=
      blockOperator (blockVector m) 0 ((K:ℝ)+1) 0 := by
    simpa [m,distinguishedOcc] using weighted_block hd m 0
  constructor
  · rw [frontierSeed,includedSeed_score,hA,blockOperator_quadratic,hn]
    rw [distinguished_overlap hk]
    simp only [one_mul,zero_mul,zero_add,sub_self,sub_zero,mul_one,add_zero,Complex.normSq_ofReal]
    push_cast
    ring
  · rw [frontierSeed,includedSeed_score,hC,blockOperator_quadratic,hn]
    simp [w,frontierVector,Complex.normSq_ofReal,pow_two]
private theorem frontierSeed_scores {K k : ℕ} (hk : 1 ≤ k)
    (α β : ℝ) (hu : α^2+β^2=1) :
    ((frontierSeed K k α β*RF (K+1) (k+1)).trace.re =
      D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve.seedF ((K:ℝ)+1) k α β) ∧
    ((frontierSeed K k α β*RG (K+1) (k+1)).trace.re =
      D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve.seedG ((K:ℝ)+1) k α) := by
  have hd : 1 ≤ k+1 := Nat.le_add_right_of_le hk
  have hD : ((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℝ)≠0 := by exact_mod_cast (dimension_pos (N:=K+1) hd).ne'
  have hS : ((K:ℝ)+1+k+1)≠0 := by positivity
  have hs := frontierSeed_scaled_scores (K:=K) hk α β hu
  have hA := congrArg Complex.re hs.1
  have hC := congrArg Complex.re hs.2
  rw [score_A_scale] at hA
  rw [score_C_scale] at hC
  simp only [Complex.ofReal_re,Nat.cast_add,Nat.cast_one] at hA hC
  constructor
  · unfold D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve.seedF
    apply (eq_div_iff hS).mpr
    apply (mul_left_cancel₀ hD)
    nlinarith only [hA]
  · unfold D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve.seedG
    apply (eq_div_iff hS).mpr
    apply (mul_left_cancel₀ hD)
    nlinarith only [hC]
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment
namespace D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral
private def curve (N d : ℕ) (G : ℝ) : ℝ :=
  1 / ((N : ℝ) + d) +
    (Real.sqrt (((d : ℝ) - 1) * (((N : ℝ) + 1) / ((N : ℝ) + d) - G)) +
      Real.sqrt ((N : ℝ) * (G - (N : ℝ) / ((N : ℝ) + d)))) ^ 2
def claim : Prop := ∀ N d : ℕ, 1 ≤ N → 2 ≤ d → ∀ G₀ : ℝ,
  (N : ℝ) / ((N : ℝ) + d - 1) ≤ G₀ → G₀ ≤ ((N : ℝ) + 1) / ((N : ℝ) + d) →
  IsGreatest {F : ℝ | ∃ χ : Matrix ({n : Fin d → ℕ // ∑ i, n i = N} × Fin d) ({n : Fin d → ℕ // ∑ i, n i = N} × Fin d) ℂ,
    χ.PosSemidef ∧ χ.trace = (((N + d - 1).choose (d - 1)) : ℂ) ∧
      (χ * RG N d).trace.re = G₀ ∧ F = (χ * RF N d).trace.re}
    (1 / ((N : ℝ) + d) +
      (Real.sqrt (((d : ℝ) - 1) * (((N : ℝ) + 1) / ((N : ℝ) + d) - G₀)) +
        Real.sqrt ((N : ℝ) * (G₀ - (N : ℝ) / ((N : ℝ) + d)))) ^ 2)
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Measurement.OccupationPartialTransposeSpectral.EntryFormula D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Scores D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Attainment D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Curve D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.Conjugate D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff.ScalarAssembly
theorem result : claim := by
  intro N d hN hd G hl hu
  obtain ⟨K,rfl⟩ : ∃ K, N=K+1 := Nat.exists_eq_add_one.mpr hN
  obtain ⟨k,rfl⟩ : ∃ k, d=k+1 := Nat.exists_eq_add_one.mpr (le_trans (by decide : 1 ≤ 2) hd)
  have hk : 1 ≤ k := Nat.le_of_lt_succ hd
  have hn : 0 < (K:ℝ)+1 := Nat.cast_add_one_pos K
  have hkr : 0 < (k:ℝ) := by exact_mod_cast hk
  have hl' : ((K:ℝ)+1)/(((K:ℝ)+1)+k) ≤ G := by
    have he : ((K:ℝ)+1)+((k:ℝ)+1)-1=((K:ℝ)+1)+k := by ring
    simpa only [Nat.cast_add,Nat.cast_one,he] using hl
  have hu' : G ≤ (((K:ℝ)+1)+1)/(((K:ℝ)+1)+k+1) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hu
  have hcurve : (1/(((K:ℝ)+1)+(k:ℝ)+1) + (Real.sqrt ((k:ℝ)*((((K:ℝ)+1)+1)/(((K:ℝ)+1)+(k:ℝ)+1)-G)) + Real.sqrt (((K:ℝ)+1)*(G-((K:ℝ)+1)/(((K:ℝ)+1)+(k:ℝ)+1))))^2)=curve (K+1) (k+1) G := by
    simp [curve,Nat.cast_add,Nat.cast_one,add_assoc]
  change IsGreatest {F : ℝ | ∃ χ : Matrix ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ((({n : Fin (k+1) → ℕ // ∑ i, n i = (K+1)}) × Fin (k+1))) ℂ,
    χ.PosSemidef ∧ χ.trace=((((K+1) + (k+1) - 1).choose ((k+1) - 1)):ℂ) ∧
      (χ*RG (K+1) (k+1)).trace.re=G ∧ F=(χ*RF (K+1) (k+1)).trace.re}
    (curve (K+1) (k+1) G)
  constructor
  · let α := Real.sqrt ((((K:ℝ)+1)+k+1)*G-((K:ℝ)+1))
    let β := Real.sqrt (((K:ℝ)+1)+1-(((K:ℝ)+1)+k+1)*G)
    have hs := curve_seed_parameters ((K:ℝ)+1) k G hn hkr hl' hu'
    change 0 < α ∧ 0 ≤ β ∧ α^2+β^2=1 ∧ seedG ((K:ℝ)+1) k α=G ∧
      (1/(((K:ℝ)+1)+(k:ℝ)+1) + (Real.sqrt ((k:ℝ)*((((K:ℝ)+1)+1)/(((K:ℝ)+1)+(k:ℝ)+1)-G)) + Real.sqrt (((K:ℝ)+1)*(G-((K:ℝ)+1)/(((K:ℝ)+1)+(k:ℝ)+1))))^2)=seedF ((K:ℝ)+1) k α β ∧ _ at hs
    rcases hs with ⟨_,_,hunit,hg,hf,_⟩
    refine ⟨frontierSeed K k α β,frontierSeed_psd K k α β,
      frontierSeed_trace hk α β hunit,?_,?_⟩
    · rw [(frontierSeed_scores (K:=K) hk α β hunit).2]
      exact hg
    · rw [(frontierSeed_scores (K:=K) hk α β hunit).1,← hcurve]
      exact hf
  · rintro F ⟨χ,hχ,htr,hG,rfl⟩
    rw [← hcurve]
    apply scalar_frontier ((K:ℝ)+1) k _ G hn hkr hl' hu'
    intro p hp hp1
    have h := seed_support_bound hk χ hχ htr p hp hp1
    rw [support_scaled (K+1) (k+1) (Nat.le_add_right_of_le hk) p] at h
    simpa only [hG,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,add_assoc,one_add_one_eq_two] using h
end D5.S3.Quantum.Measurement.QuditPartialEstimationTradeoff
end
