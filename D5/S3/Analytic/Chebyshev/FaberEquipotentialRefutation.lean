/- GID: D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Chebyshev/FaberEquipotentialRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.claim; result=D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result; claim=D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.claim
   digest: A univalent Laurent map has a degree-one monic Faber polynomial which is Chebyshev on its compact complement but not on an exterior equipotential. -/

/- Source: Miña-Díaz–Rubin, arXiv:2505.03967, Problem 2.2.
   admission_basis: open-problem-resolution (#15412; Refuted)
   Direct frozen dependencies: D5/S3/AnalyticClosure/ComplexPowerDifference
     (norm_pow_sub_pow_le;
      statement_id: sha256:b7edbb5cf79561007f44e5c761060c2fa581c7aaa1052a2f07ab94afa744ef71).
   Definitions (proof_shape: not-applicable):
     IsChebyshev -> claim, chebyshev_of_disc, result
     IsMonicFaber -> claim, faber
     claim -> result
     ψ -> perturbation_lipschitz, differentiable_exterior, correction_bound,
          faber, endpoints, compact_complement, result
   Per-declaration proof_shape and live consumers:
     powers_lipschitz: bind-only; consumer=perturbation_lipschitz
     inv_lipschitz: bind-only; consumer=perturbation_lipschitz
     perturbation_lipschitz: bind-only; consumers=injective_closed, exterior_bilipschitz
     injective_closed: bind-only; consumers=compact_complement, result
     exterior_bilipschitz: bind-only; consumer=compact_complement
     differentiable_exterior: bind-only; consumers=compact_complement, result
     correction_bound: bind-only; consumer=result
     faber: bind-only; consumer=result
     exterior_preconnected: bind-only; consumers=exterior_image_open, exterior_complement
     exterior_image_open: bind-only; consumer=compact_complement
     closed_exterior_image: bind-only; consumer=compact_complement
     exterior_complement: bind-only; consumer=compact_complement
     boundary_not_in_image: bind-only; consumer=result
     circle_algebra_bound: content; consumer=circle_complex_bound
     circle_complex_bound: content; consumer=circle_bound
     circle_bound: content; consumers=compact_complement, result
     endpoints: bind-only; consumers=compact_complement, result
     chebyshev_of_disc: bind-only; consumer=result
     compact_complement: content; consumer=result
     result: content; designated refutation conclusion
   escape_witness: circle_algebra_bound, the norm-square estimate using the
     new cross-term and residual inequalities on the normalized circle. -/

import D5.S3.AnalyticClosure.ComplexPowerDifference
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Metric Polynomial
open scoped Topology

namespace D5.S3.Analytic.Chebyshev.FaberEquipotentialRefutation

/-- `p` is a monic degree-`n` polynomial of least sup norm on `E`. -/
def IsChebyshev (E : Set ℂ) (n : ℕ) (p : Polynomial ℂ) : Prop :=
  p.Monic ∧ p.natDegree = n ∧
    ∀ q : Polynomial ℂ, q.Monic → q.natDegree = n →
      ∀ M : ℝ, (∀ z ∈ E, ‖q.eval z‖ ≤ M) → ∀ z ∈ E, ‖p.eval z‖ ≤ M

/-- `F` is the monic degree-`n` Faber polynomial of the exterior map `ψ` with capacity `κ`. -/
def IsMonicFaber (ψ : ℂ → ℂ) (κ : ℝ) (n : ℕ) (F : Polynomial ℂ) : Prop :=
  F.Monic ∧ F.natDegree = n ∧
    Filter.Tendsto (fun w => F.eval (ψ w) - ((κ : ℂ) * w) ^ n)
      (Bornology.cobounded ℂ) (nhds 0)

def claim : Prop :=
  ∀ (ψ : ℂ → ℂ) (κ : ℝ), 0 < κ →
    DifferentiableOn ℂ ψ {w | 1 < ‖w‖} → Set.InjOn ψ {w | 1 < ‖w‖} →
    IsCompact (ψ '' {w | 1 < ‖w‖})ᶜ →
    (∃ C : ℝ, ∀ w : ℂ, 2 < ‖w‖ → ‖ψ w - (κ : ℂ) * w‖ ≤ C) →
    ∀ (n : ℕ) (F : Polynomial ℂ), 1 ≤ n → IsMonicFaber ψ κ n F →
      IsChebyshev (ψ '' {w | 1 < ‖w‖})ᶜ n F →
      ∀ r : ℝ, 1 < r → IsChebyshev (ψ '' Metric.sphere 0 r) n F

private def ψ (w : ℂ) : ℂ :=
  w + (1 / 4 : ℂ) * w⁻¹ + (1 / 100 : ℂ) * (w⁻¹ ^ 2 - w⁻¹ ^ 4)

private lemma powers_lipschitz {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (j : ℕ) : ‖u ^ j - v ^ j‖ ≤ (j : ℝ) * ‖u - v‖ := by
  simpa using D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le
    u v j 1 (by norm_num) hu hv

private lemma inv_lipschitz {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖u⁻¹ - v⁻¹‖ ≤ ‖u - v‖ := by
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  have hiu : ‖u‖⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hu
  have hiv : ‖v‖⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hv
  rw [inv_sub_inv' hu0 hv0, norm_mul, norm_mul, norm_inv, norm_inv, norm_sub_rev]
  calc
    ‖u‖⁻¹ * ‖u - v‖ * ‖v‖⁻¹ ≤ 1 * ‖u - v‖ * 1 := by gcongr
    _ = ‖u-v‖ := by ring

private lemma perturbation_lipschitz {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖ψ u - ψ v - (u - v)‖ ≤ (31 / 100 : ℝ) * ‖u - v‖ := by
  have hiu : ‖u⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_le_one₀ (by linarith)).2 hu
  have hiv : ‖v⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_le_one₀ (by linarith)).2 hv
  have h1 := inv_lipschitz hu hv
  have h2 := (powers_lipschitz hiu hiv 2).trans (mul_le_mul_of_nonneg_left h1 (by norm_num))
  have h4 := (powers_lipschitz hiu hiv 4).trans (mul_le_mul_of_nonneg_left h1 (by norm_num))
  have heq : ψ u - ψ v - (u-v) = (1/4:ℂ)*(u⁻¹-v⁻¹) +
      (1/100:ℂ)*((u⁻¹^2-v⁻¹^2)-(u⁻¹^4-v⁻¹^4)) := by unfold ψ; ring
  rw [heq]
  have h := norm_sub_le (u⁻¹^2-v⁻¹^2) (u⁻¹^4-v⁻¹^4)
  calc
    _ ≤ ‖(1/4:ℂ)*(u⁻¹-v⁻¹)‖ +
        ‖(1/100:ℂ)*((u⁻¹^2-v⁻¹^2)-(u⁻¹^4-v⁻¹^4))‖ := norm_add_le _ _
    _ = (1/4:ℝ)*‖u⁻¹-v⁻¹‖ +
        (1/100:ℝ)*‖(u⁻¹^2-v⁻¹^2)-(u⁻¹^4-v⁻¹^4)‖ := by
      simp only [norm_mul]; norm_num
    _ ≤ (1/4:ℝ)*‖u-v‖ + (1/100:ℝ)*(2*‖u-v‖+4*‖u-v‖) := by
      gcongr
      exact h.trans (add_le_add h2 h4)
    _ = _ := by ring

private lemma injective_closed : InjOn ψ {w | 1 ≤ ‖w‖} := by
  intro u hu v hv heq
  have h := perturbation_lipschitz hu hv
  rw [heq, sub_self, zero_sub, norm_neg] at h
  have hn : ‖u-v‖ = 0 := by nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

private lemma exterior_bilipschitz {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖ψ u - ψ v‖ ≤ (131/100:ℝ)*‖u-v‖ ∧ ‖u-v‖ ≤ 2*‖ψ u-ψ v‖ := by
  have h := perturbation_lipschitz hu hv
  have ha := norm_add_le (ψ u-ψ v-(u-v)) (u-v)
  have hb := norm_sub_le (ψ u-ψ v) (ψ u-ψ v-(u-v))
  have he1 : ψ u-ψ v-(u-v)+(u-v) = ψ u-ψ v := by ring
  have he2 : ψ u-ψ v-(ψ u-ψ v-(u-v)) = u-v := by ring
  rw [he1] at ha
  rw [he2] at hb
  constructor <;> nlinarith [norm_nonneg (ψ u-ψ v)]

private lemma differentiable_exterior : DifferentiableOn ℂ ψ {w | 1 < ‖w‖} := by
  intro w hw
  have h0 : w ≠ 0 := by intro h; norm_num [h] at hw
  exact ((differentiableAt_id.add ((differentiableAt_id.inv h0).const_mul _)).add
    ((((differentiableAt_id.inv h0).pow 2).sub
      ((differentiableAt_id.inv h0).pow 4)).const_mul _)).differentiableWithinAt

private lemma correction_bound {w : ℂ} (hw : 1 ≤ ‖w‖) : ‖ψ w - w‖ ≤ 27/100 := by
  have hi : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_le_one₀ (by linarith)).2 hw
  have h2 : ‖w⁻¹^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi
  have h4 : ‖w⁻¹^4‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi
  have he : ψ w - w = (1/4:ℂ)*w⁻¹ + (1/100:ℂ)*(w⁻¹^2-w⁻¹^4) := by unfold ψ; ring
  rw [he]
  calc
    _ ≤ ‖(1/4:ℂ)*w⁻¹‖ + ‖(1/100:ℂ)*(w⁻¹^2-w⁻¹^4)‖ := norm_add_le _ _
    _ = (1/4:ℝ)*‖w⁻¹‖ + (1/100:ℝ)*‖w⁻¹^2-w⁻¹^4‖ := by
      simp only [norm_mul]; norm_num
    _ ≤ (1/4:ℝ)*1 + (1/100:ℝ)*(1+1) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add h2 h4)
    _ = _ := by norm_num

private lemma faber : IsMonicFaber ψ 1 1 X := by
  refine ⟨monic_X, natDegree_X, ?_⟩
  have hi : Tendsto (fun w : ℂ => w⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have ht := (hi.const_mul (1/4:ℂ)).add (((hi.pow 2).sub (hi.pow 4)).const_mul (1/100:ℂ))
  convert ht using 1 <;> simp only [eval_X, Complex.ofReal_one, one_mul, pow_one, ψ,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    mul_zero, sub_self, add_zero]
  ext w
  ring


private lemma exterior_preconnected (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hs : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1
  have hc := (isPreconnected_Ioi (a := R)).prod hs
  have hi := hc.image (fun p : ℝ × ℂ => p.1 • p.2) (by fun_prop)
  have he : (fun p : ℝ × ℂ => p.1 • p.2) ''
      (Ioi R ×ˢ Metric.sphere (0 : ℂ) 1) = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨t,w⟩, ⟨ht, hw⟩, rfl⟩
      have hn : ‖w‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hw
      simp only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, hn, mul_one]
      rwa [abs_of_pos (lt_of_le_of_lt hR ht)]
    · intro hz
      have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hR hz)
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · simp [inv_mul_cancel₀ hn]
      · change ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rwa [he] at hi

private lemma exterior_image_open {ψ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ ψ {w | 1 < ‖w‖})
    (hinj : InjOn ψ {w | 1 < ‖w‖}) :
    IsOpen (ψ '' {w | 1 < ‖w‖}) := by
  have ho : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have ha := (Complex.analyticOnNhd_iff_differentiableOn ho).mpr hd
  have hm := ha.is_constant_or_isOpen (exterior_preconnected 1 (by norm_num))
  rcases hm with ⟨c, hc⟩ | hm
  · have h2 : (2 : ℂ) ∈ {w : ℂ | 1 < ‖w‖} := by norm_num
    have h3 : (3 : ℂ) ∈ {w : ℂ | 1 < ‖w‖} := by norm_num
    have he : (2 : ℂ) = 3 := hinj h2 h3 ((hc 2 h2).trans (hc 3 h3).symm)
    norm_num at he
  · exact hm _ subset_rfl ho

private lemma closed_exterior_image {ψ : ℂ → ℂ}
    (hu : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖ψ u - ψ v‖ ≤ 2 * ‖u - v‖)
    (hl : ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖u - v‖ ≤ 2 * ‖ψ u - ψ v‖) :
    IsClosed (ψ '' {w | 1 ≤ ‖w‖}) := by
  let S : Set ℂ := {w | 1 ≤ ‖w‖}
  have hS : IsClosed S := isClosed_le continuous_const continuous_norm
  let : CompleteSpace S := hS.isComplete.completeSpace_coe
  let f : S → ℂ := fun w => ψ w
  have hfu : LipschitzWith 2 f := LipschitzWith.of_dist_le_mul fun u v => by
    simpa [f, Subtype.dist_eq, dist_eq_norm] using hu u v u.property v.property
  have hfl : AntilipschitzWith 2 f := AntilipschitzWith.of_le_mul_dist fun u v => by
    simpa [f, Subtype.dist_eq, dist_eq_norm] using hl u v u.property v.property
  convert (hfl.isClosedEmbedding hfu.uniformContinuous).isClosed_range using 1
  ext z
  simp [f, S, Set.mem_range, Set.mem_image]

private lemma exterior_complement {ψ : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (ho : IsOpen (ψ '' {w | 1 < ‖w‖}))
    (hc : IsClosed (ψ '' {w | 1 ≤ ‖w‖}))
    (hb : ∀ w : ℂ, ‖w‖ = 1 → ‖ψ w‖ ≤ R)
    (hi : ∃ w : ℂ, 1 < ‖w‖ ∧ R < ‖ψ w‖) :
    (ψ '' {w | 1 < ‖w‖})ᶜ ⊆ Metric.closedBall 0 R ∧
      IsCompact (ψ '' {w | 1 < ‖w‖})ᶜ := by
  have hcl : closure (ψ '' {w | 1 < ‖w‖}) ⊆ ψ '' {w | 1 ≤ ‖w‖} :=
    closure_minimal (image_mono (fun w hw => (show 1 ≤ ‖w‖ from le_of_lt hw))) hc
  have hall : {z : ℂ | R < ‖z‖} ⊆ ψ '' {w | 1 < ‖w‖} := by
    apply (exterior_preconnected R hR).subset_of_closure_inter_subset ho
    · obtain ⟨w, hw, hz⟩ := hi
      exact ⟨ψ w, hz, ⟨w, hw, rfl⟩⟩
    · rintro z ⟨hz, hRz⟩
      obtain ⟨w, hw, rfl⟩ := hcl hz
      refine ⟨w, ?_, rfl⟩
      exact lt_of_le_of_ne hw (fun he => (not_le_of_gt hRz) (hb w he.symm))
  have hsub : (ψ '' {w | 1 < ‖w‖})ᶜ ⊆ Metric.closedBall 0 R := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_not_gt (fun h => hz (hall h))
  exact ⟨hsub, (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset ho.isClosed_compl hsub⟩

private lemma boundary_not_in_image {ψ : ℂ → ℂ}
    (hi : InjOn ψ {w | 1 ≤ ‖w‖}) {w : ℂ} (hw : ‖w‖ = 1) :
    ψ w ∈ (ψ '' {w | 1 < ‖w‖})ᶜ := by
  rintro ⟨v, hv, he⟩
  have h : v = w := hi (show 1 ≤ ‖v‖ from le_of_lt hv) (show 1 ≤ ‖w‖ from le_of_eq hw.symm) he
  change 1 < ‖v‖ at hv
  rw [h, hw] at hv
  exact lt_irrefl 1 hv


private theorem circle_algebra_bound (r s x y : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hrs : r * s = 1) (hxy : x ^ 2 + y ^ 2 = 1) :
    ((r + s / 4) * x + (1 / 50 : ℝ) * s ^ 2 * y ^ 2 * (-1 + 4 * s ^ 2 * x ^ 2)) ^ 2 +
      ((r - s / 4) * y + (1 / 50 : ℝ) * s ^ 2 * x * y * (-1 - 2 * s ^ 2 + 4 * s ^ 2 * x ^ 2)) ^ 2 ≤
        (r + s / 4) ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hu : 0 ≤ s ^ 2 := sq_nonneg s
  have hs4 : s ^ 4 ≤ 1 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
  have hux : s ^ 2 * x ^ 2 ≤ s ^ 2 := mul_le_of_le_one_right hu hx2
  have hbrlo : -3 ≤ -1 - s ^ 2 + s ^ 4 / 4 + 4 * s ^ 2 * x ^ 2 := by
    nlinarith [mul_nonneg hu (sq_nonneg x), sq_nonneg (s ^ 2)]
  have hbrhi : -1 - s ^ 2 + s ^ 4 / 4 + 4 * s ^ 2 * x ^ 2 ≤ 3 := by nlinarith
  have hxlo : -1 ≤ x := by nlinarith
  have hxhi : x ≤ 1 := by nlinarith
  have hsxlo : -1 ≤ s * x := by nlinarith [mul_nonneg hs (by linarith : 0 ≤ x + 1)]
  have hsxhi : s * x ≤ 1 := by nlinarith [mul_nonneg hs (by linarith : 0 ≤ 1 - x)]
  let H := -1 - s ^ 2 + s ^ 4 / 4 + 4 * s ^ 2 * x ^ 2
  have hprod : s * x * H ≤ 3 := by
    have h1 := mul_nonneg (by dsimp [H]; linarith : 0 ≤ 3 - H)
      (by linarith : 0 ≤ 1 + s * x)
    have h2 := mul_nonneg (by dsimp [H]; linarith : 0 ≤ 3 + H)
      (by linarith : 0 ≤ 1 - s * x)
    nlinarith
  have hcross : (2 / 25 : ℝ) * s * x * y ^ 2 * H ≤ (6 / 25 : ℝ) * y ^ 2 := by
    nlinarith [mul_nonneg hy2 (by linarith : 0 ≤ 3 - s * x * H)]
  have hres : (1 / 2500 : ℝ) * s ^ 4 * y ^ 2 * (1 - 4 * s ^ 2 * (1 - s ^ 2) * x ^ 2) ≤
      (1 / 2500 : ℝ) * y ^ 2 := by
    have hneg : 0 ≤ 4 * s ^ 2 * (1 - s ^ 2) * x ^ 2 := by positivity
    have he : 1 - 4 * s ^ 2 * (1 - s ^ 2) * x ^ 2 ≤ 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ s ^ 4 * y ^ 2)
    have hmul2 := mul_le_mul_of_nonneg_right hs4 hy2
    nlinarith
  have he :
    ((r + s / 4) * x + (1 / 50 : ℝ) * s ^ 2 * y ^ 2 * (-1 + 4 * s ^ 2 * x ^ 2)) ^ 2 +
      ((r - s / 4) * y + (1 / 50 : ℝ) * s ^ 2 * x * y * (-1 - 2 * s ^ 2 + 4 * s ^ 2 * x ^ 2)) ^ 2 =
        (r + s / 4) ^ 2 - y ^ 2 + (2 / 25 : ℝ) * s * x * y ^ 2 * H +
          (1 / 2500 : ℝ) * s ^ 4 * y ^ 2 * (1 - 4 * s ^ 2 * (1 - s ^ 2) * x ^ 2) := by
    dsimp [H]
    linear_combination
      ((10000*r^2 + 3200*r*s^4*x*y^2 + 5000*r*s + 64*s^8*x^4*y^2 -
        32*s^6*x^2*y^2 + 4*s^4*y^2 - 3200*s^3*x*y^2 + 625*s^2)/10000) * hxy -
      (y^2*(8*s^3*x*y^2 - 6*s^3*x + 2*s*x + 25)/25) * hrs
  rw [he]
  linarith

private theorem circle_complex_bound (r s : ℝ) (z : ℂ) (hr : 1 ≤ r)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hrs : r * s = 1) (hz : ‖z‖ = 1) :
    ‖(r : ℂ) * z + (1 / 4 : ℂ) * ((s : ℂ) * star z) +
      (1 / 100 : ℂ) * (((s : ℂ) * star z) ^ 2 - ((s : ℂ) * star z) ^ 4) -
      ((1 / 100 : ℝ) * (s ^ 2 - s ^ 4) : ℝ)‖ ≤ r + s / 4 := by
  have hxy : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hn := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz] at hn
    nlinarith
  let Z : ℂ := (r : ℂ) * z + (1 / 4 : ℂ) * ((s : ℂ) * star z) +
      (1 / 100 : ℂ) * (((s : ℂ) * star z) ^ 2 - ((s : ℂ) * star z) ^ 4) -
      ((1 / 100 : ℝ) * (s ^ 2 - s ^ 4) : ℝ)
  have hre : Z.re = (r + s / 4) * z.re +
      (1 / 50 : ℝ) * s ^ 2 * z.im ^ 2 * (-1 + 4 * s ^ 2 * z.re ^ 2) := by
    dsimp [Z]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_succ,
      pow_zero, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    norm_num
    linear_combination ((s^2-s^4*(z.re^2+z.im^2+1))/100) * hxy
  have him : Z.im = (r - s / 4) * z.im +
      (1 / 50 : ℝ) * s ^ 2 * z.re * z.im * (-1 - 2 * s ^ 2 + 4 * s ^ 2 * z.re ^ 2) := by
    dsimp [Z]
    simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_succ,
      pow_zero, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    norm_num
    linear_combination (-s^4*z.re*z.im/25) * hxy
  have hsq := circle_algebra_bound r s z.re z.im hs hs1 hrs hxy
  have hn : ‖Z‖ ^ 2 ≤ (r + s / 4) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    nlinarith [hsq]
  have ha : 0 ≤ r + s / 4 := by linarith
  change ‖Z‖ ≤ r + s / 4
  nlinarith [norm_nonneg Z]

private theorem circle_bound (r : ℝ) (w : ℂ) (hr : 1 ≤ r) (hw : ‖w‖ = r) :
    ‖w + (1 / 4 : ℂ) * w⁻¹ + (1 / 100 : ℂ) * (w⁻¹ ^ 2 - w⁻¹ ^ 4) -
      ((1 / 100 : ℝ) * (r⁻¹ ^ 2 - r⁻¹ ^ 4) : ℝ)‖ ≤ r + (1 / 4 : ℝ) * r⁻¹ := by
  have hrpos : 0 < r := by linarith
  have hrnz : r ≠ 0 := ne_of_gt hrpos
  let z : ℂ := w / (r : ℂ)
  have hz : ‖z‖ = 1 := by simp [z, hw, Complex.norm_real, abs_of_pos hrpos, hrnz]
  have hwz : w = (r : ℂ) * z := by
    dsimp [z]
    field_simp [(by exact_mod_cast hrnz : (r : ℂ) ≠ 0)]
  have hwi : w⁻¹ = ((r⁻¹ : ℝ) : ℂ) * star z := by
    rw [hwz, mul_inv_rev, Complex.inv_eq_conj hz]
    simp [mul_comm]
  have hs : 0 ≤ r⁻¹ := inv_nonneg.mpr (le_of_lt hrpos)
  have hs1 : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).mpr hr
  have hb := circle_complex_bound r r⁻¹ z hr hs hs1 (mul_inv_cancel₀ hrnz) hz
  rw [← hwz, ← hwi] at hb
  simpa [div_eq_mul_inv, mul_comm] using hb


private lemma endpoints : ψ 1 = (5/4:ℂ) ∧ ψ (-1) = (-5/4:ℂ) ∧
    ψ 2 = (3403/1600:ℂ) := by norm_num [ψ]

private lemma chebyshev_of_disc (E : Set ℂ)
    (hE : ∀ z ∈ E, ‖z‖ ≤ 5/4) (hp : (5/4:ℂ) ∈ E) (hm : (-5/4:ℂ) ∈ E) :
    IsChebyshev E 1 X := by
  refine ⟨monic_X, natDegree_X, ?_⟩
  intro q hq hd M hM z hz
  have hplus := hM (5/4:ℂ) hp
  have hminus := hM (-5/4:ℂ) hm
  rw [hq.eq_X_add_C hd] at hplus hminus
  simp only [eval_add, eval_X, eval_C] at hplus hminus
  have htri := norm_sub_le ((5/4:ℂ)+q.coeff 0) ((-5/4:ℂ)+q.coeff 0)
  have he : (5/4:ℂ)+q.coeff 0-((-5/4:ℂ)+q.coeff 0) = (5/2:ℂ) := by ring
  rw [he] at htri
  norm_num at htri
  have hbound : (5/4:ℝ) ≤ M := by linarith
  simpa only [eval_X] using (hE z hz).trans hbound

private lemma compact_complement :
    (ψ '' {w | 1 < ‖w‖})ᶜ ⊆ closedBall 0 (5/4) ∧
      IsCompact (ψ '' {w | 1 < ‖w‖})ᶜ := by
  have hi : InjOn ψ {w | 1 < ‖w‖} :=
    Set.InjOn.mono (fun w hw => (show 1 ≤ ‖w‖ from le_of_lt hw)) injective_closed
  have ho := exterior_image_open differentiable_exterior hi
  have hc := closed_exterior_image
    (ψ := ψ) (fun u v hu hv => by
      have h := (exterior_bilipschitz hu hv).1
      nlinarith [norm_nonneg (u-v)])
    (fun u v hu hv => (exterior_bilipschitz hu hv).2)
  refine exterior_complement (by norm_num) ho hc ?_ ?_
  · intro w hw
    have hb := circle_bound 1 w (by norm_num) hw
    norm_num at hb
    simpa only [ψ, inv_pow] using hb
  · refine ⟨2, by norm_num, ?_⟩
    rw [endpoints.2.2]
    norm_num

/-- The monic Faber polynomial need not remain Chebyshev on exterior equipotentials. -/
theorem result : ¬ claim := by
  intro h
  have hK := compact_complement
  have hp : (5/4:ℂ) ∈ (ψ '' {w | 1 < ‖w‖})ᶜ := by
    rw [← endpoints.1]
    exact boundary_not_in_image injective_closed (by norm_num)
  have hm : (-5/4:ℂ) ∈ (ψ '' {w | 1 < ‖w‖})ᶜ := by
    rw [← endpoints.2.1]
    exact boundary_not_in_image injective_closed (by norm_num)
  have hcheb := chebyshev_of_disc _
    (fun z hz => by simpa only [mem_closedBall, dist_zero_right] using hK.1 hz) hp hm
  have hcon := h ψ 1 (by norm_num) differentiable_exterior
    (Set.InjOn.mono (fun w hw => (show 1 ≤ ‖w‖ from le_of_lt hw)) injective_closed) hK.2
    ⟨1, fun w hw => by
      simpa only [Complex.ofReal_one, one_mul] using
        (correction_bound (show 1 ≤ ‖w‖ by linarith)).trans (by norm_num : (27/100:ℝ) ≤ 1)⟩
    1 X (by norm_num) faber hcheb 2 (by norm_num)
  have hM : ∀ z ∈ ψ '' sphere 0 2,
      ‖(X - C (3/1600:ℂ)).eval z‖ ≤ (17/8:ℝ) := by
    rintro z ⟨w, hw, rfl⟩
    have hn : ‖w‖ = 2 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hb := circle_bound 2 w (by norm_num) hn
    norm_num at hb
    simpa only [eval_sub, eval_X, eval_C, ψ, inv_pow] using hb
  have hbad := hcon.2.2 (X - C (3/1600:ℂ)) (monic_X_sub_C _)
    (natDegree_X_sub_C _) (17/8) hM (ψ 2) ⟨2, by norm_num [mem_sphere], rfl⟩
  simp only [eval_X] at hbad
  rw [endpoints.2.2] at hbad
  norm_num at hbad

end D5.S3.Analytic.Chebyshev.FaberEquipotentialRefutation
