/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedRootCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedRootCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A preconditioned derivative and its drift certify a unique zero in a closed ball. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting

namespace ChirpedRootCertificate

open Function Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

private theorem injective_of_norm_sub_id_le
    (A : E →L[ℝ] E) {k : ℝ} (hk : k < 1)
    (hA : ‖ContinuousLinearMap.id ℝ E - A‖ ≤ k) :
    Function.Injective A := by
  intro x y hxy
  have hz : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hb := (ContinuousLinearMap.id ℝ E - A).le_of_opNorm_le hA (x - y)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hz, sub_zero] at hb
  have hzero : ‖x - y‖ = 0 := by
    by_contra hn
    have hp := lt_of_le_of_ne (norm_nonneg (x - y)) (Ne.symm hn)
    exact (not_lt_of_ge hb) (by simpa using mul_lt_mul_of_pos_right hk hp)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- A derivative certificate at the center and a bound on its drift certify an actual,
unique zero in the closed ball. The preconditioner needs no separate invertibility proof. -/
theorem existsUnique_zero_closedBall
    (F : E → E) (DF : E → E →L[ℝ] E) (Y : E →L[ℝ] E)
    (c : E) (r δ L : ℝ) (k : NNReal)
    (hr : 0 ≤ r) (hL : 0 ≤ L) (hk : (k : ℝ) < 1)
    (hder : ∀ x ∈ closedBall c r, HasFDerivAt F (DF x) x)
    (hcenter : ‖ContinuousLinearMap.id ℝ E - Y.comp (DF c)‖ ≤ δ)
    (hdrift : ∀ x ∈ closedBall c r, ‖DF x - DF c‖ ≤ L * ‖x - c‖)
    (hcontract : δ + ‖Y‖ * L * r ≤ (k : ℝ))
    (hself : ‖Y (F c)‖ + (k : ℝ) * r ≤ r) :
    ∃! x, x ∈ closedBall c r ∧ F x = 0 := by
  let T (x : E) : E := x - Y (F x)
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hδ : δ ≤ (k : ℝ) := le_trans (le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (norm_nonneg Y) hL) hr)) hcontract
  have hcomp := injective_of_norm_sub_id_le (Y.comp (DF c)) hk (hcenter.trans hδ)
  have hDFc : Function.Injective (DF c).toLinearMap := fun x y h => hcomp (congrArg Y h)
  have hsurj : Function.Surjective (DF c).toLinearMap :=
    LinearMap.injective_iff_surjective.mp hDFc
  have hY : Function.Injective Y := by
    intro x y hxy
    obtain ⟨u, rfl⟩ := hsurj x
    obtain ⟨v, rfl⟩ := hsurj y
    exact congrArg (DF c).toLinearMap (hcomp hxy)
  have hD (x : E) (hx : x ∈ closedBall c r) :
      HasFDerivAt T (ContinuousLinearMap.id ℝ E - Y.comp (DF x)) x :=
    (hasFDerivAt_id x).sub (Y.hasFDerivAt.comp x (hder x hx))
  have hbound (x : E) (hx : x ∈ closedBall c r) :
      ‖ContinuousLinearMap.id ℝ E - Y.comp (DF x)‖ ≤ (k : ℝ) := by
    have hsplit : ContinuousLinearMap.id ℝ E - Y.comp (DF x) =
        (ContinuousLinearMap.id ℝ E - Y.comp (DF c)) - Y.comp (DF x - DF c) := by
      ext u
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    have hx' : ‖x - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
    rw [hsplit]
    calc
      _ ≤ ‖ContinuousLinearMap.id ℝ E - Y.comp (DF c)‖ + ‖Y.comp (DF x - DF c)‖ :=
        norm_sub_le _ _
      _ ≤ δ + ‖Y‖ * (L * ‖x - c‖) := add_le_add hcenter
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (hdrift x hx) (norm_nonneg Y)))
      _ ≤ δ + ‖Y‖ * L * r := by
        rw [mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hx' hL) (norm_nonneg Y))
      _ ≤ (k : ℝ) := hcontract
  have hdist (x y : E) (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
      dist (T x) (T y) ≤ (k : ℝ) * dist x y := by
    simp only [dist_eq_norm]
    exact (convex_closedBall c r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hD z hz).hasFDerivWithinAt) hbound hy hx
  have hTc : dist (T c) c = ‖Y (F c)‖ := by
    rw [dist_eq_norm]
    dsimp [T]
    rw [show c - Y (F c) - c = -(Y (F c)) by abel, norm_neg]
  have hmaps : MapsTo T (closedBall c r) (closedBall c r) := by
    intro x hx
    change dist (T x) c ≤ r
    calc
      _ ≤ dist (T x) (T c) + dist (T c) c := dist_triangle _ _ _
      _ ≤ (k : ℝ) * r + ‖Y (F c)‖ := by
        rw [hTc]
        exact add_le_add ((hdist x c hx hc).trans
          (mul_le_mul_of_nonneg_left hx k.coe_nonneg)) le_rfl
      _ ≤ r := by rw [add_comm]; exact hself
  have hK : ContractingWith k (hmaps.restrict T (closedBall c r) (closedBall c r)) := by
    refine ⟨by exact_mod_cast hk, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hdist x y x.2 y.2
  obtain ⟨x, hx, hfix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hK hc (edist_ne_top _ _)
  have hFx : F x = 0 := by
    apply hY
    have heq : x - Y (F x) = x := hfix
    rw [map_zero]
    exact sub_eq_self.mp heq
  refine ⟨x, ⟨hx, hFx⟩, fun y hy => ?_⟩
  have hTy : T y = y := by simp [T, hy.2]
  have hTx : T x = x := hfix
  have hh := hdist y x hy.1 hx
  rw [hTy, hTx] at hh
  apply dist_eq_zero.mp
  by_contra hne
  have hpos := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  exact (not_lt_of_ge hh) (by simpa using mul_lt_mul_of_pos_right hk hpos)

#print axioms existsUnique_zero_closedBall

end ChirpedRootCertificate
