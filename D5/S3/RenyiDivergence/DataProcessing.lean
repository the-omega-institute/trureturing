/- GID: D5/S3/RenyiDivergence/DataProcessing
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/DataProcessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove sub-unit Renyi data processing and recover the frozen half-order case. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms: `Renyi`, `Rényi`, `renyiDivergence`,
     `HolderConjugate`, `inner_le_Lp_mul_Lq_of_nonneg`, `data processing`, and
     `rpow_sum`. No probability-theory Renyi divergence or Renyi data-processing theorem was
     found. The finite real Holder inequality `Real.inner_le_Lp_mul_Lq_of_nonneg` and
     `Real.holderConjugate_one_div` provide the power-sum comparison used below.
   * A scan of all 694 `def`/`theorem`/`lemma` declarations below `D5/S3` found no Renyi
     data-processing theorem. The Renyi bucket contained exactly its seven prior theorems:
     five in `Basic` and two same-side order-monotonicity theorems in `Monotone`.
-/

import D5.S3.RenyiDivergence.Monotone
import D5.S3.TotalVariation.HellingerDataProcessing

namespace D5.S3.RenyiDivergence

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.HellingerDataProcessing

/-!
This module proves data processing for orders strictly between zero and one. The proof first
applies finite Holder pointwise at each output letter. This makes the Renyi power sum increase
under the channel; `Real.log` preserves that comparison, and the negative prefactor
`1 / (alpha - 1)` reverses it.

Positive input overlap is essential under the repository's totalization `Real.log 0 = 0`.
Without it, a disjoint pair can have divergence zero before a partially mixing channel and
positive divergence afterwards. Order one is likewise excluded because the literal definition
is zero there. Orders above one are not covered: with merely nonnegative masses, missing support
and zero powers can reverse the desired inequality. Stronger support hypotheses may recover that
range, but no such theorem is claimed here. Nonpositive orders are also excluded: the Holder
conjugates used below require both `alpha` and `1 - alpha` to be positive.
-/

/-- Corollary of the frozen affinity channel bound and frozen half-order identity: a channel
cannot increase half-order Renyi divergence when the input affinity is positive. This is not a
new proof of the half-order mathematics. Positive overlap is exactly what makes logarithm
monotonicity applicable despite the repository convention `Real.log 0 = 0`. -/
theorem renyi_divergence_one_half_channel_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hp : forall x, 0 <= p x) (hq : forall x, 0 <= q x)
    (hoverlap : Exists fun x => 0 < p x ∧ 0 < q x)
    (hW : (forall x y, 0 <= W x y) ∧ forall x, ∑ y, W x y = 1) :
    renyiDivergence (1 / 2) (channelOutput W p) (channelOutput W q) <=
      renyiDivergence (1 / 2) p q := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  have hOutputPNonneg (y : Y) : 0 <= channelOutput W p y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hW.1 x y)
  have hInputAffinityPos : 0 < bhattacharyya p q := by
    rw [bhattacharyya]
    apply Finset.sum_pos' fun x _ => Real.sqrt_nonneg _
    rcases hoverlap with ⟨x, hpx, hqx⟩
    exact ⟨x, Finset.mem_univ x, Real.sqrt_pos.2 (mul_pos hpx hqx)⟩
  have hAffinity := bhattacharyya_channel_le p q W hp hq hW
  have hLog := Real.log_le_log hInputAffinityPos hAffinity
  rw [renyi_divergence_one_half (channelOutput W p) (channelOutput W q)
      hOutputPNonneg,
    renyi_divergence_one_half p q hp]
  linarith

/-- A nonnegative row-stochastic finite channel cannot increase Renyi divergence at orders
strictly between zero and one, provided the input power sum is kept away from the totalized
logarithm at zero by positive support overlap. Neither input mass function is normalized. -/
theorem renyi_divergence_channel_le_of_lt_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    (alpha : Real) (p q : X -> Real) (W : X -> Y -> Real)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hp : forall x, 0 <= p x) (hq : forall x, 0 <= q x)
    (hoverlap : Exists fun x => 0 < p x ∧ 0 < q x)
    (hW : (forall x y, 0 <= W x y) ∧ forall x, ∑ y, W x y = 1) :
    renyiDivergence alpha (channelOutput W p) (channelOutput W q) <=
      renyiDivergence alpha p q := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  classical
  have hOneSubAlpha : 0 < 1 - alpha := sub_pos.mpr halpha.2
  have hAlphaNe : alpha ≠ 0 := halpha.1.ne'
  have hOneSubAlphaNe : 1 - alpha ≠ 0 := hOneSubAlpha.ne'
  have hHolder : (1 / alpha).HolderConjugate (1 / (1 - alpha)) :=
    Real.holderConjugate_one_div halpha.1 hOneSubAlpha (by ring)
  have hPointwise (y : Y) :
      (∑ x, (p x * W x y) ^ alpha * (q x * W x y) ^ (1 - alpha)) <=
        (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha) := by
    have hCollapseP (x : X) :
        ((p x * W x y) ^ alpha) ^ (1 / alpha) = p x * W x y := by
      rw [← Real.rpow_mul (mul_nonneg (hp x) (hW.1 x y)),
        show alpha * (1 / alpha) = 1 by field_simp, Real.rpow_one]
    have hCollapseQ (x : X) :
        ((q x * W x y) ^ (1 - alpha)) ^ (1 / (1 - alpha)) =
          q x * W x y := by
      rw [← Real.rpow_mul (mul_nonneg (hq x) (hW.1 x y)),
        show (1 - alpha) * (1 / (1 - alpha)) = 1 by field_simp,
        Real.rpow_one]
    have hRaw := Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := Finset.univ)
      (f := fun x => (p x * W x y) ^ alpha)
      (g := fun x => (q x * W x y) ^ (1 - alpha))
      hHolder
      (fun x _ => Real.rpow_nonneg (mul_nonneg (hp x) (hW.1 x y)) alpha)
      (fun x _ => Real.rpow_nonneg (mul_nonneg (hq x) (hW.1 x y)) (1 - alpha))
    simp_rw [hCollapseP, hCollapseQ] at hRaw
    simpa [
      show 1 / (1 / alpha) = alpha by field_simp,
      show 1 / (1 / (1 - alpha)) = 1 - alpha by field_simp,
      channelOutput] using hRaw
  have hPowerSum :
      (∑ x, (p x) ^ alpha * (q x) ^ (1 - alpha)) <=
        ∑ y, (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha) := by
    calc
      (∑ x, (p x) ^ alpha * (q x) ^ (1 - alpha)) =
          ∑ x, ∑ y, ((p x) ^ alpha * (q x) ^ (1 - alpha)) * W x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum, hW.2 x, mul_one]
      _ = ∑ y, ∑ x, ((p x) ^ alpha * (q x) ^ (1 - alpha)) * W x y :=
        Finset.sum_comm
      _ = ∑ y, ∑ x, (p x * W x y) ^ alpha *
          (q x * W x y) ^ (1 - alpha) := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        symm
        calc
          (p x * W x y) ^ alpha * (q x * W x y) ^ (1 - alpha) =
              ((p x) ^ alpha * (W x y) ^ alpha) *
                ((q x) ^ (1 - alpha) * (W x y) ^ (1 - alpha)) := by
            rw [Real.mul_rpow (hp x) (hW.1 x y),
              Real.mul_rpow (hq x) (hW.1 x y)]
          _ = ((p x) ^ alpha * (q x) ^ (1 - alpha)) *
              ((W x y) ^ alpha * (W x y) ^ (1 - alpha)) := by ring
          _ = ((p x) ^ alpha * (q x) ^ (1 - alpha)) *
              (W x y) ^ (alpha + (1 - alpha)) := by
            rw [Real.rpow_add' (hW.1 x y) (by norm_num)]
          _ = ((p x) ^ alpha * (q x) ^ (1 - alpha)) * W x y := by
            rw [show alpha + (1 - alpha) = 1 by ring, Real.rpow_one]
      _ <= ∑ y, (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha) := by
        apply Finset.sum_le_sum
        intro y _
        exact hPointwise y
  have hInputPowerSumPos :
      0 < ∑ x, (p x) ^ alpha * (q x) ^ (1 - alpha) := by
    apply Finset.sum_pos' fun x _ => mul_nonneg
      (Real.rpow_nonneg (hp x) alpha)
      (Real.rpow_nonneg (hq x) (1 - alpha))
    rcases hoverlap with ⟨x, hpx, hqx⟩
    exact ⟨x, Finset.mem_univ x, mul_pos
      (Real.rpow_pos_of_pos hpx alpha)
      (Real.rpow_pos_of_pos hqx (1 - alpha))⟩
  have hLog := Real.log_le_log hInputPowerSumPos hPowerSum
  have hPrefactorNonpos : 1 / (alpha - 1) <= 0 :=
    div_nonpos_of_nonneg_of_nonpos zero_le_one (sub_nonpos.mpr halpha.2.le)
  rw [renyiDivergence, renyiDivergence]
  exact mul_le_mul_of_nonpos_left hLog hPrefactorNonpos

/- Specializing the general theorem to one half yields exactly the proposition proved by the
frozen-material corollary. Both terms are checked here against that single statement. -/
example {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X -> Real) (W : X -> Y -> Real)
    (hp : forall x, 0 <= p x) (hq : forall x, 0 <= q x)
    (hoverlap : Exists fun x => 0 < p x ∧ 0 < q x)
    (hW : (forall x y, 0 <= W x y) ∧ forall x, ∑ y, W x y = 1) :
    (renyiDivergence (1 / 2) (channelOutput W p) (channelOutput W q) <=
        renyiDivergence (1 / 2) p q) ∧
      (renyiDivergence (1 / 2) (channelOutput W p) (channelOutput W q) <=
        renyiDivergence (1 / 2) p q) := by
  constructor
  · exact renyi_divergence_one_half_channel_le p q W hp hq hoverlap hW
  · exact renyi_divergence_channel_le_of_lt_one (1 / 2) p q W
      (by norm_num) hp hq hoverlap hW

/- The constant channel to `Unit` strictly contracts the half-order divergence between a Bool
point mass and the uniform mass function. -/
example :
    renyiDivergence (1 / 2)
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun b : Bool => if b then (1 : Real) else 0))
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun _b : Bool => (1 / 2 : Real))) <
      renyiDivergence (1 / 2)
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun _b : Bool => (1 / 2 : Real)) := by
  have hOutputP :
      channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun b : Bool => if b then (1 : Real) else 0) =
        fun _y : Unit => (1 : Real) := by
    funext y
    cases y
    norm_num [channelOutput, Fintype.sum_bool]
  have hOutputQ :
      channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun _b : Bool => (1 / 2 : Real)) =
        fun _y : Unit => (1 : Real) := by
    funext y
    cases y
    norm_num [channelOutput, Fintype.sum_bool]
  have hOutput :
      renyiDivergence (1 / 2) (fun _y : Unit => (1 : Real))
          (fun _y : Unit => (1 : Real)) = 0 := by
    exact renyi_divergence_self (1 / 2) (fun _y : Unit => (1 : Real))
      ⟨fun _ => by norm_num, by simp⟩
  have hInput :
      renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) = Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
      Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
    ring
  rw [hOutputP, hOutputQ, hOutput, hInput]
  exact Real.log_pos (by norm_num)

/- Positive overlap cannot be dropped. Disjoint Bool point masses have totalized half-order
divergence zero, while a channel that partly mixes one point produces the strict witness above. -/
example :
    ¬(renyiDivergence (1 / 2)
        (channelOutput
          (fun x y : Bool => if x then (if y then (1 : Real) else 0) else 1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0))
        (channelOutput
          (fun x y : Bool => if x then (if y then (1 : Real) else 0) else 1 / 2)
          (fun b : Bool => if b then 0 else (1 : Real))) <=
      renyiDivergence (1 / 2)
        (fun b : Bool => if b then (1 : Real) else 0)
        (fun b : Bool => if b then 0 else (1 : Real))) := by
  have hOutputP :
      channelOutput
          (fun x y : Bool => if x then (if y then (1 : Real) else 0) else 1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0) =
        fun b : Bool => if b then (1 : Real) else 0 := by
    funext y
    cases y <;> norm_num [channelOutput, Fintype.sum_bool]
  have hOutputQ :
      channelOutput
          (fun x y : Bool => if x then (if y then (1 : Real) else 0) else 1 / 2)
          (fun b : Bool => if b then 0 else (1 : Real)) =
        fun _b : Bool => (1 / 2 : Real) := by
    funext y
    cases y <;> norm_num [channelOutput, Fintype.sum_bool]
  have hMixed :
      renyiDivergence (1 / 2)
          (fun b : Bool => if b then (1 : Real) else 0)
          (fun _b : Bool => (1 / 2 : Real)) = Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [Real.log_rpow (by norm_num : (0 : Real) < 1 / 2),
      Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
    ring
  rw [hOutputP, hOutputQ, hMixed,
    renyi_divergence_disjoint_support_flattening_witness]
  exact not_le_of_gt (Real.log_pos (by norm_num))

/- Above order one, positive overlap alone is still insufficient: the totalized missing-support
term makes the uniform-versus-point-mass input negative at order two, while the constant channel
to `Unit` makes the two outputs equal and hence gives zero. -/
example :
    ¬(renyiDivergence 2
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun _b : Bool => (1 / 2 : Real)))
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun b : Bool => if b then (1 : Real) else 0)) <=
      renyiDivergence 2
        (fun _b : Bool => (1 / 2 : Real))
        (fun b : Bool => if b then (1 : Real) else 0)) := by
  have hOutputP :
      channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun _b : Bool => (1 / 2 : Real)) =
        fun _y : Unit => (1 : Real) := by
    funext y
    cases y
    norm_num [channelOutput, Fintype.sum_bool]
  have hOutputQ :
      channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun b : Bool => if b then (1 : Real) else 0) =
        fun _y : Unit => (1 : Real) := by
    funext y
    cases y
    norm_num [channelOutput, Fintype.sum_bool]
  have hOutput :
      renyiDivergence 2 (fun _y : Unit => (1 : Real))
          (fun _y : Unit => (1 : Real)) = 0 := by
    exact renyi_divergence_self 2 (fun _y : Unit => (1 : Real))
      ⟨fun _ => by norm_num, by simp⟩
  have hInput :
      renyiDivergence 2
          (fun _b : Bool => (1 / 2 : Real))
          (fun b : Bool => if b then (1 : Real) else 0) = -2 * Real.log 2 := by
    norm_num [renyiDivergence, Fintype.sum_bool]
    rw [show (1 / 4 : Real) = ((2 : Real) ^ 2)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  rw [hOutputP, hOutputQ, hOutput, hInput]
  linarith [Real.log_pos (by norm_num : (1 : Real) < 2)]

#print axioms renyi_divergence_one_half_channel_le
#print axioms renyi_divergence_channel_le_of_lt_one

end D5.S3.RenyiDivergence
