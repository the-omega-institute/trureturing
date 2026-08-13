/- GID: D5/S3/RenyiDivergence/DataProcessingAboveOne
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/DataProcessingAboveOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove above-one Renyi data processing under absolute continuity and pin failure. -/

/- Library-search audit trail (2026-08-13):
   * Pinned mathlib searches covered `HolderConjugate`, `conjExponent`,
     `inner_le_Lp_mul_Lq_of_nonneg`, `rpow_le_rpow`, `rpow_mul`, `mul_rpow`,
     `zero_rpow`, and finite nonnegative sums. `Real.HolderConjugate.conjExponent`
     supplies the pair `alpha, alpha / (alpha - 1)`, and
     `Real.inner_le_Lp_mul_Lq_of_nonneg` supplies finite Holder. The proof also
     reuses `Real.rpow_le_rpow`, `Real.rpow_mul`, `Real.mul_rpow`, and
     `Real.zero_rpow` rather than reproving real-power facts.
   * A repository-wide Renyi declaration search found below-one data processing
     and its half-order specialization only. The frozen module also contains an
     unnamed order-two reversal example, but no above-one data-processing theorem.
   * The import closure is DataProcessing -> {Monotone,
     HellingerDataProcessing}; Monotone -> Basic; HellingerDataProcessing ->
     Hellinger; Hellinger -> Bhattacharyya; Basic -> Bhattacharyya;
     Bhattacharyya -> Metric; Metric -> Pinsker; Pinsker ->
     {GrandmotherTheorem, ZeroSupportDPI}; GrandmotherTheorem -> ClassicalDPI;
     ZeroSupportDPI -> ClassicalDPI; ClassicalDPI -> Mathlib. Every repository
     module in this closure has generality G; Mathlib is external.
-/

import D5.S3.RenyiDivergence.DataProcessing

namespace D5.S3.RenyiDivergence

open D5.S3.Divergence.ClassicalDPI

/-!
For `alpha > 1`, the Renyi prefactor is positive, so data processing requires
the power sum to decrease. Finite Holder uses the conjugate pair
`alpha, alpha / (alpha - 1)`. Neither input must be strictly positive. The
negative `q` exponent requires only discrete absolute continuity: wherever
`q` vanishes, `p` must also vanish. A zero output `q`-mass is then harmless:
channel nonnegativity and absolute continuity force the corresponding output
`p`-mass to vanish as well.
-/

/-- A nonnegative row-stochastic finite channel cannot increase Renyi divergence
at orders above one for nonnegative inputs when the left input is absolutely
continuous with respect to the right. Neither input is required to be normalized. -/
theorem renyi_divergence_channel_le_of_one_lt_of_ac
    {X Y : Type*} [Fintype X] [Fintype Y]
    (alpha : Real) (p q : X -> Real) (W : X -> Y -> Real)
    (halpha : 1 < alpha) (hp : forall x, 0 <= p x)
    (hq : forall x, 0 <= q x) (hac : forall x, q x = 0 -> p x = 0)
    (hW : (forall x y, 0 <= W x y) /\ forall x, ∑ y, W x y = 1) :
    renyiDivergence alpha (channelOutput W p) (channelOutput W q) <=
      renyiDivergence alpha p q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  classical
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have halpha_ne : alpha ≠ 0 := halpha_pos.ne'
  have halpha_sub_ne : alpha - 1 ≠ 0 := sub_ne_zero.mpr halpha.ne'
  by_cases hp_zero : forall x, p x = 0
  · have hOutputP : channelOutput W p = fun _ => 0 := by
      funext y
      simp [channelOutput, hp_zero]
    rw [hOutputP]
    simp [renyiDivergence, hp_zero, Real.zero_rpow halpha_ne]
  have hone_div_pos : 0 < 1 / alpha := one_div_pos.mpr halpha_pos
  have hratio_pos : 0 < (alpha - 1) / alpha :=
    div_pos (sub_pos.mpr halpha) halpha_pos
  have hHolder : alpha.HolderConjugate (alpha / (alpha - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent halpha).2 rfl
  have hOutputNonneg (r : X -> Real) (hr : forall x, 0 <= r x) (y : Y) :
      0 <= channelOutput W r y := by
    rw [channelOutput]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hr x) (hW.1 x y)
  have hPointwise (y : Y) :
      (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha) <=
        ∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) := by
    by_cases hqy : channelOutput W q y = 0
    · have hpWzero (x : X) : p x * W x y = 0 := by
        have hqWzero : q x * W x y = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun z _ => mul_nonneg (hq z) (hW.1 z y))).mp
            (by simpa [channelOutput] using hqy) x (Finset.mem_univ x)
        rcases mul_eq_zero.mp hqWzero with hqx | hWxy
        · rw [hac x hqx, zero_mul]
        · rw [hWxy, mul_zero]
      have hpy : channelOutput W p y = 0 := by
        simp [channelOutput, hpWzero]
      rw [hpy, hqy, Real.zero_rpow halpha_ne]
      simp only [zero_mul]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (hW.1 x y)
        (mul_nonneg (Real.rpow_nonneg (hp x) alpha)
          (Real.rpow_nonneg (hq x) (1 - alpha)))
    · have hqy_pos : 0 < channelOutput W q y :=
        lt_of_le_of_ne (hOutputNonneg q hq y) (Ne.symm hqy)
      let f : X -> Real := fun x =>
        (W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha))) ^ (1 / alpha)
      let g : X -> Real := fun x =>
        (W x y * q x) ^ ((alpha - 1) / alpha)
      have hf_nonneg (x : X) : 0 <= f x := by
        exact Real.rpow_nonneg
          (mul_nonneg (hW.1 x y) (mul_nonneg
            (Real.rpow_nonneg (hp x) alpha)
            (Real.rpow_nonneg (hq x) (1 - alpha)))) (1 / alpha)
      have hg_nonneg (x : X) : 0 <= g x := by
        exact Real.rpow_nonneg (mul_nonneg (hW.1 x y) (hq x))
          ((alpha - 1) / alpha)
      have hf_power (x : X) :
          (f x) ^ alpha = W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) := by
        dsimp [f]
        rw [← Real.rpow_mul (mul_nonneg (hW.1 x y) (mul_nonneg
              (Real.rpow_nonneg (hp x) alpha)
              (Real.rpow_nonneg (hq x) (1 - alpha)))),
          show (1 / alpha) * alpha = 1 by field_simp, Real.rpow_one]
      have hg_power (x : X) :
          (g x) ^ (alpha / (alpha - 1)) = W x y * q x := by
        dsimp [g]
        rw [← Real.rpow_mul (mul_nonneg (hW.1 x y) (hq x)),
          show ((alpha - 1) / alpha) * (alpha / (alpha - 1)) = 1 by field_simp,
          Real.rpow_one]
      have hfg (x : X) : f x * g x = p x * W x y := by
        by_cases hWx : W x y = 0
        · dsimp [f, g]
          rw [hWx]
          simp only [zero_mul]
          rw [Real.zero_rpow hone_div_pos.ne']
          simp
        have hWx_pos : 0 < W x y := lt_of_le_of_ne (hW.1 x y) (Ne.symm hWx)
        by_cases hpx : p x = 0
        · dsimp [f, g]
          rw [hpx, Real.zero_rpow halpha_ne]
          simp only [zero_mul, mul_zero]
          rw [Real.zero_rpow hone_div_pos.ne']
          simp
        have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
        have hqx_ne : q x ≠ 0 := by
          intro hqx
          exact hpx (hac x hqx)
        have hqx_pos : 0 < q x := lt_of_le_of_ne (hq x) (Ne.symm hqx_ne)
        have hpCollapse : (p x) ^ (alpha * (1 / alpha)) = p x := by
          rw [show alpha * (1 / alpha) = 1 by field_simp, Real.rpow_one]
        have hWCollapse :
            (W x y) ^ (1 / alpha) * (W x y) ^ ((alpha - 1) / alpha) = W x y := by
          rw [← Real.rpow_add hWx_pos,
            show 1 / alpha + (alpha - 1) / alpha = 1 by
              field_simp
              ring,
            Real.rpow_one]
        have hqCollapse :
            (q x) ^ ((1 - alpha) * (1 / alpha)) *
                (q x) ^ ((alpha - 1) / alpha) = 1 := by
          rw [← Real.rpow_add hqx_pos,
            show (1 - alpha) * (1 / alpha) + (alpha - 1) / alpha = 0 by ring,
            Real.rpow_zero]
        dsimp [f, g]
        rw [Real.mul_rpow hWx_pos.le (mul_nonneg
              (Real.rpow_nonneg (hp x) alpha)
              (Real.rpow_nonneg (hq x) (1 - alpha))),
          Real.mul_rpow (Real.rpow_nonneg (hp x) alpha)
            (Real.rpow_nonneg (hq x) (1 - alpha)),
          Real.mul_rpow hWx_pos.le (hq x)]
        rw [← Real.rpow_mul (hp x), ← Real.rpow_mul (hq x)]
        calc
          (W x y) ^ (1 / alpha) *
                ((p x) ^ (alpha * (1 / alpha)) *
                  (q x) ^ ((1 - alpha) * (1 / alpha))) *
              ((W x y) ^ ((alpha - 1) / alpha) *
                (q x) ^ ((alpha - 1) / alpha)) =
              (p x) ^ (alpha * (1 / alpha)) *
                ((W x y) ^ (1 / alpha) * (W x y) ^ ((alpha - 1) / alpha)) *
                ((q x) ^ ((1 - alpha) * (1 / alpha)) *
                  (q x) ^ ((alpha - 1) / alpha)) := by ring
          _ = p x * W x y := by rw [hpCollapse, hWCollapse, hqCollapse]; ring
      have hRaw := Real.inner_le_Lp_mul_Lq_of_nonneg
        (s := Finset.univ) (f := f) (g := g) hHolder
        (fun x _ => hf_nonneg x) (fun x _ => hg_nonneg x)
      simp_rw [hfg, hf_power, hg_power] at hRaw
      have hBeforeRaise : channelOutput W p y <=
          (∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha))) ^ (1 / alpha) *
            (channelOutput W q y) ^ ((alpha - 1) / alpha) := by
        simpa [channelOutput, mul_comm,
          show 1 / (alpha / (alpha - 1)) = (alpha - 1) / alpha by field_simp]
          using hRaw
      have hRaised := Real.rpow_le_rpow (hOutputNonneg p hp y) hBeforeRaise
        halpha_pos.le
      have hANonneg :
          0 <= ∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) :=
        Finset.sum_nonneg fun x _ => mul_nonneg (hW.1 x y)
          (mul_nonneg (Real.rpow_nonneg (hp x) alpha)
            (Real.rpow_nonneg (hq x) (1 - alpha)))
      have hQNonneg : 0 <= channelOutput W q y := hqy_pos.le
      have hRaised' :
          (channelOutput W p y) ^ alpha <=
            (∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha))) *
              (channelOutput W q y) ^ (alpha - 1) := by
        calc
          (channelOutput W p y) ^ alpha <=
              ((∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha))) ^
                  (1 / alpha) *
                (channelOutput W q y) ^ ((alpha - 1) / alpha)) ^ alpha := hRaised
          _ = (∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha))) *
                (channelOutput W q y) ^ (alpha - 1) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hANonneg (1 / alpha))
                (Real.rpow_nonneg hQNonneg ((alpha - 1) / alpha)),
              ← Real.rpow_mul hANonneg, ← Real.rpow_mul hQNonneg,
              show (1 / alpha) * alpha = 1 by field_simp,
              show ((alpha - 1) / alpha) * alpha = alpha - 1 by field_simp,
              Real.rpow_one]
      have hqfactor_pos : 0 < (channelOutput W q y) ^ (alpha - 1) :=
        Real.rpow_pos_of_pos hqy_pos (alpha - 1)
      have hRearranged :
            (channelOutput W p y) ^ alpha /
                (channelOutput W q y) ^ (alpha - 1) <=
              ∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) :=
        (div_le_iff₀ hqfactor_pos).2 hRaised'
      calc
        (channelOutput W p y) ^ alpha *
            (channelOutput W q y) ^ (1 - alpha) =
            (channelOutput W p y) ^ alpha /
              (channelOutput W q y) ^ (alpha - 1) := by
          rw [show 1 - alpha = -(alpha - 1) by ring,
            Real.rpow_neg hqy_pos.le]
          rfl
        _ <= ∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) :=
          hRearranged
  have hPowerSum :
      (∑ y, (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha)) <=
        ∑ x, (p x) ^ alpha * (q x) ^ (1 - alpha) := by
    calc
      (∑ y, (channelOutput W p y) ^ alpha *
          (channelOutput W q y) ^ (1 - alpha)) <=
          ∑ y, ∑ x, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) :=
        Finset.sum_le_sum fun y _ => hPointwise y
      _ = ∑ x, ∑ y, W x y * ((p x) ^ alpha * (q x) ^ (1 - alpha)) :=
        Finset.sum_comm
      _ = ∑ x, (p x) ^ alpha * (q x) ^ (1 - alpha) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, hW.2 x, one_mul]
  push Not at hp_zero
  rcases hp_zero with ⟨x, hpx_ne⟩
  have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx_ne)
  have hWsum_pos : 0 < ∑ y, W x y := by rw [hW.2 x]; norm_num
  rcases (Finset.sum_pos_iff_of_nonneg fun y _ => hW.1 x y).mp hWsum_pos with
    ⟨y, _, hWxy⟩
  have hOutputPPos : 0 < channelOutput W p y := by
    rw [channelOutput]
    apply Finset.sum_pos' fun z _ => mul_nonneg (hp z) (hW.1 z y)
    exact ⟨x, Finset.mem_univ x, mul_pos hpx hWxy⟩
  have hOutputQPos : 0 < channelOutput W q y := by
    have hqx_ne : q x ≠ 0 := by
      intro hqx
      exact hpx_ne (hac x hqx)
    have hqx_pos : 0 < q x := lt_of_le_of_ne (hq x) (Ne.symm hqx_ne)
    rw [channelOutput]
    apply Finset.sum_pos' fun z _ => mul_nonneg (hq z) (hW.1 z y)
    exact ⟨x, Finset.mem_univ x, mul_pos hqx_pos hWxy⟩
  have hOutputPowerSumPos :
      0 < ∑ y, (channelOutput W p y) ^ alpha *
        (channelOutput W q y) ^ (1 - alpha) := by
    apply Finset.sum_pos' fun z _ => mul_nonneg
      (Real.rpow_nonneg (hOutputNonneg p hp z) alpha)
      (Real.rpow_nonneg (hOutputNonneg q hq z) (1 - alpha))
    exact ⟨y, Finset.mem_univ y, mul_pos
      (Real.rpow_pos_of_pos hOutputPPos alpha)
      (Real.rpow_pos_of_pos hOutputQPos (1 - alpha))⟩
  have hLog := Real.log_le_log hOutputPowerSumPos hPowerSum
  rw [renyiDivergence, renyiDivergence]
  exact mul_le_mul_of_nonneg_left hLog (by positivity)

/-- At order two, a constant Bool-to-Unit channel strictly increases the
totalized divergence from a uniform left mass to a right point mass. Thus
nonnegativity and normalization alone do not imply above-one data processing. -/
theorem renyi_divergence_data_processing_failure_order_two :
    ((forall _b : Bool, 0 <= (1 / 2 : Real)) /\
      ∑ _b : Bool, (1 / 2 : Real) = 1) /\
    ((forall b : Bool, 0 <= (if b then (1 : Real) else 0)) /\
      ∑ b : Bool, (if b then (1 : Real) else 0) = 1) /\
    ((forall x : Bool, forall y : Unit,
        0 <= (fun _x : Bool => fun _y : Unit => (1 : Real)) x y) /\
      forall x : Bool,
        ∑ y : Unit, (fun _x : Bool => fun _y : Unit => (1 : Real)) x y = 1) /\
    renyiDivergence 2
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun _b : Bool => (1 / 2 : Real)))
        (channelOutput (fun _x : Bool => fun _y : Unit => (1 : Real))
          (fun b : Bool => if b then (1 : Real) else 0)) >
      renyiDivergence 2
        (fun _b : Bool => (1 / 2 : Real))
        (fun b : Bool => if b then (1 : Real) else 0) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  constructor
  · exact ⟨fun _ => by norm_num, by norm_num [Fintype.sum_bool]⟩
  constructor
  · exact ⟨fun b => by cases b <;> norm_num,
      by norm_num [Fintype.sum_bool]⟩
  constructor
  · exact ⟨fun _ _ => by norm_num, fun _ => by simp⟩
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
  rw [hOutputP, hOutputQ]
  norm_num [renyiDivergence, Fintype.sum_bool]
  rw [show (1 / 4 : Real) = ((2 : Real) ^ 2)⁻¹ by norm_num,
    Real.log_inv, Real.log_pow]
  norm_num
  exact Real.log_pos (by norm_num)

#print axioms renyi_divergence_channel_le_of_one_lt_of_ac
#print axioms renyi_divergence_data_processing_failure_order_two

end D5.S3.RenyiDivergence
