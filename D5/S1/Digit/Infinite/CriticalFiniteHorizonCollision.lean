/- GID: D5/S1/Digit/Infinite/CriticalFiniteHorizonCollision
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/CriticalFiniteHorizonCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict critical collisions of actual finite sources at every finite horizon. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
import D5.S1.Digit.Infinite.SevenCycleSeparationRefutation
import Mathlib.Order.Interval.Set.ProjIcc

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.CriticalFiniteHorizonCollision

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.CriticalPrefixSeparation
open D5.S1.Digit.Infinite.OddColorThreeSource (shift_add golden_relations)
open D5.S1.Scale (embedding)
open D5.S0.Carrier (GoldenInt)
open Set Filter
open scoped Topology

local notation "yStar" => D5.S1.Digit.Infinite.SevenCycleCollisionData.referenceTail

private theorem root_interval (x : LegalDigits) : kappa x ∈ stateInterval false := by
  rw [← closed_observation_graph_realization.2.1 false]
  exact ⟨x, by simp [stateAddress], rfl⟩

private theorem contraction : 0 < g ∧ g < 1 ∧ 0 < lambda := by
  obtain ⟨ht, ht1, _, _, _⟩ := golden_relations
  exact ⟨pow_pos ht 3, pow_lt_one₀ ht.le ht1 (by decide),
    div_pos (sq_pos_of_pos ht) (by norm_num)⟩

private theorem prefix_bound (n : ℕ) (x y : LegalDigits)
    (hp : windowPrefix n x = windowPrefix n y) :
    |kappa x - kappa y| ≤ (2 + t) * g ^ n := by
  have hx := response_expansion x 0 n
  have hy := response_expansion y 0 n
  simp only [Nat.zero_add, Nat.mul_zero] at hx hy
  change kappa x = _ at hx
  change kappa y = _ at hy
  have hs : (∑ k ∈ Finset.range n, (-g) ^ k * offset (window x k)) =
      ∑ k ∈ Finset.range n, (-g) ^ k * offset (window y k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show window x k = window y k from congrFun hp ⟨k, Finset.mem_range.mp hk⟩]
  have he : kappa x - kappa y = (-g) ^ n *
      (kappa (bitShift x (3 * n)) - kappa (bitShift y (3 * n))) := by
    rw [hx, hy, hs]
    ring
  have hX := root_interval (bitShift x (3 * n))
  have hY := root_interval (bitShift y (3 * n))
  simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, mem_Icc] at hX hY
  rw [he, abs_mul, abs_pow, abs_neg, abs_of_pos contraction.1]
  have hb : |kappa (bitShift x (3 * n)) - kappa (bitShift y (3 * n))| ≤ 2 + t :=
    abs_le.mpr ⟨by linarith [hX.1, hY.2], by linarith [hX.2, hY.1]⟩
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (pow_nonneg contraction.1.le n)

private theorem finite_approximation (s : Bool) (x : LegalDigits)
    (hx : stateAddress s x) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : LegalDigits, stateAddress s y ∧ finiteTail y ∧
      windowPrefix n y = windowPrefix n x ∧ |kappa y - kappa x| < ε := by
  have hD : 0 < 2 + t := by linarith [golden_relations.1]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hD) contraction.2.1
  let m := n + k
  have hm : (2 + t) * g ^ m < ε := by
    have hmono : g ^ m ≤ g ^ k := pow_le_pow_of_le_one contraction.1.le
      contraction.2.1.le (by dsimp [m]; omega)
    have hh := (lt_div_iff₀ hD).mp hk
    nlinarith
  obtain ⟨y, hy, hp, ht⟩ := realize_tail m s x (fiveRun 0) hx (by simp [stateAddress, fiveRun])
  have hf : finiteTail y := by
    apply D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.finite_unshift y (3 * m)
    rw [ht]
    exact run_finite 0
  refine ⟨y, hy, hf, ?_, (prefix_bound m y x hp).trans_lt hm⟩
  funext j
  exact congrFun hp ⟨j.val, by have := j.isLt; dsimp [m]; omega⟩

private theorem cylinder_interval (s : Bool) (x : LegalDigits)
    (hx : stateAddress s x) (n : ℕ) :
    ∃ a b : ℝ, a < b ∧ a ∈ embedding.range ∧ b ∈ embedding.range ∧
      kappa '' {y : LegalDigits | stateAddress s y ∧ windowPrefix n y = windowPrefix n x} =
        Icc a b := by
  let C := ∑ k ∈ Finset.range n, (-g) ^ k * offset (window x k)
  let P := (-g) ^ n
  let U := if actualGuard s x n then t else 1 + t
  let A := C + P * (-1)
  let B := C + P * U
  have hU : -1 < U := by dsimp [U]; split <;> linarith [golden_relations.1]
  have hP : P ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr contraction.1.ne')
  have hAB : A ≠ B := by
    intro he
    have hh : P * ((-1 : ℝ) - U) = 0 := by dsimp [A, B] at he; linarith
    rcases mul_eq_zero.mp hh with hh | hh
    · exact hP hh
    · linarith
  have htR : t ∈ embedding.range := by
    refine ⟨⟨-1, 1⟩, ?_⟩
    simp [embedding, D5.S1.Digit.Infinite.SevenCycleOriginalGraph.golden_ratio_t]
  have hCR : C ∈ embedding.range := by
    obtain ⟨z, _, hp, hz⟩ := realize_tail n s x (fiveRun 0) hx (by simp [stateAddress, fiveRun])
    have hf : finiteTail z := by
      apply D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.finite_unshift z (3 * n)
      rw [hz]
      exact run_finite 0
    have ha := congrFun (affine_actual n x z hp) (0 : Fin (n + 1))
    have hzero : kappa (fiveRun 0) = 0 :=
      congrFun ((D5.S1.Digit.Infinite.CriticalPrefixSeparation.result 1 (by decide)).2.2.1.1) 0
    obtain ⟨v, hv⟩ := closed_observation_graph_realization.2.2.2.2.2.2.2.1 z hf
    refine ⟨v, ?_⟩
    simp only [response, affineResponse, Fin.val_zero, Nat.sub_zero,
      Nat.zero_add, hz, hzero, mul_zero, add_zero] at ha
    exact hv.symm.trans ha
  have hPR : P ∈ embedding.range :=
    embedding.range.pow_mem (embedding.range.neg_mem (embedding.range.pow_mem htR 3)) n
  have hUR : U ∈ embedding.range := by
    dsimp [U]
    split
    · exact htR
    · exact embedding.range.add_mem (embedding.range.one_mem) htR
  have hAR : A ∈ embedding.range := embedding.range.add_mem hCR
    (embedding.range.mul_mem hPR (embedding.range.neg_mem embedding.range.one_mem))
  have hBR : B ∈ embedding.range := embedding.range.add_mem hCR
    (embedding.range.mul_mem hPR hUR)
  have himage : kappa '' {y : LegalDigits | stateAddress s y ∧
      windowPrefix n y = windowPrefix n x} = (fun z : ℝ => C + P * z) '' Icc (-1) U := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hp⟩, rfl⟩
      have hg : actualGuard s y n = actualGuard s x n := by
        cases n with
        | zero => simp [actualGuard]
        | succ n =>
          have hh := congrArg outgoing (congrFun hp ⟨n, by omega⟩)
          simpa [windowPrefix, actualGuard, outgoing, window,
            D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift,
            show 3 * (n + 1) - 1 = 2 + 3 * n by omega] using hh
      have hs := tail_guard s y n hy
      rw [hg] at hs
      refine ⟨kappa (bitShift y (3 * n)), ?_, ?_⟩
      · change kappa (bitShift y (3 * n)) ∈ stateInterval (actualGuard s x n)
        rw [← closed_observation_graph_realization.2.1]
        exact ⟨_, hs, rfl⟩
      · have ha := congrFun (affine_actual n x y hp) (0 : Fin (n + 1))
        simpa [response, affineResponse, C, P, bitShift] using ha.symm
    · rintro ⟨z, hz, rfl⟩
      change z ∈ stateInterval (actualGuard s x n) at hz
      rw [← closed_observation_graph_realization.2.1] at hz
      obtain ⟨v, hv, hvz⟩ := hz
      obtain ⟨y, hy, hp, ht⟩ := realize_tail n s x v hx hv
      refine ⟨y, ⟨hy, hp⟩, ?_⟩
      have ha := congrFun (affine_actual n x y hp) (0 : Fin (n + 1))
      simp only [response, affineResponse, Fin.val_zero, Nat.mul_zero, Nat.sub_zero,
        Nat.zero_add, ht, hvz] at ha
      change kappa y = C + P * z at ha
      exact ha
  refine ⟨min A B, max A B, ?_, ?_, ?_, ?_⟩
  · exact min_lt_max.mpr hAB
  · rcases le_total A B with h | h
    · simpa only [min_eq_left h] using hAR
    · simpa only [min_eq_right h] using hBR
  · rcases le_total A B with h | h
    · simpa only [max_eq_right h] using hBR
    · simpa only [max_eq_left h] using hAR
  · rw [himage, ← uIcc_of_le hU.le]
    change ((fun z : ℝ => C + z) ∘ (fun z => P * z)) '' uIcc (-1) U = _
    rw [image_comp, image_const_mul_uIcc, image_const_add_uIcc]
    rfl

/-- Every guarded finite cylinder has distinct integral golden endpoints. The
coordinate yStar is interior to its cylinders, with finite sources on both sides. -/
theorem finite_cylinder_sides :
    (∀ (s : Bool) (x : LegalDigits), stateAddress s x → ∀ n : ℕ,
      ∃ a b : ℝ, a < b ∧ a ∈ embedding.range ∧ b ∈ embedding.range ∧
        kappa '' {y : LegalDigits | stateAddress s y ∧
          windowPrefix n y = windowPrefix n x} = Icc a b) ∧
    yStar ∈ Ioo (-1) t ∧ yStar ∉ embedding.range ∧
    (∀ (x : LegalDigits), stateAddress true x → kappa x = yStar →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      ∃ lo hi : LegalDigits,
        stateAddress true lo ∧ stateAddress true hi ∧ finiteTail lo ∧ finiteTail hi ∧
        windowPrefix n lo = windowPrefix n x ∧ windowPrefix n hi = windowPrefix n x ∧
        yStar - ε < kappa lo ∧ kappa lo < yStar ∧
        yStar < kappa hi ∧ kappa hi < yStar + ε) := by
  have hI : yStar ∈ Ioo (-1) t := by
    dsimp [D5.S1.Digit.Infinite.SevenCycleCollisionData.referenceTail]
    constructor <;> linarith [golden_relations.1]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hscalar, _, _⟩ :=
    D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.complete_closed_graph_common_tail_width
  obtain ⟨tau, u, v, _, htau, hnot, _⟩ := hscalar
  have hn : yStar ∉ embedding.range := by
    rintro ⟨z, hz⟩
    apply hnot
    refine ⟨z, ?_⟩
    rw [htau]
    simpa only [D5.S1.Digit.Infinite.SevenCycleCollisionData.referenceTail,
      sub_eq_add_neg, add_comm] using hz.symm
  refine ⟨cylinder_interval, hI, hn, ?_⟩
  intro x hx hxv n ε hε
  obtain ⟨a, b, hab, ha, hb, himage⟩ := cylinder_interval true x hx n
  have hmem : yStar ∈ Icc a b := by
    rw [← himage]
    exact ⟨x, ⟨hx, rfl⟩, hxv⟩
  have hleft : a < yStar := lt_of_le_of_ne hmem.1 (fun he => hn (he ▸ ha))
  have hright : yStar < b := lt_of_le_of_ne hmem.2 (fun he => hn (he.symm ▸ hb))
  let ρ := min ε (min (yStar - a) (b - yStar)) / 4
  have hρ : 0 < ρ := div_pos (lt_min hε (lt_min (sub_pos.mpr hleft)
    (sub_pos.mpr hright))) (by norm_num)
  have hρε : 4 * ρ ≤ ε := by
    have hh := min_le_left ε (min (yStar - a) (b - yStar))
    dsimp [ρ]
    linarith
  have hρa : 4 * ρ ≤ yStar - a := by
    have hh := (min_le_right ε (min (yStar - a) (b - yStar))).trans
      (min_le_left (yStar - a) (b - yStar))
    dsimp [ρ]
    linarith
  have hρb : 4 * ρ ≤ b - yStar := by
    have hh := (min_le_right ε (min (yStar - a) (b - yStar))).trans
      (min_le_right (yStar - a) (b - yStar))
    dsimp [ρ]
    linarith
  have hL : yStar - 2 * ρ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hR : yStar + 2 * ρ ∈ Icc a b := ⟨by linarith, by linarith⟩
  rw [← himage] at hL hR
  obtain ⟨xL, ⟨hsL, hpL⟩, hvL⟩ := hL
  obtain ⟨xR, ⟨hsR, hpR⟩, hvR⟩ := hR
  obtain ⟨lo, hslo, hflo, hplo, hlo⟩ := finite_approximation true xL hsL n ρ hρ
  obtain ⟨hi, hshi, hfhi, hphi, hhi⟩ := finite_approximation true xR hsR n ρ hρ
  have hl := abs_lt.mp hlo
  have hr := abs_lt.mp hhi
  refine ⟨lo, hi, hslo, hshi, hflo, hfhi, hplo.trans hpL, hphi.trans hpR,
    ?_, ?_, ?_, ?_⟩ <;> linarith

set_option maxHeartbeats 1200000 in
-- The joint construction combines cylinder witnesses with every horizon coordinate.
/-- At every fixed finite horizon, different finite sources admit the same
critical color record using errors strictly below the critical radius. -/
theorem result (Q : ℝ → Fin 6) (hQ : instrument Q) (h : ℕ) :
    ∃ lo hi : LegalDigits, finiteTail lo ∧ finiteTail hi ∧
      window lo 0 = threeLabel ∧ window hi 0 = nullLabel ∧
      ∃ eL eR : Fin (h + 1) → ℝ, ∀ j : Fin (h + 1),
        |eL j| < lambda ∧ |eR j| < lambda ∧
        Q (max (-1) (min (1 + t) (response h lo j + eL j))) =
          Q (max (-1) (min (1 + t) (response h hi j + eR j))) := by
  obtain ⟨_, hI, _, hsides⟩ := finite_cylinder_sides
  have hLambda : 0 < lambda := contraction.2.2
  have hg : 0 < g := contraction.1
  have hcell := D5.S1.Digit.Infinite.SevenCycleActualRecords.cell_geometry 1
  have hgap : 0 < cuts 1 - cuts 0 := by
    simpa [cellLower, cellUpper] using sub_pos.mpr hcell.2.1
  have hD : 0 < 2 + t := by linarith [golden_relations.1]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (div_pos (mul_pos (show (0 : ℝ) < 2 by norm_num) hLambda) hD)
    contraction.2.1
  have hclose : (2 + t) * g ^ k < 2 * lambda := by
    have hh := (lt_div_iff₀ hD).mp hk
    linarith
  let n := k + h
  let ε := min (lambda / g) (2 * (cuts 1 - cuts 0) / g)
  have hε : 0 < ε := lt_min (div_pos hLambda hg) (div_pos (by linarith) hg)
  have hγε : g * ε ≤ lambda := by
    have hh := min_le_left (lambda / g) (2 * (cuts 1 - cuts 0) / g)
    have hh' := (le_div_iff₀ hg).mp hh
    simpa only [mul_comm] using hh'
  have hεgap : g * ε ≤ 2 * (cuts 1 - cuts 0) := by
    have hh := min_le_right (lambda / g) (2 * (cuts 1 - cuts 0) / g)
    have hh' := (le_div_iff₀ hg).mp hh
    simpa only [mul_comm] using hh'
  have hyI : yStar ∈ stateInterval true := ⟨hI.1.le, hI.2.le⟩
  rw [← closed_observation_graph_realization.2.1] at hyI
  obtain ⟨x, hx, hxv⟩ := hyI
  obtain ⟨ηL, ηR, hsL, hsR, hfL, hfR, hpL, hpR, hvL, hvL', hvR, hvR'⟩ :=
    hsides x hx hxv n ε hε
  let δL := yStar - kappa ηL
  let δR := kappa ηR - yStar
  have hδL : 0 < δL ∧ δL < ε := ⟨sub_pos.mpr hvL', by dsimp [δL]; linarith⟩
  have hδR : 0 < δR ∧ δR < ε := ⟨sub_pos.mpr hvR, by dsimp [δR]; linarith⟩
  have hgδL : 0 < g * δL ∧ g * δL < lambda ∧
      g * δL < 2 * (cuts 1 - cuts 0) :=
    ⟨mul_pos hg hδL.1, (mul_lt_mul_of_pos_left hδL.2 hg).trans_le hγε,
      (mul_lt_mul_of_pos_left hδL.2 hg).trans_le hεgap⟩
  have hgδR : 0 < g * δR ∧ g * δR < lambda ∧
      g * δR < 2 * (cuts 1 - cuts 0) :=
    ⟨mul_pos hg hδR.1, (mul_lt_mul_of_pos_left hδR.2 hg).trans_le hγε,
      (mul_lt_mul_of_pos_left hδR.2 hg).trans_le hεgap⟩
  obtain ⟨lo, hlo, _⟩ := closed_observation_graph_realization.2.2.2.1
    false threeLabel false ηL (by simp [lawful, outgoing, threeLabel]) (by simp [stateAddress])
  obtain ⟨hi, hhi, _⟩ := closed_observation_graph_realization.2.2.2.1
    false nullLabel false ηR (by simp [lawful, outgoing, nullLabel]) (by simp [stateAddress])
  have flo : finiteTail lo := by
    apply D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.finite_unshift lo 3
    change finiteTail (originalT lo)
    rw [hlo.2.2]
    exact hfL
  have fhi : finiteTail hi := by
    apply D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth.finite_unshift hi 3
    change finiteTail (originalT hi)
    rw [hhi.2.2]
    exact hfR
  have hbase : kappa lo = cuts 0 - lambda + g * δL ∧
      kappa hi = cuts 1 + lambda - g * δR := by
    have hL := (closed_observation_graph_realization.2.2.1 lo).1
    have hR := (closed_observation_graph_realization.2.2.1 hi).1
    rw [hlo.2.1, hlo.2.2] at hL
    rw [hhi.2.1, hhi.2.2] at hR
    obtain ⟨_, _, ht2, hgold, _⟩ := golden_relations
    dsimp [branch, offset, threeLabel, nullLabel] at hL hR
    norm_num at hL hR
    norm_num [δL, δR, D5.S1.Digit.Infinite.SevenCycleCollisionData.referenceTail, cuts, lambda]
    rw [hgold] at hL hR ⊢
    constructor <;> nlinarith only [ht2, hL, hR]
  have hfuture (j : Fin (h + 1)) (hj : j.val ≠ 0) :
      |response h lo j - response h hi j| < 2 * lambda := by
    have htail (ω η : LegalDigits) (ht : originalT ω = η) :
        bitShift ω (3 * j.val) = bitShift η (3 * (j.val - 1)) := by
      calc
        _ = bitShift (originalT ω) (3 * (j.val - 1)) := by
          simp only [originalT, shift_add]
          congr 1
          have := j.isLt
          omega
        _ = _ := congrArg (fun z => bitShift z (3 * (j.val - 1))) ht
    have hp : windowPrefix k (bitShift ηL (3 * (j.val - 1))) =
        windowPrefix k (bitShift ηR (3 * (j.val - 1))) := by
      funext i
      simp only [windowPrefix, shifted_window]
      have hin : j.val - 1 + i.val < n := by
        have := i.isLt
        have := j.isLt
        dsimp [n]
        omega
      exact (congrFun hpL ⟨j.val - 1 + i.val, hin⟩).trans
        (congrFun hpR ⟨j.val - 1 + i.val, hin⟩).symm
    dsimp only [response]
    rw [htail lo ηL hlo.2.2, htail hi ηR hhi.2.2]
    exact (prefix_bound k _ _ hp).trans_lt hclose
  let eL : Fin (h + 1) → ℝ := fun j => if j.val = 0 then lambda - g * δL / 2
    else (response h hi j - response h lo j) / 2
  let eR : Fin (h + 1) → ℝ := fun j => if j.val = 0 then -lambda + g * δR / 2
    else (response h lo j - response h hi j) / 2
  refine ⟨lo, hi, flo, fhi, hlo.2.1, hhi.2.1, eL, eR, ?_⟩
  intro j
  by_cases hj : j.val = 0
  · have hzL : response h lo j + eL j = cuts 0 + g * δL / 2 := by
      simp only [eL, if_pos hj, response, hj, Nat.mul_zero]
      change kappa lo + (lambda - g * δL / 2) = _
      linarith only [hbase.1]
    have hzR : response h hi j + eR j = cuts 1 - g * δR / 2 := by
      simp only [eR, if_pos hj, response, hj, Nat.mul_zero]
      change kappa hi + (-lambda + g * δR / 2) = _
      linarith only [hbase.2]
    have hinsideL : cuts 0 + g * δL / 2 ∈ Ioo (cellLower 1) (cellUpper 1) := by
      change cuts 0 < _ ∧ _ < cuts 1
      constructor <;> linarith [hgδL.1, hgδL.2.2]
    have hinsideR : cuts 1 - g * δR / 2 ∈ Ioo (cellLower 1) (cellUpper 1) := by
      change cuts 0 < _ ∧ _ < cuts 1
      constructor <;> linarith [hgδR.1, hgδR.2.2]
    have hclip (z : ℝ) (hz : z ∈ Ioo (cellLower 1) (cellUpper 1)) :
        max (-1) (min (1 + t) z) = z := by
      exact congrArg Subtype.val (Set.projIcc_of_mem
        (show (-1 : ℝ) ≤ 1 + t by linarith [golden_relations.1])
        ⟨hcell.1.trans hz.1.le, hz.2.le.trans hcell.2.2⟩)
    refine ⟨?_, ?_, ?_⟩
    · simp only [eL, if_pos hj]
      exact abs_lt.mpr ⟨by linarith [hgδL.2.1], by linarith [hgδL.1]⟩
    · simp only [eR, if_pos hj]
      exact abs_lt.mpr ⟨by linarith [hgδR.1], by linarith [hgδR.2.1]⟩
    · rw [hzL, hzR, hclip _ hinsideL, hclip _ hinsideR,
        D5.S1.Digit.Infinite.SevenCycleActualRecords.interior_owned Q hQ 1 _ hinsideL,
        D5.S1.Digit.Infinite.SevenCycleActualRecords.interior_owned Q hQ 1 _ hinsideR]
  · have hm := root_interval (bitShift lo (3 * j.val))
    have hp := root_interval (bitShift hi (3 * j.val))
    change -1 ≤ response h lo j ∧ response h lo j ≤ 1 + t at hm
    change -1 ≤ response h hi j ∧ response h hi j ≤ 1 + t at hp
    have hmid : max (-1) (min (1 + t) ((response h lo j + response h hi j) / 2)) =
        (response h lo j + response h hi j) / 2 := by
      exact congrArg Subtype.val (Set.projIcc_of_mem
        (show (-1 : ℝ) ≤ 1 + t by linarith [golden_relations.1])
        ⟨by linarith [hm.1, hp.1], by linarith [hm.2, hp.2]⟩)
    refine ⟨?_, ?_, ?_⟩
    · simp only [eL, if_neg hj]
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_sub_comm]
      exact (div_lt_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
        (by simpa only [mul_comm] using hfuture j hj)
    · simp only [eR, if_neg hj]
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      exact (div_lt_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
        (by simpa only [mul_comm] using hfuture j hj)
    · have heL : response h lo j + eL j = (response h lo j + response h hi j) / 2 := by
        simp only [eL, if_neg hj]
        ring
      have heR : response h hi j + eR j = (response h lo j + response h hi j) / 2 := by
        simp only [eR, if_neg hj]
        ring
      rw [heL, heR, hmid]


end D5.S1.Digit.Infinite.CriticalFiniteHorizonCollision
