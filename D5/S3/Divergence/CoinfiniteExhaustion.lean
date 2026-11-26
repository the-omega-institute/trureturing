/- GID: D5/S3/Divergence/CoinfiniteExhaustion
   generality: G
   mirror-B: D5/B/S3/Divergence/CoinfiniteExhaustion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatible exhaustions of one bit-erasure model have different KL-loss limits. -/

import D5.S3.Divergence.ProductAdditivity
import D5.S3.Entropy.Forgetting.CapacityMonotone
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Fixed-law restrictions and exhaustion dependence for the diagonal bit-erasure model
in the setting of Yang, *Quantum data processing equality*, arXiv:2609.33815v2, §V.3. -/

open scoped BigOperators Topology
open Filter

namespace D5.S3.Divergence.CoinfiniteExhaustion

open ClassicalDPI
open D5.S3.Entropy.MaxEntropy (shannonEntropy)
open D5.S3.Entropy.Forgetting.CapacityMonotone
  (pushforward deterministic_forgetting_entropy_capacity_monotone)

noncomputable section

/-- Index i represents the physical atom k = i + 1. -/
def pAtom (i : ℕ) : ℝ := (((i : ℝ) + 1) * ((i : ℝ) + 2))⁻¹

def qAtom (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

def pTail (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹

def qTail (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m

theorem pAtom_pos (i : ℕ) : 0 < pAtom i := by
  unfold pAtom
  positivity

theorem qAtom_pos (i : ℕ) : 0 < qAtom i := by
  unfold qAtom
  positivity

private theorem pAtom_add_tail (i : ℕ) : pAtom i + pTail (i + 1) = pTail i := by
  simp only [pAtom, pTail, Nat.cast_succ]
  have h₁ : (i : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (i : ℝ) + 2 ≠ 0 := by positivity
  rw [show (i : ℝ) + 1 + 1 = (i : ℝ) + 2 by ring]
  field_simp [h₁, h₂]
  ring

private theorem pPartial (m : ℕ) :
    (∑ i ∈ Finset.range m, pAtom i) = 1 - pTail m := by
  induction m with
  | zero => simp [pTail]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    linarith only [pAtom_add_tail m]

private theorem tendsto_pTail : Tendsto pTail atTop (𝓝 0) := by
  unfold pTail
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))

theorem pAtom_hasSum : HasSum pAtom 1 := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun i => (pAtom_pos i).le) _).2 ?_
  simpa only [pPartial, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_pTail

theorem pAtom_tail (m : ℕ) : (∑' i : ℕ, pAtom (i + m)) = pTail m := by
  have h := pAtom_hasSum.summable.sum_add_tsum_nat_add m
  rw [pPartial, pAtom_hasSum.tsum_eq] at h
  linarith only [h]

theorem qAtom_tail_hasSum (m : ℕ) : HasSum (fun i : ℕ => qAtom (i + m)) (qTail m) := by
  have h := hasSum_geometric_two.mul_left ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ))
  convert h using 1
  · funext i
    simp only [qAtom, pow_succ, pow_add]
    ring
  · unfold qTail
    ring

theorem qAtom_hasSum : HasSum qAtom 1 := by
  simpa [qTail] using qAtom_tail_hasSum 0

/-- The same fair bit is retained at all fine cutoffs. -/
def fairBit (_ : Bool) : ℝ := 1 / 2

def fairLift {X : Type*} (f : X → ℝ) (x : X × Bool) : ℝ :=
  f x.1 * fairBit x.2

def sourceP : ℕ × Bool → ℝ := fairLift pAtom

def sourceQ : ℕ × Bool → ℝ := fairLift qAtom

private theorem fairLift_pos {X : Type*} {f : X → ℝ}
    (hf : ∀ x, 0 < f x) (x : X × Bool) : 0 < fairLift f x :=
  mul_pos (hf x.1) (by norm_num [fairBit])

private theorem fairLift_hasSum (f : ℕ → ℝ) (hf : HasSum f 1)
    (hpos : ∀ i, 0 < f i) : HasSum (fairLift f) 1 := by
  have hFiber (i : ℕ) : (∑' b : Bool, fairLift f (i, b)) = f i := by
    rw [tsum_fintype, Fintype.sum_bool]
    unfold fairLift fairBit
    ring
  have hsum : Summable (fairLift f) :=
    (summable_prod_of_nonneg (fun x => (fairLift_pos hpos x).le)).2
      ⟨fun _ => (hasSum_fintype _).summable, by simpa only [hFiber] using hf.summable⟩
  have htotal : (∑' x, fairLift f x) = 1 := by
    rw [hsum.tsum_prod]
    simpa only [hFiber] using hf.tsum_eq
  rw [← htotal]
  exact hsum.hasSum

theorem fixed_source_states :
    (∀ x, 0 < sourceP x) ∧ (∀ x, 0 < sourceQ x) ∧
      HasSum sourceP 1 ∧ HasSum sourceQ 1 :=
  ⟨fairLift_pos pAtom_pos, fairLift_pos qAtom_pos,
    fairLift_hasSum _ pAtom_hasSum pAtom_pos, fairLift_hasSum _ qAtom_hasSum qAtom_pos⟩

/-- The atoms at cutoff m consist of the first m singleton indices and one tail. -/
abbrev Cut (m : ℕ) := Option (Fin m)

def cutIndex (m i : ℕ) : Cut m :=
  if h : i < m then some ⟨i, h⟩ else none

private theorem cutIndex_eq_some_iff {m i : ℕ} (j : Fin m) :
    cutIndex m i = some j ↔ i = j.val := by
  by_cases hi : i < m
  · simp [cutIndex, hi, Fin.ext_iff]
  · have hne : i ≠ j.val := fun h => hi (h.symm ▸ j.isLt)
    simp [cutIndex, hi, hne]

private theorem cutIndex_eq_none_iff (m i : ℕ) :
    cutIndex m i = none ↔ m ≤ i := by
  by_cases hi : i < m
  · simp [cutIndex, hi, not_le.mpr hi]
  · simp [cutIndex, hi, Nat.le_of_not_gt hi]

/-- Give each atom the mass of its fiber in the fixed countable law. -/
def cutMass (f : ℕ → ℝ) (m : ℕ) : Cut m → ℝ
  | none => ∑' i : ℕ, f (i + m)
  | some j => f j.val

theorem cutMass_eq_restriction (f : ℕ → ℝ) (hf : Summable f)
    (m : ℕ) (x : Cut m) :
    (∑' i : ℕ, if cutIndex m i = x then f i else 0) = cutMass f m x := by
  cases x with
  | none =>
    simp only [cutIndex_eq_none_iff, cutMass]
    let g : ℕ → ℝ := fun i => if m ≤ i then f i else 0
    have hShift : (fun i : ℕ => g (i + m)) = fun i => f (i + m) := by
      funext i
      have hi : m ≤ i + m := by omega
      simp [g, hi]
    have hg : Summable g := by
      apply (summable_nat_add_iff m).1
      rw [hShift]
      exact (summable_nat_add_iff m).2 hf
    have hzeros : (∑ i ∈ Finset.range m, g i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [g, not_le.mpr (Finset.mem_range.mp hi)]
    change (∑' i, g i) = _
    rw [← hg.sum_add_tsum_nat_add m, hzeros, zero_add, hShift]
  | some j =>
    simp only [cutIndex_eq_some_iff, cutMass]
    rw [tsum_eq_single j.val (fun i hi => ite_eq_right hi), ite_eq_left rfl]

private theorem cutMass_sum {f : ℕ → ℝ} (hf : HasSum f 1) (m : ℕ) :
    (∑ x, cutMass f m x) = 1 := by
  simp only [Fintype.sum_option, cutMass, Fin.sum_univ_eq_sum_range]
  rw [add_comm, hf.summable.sum_add_tsum_nat_add m, hf.tsum_eq]

abbrev pCut : (m : ℕ) → Cut m → ℝ := cutMass pAtom
abbrev qCut : (m : ℕ) → Cut m → ℝ := cutMass qAtom

@[simp] theorem pCut_none (m : ℕ) : pCut m none = pTail m := pAtom_tail m

@[simp] theorem qCut_none (m : ℕ) : qCut m none = qTail m :=
  (qAtom_tail_hasSum m).tsum_eq

theorem pCut_pos (m : ℕ) (x : Cut m) : 0 < pCut m x := by
  cases x with
  | none => rw [pCut_none]; unfold pTail; positivity
  | some i => exact pAtom_pos i.val

theorem qCut_pos (m : ℕ) (x : Cut m) : 0 < qCut m x := by
  cases x with
  | none => rw [qCut_none]; unfold qTail; positivity
  | some i => exact qAtom_pos i.val

/-- Countable restriction of either source retains the actual bit on each fiber. -/
private theorem fairLift_cut_restriction (f : ℕ → ℝ) (hf : Summable f)
    (hpos : ∀ i, 0 < f i) (m : ℕ) (x : Cut m × Bool) :
    (∑' z : ℕ × Bool,
      if (cutIndex m z.1, z.2) = x then fairLift f z else 0) =
      fairLift (cutMass f m) x := by
  rcases x with ⟨j, b⟩
  let g : ℕ × Bool → ℝ :=
    fun z => if (cutIndex m z.1, z.2) = (j, b) then fairLift f z else 0
  have hFiber (i : ℕ) :
      (∑' c : Bool, g (i, c)) = (if cutIndex m i = j then f i else 0) * fairBit b := by
    rw [tsum_fintype, Fintype.sum_bool]
    by_cases h : cutIndex m i = j <;> cases b <;>
      simp [g, fairLift, h, Prod.mk.injEq]
  have hIndicator : Summable (fun i => if cutIndex m i = j then f i else 0) :=
    Summable.of_nonneg_of_le
      (fun i => by split_ifs <;> linarith only [(hpos i).le])
      (fun i => by split_ifs <;> linarith only [(hpos i).le]) hf
  have hg : Summable g :=
    (summable_prod_of_nonneg (fun z => by
      change 0 ≤ (if (cutIndex m z.1, z.2) = (j, b) then fairLift f z else 0)
      split_ifs
      · exact (fairLift_pos hpos z).le
      · exact le_rfl)).2
      ⟨fun _ => (hasSum_fintype _).summable, by
        simpa only [hFiber] using hIndicator.mul_right (fairBit b)⟩
  change (∑' z, g z) = _
  rw [hg.tsum_prod]
  simp only [hFiber, _root_.tsum_mul_right, cutMass_eq_restriction f hf, fairLift]

/-- Retain a coarse singleton and send every other fine atom to the coarse tail. -/
def partitionMap {a n : ℕ} (x : Cut a) : Cut n :=
  match x with
  | none => none
  | some j => cutIndex n j.val

theorem partitionMap_cutIndex {a n : ℕ} (han : n ≤ a) (i : ℕ) :
    partitionMap (a := a) (n := n) (cutIndex a i) = cutIndex n i := by
  by_cases hi : i < a
  · simp [cutIndex, hi, partitionMap]
  · have hn : ¬ i < n := fun h => hi (h.trans_le han)
    simp [cutIndex, hi, hn, partitionMap]

/-- An intermediate compatible cutoff does not change the coarse atom. -/
theorem partitionMap_comp {a m n : ℕ} (hnm : n ≤ m) (x : Cut a) :
    partitionMap (n := n) (partitionMap (n := m) x) = partitionMap (n := n) x := by
  cases x with
  | none => rfl
  | some j => exact partitionMap_cutIndex hnm j.val

theorem eventually_resolves_atom (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) (i : ℕ) :
    ∀ᶠ n in atTop, ∃ j : Fin (a n), j.val = i ∧ cutIndex (a n) i = some j := by
  filter_upwards [eventually_ge_atTop (i + 1)] with n hn
  have hi : i < a n := (Nat.lt_of_succ_le hn).trans_le (ha n)
  exact ⟨⟨i, hi⟩, rfl, (cutIndex_eq_some_iff ⟨i, hi⟩).2 rfl⟩

private theorem partitionMap_eq_some_iff {a n : ℕ} (han : n ≤ a)
    (j : Fin n) (x : Cut a) :
    partitionMap x = some j ↔ x = some ⟨j.val, j.isLt.trans_le han⟩ := by
  cases x with
  | none => simp [partitionMap]
  | some k => simp [partitionMap, cutIndex_eq_some_iff, Fin.ext_iff]

private theorem partitionMap_surjective {a n : ℕ} (han : n ≤ a) :
    Function.Surjective (partitionMap (a := a) (n := n)) := by
  intro x
  cases x with
  | none => exact ⟨none, rfl⟩
  | some j =>
    exact ⟨_, (partitionMap_eq_some_iff han j _).2 rfl⟩

private theorem sum_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : X → ℝ) : (∑ y, pushforward f p y) = ∑ x, p x := by
  classical
  simp only [pushforward]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem cutMass_pushforward (f : ℕ → ℝ) (hf : HasSum f 1) {a n : ℕ}
    (han : n ≤ a) :
    pushforward partitionMap (cutMass f a) = cutMass f n := by
  classical
  have hSingle (j : Fin n) : pushforward partitionMap (cutMass f a) (some j) =
      cutMass f n (some j) := by
    simp only [pushforward, partitionMap_eq_some_iff han j, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, cutMass]
  have htotal :
      (∑ y : Cut n, pushforward partitionMap (cutMass f a) y) = ∑ y, cutMass f n y := by
    rw [sum_pushforward, cutMass_sum hf a, cutMass_sum hf n]
  simp only [Fintype.sum_option, hSingle] at htotal
  funext y
  cases y with
  | none => exact add_right_cancel htotal
  | some j => exact hSingle j

/-- The predual of the compatible inclusion is an actual deterministic stochastic matrix. -/
def partitionChannel (a n : ℕ) (x : Cut a × Bool) (y : Cut n) : ℝ :=
  if partitionMap x.1 = y then 1 else 0

theorem partitionChannel_stochastic (a n : ℕ) :
    (∀ x y, 0 ≤ partitionChannel a n x y) ∧
      ∀ x, ∑ y, partitionChannel a n x y = 1 := by
  constructor
  · intro x y
    unfold partitionChannel
    split_ifs <;> norm_num
  · intro x
    simp only [partitionChannel, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem channelOutput_fairLift {a n : ℕ} (p : Cut a → ℝ) :
    channelOutput (partitionChannel a n) (fairLift p) = pushforward partitionMap p := by
  classical
  funext y
  simp only [channelOutput, pushforward, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : partitionMap x = y <;> simp [partitionChannel, fairLift, fairBit, h]
  · ring

def fineP (a : ℕ) : Cut a × Bool → ℝ := fairLift (pCut a)
def fineQ (a : ℕ) : Cut a × Bool → ℝ := fairLift (qCut a)

theorem fine_states_are_restrictions (m : ℕ) (x : Cut m × Bool) :
    (∑' z : ℕ × Bool, if (cutIndex m z.1, z.2) = x then sourceP z else 0) = fineP m x ∧
    (∑' z : ℕ × Bool, if (cutIndex m z.1, z.2) = x then sourceQ z else 0) = fineQ m x :=
  ⟨fairLift_cut_restriction pAtom pAtom_hasSum.summable pAtom_pos m x,
    fairLift_cut_restriction qAtom qAtom_hasSum.summable qAtom_pos m x⟩

theorem partitionChannel_outputs {a n : ℕ} (han : n ≤ a) :
    channelOutput (partitionChannel a n) (fineP a) = pCut n ∧
      channelOutput (partitionChannel a n) (fineQ a) = qCut n := by
  exact ⟨(channelOutput_fairLift _).trans (cutMass_pushforward _ pAtom_hasSum han),
    (channelOutput_fairLift _).trans (cutMass_pushforward _ qAtom_hasSum han)⟩

theorem finite_states (m : ℕ) :
    (∀ x, 0 < pCut m x) ∧ (∀ x, 0 < qCut m x) ∧
    (∀ x, 0 < fineP m x) ∧ (∀ x, 0 < fineQ m x) ∧
    (∑ x, pCut m x) = 1 ∧ (∑ x, qCut m x) = 1 ∧
    (∑ x, fineP m x) = 1 ∧ (∑ x, fineQ m x) = 1 := by
  have hsum (f : Cut m → ℝ) : (∑ x, fairLift f x) = ∑ x, f x := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Fintype.sum_bool]
    unfold fairLift fairBit
    ring
  exact ⟨pCut_pos m, qCut_pos m, fairLift_pos (pCut_pos m), fairLift_pos (qCut_pos m),
    cutMass_sum pAtom_hasSum m, cutMass_sum qAtom_hasSum m,
    (hsum _).trans (cutMass_sum pAtom_hasSum m),
    (hsum _).trans (cutMass_sum qAtom_hasSum m)⟩

private theorem kl_fairLift (m : ℕ) :
    klDivergence (fineP m) (fineQ m) = klDivergence (pCut m) (qCut m) := by
  have hbitSum : (∑ b : Bool, fairBit b) = 1 := by norm_num [Fintype.sum_bool, fairBit]
  have hbitPos (b : Bool) : 0 < fairBit b := by norm_num [fairBit]
  have hbitKL : klDivergence fairBit fairBit = 0 := by
    simp [klDivergence, fairBit]
  unfold fineP fineQ fairLift
  simpa only [hbitKL, add_zero] using
    ProductAdditivity.kl_divergence_product_additive
      (pCut m) (qCut m) fairBit fairBit (cutMass_sum pAtom_hasSum m) hbitSum
      (pCut_pos m) (qCut_pos m) hbitPos hbitPos

/-- The truncated first moment of the physical first coordinate. -/
private def crossMoment (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, pAtom i * ((i : ℝ) + 1)) + (m : ℝ) * pTail m

private theorem crossMoment_succ (m : ℕ) :
    crossMoment (m + 1) = crossMoment m + pTail m := by
  simp only [crossMoment, Finset.sum_range_succ, Nat.cast_succ]
  have h := pAtom_add_tail m
  have hm := congrArg (fun x : ℝ => (m : ℝ) * x) h
  nlinarith only [h, hm]

private theorem crossMoment_eq_harmonic (m : ℕ) : crossMoment m = (harmonic m : ℝ) := by
  induction m with
  | zero => simp [crossMoment]
  | succ m ih =>
    rw [crossMoment_succ, ih]
    simp [harmonic_succ, pTail]

private def exponent (m : ℕ) : Cut m → ℕ
  | none => m
  | some i => i.val + 1

private theorem log_qCut (m : ℕ) (x : Cut m) :
    Real.log (qCut m x) = -(exponent m x : ℝ) * Real.log 2 := by
  have hq : qCut m x = (1 / 2 : ℝ) ^ exponent m x := by
    cases x with
    | none => exact qCut_none m
    | some i => rfl
  rw [hq, Real.log_pow, Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_one]
  ring

private theorem sum_cut_exponent (m : ℕ) :
    (∑ x, pCut m x * (exponent m x : ℝ)) = crossMoment m := by
  rw [Fintype.sum_option, pCut_none]
  simp only [exponent, cutMass, Nat.cast_succ]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => pAtom i * ((i : ℝ) + 1)), crossMoment,
    mul_comm (pTail m), add_comm]

theorem kl_cut (m : ℕ) :
    klDivergence (pCut m) (qCut m) =
      Real.log 2 * (harmonic m : ℝ) - shannonEntropy (pCut m) := by
  calc
    klDivergence (pCut m) (qCut m) =
        ∑ x, (Real.log 2 * (pCut m x * (exponent m x : ℝ)) -
          Real.negMulLog (pCut m x)) := by
      unfold klDivergence
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.log_div (pCut_pos m x).ne' (qCut_pos m x).ne', log_qCut]
      unfold Real.negMulLog
      ring
    _ = Real.log 2 * (harmonic m : ℝ) - shannonEntropy (pCut m) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cut_exponent, crossMoment_eq_harmonic]
      rfl

theorem shannon_increase {a n : ℕ} (han : n ≤ a) :
    shannonEntropy (pCut n) ≤ shannonEntropy (pCut a) := by
  have h := (deterministic_forgetting_entropy_capacity_monotone
    (pCut a) (partitionMap (n := n))
    ⟨fun x => (pCut_pos a x).le, cutMass_sum pAtom_hasSum a⟩
    (partitionMap_surjective han)).1
  rwa [cutMass_pushforward _ pAtom_hasSum han] at h

/-- Fine input KL less the KL of the actual two channel outputs. -/
def loss (a n : ℕ) : ℝ :=
  klDivergence (fineP a) (fineQ a) -
    klDivergence (channelOutput (partitionChannel a n) (fineP a))
      (channelOutput (partitionChannel a n) (fineQ a))

theorem loss_exact {a n : ℕ} (han : n ≤ a) :
    loss a n =
      Real.log 2 * ((harmonic a : ℝ) - (harmonic n : ℝ)) -
        (shannonEntropy (pCut a) - shannonEntropy (pCut n)) := by
  have h := partitionChannel_outputs han
  rw [loss, h.1, h.2, kl_fairLift, kl_cut a, kl_cut n]
  ring

private theorem negMulLog_le_power {x : ℝ} (hx : 0 < x) :
    Real.negMulLog x ≤ 4 * x ^ (3 / 4 : ℝ) := by
  have hLog : -Real.log x ≤ x ^ (-(1 / 4 : ℝ)) / (1 / 4 : ℝ) := by
    have h := Real.neg_rpow_div_le_log hx.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith only [h]
  have hPower : x * x ^ (-(1 / 4 : ℝ)) = x ^ (3 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = 1 + -(1 / 4 : ℝ) by norm_num,
      Real.rpow_add hx, Real.rpow_one]
  calc
    Real.negMulLog x = x * (-Real.log x) := by unfold Real.negMulLog; ring
    _ ≤ x * (x ^ (-(1 / 4 : ℝ)) / (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hLog hx.le
    _ = 4 * (x * x ^ (-(1 / 4 : ℝ))) := by ring
    _ = 4 * x ^ (3 / 4 : ℝ) := by rw [hPower]

private theorem pAtom_le_power (i : ℕ) :
    pAtom i ≤ ((i : ℝ) + 1) ^ (-2 : ℝ) := by
  rw [Real.rpow_neg (by positivity),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pAtom]
  apply inv_anti₀ (by positivity)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem pAtom_shannon_summable : Summable (fun i => Real.negMulLog (pAtom i)) := by
  have hBase : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun i : ℕ => (i : ℝ) ^ (-(3 / 2 : ℝ))) 1).2
        (Real.summable_nat_rpow.mpr (by norm_num))
  have hNonneg (i : ℕ) : 0 ≤ Real.negMulLog (pAtom i) := by
    apply Real.negMulLog_nonneg (pAtom_pos i).le
    rw [← pAtom_hasSum.tsum_eq]
    exact pAtom_hasSum.summable.le_tsum i (fun j _ => (pAtom_pos j).le)
  refine Summable.of_nonneg_of_le hNonneg ?_ (hBase.mul_left 4)
  intro i
  calc
    Real.negMulLog (pAtom i) ≤ 4 * (pAtom i) ^ (3 / 4 : ℝ) :=
      negMulLog_le_power (pAtom_pos i)
    _ ≤ 4 * (((i : ℝ) + 1) ^ (-2 : ℝ)) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (pAtom_pos i).le (pAtom_le_power i) (by norm_num)) (by norm_num)
    _ = 4 * ((i : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 2
      norm_num

theorem tendsto_cut_shannon :
    Tendsto (fun m => shannonEntropy (pCut m)) atTop
      (𝓝 (∑' i : ℕ, Real.negMulLog (pAtom i))) := by
  have hTail : Tendsto (fun m => Real.negMulLog (pTail m)) atTop (𝓝 0) := by
    change Tendsto (Real.negMulLog ∘ pTail) atTop (𝓝 0)
    simpa only [Real.negMulLog_zero] using
      (Real.continuous_negMulLog.continuousAt.tendsto.comp tendsto_pTail)
  have hEntropy (m : ℕ) : shannonEntropy (pCut m) = Real.negMulLog (pTail m) +
      ∑ i ∈ Finset.range m, Real.negMulLog (pAtom i) := by
    rw [shannonEntropy, Fintype.sum_option, pCut_none]
    change Real.negMulLog (pTail m) + (∑ i : Fin m, Real.negMulLog (pAtom i.val)) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => Real.negMulLog (pAtom i))]
  simpa only [hEntropy, zero_add] using hTail.add pAtom_shannon_summable.hasSum.tendsto_sum_nat

private theorem fine_tendsto_atTop (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) :
    Tendsto a atTop atTop :=
  tendsto_atTop_mono ha tendsto_id

private theorem harmonic_log_ratio_error (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) :
    Tendsto (fun n : ℕ =>
      ((harmonic (a n) : ℝ) - (harmonic n : ℝ)) - Real.log ((a n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
  have h := (Real.tendsto_harmonic_sub_log.comp (fine_tendsto_atTop a ha)).sub
    Real.tendsto_harmonic_sub_log
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnPos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have haPos : (0 : ℝ) < (a n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (hn.trans (ha n)))
  change (harmonic (a n) : ℝ) - Real.log (a n) -
      ((harmonic n : ℝ) - Real.log n) =
    ((harmonic (a n) : ℝ) - (harmonic n : ℝ)) - Real.log ((a n : ℝ) / (n : ℝ))
  rw [Real.log_div haPos.ne' hnPos.ne']
  ring

/-- The residual tends to zero along every compatible fine-cutoff sequence. -/
theorem tendsto_loss_sub_log_ratio (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) :
    Tendsto (fun n : ℕ => loss (a n) n - Real.log 2 * Real.log ((a n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
  have hShannon : Tendsto
      (fun n => shannonEntropy (pCut (a n)) - shannonEntropy (pCut n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (tendsto_cut_shannon.comp (fine_tendsto_atTop a ha)).sub tendsto_cut_shannon
  have h := ((harmonic_log_ratio_error a ha).const_mul (Real.log 2)).sub hShannon
  rw [mul_zero, sub_self] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp only
    rw [loss_exact (ha n)]
    ring

theorem tendsto_loss_of_ratio (a : ℕ → ℕ) (ha : ∀ n, n ≤ a n) {R : ℝ}
    (hR : Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun n => loss (a n) n) atTop (𝓝 (Real.log 2 * Real.log R)) := by
  have hOne : (1 : ℝ) ≤ R := by
    apply ge_of_tendsto hR
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnPos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    exact (le_div_iff₀ hnPos).2 (by simpa only [one_mul] using (Nat.cast_le.mpr (ha n) :
      (n : ℝ) ≤ (a n : ℝ)))
  have hLog := (hR.log (ne_of_gt (lt_of_lt_of_le zero_lt_one hOne))).const_mul (Real.log 2)
  have h := (tendsto_loss_sub_log_ratio a ha).add hLog
  rw [zero_add] at h
  exact h.congr' (Filter.Eventually.of_forall fun n => sub_add_cancel _ _)

/-- The nested choices a = n and a = 2n have distinct limits for the same fixed model. -/
theorem nonunique_exhaustion_loss :
    Tendsto (fun n : ℕ => loss n n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => loss (2 * n) n) atTop (𝓝 (Real.log 2 * Real.log 2)) ∧
      0 < Real.log 2 * Real.log 2 := by
  refine ⟨?_, ?_, mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))⟩
  · apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
    exact Filter.Eventually.of_forall fun n => by simp [loss_exact (le_refl n)]
  · apply tendsto_loss_of_ratio (fun n => 2 * n) (fun n => by omega)
    apply (tendsto_const_nhds (x := (2 : ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnPos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    change (2 : ℝ) = ((2 * n : ℕ) : ℝ) / (n : ℝ)
    apply (eq_div_iff hnPos.ne').2
    norm_num [Nat.cast_mul]

/-- The finite losses do not admit a common limit over compatible nested exhaustions. -/
theorem no_common_exhaustion_limit :
    ¬ ∃ L : ℝ, ∀ a : ℕ → ℕ, Monotone a → (∀ n, n ≤ a n) →
      (∀ n m k, n ≤ m → m ≤ k → ∀ x : Cut (a k),
        partitionMap (n := a n) (partitionMap (n := a m) x) =
          partitionMap (n := a n) x) →
      (∀ n, (∀ x y, 0 ≤ partitionChannel (a n) n x y) ∧
        ∀ x, ∑ y, partitionChannel (a n) n x y = 1) →
      Tendsto (fun n => loss (a n) n) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  obtain ⟨hsame, hdouble, hpos⟩ := nonunique_exhaustion_loss
  have common (a : ℕ → ℕ) (hmono : Monotone a) (ha : ∀ n, n ≤ a n) :
      Tendsto (fun n => loss (a n) n) atTop (𝓝 L) :=
    hL a hmono ha (fun _ _ _ hnm _ x => partitionMap_comp (hmono hnm) x)
      (fun n => partitionChannel_stochastic (a n) n)
  have hzero : L = 0 :=
    tendsto_nhds_unique (common id monotone_id (fun n => le_rfl)) hsame
  have hpositive : L = Real.log 2 * Real.log 2 :=
    tendsto_nhds_unique
      (common (fun n => 2 * n) (fun _ _ h => Nat.mul_le_mul_left 2 h) (fun n => by omega)) hdouble
  linarith

end

end D5.S3.Divergence.CoinfiniteExhaustion
