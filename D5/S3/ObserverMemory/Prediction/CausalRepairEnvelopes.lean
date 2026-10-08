/- GID: D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/CausalRepairEnvelopes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common causal upper and lower envelopes of finite response tables. -/

import D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace D5.S3.ObserverMemory.Prediction.CausalRepairEnvelopes
open D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion

private def prependPrefix {n : ℕ} {Y : Fin (n + 1) → Type*} {k : ℕ}
    (z : Y 0) (x : Prefix (fun t : Fin n => Y t.succ) k) : Prefix Y (k + 1) :=
  fun i => Fin.cases (motive := fun j => j.val < k + 1 → Y j)
    (fun _ => z) (fun j hj => x ⟨j, by simpa using hj⟩) i.1 i.2

private def dropPrefix {n : ℕ} {Y : Fin (n + 1) → Type*} {k : ℕ}
    (x : Prefix Y (k + 1)) : Prefix (fun t : Fin n => Y t.succ) k :=
  fun i => x ⟨i.1.succ, by simpa using i.2⟩

private def tailStrategy {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t) (z : Y 0) :
    (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ :=
  fun t x => f t.succ (prependPrefix z x)

private def joinStrategy {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (a : A 0)
    (g : Y 0 → (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ) :
    (t : Fin (n + 1)) → Prefix Y t.val → A t :=
  Fin.cases (fun _ => a) (fun t x => g (x ⟨0, by simp⟩) t (dropPrefix x))

private theorem tail_actions {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t)
    (z : Y 0) (y : (t : Fin n) → Y t.succ) :
    Fin.tail (feedbackActions f (Fin.cons z y)) = feedbackActions (tailStrategy f z) y := by
  funext t
  simp only [Fin.tail, feedbackActions, tailStrategy]
  congr 1
  funext i
  rcases i with ⟨i, hi⟩
  refine Fin.cases ?_ (fun j => ?_) i hi
  · intro h
    rfl
  · intro h
    rfl

private theorem join_tail {n : ℕ} {A Y : Fin (n + 1) → Type*}
    (a : A 0)
    (g : Y 0 → (t : Fin n) → Prefix (fun i : Fin n => Y i.succ) t.val → A t.succ)
    (z : Y 0) : tailStrategy (joinStrategy a g) z = g z := by
  funext t x
  simp only [tailStrategy, joinStrategy, Fin.cases_succ]
  congr 1

private theorem split_mass {n : ℕ} {A Y : Fin (n + 1) → Type*}
    [∀ t, Fintype (Y t)]
    (P : ((t : Fin (n + 1)) → Y t) → ((t : Fin (n + 1)) → A t) → ℝ)
    (f : (t : Fin (n + 1)) → Prefix Y t.val → A t) :
    feedbackMass P f = ∑ z : Y 0,
      feedbackMass (fun y a => P (Fin.cons z y)
        (Fin.cons (f 0 (fun i => (Nat.not_lt_zero i.1.val i.2).elim)) a))
        (tailStrategy f z) := by
  classical
  rw [feedbackMass, ← (Fin.consEquiv Y).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z hz
  rw [feedbackMass]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  change feedbackActions f (Fin.cons z y) = _
  funext t
  refine Fin.cases ?_ (fun j => ?_) t
  · simp only [feedbackActions, Fin.cons_zero]
    congr 1
    funext i
    exact (Nat.not_lt_zero i.1.val i.2).elim
  · exact congrFun (tail_actions f z y) j



/-- The upper and lower tables have strategy-independent masses attained by the original table. -/
private theorem common_causal_envelopes (T : ℕ) (A Y : Fin T → Type*)
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)]
    [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ) (hP : ∀ y a, 0 ≤ P y a) :
    ∃ (U L : (∀ t, Y t) → (∀ t, A t) → ℝ)
      (fu fl : (t : Fin T) → Prefix Y t.val → A t),
      (∀ y a, 0 ≤ L y a ∧ L y a ≤ P y a ∧ P y a ≤ U y a) ∧
      (∀ f, feedbackMass U f = feedbackMass P fu ∧
        feedbackMass L f = feedbackMass P fl) := by
  classical
  induction T with
  | zero =>
    let f : (t : Fin 0) → Prefix Y t.val → A t := fun t => Fin.elim0 t
    refine ⟨P, P, f, f, fun y a => ⟨hP y a, le_rfl, le_rfl⟩, ?_⟩
    intro g
    have hg : g = f := funext fun t => Fin.elim0 t
    subst g
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    let At := fun t : Fin n => A t.succ
    let Yt := fun t : Fin n => Y t.succ
    let R (a : A 0) (z : Y 0) (y : ∀ t, Yt t) (b : ∀ t, At t) : ℝ :=
      P (Fin.cons z y) (Fin.cons a b)
    have hR (a : A 0) (z : Y 0) : ∀ y b, 0 ≤ R a z y b :=
      fun y b => hP _ _
    choose U L gu gl hUL hmass using fun a z => ih At Yt (R a z) (hR a z)
    let um (a : A 0) (z : Y 0) := feedbackMass (R a z) (gu a z)
    let lm (a : A 0) (z : Y 0) := feedbackMass (R a z) (gl a z)
    let du (a : A 0) := ∑ z, um a z
    let dl (a : A 0) := ∑ z, lm a z
    obtain ⟨au, _, hau⟩ := Finset.exists_max_image Finset.univ du Finset.univ_nonempty
    obtain ⟨al, _, hal⟩ := Finset.exists_min_image Finset.univ dl Finset.univ_nonempty
    let u := du au
    let l := dl al
    have hdu (a : A 0) : du a ≤ u := hau a (Finset.mem_univ a)
    have hdl (a : A 0) : l ≤ dl a := hal a (Finset.mem_univ a)
    have hlm (a : A 0) (z : Y 0) : 0 ≤ lm a z :=
      Finset.sum_nonneg fun y _ => hR a z y _
    have hdl0 (a : A 0) : 0 ≤ dl a := Finset.sum_nonneg fun z _ => hlm a z
    have hl0 : 0 ≤ l := hdl0 al
    have hratio (a : A 0) : 0 ≤ l / dl a ∧ l / dl a ≤ 1 := by
      refine ⟨div_nonneg hl0 (hdl0 a), ?_⟩
      by_cases hd : dl a = 0
      · simp [hd]
      · exact (div_le_one₀ (lt_of_le_of_ne (hdl0 a) (Ne.symm hd))).mpr (hdl a)
    let ystar : ∀ t, Y t := fun t => Classical.choice (inferInstance : Nonempty (Y t))
    let Cplus (y : ∀ t, Y t) (a : ∀ t, A t) :=
      U (a 0) (y 0) (Fin.tail y) (Fin.tail a) +
        if y = ystar then u - du (a 0) else 0
    let Cminus (y : ∀ t, Y t) (a : ∀ t, A t) :=
      (l / dl (a 0)) * L (a 0) (y 0) (Fin.tail y) (Fin.tail a)
    let fu := joinStrategy au (gu au)
    let fl := joinStrategy al (gl al)
    have hfu : feedbackMass P fu = u := by
      rw [split_mass]
      simp only [fu, joinStrategy, Fin.cases_zero, join_tail]
      rfl
    have hfl : feedbackMass P fl = l := by
      rw [split_mass]
      simp only [fl, joinStrategy, Fin.cases_zero, join_tail]
      rfl
    refine ⟨Cplus, Cminus, fu, fl, ?_, ?_⟩
    · intro y a
      have hc := hUL (a 0) (y 0) (Fin.tail y) (Fin.tail a)
      have hr : R (a 0) (y 0) (Fin.tail y) (Fin.tail a) = P y a := by
        simp [R, Fin.cons_self_tail]
      rw [hr] at hc
      refine ⟨mul_nonneg (hratio (a 0)).1 hc.1, ?_, ?_⟩
      · exact le_trans (mul_le_of_le_one_left hc.1 (hratio (a 0)).2) hc.2.1
      · dsimp [Cplus]
        exact le_trans hc.2.2 (le_add_of_nonneg_right (by split_ifs <;> linarith [hdu (a 0)]))
    · intro f
      let a := f 0 (fun i => (Nat.not_lt_zero i.1.val i.2).elim)
      have ha (y : ∀ t, Y t) : feedbackActions f y 0 = a := by
        dsimp [feedbackActions, a]
        congr 1
        funext i
        exact (Nat.not_lt_zero i.1.val i.2).elim
      have hu : feedbackMass Cplus f = u := by
        rw [feedbackMass]
        simp only [Cplus, ha, Finset.sum_add_distrib]
        have hbase : (∑ y, U a (y 0) (Fin.tail y)
            (Fin.tail (feedbackActions f y))) = du a := by
          rw [← (Fin.consEquiv Y).sum_comp, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro z hz
          change (∑ y, U a z (Fin.tail (Fin.cons z y))
            (Fin.tail (feedbackActions f (Fin.cons z y)))) = um a z
          simp only [Fin.tail_cons, tail_actions]
          exact (hmass a z (tailStrategy f z)).1
        rw [hbase]
        simp
      have hl : feedbackMass Cminus f = l := by
        rw [feedbackMass]
        simp only [Cminus, ha, ← Finset.mul_sum]
        have hbase : (∑ y, L a (y 0) (Fin.tail y)
            (Fin.tail (feedbackActions f y))) = dl a := by
          rw [← (Fin.consEquiv Y).sum_comp, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro z hz
          change (∑ y, L a z (Fin.tail (Fin.cons z y))
            (Fin.tail (feedbackActions f (Fin.cons z y)))) = lm a z
          simp only [Fin.tail_cons, tail_actions]
          exact (hmass a z (tailStrategy f z)).2
        rw [hbase]
        by_cases hd : dl a = 0
        · have hlz : l = 0 := le_antisymm (hd ▸ hdl a) hl0
          simp [hd, hlz]
        · exact div_mul_cancel₀ l hd
      exact ⟨hu.trans hfu.symm, hl.trans hfl.symm⟩



/-- Maximum event-mass discrepancy over every deterministic causal strategy and every output event. -/
def feedbackDistance {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, Fintype (Y t)]
    (P Q : (∀ t, Y t) → (∀ t, A t) → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun v : ((t : Fin T) → Prefix Y t.val → A t) × Set (∀ t, Y t) =>
      |∑ y, if y ∈ v.2 then P y (feedbackActions v.1 y) -
        Q y (feedbackActions v.1 y) else 0|)

/-- Maximum failure of feedback normalization, without assuming the fed-back table is a law. -/
def feedbackDefect {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, Fintype (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun f : (t : Fin T) → Prefix Y t.val → A t => |feedbackMass P f - 1|)

private theorem normalization_lower_bound {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, Fintype (Y t)]
    (P Q : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (hQ : ∀ f, feedbackMass Q f = 1) : feedbackDefect P ≤ feedbackDistance P Q := by
  classical
  apply Finset.sup'_le
  intro f hf
  have h := Finset.le_sup' (s := Finset.univ)
    (f := fun v : ((t : Fin T) → Prefix Y t.val → A t) × Set (∀ t, Y t) =>
      |∑ y, if y ∈ v.2 then P y (feedbackActions v.1 y) -
        Q y (feedbackActions v.1 y) else 0|)
    (Finset.mem_univ (f, Set.univ))
  simp only [Set.mem_univ, if_true, Finset.sum_sub_distrib] at h
  change |feedbackMass P f - feedbackMass Q f| ≤ feedbackDistance P Q at h
  simpa only [hQ f] using h



/-- A normalized finite response table has a causal repair attaining its feedback defect,
and every causal probability table has at least that error. -/
theorem result (T : ℕ) (hT : 1 ≤ T) (A Y : Fin T → Type*)
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)]
    [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (hP : ∀ y a, 0 ≤ P y a) (hPsum : ∀ a, ∑ y, P y a = 1) :
    ∃ Q : (∀ t, Y t) → (∀ t, A t) → ℝ,
      (∀ y a, 0 ≤ Q y a) ∧
      (∀ a, ∑ y, Q y a = 1) ∧
      (∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
        (∀ i, i.val < n → a i = b i) → prefixMarginal Q n x a = prefixMarginal Q n x b) ∧
      feedbackDistance P Q = feedbackDefect P ∧
      (∀ R : (∀ t, Y t) → (∀ t, A t) → ℝ,
        (∀ y a, 0 ≤ R y a) → (∀ a, ∑ y, R y a = 1) →
        (∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
          (∀ i, i.val < n → a i = b i) → prefixMarginal R n x a = prefixMarginal R n x b) →
        feedbackDefect P ≤ feedbackDistance P R) := by
  classical
  obtain ⟨U, L, fu, fl, hUL, hmass⟩ := common_causal_envelopes T A Y P hP
  let u := feedbackMass P fu
  let l := feedbackMass P fl
  have hbounds (f : (t : Fin T) → Prefix Y t.val → A t) :
      l ≤ feedbackMass P f ∧ feedbackMass P f ≤ u := by
    constructor
    · change feedbackMass P fl ≤ feedbackMass P f
      rw [← (hmass f).2]
      exact Finset.sum_le_sum fun y _ => (hUL y (feedbackActions f y)).2.1
    · change feedbackMass P f ≤ feedbackMass P fu
      rw [← (hmass f).1]
      exact Finset.sum_le_sum fun y _ => (hUL y (feedbackActions f y)).2.2
  let a : ∀ t, A t := fun t => Classical.choice (inferInstance : Nonempty (A t))
  let fconst : (t : Fin T) → Prefix Y t.val → A t := fun t _ => a t
  have hconst : feedbackMass P fconst = 1 := hPsum a
  have hl1 : l ≤ 1 := hconst ▸ (hbounds fconst).1
  have hu1 : 1 ≤ u := hconst ▸ (hbounds fconst).2
  have hlu : l ≤ u := hl1.trans hu1
  have hdeltau : u - 1 ≤ feedbackDefect P :=
    (le_abs_self (u - 1)).trans (Finset.le_sup' (s := Finset.univ)
      (f := fun f => |feedbackMass P f - 1|) (Finset.mem_univ fu))
  have hdeltal : 1 - l ≤ feedbackDefect P := by
    have h := (neg_le_abs (l - 1)).trans (Finset.le_sup' (s := Finset.univ)
      (f := fun f => |feedbackMass P f - 1|) (Finset.mem_univ fl))
    linarith
  obtain ⟨θ, hθ0, hθ1, hθmass⟩ :
      ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ l + θ * (u - l) = 1 := by
    by_cases heq : u = l
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      have hl : l = 1 := le_antisymm hl1 (heq ▸ hu1)
      simp [hl]
    · have hpos : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne hlu (Ne.symm heq))
      refine ⟨(1 - l) / (u - l), div_nonneg (sub_nonneg.mpr hl1) hpos.le,
        (div_le_one₀ hpos).mpr (by linarith), ?_⟩
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      ring
  let Q (y : ∀ t, Y t) (a : ∀ t, A t) := L y a + θ * (U y a - L y a)
  have hQbounds (y : ∀ t, Y t) (a : ∀ t, A t) :
      L y a ≤ Q y a ∧ Q y a ≤ U y a := by
    have hgap : 0 ≤ U y a - L y a := sub_nonneg.mpr
      ((hUL y a).2.1.trans (hUL y a).2.2)
    dsimp [Q]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg hθ0 hgap)
    · have hmul := mul_le_of_le_one_left hgap hθ1
      linarith
  have hQ0 : ∀ y a, 0 ≤ Q y a := fun y a => (hUL y a).1.trans (hQbounds y a).1
  have hQmass (f : (t : Fin T) → Prefix Y t.val → A t) : feedbackMass Q f = 1 := by
    dsimp [feedbackMass, Q]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    change feedbackMass L f + θ * (feedbackMass U f - feedbackMass L f) = 1
    rw [(hmass f).1, (hmass f).2]
    exact hθmass
  have hQsum : ∀ a, ∑ y, Q y a = 1 := by
    intro a
    exact hQmass (fun t _ => a t)
  have hQcausal : ∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
      (∀ i, i.val < n → a i = b i) → prefixMarginal Q n x a = prefixMarginal Q n x b :=
    ((feedback_normalization_prefix_causality_sequential_kernels T hT A Y Q hQ0 hQsum).out 0 2).mp hQmass
  have herror : feedbackDistance P Q ≤ feedbackDefect P := by
    apply Finset.sup'_le
    rintro ⟨f, E⟩ hv
    let act := feedbackActions f
    have hupper : (∑ y, if y ∈ E then P y (act y) - Q y (act y) else 0) ≤ u - 1 := by
      calc
        _ ≤ ∑ y, U y (act y) - Q y (act y) := by
          apply Finset.sum_le_sum
          intro y hy
          split_ifs
          · exact sub_le_sub_right (hUL y (act y)).2.2 _
          · exact sub_nonneg.mpr (hQbounds y (act y)).2
        _ = u - 1 := by
          rw [Finset.sum_sub_distrib]
          change feedbackMass U f - feedbackMass Q f = u - 1
          rw [(hmass f).1, hQmass]
    have hlower : -(1 - l) ≤ (∑ y, if y ∈ E then P y (act y) - Q y (act y) else 0) := by
      have hneg : (∑ y, if y ∈ E then Q y (act y) - P y (act y) else 0) ≤ 1 - l := by
        calc
          _ ≤ ∑ y, Q y (act y) - L y (act y) := by
            apply Finset.sum_le_sum
            intro y hy
            split_ifs
            · exact sub_le_sub_left (hUL y (act y)).2.1 _
            · exact sub_nonneg.mpr (hQbounds y (act y)).1
          _ = 1 - l := by
            rw [Finset.sum_sub_distrib]
            change feedbackMass Q f - feedbackMass L f = 1 - l
            rw [hQmass, (hmass f).2]
      have heq : (∑ y, if y ∈ E then Q y (act y) - P y (act y) else 0) =
          -(∑ y, if y ∈ E then P y (act y) - Q y (act y) else 0) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        split_ifs <;> ring
      rw [heq] at hneg
      linarith
    exact (abs_le.mpr ⟨by linarith [hdeltal], hupper.trans hdeltau⟩)
  refine ⟨Q, hQ0, hQsum, hQcausal,
    le_antisymm herror (normalization_lower_bound P Q hQmass), ?_⟩
  intro R hR0 hRsum hRcausal
  exact normalization_lower_bound P R
    (((feedback_normalization_prefix_causality_sequential_kernels T hT A Y R hR0 hRsum).out 0 2).mpr hRcausal)

#print axioms result
end D5.S3.ObserverMemory.Prediction.CausalRepairEnvelopes
