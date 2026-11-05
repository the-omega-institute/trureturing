/- GID: D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual synchronized recurrent pairs force exact full-alphabet emissions and complete generated future laws. -/

import D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
import D5.S3.TotalVariation.HellingerDivergence
import Mathlib.Topology.Order.MonotoneConvergence

/-! Actual positive histories define the synchronized pair chain. Decreasing
finite-word affinities force exact generation on each terminal class. -/

namespace D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Bhattacharyya D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.HellingerDivergence
open scoped BigOperators Topology
open Finset Matrix Filter

noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {Z : Type*}

/-- Source modes are proof coordinates. Membership is witnessed by an actual,
positive finite history containing an acquired singleton. -/
def Synchronized (p q r : ℝ) (O : GeneratedObserver Z) (t : State × Z) : Prop :=
  ∃ h : List Visible, 0 < historyMass p q r h ∧
    (∃ y ∈ h, y ≠ B) ∧ sourceRun h = .pure t.1 ∧ O.toObserver.run h = t.2

abbrev ActualPair (p q r : ℝ) (O : GeneratedObserver Z) :=
  {t : State × Z // Synchronized p q r O t}

def nextPair (O : GeneratedObserver Z) (t : State × Z) (y : Visible) : State × Z :=
  (nextPure t.1 y, O.update t.2 y)

private lemma row_probability {p q r : ℝ} (hp : admissible p q r) (i : State) :
    (∀ y, 0 ≤ pureRow p q r i y) ∧ (∑ y, pureRow p q r i y) = 1 := by
  simpa only [pure_one_step] using one_step_probability _ (pure_probability hp i)

private lemma synchronized_history {p q r : ℝ} {O : GeneratedObserver Z}
    {t : State × Z} (ht : Synchronized p q r O t) :
    ∃ h : List Visible, h ≠ [] ∧ 0 < historyMass p q r h ∧
      acquiredPosterior p q r h = pureVector t.1 ∧ O.toObserver.run h = t.2 := by
  obtain ⟨h, hh, ⟨y, hy, _⟩, hs, hz⟩ := ht
  refine ⟨h, ?_, hh, ?_, hz⟩
  · intro he; simpa [he] using hy
  · rw [positive_history_invariant p q r h hh, hs, pure_profile]

private lemma every_singleton_history (p q r : ℝ) (O : GeneratedObserver Z)
    (h : List Visible) (hh : 0 < historyMass p q r h)
    (hs : ∃ y ∈ h, y ≠ B) :
    ∃ t : ActualPair p q r O, t.val.2 = O.toObserver.run h ∧
      acquiredPosterior p q r h = pureVector t.val.1 := by
  obtain ⟨y, hy, hyB⟩ := hs
  obtain ⟨u, v, he⟩ := List.mem_iff_append.mp hy
  have hy' : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
  obtain ⟨i, hi⟩ := first_singleton_and_all_later u v y hy'
  have hrun : sourceRun h = .pure i := by simpa only [he] using hi
  refine ⟨⟨(i, O.toObserver.run h), h, hh, ⟨y, hy, hyB⟩, hrun, rfl⟩, rfl, ?_⟩
  change acquiredPosterior p q r h = pureVector i
  rw [positive_history_invariant p q r h hh, hrun, pure_profile]

private lemma synchronized_next {p q r : ℝ} (O : GeneratedObserver Z)
    {t : State × Z} (ht : Synchronized p q r O t) (y : Visible)
    (hy : 0 < pureRow p q r t.1 y) : Synchronized p q r O (nextPair O t y) := by
  obtain ⟨h, hh, hsing, hs, hz⟩ := ht
  have hne : h ≠ [] := by
    obtain ⟨v, hv, _⟩ := hsing
    intro he; simpa [he] using hv
  have hpost : acquiredPosterior p q r h = pureVector t.1 := by
    rw [positive_history_invariant p q r h hh, hs, pure_profile]
  have hm := all_history_conditional_identity p q r h 1 (fun _ => y)
  have hw : List.ofFn (fun _ : Fin 1 => y) = [y] := by simp
  rw [hw, actual_pure_law h hne t.1 hpost, pure_one_step] at hm
  have hmass : 0 < historyMass p q r (h ++ [y]) := by
    have he := (div_eq_iff (ne_of_gt hh)).mp hm
    rw [he]
    exact mul_pos hy hh
  refine ⟨h ++ [y], hmass, ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hvB⟩ := hsing
    exact ⟨v, List.mem_append_left _ hv, hvB⟩
  · rw [source_run_snoc, hs]
    change sourceUpdate (.pure t.1) y = .pure (nextPure t.1 y)
    generalize hi : t.1 = i
    fin_cases i <;> fin_cases y <;>
      simp [sourceUpdate, nextPure, pureBSuccessor, singletonState, B]
  · rw [run_snoc]
    change O.update (O.toObserver.run h) y = O.update t.2 y
    rw [hz]

instance [Fintype Z] (p q r : ℝ) (O : GeneratedObserver Z) : Fintype (ActualPair p q r O) :=
  Fintype.ofFinite _

private lemma actual_nonempty (p q r : ℝ) (O : GeneratedObserver Z) : Nonempty (ActualPair p q r O) := by
  refine ⟨⟨(0, O.toObserver.run [0]), [0], ?_, ?_, rfl, rfl⟩⟩
  · rw [(acquired_witness_word_masses p q r).1]; norm_num
  · exact ⟨0, by simp, by decide⟩

/-- A zero source weight contributes no transition; its auxiliary endpoint is
chosen only to make the finite matrix total. The observer update itself is total. -/
def actualStep {p q r : ℝ} (O : GeneratedObserver Z)
    (t : ActualPair p q r O) (y : Visible) : ActualPair p q r O :=
  if hy : 0 < pureRow p q r t.val.1 y then
    ⟨nextPair O t.val y, synchronized_next O t.property y hy⟩ else t

def pairMatrix {p q r : ℝ} [Fintype Z] (O : GeneratedObserver Z) :
    Matrix (ActualPair p q r O) (ActualPair p q r O) ℝ :=
  fun t u => ∑ y : Visible, if actualStep O t y = u then pureRow p q r t.val.1 y else 0

private lemma pair_stochastic {p q r : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) : pairMatrix (p := p) (q := q) (r := r) O ∈
      rowStochastic ℝ (ActualPair p q r O) := by
  apply mem_rowStochastic_iff_sum.mpr
  refine ⟨?_, ?_⟩
  · intro t u
    exact sum_nonneg fun y _ => by
      split_ifs
      · exact (row_probability hp t.val.1).1 y
      · exact le_rfl
  · intro t
    unfold pairMatrix
    rw [sum_comm]
    simpa using (row_probability hp t.val.1).2

private lemma step_reach {p q r : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : ActualPair p q r O) (y : Visible)
    (hy : 0 < pureRow p q r t.val.1 y) : Reach (pairMatrix O) t (actualStep O t y) := by
  have hpos : 0 < pairMatrix O t (actualStep O t y) := by
    apply lt_of_lt_of_le hy
    apply le_trans _ (single_le_sum (f := fun v : Visible =>
      if actualStep O t v = actualStep O t y then pureRow p q r t.val.1 v else 0)
      (fun v _ => by split_ifs <;> first | exact (row_probability hp t.val.1).1 v | exact le_rfl)
      (mem_univ y))
    simp
  letI : Quiver (ActualPair p q r O) := (pairMatrix O).toQuiver
  exact ⟨Quiver.Path.nil.cons (PLift.up hpos)⟩

private def affinity (p q r : ℝ) (O : GeneratedObserver Z) (t : State × Z) (H : Nat) : ℝ :=
  bhattacharyya (pureLaw p q r t.1 H) (generatedLaw O.update O.row t.2 H)

private def coefficient (p q r : ℝ) (O : GeneratedObserver Z)
    (t : State × Z) (y : Visible) : ℝ := Real.sqrt (pureRow p q r t.1 y * O.row t.2 y)

private lemma affinity_zero (p q r : ℝ) (O : GeneratedObserver Z) (t : State × Z) :
    affinity p q r O t 0 = 1 := by
  simp [affinity, bhattacharyya, pure_zero, generatedLaw]

private lemma affinity_step {p q r : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : State × Z) (H : Nat) :
    affinity p q r O t (H+1) =
      ∑ y, coefficient p q r O t y * affinity p q r O (nextPair O t y) H := by
  unfold affinity bhattacharyya
  rw [sum_words_succ]
  apply sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro w _
  rw [pure_cons, generated_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change Real.sqrt ((pureRow p q r t.1 y * pureLaw p q r (nextPure t.1 y) H w) *
    (O.row t.2 y * generatedLaw O.update O.row (O.update t.2 y) H w)) = _
  rw [show (pureRow p q r t.1 y * pureLaw p q r (nextPure t.1 y) H w) *
      (O.row t.2 y * generatedLaw O.update O.row (O.update t.2 y) H w) =
    (pureRow p q r t.1 y * O.row t.2 y) *
      (pureLaw p q r (nextPure t.1 y) H w *
        generatedLaw O.update O.row (O.update t.2 y) H w) by ring]
  exact Real.sqrt_mul (mul_nonneg ((row_probability hp _).1 _) (O.row_nonneg _ _)) _

private lemma coefficient_sum_le {p q r : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : State × Z) : ∑ y, coefficient p q r O t y ≤ 1 :=
  bhattacharyya_le_one _ _ (row_probability hp t.1) ⟨O.row_nonneg t.2, O.row_sum t.2⟩

private lemma affinity_nonnegative (p q r : ℝ) (O : GeneratedObserver Z)
    (t : State × Z) (H : Nat) : 0 ≤ affinity p q r O t H :=
  sum_nonneg fun _ _ => Real.sqrt_nonneg _

private lemma affinity_antitone {p q r : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : State × Z) : Antitone (affinity p q r O t) := by
  apply antitone_nat_of_succ_le
  intro n
  have h : ∀ t : State × Z, affinity p q r O t (n+1) ≤ affinity p q r O t n := by
    induction n with
    | zero =>
      intro t
      rw [affinity_step hp, affinity_zero]
      simpa only [affinity_zero, mul_one] using coefficient_sum_le hp O t
    | succ n ih =>
      intro t
      rw [affinity_step hp, affinity_step hp]
      exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih _) (Real.sqrt_nonneg _)
  exact h t

private def limitingAffinity (p q r : ℝ) (O : GeneratedObserver Z) (t : State × Z) : ℝ :=
  ⨅ H : Nat, affinity p q r O t H

private lemma affinity_tendsto {p q r : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : State × Z) :
    Tendsto (affinity p q r O t) atTop (𝓝 (limitingAffinity p q r O t)) :=
  tendsto_atTop_ciInf (affinity_antitone hp O t)
    ⟨0, by rintro _ ⟨H, rfl⟩; exact affinity_nonnegative p q r O t H⟩

private lemma limiting_step {p q r : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (t : State × Z) :
    limitingAffinity p q r O t =
      ∑ y, coefficient p q r O t y * limitingAffinity p q r O (nextPair O t y) := by
  have hleft := (affinity_tendsto hp O t).comp (tendsto_add_atTop_nat 1)
  have hright := tendsto_finsetSum (univ : Finset Visible)
    (fun y _ => (affinity_tendsto hp O (nextPair O t y)).const_mul (coefficient p q r O t y))
  simp_rw [← affinity_step hp O t] at hright
  exact tendsto_nhds_unique hleft hright

lemma guarantee_accurate {p q r ε : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z)
    (hacc : ∀ h : List Visible, 0 < historyMass p q r h → ∀ H : Nat, 0 < H →
      totalVariation (actualFutureWordWeight p q r h H)
        (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ ε) :
    O.toObserver.Accurate p q r ε true := by
  have hε0 : 0 ≤ ε := (total_variation_nonneg _ _).trans
    (hacc [] (by rw [empty_history_mass]; norm_num) 1 (by omega))
  intro h hh _ H
  cases H with
  | zero =>
    have ha : actualFutureWordWeight p q r h 0 = fun _ => (1 : ℝ) := by
      funext w
      unfold actualFutureWordWeight
      split_ifs
      · norm_num [initialWordWeight, uniformPi, Fin.sum_univ_succ]
      · exact (posterior_probability hp h hh).2
    simpa [ha, GeneratedObserver.toObserver, generatedLaw, totalVariation] using hε0
  | succ H => exact hacc h hh (H+1) (by omega)

private lemma actual_limit_lower {p q r ε : ℝ} (hp : admissible p q r)
    (O : GeneratedObserver Z) (hacc : O.toObserver.Accurate p q r ε true)
    (t : ActualPair p q r O) : 1-ε ≤ limitingAffinity p q r O t.val := by
  obtain ⟨h, hne, hh, hpost, hz⟩ := synchronized_history t.property
  apply le_ciInf
  intro H
  have htv := hacc h hh (Or.inl rfl) H
  rw [actual_pure_law h hne t.val.1 hpost] at htv
  change totalVariation (pureLaw p q r t.val.1 H)
    (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ ε at htv
  rw [hz] at htv
  have he := hellinger_sq_eq_two_sub (pureLaw p q r t.val.1 H)
    (generatedLaw O.update O.row t.val.2 H) (pure_probability hp t.val.1 H)
    ⟨generated_nonnegative O.update O.row O.row_nonneg t.val.2 H,
      generated_sum O.update O.row O.row_sum t.val.2 H⟩
  have hl := hellinger_sq_div_two_le_total_variation
    (pureLaw p q r t.val.1 H) (generatedLaw O.update O.row t.val.2 H)
  rw [he] at hl
  dsimp [affinity]
  linarith

private lemma maximal_limit_row {p q r : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) (C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O))
    (t : ActualPair p q r O) (ht : t ∈ C.val)
    (hpos : 0 < limitingAffinity p q r O t.val)
    (hmax : ∀ u ∈ C.val, limitingAffinity p q r O u.val ≤ limitingAffinity p q r O t.val) :
    O.row t.val.2 = pureRow p q r t.val.1 ∧
      ∀ y, 0 < pureRow p q r t.val.1 y →
        limitingAffinity p q r O (nextPair O t.val y) = limitingAffinity p q r O t.val := by
  let M := limitingAffinity p q r O t.val
  let f := fun y => limitingAffinity p q r O (nextPair O t.val y)
  let d := coefficient p q r O t.val
  have hbound (y : Visible) : d y * f y ≤ d y * M := by
    by_cases hy : 0 < pureRow p q r t.val.1 y
    · have hu := (actual_structure (pairMatrix O) (pair_stochastic hp O)).class_closed
        C t ht (actualStep O t y) (step_reach hp O t y hy)
      have hv : (actualStep O t y).val = nextPair O t.val y := by
        simp only [actualStep, dite_eq_left hy]
      have hm := hmax _ hu
      rw [hv] at hm
      exact mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg _)
    · have hz : pureRow p q r t.val.1 y = 0 :=
        le_antisymm (le_of_not_gt hy) ((row_probability hp t.val.1).1 y)
      simp [d, coefficient, hz]
  have hfix : M = ∑ y, d y * f y := limiting_step hp O t.val
  have hsum : (∑ y, d y) = 1 := by
    have hle := coefficient_sum_le hp O t.val
    have hb := sum_le_sum (fun y (_ : y ∈ (univ : Finset Visible)) => hbound y)
    rw [← sum_mul] at hb
    dsimp only [M, d] at *
    nlinarith
  have heq : pureRow p q r t.val.1 = O.row t.val.2 := by
    apply (hellinger_sq_eq_zero_iff _ _ (row_probability hp t.val.1).1 (O.row_nonneg t.val.2)).mp
    rw [hellinger_sq_eq_two_sub _ _ (row_probability hp t.val.1)
      ⟨O.row_nonneg t.val.2, O.row_sum t.val.2⟩]
    change 2 * (1 - ∑ y, d y) = 0
    rw [hsum]; ring
  refine ⟨heq.symm, ?_⟩
  intro y hy
  have hn (v : Visible) : 0 ≤ d v * M - d v * f v := sub_nonneg.mpr (hbound v)
  have hz : (∑ v, (d v * M - d v * f v)) = 0 := by
    rw [sum_sub_distrib, ← sum_mul, hsum, one_mul, ← hfix, sub_self]
  have hterm := (sum_eq_zero_iff_of_nonneg (fun v _ => hn v)).mp hz y (mem_univ y)
  have hd : d y = pureRow p q r t.val.1 y := by
    dsimp [d, coefficient]
    rw [← heq]
    exact Real.sqrt_mul_self ((row_probability hp _).1 y)
  rw [hd] at hterm
  change f y = M
  nlinarith

private lemma class_rows_exact {p q r ε : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) (hε : ε < 1)
    (hacc : O.toObserver.Accurate p q r ε true)
    (C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O)) :
    ∀ t ∈ C.val, O.row t.val.2 = pureRow p q r t.val.1 := by
  have st := actual_structure (pairMatrix O) (pair_stochastic hp O)
  obtain ⟨m, hm, hmax⟩ := exists_max_image C.val
    (fun t => limitingAffinity p q r O t.val) (st.class_nonempty C)
  have hM : 0 < limitingAffinity p q r O m.val :=
    lt_of_lt_of_le (by linarith) (actual_limit_lower hp O hacc m)
  have at_max (t : ActualPair p q r O) (ht : t ∈ C.val)
      (he : limitingAffinity p q r O t.val = limitingAffinity p q r O m.val) :=
    maximal_limit_row hp O C t ht (he.symm ▸ hM)
      (fun u hu => (hmax u hu).trans_eq he.symm)
  have hstep (t u : ActualPair p q r O) (ht : t ∈ C.val)
      (he : limitingAffinity p q r O t.val = limitingAffinity p q r O m.val)
      (hK : 0 < pairMatrix O t u) :
      limitingAffinity p q r O u.val = limitingAffinity p q r O m.val := by
    obtain ⟨y, _, hy⟩ := (sum_pos_iff_of_nonneg (fun y _ => show
      0 ≤ (if actualStep O t y = u then pureRow p q r t.val.1 y else 0) by
      split_ifs <;> first | exact (row_probability hp _).1 _ | exact le_rfl)).mp hK
    split_ifs at hy with heq
    · have hv : (actualStep O t y).val = nextPair O t.val y := by
        simp only [actualStep, dite_eq_left hy]
      have hl := (at_max t ht he).2 y hy
      rw [← hv, heq] at hl
      exact hl.trans he
    · exact False.elim (lt_irrefl 0 hy)
  have hreach (t : ActualPair p q r O) (hr : Reach (pairMatrix O) m t) :
      limitingAffinity p q r O t.val = limitingAffinity p q r O m.val := by
    obtain ⟨path⟩ := hr
    induction path with
    | nil => rfl
    | @cons t u path edge ih =>
      exact hstep t u (st.class_closed C m hm t ⟨path⟩) ih edge.down
  intro t ht
  exact (at_max t ht (hreach t (st.class_communicates C m hm t ht))).1

private lemma class_profiles_exact {p q r : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) (C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O))
    (he : ∀ t ∈ C.val, O.row t.val.2 = pureRow p q r t.val.1) :
    ∀ t ∈ C.val, generatedLaw O.update O.row t.val.2 = pureLaw p q r t.val.1 := by
  have st := actual_structure (pairMatrix O) (pair_stochastic hp O)
  have hf (H : Nat) : ∀ t ∈ C.val, ∀ w : Fin H → Visible,
      generatedLaw O.update O.row t.val.2 H w = pureLaw p q r t.val.1 H w := by
    induction H with
    | zero => intro t ht w; simp [generatedLaw, pure_zero]
    | succ H ih =>
      intro t ht w
      rw [pure_cons]
      change O.row t.val.2 (w 0) *
        generatedLaw O.update O.row (O.update t.val.2 (w 0)) H (fun j => w j.succ) = _
      rw [he t ht]
      by_cases hz : pureRow p q r t.val.1 (w 0) = 0
      · simp [hz]
      · have hy : 0 < pureRow p q r t.val.1 (w 0) :=
          lt_of_le_of_ne ((row_probability hp _).1 _) (Ne.symm hz)
        have hu := st.class_closed C t ht (actualStep O t (w 0)) (step_reach hp O t (w 0) hy)
        have hv : (actualStep O t (w 0)).val = nextPair O t.val (w 0) := by
          simp only [actualStep, dite_eq_left hy]
        have hih := ih _ hu (fun j => w j.succ)
        rw [hv] at hih
        exact congrArg (fun v => pureRow p q r t.val.1 (w 0) * v) hih
  intro t ht
  funext H w
  exact hf H t ht w

private lemma class_all_modes {p q r : ℝ} [Fintype Z] (hp : admissible p q r)
    (O : GeneratedObserver Z) (C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O)) :
    ∀ i : State, ∃ t ∈ C.val, t.val.1 = i := by
  have st := actual_structure (pairMatrix O) (pair_stochastic hp O)
  let E := fun i : State => ∃ t ∈ C.val, t.val.1 = i
  have hmove (i : State) (hi : E i) (y : Visible) (hy : 0 < pureRow p q r i y) :
      E (nextPure i y) := by
    obtain ⟨t, ht, hti⟩ := hi
    have hy' : 0 < pureRow p q r t.val.1 y := by rwa [hti]
    refine ⟨actualStep O t y,
      st.class_closed C t ht _ (step_reach hp O t y hy'), ?_⟩
    simp only [actualStep, dite_eq_left hy']
    exact congrArg (fun j => nextPure j y) hti
  have hzero : E 0 := by
    obtain ⟨t, ht⟩ := st.class_nonempty C
    have hi : E t.val.1 := ⟨t, ht, rfl⟩
    generalize he : t.val.1 = i at hi
    fin_cases i
    · exact hi
    · simpa [nextPure, singletonState, B] using hmove 1 hi 0 (by simpa [pureRow] using hp.2.1)
    · have h1 : E 1 := by
        simpa [nextPure, singletonState, B] using hmove 2 hi 1 (by simpa [pureRow] using hp.2.1)
      simpa [nextPure, singletonState, B] using hmove 1 h1 0 (by simpa [pureRow] using hp.2.1)
    · simpa [nextPure, singletonState, B] using hmove 3 hi 0 (by simpa [pureRow] using hp.1)
    · simpa [nextPure, singletonState, B] using hmove 4 hi 0 (by simpa [pureRow] using hp.2.2.1)
  have h1 : E 1 := by
    simpa [nextPure, singletonState, B] using hmove 0 hzero 1 (by simpa [pureRow] using hp.1)
  intro i
  change E i
  fin_cases i
  · exact hzero
  · exact h1
  · simpa [nextPure, pureBSuccessor, B] using hmove 1 h1 B (by simpa [pureRow, B] using hp.1)
  · simpa [nextPure, singletonState, B] using hmove 0 hzero 3 (by simpa [pureRow] using hp.2.1)
  · simpa [nextPure, pureBSuccessor, B] using hmove 0 hzero B (by simpa [pureRow, B] using hp.2.2.1)

/-- Every actual synchronized recurrent class is exact. The guarantee is stated
only at positive horizons, with arbitrary real error strictly below one. -/
theorem recurrent_pair_rigidity {p q r ε : ℝ} [Fintype Z]
    (hp : admissible p q r) (O : GeneratedObserver Z) (hε : ε < 1)
    (hacc : ∀ h : List Visible, 0 < historyMass p q r h → ∀ H : Nat, 0 < H →
      totalVariation (actualFutureWordWeight p q r h H)
        (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ ε) :
    Nonempty (ActualPair p q r O) ∧
    (∀ h : List Visible, 0 < historyMass p q r h → (∃ y ∈ h, y ≠ B) →
      ∃ t : ActualPair p q r O, t.val.2 = O.toObserver.run h ∧
        acquiredPosterior p q r h = pureVector t.val.1) ∧
    (∀ t : ActualPair p q r O, ∀ y, 0 < pureRow p q r t.val.1 y →
      (actualStep O t y).val = nextPair O t.val y) ∧
    pairMatrix (p := p) (q := q) (r := r) O ∈ rowStochastic ℝ (ActualPair p q r O) ∧
    Nonempty (ClosedClass (pairMatrix (p := p) (q := q) (r := r) O)) ∧
    (∀ C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O),
      C.val.Nonempty ∧ IsIrreducible (restriction (pairMatrix O) C.val) ∧
      (∀ t ∈ C.val, ∀ u, Reach (pairMatrix O) t u → u ∈ C.val) ∧
      (∀ t ∈ C.val, O.row t.val.2 = pureRow p q r t.val.1) ∧
      (∀ t ∈ C.val, generatedLaw O.update O.row t.val.2 = pureLaw p q r t.val.1) ∧
      (∀ i : State, ∃ t ∈ C.val, t.val.1 = i)) ∧
    (∃ f : State → Z, Function.Injective f ∧ ∀ i,
      f i ∈ O.toObserver.Reached p q r ∧
      generatedLaw O.update O.row (f i) = pureLaw p q r i) := by
  have hactual := actual_nonempty p q r O
  have hK := pair_stochastic hp O
  have st := actual_structure (pairMatrix O) hK
  have hclasses := st.ambient_nonempty hactual
  have hAcc := guarantee_accurate hp O hacc
  have hrows := class_rows_exact hp O hε hAcc
  have hprofiles (C : ClosedClass (pairMatrix (p := p) (q := q) (r := r) O)) :=
    class_profiles_exact hp O C (hrows C)
  refine ⟨hactual, every_singleton_history p q r O, ?_, hK, hclasses, ?_, ?_⟩
  · intro t y hy
    simp only [actualStep, dite_eq_left hy]
  · intro C
    exact ⟨st.class_nonempty C, st.class_irreducible C, st.class_closed C,
      hrows C, hprofiles C, class_all_modes hp O C⟩
  · obtain ⟨C⟩ := hclasses
    choose t ht hi using class_all_modes hp O C
    let f : State → Z := fun i => (t i).val.2
    have hf (i : State) : generatedLaw O.update O.row (f i) = pureLaw p q r i := by
      simpa only [f, hi] using hprofiles C (t i) (ht i)
    refine ⟨f, ?_, fun i => ⟨?_, hf i⟩⟩
    · intro i j hij
      by_contra hne
      have he : pureLaw p q r i = pureLaw p q r j := by rw [← hf i, ← hf j, hij]
      have hsep := pure_pair_separation hp i j hne
      rw [profile_distance_eq_zero_of_eq he] at hsep
      exact (not_le_of_gt (kappa_positive hp)) hsep
    · obtain ⟨h, hne, hh, hpost, hz⟩ := synchronized_history (t i).property
      exact ⟨h, hne, hh, hz⟩

end
end D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity
