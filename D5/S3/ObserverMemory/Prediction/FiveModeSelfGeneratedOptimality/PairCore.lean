/- GID: D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/PairCore
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedOptimality/PairCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affinity leakage forces exact recurrent cores and disjoint startup charges. -/

import D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
import D5.S3.TotalVariation.HellingerDivergence
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Logic.Relation

namespace D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.PairCore

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.TotalVariation.Bhattacharyya D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.HellingerDivergence
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators Matrix

noncomputable section

private lemma mul_vec_mono {T : Type*} [Fintype T] (A : Matrix T T ℝ)
    (hA : ∀ i j, 0 ≤ A i j) {f g : T → ℝ} (hfg : f ≤ g) : A *ᵥ f ≤ A *ᵥ g := by
  intro i
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hfg j) (hA i j)

private lemma survival_antitone {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1) :
    Antitone (fun n : Nat => A ^ n *ᵥ (1 : T → ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [pow_succ, ← Matrix.mulVec_mulVec]
  exact mul_vec_mono _ (Matrix.pow_apply_nonneg hA n) hrow

/-- Follow actual edges only while the current row has no loss. A loss encountered before
the nominated endpoint already suffices, so no irreducibility of the affinity matrix is used. -/
private lemma loss_along_actual_path {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1)
    (R : T → T → Prop)
    (hfull : ∀ i, (A *ᵥ 1) i = 1 → ∀ j, R i j → 0 < A i j)
    {i j : T} (hpath : Relation.ReflTransGen R i j) (hj : (A *ᵥ 1) j < 1) :
    ∃ n : Nat, 1 ≤ n ∧ (A ^ n *ᵥ 1) i < 1 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨1, le_rfl, by simpa using hj⟩
  | @head i k hik _ ih =>
    by_cases hi : (A *ᵥ 1) i < 1
    · exact ⟨1, le_rfl, by simpa using hi⟩
    · have he : (A *ᵥ 1) i = 1 := le_antisymm (hrow i) (le_of_not_gt hi)
      obtain ⟨n, hn, hkn⟩ := ih
      refine ⟨n+1, by omega, ?_⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hle : A ^ n *ᵥ (1 : T → ℝ) ≤ 1 := by
        simpa using survival_antitone A hA hrow (Nat.zero_le n)
      calc
        (A *ᵥ (A ^ n *ᵥ 1)) i < (A *ᵥ 1) i := by
          apply Finset.sum_lt_sum
          · intro t _
            exact mul_le_mul_of_nonneg_left (hle t) (hA i t)
          · exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left hkn (hfull i he k hik)⟩
        _ = 1 := he

private lemma common_loss {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : A *ᵥ 1 ≤ 1)
    (R : T → T → Prop)
    (hfull : ∀ i, (A *ᵥ 1) i = 1 → ∀ j, R i j → 0 < A i j)
    (hirr : ∀ i j, Relation.ReflTransGen R i j)
    (hdef : ∃ j, (A *ᵥ 1) j < 1) :
    ∃ L : Nat, 1 ≤ L ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ i, (A ^ L *ᵥ 1) i ≤ c := by
  classical
  obtain ⟨j, hj⟩ := hdef
  choose n hn hlt using fun i => loss_along_actual_path A hA hrow R hfull (hirr i j) hj
  let L := Finset.univ.sup n
  have hnL (i : T) : n i ≤ L := Finset.le_sup (Finset.mem_univ i)
  have hL (i : T) : (A ^ L *ᵥ 1) i < 1 :=
    lt_of_le_of_lt (survival_antitone A hA hrow (hnL i) i) (hlt i)
  let s : Finset ℝ := Finset.univ.image (fun i => (A ^ L *ᵥ 1) i)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  refine ⟨L, (hn j).trans (hnL j), s.max' hs, ?_, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.max'_mem hs)
    rw [← hi]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Matrix.pow_apply_nonneg hA L i k) zero_le_one
  · apply (s.max'_lt_iff hs).mpr
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hL i
  · intro i
    exact s.le_max' _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private lemma block_survival_bound {T : Type*} [Fintype T] [DecidableEq T]
    (A : Matrix T T ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {L : Nat} {c : ℝ} (hc : 0 ≤ c) (hL : ∀ i, (A ^ L *ᵥ 1) i ≤ c) (n : Nat) :
    ∀ i, (A ^ (L*n) *ᵥ 1) i ≤ c ^ n := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [Nat.mul_succ, Nat.add_comm, pow_add, ← Matrix.mulVec_mulVec]
    calc
      (A ^ L *ᵥ (A ^ (L*n) *ᵥ 1)) i ≤ (A ^ L *ᵥ (fun _ => c^n)) i :=
        mul_vec_mono _ (Matrix.pow_apply_nonneg hA L) ih i
      _ = (A ^ L *ᵥ 1) i * c^n := by
        simp [Matrix.mulVec, dotProduct, Finset.sum_mul]
      _ ≤ c * c^n := mul_le_mul_of_nonneg_right (hL i) (pow_nonneg hc n)
      _ = c^(n+1) := (pow_succ' c n).symm

/-- A finite set of source--observer pairs closed under every source-positive symbol.
Zero forecast probabilities do not remove actual transitions. -/
structure PairClass {Z : Type*} (p q r : ℝ) (O : GeneratedObserver Z) where
  carrier : Finset (State × Z)
  closed : ∀ t ∈ carrier, ∀ y, 0 < pureRow p q r t.1 y →
    (nextPure t.1 y, O.update t.2 y) ∈ carrier

namespace PairClass

variable {Z : Type*} {p q r : ℝ} {O : GeneratedObserver Z}

/-- Source-positive transitions have their actual endpoint. A source-zero symbol uses the
current pair as a harmless totalization; its affinity coefficient is zero. -/
def step (C : PairClass p q r O) (t : C.carrier) (y : Visible) : C.carrier := by
  classical
  exact if h : 0 < pureRow p q r t.val.1 y then
    ⟨(nextPure t.val.1 y, O.update t.val.2 y), C.closed t.val t.property y h⟩ else t

/-- Edges of the actual synchronized source chain, independent of forecast support. -/
def Edge (C : PairClass p q r O) (t u : C.carrier) : Prop :=
  ∃ y, 0 < pureRow p q r t.val.1 y ∧ C.step t y = u

/-- The visible-symbol affinity matrix on the closed pair set. -/
def affinity (C : PairClass p q r O) : Matrix C.carrier C.carrier ℝ := by
  classical
  exact fun t u => ∑ y, if C.step t y = u then
    Real.sqrt (pureRow p q r t.val.1 y * O.row t.val.2 y) else 0

private lemma source_row_probability (hp : admissible p q r) (i : State) :
    (∀ y, 0 ≤ pureRow p q r i y) ∧ (∑ y, pureRow p q r i y) = 1 := by
  simpa only [pure_one_step] using one_step_probability _ (pure_probability hp i)

private lemma affinity_nonneg (C : PairClass p q r O) : ∀ t u, 0 ≤ C.affinity t u := by
  classical
  intro t u
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

private lemma affinity_apply (C : PairClass p q r O) (f : C.carrier → ℝ)
    (t : C.carrier) :
    (C.affinity *ᵥ f) t = ∑ y,
      Real.sqrt (pureRow p q r t.val.1 y * O.row t.val.2 y) * f (C.step t y) := by
  classical
  simp only [Matrix.mulVec, dotProduct, affinity, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp [ite_mul]

private lemma affinity_row (C : PairClass p q r O) (t : C.carrier) :
    (C.affinity *ᵥ 1) t = bhattacharyya (pureRow p q r t.val.1) (O.row t.val.2) := by
  rw [affinity_apply]
  simp [bhattacharyya]

private lemma affinity_substochastic (C : PairClass p q r O) (hp : admissible p q r) :
    C.affinity *ᵥ 1 ≤ 1 := by
  intro t
  rw [affinity_row]
  exact bhattacharyya_le_one _ _ (source_row_probability hp t.val.1)
    ⟨O.row_nonneg _, O.row_sum _⟩

private lemma full_row_iff (C : PairClass p q r O) (hp : admissible p q r)
    (t : C.carrier) : (C.affinity *ᵥ 1) t = 1 ↔ O.row t.val.2 = pureRow p q r t.val.1 := by
  rw [affinity_row]
  constructor
  · intro h
    have hz := hellinger_sq_eq_two_sub (pureRow p q r t.val.1) (O.row t.val.2)
      (source_row_probability hp t.val.1) ⟨O.row_nonneg t.val.2, O.row_sum t.val.2⟩
    rw [h, sub_self, mul_zero] at hz
    exact ((hellinger_sq_eq_zero_iff _ _ (source_row_probability hp t.val.1).1
      (O.row_nonneg _)).mp hz).symm
  · intro h
    rw [h]
    exact bhattacharyya_self _ (source_row_probability hp t.val.1)

private lemma full_row_edge_positive (C : PairClass p q r O) (hp : admissible p q r)
    (t : C.carrier) (h : (C.affinity *ᵥ 1) t = 1) (u : C.carrier)
    (htu : C.Edge t u) : 0 < C.affinity t u := by
  classical
  obtain ⟨y, hy, hnext⟩ := htu
  apply Finset.sum_pos'
  · intro a _
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  · refine ⟨y, Finset.mem_univ _, ?_⟩
    simp only [hnext, (C.full_row_iff hp t).mp h]
    rw [Real.sqrt_mul_self hy.le]
    exact hy

open Classical in
/-- A nonexact row in an actual irreducible closed class forces one common strict
affinity loss, even when the affinity matrix itself is reducible. -/
theorem affinity_leak (C : PairClass p q r O) (hp : admissible p q r)
    (hirr : ∀ t u, Relation.ReflTransGen C.Edge t u)
    (hbad : ∃ t : C.carrier, O.row t.val.2 ≠ pureRow p q r t.val.1) :
    ∃ L : Nat, 1 ≤ L ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      (∀ t, (C.affinity ^ L *ᵥ 1) t ≤ 1-η) ∧
      (∀ n t, (C.affinity ^ (L*n) *ᵥ 1) t ≤ (1-η)^n) := by
  classical
  obtain ⟨t, ht⟩ := hbad
  have : Nonempty C.carrier := ⟨t⟩
  have hd : ∃ t, (C.affinity *ᵥ 1) t < 1 :=
    ⟨t, lt_of_le_of_ne (C.affinity_substochastic hp t)
      (fun h => ht ((C.full_row_iff hp t).mp h))⟩
  obtain ⟨L, hL, c, hc, hc1, hbound⟩ := common_loss C.affinity C.affinity_nonneg
    (C.affinity_substochastic hp) C.Edge (C.full_row_edge_positive hp) hirr hd
  refine ⟨L, hL, 1-c, by linarith, by linarith, ?_, ?_⟩
  · simpa using hbound
  · intro n t
    simpa using block_survival_bound C.affinity C.affinity_nonneg hc hbound n t

private lemma step_val (C : PairClass p q r O) (t : C.carrier) (y : Visible)
    (hy : 0 < pureRow p q r t.val.1 y) :
    (C.step t y).val = (nextPure t.val.1 y, O.update t.val.2 y) := by
  classical
  simp [step, hy]

open Classical in
/-- Unifilarity identifies matrix survival with affinity of the original visible-word laws.
Source-zero words contribute zero even if the observer generates them with positive mass. -/
private lemma word_affinity (C : PairClass p q r O) (hp : admissible p q r)
    (H : Nat) (t : C.carrier) :
    bhattacharyya (pureLaw p q r t.val.1 H)
      (generatedLaw O.update O.row t.val.2 H) = (C.affinity ^ H *ᵥ 1) t := by
  classical
  induction H generalizing t with
  | zero => simp [bhattacharyya, pure_zero, generatedLaw]
  | succ H ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, affinity_apply, bhattacharyya, sum_words_succ]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : 0 < pureRow p q r t.val.1 y
    · rw [← ih (C.step t y)]
      simp only [pure_cons, generated_cons, Fin.cons_zero, Fin.cons_succ,
        bhattacharyya, C.step_val t y hy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [show (pureRow p q r t.val.1 y * pureLaw p q r (nextPure t.val.1 y) H w) *
          (O.row t.val.2 y * generatedLaw O.update O.row (O.update t.val.2 y) H w) =
        (pureRow p q r t.val.1 y * O.row t.val.2 y) *
          (pureLaw p q r (nextPure t.val.1 y) H w *
            generatedLaw O.update O.row (O.update t.val.2 y) H w) by ring]
      exact Real.sqrt_mul (mul_nonneg hy.le (O.row_nonneg _ _)) _
    · have hz : pureRow p q r t.val.1 y = 0 :=
        le_antisymm (le_of_not_gt hy) ((source_row_probability hp _).1 y)
      simp [pure_cons, generated_cons, hz]

open Classical in
private lemma tv_lower (C : PairClass p q r O) (hp : admissible p q r)
    (H : Nat) (t : C.carrier) :
    1 - (C.affinity ^ H *ᵥ 1) t ≤
      totalVariation (pureLaw p q r t.val.1 H)
        (generatedLaw O.update O.row t.val.2 H) := by
  have hP := pure_probability hp t.val.1 H
  have hQ := (generated_coherent O t.val.2).1 H
  have h := hellinger_sq_div_two_le_total_variation
    (pureLaw p q r t.val.1 H) (generatedLaw O.update O.row t.val.2 H)
  rw [hellinger_sq_eq_two_sub (pureLaw p q r t.val.1 H)
    (generatedLaw O.update O.row t.val.2 H) hP hQ, C.word_affinity hp H t] at h
  linarith

/-- A deficient recurrent class becomes perfectly distinguishable in the limit of finite
visible-word horizons, with the original observer law, including its extra support. -/
private theorem tv_tendsto_one (C : PairClass p q r O) (hp : admissible p q r)
    (hirr : ∀ t u, Relation.ReflTransGen C.Edge t u)
    (hbad : ∃ t : C.carrier, O.row t.val.2 ≠ pureRow p q r t.val.1) (t : C.carrier) :
    Filter.Tendsto (fun H => totalVariation (pureLaw p q r t.val.1 H)
      (generatedLaw O.update O.row t.val.2 H)) Filter.atTop (nhds 1) := by
  classical
  obtain ⟨L, hL, η, hη, hη1, _, hblock⟩ := C.affinity_leak hp hirr hbad
  have hbound (H : Nat) : (C.affinity ^ H *ᵥ 1) t ≤ (1-η)^(H/L) := by
    have hdiv : L * (H/L) ≤ H := by simpa [Nat.mul_comm] using Nat.div_mul_le_self H L
    exact (survival_antitone C.affinity C.affinity_nonneg
      (C.affinity_substochastic hp) hdiv t).trans (hblock (H/L) t)
  have hdivlim : Filter.Tendsto (fun H : Nat => H/L) Filter.atTop Filter.atTop := by
    rw [Filter.Tendsto, Filter.map_div_atTop_eq_nat L (by omega)]
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by linarith : 0 ≤ 1-η) (by linarith : 1-η < 1)).comp hdivlim
  have hzero : Filter.Tendsto (fun H => (C.affinity ^ H *ᵥ 1) t)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun H => ?_) hbound hpow
    exact Finset.sum_nonneg fun u _ =>
      mul_nonneg (Matrix.pow_apply_nonneg C.affinity_nonneg H t u) zero_le_one
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Filter.Tendsto (fun H => 1 - (C.affinity ^ H *ᵥ 1) t)
      Filter.atTop (nhds 1) by simpa using tendsto_const_nhds.sub hzero)
    tendsto_const_nhds (fun H => C.tv_lower hp H t)
  intro H
  exact total_variation_le_one _ _ (pure_probability hp t.val.1 H)
    ((generated_coherent O t.val.2).1 H)

/-- Uniform all-horizon error below one forces every row in each actual irreducible closed
pair class to be exact. The approximation tolerance is not required to be small. -/
private theorem rows_exact (C : PairClass p q r O) (hp : admissible p q r)
    (hirr : ∀ t u, Relation.ReflTransGen C.Edge t u) {ε : ℝ} (hε : ε < 1)
    (hacc : ∀ t : C.carrier, ∀ H,
      totalVariation (pureLaw p q r t.val.1 H)
        (generatedLaw O.update O.row t.val.2 H) ≤ ε) :
    ∀ t : C.carrier, O.row t.val.2 = pureRow p q r t.val.1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := h
  have hle := le_of_tendsto' (C.tv_tendsto_one hp hirr ⟨t, ht⟩ t) (hacc t)
  exact (not_le_of_gt hε) hle

private lemma laws_exact_of_rows (C : PairClass p q r O) (hp : admissible p q r)
    (he : ∀ t : C.carrier, O.row t.val.2 = pureRow p q r t.val.1)
    (t : C.carrier) (H : Nat) (w : Fin H → Visible) :
    generatedLaw O.update O.row t.val.2 H w = pureLaw p q r t.val.1 H w := by
  induction H generalizing t with
  | zero => simp [generatedLaw, pure_zero]
  | succ H ih =>
    rw [generatedLaw, pure_cons, congrFun (he t) (w 0)]
    by_cases hy : 0 < pureRow p q r t.val.1 (w 0)
    · have hs := C.step_val t (w 0) hy
      have hi := ih (C.step t (w 0)) (fun j => w j.succ)
      simpa only [hs] using congrArg (fun x => pureRow p q r t.val.1 (w 0) * x) hi
    · have hz : pureRow p q r t.val.1 (w 0) = 0 :=
        le_antisymm (le_of_not_gt hy) ((source_row_probability hp _).1 _)
      simp [hz]

end PairClass

open Classical in
/-- Actual synchronized pairs are witnessed by positive finite histories and a pure source tag. -/
private def synchronizedPairs {Z : Type*} [Fintype Z] (p q r : ℝ) (O : GeneratedObserver Z) :
    Finset (State × Z) :=
  Finset.univ.filter fun t => ∃ h : List Visible, h ≠ [] ∧ 0 < historyMass p q r h ∧
    sourceRun h = .pure t.1 ∧ O.toObserver.run h = t.2

private lemma synchronized_closed {Z : Type*} [Fintype Z] {p q r : ℝ}
    (O : GeneratedObserver Z) :
    ∀ t ∈ synchronizedPairs p q r O, ∀ y, 0 < pureRow p q r t.1 y →
      (nextPure t.1 y, O.update t.2 y) ∈ synchronizedPairs p q r O := by
  classical
  intro t ht y hy
  obtain ⟨h, hne, hpos, htag, hr⟩ := (Finset.mem_filter.mp ht).2
  have hpost : acquiredPosterior p q r h = pureVector t.1 := by
    rw [positive_history_invariant p q r h hpos, htag, pure_profile]
  have hmass := all_history_conditional_identity p q r h 1 (fun _ => y)
  rw [actual_pure_law h hne t.1 hpost, pure_one_step] at hmass
  have hpos' : 0 < historyMass p q r (h ++ [y]) := by
    have hv : 0 < historyMass p q r (h ++ List.ofFn (fun _ : Fin 1 => y)) /
        historyMass p q r h := by rw [hmass]; exact hy
    simpa using (div_pos_iff_of_pos_right hpos).mp hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, h ++ [y], by simp, hpos', ?_, ?_⟩
  · rw [source_run_snoc, htag]
    have hencode := pure_update (0 : State) 0 t.1 y
    change encodeSource 0 0 (sourceUpdate (.pure t.1) y) =
      some (Sum.inl (nextPure t.1 y)) at hencode
    obtain ⟨i, hi⟩ := fold_pure [y] t.1
    simp only [List.foldl_cons, List.foldl_nil] at hi
    rw [hi] at hencode ⊢
    simpa [encodeSource] using hencode
  · rw [run_snoc]
    change O.update (O.toObserver.run h) y = O.update t.2 y
    rw [hr]

private lemma terminal_subset {T : Type*} [Finite T] [Nonempty T]
    (R : T → T → Prop) :
    ∃ s : Finset T, s.Nonempty ∧ (∀ i ∈ s, ∀ j, R i j → j ∈ s) ∧
      (∀ i ∈ s, ∀ j ∈ s, Relation.ReflTransGen R i j) := by
  classical
  let := Fintype.ofFinite T
  let reach (i : T) := Finset.univ.filter (Relation.ReflTransGen R i)
  have hsub {i j : T} (h : Relation.ReflTransGen R i j) : reach j ⊆ reach i := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hk).2⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun i => (reach i).card)
    Finset.univ_nonempty
  refine ⟨reach i, ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩⟩, ?_, ?_⟩
  · intro j hj k hjk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.tail hjk⟩
  · intro j hj k hk
    have heq : reach j = reach i := Finset.eq_of_subset_of_card_le
      (hsub (Finset.mem_filter.mp hj).2) (hi j (Finset.mem_univ _))
    have hjk : k ∈ reach j := by rw [heq]; exact hk
    exact (Finset.mem_filter.mp hjk).2

private lemma lift_closed_path {T : Type*} (R : T → T → Prop) (s : Finset T)
    (hclosed : ∀ i ∈ s, ∀ j, R i j → j ∈ s) {i j : T}
    (h : Relation.ReflTransGen R i j) (hi : i ∈ s) :
    ∃ hj : j ∈ s, Relation.ReflTransGen (fun a b : s => R a.val b.val) ⟨i, hi⟩ ⟨j, hj⟩ := by
  induction h with
  | refl => exact ⟨hi, .refl⟩
  | @tail j k _ hjk ih =>
    obtain ⟨hj, hpath⟩ := ih
    exact ⟨hclosed j hj k hjk, hpath.tail hjk⟩

private lemma recurrent_class_exists {Z : Type*} [Fintype Z] {p q r : ℝ}
    (O : GeneratedObserver Z) (hp : admissible p q r) :
    ∃ C : PairClass p q r O, C.carrier.Nonempty ∧
      C.carrier ⊆ synchronizedPairs p q r O ∧
      ∀ t u, Relation.ReflTransGen C.Edge t u := by
  classical
  let C₀ : PairClass p q r O := ⟨synchronizedPairs p q r O, synchronized_closed O⟩
  have hstart : (0, O.toObserver.run (pureWitness 0)) ∈ C₀.carrier :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, pureWitness 0,
      (pure_witness_actual hp 0).1, (pure_witness_actual hp 0).2.1, pure_witness_run 0, rfl⟩
  have : Nonempty C₀.carrier := ⟨⟨_, hstart⟩⟩
  obtain ⟨s, hs, hclosed, hirr⟩ := terminal_subset C₀.Edge
  let C : PairClass p q r O := {
    carrier := s.image Subtype.val
    closed := by
      intro t ht y hy
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      have hn := hclosed t₀ ht₀ (C₀.step t₀ y) ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨C₀.step t₀ y, hn, C₀.step_val t₀ y hy⟩ }
  refine ⟨C, hs.image _, ?_, ?_⟩
  · intro t ht
    obtain ⟨t₀, _, rfl⟩ := Finset.mem_image.mp ht
    exact t₀.property
  · intro t u
    obtain ⟨t₀, ht₀, het⟩ := Finset.mem_image.mp t.property
    obtain ⟨u₀, hu₀, heu⟩ := Finset.mem_image.mp u.property
    obtain ⟨hu, hpath⟩ := lift_closed_path C₀.Edge s hclosed (hirr t₀ ht₀ u₀ hu₀) ht₀
    let emb : s → C.carrier := fun x =>
      ⟨x.val.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
    have hedge : ∀ a b : s, C₀.Edge a.val b.val → C.Edge (emb a) (emb b) := by
      intro a b hab
      obtain ⟨y, hy, he⟩ := hab
      refine ⟨y, hy, Subtype.ext ?_⟩
      change (C.step (emb a) y).val = b.val.val
      rw [C.step_val (emb a) y hy]
      exact (C₀.step_val a.val y hy).symm.trans (congrArg Subtype.val he)
    have hp' := hpath.lift emb hedge
    have het' : emb ⟨t₀, ht₀⟩ = t := Subtype.ext het
    have heu' : emb ⟨u₀, hu⟩ = u := Subtype.ext heu
    simpa only [Function.onFun, het', heu'] using hp'

private lemma class_accuracy {Z : Type*} [Fintype Z] {p q r ε : ℝ}
    {O : GeneratedObserver Z} (C : PairClass p q r O)
    (hsub : C.carrier ⊆ synchronizedPairs p q r O)
    (hacc : O.toObserver.Accurate p q r ε true) (t : C.carrier) (H : Nat) :
    totalVariation (pureLaw p q r t.val.1 H)
      (generatedLaw O.update O.row t.val.2 H) ≤ ε := by
  classical
  obtain ⟨h, hne, hpos, htag, hr⟩ := (Finset.mem_filter.mp (hsub t.property)).2
  have hpost : acquiredPosterior p q r h = pureVector t.val.1 := by
    rw [positive_history_invariant p q r h hpos, htag, pure_profile]
  have ha := hacc h hpos (Or.inl rfl) H
  rw [actual_pure_law h hne _ hpost, hr] at ha
  exact ha

private lemma covers_modes {Z : Type*} {p q r : ℝ} {O : GeneratedObserver Z}
    (C : PairClass p q r O) (hp : admissible p q r) (hn : C.carrier.Nonempty) :
    ∀ i : State, ∃ z, (i, z) ∈ C.carrier := by
  have hzero : ∃ z, ((0 : State), z) ∈ C.carrier := by
    obtain ⟨⟨i, z⟩, hz⟩ := hn
    fin_cases i
    · exact ⟨z, hz⟩
    · exact ⟨O.update z 0, by
        simpa [nextPure, singletonState, B] using
          C.closed (1, z) hz 0 (by simpa [pureRow] using hp.2.1)⟩
    · have h1 : ((1 : State), O.update z 1) ∈ C.carrier := by
        simpa [nextPure, singletonState, B] using
          C.closed (2, z) hz 1 (by simpa [pureRow] using hp.2.1)
      exact ⟨O.update (O.update z 1) 0, by
        simpa [nextPure, singletonState, B] using
          C.closed (1, O.update z 1) h1 0 (by simpa [pureRow] using hp.2.1)⟩
    · exact ⟨O.update z 0, by
        simpa [nextPure, singletonState, B] using
          C.closed (3, z) hz 0 (by simpa [pureRow] using hp.1)⟩
    · exact ⟨O.update z 0, by
        simpa [nextPure, singletonState, B] using
          C.closed (4, z) hz 0 (by simpa [pureRow] using hp.2.2.1)⟩
  obtain ⟨z, hz⟩ := hzero
  have h1 : ((1 : State), O.update z 1) ∈ C.carrier := by
    simpa [nextPure, singletonState, B] using
      C.closed (0, z) hz 1 (by simpa [pureRow] using hp.1)
  intro i
  fin_cases i
  · exact ⟨z, hz⟩
  · exact ⟨O.update z 1, h1⟩
  · exact ⟨O.update (O.update z 1) B, by
      simpa [nextPure, pureBSuccessor] using
        C.closed (1, O.update z 1) h1 B (by simpa [pureRow, B] using hp.1)⟩
  · exact ⟨O.update z 3, by
      simpa [nextPure, singletonState, B] using
        C.closed (0, z) hz 3 (by simpa [pureRow] using hp.2.1)⟩
  · exact ⟨O.update z B, by
      simpa [nextPure, pureBSuccessor] using
        C.closed (0, z) hz B (by simpa [pureRow, B] using hp.2.2.1)⟩

/-- Every accurate finite generated observer has an actually reachable, B-closed exact core
covering all five source modes. Additional generated-only states remain in the carrier. -/
theorem exact_core_exists {Z : Type*} [Finite Z] {p q r ε : ℝ}
    (O : GeneratedObserver Z) (hp : admissible p q r) (hε : ε < 1)
    (hacc : O.toObserver.Accurate p q r ε true) :
    ∃ core : Finset Z, 5 ≤ core.card ∧
      (∀ z ∈ core, O.update z B ∈ core) ∧
      (∀ z ∈ core, ∃ i : State, O.toObserver.decoder z = pureLaw p q r i) ∧
      (∀ i : State, ∃ z ∈ core, O.toObserver.decoder z = pureLaw p q r i) ∧
      (∀ z ∈ core, z ∈ O.toObserver.Reached p q r) := by
  classical
  let := Fintype.ofFinite Z
  obtain ⟨C, hn, hsub, hirr⟩ := recurrent_class_exists O hp
  have hrows := C.rows_exact hp hirr hε (class_accuracy C hsub hacc)
  have hlaws (t : C.carrier) : O.toObserver.decoder t.val.2 = pureLaw p q r t.val.1 := by
    funext H w
    exact C.laws_exact_of_rows hp hrows t H w
  let core := C.carrier.image Prod.snd
  have hcover (i : State) : ∃ z ∈ core, O.toObserver.decoder z = pureLaw p q r i := by
    obtain ⟨z, hz⟩ := covers_modes C hp hn i
    exact ⟨z, Finset.mem_image.mpr ⟨(i, z), hz, rfl⟩, hlaws ⟨(i, z), hz⟩⟩
  have hcard : 5 ≤ core.card := by
    choose z hz hl using hcover
    have hinj : Function.Injective z := by
      intro i j hij
      apply (actual_predictive_class_distinctness hp).1
      rw [← hl i, ← hl j, hij]
    have hc := Fintype.card_le_of_injective (fun i : State => (⟨z i, hz i⟩ : core))
      (fun i j h => hinj (congrArg Subtype.val h))
    simpa using hc
  refine ⟨core, hcard, ?_, ?_, hcover, ?_⟩
  · intro z hz
    obtain ⟨⟨i, z⟩, hi, rfl⟩ := Finset.mem_image.mp hz
    have hB : 0 < pureRow p q r i B := by
      have he : pureRow p q r i B = pureBMass p q r i := by
        fin_cases i <;> simp [pureRow, pureBMass, B]
      rw [he]
      exact pure_B_mass_positive hp i
    exact Finset.mem_image.mpr ⟨_, C.closed (i, z) hi B hB, rfl⟩
  · intro z hz
    obtain ⟨⟨i, z⟩, hi, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, hlaws ⟨(i, z), hi⟩⟩
  · intro z hz
    obtain ⟨⟨i, z⟩, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨h, hne, hpos, _, hr⟩ := (Finset.mem_filter.mp (hsub hi)).2
    exact ⟨h, hne, hpos, hr⟩

private lemma first_core_entry_cost {Z : Type*} [Fintype Z] {p q r ε : ℝ}
    (O : GeneratedObserver Z) (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true) (core : Finset Z)
    (hcard : 5 ≤ core.card)
    (hexact : ∀ z ∈ core, ∃ i : State, O.toObserver.decoder z = pureLaw p q r i)
    (hinit : O.initial ∉ core)
    (hentry : ∃ k, startupState O.toObserver k ∈ core) :
    6 + N1 p q r ε ≤ Fintype.card Z := by
  classical
  let m := Nat.find hentry
  have hm : startupState O.toObserver m ∈ core := Nat.find_spec hentry
  have hbefore (k : Nat) (hk : k < m) : startupState O.toObserver k ∉ core :=
    Nat.find_min hentry hk
  have hNm : N1 p q r ε ≤ m := by
    by_contra hn
    obtain ⟨i, hi⟩ := hexact _ hm
    have hdist := accurate_profile hacc (List.replicate (m+1) B)
      (startup_history_positive hp m) (Or.inl rfl)
    change profileDistance (actualFutureWordWeight p q r (List.replicate (m+1) B))
      (O.toObserver.decoder (startupState O.toObserver m)) ≤ ε at hdist
    rw [hi] at hdist
    have hsep := (startup_transient_separation (ε := ε/2) hp hne
      (by linarith) (by linarith) m
      (by simpa only [N1, N2, show 2 * (ε/2) = ε by ring] using Nat.lt_of_not_ge hn)).1 i
    linarith
  have hcoll {i j : Nat} (hij : i < j) (hj : j < m)
      (he : startupState O.toObserver i = startupState O.toObserver j) : False := by
    have hs : startupState O.toObserver (i+(m-j)) = startupState O.toObserver m := by
      rw [startup_shift, he, ← startup_shift]
      congr 1
      omega
    exact hbefore (i+(m-j)) (by omega) (by rw [hs]; exact hm)
  let pre := (Finset.range m).image (startupState O.toObserver)
  have hpre : pre.card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hcoll hij hj' he).elim
    · exact hij
    · exact (hcoll hij hi' he.symm).elim
  have hdis : Disjoint core pre := by
    apply Finset.disjoint_left.mpr
    intro z hz hpz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hpz
    exact hbefore k (Finset.mem_range.mp hk) hz
  have hnpre : O.initial ∉ pre := by
    intro hi
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
    exact postread_initialization_extra_state hp hne hεk (generated_coherent O) hacc
      (List.replicate (k+1) B) (by simp) (startup_history_positive hp k) hk.symm
  have hc := (insert O.initial (core ∪ pre)).card_le_univ
  rw [Finset.card_insert_of_notMem (by simpa using And.intro hinit hnpre),
    Finset.card_union_of_disjoint hdis, hpre] at hc
  omega

/-- Below the exact-emission cutoff cost, the whole startup orbit avoids an exact core.
Initialization, the five core modes and every distinct selected startup configuration are
charged to the original finite carrier. -/
theorem exact_core_billing {Z : Type*} [Fintype Z] {p q r ε : ℝ}
    (O : GeneratedObserver Z) (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true)
    (hsmall : Fintype.card Z < 6 + N1 p q r ε) :
    ∃ core : Finset Z, 5 ≤ core.card ∧
      (∀ z ∈ core, O.update z B ∈ core) ∧
      (∀ z ∈ core, ∃ i : State, O.toObserver.decoder z = pureLaw p q r i) ∧
      (∀ i : State, ∃ z ∈ core, O.toObserver.decoder z = pureLaw p q r i) ∧
      O.initial ∉ core ∧ (∀ k, startupState O.toObserver k ∉ core) ∧
      (∀ k, O.initial ≠ startupState O.toObserver k) ∧
      (∀ s : Finset Nat, Set.InjOn (startupState O.toObserver) s →
        6 + s.card ≤ Fintype.card Z) := by
  classical
  have he1 : ε < 1 := by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
  obtain ⟨core, hc, hB, hex, hcov, hr⟩ := exact_core_exists O hp he1 hacc
  have hi : O.initial ∉ core := by
    intro h
    obtain ⟨w, hne', hpos, hw⟩ := hr O.initial h
    exact postread_initialization_extra_state hp hne hεk (generated_coherent O) hacc
      w hne' hpos hw.symm
  have havoid (k : Nat) : startupState O.toObserver k ∉ core := by
    intro hk
    exact (not_le_of_gt hsmall)
      (first_core_entry_cost O hp hne hε hεk hacc core hc hex hi ⟨k, hk⟩)
  have hinit (k : Nat) : O.initial ≠ startupState O.toObserver k :=
    postread_initialization_extra_state hp hne hεk (generated_coherent O) hacc
      (List.replicate (k+1) B) (by simp) (startup_history_positive hp k)
  refine ⟨core, hc, hB, hex, hcov, hi, havoid, hinit, ?_⟩
  intro s hs
  let pre := s.image (startupState O.toObserver)
  have hpre : pre.card = s.card := Finset.card_image_of_injOn hs
  have hdis : Disjoint core pre := by
    apply Finset.disjoint_left.mpr
    intro z hz hpz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hpz
    exact havoid k hz
  have hnpre : O.initial ∉ pre := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    exact hinit k hk.symm
  have hcount := (insert O.initial (core ∪ pre)).card_le_univ
  rw [Finset.card_insert_of_notMem (by simpa using And.intro hi hnpre),
    Finset.card_union_of_disjoint hdis, hpre] at hcount
  omega

end

end D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedOptimality.PairCore
