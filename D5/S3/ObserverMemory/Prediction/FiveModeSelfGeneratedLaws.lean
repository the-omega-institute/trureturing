/- GID: D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-update complete product laws, exact uniform errors and attained finite-carrier minimum bounds for the five-mode source. -/

import D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount

namespace D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators
noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def generatedLaw {Z : Type*} (U : Z → Visible → Z) (g : Z → Visible → ℝ) : Z → LawProfile
  | _, 0, _ => 1
  | z, H+1, w => g z (w 0) * generatedLaw U g (U z (w 0)) H (fun k => w k.succ)

structure GeneratedObserver (Z : Type*) where
  initial : Z
  update : Z → Visible → Z
  row : Z → Visible → ℝ
  row_nonneg : ∀ z y, 0 ≤ row z y
  row_sum : ∀ z, (∑ y, row z y) = 1

def GeneratedObserver.toObserver {Z : Type*} (O : GeneratedObserver Z) : Observer Z where
  initial := O.initial
  update := O.update
  decoder := generatedLaw O.update O.row

lemma generated_cons {Z : Type*} (U : Z → Visible → Z) (g : Z → Visible → ℝ)
    (z : Z) (H : Nat) (y : Visible) (w : Fin H → Visible) :
    generatedLaw U g z (H+1) (Fin.cons y w) = g z y * generatedLaw U g (U z y) H w := by
  simp only [generatedLaw, Fin.cons_zero, Fin.cons_succ]

lemma generated_nonnegative {Z : Type*} (U : Z → Visible → Z) (g : Z → Visible → ℝ)
    (hg : ∀ z y, 0 ≤ g z y) (z : Z) (H : Nat) (w : Fin H → Visible) :
    0 ≤ generatedLaw U g z H w := by
  induction H generalizing z with
  | zero => norm_num [generatedLaw]
  | succ H ih => exact mul_nonneg (hg z (w 0)) (ih _ _)

lemma generated_sum {Z : Type*} (U : Z → Visible → Z) (g : Z → Visible → ℝ)
    (hg : ∀ z, (∑ y, g z y) = 1) (z : Z) (H : Nat) :
    (∑ w, generatedLaw U g z H w) = 1 := by
  induction H generalizing z with
  | zero => simp [generatedLaw]
  | succ H ih =>
    rw [sum_words_succ]
    simp only [generated_cons, ← Finset.mul_sum, ih, mul_one]
    exact hg z

lemma generated_final_symbol {Z : Type*} (U : Z → Visible → Z) (g : Z → Visible → ℝ)
    (hg : ∀ z, (∑ y, g z y) = 1) (z : Z) (H : Nat) (w : Fin H → Visible) :
    (∑ y, generatedLaw U g z (H+1) (Fin.snoc (α := fun _ => Visible) w y)) = generatedLaw U g z H w := by
  induction H generalizing z with
  | zero => simpa only [Fin.snoc_zero, generatedLaw, mul_one] using hg z
  | succ H ih =>
    have hw : Fin.cons (w 0) (fun k => w k.succ) = w := by
      funext i; exact Fin.cases rfl (fun _ => rfl) i
    have hs (y : Visible) : Fin.snoc (α := fun _ => Visible) w y =
        Fin.cons (w 0) (Fin.snoc (α := fun _ => Visible) (fun k : Fin H => w k.succ) y) := by
      exact (congrArg (fun t : Fin (H+1) → Visible => Fin.snoc (α := fun _ => Visible) t y) hw.symm).trans
        (Fin.cons_snoc_eq_snoc_cons (w 0) (fun k => w k.succ) y).symm
    calc
      _ = g z (w 0) * ∑ y, generatedLaw U g (U z (w 0)) (H+1)
          (Fin.snoc (α := fun _ => Visible) (fun k : Fin H => w k.succ) y) := by
        simp only [hs, generated_cons, Finset.mul_sum]
      _ = g z (w 0) * generatedLaw U g (U z (w 0)) H (fun k => w k.succ) := by rw [ih]
      _ = _ := rfl

lemma generated_coherent {Z : Type*} (O : GeneratedObserver Z) : O.toObserver.Coherent := by
  intro z
  exact ⟨fun H => ⟨generated_nonnegative _ _ O.row_nonneg z H,
    generated_sum _ _ O.row_sum z H⟩, generated_final_symbol _ _ O.row_sum z⟩

lemma one_step_probability (F : LawProfile) (hF : ProbabilityProfile F) :
    (∀ y : Visible, 0 ≤ F 1 (fun _ => y)) ∧ (∑ y : Visible, F 1 (fun _ => y)) = 1 := by
  refine ⟨fun y => (hF 1).1 _, ?_⟩
  have hs := (hF 1).2
  rw [one_horizon_sum] at hs
  exact hs

def cutoffRows (p q r : ℝ) (N : Nat) : SharpState N → Visible → ℝ
  | none, y => if y = B then 2/5 else 1/5
  | some (.inl i), y => pureRow p q r i y
  | some (.inr k), y => orientedMixture p q r (minority (theta p q r) k.val) 1 (fun _ => y)

lemma cutoffRows_probability {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) :
    (∀ z y, 0 ≤ cutoffRows p q r N z y) ∧ (∀ z, (∑ y, cutoffRows p q r N z y) = 1) := by
  have hz (z : SharpState N) : (∀ y, 0 ≤ cutoffRows p q r N z y) ∧
      (∑ y, cutoffRows p q r N z y) = 1 := by
    cases z with
    | none => simpa only [cutoffRows, empty_one_step] using one_step_probability _ (empty_probability hp)
    | some z =>
      cases z with
      | inl i => simpa only [cutoffRows, ← pure_one_step] using one_step_probability _ (pure_probability hp i)
      | inr k =>
        have ht := theta_bounds hp hne
        have hx : minority (theta p q r) k.val ∈ Set.Icc 0 1 :=
          ⟨(minority_positive ht.1 _).le, (minority_le_half ht.1.le ht.2.le _).trans (by norm_num)⟩
        dsimp [cutoffRows, orientedMixture]
        split_ifs
        · exact one_step_probability _ (mixture_probability hp ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        · exact one_step_probability _ (mixture_probability hp hx)
  exact ⟨fun z => (hz z).1, fun z => (hz z).2⟩

def cutoffGenerator {p q r : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r) (N : Nat) :
    GeneratedObserver (SharpState N) where
  initial := none
  update := sharpUpdate (dominantState p q r) N
  row := cutoffRows p q r N
  row_nonneg := (cutoffRows_probability hp hne N).1
  row_sum := (cutoffRows_probability hp hne N).2

lemma cutoff_row_is_actual {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) (y : Visible) :
    cutoffRows p q r N (some (.inr k)) y =
      actualFutureWordWeight p q r (List.replicate (k.val+1) B) 1 (fun _ => y) :=
  (actual_oriented_startup hp hne k.val 1 (fun _ => y)).symm

lemma cutoff_run_is_actual {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (h : List Visible) :
    (cutoffGenerator hp hne N).toObserver.run h =
      encodeSource (dominantState p q r) N (sourceRun h) :=
  sharp_source_run _ _ (dominant_successor p q r) h

lemma cutoff_singleton_total (p q r : ℝ) (N : Nat) (z : SharpState N)
    (y : Visible) (hy : y = 0 ∨ y = 1 ∨ y = 3) :
    sharpUpdate (dominantState p q r) N z y =
      some (.inl (if y = 0 then 0 else if y = 1 then 1 else 3)) := by
  unfold sharpUpdate
  rw [singleton_resets _ _ hy]
  rfl

lemma actual_startup_B_recurrence {p q r : ℝ} (hp : admissible p q r)
    (k H : Nat) (w : Fin H → Visible) :
    ((a p q)^k+(b r)^k) *
        actualFutureWordWeight p q r (List.replicate (k+1) B) (H+1) (Fin.cons B w) =
      ((a p q)^(k+1)+(b r)^(k+1)) *
        actualFutureWordWeight p q r (List.replicate (k+2) B) H w := by
  have hk : (a p q)^k+(b r)^k ≠ 0 := ne_of_gt
    (add_pos (pow_pos (holding_bounds hp).1 _) (pow_pos (holding_bounds hp).2.2.1 _))
  have hk1 : (a p q)^(k+1)+(b r)^(k+1) ≠ 0 := ne_of_gt
    (add_pos (pow_pos (holding_bounds hp).1 _) (pow_pos (holding_bounds hp).2.2.1 _))
  rw [actual_startup_mixture hp, actual_startup_mixture hp]
  simp only [mixtureLaw, branch2_cons, branch4_cons, Fin.cons_zero, Fin.cons_succ, ite_true]
  unfold startupCoordinate
  field_simp [hk, hk1]
  simp only [pow_succ]
  ring

def singletonState (y : Visible) : State := if y = 0 then 0 else if y = 1 then 1 else 3

def nextPure (i : State) (y : Visible) : State :=
  if y = B then pureBSuccessor i else singletonState y

lemma pure_zero (p q r : ℝ) (i : State) (w : Fin 0 → Visible) :
    pureLaw p q r i 0 w = 1 := by simp [pureLaw, futureWordWeight, pureVector]

lemma pure_cons (p q r : ℝ) (i : State) (H : Nat) (w : Fin (H+1) → Visible) :
    pureLaw p q r i (H+1) w = pureRow p q r i (w 0) *
      pureLaw p q r (nextPure i (w 0)) H (fun j => w j.succ) := by
  by_cases hy : w 0 = B
  · have hr : pureRow p q r i B = pureBMass p q r i := by
      fin_cases i <;> simp [pureRow, pureBMass, B]
    simp only [pureLaw, futureWordWeight, hy, pure_B_step, future_word_scale]
    simp [hr, nextPure]
  · have hs : w 0 = 0 ∨ w 0 = 1 ∨ w 0 = 3 := by
      generalize he : w 0 = y at *
      fin_cases y <;> simp_all [B]
    have hf := filter_singleton (advance p q r (pureVector i)) (w 0) hs
    have hr : advance p q r (pureVector i) (singletonState (w 0)) =
        pureRow p q r i (w 0) := by
      rcases hs with hs | hs | hs
      all_goals fin_cases i <;> simp [hs, singletonState, advance, pureVector,
        transition, pureRow, a, b, c]
    change futureWordWeight p q r (filterAt (advance p q r (pureVector i)) (w 0))
      H (fun j => w j.succ) = _
    rw [hf, future_word_scale]
    change advance p q r (pureVector i) (singletonState (w 0)) *
      pureLaw p q r (singletonState (w 0)) H (fun j => w j.succ) = _
    rw [hr]
    simp only [nextPure, if_neg hy]

lemma pure_update (d : State) (N : Nat) (i : State) (y : Visible) :
    sharpUpdate d N (some (.inl i)) y = some (.inl (nextPure i y)) := by
  fin_cases i <;> fin_cases y <;> simp [sharpUpdate, representative, sourceUpdate, encodeSource,
    nextPure, singletonState, B, pureBSuccessor]

def cutoffLaw (p q r : ℝ) (N : Nat) : SharpState N → LawProfile :=
  generatedLaw (sharpUpdate (dominantState p q r) N) (cutoffRows p q r N)

lemma pure_generated (p q r : ℝ) (N : Nat) (i : State) (H : Nat)
    (w : Fin H → Visible) :
    cutoffLaw p q r N (some (.inl i)) H w = pureLaw p q r i H w := by
  induction H generalizing i with
  | zero => simp [cutoffLaw, generatedLaw, pure_zero]
  | succ H ih =>
    change cutoffRows p q r N (some (.inl i)) (w 0) *
      generatedLaw (sharpUpdate (dominantState p q r) N) (cutoffRows p q r N)
        (sharpUpdate (dominantState p q r) N (some (.inl i)) (w 0)) H
        (fun j => w j.succ) = _
    rw [pure_update]
    change pureRow p q r i (w 0) * cutoffLaw p q r N
      (some (.inl (nextPure i (w 0)))) H (fun j => w j.succ) = _
    rw [ih, pure_cons]

def T (p q r : ℝ) (k : Nat) : ℝ := (a p q)^k + (b r)^k

def startupLaw (p q r : ℝ) (k : Nat) : LawProfile :=
  actualFutureWordWeight p q r (List.replicate (k+1) B)

lemma T_pos {p q r : ℝ} (hp : admissible p q r) (k : Nat) : 0 < T p q r k :=
  add_pos (pow_pos (holding_bounds hp).1 _) (pow_pos (holding_bounds hp).2.2.1 _)

lemma startup_zero {p q r : ℝ} (hp : admissible p q r) (k : Nat)
    (w : Fin 0 → Visible) : startupLaw p q r k 0 w = 1 := by
  unfold startupLaw
  rw [actual_startup_mixture hp]
  simp only [mixtureLaw, pure_zero]
  ring

lemma startup_B {p q r : ℝ} (hp : admissible p q r) (k H : Nat)
    (w : Fin H → Visible) :
    startupLaw p q r k (H+1) (Fin.cons B w) =
      (T p q r (k+1) / T p q r k) * startupLaw p q r (k+1) H w := by
  have he := actual_startup_B_recurrence hp k H w
  change T p q r k * startupLaw p q r k (H+1) (Fin.cons B w) =
    T p q r (k+1) * startupLaw p q r (k+1) H w at he
  apply (mul_left_cancel₀ (ne_of_gt (T_pos hp k)))
  rw [he]
  field_simp [ne_of_gt (T_pos hp k)]

lemma startup_singleton {p q r : ℝ} (hp : admissible p q r) (k H : Nat)
    (y : Visible) (hy : y ≠ B) (w : Fin H → Visible) :
    startupLaw p q r k (H+1) (Fin.cons y w) =
      startupLaw p q r k 1 (fun _ => y) * pureLaw p q r (singletonState y) H w := by
  have hs : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
  unfold startupLaw
  rw [actual_startup_mixture hp, actual_startup_mixture hp]
  simp only [mixtureLaw, branch2_cons, branch4_cons, Fin.cons_zero, Fin.cons_succ,
    pure_one_step]
  rcases hs with rfl | rfl | rfl
  all_goals simp [B, singletonState, pureRow]; ring

lemma startup_B_row {p q r : ℝ} (hp : admissible p q r) (k : Nat) :
    startupLaw p q r k 1 (fun _ => B) = T p q r (k+1) / T p q r k := by
  have he := startup_B hp k 0 (fun i => Fin.elim0 i)
  have hw : Fin.cons B (fun i : Fin 0 => Fin.elim0 i) = (fun _ : Fin 1 => B) := by
    funext i; fin_cases i; rfl
  simpa only [hw, startup_zero hp, mul_one] using he

lemma cutoff_startup_row {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N k : Nat) (hk : k < N) (y : Visible) :
    cutoffRows p q r N (encodeSource (dominantState p q r) N (.startup k)) y =
      startupLaw p q r k 1 (fun _ => y) := by
  simpa only [encodeSource, dif_pos hk, startupLaw] using cutoff_row_is_actual hp hne N ⟨k,hk⟩ y

lemma generated_startup_B {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N k H : Nat) (hk : k < N) (w : Fin H → Visible) :
    cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k))
      (H+1) (Fin.cons B w) =
      (T p q r (k+1) / T p q r k) *
        cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup (k+1))) H w := by
  unfold cutoffLaw
  rw [generated_cons, cutoff_startup_row hp hne N k hk, startup_B_row hp]
  have hu : sharpUpdate (dominantState p q r) N
      (encodeSource (dominantState p q r) N (.startup k)) B =
      encodeSource (dominantState p q r) N (.startup (k+1)) := by
    simp [encodeSource, hk, sharpUpdate, representative, sourceUpdate, B]
  rw [hu]

lemma generated_startup_singleton {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N k H : Nat) (hk : k < N)
    (y : Visible) (hy : y ≠ B) (w : Fin H → Visible) :
    cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k))
      (H+1) (Fin.cons y w) =
      startupLaw p q r k 1 (fun _ => y) * pureLaw p q r (singletonState y) H w := by
  have hs : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
  change generatedLaw _ _ _ _ _ = _
  rw [generated_cons, cutoff_startup_row hp hne N k hk,
    cutoff_singleton_total p q r N _ y hs]
  change startupLaw p q r k 1 (fun _ => y) *
    cutoffLaw p q r N (some (.inl (singletonState y))) H w = _
  rw [pure_generated]

def cylinder (m : Nat) (F : LawProfile) : LawProfile :=
  match m with
  | 0 => F
  | m+1 => fun H w => match H with
    | 0 => 0
    | H+1 => if w 0 = B then cylinder m F H (fun j => w j.succ) else 0

lemma cylinder_zero (m : Nat) (F : LawProfile) (hF : ∀ w, F 0 w = 0)
    (w : Fin 0 → Visible) : cylinder m F 0 w = 0 := by
  cases m with
  | zero => exact hF w
  | succ m => rfl

lemma source_product_localization {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N k H : Nat) (hk : k ≤ N) (w : Fin H → Visible) :
    startupLaw p q r k H w -
      cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k)) H w =
      (T p q r N / T p q r k) *
        cylinder (N-k) (fun h v => startupLaw p q r N h v -
          pureLaw p q r (dominantState p q r) h v) H w := by
  induction H generalizing k with
  | zero =>
    rw [startup_zero hp]
    change 1 - 1 = _
    rw [cylinder_zero _ _ (by intro v; rw [startup_zero hp, pure_zero]; ring)]
    ring
  | succ H ih =>
    by_cases hkn : k = N
    · subst k
      have hn : ¬ N < N := by omega
      simp only [encodeSource, dif_neg hn, pure_generated, Nat.sub_self, cylinder,
        div_self (ne_of_gt (T_pos hp N)), one_mul]
    · have hlt : k < N := by omega
      have hm : N-k = (N-(k+1))+1 := by omega
      have hw : Fin.cons (w 0) (fun j => w j.succ) = w := by
        funext j; exact Fin.cases rfl (fun _ => rfl) j
      rw [← hw]
      by_cases hy : w 0 = B
      · rw [hy, startup_B hp, generated_startup_B hp hne N k H hlt,
          ← mul_sub, ih (k+1) (by omega), hm]
        simp only [cylinder, Fin.cons_zero, Fin.cons_succ, ite_true]
        field_simp [ne_of_gt (T_pos hp k), ne_of_gt (T_pos hp (k+1))]
      · rw [startup_singleton hp k H (w 0) hy,
          generated_startup_singleton hp hne N k H hlt (w 0) hy, sub_self, hm]
        simp only [cylinder, Fin.cons_zero, if_neg hy, mul_zero]

lemma cylinder_pre (m : Nat) (F : LawProfile) (hF : ∀ w, F 0 w = 0)
    (H : Nat) (hH : H ≤ m) (w : Fin H → Visible) : cylinder m F H w = 0 := by
  induction m generalizing H with
  | zero =>
    have h : H = 0 := by omega
    subst H
    exact hF w
  | succ m ih =>
    cases H with
    | zero => rfl
    | succ H =>
      simp only [cylinder]
      split_ifs
      · exact ih H (by omega) _
      · rfl

lemma precutoff_agreement {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) (H : Nat)
    (hH : H ≤ N-k.val) (w : Fin H → Visible) :
    cutoffLaw p q r N (some (.inr k)) H w =
      orientedMixture p q r (minority (theta p q r) k.val) H w := by
  have he := source_product_localization hp hne N k.val H k.isLt.le w
  rw [cylinder_pre _ _ (by intro v; rw [startup_zero hp, pure_zero]; ring) H hH,
    mul_zero] at he
  have hx := sub_eq_zero.mp he
  have hs := actual_oriented_startup hp hne k.val H w
  simpa only [encodeSource, dif_pos k.isLt, startupLaw] using hx.symm.trans hs

lemma cylinder_abs_sum (m : Nat) (F : LawProfile) (t : Nat) :
    (∑ w : Fin (t+m) → Visible, |cylinder m F (t+m) w|) =
      ∑ w : Fin t → Visible, |F t w| := by
  induction m with
  | zero => rfl
  | succ m ih =>
    conv_lhs => rw [← Nat.add_assoc]
    rw [sum_words_succ]
    simp only [cylinder, Fin.cons_zero, Fin.cons_succ]
    simp only [apply_ite abs, abs_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simpa using ih

lemma startup_dominant_finite {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (k H : Nat) :
    totalVariation (startupLaw p q r k H) (pureLaw p q r (dominantState p q r) H) =
      minority (theta p q r) k * (1-(min (a p q) (b r))^H) := by
  have ht := theta_bounds hp hne
  have hx : minority (theta p q r) k ∈ Set.Icc 0 1 :=
    ⟨(minority_positive ht.1 k).le,(minority_le_half ht.1.le ht.2.le k).trans (by norm_num)⟩
  have he : startupLaw p q r k = orientedMixture p q r (minority (theta p q r) k) := by
    funext H w; exact actual_oriented_startup hp hne k H w
  rw [he, dominant_law, dominant_as_zero, (oriented_geometry hp hx (by norm_num)).2.1 H,
    sub_zero, abs_of_pos (minority_positive ht.1 k)]

lemma transient_shift_tv {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) (t : Nat) :
    totalVariation (startupLaw p q r k.val (t+(N-k.val)))
      (cutoffLaw p q r N (some (.inr k)) (t+(N-k.val))) =
      (T p q r N / T p q r k.val) *
        totalVariation (startupLaw p q r N t) (pureLaw p q r (dominantState p q r) t) := by
  have hs : 0 ≤ T p q r N / T p q r k.val := (div_pos (T_pos hp N) (T_pos hp k.val)).le
  have he (w : Fin (t+(N-k.val)) → Visible) :=
    source_product_localization hp hne N k.val (t+(N-k.val)) k.isLt.le w
  simp only [encodeSource, dif_pos k.isLt] at he
  simp only [totalVariation, he, abs_mul, abs_of_nonneg hs, ← Finset.mul_sum]
  rw [cylinder_abs_sum]
  ring

lemma transient_finite_tv {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) (H : Nat) :
    totalVariation (startupLaw p q r k.val H) (cutoffLaw p q r N (some (.inr k)) H) =
      if H ≤ N-k.val then 0 else
        (T p q r N / T p q r k.val) * minority (theta p q r) N *
          (1-(min (a p q) (b r))^(H-(N-k.val))) := by
  by_cases hH : H ≤ N-k.val
  · rw [if_pos hH]
    have he : cutoffLaw p q r N (some (.inr k)) H = startupLaw p q r k.val H := by
      funext w
      exact (precutoff_agreement hp hne N k H hH w).trans
        (actual_oriented_startup hp hne k.val H w).symm
    rw [he]
    simp [totalVariation]
  · rw [if_neg hH]
    have hlen : H = (H-(N-k.val))+(N-k.val) := by omega
    conv_lhs => rw [hlen]
    rw [transient_shift_tv hp hne, startup_dominant_finite hp hne]
    ring

lemma transient_profile_distance {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) :
    profileDistance (startupLaw p q r k.val) (cutoffLaw p q r N (some (.inr k))) =
      (T p q r N / T p q r k.val) * minority (theta p q r) N := by
  let S := T p q r N / T p q r k.val
  have hs : 0 < S := div_pos (T_pos hp N) (T_pos hp k.val)
  have ht := theta_bounds hp hne
  have hd := (actual_startup_geometry hp hne N N).2.2
  have hD := (generated_coherent (cutoffGenerator hp hne N) (some (.inr k))).1
  have hF := (actual_coherent hp _ (startup_history_positive hp k.val)).1
  apply le_antisymm
  · apply profile_le
    intro H
    rw [transient_finite_tv hp hne]
    split_ifs
    · exact mul_nonneg hs.le (minority_positive ht.1 N).le
    · have hu : 0 ≤ min (a p q) (b r) := le_min (holding_bounds hp).1.le (holding_bounds hp).2.2.1.le
      have hx := mul_nonneg hs.le (minority_positive ht.1 N).le
      nlinarith [mul_nonneg hx (pow_nonneg hu (H-(N-k.val)))]
  · have hr : profileDistance (startupLaw p q r N) (pureLaw p q r (dominantState p q r)) ≤
        profileDistance (startupLaw p q r k.val) (cutoffLaw p q r N (some (.inr k))) / S := by
      apply profile_le
      intro t
      apply (le_div_iff₀ hs).mpr
      have hb := finite_le_profile hF hD (t+(N-k.val))
      change totalVariation (startupLaw p q r k.val (t+(N-k.val)))
        (cutoffLaw p q r N (some (.inr k)) (t+(N-k.val))) ≤
        profileDistance (startupLaw p q r k.val) (cutoffLaw p q r N (some (.inr k))) at hb
      rw [transient_shift_tv hp hne] at hb
      simpa [S, mul_comm] using hb
    rw [dominant_law] at hr
    change profileDistance (actualFutureWordWeight p q r (List.replicate (N+1) B))
      (dominantLaw p q r) ≤ _ at hr
    rw [hd] at hr
    have he := (le_div_iff₀ hs).mp hr
    simpa [S,mul_comm] using he

lemma minority_power_ratio {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (k : Nat) :
    minority (theta p q r) k = (min (a p q) (b r))^k / T p q r k := by
  have hc := oriented_startup_coordinate hp hne k
  by_cases hab : b r < a p q
  · rw [if_pos hab] at hc
    have he : minority (theta p q r) k = 1-startupCoordinate p q r k := by linarith
    rw [he, min_eq_right hab.le]
    have ht : (a p q)^k+(b r)^k ≠ 0 := ne_of_gt (T_pos hp k)
    unfold startupCoordinate T
    field_simp [ht]
    ring
  · rw [if_neg hab] at hc
    rw [← hc, min_eq_left (le_of_not_gt hab)]
    rfl

lemma T_antitone {p q r : ℝ} (hp : admissible p q r) (k N : Nat) (hk : k ≤ N) :
    T p q r N ≤ T p q r k := by
  have hn : N = k+(N-k) := by omega
  have ha := mul_le_of_le_one_right (pow_pos (holding_bounds hp).1 k).le
    (pow_le_one₀ (n := N-k) (holding_bounds hp).1.le (holding_bounds hp).2.1.le)
  have hb := mul_le_of_le_one_right (pow_pos (holding_bounds hp).2.2.1 k).le
    (pow_le_one₀ (n := N-k) (holding_bounds hp).2.2.1.le (holding_bounds hp).2.2.2.1.le)
  unfold T
  conv_lhs => rw [hn,pow_add,pow_add]
  exact add_le_add ha hb

lemma transient_gain {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (k : Fin N) :
    (T p q r N/T p q r k.val)*minority (theta p q r) N =
      (min (a p q) (b r))^N/T p q r k.val ∧
    (T p q r N/T p q r k.val)*minority (theta p q r) N ≤ minority (theta p q r) N := by
  constructor
  · rw [minority_power_ratio hp hne]
    field_simp [ne_of_gt (T_pos hp N),ne_of_gt (T_pos hp k.val)]
  · apply mul_le_of_le_one_left (minority_positive (theta_bounds hp hne).1 N).le
    exact (div_le_one (T_pos hp k.val)).mpr (T_antitone hp _ _ k.isLt.le)

lemma empty_singleton_cons (p q r : ℝ) (H : Nat) (y : Visible) (hy : y ≠ B)
    (w : Fin H → Visible) :
    emptyLaw p q r (H+1) (Fin.cons y w) = (1/5)*pureLaw p q r (singletonState y) H w := by
  have hs : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
  unfold emptyLaw
  rw [initialWordWeight]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [filter_singleton uniformPi y hs, future_word_scale]
  rcases hs with rfl | rfl | rfl
  all_goals simp [uniformPi, singletonState, pureLaw]

lemma empty_B_startup {p q r : ℝ} (hp : admissible p q r) (H : Nat) (w : Fin H → Visible) :
    emptyLaw p q r (H+1) (Fin.cons B w) = (2/5)*startupLaw p q r 0 H w := by
  rw [empty_B_word]
  simp only [startupLaw,actual_startup_mixture hp, startupCoordinate,pow_zero]
  unfold mixtureLaw
  ring

lemma initial_difference {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) (H : Nat)
    (y : Visible) (w : Fin H → Visible) :
    emptyLaw p q r (H+1) (Fin.cons y w)-cutoffLaw p q r N none (H+1) (Fin.cons y w) =
      if y = B then (2/5)*(startupLaw p q r 0 H w-cutoffLaw p q r N (some (.inr ⟨0,hN⟩)) H w) else 0 := by
  change _ - generatedLaw _ _ _ _ _ = _
  rw [generated_cons]
  by_cases hy : y = B
  · subst y
    rw [if_pos rfl, empty_B_startup hp]
    have hu : sharpUpdate (dominantState p q r) N none B = some (.inr ⟨0,hN⟩) := by
      simp [sharpUpdate,representative,sourceUpdate,encodeSource,hN,B]
    rw [hu]
    change _ -(2/5)*cutoffLaw p q r N (some (.inr ⟨0,hN⟩)) H w = _
    ring
  · rw [if_neg hy,empty_singleton_cons p q r H y hy]
    have hs : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
    rw [cutoff_singleton_total p q r N none y hs]
    change _ - cutoffRows p q r N none y * cutoffLaw p q r N (some (.inl (singletonState y))) H w = 0
    rw [pure_generated]
    simp [cutoffRows,hy]

lemma initial_succ_tv {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) (H : Nat) :
    totalVariation (emptyLaw p q r (H+1)) (cutoffLaw p q r N none (H+1)) =
      (2/5)*totalVariation (startupLaw p q r 0 H)
        (cutoffLaw p q r N (some (.inr ⟨0,hN⟩)) H) := by
  unfold totalVariation
  rw [sum_words_succ]
  simp only [initial_difference hp hne N hN, apply_ite abs, abs_zero, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2/5), ← Finset.mul_sum,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp
  ring

lemma initial_finite_tv {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) (H : Nat) :
    totalVariation (emptyLaw p q r H) (cutoffLaw p q r N none H) =
      if H ≤ N+1 then 0 else (min (a p q) (b r))^N/5 *
        (1-(min (a p q) (b r))^(H-(N+1))) := by
  cases H with
  | zero => simp [emptyLaw,initialWordWeight,uniformPi,generatedLaw,cutoffLaw,totalVariation,Fin.sum_univ_succ]
  | succ H =>
    rw [initial_succ_tv hp hne N hN,transient_finite_tv hp hne N ⟨0,hN⟩ H]
    have he := (transient_gain hp hne N ⟨0,hN⟩).1
    change (T p q r N/T p q r 0)*minority (theta p q r) N =
      (min (a p q) (b r))^N/T p q r 0 at he
    by_cases h : H ≤ N
    · simp [h,show H+1 ≤ N+1 by omega]
    · simp only [if_neg h,if_neg (show ¬ H+1 ≤ N+1 by omega), Fin.val_zero,Nat.sub_zero]
      have hexp : H+1-(N+1) = H-N := by omega
      rw [hexp]
      rw [← mul_assoc,he]
      norm_num [T]

lemma initial_profile_distance {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) :
    profileDistance (emptyLaw p q r) (cutoffLaw p q r N none) = (min (a p q) (b r))^N/5 := by
  have hd := transient_profile_distance hp hne N ⟨0,hN⟩
  have hg := (transient_gain hp hne N ⟨0,hN⟩).1
  have hzero : T p q r 0 = 2 := by norm_num [T]
  rw [hzero] at hg
  have hu : 0 ≤ min (a p q) (b r) := le_min (holding_bounds hp).1.le (holding_bounds hp).2.2.1.le
  apply le_antisymm
  · apply profile_le
    intro H
    rw [initial_finite_tv hp hne N hN]
    split_ifs
    · positivity
    · have hx := div_nonneg (pow_nonneg hu N) (by norm_num : (0:ℝ) ≤ 5)
      nlinarith [mul_nonneg hx (pow_nonneg hu (H-(N+1)))]
  · have hr : profileDistance (startupLaw p q r 0) (cutoffLaw p q r N (some (.inr ⟨0,hN⟩))) ≤
        profileDistance (emptyLaw p q r) (cutoffLaw p q r N none)/(2/5) := by
      apply profile_le
      intro H
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2/5)).mpr
      have hb := finite_le_profile (empty_probability hp)
        (generated_coherent (cutoffGenerator hp hne N) none).1 (H+1)
      change totalVariation (emptyLaw p q r (H+1)) (cutoffLaw p q r N none (H+1)) ≤
        profileDistance (emptyLaw p q r) (cutoffLaw p q r N none) at hb
      rw [initial_succ_tv hp hne N hN] at hb
      simpa [mul_comm] using hb
    rw [hd] at hr
    have hh := (le_div_iff₀ (by norm_num : (0:ℝ) < 2/5)).mp hr
    change (T p q r N / T p q r 0 * minority (theta p q r) N)*(2/5) ≤ _ at hh
    rw [hzero,hg] at hh
    nlinarith

lemma initial_gain_le {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) :
    (min (a p q) (b r))^N/5 ≤ minority (theta p q r) N := by
  have hg := transient_gain hp hne N ⟨0,hN⟩
  have hzero : T p q r 0 = 2 := by norm_num [T]
  simp only [Fin.val_zero,hzero] at hg
  have hx := (minority_positive (theta_bounds hp hne).1 N).le
  nlinarith [hg.1,hg.2]

lemma saturated_profile {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N k : Nat) (hk : N ≤ k) :
    profileDistance (startupLaw p q r k)
      (cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k))) =
      minority (theta p q r) k := by
  have he : cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k)) =
      pureLaw p q r (dominantState p q r) := by
    funext H w
    simpa only [encodeSource,dif_neg (not_lt_of_ge hk)] using pure_generated p q r N (dominantState p q r) H w
  rw [he,dominant_law]
  exact (actual_startup_geometry hp hne k k).2.2

lemma pure_history_exact {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (h : List Visible) (hn : h ≠ [])
    (i : State) (hr : sourceRun h = .pure i) (hpost : acquiredPosterior p q r h = pureVector i) :
    (cutoffGenerator hp hne N).toObserver.decoder ((cutoffGenerator hp hne N).toObserver.run h) =
      actualFutureWordWeight p q r h := by
  rw [cutoff_run_is_actual hp hne N h,hr]
  funext H w
  change cutoffLaw p q r N (some (.inl i)) H w = _
  rw [pure_generated]
  simp only [actualFutureWordWeight,if_neg hn,hpost,pureLaw]

lemma cutoff_history_profile {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N)
    (h : List Visible) (hpos : 0 < historyMass p q r h) :
    profileDistance (actualFutureWordWeight p q r h)
      ((cutoffGenerator hp hne N).toObserver.decoder ((cutoffGenerator hp hne N).toObserver.run h)) ≤
      minority (theta p q r) N := by
  by_cases hn : h = []
  · subst h
    change profileDistance (emptyLaw p q r) (cutoffLaw p q r N none) ≤ _
    rw [initial_profile_distance hp hne N hN]
    exact initial_gain_le hp hne N hN
  · rcases positive_history_classification p q r h hn hpos with hs | hpure
    · rcases hs with ⟨k,rfl,hr,_⟩
      rw [cutoff_run_is_actual hp hne N _,hr]
      change profileDistance (startupLaw p q r k)
        (cutoffLaw p q r N (encodeSource (dominantState p q r) N (.startup k))) ≤ _
      by_cases hk : k < N
      · simp only [encodeSource,dif_pos hk]
        rw [transient_profile_distance hp hne N ⟨k,hk⟩]
        exact (transient_gain hp hne N ⟨k,hk⟩).2
      · rw [saturated_profile hp hne N k (by omega)]
        exact (minority_strictAnti (theta_bounds hp hne).1 (theta_bounds hp hne).2).antitone (by omega)
    · rcases hpure with ⟨i,hr,hpost⟩
      rw [pure_history_exact hp hne N h hn i hr hpost,profile_distance_eq_zero_of_eq rfl]
      exact (minority_positive (theta_bounds hp hne).1 N).le

lemma cutoff_accuracy {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (N : Nat) (hN : 0 < N) :
    (cutoffGenerator hp hne N).toObserver.Accurate p q r (minority (theta p q r) N) true := by
  intro h hpos _ H
  exact (finite_le_profile (actual_coherent hp h hpos).1
    (generated_coherent (cutoffGenerator hp hne N) _).1 H).trans
      (cutoff_history_profile hp hne N hN h hpos)

def N1 (p q r ε : ℝ) : Nat := cutoff (theta p q r) ε

lemma N1_threshold {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    0 < N1 p q r ε ∧ minority (theta p q r) (N1 p q r ε) ≤ ε ∧
    (∀ i < N1 p q r ε, ε < minority (theta p q r) i) ∧
    (∀ k, minority (theta p q r) k ≤ ε ↔ N1 p q r ε ≤ k) ∧
    (minority (theta p q r) (N1 p q r ε) = ε ↔
      Real.log ((1-ε)/ε)/|Real.log (theta p q r)| = (N1 p q r ε : ℝ)) := by
  have ht := theta_bounds hp hne
  have he : 0 < ε := by linarith
  have he1 : ε < 1/2 := by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
  exact cutoff_first_nonstrict ht.1 ht.2 he he1

lemma N1_generator_accuracy {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    (cutoffGenerator hp hne (N1 p q r ε)).toObserver.Accurate p q r ε true := by
  have ht := N1_threshold hp hne hε hεk
  intro h hpos hquery H
  exact (cutoff_accuracy hp hne _ ht.1 h hpos hquery H).trans ht.2.1

lemma generated_competing_lower {Z : Type*} [Fintype Z] (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true) : 6+N2 p q r ε ≤ Fintype.card Z :=
  (universal_unequal_lower_bound hp hne hε hεk (generated_coherent O) hacc).1

def transport {Z W : Type*} (e : Z ≃ W) (O : GeneratedObserver Z) : GeneratedObserver W where
  initial := e O.initial
  update := fun z y => e (O.update (e.symm z) y)
  row := fun z y => O.row (e.symm z) y
  row_nonneg := fun z y => O.row_nonneg (e.symm z) y
  row_sum := fun z => O.row_sum (e.symm z)

lemma transport_law {Z W : Type*} (e : Z ≃ W) (O : GeneratedObserver Z)
    (z : Z) (H : Nat) (w : Fin H → Visible) :
    (transport e O).toObserver.decoder (e z) H w = O.toObserver.decoder z H w := by
  induction H generalizing z with
  | zero => rfl
  | succ H ih =>
    change O.row (e.symm (e z)) (w 0) *
      (transport e O).toObserver.decoder (e (O.update (e.symm (e z)) (w 0))) H (fun i => w i.succ) = _
    rw [e.symm_apply_apply,ih]
    rfl

lemma transport_run {Z W : Type*} (e : Z ≃ W) (O : GeneratedObserver Z) (h : List Visible) :
    (transport e O).toObserver.run h = e (O.toObserver.run h) := by
  unfold Observer.run
  exact List.foldl_hom e (l := h) (init := O.initial) (by intro z y; simp [transport,GeneratedObserver.toObserver])

lemma transport_accurate {Z W : Type*} (e : Z ≃ W) (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hacc : O.toObserver.Accurate p q r ε true) :
    (transport e O).toObserver.Accurate p q r ε true := by
  intro h hpos hquery H
  have he : (transport e O).toObserver.decoder ((transport e O).toObserver.run h) H =
      O.toObserver.decoder (O.toObserver.run h) H := by
    rw [transport_run]
    funext w; exact transport_law e O _ H w
  rw [he]
  exact hacc h hpos hquery H

def Attainable (p q r ε : ℝ) (n : Nat) : Prop :=
  ∃ O : GeneratedObserver (Fin n), O.toObserver.Accurate p q r ε true

lemma attainable_constructed {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    Attainable p q r ε (6+N1 p q r ε) := by
  let e : SharpState (N1 p q r ε) ≃ Fin (6+N1 p q r ε) :=
    (Fintype.equivFin _).trans (finCongr (sharp_state_card _))
  exact ⟨transport e (cutoffGenerator hp hne _),
    transport_accurate e _ (N1_generator_accuracy hp hne hε hεk)⟩

lemma attainable_nonempty {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) : ∃ n, Attainable p q r ε n :=
  ⟨6+N1 p q r ε,attainable_constructed hp hne hε hεk⟩

def minimum {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) : Nat :=
  Nat.find (attainable_nonempty hp hne hε hεk)

lemma minimum_attained {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    Attainable p q r ε (minimum hp hne hε hεk) :=
  Nat.find_spec (attainable_nonempty hp hne hε hεk)

lemma minimum_le {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) (n : Nat) (hn : Attainable p q r ε n) :
    minimum hp hne hε hεk ≤ n := Nat.find_min' _ hn

lemma minimum_of_any_carrier {Z : Type*} [Fintype Z] (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true) : minimum hp hne hε hεk ≤ Fintype.card Z := by
  exact minimum_le hp hne hε hεk _ ⟨transport (Fintype.equivFin Z) O,
    transport_accurate _ O hacc⟩

lemma initialized_generated_minimum {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    Attainable p q r ε (minimum hp hne hε hεk) ∧
    (∀ n, Attainable p q r ε n → minimum hp hne hε hεk ≤ n) ∧
    6+N2 p q r ε ≤ minimum hp hne hε hεk ∧
    minimum hp hne hε hεk ≤ 6+N1 p q r ε ∧
    (N1 p q r ε = N2 p q r ε → minimum hp hne hε hεk = 6+N1 p q r ε) := by
  have hatt := minimum_attained hp hne hε hεk
  have hl : 6+N2 p q r ε ≤ minimum hp hne hε hεk := by
    rcases hatt with ⟨O,hO⟩
    simpa using generated_competing_lower O hp hne hε hεk hO
  have hu : minimum hp hne hε hεk ≤ 6+N1 p q r ε := by
    simpa only [sharp_state_card] using minimum_of_any_carrier
      (cutoffGenerator hp hne (N1 p q r ε)) hp hne hε hεk (N1_generator_accuracy hp hne hε hεk)
  exact ⟨minimum_attained hp hne hε hεk,minimum_le hp hne hε hεk,hl,hu,
    fun he => by omega⟩

end
end D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
