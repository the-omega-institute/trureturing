/- GID: D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent finite word laws and exact acquired-history source updating. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource

abbrev State := Fin 5
abbrev Visible := Fin 4

/-- The visible code `2` is the symbol `B`; the other codes are `0,1,3`. -/
def B : Visible := 2

def transition (p q r : ℝ) : Matrix State State ℝ :=
  ![![1-p-q-r,p,0,q,r],
    ![q,1-p-q,p,0,0],
    ![0,q,1-p-q,p,0],
    ![p,0,q,1-p-q,0],
    ![r,0,0,0,1-r]]

def observation : State → Visible := ![0,1,2,3,2]

def admissible (p q r : ℝ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < r ∧ p + q + r < 1

def a (p q : ℝ) : ℝ := 1 - p - q
def b (r : ℝ) : ℝ := 1 - r
def c (p q r : ℝ) : ℝ := 1 - p - q - r

noncomputable def uniformPi : State → ℝ := fun _ => (1 / 5 : ℝ)

/-- The source transition is represented by the literal five-by-five matrix. -/
theorem transition_row_stochastic {p q r : ℝ} :
    ∀ i : State, ∑ j : State, transition p q r i j = 1 := by
  intro i
  fin_cases i <;> norm_num [transition, Fin.sum_univ_succ] <;> ring

/-- The same strict parameter domain makes every matrix entry nonnegative. -/
theorem transition_nonnegative {p q r : ℝ} (h : admissible p q r) :
    ∀ i j : State, 0 ≤ transition p q r i j := by
  rcases h with ⟨hp, hq, hr, hpqr⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transition] <;> linarith

/-- Uniform stationarity is checked against the literal columns, before any
future-law simplification is used. -/
theorem uniform_stationary {p q r : ℝ} :
    ∀ j : State, ∑ i : State, uniformPi i * transition p q r i j = uniformPi j := by
  intro j
  fin_cases j <;> norm_num [uniformPi, transition, Fin.sum_univ_succ] <;> ring

def filterAt (v : State → ℝ) (y : Visible) : State → ℝ :=
  fun i => if observation i = y then v i else 0

def advance (p q r : ℝ) (v : State → ℝ) : State → ℝ :=
  fun j => ∑ i : State, v i * transition p q r i j

/-- Future words advance before every read. The initialized law below filters
the initial state before advancing for the remaining chronological reads. -/
def futureWordWeight (p q r : ℝ) (v : State → ℝ) :
    (n : Nat) → (Fin n → Visible) → ℝ
  | 0, _ => ∑ i : State, v i
  | n + 1, w =>
      futureWordWeight p q r
        (filterAt (advance p q r v) (w 0)) n (fun k => w k.succ)

def initialWordWeight (p q r : ℝ) (v : State → ℝ) :
    (n : Nat) → (Fin n → Visible) → ℝ
  | 0, _ => ∑ i : State, v i
  | n + 1, w =>
      futureWordWeight p q r (filterAt v (w 0)) n (fun k => w k.succ)

def totalFutureWeight (p q r : ℝ) (v : State → ℝ) : Nat → ℝ
  | 0 => ∑ i : State, v i
  | n + 1 =>
      ∑ y : Visible,
        totalFutureWeight p q r
          (filterAt (advance p q r v) y) n

lemma sum_filterAt (v : State → ℝ) (i : State) :
    ∑ y : Visible, filterAt v y i = v i := by
  fin_cases i <;> simp [filterAt, observation, Fin.sum_univ_succ]

lemma sum_filterAt_total (v : State → ℝ) :
    ∑ y : Visible, ∑ i : State, filterAt v y i = ∑ i : State, v i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_filterAt v i

lemma sum_advance {p q r : ℝ} (v : State → ℝ) :
    ∑ j : State, advance p q r v j = ∑ i : State, v i := by
  simp only [advance]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum, transition_row_stochastic i, mul_one]

/-- Summing the recursive finite-word law over the next visible symbol preserves
its total mass. This is the finite-word normalization bridge used at every H. -/
theorem total_future_normalized {p q r : ℝ}
    (v : State → ℝ) (n : Nat) :
    totalFutureWeight p q r v n = ∑ i : State, v i := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [totalFutureWeight]
      rw [Finset.sum_congr rfl]
      · apply Eq.trans (sum_filterAt_total (fun i => advance p q r v i))
        exact sum_advance v
      · intro y hy
        exact ih (filterAt (advance p q r v) y)

/-- The two observed words used to expose the rare transitions have their
literal source masses. -/
theorem witness_word_masses {p q r : ℝ} :
    initialWordWeight p q r uniformPi 1 (fun _ => (0 : Visible)) = 1 / 5 ∧
    initialWordWeight p q r uniformPi 1 (fun _ => (1 : Visible)) = 1 / 5 ∧
    initialWordWeight p q r uniformPi 1 (fun _ => (3 : Visible)) = 1 / 5 ∧
    initialWordWeight p q r uniformPi 2 (fun k => if k = 0 then (1 : Visible) else B) = p / 5 ∧
    initialWordWeight p q r uniformPi 2 (fun k => if k = 0 then (0 : Visible) else B) = r / 5 := by
  norm_num [initialWordWeight, futureWordWeight, filterAt, advance, uniformPi,
    observation, B, transition, Fin.sum_univ_succ]
  repeat' first | ring | simp

noncomputable def startupVector (p q r : ℝ) (k : Nat) : State → ℝ :=
  ![0, 0, (a p q) ^ k / 5, 0, (b r) ^ k / 5]

lemma startup_vector_step {p q r : ℝ} (k : Nat) :
    filterAt (advance p q r (startupVector p q r k)) B =
      startupVector p q r (k + 1) := by
  funext i
  fin_cases i <;>
    simp [startupVector, filterAt, observation, B, advance, transition, a, b,
      Fin.sum_univ_succ] <;> ring

lemma initial_filter_B (p q r : ℝ) :
    filterAt uniformPi B = startupVector p q r 0 := by
  funext i
  fin_cases i <;>
    norm_num [filterAt, observation, B, uniformPi, startupVector] <;> decide

/-- The all-`B` cylinder has exactly the two compatible hidden paths. Its
weight is the sum of their literal powers, with the initial factor 1/5. -/
theorem all_b_mass {p q r : ℝ} (k : Nat) :
    initialWordWeight p q r uniformPi (k + 1) (fun _ => B) =
      ((a p q) ^ k + (b r) ^ k) / 5 := by
  have hvec : ∀ (j n : Nat),
      futureWordWeight p q r (startupVector p q r j) n (fun _ => B) =
        ((a p q) ^ j * (a p q) ^ n + (b r) ^ j * (b r) ^ n) / 5 := by
    intro j n
    induction n generalizing j with
    | zero =>
        norm_num [futureWordWeight, startupVector, Fin.sum_univ_succ]
        ring
    | succ n ihn =>
        simp only [futureWordWeight]
        rw [startup_vector_step j, ihn (j + 1)]
        rw [pow_succ, pow_succ]
        ring
  change futureWordWeight p q r (filterAt uniformPi B) k (fun _ => B) = _
  rw [initial_filter_B p q r, hvec 0 k]
  simp only [pow_zero, one_mul]

noncomputable def normalizeVector (v : State → ℝ) : State → ℝ :=
  fun i => v i / ∑ j : State, v j

noncomputable def posteriorAfterRead (p q r : ℝ) (v : State → ℝ) (y : Visible) : State → ℝ :=
  normalizeVector (filterAt (advance p q r v) y)

/-- Normalizing the explicit power vector gives coordinate `a^k/(a^k+b^k)`
on state 2 and its complement on state 4. -/
theorem all_b_posterior {p q r : ℝ} (h : admissible p q r) (k : Nat) :
    normalizeVector (startupVector p q r k) =
      (fun i => if i = 2 then (a p q) ^ k / ((a p q) ^ k + (b r) ^ k)
        else if i = 4 then (b r) ^ k / ((a p q) ^ k + (b r) ^ k) else 0) := by
  rcases h with ⟨hp, hq, hr, hpqr⟩
  have ha : 0 < a p q := by dsimp [a]; linarith
  have hb : 0 < b r := by dsimp [b]; linarith
  have hden : (a p q) ^ k + (b r) ^ k ≠ 0 := by
    positivity
  funext i
  fin_cases i <;>
    simp [normalizeVector, startupVector, Fin.sum_univ_succ, hden] <;>
    field_simp [hden] <;> ring

theorem all_b_positive {p q r : ℝ} (h : admissible p q r) (k : Nat) :
    0 < initialWordWeight p q r uniformPi (k + 1) (fun _ => B) := by
  rw [all_b_mass k]
  rcases h with ⟨hp, hq, hr, hpqr⟩
  have ha : 0 < a p q := by dsimp [a]; linarith
  have hb : 0 < b r := by dsimp [b]; linarith
  positivity

/-- The exact source update tags distinguish startup, pure modes, and the
singleton-reset rule. The definitions are total on impossible extensions. -/
inductive SourceTag where
  | start
  | startup (k : Nat)
  | pure (i : State)
  deriving DecidableEq, Repr

def sourceUpdate : SourceTag → Visible → SourceTag
  | _, 0 => .pure 0
  | _, 1 => .pure 1
  | _, 3 => .pure 3
  | .start, 2 => .startup 0
  | .startup k, 2 => .startup (k + 1)
  | .pure 0, 2 => .pure 4
  | .pure 4, 2 => .pure 4
  | .pure 1, 2 => .pure 2
  | .pure 2, 2 => .pure 2
  | .pure 3, 2 => .pure 2

lemma singleton_resets (z : SourceTag) (j : Visible) (hj : j = 0 ∨ j = 1 ∨ j = 3) :
    sourceUpdate z j = .pure (if j = 0 then 0 else if j = 1 then 1 else 3) := by
  rcases hj with rfl | rfl | rfl <;> rfl

lemma startup_all_b (k : Nat) :
    List.foldl sourceUpdate .start (List.replicate (k + 1) B) = .startup k := by
  have hstartup : ∀ (j m : Nat),
      List.foldl sourceUpdate (.startup j) (List.replicate m B) = .startup (j + m) := by
    intro j m
    induction m generalizing j with
    | zero => simp
    | succ m ihm =>
        change List.foldl sourceUpdate (.startup (j + 1))
          (List.replicate m B) = .startup (j + (m + 1))
        rw [ihm (j + 1)]
        congr 1
        omega
  change List.foldl sourceUpdate (.startup 0) (List.replicate k B) = .startup k
  simpa using hstartup 0 k

/-- Chronological unnormalized state weights after future reads. -/
def futureStateWeights (p q r : ℝ) (v : State → ℝ) : List Visible → State → ℝ
  | [] => v
  | y :: t => futureStateWeights p q r (filterAt (advance p q r v) y) t

/-- The first acquired read filters pi; every later read advances then filters. -/
noncomputable def acquiredStateWeights (p q r : ℝ) : List Visible → State → ℝ
  | [] => uniformPi
  | y :: t => futureStateWeights p q r (filterAt uniformPi y) t

noncomputable def historyMass (p q r : ℝ) (h : List Visible) : ℝ :=
  ∑ i : State, acquiredStateWeights p q r h i

noncomputable def acquiredPosterior (p q r : ℝ) (h : List Visible) : State → ℝ :=
  normalizeVector (acquiredStateWeights p q r h)

lemma future_state_mass (p q r : ℝ) (v : State → ℝ) (n : Nat)
    (w : Fin n → Visible) :
    (∑ i : State, futureStateWeights p q r v (List.ofFn w) i) =
      futureWordWeight p q r v n w := by
  induction n generalizing v with
  | zero => simp [List.ofFn_zero, futureStateWeights, futureWordWeight]
  | succ n ih =>
      rw [List.ofFn_succ]
      exact ih (filterAt (advance p q r v) (w 0)) (fun k => w k.succ)

/-- The state-weight recursion represents the literal initialized word law. -/
theorem acquired_mass_eq_word (p q r : ℝ) (n : Nat) (w : Fin n → Visible) :
    historyMass p q r (List.ofFn w) = initialWordWeight p q r uniformPi n w := by
  cases n with
  | zero => simp [historyMass, acquiredStateWeights, initialWordWeight]
  | succ n =>
      rw [List.ofFn_succ]
      exact future_state_mass p q r (filterAt uniformPi (w 0)) n (fun k => w k.succ)

lemma future_state_append (p q r : ℝ) (v : State → ℝ) (h t : List Visible) :
    futureStateWeights p q r v (h ++ t) =
      futureStateWeights p q r (futureStateWeights p q r v h) t := by
  induction h generalizing v with
  | nil => rfl
  | cons y h ih => exact ih (filterAt (advance p q r v) y)

lemma acquired_append (p q r : ℝ) (h t : List Visible) (hne : h ≠ []) :
    acquiredStateWeights p q r (h ++ t) =
      futureStateWeights p q r (acquiredStateWeights p q r h) t := by
  cases h with
  | nil => contradiction
  | cons y h => exact future_state_append p q r (filterAt uniformPi y) h t

lemma acquired_snoc (p q r : ℝ) (h : List Visible) (y : Visible) :
    acquiredStateWeights p q r (h ++ [y]) =
      filterAt (if h = [] then uniformPi else advance p q r (acquiredStateWeights p q r h)) y := by
  by_cases he : h = []
  · subst h; rfl
  · rw [acquired_append p q r h [y] he]
    simp [futureStateWeights, he]

lemma filter_scale (v : State → ℝ) (t : ℝ) (y : Visible) :
    filterAt (fun i => t * v i) y = fun i => t * filterAt v y i := by
  funext i; simp only [filterAt]; split_ifs <;> simp

lemma advance_scale (p q r : ℝ) (v : State → ℝ) (t : ℝ) :
    advance p q r (fun i => t * v i) = fun i => t * advance p q r v i := by
  funext j
  simp [advance, Finset.mul_sum, mul_assoc]

lemma future_state_scale (p q r : ℝ) (v : State → ℝ) (t : ℝ) (h : List Visible) :
    futureStateWeights p q r (fun i => t * v i) h =
      fun i => t * futureStateWeights p q r v h i := by
  induction h generalizing v with
  | nil => rfl
  | cons y h ih =>
      simp only [futureStateWeights, advance_scale, filter_scale]
      exact ih _

lemma future_word_scale (p q r : ℝ) (v : State → ℝ) (t : ℝ)
    (n : Nat) (w : Fin n → Visible) :
    futureWordWeight p q r (fun i => t * v i) n w =
      t * futureWordWeight p q r v n w := by
  rw [← future_state_mass, future_state_scale]
  simp only [← Finset.mul_sum]
  rw [future_state_mass]

/-- The quotient identity holds for every nonempty history and continuation.
On positive cylinders it is the conditional future law of the acquired state. -/
theorem actual_conditional_future (p q r : ℝ) (h : List Visible)
    (hne : h ≠ [])
    (H : Nat) (w : Fin H → Visible) :
    historyMass p q r (h ++ List.ofFn w) / historyMass p q r h =
      futureWordWeight p q r (acquiredPosterior p q r h) H w := by
  rw [historyMass, acquired_append p q r h _ hne, future_state_mass]
  unfold acquiredPosterior normalizeVector
  simp only [div_eq_mul_inv]
  have hs : (fun i => acquiredStateWeights p q r h i *
      (∑ j : State, acquiredStateWeights p q r h j)⁻¹) =
      (fun i => (∑ j : State, acquiredStateWeights p q r h j)⁻¹ *
        acquiredStateWeights p q r h i) := by funext i; ring
  rw [hs, future_word_scale]
  simp only [historyMass]
  ring

lemma filtered_nonnegative (v : State → ℝ) (hv : ∀ i, 0 ≤ v i) (y : Visible) :
    ∀ i, 0 ≤ filterAt v y i := by
  intro i; simp only [filterAt]; split_ifs
  · exact hv i
  · exact le_rfl

lemma advanced_nonnegative {p q r : ℝ} (hp : admissible p q r)
    (v : State → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ advance p q r v i := by
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (transition_nonnegative hp i j)

lemma future_state_nonnegative {p q r : ℝ} (hp : admissible p q r)
    (v : State → ℝ) (hv : ∀ i, 0 ≤ v i) (h : List Visible) :
    ∀ i, 0 ≤ futureStateWeights p q r v h i := by
  induction h generalizing v with
  | nil => exact hv
  | cons y h ih => exact ih _ (filtered_nonnegative _ (advanced_nonnegative hp v hv) _)

/-- Every finite future word has nonnegative mass on the admissible domain. -/
theorem future_word_nonnegative {p q r : ℝ} (hp : admissible p q r)
    (v : State → ℝ) (hv : ∀ i, 0 ≤ v i) (n : Nat) (w : Fin n → Visible) :
    0 ≤ futureWordWeight p q r v n w := by
  rw [← future_state_mass]
  exact Finset.sum_nonneg fun i _ => future_state_nonnegative hp v hv (List.ofFn w) i

/-- Every initialized finite word has nonnegative mass. -/
theorem initial_word_nonnegative {p q r : ℝ} (hp : admissible p q r)
    (n : Nat) (w : Fin n → Visible) :
    0 ≤ initialWordWeight p q r uniformPi n w := by
  cases n with
  | zero => norm_num [initialWordWeight, uniformPi, Fin.sum_univ_succ]
  | succ n =>
      exact future_word_nonnegative hp _
        (filtered_nonnegative uniformPi (by intro i; norm_num [uniformPi]) _) _ _

lemma sum_words_succ (n : Nat) (f : (Fin (n + 1) → Visible) → ℝ) :
    (∑ w : Fin (n + 1) → Visible, f w) =
      ∑ y : Visible, ∑ w : Fin n → Visible, f (Fin.cons y w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Visible)).sum_comp]
  exact Fintype.sum_prod_type _

/-- This is an actual sum over all words, not a recursively defined total. -/
theorem sum_future_words {p q r : ℝ}
    (v : State → ℝ) (n : Nat) :
    (∑ w : Fin n → Visible, futureWordWeight p q r v n w) = ∑ i : State, v i := by
  classical
  have ht : ∀ (n : Nat) (v : State → ℝ),
      (∑ w : Fin n → Visible, futureWordWeight p q r v n w) = totalFutureWeight p q r v n := by
    intro n
    induction n with
    | zero => intro v; simp [futureWordWeight, totalFutureWeight]
    | succ n ih =>
        intro v
        rw [sum_words_succ]
        simp only [futureWordWeight, Fin.cons_zero, Fin.cons_succ]
        simp_rw [ih]
        rfl
  rw [ht, total_future_normalized]

/-- piP=pi identifies the complete empty law with F_pi at every word;
its acquisition convention still begins with Y0. -/
theorem empty_boundary_and_positive_timing (p q r : ℝ) (H : Nat) (w : Fin H → Visible) :
    initialWordWeight p q r uniformPi H w = futureWordWeight p q r uniformPi H w := by
  have hs : advance p q r uniformPi = uniformPi := by funext j; exact uniform_stationary j
  cases H with
  | zero => rfl
  | succ H => simp only [initialWordWeight, futureWordWeight, hs]

/-- The initialized laws sum to one over the complete finite word space. -/
theorem sum_initial_words {p q r : ℝ} (n : Nat) :
    (∑ w : Fin n → Visible, initialWordWeight p q r uniformPi n w) = 1 := by
  simp_rw [empty_boundary_and_positive_timing]
  exact (sum_future_words uniformPi n).trans (by norm_num [uniformPi, Fin.sum_univ_succ])

/-- Each fixed prefix has its own final-symbol marginal identity. -/
theorem final_symbol_coherence {p q r : ℝ}
    (v : State → ℝ) (n : Nat) (w : Fin n → Visible) :
    (∑ y : Visible, futureWordWeight p q r v (n + 1) (Fin.snoc w y)) =
      futureWordWeight p q r v n w := by
  have he (y : Visible) : List.ofFn (Fin.snoc w y) = List.ofFn w ++ [y] := by
    rw [List.ofFn_succ']
    simp
  calc
    _ = ∑ y : Visible, ∑ i : State,
        filterAt (advance p q r (futureStateWeights p q r v (List.ofFn w))) y i := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← future_state_mass, he, future_state_append]
      rfl
    _ = ∑ i : State, futureStateWeights p q r v (List.ofFn w) i := by
      rw [sum_filterAt_total, sum_advance]
    _ = _ := future_state_mass p q r v n w

/-- Initialized prefix laws have pointwise deletion-of-last-read coherence. -/
theorem initial_final_symbol_coherence {p q r : ℝ}
    (n : Nat) (w : Fin n → Visible) :
    (∑ y : Visible, initialWordWeight p q r uniformPi (n + 1) (Fin.snoc w y)) =
      initialWordWeight p q r uniformPi n w := by
  simp_rw [empty_boundary_and_positive_timing]
  exact final_symbol_coherence uniformPi n w

noncomputable def pureVector (j : State) : State → ℝ := fun i => if i = j then 1 else 0

noncomputable def sourceWeights (p q r : ℝ) : SourceTag → State → ℝ
  | .start => uniformPi
  | .startup k => startupVector p q r k
  | .pure j => pureVector j

noncomputable def sourceProfile (p q r : ℝ) (z : SourceTag) : State → ℝ :=
  normalizeVector (sourceWeights p q r z)

def sourceRun (h : List Visible) : SourceTag := List.foldl sourceUpdate .start h

lemma source_update_ne_start (z : SourceTag) (y : Visible) : sourceUpdate z y ≠ .start := by
  cases z with
  | start => fin_cases y <;> simp [sourceUpdate]
  | startup k => fin_cases y <;> simp [sourceUpdate]
  | pure i => fin_cases i <;> fin_cases y <;> simp [sourceUpdate]

lemma source_run_ne_start (h : List Visible) (hne : h ≠ []) : sourceRun h ≠ .start := by
  have hf : ∀ (t : List Visible) (z : SourceTag), z ≠ .start →
      List.foldl sourceUpdate z t ≠ .start := by
    intro t
    induction t with
    | nil => intro z hz; exact hz
    | cons y t ih => intro z hz; exact ih _ (source_update_ne_start z y)
  cases h with
  | nil => contradiction
  | cons y t => exact hf t _ (source_update_ne_start .start y)

lemma source_run_snoc (h : List Visible) (y : Visible) :
    sourceRun (h ++ [y]) = sourceUpdate (sourceRun h) y := by
  simp [sourceRun, List.foldl_append]

lemma filter_singleton (v : State → ℝ) (y : Visible)
    (hy : y = 0 ∨ y = 1 ∨ y = 3) :
    filterAt v y = fun i => v (if y = 0 then 0 else if y = 1 then 1 else 3) *
      pureVector (if y = 0 then 0 else if y = 1 then 1 else 3) i := by
  rcases hy with rfl | rfl | rfl
  all_goals funext i; fin_cases i <;> simp [filterAt, observation, pureVector]

lemma source_weights_step (p q r : ℝ)
    (z : SourceTag) (y : Visible) :
    ∃ t : ℝ, filterAt (if z = .start then uniformPi else advance p q r (sourceWeights p q r z)) y =
      fun i => t * sourceWeights p q r (sourceUpdate z y) i := by
  by_cases hy : y = 0 ∨ y = 1 ∨ y = 3
  · rw [filter_singleton _ y hy, singleton_resets z y hy]
    exact ⟨_, rfl⟩
  · have hB : y = B := by fin_cases y <;> simp_all [B]
    subst y
    cases z with
    | start =>
        refine ⟨1, ?_⟩
        simpa [sourceWeights, sourceUpdate, B] using initial_filter_B p q r
    | startup k =>
        refine ⟨1, ?_⟩
        simpa [sourceWeights, sourceUpdate, B] using startup_vector_step k
    | pure j =>
        refine ⟨if j = 0 then r else if j = 4 then b r else
          if j = 1 then p else if j = 3 then q else a p q, ?_⟩
        funext i
        fin_cases j <;> fin_cases i <;>
          simp [sourceWeights, sourceUpdate, pureVector, filterAt, advance,
            observation, B, transition, Fin.sum_univ_succ, a, b]

/-- Every chronological acquired history, including impossible ones, lies on
its computed source-tag ray. The first read and all later reads use different
instruments exactly as prescribed by the source. -/
theorem acquired_source_ray (p q r : ℝ) (h : List Visible) :
    ∃ t : ℝ, acquiredStateWeights p q r h =
      fun i => t * sourceWeights p q r (sourceRun h) i := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨1, by simp [acquiredStateWeights, sourceRun, sourceWeights]⟩
  | append_singleton h y ih =>
      rw [acquired_snoc, source_run_snoc]
      rcases source_weights_step p q r (sourceRun h) y with ⟨s, hs⟩
      by_cases he : h = []
      · subst h
        refine ⟨s, ?_⟩
        simpa [sourceRun] using hs
      · rcases ih with ⟨t, ht⟩
        have hz := source_run_ne_start h he
        simp only [he, if_false, ht, advance_scale, filter_scale]
        simp only [hz, if_false] at hs
        rw [hs]
        exact ⟨t * s, by funext i; ring⟩

lemma normalize_scale (v : State → ℝ) (t : ℝ) (ht : t ≠ 0) :
    normalizeVector (fun i => t * v i) = normalizeVector v := by
  funext i
  simp only [normalizeVector, ← Finset.mul_sum]
  exact mul_div_mul_left (v i) (∑ j : State, v j) ht

/-- The computed total source update agrees with the current acquired state law
on every positive actual history, with no excluded rare histories. -/
theorem positive_history_invariant (p q r : ℝ)
    (h : List Visible) (hpos : 0 < historyMass p q r h) :
    acquiredPosterior p q r h = sourceProfile p q r (sourceRun h) := by
  rcases acquired_source_ray p q r h with ⟨t, ht⟩
  have ht0 : t ≠ 0 := by
    intro he
    simp [historyMass, ht, he] at hpos
  unfold acquiredPosterior sourceProfile
  rw [ht, normalize_scale _ t ht0]

lemma future_state_all_B (p q r : ℝ) (j n : Nat) :
    futureStateWeights p q r (startupVector p q r j) (List.replicate n B) =
      startupVector p q r (j + n) := by
  induction n generalizing j with
  | zero => simp [futureStateWeights]
  | succ n ih =>
      simp only [List.replicate_succ, futureStateWeights]
      rw [startup_vector_step, ih]
      congr 1
      omega

/-- The explicit power vector is the actual acquired all-B cylinder vector. -/
theorem acquired_all_B (p q r : ℝ) (k : Nat) :
    acquiredStateWeights p q r (List.replicate (k + 1) B) = startupVector p q r k := by
  simp only [List.replicate_succ, acquiredStateWeights]
  rw [initial_filter_B, future_state_all_B p q r]
  simp

/-- All-B posterior coordinates are tied to the acquired history itself. -/
theorem actual_all_B_posterior {p q r : ℝ} (hp : admissible p q r) (k : Nat) :
    acquiredPosterior p q r (List.replicate (k + 1) B) =
      fun i => if i = 2 then (a p q) ^ k / ((a p q) ^ k + (b r) ^ k)
        else if i = 4 then (b r) ^ k / ((a p q) ^ k + (b r) ^ k) else 0 := by
  unfold acquiredPosterior
  rw [acquired_all_B p q r, all_b_posterior hp]

lemma pure_profile (p q r : ℝ) (j : State) : sourceProfile p q r (.pure j) = pureVector j := by
  funext i
  simp [sourceProfile, sourceWeights, normalizeVector, pureVector]

lemma fold_pure (h : List Visible) (j : State) :
    ∃ i : State, List.foldl sourceUpdate (.pure j) h = .pure i := by
  induction h generalizing j with
  | nil => exact ⟨j, rfl⟩
  | cons y h ih =>
      have he : ∃ i : State, sourceUpdate (.pure j) y = .pure i := by
        fin_cases j <;> fin_cases y <;> simp [sourceUpdate]
      rcases he with ⟨i, hi⟩
      simpa [List.foldl_cons, hi] using ih i

/-- The first singleton resets the source to its identified state; every later
read keeps it pure. This quantifies arbitrary preceding and subsequent words. -/
theorem first_singleton_and_all_later (u t : List Visible) (y : Visible)
    (hy : y = 0 ∨ y = 1 ∨ y = 3) :
    ∃ i : State, sourceRun (u ++ y :: t) = .pure i := by
  simp only [sourceRun, List.foldl_append, List.foldl_cons]
  rw [singleton_resets _ y hy]
  exact fold_pure t _

/-- Every positive nonempty history is either an all-B startup cylinder or
is pure after a first singleton, exhaustively across the actual domain. -/
theorem positive_history_classification (p q r : ℝ)
    (h : List Visible) (hne : h ≠ []) (hpos : 0 < historyMass p q r h) :
    (∃ k : Nat, h = List.replicate (k + 1) B ∧ sourceRun h = .startup k ∧
      acquiredStateWeights p q r h = startupVector p q r k) ∨
    (∃ i : State, sourceRun h = .pure i ∧ acquiredPosterior p q r h = pureVector i) := by
  by_cases hall : ∀ y ∈ h, y = B
  · have hr : h = List.replicate h.length B := List.eq_replicate_of_mem hall
    have hl : 0 < h.length := List.length_pos_iff.mpr hne
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
    left
    refine ⟨k, ?_, ?_, ?_⟩
    · simpa [hk] using hr
    · rw [hr, hk]; exact startup_all_b k
    · rw [hr, hk]; exact acquired_all_B p q r k
  · push Not at hall
    rcases hall with ⟨y, hyh, hyB⟩
    obtain ⟨u, t, he⟩ := List.mem_iff_append.mp hyh
    have hy : y = 0 ∨ y = 1 ∨ y = 3 := by fin_cases y <;> simp_all [B]
    rcases first_singleton_and_all_later u t y hy with ⟨i, hi⟩
    right
    refine ⟨i, ?_, ?_⟩
    · simpa [he] using hi
    · rw [positive_history_invariant p q r h hpos, he, hi, pure_profile]


lemma acquired_state_nonnegative {p q r : ℝ} (hp : admissible p q r) (h : List Visible) :
    ∀ i, 0 ≤ acquiredStateWeights p q r h i := by
  cases h with
  | nil => intro i; norm_num [acquiredStateWeights, uniformPi]
  | cons y h =>
      exact future_state_nonnegative hp _
        (filtered_nonnegative uniformPi (by intro i; norm_num [uniformPi]) y) h

lemma empty_history_mass (p q r : ℝ) : historyMass p q r [] = 1 := by
  norm_num [historyMass, acquiredStateWeights, uniformPi, Fin.sum_univ_succ]

lemma posterior_probability {p q r : ℝ} (hp : admissible p q r)
    (h : List Visible) (hpos : 0 < historyMass p q r h) :
    (∀ i, 0 ≤ acquiredPosterior p q r h i) ∧ (∑ i : State, acquiredPosterior p q r h i) = 1 := by
  constructor
  · intro i
    exact div_nonneg (acquired_state_nonnegative hp h i) (le_of_lt hpos)
  · unfold acquiredPosterior normalizeVector
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

/-- Positive actual cylinders have a normalized, nonnegative conditional law
at every future horizon, equal word by word to the joint-cylinder quotient. -/
theorem actual_positive_conditional_law {p q r : ℝ} (hp : admissible p q r)
    (h : List Visible) (hne : h ≠ []) (hpos : 0 < historyMass p q r h)
    (H : Nat) (w : Fin H → Visible) :
    historyMass p q r (h ++ List.ofFn w) / historyMass p q r h =
      futureWordWeight p q r (acquiredPosterior p q r h) H w ∧
    (∑ u : Fin H → Visible, futureWordWeight p q r (acquiredPosterior p q r h) H u) = 1 ∧
    0 ≤ futureWordWeight p q r (acquiredPosterior p q r h) H w := by
  rcases posterior_probability hp h hpos with ⟨hnon, hsum⟩
  exact ⟨actual_conditional_future p q r h hne H w,
    (sum_future_words _ H).trans hsum, future_word_nonnegative hp _ hnon H w⟩

/-- The same conditioning identity in the literal fixed-length word notation. -/
theorem literal_conditional_future {p q r : ℝ} (hp : admissible p q r)
    (n : Nat) (hw : Fin n → Visible) (hn : 0 < n)
    (hpos : 0 < initialWordWeight p q r uniformPi n hw)
    (H : Nat) (w : Fin H → Visible) :
    initialWordWeight p q r uniformPi (n + H) (Fin.append hw w) /
        initialWordWeight p q r uniformPi n hw =
      futureWordWeight p q r (acquiredPosterior p q r (List.ofFn hw)) H w := by
  have hne : List.ofFn hw ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at this
    omega
  have hmass : 0 < historyMass p q r (List.ofFn hw) := by rwa [acquired_mass_eq_word]
  have hc := (actual_positive_conditional_law hp (List.ofFn hw) hne hmass H w).1
  rw [← List.ofFn_fin_append, acquired_mass_eq_word, acquired_mass_eq_word] at hc
  exact hc

noncomputable def actualFutureWordWeight (p q r : ℝ) (h : List Visible)
    (H : Nat) (w : Fin H → Visible) : ℝ :=
  if h = [] then initialWordWeight p q r uniformPi H w
  else futureWordWeight p q r (acquiredPosterior p q r h) H w

/-- At empty history the quotient starts with Y0; after positive acquired h
it starts with Y_length(h), using the posterior at the last acquired state. -/
theorem all_history_conditional_identity (p q r : ℝ) (h : List Visible)
    (H : Nat) (w : Fin H → Visible) :
    historyMass p q r (h ++ List.ofFn w) / historyMass p q r h =
      actualFutureWordWeight p q r h H w := by
  by_cases he : h = []
  · subst h
    simp [actualFutureWordWeight, empty_history_mass, acquired_mass_eq_word]
  · simpa [actualFutureWordWeight, he] using actual_conditional_future p q r h he H w

/-- Every actual positive-history decoder is one common coherent law family. -/
theorem actual_law_probability_and_coherence {p q r : ℝ} (hp : admissible p q r)
    (h : List Visible) (hpos : 0 < historyMass p q r h) (H : Nat) (w : Fin H → Visible) :
    0 ≤ actualFutureWordWeight p q r h H w ∧
    (∑ u : Fin H → Visible, actualFutureWordWeight p q r h H u) = 1 ∧
    (∑ y : Visible, actualFutureWordWeight p q r h (H + 1) (Fin.snoc w y)) =
      actualFutureWordWeight p q r h H w := by
  by_cases he : h = []
  · subst h
    simp only [actualFutureWordWeight, if_pos rfl]
    exact ⟨initial_word_nonnegative hp H w, sum_initial_words H,
      initial_final_symbol_coherence H w⟩
  · simp only [actualFutureWordWeight, he, if_false]
    rcases posterior_probability hp h hpos with ⟨hnon, hsum⟩
    exact ⟨future_word_nonnegative hp _ hnon H w, (sum_future_words _ H).trans hsum,
      final_symbol_coherence _ H w⟩

/-- Every extension of a positive history advances and filters its posterior;
empty history instead filters pi directly. -/
theorem actual_posterior_update (p q r : ℝ) (h : List Visible) (y : Visible)
    (hpos : 0 < historyMass p q r h) :
    acquiredPosterior p q r (h ++ [y]) =
      if h = [] then normalizeVector (filterAt uniformPi y)
      else posteriorAfterRead p q r (acquiredPosterior p q r h) y := by
  unfold acquiredPosterior
  rw [acquired_snoc]
  by_cases he : h = []
  · simp [he]
  · simp only [he, if_false, posteriorAfterRead, normalizeVector]
    have hs : normalizeVector (acquiredStateWeights p q r h) =
        (fun i => (historyMass p q r h)⁻¹ * acquiredStateWeights p q r h i) := by
      funext i; simp [normalizeVector, historyMass, div_eq_mul_inv, mul_comm]
    rw [hs, advance_scale, filter_scale]
    exact (normalize_scale _ _ (inv_ne_zero (ne_of_gt hpos))).symm


def pureBSuccessor (j : State) : State := if j = 0 ∨ j = 4 then 4 else 2
noncomputable def pureBMass (p q r : ℝ) (j : State) : ℝ :=
  if j = 0 then r else if j = 4 then b r else
    if j = 1 then p else if j = 3 then q else a p q

lemma pure_B_step (p q r : ℝ) (j : State) :
    filterAt (advance p q r (pureVector j)) B =
      fun i => pureBMass p q r j * pureVector (pureBSuccessor j) i := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [filterAt, advance, pureVector, observation, B, transition,
      pureBMass, pureBSuccessor, a, b, Fin.sum_univ_succ]

lemma pure_B_mass_positive {p q r : ℝ} (hp : admissible p q r) (j : State) :
    0 < pureBMass p q r j := by
  rcases hp with ⟨hp, hq, hr, ht⟩
  fin_cases j <;> simp [pureBMass, a, b] <;> linarith

lemma reconstruct_posterior (p q r : ℝ) (h : List Visible)
    (hpos : 0 < historyMass p q r h) :
    acquiredStateWeights p q r h =
      fun i => historyMass p q r h * acquiredPosterior p q r h i := by
  funext i
  unfold acquiredPosterior normalizeVector
  change acquiredStateWeights p q r h i =
    historyMass p q r h * (acquiredStateWeights p q r h i / historyMass p q r h)
  field_simp [ne_of_gt hpos]

/-- Each pure B transition occurs positively on every positive pure history;
its mass and successor state come from the literal matrix. -/
theorem actual_pure_B_transition {p q r : ℝ} (hp : admissible p q r)
    (h : List Visible) (hne : h ≠ []) (hpos : 0 < historyMass p q r h)
    (j : State) (hj : acquiredPosterior p q r h = pureVector j) :
    historyMass p q r (h ++ [B]) = historyMass p q r h * pureBMass p q r j ∧
    0 < historyMass p q r (h ++ [B]) ∧
    acquiredPosterior p q r (h ++ [B]) = pureVector (pureBSuccessor j) := by
  have he : acquiredStateWeights p q r (h ++ [B]) =
      fun i => (historyMass p q r h * pureBMass p q r j) * pureVector (pureBSuccessor j) i := by
    rw [acquired_append p q r h [B] hne]
    simp only [futureStateWeights]
    rw [reconstruct_posterior p q r h hpos, hj, advance_scale, filter_scale, pure_B_step]
    funext i; ring
  have hm : historyMass p q r (h ++ [B]) = historyMass p q r h * pureBMass p q r j := by
    simp [historyMass, he, pureVector]
  have hcp : 0 < historyMass p q r h * pureBMass p q r j :=
    mul_pos hpos (pure_B_mass_positive hp j)
  refine ⟨hm, hm ▸ hcp, ?_⟩
  rw [actual_posterior_update p q r h B hpos, if_neg hne, hj]
  unfold posteriorAfterRead
  rw [pure_B_step, normalize_scale _ _ (ne_of_gt (pure_B_mass_positive hp j))]
  simpa [sourceProfile, sourceWeights] using pure_profile p q r (pureBSuccessor j)

lemma pure_self_loop (p q r : ℝ) (j : State) :
    filterAt (advance p q r (pureVector j)) (observation j) =
      fun i => transition p q r j j * pureVector j i := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [filterAt, advance, pureVector, observation, transition, Fin.sum_univ_succ]

lemma pure_self_padding_weights (p q r : ℝ) (j : State) (n : Nat) :
    futureStateWeights p q r (pureVector j) (List.replicate n (observation j)) =
      fun i => (transition p q r j j) ^ n * pureVector j i := by
  induction n with
  | zero => simp [futureStateWeights]
  | succ n ih =>
      simp only [List.replicate_succ, futureStateWeights]
      rw [pure_self_loop, future_state_scale, ih]
      funext i
      simp only [pow_succ]
      ring

/-- The five literal acquired words identify all five pure states. -/
def pureWitness : State → List Visible := ![[0], [1], [1,B], [3], [0,B]]
noncomputable def pureWitnessMass (p r : ℝ) : State → ℝ := ![1/5,1/5,p/5,1/5,r/5]

lemma pure_witness_weights (p q r : ℝ) (j : State) :
    acquiredStateWeights p q r (pureWitness j) =
      fun i => pureWitnessMass p r j * pureVector j i := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [pureWitness, pureWitnessMass, acquiredStateWeights, futureStateWeights,
      filterAt, advance, uniformPi, pureVector, observation, B, transition, Fin.sum_univ_succ] <;>
    ring

lemma pure_witness_mass_positive {p q r : ℝ} (hp : admissible p q r) (j : State) :
    0 < pureWitnessMass p r j := by
  rcases hp with ⟨hp, hq, hr, ht⟩
  fin_cases j <;> simp [pureWitnessMass] <;> positivity

lemma diagonal_positive {p q r : ℝ} (hp : admissible p q r) (j : State) :
    0 < transition p q r j j := by
  rcases hp with ⟨hp, hq, hr, ht⟩
  fin_cases j <;> simp [transition] <;> linarith

/-- At every finite extension length each pure witness can be padded by its
positive self-loop. For states 2 and 4 these are 1B and 0B followed by arbitrary B's. -/
theorem positive_pure_padding {p q r : ℝ} (hp : admissible p q r) (j : State) (n : Nat) :
    let h := pureWitness j ++ List.replicate n (observation j)
    historyMass p q r h = pureWitnessMass p r j * (transition p q r j j) ^ n ∧
    0 < historyMass p q r h ∧ acquiredPosterior p q r h = pureVector j := by
  dsimp only
  have hne : pureWitness j ≠ [] := by fin_cases j <;> simp [pureWitness]
  have he : acquiredStateWeights p q r (pureWitness j ++ List.replicate n (observation j)) =
      fun i => (pureWitnessMass p r j * (transition p q r j j) ^ n) * pureVector j i := by
    rw [acquired_append p q r _ _ hne, pure_witness_weights, future_state_scale,
      pure_self_padding_weights]
    funext i; ring
  have hm : historyMass p q r (pureWitness j ++ List.replicate n (observation j)) =
      pureWitnessMass p r j * (transition p q r j j) ^ n := by
    simp [historyMass, he, pureVector]
  have hc : 0 < pureWitnessMass p r j * (transition p q r j j) ^ n :=
    mul_pos (pure_witness_mass_positive hp j) (pow_pos (diagonal_positive hp j) n)
  refine ⟨hm, hm ▸ hc, ?_⟩
  unfold acquiredPosterior
  rw [he, normalize_scale _ _ (ne_of_gt hc)]
  simpa [sourceProfile, sourceWeights] using pure_profile p q r j

/-- The rare transitions remain positive with closed masses at every B-padding length. -/
theorem rare_B_extension_masses {p q r : ℝ} (hp : admissible p q r) (n : Nat) :
    historyMass p q r ([1, B] ++ List.replicate n B) = p * (a p q) ^ n / 5 ∧
    0 < historyMass p q r ([1, B] ++ List.replicate n B) ∧
    acquiredPosterior p q r ([1, B] ++ List.replicate n B) = pureVector 2 ∧
    historyMass p q r ([0, B] ++ List.replicate n B) = r * (b r) ^ n / 5 ∧
    0 < historyMass p q r ([0, B] ++ List.replicate n B) ∧
    acquiredPosterior p q r ([0, B] ++ List.replicate n B) = pureVector 4 := by
  have h2 := positive_pure_padding hp 2 n
  have h4 := positive_pure_padding hp 4 n
  change historyMass p q r ([1,B] ++ List.replicate n B) = p / 5 * (a p q) ^ n ∧ _ at h2
  change historyMass p q r ([0,B] ++ List.replicate n B) = r / 5 * (b r) ^ n ∧ _ at h4
  exact ⟨h2.1.trans (by ring), h2.2.1, h2.2.2,
    h4.1.trans (by ring), h4.2.1, h4.2.2⟩


/-- All five literal witness masses are the masses of acquired histories. -/
theorem acquired_witness_word_masses (p q r : ℝ) :
    historyMass p q r [0] = 1 / 5 ∧ historyMass p q r [1] = 1 / 5 ∧
    historyMass p q r [3] = 1 / 5 ∧ historyMass p q r [1,B] = p / 5 ∧
    historyMass p q r [0,B] = r / 5 := by
  have hh (y : Visible) : List.ofFn (fun _ : Fin 1 => y) = [y] := by simp
  have hb (y : Visible) : List.ofFn (fun k : Fin 2 => if k = 0 then y else B) = [y,B] := by
    simp [List.ofFn_succ]
  have ht := @witness_word_masses p q r
  simp_rw [← acquired_mass_eq_word, hh, hb] at ht
  exact ht


lemma pure_witness_run (j : State) : sourceRun (pureWitness j) = .pure j := by
  fin_cases j <;> rfl

/-- Every declared source tag is realized by an actual positive acquired
history, and only Start uses the empty history. -/
theorem complete_source_tag_reachability {p q r : ℝ} (hp : admissible p q r) (z : SourceTag) :
    ∃ h : List Visible, sourceRun h = z ∧ 0 < historyMass p q r h ∧
      acquiredPosterior p q r h = sourceProfile p q r z ∧
      (h = [] ↔ z = .start) := by
  cases z with
  | start =>
      refine ⟨[], rfl, ?_, rfl, by simp⟩
      rw [empty_history_mass]
      norm_num
  | startup k =>
      have he : List.ofFn (fun _ : Fin (k + 1) => B) = List.replicate (k + 1) B := by simp [List.replicate_succ]
      have hm : 0 < historyMass p q r (List.replicate (k + 1) B) := by
        rw [← he, acquired_mass_eq_word]
        exact all_b_positive hp k
      refine ⟨List.replicate (k + 1) B, startup_all_b k, hm, ?_, by simp⟩
      rw [positive_history_invariant p q r _ hm]
      congr 1
      exact startup_all_b k
  | pure j =>
      have hm : 0 < historyMass p q r (pureWitness j) := by
        have ht := acquired_witness_word_masses p q r
        rcases hp with ⟨hp, hq, hr, hh⟩
        fin_cases j <;> simp only [pureWitness] <;>
          first | simpa [ht.1] using (show (0 : ℝ) < 1 / 5 by norm_num)
                | simpa [ht.2.1] using (show (0 : ℝ) < 1 / 5 by norm_num)
                | simpa [ht.2.2.1] using (show (0 : ℝ) < 1 / 5 by norm_num)
                | simpa [ht.2.2.2.1] using (div_pos hp (by norm_num : (0 : ℝ) < 5))
                | simpa [ht.2.2.2.2] using (div_pos hr (by norm_num : (0 : ℝ) < 5))
      refine ⟨pureWitness j, pure_witness_run j, hm, ?_, ?_⟩
      · rw [positive_history_invariant p q r _ hm, pure_witness_run]
      · fin_cases j <;> simp [pureWitness]

lemma start_profile (p q r : ℝ) : sourceProfile p q r .start = uniformPi := by
  funext i
  norm_num [sourceProfile, sourceWeights, normalizeVector, uniformPi, Fin.sum_univ_succ]

/-- The computed tag predicts the actual conditional cylinder at every horizon,
including the stationary empty boundary. -/
theorem source_tag_conditional_future (p q r : ℝ)
    (h : List Visible) (hpos : 0 < historyMass p q r h) (H : Nat) (w : Fin H → Visible) :
    historyMass p q r (h ++ List.ofFn w) / historyMass p q r h =
      futureWordWeight p q r (sourceProfile p q r (sourceRun h)) H w := by
  rw [all_history_conditional_identity]
  by_cases he : h = []
  · subst h
    simp only [actualFutureWordWeight, if_pos rfl, sourceRun, List.foldl_nil, start_profile]
    exact empty_boundary_and_positive_timing p q r H w
  · simp only [actualFutureWordWeight, he, if_false]
    rw [positive_history_invariant p q r h hpos]

end D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
