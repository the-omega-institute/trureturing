/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original integer-time marked cylinders determine the actual unifilar endpoint masses. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix Classical
open MeasureTheory Function

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient

universe u

variable {H : Type*} [Fintype H]

/-- The full stationary nonnegative binary edge-emission domain, including zero masses. -/
structure Presentation (H : Type*) [Fintype H] where
  initial : H → ℝ
  matrix : Bool → Matrix H H ℝ
  initial_nonneg : ∀ i, 0 ≤ initial i
  initial_sum : ∑ i, initial i = 1
  matrix_nonneg : ∀ x i j, 0 ≤ matrix x i j
  stochastic : ∀ i, ∑ j, (matrix false i j + matrix true i j) = 1
  stationary : ∀ j, ∑ i, initial i * (matrix false i j + matrix true i j) = initial j
  no11 : ∑ i, ∑ j, initial i * (matrix true * matrix true) i j = 0

/-- The arbitrary finite original producer, with its finite domain carried as data. -/
structure Producer where
  hidden : Type u
  finite : Fintype hidden
  parameter : @Presentation hidden finite

/-- At most one positive successor for each original row and symbol. -/
def RowUnifilar (M : Bool → Matrix H H ℝ) : Prop :=
  ∀ x i j k, 0 < M x i j → 0 < M x i k → j = k

def symbolMass (M : Bool → Matrix H H ℝ) (i : H) (x : Bool) : ℝ := ∑ j, M x i j

/-- A zero row keeps its source state; this arbitrary choice has zero weight. -/
def successor (M : Bool → Matrix H H ℝ) (i : H) (x : Bool) : H :=
  if h : ∃ j, 0 < M x i j then Classical.choose h else i

theorem row_eq (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M) (i j : H) (x : Bool) :
    M x i j = if j = successor M i x then symbolMass M i x else 0 := by
  by_cases h : ∃ k, 0 < M x i k
  · have hk := Classical.choose_spec h
    have hz : ∀ k, k ≠ Classical.choose h → M x i k = 0 := by
      intro k hne
      apply le_antisymm _ (hn _ _ _)
      exact le_of_not_gt (fun hp => hne (hu x i k _ hp hk))
    have hs : symbolMass M i x = M x i (Classical.choose h) := by
      exact Finset.sum_eq_single _ (fun k _ hk => hz k hk) (by simp)
    simp only [successor, dif_pos h]
    by_cases hj : j = Classical.choose h
    · simp [hj, hs]
    · simp [hj, hz j hj]
  · have hz : ∀ k, M x i k = 0 := by
      intro k
      exact le_antisymm (le_of_not_gt (fun hp => h ⟨k, hp⟩)) (hn _ _ _)
    simp [symbolMass, hz]

def wordMatrix (M : Bool → Matrix H H ℝ) : (n : ℕ) → (Fin n → Bool) → Matrix H H ℝ
  | 0, _ => 1
  | n + 1, w => M (w 0) * wordMatrix M n (Fin.tail w)

def futureMass (M : Bool → Matrix H H ℝ) (i : H) (n : ℕ) (w : Fin n → Bool) : ℝ :=
  ∑ j, wordMatrix M n w i j

/-- Equality of every original finite future cylinder, rather than of a surrogate readout. -/
def futureSetoid (M : Bool → Matrix H H ℝ) : Setoid H :=
  Setoid.ker (fun i => fun n => futureMass M i n)

abbrev FutureClass (M : Bool → Matrix H H ℝ) := Quotient (futureSetoid M)
def classOf (M : Bool → Matrix H H ℝ) (i : H) : FutureClass M := Quotient.mk _ i

theorem future_step (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M)
    (i : H) (x : Bool) (n : ℕ) (w : Fin n → Bool) :
    futureMass M i (n + 1) (Fin.cons x w) =
      symbolMass M i x * futureMass M (successor M i x) n w := by
  simp only [futureMass, wordMatrix, Fin.cons_zero, Fin.tail_cons, Matrix.mul_apply]
  simp_rw [row_eq M hn hu, ite_mul]
  simp only [zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]

private theorem same_symbol (M : Bool → Matrix H H ℝ)
    {i j : H} (h : (futureSetoid M).r i j) (x : Bool) :
    symbolMass M i x = symbolMass M j x := by
  have he := congrFun (congrFun h 1) (fun _ => x)
  simpa [futureMass, wordMatrix, symbolMass] using he

private theorem same_successor (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M)
    {i j : H} (h : (futureSetoid M).r i j) (x : Bool)
    (hp : symbolMass M i x ≠ 0) :
    classOf M (successor M i x) = classOf M (successor M j x) := by
  apply Quotient.sound
  funext n w
  have he := congrFun (congrFun h (n + 1)) (Fin.cons x w)
  change futureMass M i (n + 1) (Fin.cons x w) = futureMass M j (n + 1) (Fin.cons x w) at he
  rw [future_step M hn hu, future_step M hn hu, ← same_symbol M h x] at he
  exact mul_left_cancel₀ hp he

/-- Both masses and successors are selected from the actual finite future-law classes. -/
def quotientMass (M : Bool → Matrix H H ℝ) (a : FutureClass M) (x : Bool) : ℝ :=
  symbolMass M a.out x

def quotientSuccessor (M : Bool → Matrix H H ℝ) (a : FutureClass M) (x : Bool) :
    FutureClass M := classOf M (successor M a.out x)

theorem quotient_mass_mk (M : Bool → Matrix H H ℝ) (i : H) (x : Bool) :
    quotientMass M (classOf M i) x = symbolMass M i x :=
  same_symbol M (Quotient.exact (Quotient.out_eq (classOf M i))) x

theorem quotient_successor_mk (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M)
    (i : H) (x : Bool) (hp : symbolMass M i x ≠ 0) :
    quotientSuccessor M (classOf M i) x = classOf M (successor M i x) := by
  apply same_successor M hn hu (Quotient.exact (Quotient.out_eq (classOf M i)))
  simpa [← quotient_mass_mk M i x, quotientMass] using hp

open UnifilarPairSurvival

theorem word_quotient (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M)
    (n : ℕ) (i : H) (w : Fin n → Bool) (a : FutureClass M) :
    (if classOf M (endpoint (successor M) n i w) = a
      then wordMass (symbolMass M) (successor M) n i w else 0) =
    if endpoint (quotientSuccessor M) n (classOf M i) w = a
      then wordMass (quotientMass M) (quotientSuccessor M) n (classOf M i) w else 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [endpoint, wordMass, quotient_mass_mk]
    by_cases hp : symbolMass M i (w 0) = 0
    · simp [hp]
    · rw [quotient_successor_mk M hn hu i (w 0) hp]
      have he := ih (successor M i (w 0)) (Fin.tail w)
      simpa only [mul_ite, mul_zero] using congrArg (fun z => symbolMass M i (w 0) * z) he

/-- A complete original hidden path, without quotienting its coordinates. -/
def pathMass (M : Bool → Matrix H H ℝ) (n : ℕ) (h : Fin (n + 1) → H)
    (w : Fin n → Bool) : ℝ := ∏ k : Fin n, M (w k) (h k.castSucc) (h k.succ)

def trajectory (δ : H → Bool → H) : (n : ℕ) → H → (Fin n → Bool) → (Fin (n + 1) → H)
  | 0, i, _ => fun _ => i
  | n + 1, i, w => Fin.cons i (trajectory δ n (δ i (w 0)) (Fin.tail w))

omit [Fintype H] in
theorem trajectory_first (δ : H → Bool → H) (n : ℕ) (i : H) (w : Fin n → Bool) :
    trajectory δ n i w 0 = i := by cases n <;> simp [trajectory]

omit [Fintype H] in
theorem trajectory_last (δ : H → Bool → H) (n : ℕ) (i : H) (w : Fin n → Bool) :
    trajectory δ n i w (Fin.last n) = endpoint δ n i w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simpa [trajectory, endpoint, ← Fin.succ_last] using ih (δ i (w 0)) (Fin.tail w)

omit [Fintype H] in
theorem path_step (M : Bool → Matrix H H ℝ) (n : ℕ)
    (h : Fin (n + 2) → H) (w : Fin (n + 1) → Bool) :
    pathMass M (n + 1) h w = M (w 0) (h 0) (h 1) *
      pathMass M n (Fin.tail h) (Fin.tail w) := by
  simp [pathMass, Fin.prod_univ_succ, Fin.tail, Fin.castSucc_succ]

theorem path_support (M : Bool → Matrix H H ℝ)
    (hn : ∀ x i j, 0 ≤ M x i j) (hu : RowUnifilar M)
    (n : ℕ) (i : H) (h : Fin n → H) (w : Fin n → Bool) :
    pathMass M n (Fin.cons i h) w =
      if Fin.cons i h = trajectory (successor M) n i w
      then wordMass (symbolMass M) (successor M) n i w else 0 := by
  induction n generalizing i with
  | zero =>
    have he : Fin.cons i h = (fun _ : Fin 1 => i) := by
      funext k
      fin_cases k
      rfl
    simp [pathMass, trajectory, wordMass, he]
  | succ n ih =>
    rw [path_step]
    simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons, trajectory, wordMass,
      Fin.cons_inj, row_eq M hn hu]
    by_cases hh : h 0 = successor M i (w 0)
    · rw [if_pos hh]
      rw [← Fin.cons_self_tail h]
      rw [hh, ih]
      simp [mul_ite]
    · have hne : h ≠ trajectory (successor M) n (successor M i (w 0)) (Fin.tail w) := by
        intro he
        apply hh
        rw [he, trajectory_first]
      simp [hh, hne]

abbrev PathSpace (H : Type*) := (ℤ → H) × (ℤ → Bool)

def cylinder (t : ℤ) (n : ℕ) (h : Fin (n + 1) → H) (w : Fin n → Bool) : Set (PathSpace H) :=
  {z | (∀ k : Fin (n + 1), z.1 (t + (k.val : ℤ)) = h k) ∧ ∀ k : Fin n, z.2 (t + (k.val : ℤ)) = w k}

/-- An intermediate interface for the original law: every integer interval has its defining mass.
This interface asserts no screening and supplies no existence theorem. -/
def HasOriginalCylinders [MeasurableSpace H] (J : Measure (PathSpace H))
    (θ : Presentation H) : Prop :=
  ∀ t n h w, J.real (cylinder t n h w) = θ.initial (h 0) * pathMass θ.matrix n h w

def endpointEvent (M : Bool → Matrix H H ℝ) (t : ℤ) (n : ℕ)
    (w : Fin n → Bool) (a : FutureClass M) : Set (PathSpace H) :=
  {z | (∀ k : Fin n, z.2 (t + (k.val : ℤ)) = w k) ∧ classOf M (z.1 (t + n)) = a}

theorem sum_paths (n : ℕ) (f : (Fin (n + 1) → H) → ℝ) :
    ∑ h, f h = ∑ i : H, ∑ h : Fin n → H, f (Fin.cons i h) := by
  let e := (Fin.consEquiv (fun _ : Fin (n + 1) => H)).symm
  calc
    (∑ h, f h) = ∑ z : H × (Fin n → H), f (Fin.cons z.1 z.2) :=
      Fintype.sum_equiv e f (fun z => f (Fin.cons z.1 z.2))
        (fun h => congrArg f (Fin.cons_self_tail h).symm)
    _ = _ := Fintype.sum_prod_type _

private theorem summed_path_mass (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (n : ℕ) (w : Fin n → Bool) (a : FutureClass θ.matrix) :
    (∑ h : Fin (n + 1) → H,
      if classOf θ.matrix (h (Fin.last n)) = a
      then θ.initial (h 0) * pathMass θ.matrix n h w else 0) =
    ∑ i, θ.initial i *
      if classOf θ.matrix (endpoint (successor θ.matrix) n i w) = a
      then wordMass (symbolMass θ.matrix) (successor θ.matrix) n i w else 0 := by
  rw [sum_paths]
  apply Finset.sum_congr rfl
  intro i _
  let hstar := trajectory (successor θ.matrix) n i w
  have he : Fin.cons i (Fin.tail hstar) = hstar := by
    rw [← trajectory_first (successor θ.matrix) n i w]
    exact Fin.cons_self_tail hstar
  rw [Finset.sum_eq_single (Fin.tail hstar)]
  · have hmass : pathMass θ.matrix n (trajectory (successor θ.matrix) n i w) w =
        wordMass (symbolMass θ.matrix) (successor θ.matrix) n i w := by
      simpa [he, hstar] using path_support θ.matrix θ.matrix_nonneg hu n i (Fin.tail hstar) w
    simp only [he, hstar, trajectory_first, trajectory_last, hmass, mul_ite, mul_zero]
  · intro h _ hne
    have hpath : Fin.cons i h ≠ hstar := by
      intro hh
      apply hne
      simpa only [Fin.tail_cons] using congrArg Fin.tail hh
    rw [path_support θ.matrix θ.matrix_nonneg hu]
    simp [hpath, hstar]
  · simp

/-- The original integer-time cylinder law gives the actual joint emitted-word/final-class mass.
No new probability model, positive-row assumption, or conditional table is substituted for J. -/
theorem actual_endpoint_mass (T : Producer.{u})
    [MeasurableSpace T.hidden] [MeasurableSingletonClass T.hidden] :
    letI : Fintype T.hidden := T.finite
    ∀ (hu : RowUnifilar T.parameter.matrix)
      (J : Measure (PathSpace T.hidden)) [IsProbabilityMeasure J]
      (hcyl : HasOriginalCylinders J T.parameter) (t : ℤ) (n : ℕ)
      (w : Fin n → Bool) (a : FutureClass T.parameter.matrix),
      J.real (endpointEvent T.parameter.matrix t n w a) =
        ∑ i, T.parameter.initial i *
          if endpoint (quotientSuccessor T.parameter.matrix) n
            (classOf T.parameter.matrix i) w = a
          then wordMass (quotientMass T.parameter.matrix) (quotientSuccessor T.parameter.matrix)
            n (classOf T.parameter.matrix i) w else 0 := by
  letI : Fintype T.hidden := T.finite
  intro hu J hJ hcyl t n w a
  let θ := T.parameter
  let f : (Fin (n + 1) → T.hidden) → Set (PathSpace T.hidden) := fun h =>
    if classOf θ.matrix (h (Fin.last n)) = a then cylinder t n h w else ∅
  have he : endpointEvent θ.matrix t n w a = ⋃ h, f h := by
    ext z
    simp only [endpointEvent, Set.mem_ofPred, Set.mem_iUnion]
    constructor
    · rintro ⟨hw, ha⟩
      refine ⟨(fun k => z.1 (t + (k.val : ℤ))), ?_⟩
      simp [f, ha, cylinder, hw]
    · rintro ⟨h, hz⟩
      by_cases ha : classOf θ.matrix (h (Fin.last n)) = a
      · have hz' : z ∈ cylinder t n h w := by simpa [f, ha] using hz
        exact ⟨hz'.2, by simpa using (congrArg (classOf θ.matrix) (hz'.1 (Fin.last n))).trans ha⟩
      · simpa [f, ha] using hz
  have hd : Pairwise (fun h k => Disjoint (f h) (f k)) := by
    intro h k hne
    by_cases hh : classOf θ.matrix (h (Fin.last n)) = a
    · by_cases hk : classOf θ.matrix (k (Fin.last n)) = a
      · simp only [f, if_pos hh, if_pos hk, Set.disjoint_left]
        intro z hz hz'
        apply hne
        funext j
        exact (hz.1 j).symm.trans (hz'.1 j)
      · simp [f, hk]
    · simp [f, hh]
  have hm : ∀ h, MeasurableSet (f h) := by
    intro h
    by_cases hh : classOf θ.matrix (h (Fin.last n)) = a
    · simp only [f, if_pos hh, cylinder]
      simp only [Set.ofPred_and, Set.ofPred_forall]
      exact (MeasurableSet.iInter (fun k =>
        (measurableSet_singleton (h k)).preimage
          ((measurable_pi_apply (t + (k.val : ℤ))).comp measurable_fst))).inter
        (MeasurableSet.iInter (fun k =>
          (measurableSet_singleton (w k)).preimage
            ((measurable_pi_apply (t + (k.val : ℤ))).comp measurable_snd)))
    · simp [f, hh]
  rw [he, measureReal_iUnion_fintype hd hm]
  have hf : ∀ h, J.real (f h) =
      if classOf θ.matrix (h (Fin.last n)) = a
      then θ.initial (h 0) * pathMass θ.matrix n h w else 0 := by
    intro h
    by_cases hh : classOf θ.matrix (h (Fin.last n)) = a
    · simp [f, hh, hcyl t n h w, θ]
    · simp [f, hh]
  simp_rw [hf]
  rw [summed_path_mass θ hu]
  apply Finset.sum_congr rfl
  intro i _
  rw [word_quotient θ.matrix θ.matrix_nonneg hu]

#print axioms actual_endpoint_mass

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
