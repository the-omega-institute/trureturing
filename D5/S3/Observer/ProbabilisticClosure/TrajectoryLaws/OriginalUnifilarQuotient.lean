/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalUnifilarQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive-support predictive classes carry a stationary marked unifilar law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarAffinityContraction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
attribute [local instance 100000] Classical.propDecidable
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming
open PositiveSupportPresentation OriginalFutureCylinders OriginalFutureScreening
open UnifilarPairSurvival OriginalErasureComparison
open UnifilarAffinityContraction

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarQuotient
section GroupedMass
variable {S C : Type*} [Fintype S] [DecidableEq S] [DecidableEq C]

/-- Half the ordered off-diagonal sum, equal to the sum over any ordering a < b. -/
def pairWeight (pi : S → ℝ) : ℝ :=
  (∑ i, ∑ j, if i ≠ j then Real.sqrt (pi i * pi j) else 0) / 2

private theorem sqrt_group (a : S → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : S → C) (m : C) (i : S)
    (hi : a i ≤ ∑ j, if f j = m then a j else 0) :
    a i ≤ ∑ j, if f j = m then Real.sqrt (a i*a j) else 0 := by
  let g : S → ℝ := fun j => if f j = m then Real.sqrt (a i*a j) else 0
  have hn (j : S) : 0 ≤ g j := by dsimp [g]; split_ifs <;> positivity
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := g) (fun j _ => hn j)
  have he : ∑ j, g j^2 = a i * ∑ j, if f j = m then a j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    split_ifs <;> simp [Real.sq_sqrt (mul_nonneg (ha i) (ha j))]
  rw [he] at hs
  have hn' : 0 ≤ ∑ j, g j := Finset.sum_nonneg (fun j _ => hn j)
  have hm := mul_le_mul_of_nonneg_left hi (ha i)
  change a i ≤ ∑ j, g j
  nlinarith

/-- This estimate applies to actual endpoint groups, including zero groups and ties.
Its sum omits all pairs whose final states have merged. -/
theorem grouped_map_pair_bound (a : S → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : S → C) (m : C)
    (hm : ∀ c, (∑ i, if f i = c then a i else 0) ≤
      ∑ i, if f i = m then a i else 0) :
    (∑ i, a i) - (∑ i, if f i = m then a i else 0) ≤
      (∑ i, ∑ j, if f i ≠ f j then Real.sqrt (a i*a j) else 0) / 2 := by
  classical
  let star : S → S → ℝ := fun i j =>
    if f i ≠ m ∧ f j = m then Real.sqrt (a i*a j) else 0
  have hstar : (∑ i, a i) - (∑ i, if f i = m then a i else 0) ≤
      ∑ i, ∑ j, star i j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : f i = m
    · simp [star,hi]
    · simp only [if_neg hi,sub_zero]
      have hlocal : a i ≤ ∑ j, if f j = f i then a j else 0 := by
        calc
          a i = if f i = f i then a i else 0 := by simp
          _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (a := i)
            (f := fun j => if f j = f i then a j else 0) (by
              intro j _
              split_ifs
              · exact ha j
              · exact le_rfl) (Finset.mem_univ i)
      simpa only [star,ne_eq,hi,not_false_eq_true,true_and] using sqrt_group a ha f m i (hlocal.trans (hm (f i)))
  have hdouble : 2*(∑ i, ∑ j, star i j) ≤
      ∑ i, ∑ j, if f i ≠ f j then Real.sqrt (a i*a j) else 0 := by
    have hpoint (i j : S) : star i j+star j i ≤
        if f i ≠ f j then Real.sqrt (a i*a j) else 0 := by
      dsimp [star]
      by_cases hi : f i = m <;> by_cases hj : f j = m <;>
        by_cases hij : f i = f j <;> simp_all [mul_comm,Real.sqrt_nonneg] <;> positivity
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
    simp only [Finset.sum_add_distrib] at hsum
    rw [Finset.sum_comm (f := fun i j => star j i)] at hsum
    linarith
  linarith

/-- The coefficient is the source unordered sum and has the stationary cardinal bound. -/
theorem pair_weight_bound (pi : S → ℝ) (hp : ∀ i, 0 ≤ pi i) (hs : ∑ i, pi i = 1) :
    0 ≤ pairWeight pi ∧ pairWeight pi ≤ ((Fintype.card S : ℝ)-1)/2 ∧
    (∀ (_ : LinearOrder S), pairWeight pi =
      ∑ i, ∑ j, if i < j then Real.sqrt (pi i*pi j) else 0) := by
  classical
  have hoff : (∑ i, ∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
      (∑ i, Real.sqrt (pi i))^2-1 := by
    have hsplit (i : S) : (∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
        (∑ j, Real.sqrt (pi i*pi j)) - pi i := by
      have he : (∑ j, if i = j then Real.sqrt (pi i*pi j) else 0) = pi i := by
        simp [Real.sqrt_mul_self (hp i)]
      have hall : (∑ j, if i ≠ j then Real.sqrt (pi i*pi j) else 0) +
          (∑ j, if i = j then Real.sqrt (pi i*pi j) else 0) =
          ∑ j, Real.sqrt (pi i*pi j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij]
      linarith
    simp_rw [hsplit,Real.sqrt_mul (hp _)]
    rw [Finset.sum_sub_distrib,hs,← Finset.sum_mul_sum]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : S => Real.sqrt (pi i)) (g := fun _ : S => (1:ℝ))
  simp only [mul_one,Real.sq_sqrt (hp _),hs,one_pow,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,one_mul] at hcs
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
    split_ifs <;> positivity))) (by norm_num),?_,?_⟩
  · dsimp [pairWeight]
    rw [hoff]
    linarith
  · intro order
    letI := order
    have hsplit (i j : S) : (if i ≠ j then Real.sqrt (pi i*pi j) else 0) =
        (if i < j then Real.sqrt (pi i*pi j) else 0) +
        (if j < i then Real.sqrt (pi i*pi j) else 0) := by
      rcases lt_trichotomy i j with h | h | h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,h.le]
    unfold pairWeight
    simp_rw [hsplit,Finset.sum_add_distrib]
    have he : (∑ i, ∑ j, if j < i then Real.sqrt (pi i*pi j) else 0) =
        ∑ i, ∑ j, if i < j then Real.sqrt (pi i*pi j) else 0 := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [he]
    ring

end GroupedMass

universe u
variable {H : Type u} [Fintype H]

/-- The stationary mass of an actual predictive class, including all retained lifts. -/
def classWeight (θ : Presentation H) (a : FutureClass θ.matrix) : ℝ :=
  by
  classical
  exact ∑ i, if classOf θ.matrix i = a then θ.initial i else 0

/-- The marked kernel uses the existing future-law quotient and its weighted successor. -/
def classMatrix (M : Bool → Matrix H H ℝ) : Bool →
    Matrix (FutureClass M) (FutureClass M) ℝ :=
  by
  classical
  exact fun x a b => if b = quotientSuccessor M a x then quotientMass M a x else 0

theorem word_class (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (n : ℕ) (i : H) (w : Fin n → Bool) :
    wordMass (quotientMass θ.matrix) (quotientSuccessor θ.matrix) n (classOf θ.matrix i) w =
      futureMass θ.matrix i n w := by
  induction n generalizing i with
  | zero => classical
    simp [wordMass,futureMass,wordMatrix,Matrix.one_apply]
  | succ n ih =>
    rw [wordMass,quotient_mass_mk]
    by_cases hp : symbolMass θ.matrix i (w 0) = 0
    · rw [hp,zero_mul]
      have hh := future_step θ.matrix θ.matrix_nonneg hu i (w 0) n (Fin.tail w)
      simpa [hp,Fin.cons_self_tail] using hh.symm
    · rw [quotient_successor_mk θ.matrix θ.matrix_nonneg hu i (w 0) hp,ih]
      simpa only [Fin.cons_self_tail] using
        (future_step θ.matrix θ.matrix_nonneg hu i (w 0) n (Fin.tail w)).symm

theorem q_nonneg (θ : Presentation H) (a : FutureClass θ.matrix) (x : Bool) :
    0 ≤ quotientMass θ.matrix a x :=
  Finset.sum_nonneg (fun _ _ => θ.matrix_nonneg _ _ _)

theorem q_total (θ : Presentation H) (a : FutureClass θ.matrix) :
    ∑ x, quotientMass θ.matrix a x = 1 := by
  simpa [quotientMass,symbolMass,Fintype.sum_bool,Finset.sum_add_distrib,add_comm]
    using θ.stochastic a.out

private theorem fiber_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (q : A → B) (f : A → ℝ) (g : B → ℝ) :
    ∑ a, f a * g (q a) = ∑ b, (∑ a, if q a = b then f a else 0) * g b := by
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

private theorem weight_nonneg (θ : Presentation H) (a : FutureClass θ.matrix) :
    0 ≤ classWeight θ a := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact θ.initial_nonneg _ | exact le_rfl

private theorem weight_total (θ : Presentation H) :
    letI := Fintype.ofFinite (FutureClass θ.matrix)
    ∑ a, classWeight θ a = 1 := by
  classical
  letI := Fintype.ofFinite (FutureClass θ.matrix)
  simpa [classWeight] using (fiber_sum (classOf θ.matrix) θ.initial (fun _ => 1)).symm.trans
    (by simpa using θ.initial_sum)

theorem row_group (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (i : H) (x : Bool) (b : FutureClass θ.matrix) :
    (∑ j, if classOf θ.matrix j = b then θ.matrix x i j else 0) =
      classMatrix θ.matrix x (classOf θ.matrix i) b := by
  simp_rw [row_eq θ.matrix θ.matrix_nonneg hu]
  rw [Finset.sum_eq_single (successor θ.matrix i x)]
  · by_cases hp : symbolMass θ.matrix i x = 0
    · simp [classMatrix,quotient_mass_mk,hp]
    · simp [classMatrix,quotient_mass_mk,
        quotient_successor_mk θ.matrix θ.matrix_nonneg hu i x hp,eq_comm]
  · intro j _ hj
    simp [hj]
  · simp

private theorem weight_stationary (θ : Presentation H) (hu : RowUnifilar θ.matrix) :
    letI := Fintype.ofFinite (FutureClass θ.matrix)
    ∀ b, ∑ a, classWeight θ a * (classMatrix θ.matrix false a b +
      classMatrix θ.matrix true a b) = classWeight θ b := by
  classical
  letI := Fintype.ofFinite (FutureClass θ.matrix)
  intro b
  unfold classWeight
  rw [← fiber_sum (classOf θ.matrix) θ.initial
    (fun a => classMatrix θ.matrix false a b + classMatrix θ.matrix true a b)]
  simp_rw [← row_group θ hu,← Finset.sum_add_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : classOf θ.matrix j = b
  · simp only [if_pos hj,θ.stationary]
  · simp [hj]


private theorem class_trajectory (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (n : ℕ) (i : H) (w : Fin n → Bool) (q : Fin (n+1) → FutureClass θ.matrix) :
    (if (classOf θ.matrix ∘ trajectory (successor θ.matrix) n i w) = q
      then wordMass (symbolMass θ.matrix) (successor θ.matrix) n i w else 0) =
    if trajectory (quotientSuccessor θ.matrix) n (classOf θ.matrix i) w = q
      then wordMass (quotientMass θ.matrix) (quotientSuccessor θ.matrix)
        n (classOf θ.matrix i) w else 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have he : classOf θ.matrix ∘ trajectory (successor θ.matrix) (n+1) i w =
        Fin.cons (classOf θ.matrix i)
          (classOf θ.matrix ∘ trajectory (successor θ.matrix) n
            (successor θ.matrix i (w 0)) (Fin.tail w)) := by
      ext k
      refine Fin.cases rfl (fun j => rfl) k
    rw [he, ← Fin.cons_self_tail q]
    simp only [trajectory,wordMass,Fin.cons_inj,quotient_mass_mk]
    by_cases hp : symbolMass θ.matrix i (w 0) = 0
    · simp [hp]
    · rw [quotient_successor_mk θ.matrix θ.matrix_nonneg hu i (w 0) hp]
      by_cases hi : classOf θ.matrix i = q 0
      · simpa only [hi,true_and,mul_ite,mul_zero] using
          congrArg (fun z => symbolMass θ.matrix i (w 0)*z)
            (ih (successor θ.matrix i (w 0)) (Fin.tail w) (Fin.tail q))
      · simp [hi]

private theorem lifted_paths (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (n : ℕ) (q : Fin (n+1) → FutureClass θ.matrix) (w : Fin n → Bool) :
    (∑ h : Fin (n+1) → H, if classOf θ.matrix ∘ h = q
      then θ.initial (h 0) * pathMass θ.matrix n h w else 0) =
    ∑ i, θ.initial i *
      if trajectory (quotientSuccessor θ.matrix) n (classOf θ.matrix i) w = q
      then wordMass (quotientMass θ.matrix) (quotientSuccessor θ.matrix)
        n (classOf θ.matrix i) w else 0 := by
  rw [sum_paths]
  apply Finset.sum_congr rfl
  intro i _
  let hstar := trajectory (successor θ.matrix) n i w
  have he : Fin.cons i (Fin.tail hstar) = hstar := by
    rw [← trajectory_first (successor θ.matrix) n i w]
    exact Fin.cons_self_tail hstar
  rw [Finset.sum_eq_single (Fin.tail hstar)]
  · have hm := path_support θ.matrix θ.matrix_nonneg hu n i (Fin.tail hstar) w
    rw [he,if_pos rfl] at hm
    rw [he,hm]
    dsimp [hstar]
    rw [trajectory_first]
    simpa only [mul_ite,mul_zero] using congrArg (fun z => θ.initial i*z)
      (class_trajectory θ hu n i w q)
  · intro h _ hne
    have hh : Fin.cons i h ≠ hstar := by
      intro hh
      exact hne (by simpa only [Fin.tail_cons] using congrArg Fin.tail hh)
    rw [path_support θ.matrix θ.matrix_nonneg hu]
    simp [hh,hstar]
  · simp

private theorem deterministic_path {S : Type*} [DecidableEq S] (p : S → Bool → ℝ) (δ : S → Bool → S)
    (n : ℕ) (q : Fin (n+1) → S) (w : Fin n → Bool) :
    pathMass (fun x a b => if b = δ a x then p a x else 0) n q w =
      if q = trajectory δ n (q 0) w then wordMass p δ n (q 0) w else 0 := by
  induction n with
  | zero =>
    have hq : q = fun _ => q 0 := by ext k; fin_cases k; rfl
    simp only [pathMass,Finset.univ_eq_empty,Finset.prod_empty,trajectory,wordMass,if_pos hq]
  | succ n ih =>
    rw [path_step,ih]
    conv_rhs => rw [← Fin.cons_self_tail q]
    simp only [trajectory,Fin.cons_zero,Fin.cons_inj,true_and,wordMass,Fin.tail_cons]
    rw [show Fin.tail q 0 = q 1 from rfl]
    by_cases hq : q 1 = δ (q 0) (w 0)
    · simp [hq,mul_ite]
    · have hh : Fin.tail q ≠ trajectory δ n (δ (q 0) (w 0)) (Fin.tail w) := by
        intro he
        exact hq ((congrFun he 0).trans (trajectory_first δ n _ _))
      simp [hq,hh]

private theorem grouped_paths (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    (n : ℕ) (q : Fin (n+1) → FutureClass θ.matrix) (w : Fin n → Bool) :
    (∑ h : Fin (n+1) → H, if classOf θ.matrix ∘ h = q
      then θ.initial (h 0) * pathMass θ.matrix n h w else 0) =
      classWeight θ (q 0) * pathMass (classMatrix θ.matrix) n q w := by
  classical
  letI := Fintype.ofFinite (FutureClass θ.matrix)
  rw [lifted_paths θ hu, fiber_sum (classOf θ.matrix) θ.initial
    (fun a => if trajectory (quotientSuccessor θ.matrix) n a w = q then
      wordMass (quotientMass θ.matrix) (quotientSuccessor θ.matrix) n a w else 0)]
  change (∑ a, classWeight θ a * _) = _
  rw [Finset.sum_eq_single (q 0)]
  · change _ = classWeight θ (q 0) * pathMass
      (fun x a b => if b = quotientSuccessor θ.matrix a x then quotientMass θ.matrix a x else 0) n q w
    rw [deterministic_path]
    simp [eq_comm]
  · intro a _ ha
    have hh : trajectory (quotientSuccessor θ.matrix) n a w ≠ q := by
      intro he
      exact ha ((trajectory_first _ n a w).symm.trans (congrFun he 0))
    simp [hh]
  · simp

/-- Apply the class map to every hidden coordinate and keep the original output coordinates. -/
def classPath (M : Bool → Matrix H H ℝ) (z : PathSpace H) : PathSpace (FutureClass M) :=
  (fun t => classOf M (z.1 t),z.2)

private theorem actual_class_cylinder (θ : Presentation H) (hu : RowUnifilar θ.matrix)
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (t : ℤ) (n : ℕ) (q : Fin (n+1) → FutureClass θ.matrix) (w : Fin n → Bool) :
    (J.map (classPath θ.matrix)).real (MarkedPredictiveQuotient.cylinder t n q w) =
      classWeight θ (q 0) * pathMass (classMatrix θ.matrix) n q w := by
  let f : (Fin (n+1) → H) → Set (PathSpace H) := fun h =>
    if classOf θ.matrix ∘ h = q then MarkedPredictiveQuotient.cylinder t n h w else ∅
  have he : classPath θ.matrix ⁻¹' MarkedPredictiveQuotient.cylinder t n q w = ⋃ h, f h := by
    ext z
    simp only [Set.mem_preimage,Set.mem_iUnion]
    constructor
    · intro hz
      let h : Fin (n+1) → H := fun k => z.1 (t+k.val)
      have hh : classOf θ.matrix ∘ h = q := funext hz.1
      exact ⟨h,by simpa [f,hh,MarkedPredictiveQuotient.cylinder,h,classPath] using hz.2⟩
    · rintro ⟨h,hz⟩
      by_cases hh : classOf θ.matrix ∘ h = q
      · have hz' : z ∈ MarkedPredictiveQuotient.cylinder t n h w := by simpa [f,hh] using hz
        exact ⟨fun k => (congrArg (classOf θ.matrix) (hz'.1 k)).trans (congrFun hh k),hz'.2⟩
      · simpa [f,hh] using hz
  have hd : Pairwise (fun h k => Disjoint (f h) (f k)) := by
    intro h k hne
    by_cases hh : classOf θ.matrix ∘ h = q
    · by_cases hk : classOf θ.matrix ∘ k = q
      · simp only [f,if_pos hh,if_pos hk,Set.disjoint_left]
        intro z hz hz'
        exact hne (funext fun j => (hz.1 j).symm.trans (hz'.1 j))
      · simp [f,hk]
    · simp [f,hh]
  have hm : ∀ h, MeasurableSet (f h) := by
    intro h
    dsimp [f]
    split_ifs
    · exact cylinder_measurable t n h w
    · exact MeasurableSet.empty
  rw [measureReal_def,Measure.map_apply (by
    exact (Measurable.of_eval fun t => (measurable_of_finite (classOf θ.matrix)).comp
      ((measurable_pi_apply t).comp measurable_fst)).prodMk measurable_snd)
    (cylinder_measurable t n q w),he]
  change J.real (⋃ h, f h) = _
  rw [measureReal_iUnion_fintype hd hm]
  have hf (h : Fin (n+1) → H) : J.real (f h) = if classOf θ.matrix ∘ h = q
      then θ.initial (h 0) * pathMass θ.matrix n h w else 0 := by
    by_cases hh : classOf θ.matrix ∘ h = q
    · simp only [f,if_pos hh]
      exact hc t n h w
    · simp [f,hh]
  simp_rw [hf]
  exact grouped_paths θ hu n q w

/-- The actual marked pushforward on the selected original bilateral law. -/
def markedLaw [MeasurableSpace H] [MeasurableSingletonClass H] (θ : Presentation H) :
    Measure (PathSpace (FutureClass (trim θ).matrix)) :=
  (jointLaw θ : Measure _).map (fun z => (fun t => originalClass θ t z,z.2))

/-- All marked cylinders, stationary row and every original visible cylinder share J and P.
Only the retained rows are assumed unifilar. -/
theorem actual_marked_quotient [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (hu : RowUnifilar (trim θ).matrix) :
    letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
    (∀ a, 0 ≤ classWeight (trim θ) a) ∧ (∑ a, classWeight (trim θ) a = 1) ∧
    (∀ x a b, 0 ≤ classMatrix (trim θ).matrix x a b) ∧
    (∀ a, ∑ b, (classMatrix (trim θ).matrix false a b +
      classMatrix (trim θ).matrix true a b) = 1) ∧
    RowUnifilar (classMatrix (trim θ).matrix) ∧
    (∀ b, ∑ a, classWeight (trim θ) a * (classMatrix (trim θ).matrix false a b +
      classMatrix (trim θ).matrix true a b) = classWeight (trim θ) b) ∧
    (∀ t n q w, (markedLaw θ).real (MarkedPredictiveQuotient.cylinder t n q w) =
      classWeight (trim θ) (q 0) * pathMass (classMatrix (trim θ).matrix) n q w) ∧
    ((markedLaw θ).map Prod.snd = (visibleLaw θ : Measure _)) ∧
    (∀ a : ℤ, (markedLaw θ).map (shift a) = markedLaw θ) ∧
    (∀ t n w, ((markedLaw θ).map Prod.snd).real (visibleCylinder t n w) =
      ∑ i, θ.initial i * futureMass θ.matrix i n w) := by
  letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
  let F : PathSpace H → PathSpace (FutureClass (trim θ).matrix) :=
    fun z => (fun t => originalClass θ t z,z.2)
  have hF : Measurable F :=
    (Measurable.of_eval (fun t => originalClass_measurable θ t)).prodMk measurable_snd
  have hmap : markedLaw θ = (retainedLaw θ : Measure _).map (classPath (trim θ).matrix) := by
    change ((retainedLaw θ : Measure _).map (includePath θ)).map F = _
    rw [Measure.map_map hF (inclusion_measurable θ)]
    congr 1
    funext z
    dsimp [Function.comp_def,F,classPath]
    apply Prod.ext
    · funext t
      simp [F,originalClass,retainState,state,includePath,classPath,(z.1 t).property]
    · rfl
  have hp : (markedLaw θ).map Prod.snd = (visibleLaw θ : Measure _) := by
    change ((jointLaw θ : Measure _).map F).map Prod.snd = _
    rw [Measure.map_map measurable_snd hF]
    rfl
  refine ⟨weight_nonneg _,weight_total _,?_,?_,?_,weight_stationary _ hu,?_,hp,?_,?_⟩
  · intro x a b
    dsimp [classMatrix]
    split_ifs
    · exact q_nonneg _ _ _
    · exact le_rfl
  · intro a
    simpa [classMatrix,Finset.sum_add_distrib,Fintype.sum_bool,add_comm] using q_total (trim θ) a
  · intro x a b c hb hc
    have hb' : b = quotientSuccessor (trim θ).matrix a x := by
      by_contra hh
      simp [classMatrix,hh] at hb
    have hc' : c = quotientSuccessor (trim θ).matrix a x := by
      by_contra hh
      simp [classMatrix,hh] at hc
    exact hb'.trans hc'.symm
  · intro t n q w
    rw [hmap]
    exact actual_class_cylinder (trim θ) hu (retainedLaw θ : Measure _)
      (same_law_trimming θ).2.1 t n q w
  · intro a
    change ((jointLaw θ : Measure _).map F).map (shift a) = _
    have hs : Measurable (shift (H := FutureClass (trim θ).matrix) a) := by unfold shift; fun_prop
    rw [Measure.map_map hs hF]
    have he : shift a ∘ F = F ∘ shift a := rfl
    rw [he,← Measure.map_map hF (by unfold shift; fun_prop),
      (same_law_trimming θ).2.2.2.2.2.1 a]
    rfl
  · intro t n w
    rw [hp]
    exact (same_law_trimming θ).2.2.2.2.2.2.2.1 t n w

#print axioms actual_marked_quotient

private theorem actual_cell (θ : Presentation H) (hu : RowUnifilar (trim θ).matrix)
    [MeasurableSpace H] [MeasurableSingletonClass H] (r : ℕ) (w : Fin r → Bool)
    (a : FutureClass (trim θ).matrix) :
    letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
    (cellMass (jointLaw θ : Measure _) (originalClass θ 0) (leftWord r ∘ Prod.snd) w a).toReal =
      ∑ i, classWeight (trim θ) i *
        if endpoint (quotientSuccessor (trim θ).matrix) r i w = a then
          wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) r i w else 0 := by
  classical
  letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
  have hm : MeasurableSet ((originalClass θ 0 ⁻¹' {a}) ∩
      ((leftWord r ∘ Prod.snd) ⁻¹' {w})) :=
    ((measurableSet_singleton a).preimage (originalClass_measurable θ 0)).inter
      ((measurableSet_singleton w).preimage (by unfold leftWord; fun_prop))
  change (((retainedLaw θ : Measure _).map (includePath θ)) _).toReal = _
  rw [Measure.map_apply (inclusion_measurable θ) hm]
  have he : includePath θ ⁻¹' ((originalClass θ 0 ⁻¹' {a}) ∩
      ((leftWord r ∘ Prod.snd) ⁻¹' {w})) = endpointEvent (trim θ).matrix (-(r : ℤ)) r w a := by
    ext z
    simp [originalClass,retainState,state,includePath,endpointEvent,leftWord,
      (z.1 0).property,eq_comm,and_comm,funext_iff,leftWord]
  rw [he]
  change (retainedLaw θ : Measure (PathSpace (Positive θ))).real (endpointEvent _ _ _ _ _) = _
  rw [actual_endpoint_mass ⟨Positive θ,inferInstance,trim θ⟩ hu
    (retainedLaw θ : Measure _) (same_law_trimming θ).2.1]
  simpa only [classWeight] using fiber_sum (classOf (trim θ).matrix) (trim θ).initial
    (fun i => if endpoint (quotientSuccessor (trim θ).matrix) r i w = a then
      wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) r i w else 0)

theorem error_real_cells {Ω Q W : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSpace W] [MeasurableSingletonClass Q] [MeasurableSingletonClass W]
    [Fintype Q] [Fintype W] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → Q) (w : Ω → W) (hq : Measurable q) (hw : Measurable w) (m : W → Q) :
    μ.real {z | q z ≠ m (w z)} =
      ∑ b, ((∑ a, (cellMass μ q w b a).toReal) - (cellMass μ q w b (m b)).toReal) := by
  classical
  have hp := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (f := fun z => (w z,q z)) (fun z _ => (measurableSet_singleton z).preimage (hw.prodMk hq))
  have hcell (b : W) (a : Q) : μ.real ((fun z => (w z,q z)) ⁻¹' {(b,a)}) =
      (cellMass μ q w b a).toReal := by
    have he : ((fun z => (w z,q z)) ⁻¹' {(b,a)}) = (q ⁻¹' {a}) ∩ (w ⁻¹' {b}) := by
      ext z
      simp [and_comm]
    rw [he]
    rfl
  have htotal : (∑ b, ∑ a, (cellMass μ q w b a).toReal) = 1 := by
    simpa only [Finset.coe_univ,Set.preimage_univ,Fintype.sum_prod_type,hcell,measureReal_def,measure_univ,ENNReal.toReal_one] using hp
  have hsel : (∑ b, (cellMass μ q w b (m b)).toReal) ≤ 1 := by
    rw [← htotal]
    exact Finset.sum_le_sum (fun b _ => Finset.single_le_sum
      (fun a _ => ENNReal.toReal_nonneg) (Finset.mem_univ (m b)))
  have hn : (∑ b, cellMass μ q w b (m b)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)
  have hsreal : (∑ b, cellMass μ q w b (m b)).toReal =
      ∑ b, (cellMass μ q w b (m b)).toReal := by
    simpa using
      ENNReal.toReal_sum (s := Finset.univ) (f := fun b => cellMass μ q w b (m b))
        (fun _ _ => measure_ne_top _ _)
  have hsel' : (∑ b, cellMass μ q w b (m b)) ≤ 1 := by
    apply (ENNReal.toReal_le_toReal hn ENNReal.one_ne_top).mp
    rw [hsreal,ENNReal.toReal_one]
    exact hsel
  rw [measureReal_def,error_mass_formula μ q w hq hw m,
    ENNReal.toReal_sub_of_le hsel' ENNReal.one_ne_top,ENNReal.toReal_one,
    hsreal,Finset.sum_sub_distrib,htotal]

theorem actual_map_pairs (θ : Presentation H) (hu : RowUnifilar (trim θ).matrix)
    [MeasurableSpace H] [MeasurableSingletonClass H] (r : ℕ) :
    letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
    (classError θ r).toReal ≤
      (∑ i, ∑ j, if h : i ≠ j then
        Real.sqrt (classWeight (trim θ) i * classWeight (trim θ) j) *
          survivingAffinity (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix)
            r ⟨(i,j),h⟩ else 0) / 2 := by
  classical
  letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
  let pi := classWeight (trim θ)
  let p := quotientMass (trim θ).matrix
  let δ := quotientSuccessor (trim θ).matrix
  let A (w : Fin r → Bool) (i : FutureClass (trim θ).matrix) := pi i * wordMass p δ r i w
  have hA (w) (i) : 0 ≤ A w i := mul_nonneg (weight_nonneg _ _)
    (word_nonneg p δ (q_nonneg _) r i w)
  obtain ⟨m,hm,hmax⟩ := current_map_error θ r
  have hcell (w a) : (cellMass (jointLaw θ : Measure _) (originalClass θ 0)
      (leftWord r ∘ Prod.snd) w a).toReal = ∑ i, if endpoint δ r i w = a then A w i else 0 := by
    rw [actual_cell θ hu]
    simp only [A,pi,p,δ,mul_ite,mul_zero] <;> rfl
  have herr : (classError θ r).toReal =
      ∑ w, ((∑ i, A w i) - ∑ i, if endpoint δ r i w = m w then A w i else 0) := by
    rw [← hm]
    change (jointLaw θ : Measure (PathSpace H)).real _ = _
    refine (error_real_cells (jointLaw θ : Measure (PathSpace H)) (originalClass θ 0)
      (leftWord r ∘ Prod.snd) (originalClass_measurable θ 0) (by unfold leftWord; fun_prop) m).trans ?_
    simp_rw [hcell]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
    simp
  have hb (w : Fin r → Bool) := grouped_map_pair_bound (A w) (hA w)
    (fun i => endpoint δ r i w) (m w) (fun a => by
      rw [← hcell,← hcell]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (hmax w a))
  rw [herr]
  apply le_trans (Finset.sum_le_sum (fun w _ => hb w))
  rw [← Finset.sum_div,Finset.sum_comm]
  apply le_of_eq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · rw [dif_pos hij]
    unfold survivingAffinity D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [Subtype.coe_mk,Prod.fst,Prod.snd]
    by_cases hw : endpoint (quotientSuccessor (trim θ).matrix) r i w =
        endpoint (quotientSuccessor (trim θ).matrix) r j w
    · simp [δ,hw]
    · simp only [δ,hw,ne_eq,not_false_eq_true,if_true]
      change Real.sqrt ((pi i*wordMass p δ r i w)*(pi j*wordMass p δ r j w)) = _
      rw [show (pi i*wordMass p δ r i w)*(pi j*wordMass p δ r j w) =
        (pi i*pi j)*(wordMass p δ r i w*wordMass p δ r j w) by ring,
        Real.sqrt_mul (mul_nonneg (weight_nonneg _ _) (weight_nonneg _ _))]

/-- Actual finite MAP loss has a strict law-dependent geometric bound on the same J.
The constant is exactly the unordered stationary class affinity coefficient. -/
theorem actual_geometric_classification [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (hu : RowUnifilar (trim θ).matrix) :
    letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
    let D := pairWeight (classWeight (trim θ))
    0 ≤ D ∧ D ≤ ((Fintype.card (FutureClass (trim θ).matrix) : ℝ)-1)/2 ∧
    ∃ (ell : ℕ) (rho : ℝ), 0 < ell ∧ 0 ≤ rho ∧ rho < 1 ∧
      (∀ a b : FutureClass (trim θ).matrix, a ≠ b →
        wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) ell a ≠
        wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) ell b) ∧
      (∀ a b : FutureClass (trim θ).matrix, a ≠ b →
        D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
          (wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) ell a)
          (wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) ell b) ≤ rho) ∧
      (∀ r (s : Pair (FutureClass (trim θ).matrix)),
        survivingAffinity (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix) r s ≤ rho^(r/ell)) ∧
      (∀ r, classError θ r ≤ ENNReal.ofReal (D*rho^(r/ell))) := by
  classical
  letI := Fintype.ofFinite (FutureClass (trim θ).matrix)
  let pi := classWeight (trim θ)
  let p := quotientMass (trim θ).matrix
  let δ := quotientSuccessor (trim θ).matrix
  have hpi := pair_weight_bound pi (weight_nonneg _) (weight_total _)
  refine ⟨hpi.1,hpi.2.1,?_⟩
  have hd : ∀ a b : FutureClass (trim θ).matrix, a ≠ b →
      ∃ n, wordMass p δ n a ≠ wordMass p δ n b := by
    intro a b hab
    by_contra hn
    push_neg at hn
    apply hab
    have he : (futureSetoid (trim θ).matrix).r a.out b.out := by
      funext n w
      have hh := congrFun (hn n) w
      have ha := word_class (trim θ) hu n a.out w
      have hb := word_class (trim θ) hu n b.out w
      rw [show classOf (trim θ).matrix a.out = a from Quotient.out_eq a] at ha
      rw [show classOf (trim θ).matrix b.out = b from Quotient.out_eq b] at hb
      exact ha.symm.trans (hh.trans hb)
    exact (Quotient.out_eq a).symm.trans ((Quotient.sound he).trans (Quotient.out_eq b))
  obtain ⟨ell,rho,he,hr0,hr1,hdell,haff,hc⟩ := finite_distinguishing_contraction p δ
    (q_nonneg _) (q_total _) hd
  have hsurv (r : ℕ) (s : Pair (FutureClass (trim θ).matrix)) :
      survivingAffinity p δ r s ≤ rho^(r/ell) := by
    rw [← pair_survival_word_affinity p δ (q_nonneg _) r s]
    exact hc r s
  refine ⟨ell,rho,he,hr0,hr1,hdell,haff,hsurv,?_⟩
  intro r
  obtain ⟨m,hm,_⟩ := current_map_error θ r
  have hf : classError θ r ≠ ⊤ := by rw [← hm]; exact measure_ne_top _ _
  apply (ENNReal.le_ofReal_iff_toReal_le hf (mul_nonneg hpi.1 (pow_nonneg hr0 _))).mpr
  apply le_trans (actual_map_pairs θ hu r)
  unfold pairWeight
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · rw [dif_pos hij,if_pos hij]
    exact mul_le_mul_of_nonneg_left (hsurv r ⟨(i,j),hij⟩) (Real.sqrt_nonneg _)

#print axioms actual_geometric_classification
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarQuotient
