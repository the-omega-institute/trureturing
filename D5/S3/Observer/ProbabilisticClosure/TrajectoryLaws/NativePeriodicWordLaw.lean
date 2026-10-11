/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodic installed emissions identify the original complete stopped-word laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators Matrix Classical
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeFullResidual
open NativeObserverJointLaw NativeInstalledFullLaw

abbrev Label := Fin 3
abbrev Config := FiniteFields × Label
instance : MeasurableSpace Config := ⊤
instance : MeasurableSingletonClass Config := ⟨fun _ => trivial⟩

def swap (i : Label) : Label := if i = 0 then 1 else if i = 1 then 0 else 2

structure Parameters where
  w : ℝ
  u : Label → ℝ
  v : Label → ℝ
  w_pos : 0 < w
  w_lt : w < 1/2
  u_box : ∀ i, 1/3 ≤ u i ∧ u i ≤ 2/5
  v_box : ∀ i, 1/3 ≤ v i ∧ v i ≤ 2/5

def pi (T : Parameters) (i : Label) : ℝ := if i = 2 then 1-2*T.w else T.w

private theorem pi_nonneg (T : Parameters) (i : Label) : 0 ≤ pi T i := by
  unfold pi
  split_ifs <;> linarith [T.w_pos, T.w_lt]

private theorem pi_sum (T : Parameters) : ∑ i : Label, ENNReal.ofReal (pi T i) = 1 := by
  rw [Fin.sum_univ_three, ← ENNReal.ofReal_add (pi_nonneg T 0) (pi_nonneg T 1),
    ← ENNReal.ofReal_add (add_nonneg (pi_nonneg T 0) (pi_nonneg T 1)) (pi_nonneg T 2)]
  have hs : pi T 0 + pi T 1 + pi T 2 = 1 := by
    change T.w + T.w + (1-2*T.w) = 1
    ring
  rw [hs]
  simp

def initialLabels (T : Parameters) : PMF Label := PMF.ofFintype _ (pi_sum T)

/-- The alpha update is the identity; the beta update swaps labels zero and one. -/
def nextLabel (op : Operation) (i : Label) : Label :=
  match op with
  | .read b => if b = 0 then i else swap i
  | .stop _ => i

def successor (op : Operation) (z : Config) : Config :=
  ((finiteStep z.1 op).getD z.1, nextLabel op z.2)

def observer (T : Parameters) : Observer Config where
  project := Prod.fst
  init := (initialLabels T).map fun i => (initial.source.finiteFields, i)
  update op z := PMF.pure (successor op z)
  init_refines := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rfl
  update_refines := by
    intro op z f hf z' hz'
    have he : z' = successor op z := by simpa using hz'
    subst z'
    simp [successor, hf]

def rate (T : Parameters) (z : Config) : ℝ :=
  match z.1.control with
  | .fourth (.active .beta) => T.v z.2
  | _ => T.u z.2

private theorem rate_box (T : Parameters) (z : Config) : 1/3 ≤ rate T z ∧ rate T z ≤ 2/5 := by
  unfold rate
  split <;> first | exact T.u_box _ | exact T.v_box _

def coin (T : Parameters) (z : Config) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal (rate T z)
    else ENNReal.ofReal (1-rate T z)) (by
      rw [Fintype.sum_bool]
      change ENNReal.ofReal (rate T z) + ENNReal.ofReal (1-rate T z) = 1
      rw [← ENNReal.ofReal_add (by linarith [(rate_box T z).1, (rate_box T z).2])
        (by linarith [(rate_box T z).1, (rate_box T z).2])]
      simp)

def readEmission (T : Parameters) (z : Config) : PMF (Option Operation) :=
  (coin T z).map (fun b => some (.read (if b then 0 else 1)))

def emission (T : Parameters) (z : Config) : PMF (Option Operation) :=
  match z.1.control with
  | .fourth (.pending b) => PMF.pure (some (.stop b))
  | .fourth .delivered => PMF.pure none
  | _ => readEmission T z

def emitter (T : Parameters) : InstalledEmitter (observer T) where
  emit := emission T
  lawful := by
    intro z a ha
    cases hc : z.1.control with
    | seed f =>
      simp only [emission, hc] at ha
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
      cases f <;> simp [observer, finiteStep, finiteRead, hc]
    | early t s =>
      simp only [emission, hc] at ha
      obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
      simp [observer, finiteStep, finiteRead, hc]
    | fourth c =>
      cases c with
      | active s =>
        simp only [emission, hc] at ha
        obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
        simp [observer, finiteStep, finiteRead, hc]
      | pending b =>
        have he : a = some (.stop b) := by simpa [emission, hc] using ha
        subst a
        simp [observer, finiteStep, finiteStop, hc]
      | delivered =>
        have he : a = none := by simpa [emission, hc] using ha
        subst a
        simpa [observer] using hc

@[fun_prop] private theorem measurable_raw : Measurable (rawFrom (Z := Config)) := by
  fun_prop

@[fun_prop] private theorem measurable_prefix (w : Marked Config) : Measurable (prepend w) := by
  fun_prop

def streamLaw (T : Parameters) (z : Config) : Measure Stream :=
  (markedLaw (observer T) (emitter T) (z, none)).map rawFrom

instance (T : Parameters) (z : Config) : IsProbabilityMeasure (streamLaw T z) :=
  Measure.isProbabilityMeasure_map measurable_raw.aemeasurable

def wordLaw (T : Parameters) (s : ActivePhase) (z : Config) : Measure RawTail :=
  (streamLaw T z).map (stoppedReadWord s)

instance (T : Parameters) (s : ActivePhase) (z : Config) :
    IsProbabilityMeasure (wordLaw T s z) :=
  Measure.isProbabilityMeasure_map (measurable_stopped_read_word s).aemeasurable

def cylinderMass (T : Parameters) (z : Config) (w : List Letter) : ℝ≥0∞ :=
  streamLaw T z (prefixCylinder w)

private theorem initial_mark_irrelevance (T : Parameters) (z : Config) (a : Option Operation) :
    (markedLaw (observer T) (emitter T) (z,a)).map rawFrom = streamLaw T z := by
  rw [streamLaw, marked_regenerate (observer T) (emitter T) (z,a),
    marked_regenerate (observer T) (emitter T) (z,none),
    Measure.map_finset_sum' measurable_raw.aemeasurable,
    Measure.map_finset_sum' measurable_raw.aemeasurable]
  simp only [Measure.map_smul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Measure.map_map measurable_raw (measurable_prefix _),
    Measure.map_map measurable_raw (measurable_prefix _)]
  rfl

private theorem prepended_cylinder (T : Parameters) (z z' : Config) (x b : Letter)
    (w : List Letter) :
    ((markedLaw (observer T) (emitter T) (z',some (.read x))).map
      (rawFrom ∘ prepend (z,none))) (prefixCylinder (b :: w)) =
        if x = b then cylinderMass T z' w else 0 := by
  rw [Measure.map_apply (measurable_raw.comp (measurable_prefix _))
    (measurable_cylinder _)]
  have he : (rawFrom ∘ prepend (z,none)) ⁻¹' prefixCylinder (b :: w) =ᵐ[
      markedLaw (observer T) (emitter T) (z',some (.read x))]
      (if x = b then rawFrom ⁻¹' prefixCylinder w else ∅ : Set (ℕ → Marked Config)) := by
    filter_upwards [marked_head (observer T) (emitter T) (z',some (.read x))] with y hy
    apply propext
    have hp : Prefix (rawFrom (prepend (z,none) y)) (b :: w) ↔
        x = b ∧ Prefix (rawFrom y) w := by
      simp [Prefix, readPrefix, List.ofFn_succ, rawFrom, prepend, hy]
    change Prefix (rawFrom (prepend (z,none) y)) (b :: w) ↔
      y ∈ (if x = b then rawFrom ⁻¹' prefixCylinder w else ∅ : Set (ℕ → Marked Config))
    rw [hp]
    split_ifs with h <;> simp [h, prefixCylinder]
  rw [measure_congr he]
  split_ifs
  · rw [← Measure.map_apply measurable_raw (measurable_cylinder _),
      initial_mark_irrelevance]
    rfl
  · exact measure_empty

private theorem row_active (T : Parameters) (z : Config) (s : ActivePhase)
    (hc : z.1.control = .fourth (.active s)) :
    markedRow (observer T) (emitter T) (z,none) =
      (coin T z).map
        (fun b => (successor (.read (if b then 0 else 1)) z,
          some (.read (if b then 0 else 1)))) := by
  simp [markedRow, emitter, emission, hc, readEmission, PMF.map_bind, observer,
    Function.comp_def, PMF.pure_map]
  rfl

private theorem cylinder_recursion (T : Parameters) (z : Config) (s : ActivePhase)
    (hc : z.1.control = .fourth (.active s)) (b : Letter) (w : List Letter) :
    cylinderMass T z (b :: w) =
      (if b = 0 then ENNReal.ofReal (rate T z) else ENNReal.ofReal (1-rate T z)) *
        cylinderMass T (successor (.read b) z) w := by
  rw [cylinderMass, streamLaw, marked_regenerate (observer T) (emitter T) (z,none),
    Measure.map_finset_sum' measurable_raw.aemeasurable]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.map_smul,
    Measure.smul_apply, smul_eq_mul,
    Measure.map_map measurable_raw (measurable_prefix _)]
  rw [row_active T z s hc]
  simp only [PMF.map_apply, tsum_fintype, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [prepended_cylinder]
  fin_cases b <;> simp [coin, Fintype.sum_bool]

def h (T : Parameters) (i : Label) : ℝ := (1-T.u i) * T.v (swap i)
def g (T : Parameters) (i : Label) : ℝ := (1-T.u i) * (1-T.v (swap i))

/-- One application of the original return matrix diag(1-u) B diag(v). -/
def hStep (T : Parameters) (f : Label → ℝ) (i : Label) : ℝ := h T i * f (swap i)

def B : Matrix Label Label ℝ := fun i j => if j = swap i then 1 else 0
def A : Matrix Label Label ℝ := 1
def H (T : Parameters) : Matrix Label Label ℝ :=
  fun i j => (1-T.u i) * B i j * T.v j

private theorem matrix_step (T : Parameters) (f : Label → ℝ) : H T *ᵥ f = hStep T f := by
  funext i
  simp only [Matrix.mulVec, dotProduct, H, B, hStep, h]
  rw [Finset.sum_eq_single (swap i)]
  · simp
  · intro j _ hj
    simp [hj]
  · exact fun h => (h (Finset.mem_univ _)).elim

def coord (T : Parameters) : ℕ → Letter → Label → ℝ
  | 0, b => if b = 0 then T.u else g T
  | n+1, b => hStep T (coord T n b)

private theorem coord_matrix (T : Parameters) (n : ℕ) (b : Letter) :
    coord T n b = H T ^ n *ᵥ (if b = 0 then T.u else g T) := by
  induction n with
  | zero => simp [coord]
  | succ n ih =>
    rw [coord, ih, pow_succ', ← Matrix.mulVec_mulVec, matrix_step]

def sourceCoord (T : Parameters) (s : ActivePhase) (n : ℕ) (b : Letter) (i : Label) : ℝ :=
  (if s = .p then 1 else T.v i) * (H T ^ n *ᵥ (if b = 0 then T.u else g T)) i

private theorem h_nonneg (T : Parameters) (i : Label) : 0 ≤ h T i :=
  mul_nonneg (by linarith [(T.u_box i).2]) (by linarith [(T.v_box (swap i)).1])

private theorem coord_nonneg (T : Parameters) (n : ℕ) (b : Letter) (i : Label) :
    0 ≤ coord T n b i := by
  induction n generalizing i with
  | zero =>
    simp only [coord]
    split_ifs
    · linarith [(T.u_box i).1]
    · exact mul_nonneg (by linarith [(T.u_box i).2])
        (by linarith [(T.v_box (swap i)).2])
  | succ n ih => exact mul_nonneg (h_nonneg T i) (ih _)

private theorem successor_p (z : Config)
    (hc : z.1.control = .fourth (.active .p)) :
    (successor (.read 1) z).1.control = .fourth (.active .beta) ∧
      (successor (.read 1) z).2 = swap z.2 := by
  simp [successor, finiteStep, finiteRead, payloadRead, payloadControl, hc, nextLabel]

private theorem successor_beta (z : Config)
    (hc : z.1.control = .fourth (.active .beta)) :
    (successor (.read 0) z).1.control = .fourth (.active .p) ∧
      (successor (.read 0) z).2 = z.2 := by
  simp [successor, finiteStep, finiteRead, payloadRead, payloadControl, hc, nextLabel]

private theorem cylinder_nil (T : Parameters) (z : Config) : cylinderMass T z [] = 1 := by
  simp [cylinderMass, prefixCylinder, Prefix, readPrefix]

private theorem p_cylinder (T : Parameters) (z : Config)
    (hc : z.1.control = .fourth (.active .p)) (n : ℕ) (b : Letter) :
    cylinderMass T z (pWord n b) = ENNReal.ofReal (coord T n b z.2) := by
  induction n generalizing z with
  | zero =>
    fin_cases b
    · change cylinderMass T z [0] = ENNReal.ofReal (T.u z.2)
      rw [cylinder_recursion T z .p hc 0 [], cylinder_nil]
      simp [rate, hc]
    · change cylinderMass T z [1,1] = ENNReal.ofReal (g T z.2)
      rw [cylinder_recursion T z .p hc 1 [1],
        cylinder_recursion T (successor (.read 1) z) .beta (successor_p z hc).1 1 [],
        cylinder_nil]
      simp only [rate, hc, (successor_p z hc).1, (successor_p z hc).2,
        Fin.reduceEq, if_false, mul_one, g]
      exact (ENNReal.ofReal_mul (by linarith [(T.u_box z.2).2])).symm
  | succ n ih =>
    rw [p_word_succ, cylinder_recursion T z .p hc 1 _,
      cylinder_recursion T (successor (.read 1) z) .beta (successor_p z hc).1 0 _]
    rw [ih _ (successor_beta _ (successor_p z hc).1).1]
    simp only [rate, hc, (successor_p z hc).1, (successor_p z hc).2,
      (successor_beta _ (successor_p z hc).1).2, Fin.reduceEq, if_false, if_true,
      coord, hStep, h]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith [(T.u_box z.2).2]),
      ← ENNReal.ofReal_mul (p := (1-T.u z.2)*T.v (swap z.2))
        (show 0 ≤ (1-T.u z.2)*T.v (swap z.2) from h_nonneg T z.2)]

def typeWord (s : ActivePhase) (n : ℕ) (b : Letter) : List Letter :=
  match s with
  | .p => pWord n b
  | .beta => 0 :: pWord n b

def nativeCoord (T : Parameters) (s : ActivePhase) (n : ℕ) (b : Letter) (i : Label) : ℝ :=
  match s with
  | .p => coord T n b i
  | .beta => T.v i * coord T n b i

@[simp] private theorem source_coord_eq (T : Parameters) (s : ActivePhase)
    (n : ℕ) (b : Letter) (i : Label) : sourceCoord T s n b i = nativeCoord T s n b i := by
  cases s
  · simp [sourceCoord, nativeCoord, ← coord_matrix]
  · have hne : ActivePhase.beta ≠ .p := by intro he; cases he
    simp [sourceCoord, nativeCoord, ← coord_matrix, hne]

private theorem finite_word (T : Parameters) (s : ActivePhase) (z : Config)
    (w : List Letter) (hw : ∃ b, WordFamily s b w) :
    wordLaw T s z {some w} = cylinderMass T z w := by
  rw [wordLaw, Measure.map_apply (measurable_stopped_read_word s)
    (measurableSet_singleton _)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, stopped_word_fiber,
    prefixCylinder, Set.mem_ofPred_eq, hw, and_true]

/-- The four indexed source coordinates and the immediate suspended coordinate
are probabilities of the original first-completion words, under the installed
generator using the same acquired-letter updates. -/
theorem native_word_identification (T : Parameters) (s : ActivePhase) (z : Config)
    (hc : z.1.control = .fourth (.active s)) :
    (∀ n b, (wordLaw T s z).real {some (typeWord s n b)} = sourceCoord T s n b z.2) ∧
      (s = .beta → (wordLaw T s z).real {some [1]} = 1-T.v z.2) := by
  simp only [source_coord_eq]
  cases s with
  | p =>
    refine ⟨?_, by intro he; cases he⟩
    intro n b
    rw [Measure.real, typeWord, finite_word T .p z (pWord n b) ⟨b,n,rfl⟩,
      p_cylinder T z hc, ENNReal.toReal_ofReal (coord_nonneg T n b z.2)]
    rfl
  | beta =>
    constructor
    · intro n b
      rw [Measure.real, typeWord, finite_word T .beta z (0 :: pWord n b)
        ⟨b,Or.inr ⟨n,rfl⟩⟩, cylinder_recursion T z .beta hc 0 _,
        p_cylinder T _ (successor_beta z hc).1]
      simp only [Fin.reduceEq, if_true, rate, hc, (successor_beta z hc).2,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ T.v z.2 by linarith [(T.v_box z.2).1]),
        ENNReal.toReal_ofReal (coord_nonneg T n b z.2), nativeCoord]
    · intro _
      rw [Measure.real, finite_word T .beta z [1] ⟨1,Or.inl ⟨rfl,rfl⟩⟩,
        cylinder_recursion T z .beta hc 1 [], cylinder_nil]
      simp only [Fin.reduceEq, if_false, mul_one, rate, hc,
        ENNReal.toReal_ofReal (show 0 ≤ 1-T.v z.2 by linarith [(T.v_box z.2).2])]

def survival (T : Parameters) : ℕ → Label → ℝ
  | 0, _ => 1
  | n+1, i => h T i * survival T n (swap i)

private theorem h_bound (T : Parameters) (i : Label) : h T i ≤ 4/15 := by
  have hu := T.u_box i
  have hv := T.v_box (swap i)
  unfold h
  nlinarith [mul_nonneg (show 0 ≤ 1-T.u i by linarith)
    (show 0 ≤ 2/5-T.v (swap i) by linarith),
    mul_nonneg (show 0 ≤ T.u i-1/3 by linarith) (show 0 ≤ T.v (swap i) by linarith)]

private theorem survival_bounds (T : Parameters) (n : ℕ) (i : Label) :
    0 ≤ survival T n i ∧ survival T n i ≤ (4/15)^n := by
  induction n generalizing i with
  | zero => simp [survival]
  | succ n ih =>
    obtain ⟨hn,hb⟩ := ih (swap i)
    constructor
    · exact mul_nonneg (h_nonneg T i) hn
    · exact (mul_le_mul (h_bound T i) hb hn (by norm_num)).trans_eq
        (by rw [pow_succ]; ring)

private theorem loop_cylinder (T : Parameters) (z : Config)
    (hc : z.1.control = .fourth (.active .p)) (n : ℕ) :
    cylinderMass T z (loopWord n) = ENNReal.ofReal (survival T n z.2) := by
  induction n generalizing z with
  | zero => simp [loopWord, cylinder_nil, survival]
  | succ n ih =>
    rw [loop_succ, cylinder_recursion T z .p hc 1 _,
      cylinder_recursion T (successor (.read 1) z) .beta (successor_p z hc).1 0 _,
      ih _ (successor_beta _ (successor_p z hc).1).1]
    simp only [rate, hc, (successor_p z hc).1, (successor_p z hc).2,
      (successor_beta _ (successor_p z hc).1).2, Fin.reduceEq, if_false, if_true,
      survival, h]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith [(T.u_box z.2).2]),
      ← ENNReal.ofReal_mul (p := (1-T.u z.2)*T.v (swap z.2))
        (show 0 ≤ (1-T.u z.2)*T.v (swap z.2) from h_nonneg T z.2)]

/-- Emission bounds alone give complete normalization and zero mass to the
original native noncompletion outcome, in both phases. -/
theorem native_noncompletion (T : Parameters) (s : ActivePhase) (z : Config)
    (hc : z.1.control = .fourth (.active s)) :
    wordLaw T s z Set.univ = 1 ∧ wordLaw T s z {none} = 0 := by
  refine ⟨measure_univ, ?_⟩
  rw [wordLaw, Measure.map_apply (measurable_stopped_read_word s)
    (measurableSet_singleton _)]
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (ENNReal.ofReal (4/15:ℝ)) < 1 by norm_num)
  apply le_antisymm _ (by positivity)
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  cases s with
  | p =>
    calc
      streamLaw T z ((stoppedReadWord .p) ⁻¹' {none}) ≤
          cylinderMass T z (loopWord n) := by
        apply measure_mono
        intro ω hω
        have hn : stoppedReadWord .p ω = none := hω
        rw [(noncompletion_fiber .p ω).mp hn]
        change Prefix (infiniteTail .p) (loopWord n)
        unfold Prefix
        rw [loop_as_prefix, prefix_length]
      _ = ENNReal.ofReal (survival T n z.2) := loop_cylinder T z hc n
      _ ≤ (ENNReal.ofReal (4/15:ℝ))^n := by
        rw [← ENNReal.ofReal_pow (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (survival_bounds T n z.2).2

  | beta =>
    calc
      streamLaw T z ((stoppedReadWord .beta) ⁻¹' {none}) ≤
          cylinderMass T z (0 :: loopWord n) := by
        apply measure_mono
        intro ω hω
        have hn : stoppedReadWord .beta ω = none := hω
        have hpath := (noncompletion_fiber .beta ω).mp hn
        obtain ⟨h0,hh⟩ := nonstop_beta_return ω
          (hpath.symm ▸ infinite_tail_nonstop .beta)
        have hp := nonstop_p_prefix _ hh n
        change Prefix ω (0 :: loopWord n)
        simpa [Prefix, prefix_succ, h0] using
          congrArg (fun w => (0 : Letter) :: w) hp
      _ = ENNReal.ofReal (T.v z.2) *
          ENNReal.ofReal (survival T n z.2) := by
        rw [cylinder_recursion T z .beta hc 0 _,
          loop_cylinder T _ (successor_beta z hc).1]
        simp [rate, hc, (successor_beta z hc).2]
      _ ≤ ENNReal.ofReal (survival T n z.2) := by
        exact mul_le_of_le_one_left (by positivity)
          (by rw [ENNReal.ofReal_le_one]; linarith [(T.v_box z.2).2])
      _ ≤ (ENNReal.ofReal (4/15:ℝ))^n := by
        rw [← ENNReal.ofReal_pow (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (survival_bounds T n z.2).2


def eta (T : Parameters) : ℝ := h T 0 * h T 1
def fixedRate (T : Parameters) : ℝ := h T 2
def periodRate (T : Parameters) (i : Label) : ℝ :=
  if i = 2 then fixedRate T ^ 2 else eta T

@[simp] private theorem beta_ne_p : ActivePhase.beta ≠ .p := by
  intro h
  cases h

def pureCoeff (r : ℝ) (s : ActivePhase) (b : Letter) : ℝ :=
  (if s = .p then 1 else r) * (if b = 0 then r else (1-r)^2)

def pureCoord (r : ℝ) (s : ActivePhase) (n : ℕ) (b : Letter) : ℝ :=
  pureCoeff r s b * (r*(1-r))^n

def InBox (x a b : ℝ) : Prop := min a b ≤ x ∧ x ≤ max a b

def IndexedBox (T : Parameters) (s : ActivePhase) (n : ℕ) (b : Letter) (i : Label) : Prop :=
  InBox (nativeCoord T s n b i) (pureCoord (1/3) s n b) (pureCoord (2/5) s n b)

def Seeds (T : Parameters) : Prop := ∀ s n, n ≤ 4 → ∀ b i,
  InBox (sourceCoord T s n b i) (pureCoord (1/3) s n b) (pureCoord (2/5) s n b)
def Rates (T : Parameters) : Prop :=
  (2/9)^2 ≤ eta T ∧ eta T ≤ (6/25)^2 ∧ 2/9 ≤ fixedRate T ∧ fixedRate T ≤ 6/25

private theorem swap_involutive (i : Label) : swap (swap i) = i := by
  fin_cases i <;> rfl

private theorem coord_two (T : Parameters) (n : ℕ) (b : Letter) (i : Label) :
    coord T (n+2) b i = periodRate T i * coord T n b i := by
  simp only [coord, hStep, swap_involutive]
  fin_cases i
  · change h T 0 * (h T 1 * coord T n b 0) =
      (h T 0 * h T 1) * coord T n b 0
    ring
  · change h T 1 * (h T 0 * coord T n b 1) =
      (h T 0 * h T 1) * coord T n b 1
    ring
  · change h T 2 * (h T 2 * coord T n b 2) = h T 2 ^ 2 * coord T n b 2
    ring

private theorem native_two (T : Parameters) (s : ActivePhase) (n : ℕ)
    (b : Letter) (i : Label) :
    nativeCoord T s (n+2) b i = periodRate T i * nativeCoord T s n b i := by
  cases s <;> simp only [nativeCoord, coord_two] <;> ring

private theorem coord_even (T : Parameters) (n : ℕ) (b : Letter) (i : Label) :
    coord T (2*n) b i = periodRate T i ^ n * coord T 0 b i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+2 by omega, coord_two, ih, pow_succ]
    ring

private theorem fixed_coord (T : Parameters) (n : ℕ) (b : Letter) :
    coord T n b 2 = fixedRate T ^ n * coord T 0 b 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [coord, hStep, show swap 2 = 2 from rfl]
    rw [ih, pow_succ]
    simp only [fixedRate, coord]
    ring

private theorem pure_nonneg (s : ActivePhase) (n : ℕ) (b : Letter) :
    0 ≤ pureCoord (1/3) s n b ∧ 0 ≤ pureCoord (2/5) s n b := by
  cases s <;> fin_cases b <;> norm_num [pureCoord, pureCoeff] <;> positivity

private theorem native_nonneg (T : Parameters) (s : ActivePhase)
    (n : ℕ) (b : Letter) (i : Label) : 0 ≤ nativeCoord T s n b i := by
  cases s
  · exact coord_nonneg T n b i
  · exact mul_nonneg (by linarith [(T.v_box i).1]) (coord_nonneg T n b i)

private theorem pure_succ (r : ℝ) (s : ActivePhase) (n : ℕ) (b : Letter) :
    pureCoord r s (n+1) b = (r*(1-r)) * pureCoord r s n b := by
  simp only [pureCoord, pow_succ]
  ring

private theorem pure_two (r : ℝ) (s : ActivePhase) (n : ℕ) (b : Letter) :
    pureCoord r s (n+2) b = (r*(1-r))^2 * pureCoord r s n b := by
  rw [pure_succ, pure_succ]
  ring

private theorem tail_order (s : ActivePhase) (b : Letter) (n : ℕ) (hn : 3 ≤ n) :
    pureCoord (1/3) s n b ≤ pureCoord (2/5) s n b := by
  induction n, hn using Nat.le_induction with
  | base => cases s <;> fin_cases b <;> norm_num [pureCoord, pureCoeff]
  | succ n hn ih =>
    rw [pure_succ, pure_succ]
    exact mul_le_mul (by norm_num) ih (pure_nonneg s n b).1 (by norm_num)

def crossover (s : ActivePhase) (b : Letter) : ℕ :=
  if b = 0 then 0 else if s = .p then 3 else 1

private theorem zero_order (n : ℕ) :
    pureCoord (1/3) .p n 0 ≤ pureCoord (2/5) .p n 0 := by
  simp only [pureCoord, pureCoeff, if_pos rfl, one_mul]
  exact mul_le_mul (by norm_num)
    (pow_le_pow_left₀ (by norm_num) (by norm_num) n) (by positivity) (by norm_num)

private theorem endpoint_order (s : ActivePhase) (b : Letter) (n : ℕ) :
    (crossover s b ≤ n → pureCoord (1/3) s n b ≤ pureCoord (2/5) s n b) ∧
      (n < crossover s b → pureCoord (2/5) s n b ≤ pureCoord (1/3) s n b) := by
  by_cases hn : 3 ≤ n
  · refine ⟨fun _ => tail_order s b n hn, ?_⟩
    intro h
    have hc : crossover s b ≤ 3 := by
      cases s <;> fin_cases b <;> norm_num [crossover]
    omega
  · have hn' : n ≤ 2 := by omega
    interval_cases n <;> cases s <;> fin_cases b <;>
      norm_num [pureCoord, pureCoeff, crossover]

private theorem h_pos (T : Parameters) (i : Label) : 0 < h T i :=
  mul_pos (by linarith [(T.u_box i).2]) (by linarith [(T.v_box (swap i)).1])

private theorem period_bounds (T : Parameters) (hr : Rates T) (i : Label) :
    (2/9)^2 ≤ periodRate T i ∧ periodRate T i ≤ (6/25)^2 := by
  rcases hr with ⟨hlo,hhi,hflo,hfhi⟩
  unfold periodRate
  split_ifs
  · constructor <;> nlinarith
  · exact ⟨hlo,hhi⟩

private theorem all_indices (T : Parameters) (hr : Rates T) (hs : Seeds T) :
    ∀ s n b i, IndexedBox T s n b i := by
  intro s n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b i
    by_cases hn : n ≤ 4
    · simpa only [IndexedBox, source_coord_eq] using hs s n hn b i
    · let m := n-2
      have hm : 3 ≤ m := by dsimp [m]; omega
      have hnm : n = m+2 := by dsimp [m]; omega
      have hc : crossover s b ≤ m := by
        have hh : crossover s b ≤ 3 := by
          cases s <;> fin_cases b <;> norm_num [crossover]
        omega
      have ho := (endpoint_order s b m).1 hc
      have ho' := (endpoint_order s b n).1 (by omega)
      have hprev := ih m (by dsimp [m]; omega) b i
      change InBox _ _ _ at hprev ⊢
      rw [InBox, min_eq_left ho, max_eq_right ho] at hprev
      rw [InBox, min_eq_left ho', max_eq_right ho', hnm, native_two, pure_two, pure_two]
      constructor
      · exact mul_le_mul (by have hh := (period_bounds T hr i).1; norm_num at hh ⊢; exact hh) hprev.1
          (pure_nonneg s m b).1 (le_trans (by norm_num) (period_bounds T hr i).1)
      · exact mul_le_mul (by have hh := (period_bounds T hr i).2; norm_num at hh ⊢; exact hh) hprev.2
          (native_nonneg T s m b i) (by norm_num)

private theorem geometric_rate_bound {x y A B : ℝ} (hy : 0 < y) (hA : 0 < A)
    (hb : ∀ n : ℕ, A*x^n ≤ B*y^n) : x ≤ y := by
  by_contra h
  have hxy : y < x := lt_of_not_ge h
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (B/A) ((one_lt_div hy).mpr hxy)
  have he : A*(x/y)^n ≤ B := by
    rw [div_pow, ← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hy n)).mpr (hb n)
  have he' : (x/y)^n ≤ B/A :=
    (le_div_iff₀ hA).mpr (by nlinarith [he])
  linarith

private theorem rate_necessity (T : Parameters)
    (hb : ∀ s n b i, IndexedBox T s n b i) : Rates T := by
  have he (n : ℕ) (i : Label) :
      pureCoord (1/3) .p n 0 ≤ coord T n 0 i ∧
        coord T n 0 i ≤ pureCoord (2/5) .p n 0 := by
    have hh := hb .p n 0 i
    simpa only [IndexedBox, InBox, nativeCoord,
      min_eq_left (zero_order n), max_eq_right (zero_order n)] using hh
  have ha : ((1/3:ℝ)*(1-1/3)) = 2/9 := by norm_num
  have hb' : ((2/5:ℝ)*(1-2/5)) = 6/25 := by norm_num
  have heta : 0 < eta T := mul_pos (h_pos T 0) (h_pos T 1)
  have hfixed : 0 < fixedRate T := h_pos T 2
  have heven (n : ℕ) := he (2*n) 0
  simp only [coord_even, periodRate, Fin.reduceEq, if_false, coord, if_true,
    pureCoord, pureCoeff, one_mul, ha, hb'] at heven
  have hf (n : ℕ) := he n 2
  simp only [fixed_coord, coord, if_true, pureCoord, pureCoeff, one_mul, ha, hb'] at hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply geometric_rate_bound (B := T.u 0) heta (by norm_num : (0:ℝ) < 1/3)
    intro n
    have hh := (heven n).1
    rw [pow_mul] at hh
    simpa only [mul_comm] using hh
  · apply geometric_rate_bound (B := 2/5) (by norm_num : (0:ℝ) < (6/25)^2)
      (by linarith [(T.u_box 0).1] : 0 < T.u 0)
    intro n
    have hh := (heven n).2
    rw [pow_mul] at hh
    simpa only [mul_comm] using hh
  · apply geometric_rate_bound (B := T.u 2) hfixed (by norm_num : (0:ℝ) < 1/3)
    intro n
    have hh := (hf n).1
    simpa only [mul_comm] using hh
  · apply geometric_rate_bound (B := 2/5) (by norm_num : (0:ℝ) < 6/25)
      (by linarith [(T.u_box 2).1] : 0 < T.u 2)
    intro n
    have hh := (hf n).2
    simpa only [mul_comm] using hh

theorem endpoint_coordinates (r : unitInterval) (s : ActivePhase)
    (n : ℕ) (b : Letter) :
    (explicitStoppedWordLaw s r).real {some (typeWord s n b)} =
      pureCoord (r:ℝ) s n b := by
  cases s with
  | p =>
    fin_cases b
    · change (explicitStoppedWordLaw .p r).real {some (pWord n 0)} =
        pureCoord (r:ℝ) .p n 0
      rw [Measure.real, explicit_finite_mass,
        if_pos (show ∃ b, WordFamily .p b (pWord n 0) from ⟨0,n,rfl⟩), p_word_mass]
      simp [alphaMass, betaMass, pureCoord, pureCoeff, unitInterval.coe_symm_eq]
    · simpa [typeWord, pureCoord, pureCoeff] using
        ConstantSuspensionSeparator.endpoint_p_word r n
  | beta =>
    rw [Measure.real, typeWord, explicit_finite_mass,
      if_pos (show ∃ b', WordFamily .beta b' (0 :: pWord n b) from
        ⟨b,Or.inr ⟨n,rfl⟩⟩)]
    change ((bernoulliMeasure (0 : Letter) 1 r) {0} * wordMass r (pWord n b)).toReal = _
    rw [p_word_mass]
    fin_cases b <;>
      simp [bernoulliMeasure, alphaMass, betaMass, pureCoord, pureCoeff,
        unitInterval.coe_symm_eq] <;> ring

theorem endpoint_immediate (r : unitInterval) :
    (explicitStoppedWordLaw .beta r).real {some [1]} = 1-(r:ℝ) := by
  rw [Measure.real, explicit_finite_mass,
    if_pos (show ∃ b, WordFamily .beta b [1] from ⟨1,Or.inl ⟨rfl,rfl⟩⟩)]
  simp [wordMass, bernoulliMeasure, unitInterval.coe_symm_eq]

def FullBoxes (T : Parameters) : Prop :=
  ∀ (s : ActivePhase) (z : Config), z.1.control = .fourth (.active s) →
    ∀ t : ValidTail s, InBox ((wordLaw T s z).real {t.val})
      ((explicitStoppedWordLaw s ConstantSuspensionSeparator.endpointA).real {t.val})
      ((explicitStoppedWordLaw s ConstantSuspensionSeparator.endpointB).real {t.val})

def ImmediateBoxes (T : Parameters) : Prop := ∀ i, 1-2/5 ≤ 1-T.v i ∧ 1-T.v i ≤ 1-1/3

def atLabel (s : ActivePhase) (i : Label) : Config := (⟨.fourth (.active s),emptyRegisters⟩,i)

private theorem full_to_indices (T : Parameters) (hf : FullBoxes T) :
    (∀ s n b i, IndexedBox T s n b i) ∧ ImmediateBoxes T := by
  constructor
  · intro s n b i
    have hv : Valid s (some (typeWord s n b)) := by
      cases s
      · exact ⟨b,n,rfl⟩
      · exact ⟨b,Or.inr ⟨n,rfl⟩⟩
    have hh := hf s (atLabel s i) rfl ⟨some (typeWord s n b),hv⟩
    rw [(native_word_identification T s _ rfl).1 n b,
      endpoint_coordinates, endpoint_coordinates] at hh
    simpa only [source_coord_eq, IndexedBox, atLabel,
      ConstantSuspensionSeparator.endpointA, ConstantSuspensionSeparator.endpointB] using hh
  · intro i
    have hh := hf .beta (atLabel .beta i) rfl ⟨some [1],1,Or.inl ⟨rfl,rfl⟩⟩
    rw [(native_word_identification T .beta _ rfl).2 rfl,
      endpoint_immediate, endpoint_immediate] at hh
    norm_num [InBox, ConstantSuspensionSeparator.endpointA,
      ConstantSuspensionSeparator.endpointB, atLabel] at hh ⊢
    exact hh

private theorem indices_to_full (T : Parameters)
    (hi : ∀ s n b i, IndexedBox T s n b i) (hb : ImmediateBoxes T) : FullBoxes T := by
  intro s z hc t
  rcases t with ⟨t,ht⟩
  change InBox ((wordLaw T s z).real {t})
    ((explicitStoppedWordLaw s ConstantSuspensionSeparator.endpointA).real {t})
    ((explicitStoppedWordLaw s ConstantSuspensionSeparator.endpointB).real {t})
  cases t with
  | none =>
    rw [Measure.real, (native_noncompletion T s z hc).2]
    cases s <;> simp [InBox, Measure.real, explicitStoppedWordLaw, Measure.sum_apply]
  | some w =>
    obtain ⟨b,hb'⟩ := ht
    cases s with
    | p =>
      obtain ⟨n,rfl⟩ := hb'
      have hn := (native_word_identification T .p z hc).1 n b
      have he := endpoint_coordinates ConstantSuspensionSeparator.endpointA .p n b
      have he' := endpoint_coordinates ConstantSuspensionSeparator.endpointB .p n b
      change InBox ((wordLaw T .p z).real {some (typeWord .p n b)}) _ _
      simp only [typeWord] at hn he he'
      simp only [typeWord]
      rw [hn,source_coord_eq,he,he']
      exact hi .p n b z.2
    | beta =>
      rcases hb' with ⟨rfl,rfl⟩ | ⟨n,rfl⟩
      · rw [(native_word_identification T .beta z hc).2 rfl,
          endpoint_immediate, endpoint_immediate]
        have hh := hb z.2
        norm_num [InBox, ConstantSuspensionSeparator.endpointA,
          ConstantSuspensionSeparator.endpointB] at hh ⊢
        exact hh
      · have hn := (native_word_identification T .beta z hc).1 n b
        have he := endpoint_coordinates ConstantSuspensionSeparator.endpointA .beta n b
        have he' := endpoint_coordinates ConstantSuspensionSeparator.endpointB .beta n b
        change InBox ((wordLaw T .beta z).real {some (typeWord .beta n b)}) _ _
        simp only [typeWord] at hn he he'
        simp only [typeWord]
        rw [hn,source_coord_eq,he,he']
        exact hi .beta n b z.2

/-- Every coordinate on each complete native word carrier satisfies its endpoint
box exactly when the original rates, immediate beta coordinates and all four
families through index four satisfy their closed bounds. -/
private theorem raw_full_box_criterion (T : Parameters) :
    FullBoxes T ↔ Rates T ∧ ImmediateBoxes T ∧ Seeds T := by
  constructor
  · intro hf
    obtain ⟨hi,hb⟩ := full_to_indices T hf
    refine ⟨rate_necessity T hi,hb,?_⟩
    intro s n _ b i
    simpa only [IndexedBox, source_coord_eq] using hi s n b i
  · rintro ⟨hr,hb,hs⟩
    exact indices_to_full T (all_indices T hr hs) hb

def endpointTail (r : unitInterval) (s : ActivePhase) : Measure (ValidTail s) :=
  (rawReadLaw r).map (tailValue s)

def endpointFull (r : unitInterval) (c : AcquiredNativeState) : Measure FullTranscript :=
  (rawReadLaw r).map (fullTranscript c)

private theorem endpoint_rendering (r : unitInterval) (c : AcquiredNativeState)
    (s : ActivePhase) (hc : c.source.finiteFields.control = .fourth (.active s)) :
    endpointFull r c = (endpointTail r s).map (fullRenderer c s) := by
  rw [endpointFull, endpointTail, Measure.map_map (measurable_of_countable _)
    (by fun_prop : Measurable (tailValue s))]
  congr 1
  funext ω
  exact full_renderer_all_paths c s hc ω

private theorem renderer_point {s : ActivePhase} (μ : Measure (ValidTail s)) (c : AcquiredNativeState)
    (hc : c.source.finiteFields.control = .fourth (.active s)) (t : ValidTail s) :
    (μ.map (fullRenderer c s)).real {fullRenderer c s t} = μ.real {t} := by
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  apply congrArg ENNReal.toReal
  apply congrArg μ
  ext t'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro he
    apply Subtype.ext
    have hh := congrArg readbackRaw he
    simpa only [full_renderer_readback c s hc] using hh
  · intro he
    rw [he]

private theorem installed_point (T : Parameters) (c : AcquiredNativeState)
    (s : ActivePhase) (hc : c.source.finiteFields.control = .fourth (.active s))
    (i : Label) (t : ValidTail s) :
    (fullLaw (observer T) (emitter T) (c.source.finiteFields,i)).real
      {fullRenderer c s t} = (wordLaw T s (c.source.finiteFields,i)).real {t.val} := by
  rw [installed_configuration_identity (observer T) (emitter T) s
    (c.source.finiteFields,i) c rfl hc, renderer_point _ c hc t]
  rw [Measure.real, tailLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    Measure.real, wordLaw, streamLaw,
    Measure.map_map (measurable_stopped_read_word s) measurable_raw,
    Measure.map_apply ((measurable_stopped_read_word s).comp measurable_raw)
      (measurableSet_singleton _)]
  congr 2
  ext x
  simp [tailValue, Set.mem_preimage, Subtype.ext_iff]

private theorem endpoint_point (r : unitInterval) (c : AcquiredNativeState)
    (s : ActivePhase) (hc : c.source.finiteFields.control = .fourth (.active s))
    (t : ValidTail s) :
    (endpointFull r c).real {fullRenderer c s t} =
      (explicitStoppedWordLaw s r).real {t.val} := by
  rw [endpoint_rendering r c s hc, renderer_point _ c hc t,
    ← (actual_fourth_segment_stopped_word_law r s).2]
  rw [Measure.real, endpointTail, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    Measure.real, Measure.map_apply (measurable_stopped_read_word s)
      (measurableSet_singleton _)]
  congr 2
  ext x
  simp [tailValue, Set.mem_preimage, Subtype.ext_iff]

def RenderedBoxes (T : Parameters) : Prop :=
  ∀ (c : AcquiredNativeState) (s : ActivePhase),
    c.source.finiteFields.control = .fourth (.active s) → ∀ (i : Label) (t : ValidTail s),
      InBox ((fullLaw (observer T) (emitter T) (c.source.finiteFields,i)).real
        {fullRenderer c s t})
        ((endpointFull ConstantSuspensionSeparator.endpointA c).real {fullRenderer c s t})
        ((endpointFull ConstantSuspensionSeparator.endpointB c).real {fullRenderer c s t})

private theorem rendered_raw (T : Parameters) : RenderedBoxes T ↔ FullBoxes T := by
  constructor
  · intro hr s z hz t
    have hh := hr (representative z.1) s hz z.2 t
    rw [installed_point T (representative z.1) s hz z.2 t,
      endpoint_point ConstantSuspensionSeparator.endpointA (representative z.1) s hz t,
      endpoint_point ConstantSuspensionSeparator.endpointB (representative z.1) s hz t] at hh
    exact hh
  · intro hr c s hc i t
    rw [installed_point T c s hc i t,
      endpoint_point ConstantSuspensionSeparator.endpointA c s hc t,
      endpoint_point ConstantSuspensionSeparator.endpointB c s hc t]
    exact hr s (c.source.finiteFields,i) hc t

/-- The periodic criterion holds on the literal complete native transcripts.
Every installed phase law normalizes without conditioning, and its original
infinite noncompletion transcript has zero mass under the emission domain alone. -/
theorem native_full_box_criterion (T : Parameters) :
    ((∀ (c : AcquiredNativeState) (s : ActivePhase),
        c.source.finiteFields.control = .fourth (.active s) →
        ∀ (i : Label) (t : ValidTail s),
          InBox ((fullLaw (observer T) (emitter T) (c.source.finiteFields,i)).real
            {fullRenderer c s t})
            ((endpointFull ConstantSuspensionSeparator.endpointA c).real {fullRenderer c s t})
            ((endpointFull ConstantSuspensionSeparator.endpointB c).real {fullRenderer c s t})) ↔
        Rates T ∧ ImmediateBoxes T ∧ Seeds T) ∧
      (∀ (c : AcquiredNativeState) (s : ActivePhase),
        c.source.finiteFields.control = .fourth (.active s) → ∀ i : Label,
          fullLaw (observer T) (emitter T) (c.source.finiteFields,i) Set.univ = 1 ∧
            fullLaw (observer T) (emitter T) (c.source.finiteFields,i)
              {fullRenderer c s ⟨none,trivial⟩} = 0) := by
  refine ⟨(rendered_raw T).trans (raw_full_box_criterion T), ?_⟩
  intro c s hc i
  refine ⟨measure_univ, ?_⟩
  have hh := installed_point T c s hc i ⟨none,trivial⟩
  rw [Measure.real, Measure.real, (native_noncompletion T s _ hc).2,
    ENNReal.toReal_zero] at hh
  exact (ENNReal.toReal_eq_zero_iff _).mp hh |>.resolve_right (measure_ne_top _ _)

#print axioms native_word_identification
#print axioms native_noncompletion
#print axioms native_full_box_criterion


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
