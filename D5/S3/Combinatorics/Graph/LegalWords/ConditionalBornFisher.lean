/- GID: D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual endpoint conditioning and count information of legal Born blocks. -/
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditiveTrajectory

/-! # Endpoint-conditioned circuit observations and their count information -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix
namespace D5.S3.Combinatorics.Graph.LegalWords.ConditionalBornFisher
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.Entanglement.PhaseHistoryBound (transition)
open D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight

/-- Illegal padded words contain a forbidden transition and have zero mass. -/
theorem illegal_mass_zero (q : ℝ) (m : ℕ) (l r : Bool) (w : Fin m → Bool)
    (hw : ¬ Adm (m+2) (Fin.cons l (Fin.snoc w r))) :
    pathMass q m l w r = 0 := by
  induction m generalizing l with
  | zero =>
    cases l <;> cases r <;> simp [Adm, pathMass, transition, Fin.snoc] at hw ⊢
  | succ m ih =>
    have he : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
    have hh : ¬ ((¬ (l ∧ w 0)) ∧
        Adm (m+2) (Fin.cons (w 0) (Fin.snoc (Fin.tail w) r))) := by
      rw [he, ← Fin.cons_snoc_eq_snoc_cons] at hw
      simpa [Adm, Fin.cons_zero, Fin.cons_one, Fin.tail_cons] using hw
    rw [pathMass]
    by_cases ha : ¬ (l ∧ w 0)
    · rw [ih (w 0) (Fin.tail w) (fun h => hh ⟨ha, h⟩), mul_zero]
    · have hl : l = true := (not_not.mp ha).1
      have hw0 : w 0 = true := (not_not.mp ha).2
      simp [transition, hl, hw0]

private theorem mass_nonneg (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) (l r : Bool) (w : Fin m → Bool) : 0 ≤ pathMass q m l w r := by
  induction m generalizing l with
  | zero => cases l <;> cases r <;> simp [pathMass, transition, hq, sub_nonneg.mpr hq1]
  | succ m ih =>
    apply mul_nonneg _ (ih (w 0) (Fin.tail w))
    cases l <;> cases w 0 <;> simp [transition, hq, sub_nonneg.mpr hq1]

/-- Summing all interior states gives the actual (m+1)-transition endpoint mass. -/
theorem normalizer_eq_power (q : ℝ) (m : ℕ) (l r : Bool) :
    pathNormalizer q m l r = (Matrix.of (transition q)^(m+1)) l r := by
  have hall (m : ℕ) (l r : Bool) : pathNormalizer q m l r =
      ∑ w : Fin m → Bool, pathMass q m l w r := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))
    · simp [hw]
    · simp [hw, illegal_mass_zero q m l r w hw]
  rw [hall]
  induction m generalizing l with
  | zero => simp [pathMass, pow_one, Fintype.sum_unique]
  | succ m ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => Bool)),
      Fintype.sum_prod_type, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathMass, Fin.cons_zero, Fin.tail_cons]
    rw [← Finset.mul_sum, ih]
    rfl

/-- Exact endpoint transition probability, retaining the alternating finite-volume term. -/
theorem endpoint_power_formula (q : ℝ) (hq : 0 < q) (n : ℕ) (l r : Bool) :
    (Matrix.of (transition q)^n) l r =
      (if r then q/(1+q) else 1/(1+q)) + (-q)^n *
        ((if l = r then 1 else 0) - (if r then q/(1+q) else 1/(1+q))) := by
  have hq0 : 1+q ≠ 0 := ne_of_gt (by linarith)
  induction n generalizing l with
  | zero => cases l <;> cases r <;> simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [Fintype.sum_bool, Matrix.of_apply, transition]
    rw [ih, ih]
    cases l <;> cases r <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
      ite_true, ite_false, one_mul, zero_mul, add_zero, zero_add, pow_succ]
    all_goals field_simp
    all_goals ring

private theorem zero_interior_legal (m : ℕ) (hm : 1 ≤ m) (l r : Bool) :
    Adm (m+2) (Fin.cons l (Fin.snoc (fun _ : Fin m => false) r)) := by
  apply (adm_iff_no_adjacent_true _ _).mpr
  intro i j hij
  by_cases hi : i.val = 0
  · right
    have hj : j = (⟨0, by omega⟩ : Fin m).castSucc.succ := Fin.ext (by simp; omega)
    rw [hj]
    simp only [Fin.cons_succ, Fin.snoc_castSucc]
  · left
    have hi' : i = (⟨i.val-1, by omega⟩ : Fin m).castSucc.succ :=
      Fin.ext (by simp; omega)
    rw [hi']
    simp only [Fin.cons_succ, Fin.snoc_castSucc]

/-- Every exterior pair has a strictly positive event once there is an interior site. -/
theorem normalizer_pos (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) : 0 < pathNormalizer q m l r := by
  have hall : pathNormalizer q m l r = ∑ w : Fin m → Bool, pathMass q m l w r := by
    unfold pathNormalizer
    apply Finset.sum_congr rfl
    intro w _
    split_ifs with hw
    · rfl
    · exact (illegal_mass_zero q m l r w hw).symm
  rw [hall]
  apply Finset.sum_pos'
  · intro w _
    exact mass_nonneg q hq.le hq1.le m l r w
  · exact ⟨fun _ => false, Finset.mem_univ _,
      (path_weight_formula q hq hq1 m hm l r _ (zero_interior_legal m hm l r)).2⟩

/-- Real masses of the endpoint-conditioned experiment; conditioning requires positivity. -/
def conditionalLaw (q : ℝ) (m : ℕ) (l r : Bool) (w : Fin m → Bool) : ℝ :=
  pathMass q m l w r / pathNormalizer q m l r

/-- The normalized law retains precisely the padded legal support. -/
theorem conditional_normalization (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) :
    (∑ w, conditionalLaw q m l r w) = 1 ∧
    (∀ w, 0 ≤ conditionalLaw q m l r w) ∧
    (∀ w, 0 < conditionalLaw q m l r w ↔
      Adm (m+2) (Fin.cons l (Fin.snoc w r))) := by
  have hb := normalizer_pos q hq hq1 m hm l r
  refine ⟨?_, ?_, ?_⟩
  · unfold conditionalLaw
    rw [← Finset.sum_div]
    have he : (∑ w : Fin m → Bool, pathMass q m l w r) = pathNormalizer q m l r := by
      unfold pathNormalizer
      apply Finset.sum_congr rfl
      intro w _
      split_ifs with hw
      · rfl
      · exact illegal_mass_zero q m l r w hw
    rw [he, div_self hb.ne']
  · intro w
    exact div_nonneg (mass_nonneg q hq.le hq1.le m l r w) hb.le
  · intro w
    constructor
    · intro hw
      by_contra ha
      simp [conditionalLaw, illegal_mass_zero q m l r w ha] at hw
    · intro hw
      exact div_pos (path_weight_formula q hq hq1 m hm l r w hw).2 hb

/-- Interior occupation count. -/
def count {m : ℕ} (w : Fin m → Bool) : ℕ := ∑ i, (w i).toNat

/-- Finite activity weights at the exponential activity coordinate. -/
def tiltedWeight (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) (w : Fin m → Bool) : ℝ :=
  if Adm (m+2) (Fin.cons l (Fin.snoc w r)) then
    (q / (1-q)^2)^count w * Real.exp (t * count w) else 0

def partition (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) : ℝ :=
  ∑ w, tiltedWeight q m l r t w

def tiltedLaw (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) (w : Fin m → Bool) : ℝ :=
  tiltedWeight q m l r t w / partition q m l r t

def countMean (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) : ℝ :=
  ∑ w, tiltedLaw q m l r t w * count w

def countVariance (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) : ℝ :=
  ∑ w, tiltedLaw q m l r t w * (count w - countMean q m l r t)^2

private theorem partition_pos (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) : 0 < partition q m l r t := by
  apply Finset.sum_pos'
  · intro w _
    unfold tiltedWeight
    split_ifs
    · exact (mul_pos (pow_pos (div_pos hq (sq_pos_of_pos (sub_pos.mpr hq1))) _)
        (Real.exp_pos _)).le
    · rfl
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp [tiltedWeight, zero_interior_legal m hm l r, count, Real.exp_pos]

private theorem weight_deriv (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ)
    (w : Fin m → Bool) : HasDerivAt (fun s => tiltedWeight q m l r s w)
      (tiltedWeight q m l r t w * count w) t := by
  by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))
  · simpa [tiltedWeight, hw, mul_assoc] using
      (((hasDerivAt_id t).mul_const (count w : ℝ)).exp.const_mul
        ((q / (1-q)^2)^count w))
  · simpa [tiltedWeight, hw] using hasDerivAt_const t (0 : ℝ)

private theorem partition_deriv (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) :
    HasDerivAt (partition q m l r)
      (∑ w, tiltedWeight q m l r t w * count w) t := by
  exact HasDerivAt.fun_sum (fun w _ => weight_deriv q m l r t w)

/-- Differentiating the finite normalizer centers the actual count score. -/
theorem tilted_law_deriv (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) (w : Fin m → Bool) :
    HasDerivAt (fun s => tiltedLaw q m l r s w)
      (tiltedLaw q m l r t w * (count w - countMean q m l r t)) t := by
  have hz := (partition_pos q hq hq1 m hm l r t).ne'
  have hd := (weight_deriv q m l r t w).div (partition_deriv q m l r t) hz
  convert hd using 1
  · rfl
  · simp only [tiltedLaw, countMean, div_mul_eq_mul_div, ← Finset.sum_div]
    field_simp
    <;> ring

/-- Positive legal words have logarithmic score K minus its conditional mean. -/
theorem count_score (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) (w : Fin m → Bool)
    (hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))) :
    HasDerivAt (fun s => Real.log (tiltedLaw q m l r s w))
      (count w - countMean q m l r t) t := by
  have hwpos : 0 < tiltedLaw q m l r t w := by
    apply div_pos _ (partition_pos q hq hq1 m hm l r t)
    simp only [tiltedWeight, hw, ite_true]
    exact mul_pos (pow_pos (div_pos hq (sq_pos_of_pos (sub_pos.mpr hq1))) _)
      (Real.exp_pos _)
  simpa [hwpos.ne'] using (tilted_law_deriv q hq hq1 m hm l r t w).log hwpos.ne'

/-- Classical Fisher of this observed finite law, including its zero-mass words. -/
def conditionalFisher (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) : ℝ :=
  ∑ w, tiltedLaw q m l r t w *
    (deriv (fun s => Real.log (tiltedLaw q m l r s w)) t)^2

/-- The actual activity experiment has count variance as its Fisher information. -/
theorem fisher_eq_count_variance (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    conditionalFisher q m l r t = countVariance q m l r t := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))
  · rw [(count_score q hq hq1 m hm l r t w hw).deriv]
  · simp [tiltedLaw, tiltedWeight, hw]

open D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive

/-- The arrival-bit reward in the actual source Markov chain. -/
def arrival (_ : Bool) (j : Bool) : ℝ := if j then 1 else 0

private theorem source_stochastic (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    Matrix.of (transition q) ∈ Matrix.rowStochastic ℝ Bool := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  constructor
  · intro i j
    cases i <;> cases j <;> simp [transition, hq.le, sub_nonneg.mpr hq1.le]
  · intro i
    cases i <;> simp [transition, Fintype.sum_bool]

private theorem source_irreducible (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (Matrix.of (transition q)).IsIrreducible := by
  refine ⟨fun i j => (source_stochastic q hq hq1).1 i j, ?_⟩
  letI : Quiver Bool := Matrix.toQuiver (Matrix.of (transition q))
  have hc : Quiver.IsStronglyConnected Bool := by
    intro i j
    cases i <;> cases j
    · exact ⟨Quiver.Path.nil⟩
    · exact ⟨Quiver.Path.nil.cons (⟨hq⟩ : false ⟶ true)⟩
    · exact ⟨Quiver.Path.nil.cons (⟨zero_lt_one⟩ : true ⟶ false)⟩
    · exact ⟨Quiver.Path.nil⟩
  exact hc.isSStronglyConnected_of_hom (i₀ := false) (j₀ := false)
    ⟨sub_pos.mpr hq1⟩

/-- The source parameter selected by the actual Perron radius, not an assumed change of coordinates. -/
def tiltParameter (q t : ℝ) : ℝ :=
  1 - (1-q) / eigenvalue (Matrix.of (transition q)) arrival t

/-- Actual global Doob normalization determines the source amplitude and its activity. -/
theorem global_doob_parameter (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) (t : ℝ) :
    0 < tiltParameter q t ∧ tiltParameter q t < 1 ∧
    π.globalDoob hI arrival t = Matrix.of (transition (tiltParameter q t)) ∧
    tiltParameter q t / (1-tiltParameter q t)^2 = Real.exp t * (q / (1-q)^2) := by
  let a := eigenvalue (Matrix.of (transition q)) arrival t
  let x := π.perronVector hI arrival t
  have ha : 0 < a := eigenvalue_pos _ hI arrival t
  obtain ⟨hx, _, he⟩ := π.perronVector_spec hI arrival t
  have he0 := congrFun he false
  have he1 := congrFun he true
  change (∑ j, tilt (Matrix.of (transition q)) arrival t false j * x j) = a * x false at he0
  change (∑ j, tilt (Matrix.of (transition q)) arrival t true j * x j) = a * x true at he1
  simp [Fintype.sum_bool, tilt, Matrix.of_apply, transition, arrival] at he0 he1
  have hpoly : a^2 - (1-q)*a = q * Real.exp t := by
    have h := he0
    rw [he1] at h
    have hn := hx true
    change 0 < x true at hn
    nlinarith
  have hag : 1-q < a := by
    have hp := mul_pos hq (Real.exp_pos t)
    nlinarith
  have hp0 : 0 < tiltParameter q t := by
    change 0 < 1-(1-q)/a
    exact sub_pos.mpr ((div_lt_one ha).mpr hag)
  have hp1 : tiltParameter q t < 1 := by
    change 1-(1-q)/a < 1
    linarith [div_pos (sub_pos.mpr hq1) ha]
  refine ⟨hp0, hp1, ?_, ?_⟩
  · ext i j
    have hx0 : x false ≠ 0 := (hx false).ne'
    have hx1 : x true ≠ 0 := (hx true).ne'
    change tilt (Matrix.of (transition q)) arrival t i j * x j / (a*x i) =
      transition (tiltParameter q t) i j
    cases i <;> cases j <;>
      simp only [tilt, Matrix.of_apply, transition, arrival, Bool.false_eq_true,
        ite_false, ite_true, mul_zero, Real.exp_zero, mul_one, zero_mul, zero_div]
    · simp only [tiltParameter]
      change (1-q)*x false/(a*x false) = 1-(1-(1-q)/a)
      field_simp
      <;> ring
    · change q*Real.exp t*x true/(a*x false) = 1-(1-q)/a
      rw [he1]
      field_simp
      nlinarith
    · rw [he1]
      field_simp
  · change (1-(1-q)/a)/(1-(1-(1-q)/a))^2 = Real.exp t*(q/(1-q)^2)
    rw [show 1-(1-(1-q)/a) = (1-q)/a by ring]
    field_simp [ha.ne', (sub_pos.mpr hq1).ne']
    nlinarith

/-- The conditional source family is exactly the exponential count family at every tilt. -/
theorem conditional_tilt (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) (w : Fin m → Bool) :
    conditionalLaw (tiltParameter q t) m l r w = tiltedLaw q m l r t w := by
  obtain ⟨hp, hp1, _, hz⟩ := global_doob_parameter q hq hq1 π hI t
  have he (v : Fin m → Bool) :
      (tiltParameter q t / (1-tiltParameter q t)^2)^count v =
      (q/(1-q)^2)^count v * Real.exp (t * count v) := by
    rw [hz, mul_pow, ← Real.exp_nat_mul]
    ring_nf
  have hpz : activityPartition (tiltParameter q t) m l r = partition q m l r t := by
    unfold activityPartition partition tiltedWeight
    apply Finset.sum_congr rfl
    intro v _
    split_ifs
    · exact he v
    · rfl
  by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))
  · rw [conditionalLaw, normalized_path _ hp hp1 m hm l r w hw]
    rw [show (∑ i, (w i).toNat) = count w from rfl, he, hpz]
    simp [tiltedLaw, tiltedWeight, hw]
  · simp [conditionalLaw, illegal_mass_zero _ m l r w hw, tiltedLaw, tiltedWeight, hw]

private theorem tilted_total (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    (∑ w, tiltedLaw q m l r t w) = 1 := by
  unfold tiltedLaw
  rw [← Finset.sum_div]
  exact div_self (partition_pos q hq hq1 m hm l r t).ne'

/-- The derivative of the conditional mean is the count variance. -/
theorem count_mean_deriv (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    HasDerivAt (countMean q m l r) (countVariance q m l r t) t := by
  have hd := HasDerivAt.fun_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Bool))) =>
    (tilted_law_deriv q hq hq1 m hm l r t w).mul_const (count w : ℝ))
  convert hd using 1
  · rfl
  · let E := countMean q m l r t
    let μ := tiltedLaw q m l r t
    have ht : (∑ w, μ w) = 1 := tilted_total q hq hq1 m hm l r t
    have he : countVariance q m l r t =
        (∑ w, μ w * (count w : ℝ)^2) - E^2 := by
      calc
        _ = ∑ w, (μ w * (count w : ℝ)^2 -
            (2*E)*(μ w * count w) + E^2 * μ w) := by
          apply Finset.sum_congr rfl
          intro w _
          dsimp [μ, E, countVariance]
          ring
        _ = (∑ w, μ w * (count w : ℝ)^2) -
            (2*E) * (∑ w, μ w * count w) + E^2*(∑ w, μ w) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        _ = _ := by rw [ht]; change _ - 2*E*E + E^2*1 = _; ring
    rw [he]
    change (∑ w, μ w * (count w : ℝ)^2) - E^2 =
      ∑ w, μ w * (count w - E) * count w
    calc
      _ = (∑ w, μ w * (count w : ℝ)^2) - E*(∑ w, μ w * count w) := by
        change _ - E^2 = _ - E*E
        ring
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro w _
        ring

/-- The first logarithmic partition derivative is the mean. -/
theorem log_partition_deriv (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    HasDerivAt (fun s => Real.log (partition q m l r s)) (countMean q m l r t) t := by
  convert (partition_deriv q m l r t).log
    (partition_pos q hq hq1 m hm l r t).ne' using 1
  simp only [countMean, tiltedLaw, div_mul_eq_mul_div, ← Finset.sum_div]

open D5.S3.Quantum.Entanglement

/-- Actual squared circuit coefficients, their endpoint event and its conditional count law. -/
theorem actual_conditional_experiment (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (φ : ℕ → ℝ)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    ∃ U : ℕ → SequentialRegisterCircuit.Unitary (Bool × Bool),
      let b := fun w : Fin m → Bool =>
        ‖SequentialRegisterCircuit.circuit U (m+1) 0
          (SequentialRegisterCircuit.blankState false (m+1) l)
          (PhaseHistoryBound.register (m+1)
            (Born.sourcePath (m+1) l (Fin.snoc w r)))‖^2
      (∑ w, b w) = ((Matrix.of (transition (tiltParameter q t)))^(m+1)) l r ∧
      (∑ w, b w) = (if r then tiltParameter q t/(1+tiltParameter q t)
        else 1/(1+tiltParameter q t)) + (-tiltParameter q t)^(m+1) *
        ((if l = r then 1 else 0) - (if r then tiltParameter q t/(1+tiltParameter q t)
          else 1/(1+tiltParameter q t))) ∧
      0 < ∑ w, b w ∧
      ((∑ w, tiltedLaw q m l r t w) = 1 ∧
        (∀ w, 0 ≤ tiltedLaw q m l r t w) ∧
        (∀ w, 0 < tiltedLaw q m l r t w ↔ Adm (m+2) (Fin.cons l (Fin.snoc w r)))) ∧
      (∀ w, b w / (∑ v, b v) = tiltedLaw q m l r t w) ∧
      (∀ w, ¬ Adm (m+2) (Fin.cons l (Fin.snoc w r)) → b w = 0) := by
  let hI := source_irreducible q hq hq1
  let π := stationary (Matrix.of (transition q)) (source_stochastic q hq hq1) hI
  obtain ⟨hp, hp1, hQ, _⟩ := global_doob_parameter q hq hq1 π hI t
  have hP : Matrix.of (transition (tiltParameter q t)) ∈ Matrix.rowStochastic ℝ Bool := by
    rw [← hQ]
    exact (π.globalDoob_stochastic hI arrival t).1
  let ρ := stationary (Matrix.of (transition (tiltParameter q t))) hP
    (by simpa [hQ] using π.globalDoob_irreducible hI arrival t)
  obtain ⟨U, _, _, hU⟩ := Born.actual_circuit_path_laws
    (tiltParameter q t) hp hp1 φ ρ hP
  refine ⟨U, ?_⟩
  dsimp only
  simp_rw [hU]
  have hs : (∑ w : Fin m → Bool, pathMass (tiltParameter q t) m l w r) =
      pathNormalizer (tiltParameter q t) m l r := by
    unfold pathNormalizer
    apply Finset.sum_congr rfl
    intro w _
    split_ifs with hw
    · rfl
    · exact illegal_mass_zero _ m l r w hw
  rw [hs]
  have hn := conditional_normalization _ hp hp1 m hm l r
  simp_rw [conditional_tilt q hq hq1 π hI m hm l r t] at hn
  refine ⟨normalizer_eq_power _ m l r, ?_, normalizer_pos _ hp hp1 m hm l r, hn,
    fun w => conditional_tilt q hq hq1 π hI m hm l r t w,
    fun w hw => illegal_mass_zero _ m l r w hw⟩
  rw [normalizer_eq_power]
  exact endpoint_power_formula _ hp (m+1) l r

private theorem log_partition_boundary (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    Real.log (pathNormalizer (tiltParameter q t) m l r) =
      Real.log (partition q m l r t) -
        ((m+1 : ℝ) + r.toNat - l.toNat) *
          pressure (Matrix.of (transition q)) arrival t + t*r.toNat +
        Real.log (q^r.toNat * (1-q)^(m+1-l.toNat-r.toNat)) := by
  obtain ⟨hp, hp1, _, hz⟩ := global_doob_parameter q hq hq1 π hI t
  let a := eigenvalue (Matrix.of (transition q)) arrival t
  have ha : 0 < a := eigenvalue_pos _ hI arrival t
  have hqt : 1-tiltParameter q t = (1-q)/a := by dsimp [tiltParameter, a]; ring
  have hlog0 : Real.log (1-tiltParameter q t) = Real.log (1-q) - Real.log a := by
    rw [hqt, Real.log_div (sub_pos.mpr hq1).ne' ha.ne']
  have hlog1 : Real.log (tiltParameter q t) =
      Real.log q + t - 2*Real.log a := by
    have hh := congrArg Real.log hz
    rw [Real.log_div hp.ne' (pow_ne_zero 2 (sub_pos.mpr hp1).ne'),
      Real.log_mul (Real.exp_ne_zero t)
        (div_ne_zero hq.ne' (pow_ne_zero 2 (sub_pos.mpr hq1).ne')),
      Real.log_exp, Real.log_div hq.ne' (pow_ne_zero 2 (sub_pos.mpr hq1).ne'),
      Real.log_pow, Real.log_pow, hlog0] at hh
    norm_num at hh
    linarith
  have hpz : activityPartition (tiltParameter q t) m l r = partition q m l r t := by
    unfold activityPartition partition tiltedWeight
    apply Finset.sum_congr rfl
    intro w _
    split_ifs
    · change (tiltParameter q t / (1-tiltParameter q t)^2)^count w = _
      rw [hz, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    · rfl
  rw [normalizer_factor _ hp hp1 m hm l r, hpz,
    Real.log_mul (mul_ne_zero (pow_ne_zero _ hp.ne')
      (pow_ne_zero _ (sub_pos.mpr hp1).ne')) (partition_pos q hq hq1 m hm l r t).ne',
    Real.log_mul (pow_ne_zero _ hp.ne') (pow_ne_zero _ (sub_pos.mpr hp1).ne'),
    Real.log_mul (pow_ne_zero _ hq.ne') (pow_ne_zero _ (sub_pos.mpr hq1).ne')]
  simp only [Real.log_pow, hlog0, hlog1, pressure]
  change _ = _ - _ * Real.log a + _ + _
  have he : ((m+1-l.toNat-r.toNat : ℕ) : ℝ) =
      (m+1 : ℝ) - l.toNat-r.toNat := by
    rw [Nat.cast_sub (by cases l <;> cases r <;> simp <;> omega),
      Nat.cast_sub (by cases l <;> simp <;> omega)]
    push_cast
    ring
  rw [he]
  ring

/-- Exact finite boundary correction for the conditional Fisher experiment. -/
theorem conditional_fisher_boundary (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    conditionalFisher q m l r t =
      ((m+1 : ℝ) + r.toNat-l.toNat) *
        deriv (deriv (pressure (Matrix.of (transition q)) arrival)) t +
      deriv (deriv (fun s => Real.log (pathNormalizer (tiltParameter q s) m l r))) t := by
  let p := pressure (Matrix.of (transition q)) arrival
  let c : ℝ := (m+1 : ℝ) + r.toNat-l.toNat
  let C := q^r.toNat * (1-q)^(m+1-l.toNat-r.toNat)
  let B := fun s => Real.log (pathNormalizer (tiltParameter q s) m l r)
  have hc : ContDiff ℝ 2 p := π.pressure_contDiff hI arrival
  have hd (s : ℝ) : HasDerivAt B
      (countMean q m l r s - c*deriv p s + r.toNat) s := by
    have hh := (((log_partition_deriv q hq hq1 m hm l r s).sub
      ((hc.differentiable (by norm_num) s).hasDerivAt.const_mul c)).add
        ((hasDerivAt_id s).mul_const (r.toNat : ℝ))).add_const (Real.log C)
    have he : B = (fun z => Real.log (partition q m l r z) - c*p z +
        z*r.toNat + Real.log C) := funext (log_partition_boundary q hq hq1 π hI m hm l r)
    rw [he]
    simpa using hh
  have he : deriv B = fun s => countMean q m l r s - c*deriv p s + r.toNat :=
    funext fun s => (hd s).deriv
  have hh := ((count_mean_deriv q hq hq1 m hm l r t).sub
    ((hc.differentiable_deriv_two t).hasDerivAt.const_mul c)).add_const (r.toNat : ℝ)
  have hdd : deriv (deriv B) t = countVariance q m l r t - c*deriv (deriv p) t := by
    rw [he]
    exact hh.deriv
  rw [fisher_eq_count_variance q hq hq1 m hm l r t]
  change _ = c*deriv (deriv p) t + deriv (deriv B) t
  rw [hdd]
  ring

/-- The stationary endpoint mass, separated from the alternating correction. -/
def endpointStationary (x : ℝ) (r : Bool) : ℝ :=
  if r then x / (1+x) else 1 / (1+x)
/-- Exact logarithmic alternating remainder, with the original exterior bits fixed. -/
def endpointLogRemainder (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) : ℝ :=
  Real.log (1 - (-tiltParameter q t)^(m+2-l.toNat-r.toNat))
private theorem tilt_parameter_contDiff (q : ℝ)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) :
    ContDiff ℝ 2 (tiltParameter q) := by
  have he : (fun t => Real.exp (pressure (Matrix.of (transition q)) arrival t)) =
      eigenvalue (Matrix.of (transition q)) arrival := by
    funext t
    exact Real.exp_log (eigenvalue_pos _ hI arrival t)
  have hc := (π.pressure_contDiff hI arrival).exp
  rw [he] at hc
  exact contDiff_const.sub (contDiff_const.div hc (fun t => (eigenvalue_pos _ hI arrival t).ne'))
private theorem endpoint_factor (x : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m)
    (l r : Bool) :
    pathNormalizer x m l r = endpointStationary x r *
      (1 - (-x)^(m+2-l.toNat-r.toNat)) := by
  rw [normalizer_eq_power, endpoint_power_formula x hx]
  cases l <;> cases r <;> simp only [endpointStationary, Bool.toNat_false,
    Bool.toNat_true, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
    Nat.sub_zero, Nat.add_sub_cancel]
  · rw [show m+2 = (m+1)+1 by omega, pow_succ]
    field_simp; ring
  · rw [show m+2-1 = m+1 by omega]
    field_simp; ring
  · rw [show m+2-1 = m+1 by omega]
    field_simp; ring
  · rw [show m+2-1-1 = m by omega, pow_succ]
    field_simp; ring
private theorem power_deriv (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (k : ℕ) (t : ℝ) (hft : f t ≠ 0) :
    HasDerivAt (fun s => f s^k) ((k : ℝ) * f t^k * (deriv f t / f t)) t := by
  have hh := (hf t).hasDerivAt.pow k
  convert hh using 1
  cases k with
  | zero => simp
  | succ k =>
    dsimp
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
private theorem alternating_log_second (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfn : ∀ t, f t ≠ 0) (hfp : ∀ t, |f t| < 1) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    deriv (deriv (fun s => Real.log (1-f s^k))) t =
      -(k : ℝ) * f t^k *
          ((k : ℝ) * (deriv f t / f t)^2 +
            ((deriv (deriv f) t * f t - (deriv f t)^2) / (f t)^2)) / (1-f t^k) -
        ((k : ℝ) * f t^k * (deriv f t / f t))^2 / (1-f t^k)^2 := by
  let A := fun s => deriv f s / f s
  have hpow (s : ℝ) := power_deriv f (hf.differentiable (by norm_num)) k s (hfn s)
  have hden (s : ℝ) : 1-f s^k ≠ 0 := by
    have hh : |f s^k| < 1 := by
      rw [abs_pow]
      exact pow_lt_one₀ (abs_nonneg _) (hfp s) (by omega)
    linarith [le_abs_self (f s^k)]
  have hlog (s : ℝ) : HasDerivAt (fun z => Real.log (1-f z^k))
      (-(k : ℝ) * f s^k * A s / (1-f s^k)) s := by
    convert ((hpow s).const_sub 1).log (hden s) using 1 <;> dsimp [A] <;> ring
  have heq : deriv (fun s => Real.log (1-f s^k)) =
      fun s => -(k : ℝ) * f s^k * A s / (1-f s^k) := funext fun s => (hlog s).deriv
  have hA : HasDerivAt A
      ((deriv (deriv f) t * f t - (deriv f t)^2) / (f t)^2) t := by
    convert ((hf.differentiable_deriv_two t).hasDerivAt.div
      (hf.differentiable (by norm_num) t).hasDerivAt (hfn t)) using 1 <;> ring
  have hh := (((hpow t).mul hA).const_mul (-(k : ℝ))).div
    ((hpow t).const_sub 1) (hden t)
  have hh' := hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s =>
    show -(k : ℝ) * f s^k * A s / (1-f s^k) = _ by dsimp; ring))
  rw [heq]
  convert hh'.deriv using 1 <;> dsimp [A] <;> field_simp <;> ring
private def alternatingBound (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  let a := deriv f t / f t
  let b := (deriv (deriv f) t * f t - (deriv f t)^2) / (f t)^2
  (a^2 + |b|) / (1-|f t|) + a^2 / (1-|f t|)^2
private theorem alternating_log_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfn : ∀ t, f t ≠ 0) (hfp : ∀ t, |f t| < 1) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    |deriv (deriv (fun s => Real.log (1-f s^k))) t| ≤
      (k : ℝ)^2 * |f t|^k * alternatingBound f t := by
  let a := deriv f t / f t
  let b := (deriv (deriv f) t * f t - (deriv f t)^2) / (f t)^2
  let z := |f t|^k
  let d := 1-|f t|
  have hd : 0 < d := sub_pos.mpr (hfp t)
  have hz0 : 0 ≤ z := pow_nonneg (abs_nonneg _) _
  have hz1 : z ≤ 1 := pow_le_one₀ (abs_nonneg _) (hfp t).le
  have hz : z ≤ |f t| := pow_le_of_le_one (abs_nonneg _) (hfp t).le (by omega)
  have hden : d ≤ 1-f t^k := by
    have hh : f t^k ≤ z := le_abs_self (f t^k) |>.trans_eq (abs_pow _ _)
    dsimp [d]; linarith
  have hdenpos : 0 < 1-f t^k := lt_of_lt_of_le hd hden
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [alternating_log_second f hf hfn hfp k hk t]
  change |-(k : ℝ) * f t^k * ((k : ℝ)*a^2+b) / (1-f t^k) -
    ((k : ℝ) * f t^k * a)^2 / (1-f t^k)^2| ≤ _
  calc
    _ ≤ |-(k : ℝ) * f t^k * ((k : ℝ)*a^2+b) / (1-f t^k)| +
        |((k : ℝ) * f t^k * a)^2 / (1-f t^k)^2| := abs_sub _ _
    _ = (k : ℝ) * z * |(k : ℝ)*a^2+b| / (1-f t^k) +
        (k : ℝ)^2 * z^2 * a^2 / (1-f t^k)^2 := by
      simp only [abs_div, abs_mul, abs_neg, abs_pow, abs_of_nonneg hk0,
        abs_of_pos hdenpos, sq_abs, z, mul_pow]
    _ ≤ (k : ℝ) * z * ((k : ℝ)*a^2+|b|) / d +
        (k : ℝ)^2 * z * a^2 / d^2 := by
      gcongr
      · calc
          _ ≤ |(k : ℝ)*a^2| + |b| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg (mul_nonneg hk0 (sq_nonneg _))]
      · exact sq_le hz0 hz1
    _ ≤ (k : ℝ)^2 * z * (a^2+|b|) / d +
        (k : ℝ)^2 * z * a^2 / d^2 := by
      have hi : (k : ℝ) * a^2 + |b| ≤ (k : ℝ) * (a^2 + |b|) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (abs_nonneg b)]
      have hfirst : (k : ℝ) * z * ((k : ℝ)*a^2+|b|) / d ≤
          (k : ℝ)^2 * z * (a^2+|b|) / d := by
        apply (div_le_div_iff_of_pos_right hd).mpr
        convert mul_le_mul_of_nonneg_left hi (mul_nonneg hk0 hz0) using 1 <;> ring
      exact add_le_add hfirst (le_refl _)
    _ = _ := by dsimp [alternatingBound, a, b, d, z]; ring
/-- The boundary log splits into its stationary term and a parity-sensitive remainder. -/
theorem endpoint_log_decomposition (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    Real.log (pathNormalizer (tiltParameter q t) m l r) =
      Real.log (endpointStationary (tiltParameter q t) r) + endpointLogRemainder q m l r t := by
  obtain ⟨hp, hp1, _, _⟩ := global_doob_parameter q hq hq1 π hI t
  have hS : 0 < endpointStationary (tiltParameter q t) r := by
    cases r <;> simp only [endpointStationary, ite_true, ite_false] <;> positivity
  have hk : m ≤ m+2-l.toNat-r.toNat := by cases l <;> cases r <;> simp <;> omega
  have hpow : |(-tiltParameter q t)^(m+2-l.toNat-r.toNat)| < 1 := by
    rw [abs_pow, abs_neg, abs_of_pos hp]
    exact pow_lt_one₀ hp.le hp1 (by omega)
  have hR : 0 < 1-(-tiltParameter q t)^(m+2-l.toNat-r.toNat) := by
    linarith [le_abs_self ((-tiltParameter q t)^(m+2-l.toNat-r.toNat))]
  rw [endpoint_factor _ hp m hm l r, Real.log_mul hS.ne' hR.ne']
  rfl
/-- An explicit differentiated alternating remainder bound at every actual real tilt. -/
theorem endpoint_remainder_second_bound (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) (t : ℝ) :
    let C := alternatingBound (fun s => -tiltParameter q s) t
    0 ≤ C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ l r : Bool,
      |deriv (deriv (endpointLogRemainder q m l r)) t| ≤
        C * (m+2 : ℝ)^2 * (tiltParameter q t)^m := by
  let f := fun s => -tiltParameter q s
  have hc : ContDiff ℝ 2 f := (tilt_parameter_contDiff q π hI).neg
  have hp (s : ℝ) := global_doob_parameter q hq hq1 π hI s
  have hn (s : ℝ) : f s ≠ 0 := neg_ne_zero.mpr (hp s).1.ne'
  have hf (s : ℝ) : |f s| < 1 := by simpa [f, abs_of_pos (hp s).1] using (hp s).2.1
  refine ⟨?_, ?_⟩
  · dsimp [alternatingBound]
    have hd : 0 < 1-|f t| := sub_pos.mpr (hf t)
    have hd0 : 0 ≤ 1-|f t| := hd.le
    positivity
  · intro m hm l r
    have hk : m ≤ m+2-l.toNat-r.toNat := by cases l <;> cases r <;> simp <;> omega
    have hk2 : m+2-l.toNat-r.toNat ≤ m+2 := by omega
    have hh := alternating_log_bound f hc hn hf (m+2-l.toNat-r.toNat) (by omega) t
    change |deriv (deriv (endpointLogRemainder q m l r)) t| ≤ _ at hh
    calc
      _ ≤ ((m+2-l.toNat-r.toNat : ℕ) : ℝ)^2 * |f t|^(m+2-l.toNat-r.toNat) *
          alternatingBound f t := hh
      _ ≤ (m+2 : ℝ)^2 * |f t|^m * alternatingBound f t := by
        have hecast : ((m+2-l.toNat-r.toNat : ℕ) : ℝ) ≤ (m+2 : ℝ) := by exact_mod_cast hk2
        have hsq : ((m+2-l.toNat-r.toNat : ℕ) : ℝ)^2 ≤ (m+2 : ℝ)^2 := by
          have hnon : (0 : ℝ) ≤ ((m+2-l.toNat-r.toNat : ℕ) : ℝ) := by positivity
          nlinarith [hecast, hnon]
        have hpowle : |f t|^(m+2-l.toNat-r.toNat) ≤ |f t|^m :=
          pow_le_pow_of_le_one (abs_nonneg _) (hf t).le hk
        have hbase : ((m+2-l.toNat-r.toNat : ℕ) : ℝ)^2 * |f t|^(m+2-l.toNat-r.toNat) ≤
            (m+2 : ℝ)^2 * |f t|^m := by
          calc
            _ ≤ (m+2 : ℝ)^2 * |f t|^(m+2-l.toNat-r.toNat) :=
              mul_le_mul_of_nonneg_right hsq (pow_nonneg (abs_nonneg _) _)
            _ ≤ _ := mul_le_mul_of_nonneg_left hpowle (sq_nonneg _)
        have hC : 0 ≤ alternatingBound f t := by
          have hd2 : 0 < (1-|f t|)^2 := sq_pos_of_pos (sub_pos.mpr (hf t))
          have hd1 : 0 ≤ 1-|f t| := (sub_pos.mpr (hf t)).le
          have hnum : 0 ≤ (deriv f t / f t)^2 +
              |(deriv (deriv f) t * f t - (deriv f t)^2) / (f t)^2| := by positivity
          dsimp [alternatingBound]
          exact add_nonneg (div_nonneg hnum hd1) (div_nonneg (sq_nonneg _) hd2.le)
        exact mul_le_mul_of_nonneg_right hbase hC
      _ = _ := by rw [show |f t| = tiltParameter q t by simp [f, abs_of_pos (hp t).1]]; ring
private theorem endpoint_terms_contDiff (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) :
    ContDiff ℝ 2 (fun s => Real.log (endpointStationary (tiltParameter q s) r)) ∧
    ContDiff ℝ 2 (endpointLogRemainder q m l r) := by
  have hc := tilt_parameter_contDiff q π hI
  have hp (s : ℝ) := global_doob_parameter q hq hq1 π hI s
  have hden (s : ℝ) : 1 + tiltParameter q s ≠ 0 := by linarith [hp s |>.1]
  have hstat : ContDiff ℝ 2 (fun s => endpointStationary (tiltParameter q s) r) := by
    cases r
    · simp only [endpointStationary, Bool.false_eq_true, ite_false]
      exact contDiff_const.div (contDiff_const.add hc) (fun s => hden s)
    · simp only [endpointStationary]
      exact hc.div (contDiff_const.add hc) (fun s => hden s)
  have hpow : ContDiff ℝ 2 (fun s => (-tiltParameter q s)^(m+2-l.toNat-r.toNat)) := by
    exact (hc.neg).pow _
  have hrem : ContDiff ℝ 2 (fun s => 1-(-tiltParameter q s)^(m+2-l.toNat-r.toNat)) :=
    contDiff_const.sub hpow
  have hremnz (s : ℝ) : 1-(-tiltParameter q s)^(m+2-l.toNat-r.toNat) ≠ 0 := by
    have hh := global_doob_parameter q hq hq1 π hI s
    have hlt : |(-tiltParameter q s)^(m+2-l.toNat-r.toNat)| < 1 := by
      rw [abs_pow, abs_neg, abs_of_pos hh.1]
      exact pow_lt_one₀ hh.1.le hh.2.1 (by cases l <;> cases r <;> simp_all <;> omega)
    linarith [le_abs_self ((-tiltParameter q s)^(m+2-l.toNat-r.toNat))]
  have hstatnz : ∀ s, endpointStationary (tiltParameter q s) r ≠ 0 := by
    intro s
    cases r
    · simp only [endpointStationary, Bool.false_eq_true, ite_false]
      exact (div_ne_zero one_ne_zero (hden s))
    · simp only [endpointStationary]
      exact div_ne_zero (hp s).1.ne' (hden s)
  exact ⟨hstat.log hstatnz, hrem.log hremnz⟩
/-- Exact Fisher decomposition with a stationary endpoint curvature and a decaying remainder. -/
theorem conditional_fisher_stationary_remainder (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (t : ℝ) :
    conditionalFisher q m l r t =
      ((m+1 : ℝ) + r.toNat-l.toNat) *
        deriv (deriv (pressure (Matrix.of (transition q)) arrival)) t +
      deriv (deriv (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t +
      deriv (deriv (endpointLogRemainder q m l r)) t := by
  rw [conditional_fisher_boundary q hq hq1 π hI m hm l r t]
  have heq : (fun s => Real.log (pathNormalizer (tiltParameter q s) m l r)) =
      (fun s => Real.log (endpointStationary (tiltParameter q s) r) +
        endpointLogRemainder q m l r s) := by
    funext s
    exact endpoint_log_decomposition q hq hq1 π hI m hm l r s
  have hc := endpoint_terms_contDiff q hq hq1 π hI m hm l r
  rw [heq]
  have hadd := iteratedDeriv_fun_add (n := 2) (x := t) hc.1.contDiffAt hc.2.contDiffAt
  have hh : deriv (deriv (fun s => Real.log (endpointStationary (tiltParameter q s) r) +
      endpointLogRemainder q m l r s)) t =
      deriv (deriv (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t +
      deriv (deriv (endpointLogRemainder q m l r)) t := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hadd
  rw [hh]
  ring
private theorem endpoint_second_tendsto (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) (l r : Bool) (t : ℝ) :
    Filter.Tendsto (fun m : ℕ => deriv (deriv (endpointLogRemainder q m l r)) t)
      Filter.atTop (nhds 0) := by
  let C := alternatingBound (fun s => -tiltParameter q s) t
  obtain ⟨hC, hb⟩ := endpoint_remainder_second_bound q hq hq1 π hI t
  have hp := global_doob_parameter q hq hq1 π hI t
  have hl : Filter.Tendsto (fun m : ℕ => C*9*((m : ℝ)^2*(tiltParameter q t)^m))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 2 hp.1.le hp.2.1).const_mul (C*9)
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpoly : (m+2 : ℝ)^2 ≤ 9*(m : ℝ)^2 := by nlinarith
  calc
    _ ≤ C*(m+2 : ℝ)^2*(tiltParameter q t)^m := hb m hm l r
    _ ≤ C*(9*(m : ℝ)^2)*(tiltParameter q t)^m := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC)
        (pow_nonneg hp.1.le _)
    _ = _ := by ring
/-- The limiting log normalizer and its curvature retain the stationary endpoint term. -/
theorem endpoint_boundary_limit (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) (l r : Bool) (t : ℝ) :
    Filter.Tendsto (fun m : ℕ => Real.log (pathNormalizer (tiltParameter q t) (m+1) l r))
      Filter.atTop (nhds (Real.log (endpointStationary (tiltParameter q t) r))) ∧
    Filter.Tendsto (fun m : ℕ => deriv (deriv
      (fun s => Real.log (pathNormalizer (tiltParameter q s) (m+1) l r))) t)
      Filter.atTop (nhds (deriv (deriv
        (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t)) := by
  have hp := global_doob_parameter q hq hq1 π hI t
  have hpow : Filter.Tendsto (fun m : ℕ =>
      (-tiltParameter q t)^((m+1)+2-l.toNat-r.toNat)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (Filter.Eventually.of_forall (fun m => ?_))
      (tendsto_pow_atTop_nhds_zero_of_lt_one hp.1.le hp.2.1)
    rw [Real.norm_eq_abs, abs_pow, abs_neg, abs_of_pos hp.1]
    apply pow_le_pow_of_le_one hp.1.le hp.2.1.le
    cases l <;> cases r <;> simp <;> omega
  have harg : Filter.Tendsto (fun m : ℕ =>
      1-(-tiltParameter q t)^((m+1)+2-l.toNat-r.toNat)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hpow
  have hlog := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp harg
  have hsecond := (endpoint_second_tendsto q hq hq1 π hI l r t).comp
    (Filter.tendsto_add_atTop_nat 1)
  constructor
  · have hh := hlog.const_add (Real.log (endpointStationary (tiltParameter q t) r))
    have hlim : Filter.Tendsto (fun m : ℕ =>
        Real.log (endpointStationary (tiltParameter q t) r) + endpointLogRemainder q (m+1) l r t)
        Filter.atTop (nhds (Real.log (endpointStationary (tiltParameter q t) r))) := by
      simpa [Function.comp_def, endpointLogRemainder] using hh
    apply hlim.congr'
    exact Filter.Eventually.of_forall fun m =>
      (endpoint_log_decomposition q hq hq1 π hI (m+1) (by omega) l r t).symm
  · have hh := hsecond.const_add (deriv (deriv
      (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t)
    have he (m : ℕ) := conditional_fisher_stationary_remainder q hq hq1 π hI (m+1) (by omega) l r t
    have hb (m : ℕ) := conditional_fisher_boundary q hq hq1 π hI (m+1) (by omega) l r t
    apply (show Filter.Tendsto (fun m : ℕ => deriv (deriv
      (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t +
        deriv (deriv (endpointLogRemainder q (m+1) l r)) t) Filter.atTop
      (nhds (deriv (deriv (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t))
      by simpa [Function.comp_def] using hh).congr'
    exact Filter.Eventually.of_forall fun m => by linarith [he m, hb m]
/-- Conditional Fisher per transition converges to pressure curvature and the actual Poisson rate. -/
theorem conditional_fisher_rate_tendsto (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (π : Stationary (Matrix.of (transition q)))
    (hI : (Matrix.of (transition q)).IsIrreducible) (l r : Bool) (t : ℝ) :
    Filter.Tendsto
      (fun m : ℕ => conditionalFisher q (m+1) l r t / (m+2 : ℝ))
      Filter.atTop (nhds (deriv (deriv (pressure (Matrix.of (transition q)) arrival)) t)) ∧
    deriv (deriv (pressure (Matrix.of (transition q)) arrival)) t =
      (stationary (π.globalDoob hI arrival t) (π.globalDoob_stochastic hI arrival t).1
        (π.globalDoob_irreducible hI arrival t)).varianceRate
          (π.globalDoob_stochastic hI arrival t).1 (π.globalDoob_irreducible hI arrival t) arrival ∧
    (∀ m : ℕ, 1 ≤ m → conditionalFisher q m l r t / (m : ℝ) =
      ((m+1 : ℝ) / m) * (conditionalFisher q m l r t / (m+1 : ℝ))) := by
  refine ⟨?_, π.pressure_second_derivative hI arrival t, fun m hm => ?_⟩
  rotate_left
  · have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm1 : (m+1 : ℝ) ≠ 0 := by positivity
    field_simp
  let p2 := deriv (deriv (pressure (Matrix.of (transition q)) arrival)) t
  let s2 := deriv (deriv (fun s => Real.log (endpointStationary (tiltParameter q s) r))) t
  have hsplit (m : ℕ) (hm : 1 ≤ m) :=
    conditional_fisher_stationary_remainder q hq hq1 π hI (m+1) (by omega) l r t
  have hpref : Filter.Tendsto (fun m : ℕ =>
      (((m+2 : ℝ) + r.toNat-l.toNat) * p2) / (m+2 : ℝ))
      Filter.atTop (nhds p2) := by
    let d : ℝ := r.toNat-l.toNat
    have hconst : Filter.Tendsto (fun m : ℕ => d / (m+2 : ℝ))
        Filter.atTop (nhds 0) := by
      simpa [d, Function.comp_def, Nat.cast_add] using
        (tendsto_const_div_atTop_nhds_zero_nat d).comp (Filter.tendsto_add_atTop_nat 2)
    have hbase : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hsum := hbase.add hconst
    have hmul := hsum.mul_const p2
    convert hmul using 1
    · funext m
      dsimp [d]
      have hn : (m+2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · simp
  have hsrate : Filter.Tendsto (fun m : ℕ => s2 / (m+2 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (tendsto_const_div_atTop_nhds_zero_nat s2).comp (Filter.tendsto_add_atTop_nat 2)
  have hrrate : Filter.Tendsto (fun m : ℕ =>
      deriv (deriv (endpointLogRemainder q (m+1) l r)) t / (m+2 : ℝ))
      Filter.atTop (nhds 0) := by
    have hR := (endpoint_second_tendsto q hq hq1 π hI l r t).comp
      (Filter.tendsto_add_atTop_nat 1)
    have hInv : Filter.Tendsto (fun m : ℕ => 1/(m+2 : ℝ)) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def, Nat.cast_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (Filter.tendsto_add_atTop_nat 2)
    simpa [Function.comp_def, div_eq_mul_inv] using hR.mul hInv
  have hsum := (hpref.add hsrate).add hrrate
  apply (show Filter.Tendsto
    (fun m : ℕ => (((m+2 : ℝ) + r.toNat-l.toNat) * p2) / (m+2 : ℝ) +
      s2 / (m+2 : ℝ) + deriv (deriv (endpointLogRemainder q (m+1) l r)) t / (m+2 : ℝ))
      Filter.atTop (nhds p2) by simpa using hsum).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh := hsplit m hm
  show _ = conditionalFisher q (m+1) l r t / (m+2 : ℝ)
  symm
  show conditionalFisher q (m+1) l r t / (m+2 : ℝ) =
      (((m+2 : ℝ) + r.toNat-l.toNat) * p2) / (m+2 : ℝ) +
        s2 / (m+2 : ℝ) + deriv (deriv (endpointLogRemainder q (m+1) l r)) t /
          (m+2 : ℝ)
  rw [hh]; dsimp [p2, s2]; push_cast; ring
end D5.S3.Combinatorics.Graph.LegalWords.ConditionalBornFisher
