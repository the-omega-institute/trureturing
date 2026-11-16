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

/-- Number of admissible words in a count fiber. -/
def fiberCard (m : ℕ) (l r : Bool) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin m → Bool =>
    Adm (m+2) (Fin.cons l (Fin.snoc w r)) ∧ count w = k)).card

/-- Distribution of the count in the activity experiment. -/
def countLaw (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ w : Fin m → Bool, if count w = k then tiltedLaw q m l r t w else 0

/-- Uniform legal-count reconstruction, independent of q and t; empty fibers have zero mass. -/
def recovery (m : ℕ) (l r : Bool) (k : ℕ) (w : Fin m → Bool) : ℝ :=
  if Adm (m+2) (Fin.cons l (Fin.snoc w r)) ∧ count w = k then
    1 / (fiberCard m l r k : ℝ) else 0

private theorem count_law_formula (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) (k : ℕ) :
    countLaw q m l r t k = (fiberCard m l r k : ℝ) *
      ((q / (1-q)^2)^k * Real.exp (t*k) / partition q m l r t) := by
  classical
  unfold countLaw
  have he : (fun w : Fin m → Bool => if count w = k then tiltedLaw q m l r t w else 0) =
      (fun w => if Adm (m+2) (Fin.cons l (Fin.snoc w r)) ∧ count w = k then
        (q / (1-q)^2)^k * Real.exp (t*k) / partition q m l r t else 0) := by
    funext w
    by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r)) <;>
      by_cases hk : count w = k <;> simp [tiltedLaw, tiltedWeight, hw, hk]
  rw [he]
  simp [fiberCard, ← Finset.sum_filter]

/-- Uniform reconstruction recovers the complete word law on every occupied fiber. -/
theorem count_recovery (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ)
    (k : ℕ) (w : Fin m → Bool) :
    countLaw q m l r t k * recovery m l r k w =
      if count w = k then tiltedLaw q m l r t w else 0 := by
  classical
  by_cases hw : Adm (m+2) (Fin.cons l (Fin.snoc w r))
  · by_cases hk : count w = k
    · have hc : 0 < fiberCard m l r k := by
        apply Finset.card_pos.mpr
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hk⟩⟩
      have hn : (fiberCard m l r k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
      rw [count_law_formula]
      simp only [recovery, hw, hk, and_self, ite_true, tiltedLaw, tiltedWeight]
      field_simp
    · simp [recovery, hk]
  · simp [recovery, hw, tiltedLaw, tiltedWeight]

/-- Reconstruction is normalized on every nonempty fiber and restores the whole law. -/
theorem uniform_reconstruction (q : ℝ) (m : ℕ) (l r : Bool) (t : ℝ) :
    (∀ k, 0 < fiberCard m l r k → ∑ w, recovery m l r k w = 1) ∧
    (∀ w, ∑ k ∈ Finset.range (m+1), countLaw q m l r t k * recovery m l r k w =
      tiltedLaw q m l r t w) := by
  classical
  constructor
  · intro k hk
    have hn : (fiberCard m l r k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
    simp only [recovery, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    change (fiberCard m l r k : ℝ) * (1/(fiberCard m l r k : ℝ)) = 1
    exact mul_one_div_cancel hn
  · intro w
    simp_rw [count_recovery]
    have hb : count w < m+1 := by
      have hh : count w ≤ m := by
        calc
          count w ≤ ∑ _ : Fin m, 1 := Finset.sum_le_sum (fun i _ => by
            cases w i <;> simp)
          _ = m := by simp
      omega
    exact Finset.sum_eq_single (count w) (fun k _ hk => by simp [Ne.symm hk])
      (fun h => (h (Finset.mem_range.mpr hb)).elim) |>.trans (by simp)

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

end D5.S3.Combinatorics.Graph.LegalWords.ConditionalBornFisher
