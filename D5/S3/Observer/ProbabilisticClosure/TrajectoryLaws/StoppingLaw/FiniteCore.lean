/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete finite stopping law forces the exact comb, consecutive edges, and target separation. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace ReadTree

/-- In the opposite phase every spin configuration returns a0 at the prescribed depth. -/
def OppositeSection (T : ReadTree) (φ : Bool) (k : ℕ) : Prop :=
  ∀ S : Spins, (T.run (visible (!φ) S)).output = some (.a false) ∧
    (T.run (visible (!φ) S)).paid = k

/-- Every positive paid depth occurs with output a1 in the active phase. -/
def AllStoppingDepths (T : ReadTree) (φ : Bool) (k : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → ∃ S : Spins,
    (T.run (visible φ S)).output = some (.a true) ∧
      (T.run (visible φ S)).paid = i

/-- Neither the comb shape nor the addresses' parity is an input assumption. -/
private theorem sections_force_stopComb (k : ℕ) (T : ReadTree) (φ : Bool)
    (hh : T.height ≤ k) (hA : T.OppositeSection φ k)
    (hB : T.AllStoppingDepths φ k) :
    ∃ ts : List ℤ, ts.length = k ∧
      (∀ t ∈ ts, (t - φ.toInt) % 2 = 0) ∧ T = stopComb ts := by
  have houtput (t : ℤ) (b : Bool) (v : Execution) :
      (v.prepend t b).output = v.output := rfl
  induction k generalizing T with
  | zero =>
    have h0 := hA (fun _ => false)
    have he := leaf_of_paid_zero T _ h0.2
    refine ⟨[], rfl, by simp, ?_⟩
    simpa [stopComb, h0.1] using he
  | succ k ih =>
    cases T with
    | leaf a =>
      have hn := (hA (fun _ => false)).2
      simp [run, Execution.paid] at hn
    | read t z o =>
      obtain ⟨S, hs, hn⟩ := hB 1 (by omega) (by omega)
      have hzero := hA (fun _ => false)
      have hconst : visible (!φ) (fun _ => false) t = false := constant_visible _ _ _
      have hzout : (z.run (visible (!φ) (fun _ => false))).output = some (.a false) := by
        simpa only [run, hconst, Bool.false_eq_true, ↓reduceIte, houtput]
          using hzero.1
      have htrue : visible φ S t = true := by
        cases he : visible φ S t with
        | false =>
          have hz0 : (z.run (visible φ S)).paid = 0 := by
            simp only [run, he, Bool.false_eq_true, ↓reduceIte, Execution.paid_prepend] at hn
            omega
          have hzleaf := leaf_of_paid_zero z (visible φ S) hz0
          have hzlabel : (z.run (visible φ S)).output = some (.a true) := by
            simpa only [run, he, Bool.false_eq_true, ↓reduceIte, houtput] using hs
          rw [hzlabel] at hzleaf
          rw [hzleaf] at hzout
          simp [run] at hzout
        | true => rfl
      have ht : (t - φ.toInt) % 2 = 0 := by
        by_contra h
        simp [visible, h] at htrue
      have ho0 : (o.run (visible φ S)).paid = 0 := by
        simp only [run, htrue, ↓reduceIte, Execution.paid_prepend] at hn
        omega
      have holeaf := leaf_of_paid_zero o (visible φ S) ho0
      have holabel : (o.run (visible φ S)).output = some (.a true) := by
        simpa only [run, htrue, ↓reduceIte, houtput] using hs
      rw [holabel] at holeaf
      have hzheight : z.height ≤ k := by
        simp only [height] at hh
        have := le_max_left z.height o.height
        omega
      have hzA : z.OppositeSection φ k := by
        intro R
        have hr := hA R
        have hv := opposite_phase_visible φ R t ht
        simp only [run, hv, Bool.false_eq_true, ↓reduceIte,
          houtput, Execution.paid_prepend] at hr
        exact ⟨hr.1, by omega⟩
      have hzB : z.AllStoppingDepths φ k := by
        intro i hi hik
        obtain ⟨R, hrout, hrn⟩ := hB (i + 1) (by omega) (by omega)
        have hv : visible φ R t = false := by
          cases he : visible φ R t with
          | false => rfl
          | true =>
            simp [run, he, holeaf, Execution.paid, Execution.prepend] at hrn
            omega
        simp only [run, hv, Bool.false_eq_true, ↓reduceIte,
          houtput, Execution.paid_prepend] at hrout hrn
        exact ⟨R, hrout, by omega⟩
      obtain ⟨ts, hlen, hpar, heq⟩ := ih z hzheight hzA hzB
      refine ⟨t :: ts, by simp [hlen], ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ht
        · exact hpar a ha
      · rw [heq, holeaf]; rfl

/-- Active integer labels are exactly the lifted spin-edge indices, without an ordering restriction. -/
private theorem stopComb_edge_indices (k : ℕ) (T : ReadTree) (φ : Bool)
    (hh : T.height ≤ k) (hA : T.OppositeSection φ k)
    (hB : T.AllStoppingDepths φ k) :
    ∃ es : List ℤ, es.length = k ∧
      T = stopComb (es.map (fun e => 2 * e + φ.toInt)) := by
  obtain ⟨ts, hlen, hpar, heq⟩ := sections_force_stopComb k T φ hh hA hB
  refine ⟨ts.map (fun t => (t - φ.toInt) / 2), by simpa, ?_⟩
  rw [List.map_map]
  have hm : ts.map (fun t => 2 * ((t - φ.toInt) / 2) + φ.toInt) = ts := by
    calc
      _ = ts.map (fun t => t) := by
        apply List.map_congr_left
        intro t ht
        have := hpar t ht
        omega
      _ = ts := List.map_id' ts
  simpa only [Function.comp_def, hm] using heq

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace ReadTree

def ZeroReplies (ts : List ℤ) (r : ℕ) (x : ℤ → Bool) : Prop :=
  ∀ t ∈ ts.take r, x t = false

theorem stopComb_outcomes (ts : List ℤ) (x : ℤ → Bool) :
    ((stopComb ts).run x).output = some (.a false) ∧
      ((stopComb ts).run x).paid = ts.length ∨
    ((stopComb ts).run x).output = some (.a true) ∧
      1 ≤ ((stopComb ts).run x).paid ∧ ((stopComb ts).run x).paid ≤ ts.length := by
  have houtput (t : ℤ) (b : Bool) (v : Execution) :
      (v.prepend t b).output = v.output := rfl
  induction ts with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons t ts ih =>
    cases ht : x t with
    | true =>
      right
      simp [stopComb, run, ht, Execution.paid, Execution.prepend]
    | false =>
      rcases ih with h | h
      · left
        simpa only [stopComb, run, ht, Bool.false_eq_true, ↓reduceIte,
          houtput, Execution.paid_prepend, List.length_cons] using
          And.intro h.1 (congrArg (· + 1) h.2)
      · right
        simp only [stopComb, run, ht, Bool.false_eq_true, ↓reduceIte,
          houtput, Execution.paid_prepend, List.length_cons]
        exact ⟨h.1, by omega, by omega⟩

private theorem stopComb_not_a1_at_zero (ts : List ℤ) (x : ℤ → Bool) :
    ¬(((stopComb ts).run x).output = some (.a true) ∧ ((stopComb ts).run x).paid = 0) := by
  intro h
  rcases stopComb_outcomes ts x with ha | ha
  · have := ha.1.symm.trans h.1; cases this
  · omega

/-- A new one response is exactly the difference of successive zero-prefix events. -/
private theorem zero_prefix_difference (ts : List ℤ) (x : ℤ → Bool) (r : ℕ)
    (hr : r < ts.length) :
    (ZeroReplies ts r x ∧ ¬ZeroReplies ts (r + 1) x) ↔
      ((stopComb ts).run x).output = some (.a true) ∧
        ((stopComb ts).run x).paid = r + 1 := by
  have houtput (t : ℤ) (b : Bool) (v : Execution) :
      (v.prepend t b).output = v.output := rfl
  induction ts generalizing r with
  | nil => simp at hr
  | cons t ts ih =>
    cases r with
    | zero =>
      cases hx : x t with
      | true => simp [ZeroReplies, stopComb, run, hx, Execution.paid, Execution.prepend]
      | false =>
        have hn := stopComb_not_a1_at_zero ts x
        simp only [ZeroReplies, List.take_zero, List.take_succ_cons, List.forall_mem_cons,
          List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
          hx, not_true_eq_false, true_and, stopComb, run, Bool.false_eq_true, ↓reduceIte,
          houtput, Execution.paid_prepend] at *
        simpa using hn
    | succ r =>
      have hr' : r < ts.length := by simpa using hr
      cases hx : x t with
      | true =>
        simp [ZeroReplies, stopComb, run, hx, Execution.paid, Execution.prepend]
      | false =>
        simpa [ZeroReplies, stopComb, run, hx, Execution.paid_prepend,
          houtput, Nat.add_assoc] using ih r hr'

/-- The final zero prefix is the a0 return event, rather than strict survival. -/
theorem zero_prefix_final (ts : List ℤ) (x : ℤ → Bool) :
    ZeroReplies ts ts.length x ↔
      ((stopComb ts).run x).output = some (.a false) ∧
        ((stopComb ts).run x).paid = ts.length := by
  have houtput (t : ℤ) (b : Bool) (v : Execution) :
      (v.prepend t b).output = v.output := rfl
  induction ts with
  | nil => simp [ZeroReplies, stopComb, run, Execution.paid]
  | cons t ts ih =>
    cases hx : x t with
    | true => simp [ZeroReplies, stopComb, run, hx, houtput]
    | false =>
      simpa [ZeroReplies, stopComb, run, hx, houtput,
        Execution.paid_prepend] using ih

def edgeComb (es : List ℤ) (φ : Bool) : ReadTree :=
  stopComb (es.map (fun e => 2 * e + φ.toInt))

theorem edge_zero_prefix (es : List ℤ) (φ : Bool) (S : Spins) (r : ℕ) :
    ZeroReplies (es.map (fun e => 2 * e + φ.toInt)) r (visible φ S) ↔
      ∀ e ∈ (es.take r).toFinset, S e = S (e + 1) := by
  have hb (a b : Bool) : Bool.xor a b = false ↔ a = b := by
    cases a <;> cases b <;> decide
  simp [ZeroReplies, ← List.map_take, active_visible, hb]

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- The return indicator is retained explicitly and computed from the optional output. -/
structure Observation where
  endpoint : Hidden
  output : Option Hidden
  returned : Bool
  paid : ℕ
  deriving DecidableEq

def observation (j φ : Bool) (T : ReadTree) (S : Spins) : Observation :=
  let v := T.run (visible φ S)
  ⟨hidden φ S j.toInt, v.output, v.returned, v.paid⟩

/-- Explicit averaging of the two independent equally weighted source phases. -/
def fullMass (β : Bias) (V : Finset ℤ) (j : Bool) (T : ReadTree) (z : Observation) : ℝ :=
  (∑ φ : Bool, SpinWindow.prob β V {S | observation j φ T S = z}) / 2

/-- The complete stopping table; every unspecified tuple, including nonreturn, has zero mass. -/
def stoppingMass (β : Bias) (k : ℕ) (z : Observation) : ℝ :=
  if z.returned = true then
    match z.endpoint, z.output with
    | .b s, some (.a true) => if 1 ≤ z.paid ∧ z.paid ≤ k then β.π s * β.d z.paid / 2 else 0
    | .b s, some (.a false) => if z.paid = k then β.π s * β.T (k + 1) / 2 else 0
    | .a s, some (.a false) => if z.paid = k then β.π s / 2 else 0
    | _, _ => 0
  else 0

def HasStoppingLaw (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ) (T : ReadTree) : Prop :=
  ∀ z : Observation, fullMass β V j T z = stoppingMass β k z

namespace SpinWindow

private theorem split_spin (β : Bias) (V : Finset ℤ) (q : ℤ) (E : Set Spins) :
    prob β V E = prob β V ({S | S q = false} ∩ E) +
      prob β V ({S | S q = true} ∩ E) := by
  have he : E = ({S | S q = false} ∩ E) ∪ ({S | S q = true} ∩ E) := by
    ext S
    constructor
    · intro h; cases hs : S q <;> simp [hs, h]
    · intro h; exact h.elim (fun h => h.2) (fun h => h.2)
  have hd : Disjoint ({S : Spins | S q = false} ∩ E) ({S | S q = true} ∩ E) := by
    apply Set.disjoint_left.mpr
    intro S h0 h1
    have := h0.1.symm.trans h1.1
    cases this
  calc
    prob β V E = prob β V (({S | S q = false} ∩ E) ∪ ({S | S q = true} ∩ E)) :=
      congrArg (prob β V) he
    _ = _ := prob_union β V hd

theorem spin_prob (β : Bias) (V : Finset ℤ) (q : ℤ) (hq : q ∈ V) (s : Bool) :
    prob β V {S | S q = s} = β.π s := by
  have he : {S : Spins | S q = s} = constant {q} s := by ext S; simp [constant]
  rw [he, constant_prob β V {q} (by simpa) s]
  simp

end SpinWindow

namespace ReadTree

private theorem observation_a_iff (j φ s : Bool) (T : ReadTree) (S : Spins)
    (o : Option Hidden) (n : ℕ) :
    observation j φ T S = ⟨.a s, o, o.isSome, n⟩ ↔
      φ = j ∧ S (targetIndex j j) = s ∧
        (T.run (visible j S)).output = o ∧ (T.run (visible j S)).paid = n := by
  cases j <;> cases φ <;>
    simp [observation, hidden, Bool.toInt, targetClass, targetIndex,
      Observation.mk.injEq, Execution.returned] <;> aesop

private theorem observation_b_iff (j φ s : Bool) (T : ReadTree) (S : Spins)
    (o : Option Hidden) (n : ℕ) :
    observation j φ T S = ⟨.b s, o, o.isSome, n⟩ ↔
      φ = !j ∧ S j.toInt = s ∧
        (T.run (visible (!j) S)).output = o ∧ (T.run (visible (!j) S)).paid = n := by
  cases j <;> cases φ <;>
    simp [observation, hidden, Bool.toInt, targetClass, targetIndex,
      Observation.mk.injEq, Execution.returned] <;> aesop

/-- The indicator condition is retained in the complete observation. -/
theorem fullMass_a (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree)
    (o : Option Hidden) (n : ℕ) :
    fullMass β V j T ⟨.a s, o, o.isSome, n⟩ =
      SpinWindow.prob β V {S | S (targetIndex j j) = s ∧
        (T.run (visible j S)).output = o ∧ (T.run (visible j S)).paid = n} / 2 := by
  unfold fullMass
  simp_rw [observation_a_iff]
  cases j <;> simp [Fintype.sum_bool]

theorem fullMass_b (β : Bias) (V : Finset ℤ) (j s : Bool) (T : ReadTree)
    (o : Option Hidden) (n : ℕ) :
    fullMass β V j T ⟨.b s, o, o.isSome, n⟩ =
      SpinWindow.prob β V {S | S j.toInt = s ∧
        (T.run (visible (!j) S)).output = o ∧ (T.run (visible (!j) S)).paid = n} / 2 := by
  unfold fullMass
  simp_rw [observation_b_iff]
  cases j <;> simp [Fintype.sum_bool]

private theorem stopping_law_b_depth (β : Bias) (V : Finset ℤ) (j s : Bool) (k i : ℕ)
    (T : ReadTree) (hlaw : HasStoppingLaw β V j k T) (hi : 1 ≤ i) (hik : i ≤ k) :
    SpinWindow.prob β V {S | S j.toInt = s ∧
      (T.run (visible (!j) S)).output = some (.a true) ∧
        (T.run (visible (!j) S)).paid = i} = β.π s * β.d i := by
  have h := hlaw ⟨.b s, some (.a true), true, i⟩
  have hmass := fullMass_b β V j s T (some (.a true)) i
  simp only [Option.isSome_some] at hmass
  rw [hmass] at h
  simp only [stoppingMass, hi, hik, and_self, ↓reduceIte] at h
  linarith

private theorem stopping_law_sections (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
    (T : ReadTree) (hV : T.support ⊆ V) (hlaw : HasStoppingLaw β V j k T) :
    T.OppositeSection (!j) k ∧ T.AllStoppingDepths (!j) k := by
  have hA (s : Bool) : SpinWindow.prob β V {S | S (targetIndex j j) = s ∧
      (T.run (visible j S)).output = some (.a false) ∧
        (T.run (visible j S)).paid = k} = β.π s := by
    have h := hlaw ⟨.a s, some (.a false), true, k⟩
    have hmass := fullMass_a β V j s T (some (.a false)) k
    simp only [Option.isSome_some] at hmass
    rw [hmass] at h
    simp only [stoppingMass, ↓reduceIte] at h
    linarith
  have hAone : SpinWindow.prob β V {S |
      (T.run (visible j S)).output = some (.a false) ∧ (T.run (visible j S)).paid = k} = 1 := by
    rw [SpinWindow.split_spin β V (targetIndex j j)]
    change SpinWindow.prob β V {S | S (targetIndex j j) = false ∧ _} +
      SpinWindow.prob β V {S | S (targetIndex j j) = true ∧ _} = _
    simp only [Set.mem_setOf_eq]
    rw [hA, hA, β.π_sum]
  constructor
  · intro S
    let σ : V → Bool := fun i => S i
    have hx := (SpinWindow.prob_one_iff β V _).1 hAone σ
    change (T.run (visible j (SpinWindow.extend V σ))).output = some (.a false) ∧
      (T.run (visible j (SpinWindow.extend V σ))).paid = k at hx
    have hr : T.run (visible j (SpinWindow.extend V σ)) = T.run (visible j S) :=
      T.source_run_eq_of_agree j _ S fun i hi => by
        simp [SpinWindow.extend, hV hi, σ]
    simpa only [Bool.not_not, hr] using hx
  · intro i hi hik
    have hBpos : 0 < SpinWindow.prob β V {S |
        (T.run (visible (!j) S)).output = some (.a true) ∧
          (T.run (visible (!j) S)).paid = i} := by
      rw [SpinWindow.split_spin β V j.toInt]
      change 0 < SpinWindow.prob β V {S | S j.toInt = false ∧ _} +
        SpinWindow.prob β V {S | S j.toInt = true ∧ _}
      simp only [Set.mem_setOf_eq]
      rw [stopping_law_b_depth β V j false k i T hlaw hi hik,
        stopping_law_b_depth β V j true k i T hlaw hi hik]
      rw [← add_mul, β.π_sum, one_mul]
      exact β.d_pos i
    obtain ⟨σ, hσ⟩ := (SpinWindow.prob_pos_iff β V _).1 hBpos
    exact ⟨SpinWindow.extend V σ, hσ⟩

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- Events are decreasing even if the same edge is queried repeatedly. -/
theorem zero_prefix_antitone (es : List ℤ) {r t : ℕ} (hrt : r ≤ t) :
    zeroEdges (es.take t).toFinset ⊆ zeroEdges (es.take r).toFinset := by
  intro S h e he
  apply h e
  exact List.mem_toFinset.mpr
    (List.take_subset_take_left es hrt (List.mem_toFinset.mp he))

theorem zero_edge_difference (es : List ℤ) (φ : Bool) (r : ℕ) (hr : r < es.length) :
    zeroEdges (es.take r).toFinset \ zeroEdges (es.take (r + 1)).toFinset =
      {S | ((ReadTree.edgeComb es φ).run (visible φ S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es φ).run (visible φ S)).paid = r + 1} := by
  ext S
  change ((∀ e ∈ (es.take r).toFinset, S e = S (e + 1)) ∧
    ¬(∀ e ∈ (es.take (r + 1)).toFinset, S e = S (e + 1))) ↔ _
  rw [← ReadTree.edge_zero_prefix, ← ReadTree.edge_zero_prefix]
  exact ReadTree.zero_prefix_difference _ _ r (by simpa using hr)

private theorem joint_zero_prefix_mass (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ)
    (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (s : Bool) (r : ℕ) (hr : r ≤ es.length) :
    prob β V (zeroEdges (es.take r).toFinset ∩ {S | S j.toInt = s}) =
      β.π s * β.T (r + 1) := by
  induction r with
  | zero =>
    have he : zeroEdges (es.take 0).toFinset = Set.univ := by ext S; simp [zeroEdges]
    rw [he, Set.univ_inter, spin_prob β V j.toInt hq s, β.T_one, mul_one]
  | succ r ih =>
    have hr' : r ≤ es.length := by omega
    have hrl : r < es.length := by omega
    have hi := ih hr'
    have hdiff := zero_edge_difference es (!j) r hrl
    let C : Set Spins := zeroEdges (es.take r).toFinset ∩ {S | S j.toInt = s}
    let D : Set Spins := zeroEdges (es.take (r + 1)).toFinset ∩ {S | S j.toInt = s}
    have hDC : D ⊆ C := fun _ h => ⟨zero_prefix_antitone es (by omega) h.1, h.2⟩
    have he : C \ D = {S | S j.toInt = s ∧
        ((ReadTree.edgeComb es (!j)).run (visible (!j) S)).output = some (.a true) ∧
        ((ReadTree.edgeComb es (!j)).run (visible (!j) S)).paid = r + 1} := by
      calc
        C \ D = {S | S j.toInt = s} ∩
            (zeroEdges (es.take r).toFinset \ zeroEdges (es.take (r + 1)).toFinset) := by
          ext S
          simp only [C, D, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
          tauto
        _ = _ := by rw [hdiff]; rfl
    have hp : prob β V (C \ D) = β.π s * β.d (r + 1) := by
      rw [he]
      exact ReadTree.stopping_law_b_depth β V j s es.length (r + 1)
        (ReadTree.edgeComb es (!j)) hlaw (by omega) (by omega)
    rw [prob_diff β V hDC] at hp
    change prob β V C = β.π s * β.T (r + 1) at hi
    change prob β V D = β.π s * β.T ((r + 1) + 1)
    rw [hi] at hp
    simp only [Bias.d] at hp
    nlinarith

theorem zero_prefix_mass (β : Bias) (V : Finset ℤ) (j : Bool) (es : List ℤ)
    (hq : j.toInt ∈ V) (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (r : ℕ) (hr : r ≤ es.length) :
    prob β V (zeroEdges (es.take r).toFinset) = β.T (r + 1) := by
  rw [split_spin β V j.toInt]
  have h0 := joint_zero_prefix_mass β V j es hq hlaw false r hr
  have h1 := joint_zero_prefix_mass β V j es hq hlaw true r hr
  rw [Set.inter_comm] at h0 h1
  rw [h0, h1, ← add_mul, β.π_sum, one_mul]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A finite window containing every potential source dependency and both possible target indices. -/
def lawWindow (T : ReadTree) : Finset ℤ := T.support ∪ {0, 1}

namespace ReadTree

theorem edgeComb_support (es : List ℤ) (φ : Bool) :
    ∀ e ∈ es, e ∈ (edgeComb es φ).support ∧ e + 1 ∈ (edgeComb es φ).support := by
  induction es with
  | nil => simp
  | cons a es ih =>
    intro e he
    simp only [edgeComb, List.map_cons, stopComb, support]
    rcases List.mem_cons.mp he with rfl | he
    · have h0 : e ∈ ({(2 * e + φ.toInt) / 2, (2 * e + φ.toInt) / 2 + 1,
          (2 * e + φ.toInt - 1) / 2, (2 * e + φ.toInt - 1) / 2 + 1} : Finset ℤ) := by
        cases φ <;> simp
      have h1 : e + 1 ∈ ({(2 * e + φ.toInt) / 2, (2 * e + φ.toInt) / 2 + 1,
          (2 * e + φ.toInt - 1) / 2, (2 * e + φ.toInt - 1) / 2 + 1} : Finset ℤ) := by
        cases φ <;> simp
      exact ⟨Finset.mem_union_left _ h0, Finset.mem_union_left _ h1⟩
    · have hh := ih e he
      exact ⟨Finset.mem_union_right _ (Finset.mem_union_left _ hh.1),
        Finset.mem_union_right _ (Finset.mem_union_left _ hh.2)⟩

end ReadTree

/-- Full law recovers tree constructors and integer geometry at each fixed biased parameter. -/
theorem finite_full_law_forces_stopping_path (β : Bias) (j : Bool) (k : ℕ)
    (hk : 1 ≤ k) (T : ReadTree) (hh : T.height ≤ k)
    (hlaw : HasStoppingLaw β (lawWindow T) j k T) :
    ∃ es : List ℤ, es.length = k ∧ es.Nodup ∧ ∃ L : ℤ,
      T = ReadTree.stopComb (es.map (fun e => 2 * e + (!j).toInt)) ∧
      es.toFinset = pathEdges L k ∧ j.toInt ∉ pathVertices L k := by
  have hV : T.support ⊆ lawWindow T := Finset.subset_union_left
  obtain ⟨hA, hB⟩ := ReadTree.stopping_law_sections β (lawWindow T) j k T hV hlaw
  obtain ⟨es, hlen, heq⟩ := ReadTree.stopComb_edge_indices k T (!j) hh hA hB
  have hcomb : T = ReadTree.edgeComb es (!j) := heq
  have hes : SpinWindow.SupportsEdges (lawWindow T) es := by
    intro e he
    have hs := ReadTree.edgeComb_support es (!j) e he
    rw [← hcomb] at hs
    exact ⟨hV hs.1, hV hs.2⟩
  have hq : j.toInt ∈ lawWindow T := by cases j <;> simp [lawWindow]
  have hlaw' : HasStoppingLaw β (lawWindow T) j es.length (ReadTree.edgeComb es (!j)) := by
    simpa only [hlen, ← hcomb] using hlaw
  have hm : SpinWindow.PrefixMasses β (lawWindow T) es := fun r _ hr =>
    SpinWindow.zero_prefix_mass β (lawWindow T) j es hq hlaw' r hr
  have ht (s : Bool) :
      SpinWindow.prob β (lawWindow T) (SpinWindow.zeroEdges es.toFinset ∩ {S | S j.toInt = s}) =
        β.π s * β.T (es.length + 1) := by
    simpa only [List.take_length] using
      SpinWindow.joint_zero_prefix_mass β (lawWindow T) j es hq hlaw' s es.length le_rfl
  obtain ⟨hnod, L, hL, hsep⟩ :=
    SpinWindow.finite_path_geometry β (lawWindow T) es j.toInt (by omega) hes hm ht
  exact ⟨es, hlen, hnod, L, heq, by simpa only [hlen] using hL,
    by simpa only [hlen] using hsep⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

def Far (j : Bool) (R : ℕ) (t : ℤ) : Prop := (R : ℤ) ≤ |t - j.toInt|

def remoteEvent (T : ReadTree) (j : Bool) (R : ℕ) (φ : Bool) : Set Spins :=
  {S | ∃ a ∈ (T.run (visible φ S)).record, Far j R a.1}

def remoteMass (β : Bias) (V : Finset ℤ) (j : Bool) (R : ℕ) (T : ReadTree) : ℝ :=
  (∑ φ : Bool, SpinWindow.prob β V (remoteEvent T j R φ)) / 2

/-- A first occurrence exists for any decidable predicate on a finite list. -/
private theorem first_far_split (j : Bool) (R : ℕ) (ts : List ℤ)
    (h : ∃ t ∈ ts, Far j R t) :
    ∃ pre : List ℤ, ∃ t : ℤ, ∃ post : List ℤ,
      ts = pre ++ t :: post ∧ (∀ a ∈ pre, ¬Far j R a) ∧ Far j R t := by
  induction ts with
  | nil => simpa using h
  | cons a ts ih =>
    by_cases ha : Far j R a
    · exact ⟨[], a, ts, rfl, by simp, ha⟩
    · have ht : ∃ t ∈ ts, Far j R t := by
        obtain ⟨t, ht, hf⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact (ha hf).elim
        · exact ⟨t, ht, hf⟩
      obtain ⟨pre, t, post, he, hn, hf⟩ := ih ht
      refine ⟨a :: pre, t, post, by simp [he], ?_, hf⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hn b hb

namespace ReadTree

theorem remote_iff_first_prefix (j : Bool) (R : ℕ) (pre : List ℤ) (t : ℤ) (post : List ℤ)
    (hn : ∀ a ∈ pre, ¬Far j R a) (hf : Far j R t) (x : ℤ → Bool) :
    (∃ a ∈ ((stopComb (pre ++ t :: post)).run x).record, Far j R a.1) ↔
      ZeroReplies pre pre.length x := by
  induction pre with
  | nil =>
    constructor
    · intro _; simp [ZeroReplies]
    · intro _
      refine ⟨(t, x t), ?_, hf⟩
      simp only [List.nil_append, stopComb, run, Execution.prepend]
      exact List.mem_cons_self
  | cons a pre ih =>
    have hna : ¬Far j R a := hn a (by simp)
    have hnp : ∀ b ∈ pre, ¬Far j R b := fun b hb => hn b (by simp [hb])
    cases hx : x a with
    | true => simp [stopComb, run, hx, Execution.prepend, hna, ZeroReplies]
    | false =>
      simpa [stopComb, run, hx, Execution.prepend, hna, ZeroReplies] using ih hnp

theorem edgeComb_opposite_remote (es : List ℤ) (j : Bool) (R : ℕ)
    (hf : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j R t) :
    remoteEvent (edgeComb es (!j)) j R j = Set.univ := by
  ext S
  constructor
  · intro _; trivial
  · intro _
    have hz : ∀ t ∈ es.map (fun e => 2 * e + (!j).toInt), visible j S t = false := by
      intro t ht
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
      have ha : (2 * e + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
      simpa only [Bool.not_not] using opposite_phase_visible (!j) S _ ha
    obtain ⟨t, ht, hfar⟩ := hf
    have hr := stopComb_all_zero (es.map (fun e => 2 * e + (!j).toInt)) (visible j S) hz
    change ∃ a ∈ ((stopComb _).run (visible j S)).record, Far j R a.1
    rw [hr]
    exact ⟨(t, false), List.mem_map.mpr ⟨t, ht, rfl⟩, hfar⟩

end ReadTree

/-- Exact source mass of the first remote call, with the paid-depth boundary m=1 included. -/
private theorem comb_first_remote_section (β : Bias) (V : Finset ℤ) (j : Bool) (R : ℕ)
    (es : List ℤ) (hq : j.toInt ∈ V)
    (hlaw : HasStoppingLaw β V j es.length (ReadTree.edgeComb es (!j)))
    (hfar : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j R t) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ es.length ∧
      remoteMass β V j R (ReadTree.edgeComb es (!j)) = (1 + β.T m) / 2 := by
  obtain ⟨pre, t, post, hts, hpre, ht⟩ := first_far_split j R _ hfar
  have hm : pre.length + 1 ≤ es.length := by
    have hlen := congrArg List.length hts
    simp only [List.length_map, List.length_append, List.length_cons] at hlen
    omega
  have he : remoteEvent (ReadTree.edgeComb es (!j)) j R (!j) =
      SpinWindow.zeroEdges (es.take pre.length).toFinset := by
    ext S
    change (∃ a ∈ ((ReadTree.stopComb _).run (visible (!j) S)).record, Far j R a.1) ↔ _
    rw [hts, ReadTree.remote_iff_first_prefix j R pre t post hpre ht]
    change ReadTree.ZeroReplies pre pre.length (visible (!j) S) ↔
      ∀ e ∈ (es.take pre.length).toFinset, S e = S (e + 1)
    rw [← ReadTree.edge_zero_prefix es (!j) S pre.length]
    simp only [ReadTree.ZeroReplies, hts, List.take_left, List.take_length]
  have hA : SpinWindow.prob β V (remoteEvent (ReadTree.edgeComb es (!j)) j R j) = 1 := by
    rw [ReadTree.edgeComb_opposite_remote es j R hfar, SpinWindow.prob_univ]
  have hB : SpinWindow.prob β V (remoteEvent (ReadTree.edgeComb es (!j)) j R (!j)) =
      β.T (pre.length + 1) := by
    rw [he]
    exact SpinWindow.zero_prefix_mass β V j es hq hlaw pre.length (by omega)
  refine ⟨pre.length + 1, by omega, hm, ?_⟩
  unfold remoteMass
  cases j <;> simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true] at hA hB ⊢ <;>
    rw [hA, hB] <;> ring

/-- Every competing tree executes a threshold-remote call with the stated sharp lower bound. -/
theorem finite_remote_read_section (β : Bias) (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (T : ReadTree) (hh : T.height ≤ k) (hlaw : HasStoppingLaw β (lawWindow T) j k T) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧
      remoteMass β (lawWindow T) j (2 * k + 1) T = (1 + β.T m) / 2 ∧
      (1 + β.T k) / 2 ≤ remoteMass β (lawWindow T) j (2 * k + 1) T := by
  obtain ⟨es, hlen, _, L, heq, hpath, hsep⟩ :=
    finite_full_law_forces_stopping_path β j k hk T hh hlaw
  have hfar : ∃ t ∈ es.map (fun e => 2 * e + (!j).toInt), Far j (2 * k + 1) t := by
    obtain ⟨e, he, hf⟩ := detached_path_remote j hk L hsep
    have he' : e ∈ es := List.mem_toFinset.mp (hpath ▸ he)
    refine ⟨2 * e + (!j).toInt, List.mem_map.mpr ⟨e, he', rfl⟩, ?_⟩
    simpa [Far] using hf
  have hcomb : T = ReadTree.edgeComb es (!j) := heq
  have hq : j.toInt ∈ lawWindow T := by cases j <;> simp [lawWindow]
  have hLaw' : HasStoppingLaw β (lawWindow T) j es.length (ReadTree.edgeComb es (!j)) := by
    simpa only [hlen, ← hcomb] using hlaw
  obtain ⟨m, hm0, hmk, hm⟩ := comb_first_remote_section β (lawWindow T) j (2 * k + 1)
    es hq hLaw' hfar
  have hmk' : m ≤ k := by omega
  rw [← hcomb] at hm
  refine ⟨m, hm0, hmk', hm, ?_⟩
  rw [hm]
  have hT := β.T_antitone hmk'
  linarith

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

private theorem observation_eq_of_agree (j φ : Bool) (T : ReadTree) (S R : Spins)
    (h : ∀ i ∈ lawWindow T, S i = R i) : observation j φ T S = observation j φ T R := by
  have hr := T.source_run_eq_of_agree φ S R (fun i hi => h i (Finset.mem_union_left _ hi))
  have hq : targetIndex j φ ∈ lawWindow T := by
    cases j <;> cases φ <;> simp [lawWindow, targetIndex]
  simp only [observation, hr, actual_endpoint, h _ hq]


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- Nonreturn observations retain their actual paid depth and have return indicator false. -/
def CappedObservation (k : ℕ) :=
  {z : Observation // z.paid ≤ k ∧ z.returned = z.output.isSome}

/-- Equality on all observations adds no hypothesis beyond the original capped complete law. -/
theorem hasStoppingLaw_iff_capped (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
    (T : ReadTree) (hh : T.height ≤ k) :
    HasStoppingLaw β V j k T ↔
      ∀ z : CappedObservation k, fullMass β V j T z.val = stoppingMass β k z.val := by
  constructor
  · intro h z; exact h z.val
  · intro h z
    by_cases hz : z.paid ≤ k ∧ z.returned = z.output.isSome
    · exact h ⟨z, hz⟩
    have he (φ : Bool) : {S : Spins | observation j φ T S = z} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro S hS
      apply hz
      have hc := T.paid_cap hh (visible φ S)
      have hr : (observation j φ T S).returned = (observation j φ T S).output.isSome := rfl
      have hp : (observation j φ T S).paid ≤ k := hc
      change observation j φ T S = z at hS
      rw [hS] at hr hp
      exact ⟨hp, hr⟩
    have hactual : fullMass β V j T z = 0 := by simp [fullMass, he]
    have hsupport (w : Observation) (hw : stoppingMass β k w ≠ 0) :
        w.paid ≤ k ∧ w.returned = w.output.isSome := by
      rcases w with ⟨h, o, d, n⟩
      cases d with
      | false => simp [stoppingMass] at hw
      | true =>
        cases h with
        | a s =>
          cases o with
          | none => simp [stoppingMass] at hw
          | some out =>
            cases out with
            | b t => simp [stoppingMass] at hw
            | a t =>
              cases t with
              | true => simp [stoppingMass] at hw
              | false =>
                have hn : n = k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨by simpa using hn.le, rfl⟩
        | b s =>
          cases o with
          | none => simp [stoppingMass] at hw
          | some out =>
            cases out with
            | b t => simp [stoppingMass] at hw
            | a t =>
              cases t with
              | false =>
                have hn : n = k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨by simpa using hn.le, rfl⟩
              | true =>
                have hn : 1 ≤ n ∧ n ≤ k := by
                  by_contra hn
                  simp [stoppingMass, hn] at hw
                exact ⟨hn.2, rfl⟩
    have htable : stoppingMass β k z = 0 := by
      by_contra hne
      exact hz (hsupport z hne)
    rw [hactual, htable]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

instance : MeasurableSpace Execution := ⊤
instance : MeasurableSingletonClass Execution := ⟨fun _ => trivial⟩
deriving instance Countable for Execution
deriving instance Countable for Observation
instance : MeasurableSpace Observation := ⊤
instance : MeasurableSingletonClass Observation := ⟨fun _ => trivial⟩


def Bias.parameter (β : Bias) : unitInterval := ⟨β.p, β.pos.le, β.lt_one.le⟩

def spinMarginal (β : Bias) : Measure Bool :=
  bernoulliMeasure true false β.parameter

/-- Bernoulli(p) spins on all integer indices, without deleting separator coordinates. -/
def spinLaw (β : Bias) : Measure Spins := Measure.infinitePi (fun _ : ℤ => spinMarginal β)

def fairPhase : Measure Bool := bernoulliMeasure true false (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : unitInterval)

/-- The fair phase is independent of the entire iid integer spin family. -/
def sourceLaw (β : Bias) : Measure SourcePoint := fairPhase.prod (spinLaw β)

instance (β : Bias) : IsProbabilityMeasure (spinMarginal β) := by
  unfold spinMarginal; infer_instance
instance (β : Bias) : IsProbabilityMeasure (spinLaw β) := by
  unfold spinLaw; infer_instance
instance : IsProbabilityMeasure fairPhase := by unfold fairPhase; infer_instance
instance (β : Bias) : IsProbabilityMeasure (sourceLaw β) := by
  unfold sourceLaw; infer_instance

private theorem spinMarginal_singleton (β : Bias) (s : Bool) :
    (spinMarginal β).real {s} = β.π s := by
  cases s <;> simp [spinMarginal, bernoulliMeasure_real_apply, Bias.parameter, Bias.π]

private theorem fairPhase_singleton (φ : Bool) : fairPhase.real {φ} = 1 / 2 := by
  cases φ <;> norm_num [fairPhase, bernoulliMeasure_real_apply]

/-- A finite marginal is the positive weighted model used by the rigidity core. -/
private theorem finiteSpinMeasure_mass (β : Bias) (V : Finset ℤ) (E : Set (V → Bool)) :
    (Measure.pi (fun _ : V => spinMarginal β)).real E = FiniteSpinLaw.mass β E := by
  classical
  let μ := Measure.pi (fun _ : V => spinMarginal β)
  have hs (σ : V → Bool) : μ.real {σ} = FiniteSpinLaw.weight β σ := by
    simp only [μ, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod,
      FiniteSpinLaw.weight]
    exact Finset.prod_congr rfl (fun i _ => spinMarginal_singleton β (σ i))
  have he : (↑(Finset.univ.filter (fun σ : V → Bool => σ ∈ E)) : Set (V → Bool)) = E := by
    ext σ; simp
  calc
    μ.real E = ∑ σ ∈ Finset.univ.filter (fun σ : V → Bool => σ ∈ E), μ.real {σ} := by
      have hsum := sum_measureReal_singleton (μ := μ)
        (Finset.univ.filter (fun σ : V → Bool => σ ∈ E))
      rw [he] at hsum
      exact hsum.symm
    _ = FiniteSpinLaw.mass β E := by
      simp only [Finset.sum_filter, hs, FiniteSpinLaw.mass]
      apply Finset.sum_congr
      · ext σ; simp
      · intro σ _; rfl

/-- Arbitrary finite-support events have their exact original infinite-source mass. -/
private theorem spinLaw_finite_event (β : Bias) (V : Finset ℤ) (E : Set Spins)
    (hE : ∀ S R, (∀ i ∈ V, S i = R i) → (S ∈ E ↔ R ∈ E)) :
    (spinLaw β).real E = SpinWindow.prob β V E := by
  let A : Set (V → Bool) := SpinWindow.extend V ⁻¹' E
  have he : E = V.restrict ⁻¹' A := by
    ext S
    apply hE S (SpinWindow.extend V (V.restrict S))
    intro i hi; simp [SpinWindow.extend, hi, Finset.restrict]
  have hm : MeasurableSet A := MeasurableSet.of_discrete
  calc
    (spinLaw β).real E = ((spinLaw β).map V.restrict).real A := by
      rw [map_measureReal_apply (V.measurable_restrict) hm]
      exact congrArg (spinLaw β).real he
    _ = (Measure.pi (fun _ : V => spinMarginal β)).real A := by
      rw [spinLaw, Measure.infinitePi_map_restrict]
    _ = SpinWindow.prob β V E := finiteSpinMeasure_mass β V A

private theorem measurable_visible (φ : Bool) (t : ℤ) : Measurable (fun S : Spins => visible φ S t) := by
  unfold visible
  split_ifs
  · change Measurable (fun S : Spins => Bool.xor (S ((t - φ.toInt) / 2))
      (S ((t - φ.toInt) / 2 + 1)))
    exact (measurable_of_countable (fun p : Bool × Bool => Bool.xor p.1 p.2)).comp
      ((measurable_pi_apply (X := fun _ : ℤ => Bool) ((t - φ.toInt) / 2)).prodMk
        (measurable_pi_apply (X := fun _ : ℤ => Bool) ((t - φ.toInt) / 2 + 1)))
  · exact measurable_const

private theorem measurable_hidden (φ : Bool) (t : ℤ) : Measurable (fun S : Spins => hidden φ S t) := by
  unfold hidden
  split_ifs <;> exact (measurable_of_countable _).comp (measurable_pi_apply _)

theorem ReadTree.measurable_source_run (T : ReadTree) (φ : Bool) :
    Measurable (fun S : Spins => T.run (visible φ S)) := by
  induction T with
  | leaf a => exact measurable_const
  | read t z o hz ho =>
    have hr : Measurable (fun S : Spins =>
        if visible φ S t then o.run (visible φ S) else z.run (visible φ S)) :=
      ho.ite ((measurable_visible φ t) (measurableSet_singleton true)) hz
    exact (measurable_of_countable (fun p : Bool × Execution =>
      p.2.prepend t p.1)).comp ((measurable_visible φ t).prodMk hr)

theorem measurable_observation (j : Bool) (T : ReadTree) :
    Measurable (fun z : SourcePoint => observation j z.1 T z.2) := by
  apply measurable_from_prod_countable_right
  intro φ
  exact (measurable_of_countable (fun p : Hidden × Execution =>
    (⟨p.1, p.2.output, p.2.returned, p.2.paid⟩ : Observation))).comp
      ((measurable_hidden φ j.toInt).prodMk (T.measurable_source_run φ))

/-- Averaging any measurable source event over the two original phases. -/
private theorem sourceLaw_real_sections (β : Bias) (E : Set SourcePoint) (hE : MeasurableSet E) :
    (sourceLaw β).real E = (∑ φ : Bool, (spinLaw β).real {S | (φ, S) ∈ E}) / 2 := by
  have he : E = ⋃ φ : Bool, ({φ} ×ˢ {S | (φ, S) ∈ E}) := by ext z; simp
  have hd : Pairwise (fun φ ψ : Bool => Disjoint
      ({φ} ×ˢ {S | (φ, S) ∈ E}) ({ψ} ×ˢ {S | (ψ, S) ∈ E})) := by
    intro φ ψ hne
    exact Set.disjoint_left.mpr (by rintro z ⟨hφ, _⟩ ⟨hψ, _⟩; exact hne (hφ.symm.trans hψ))
  conv_lhs => rw [he]
  rw [measureReal_iUnion_fintype hd (fun φ =>
    (measurableSet_singleton φ).prod (measurable_prodMk_left hE))]
  simp only [sourceLaw, measureReal_prod_prod, fairPhase_singleton]
  rw [← Finset.mul_sum]
  ring

/-- The actual original (H_j,O,D,N) law, with all nonreturn depths retained. -/
theorem sourceLaw_observation (β : Bias) (j : Bool) (T : ReadTree) (z : Observation) :
    (sourceLaw β).real {s | observation j s.1 T s.2 = z} =
      fullMass β (lawWindow T) j T z := by
  rw [sourceLaw_real_sections β {s | observation j s.1 T s.2 = z}
    ((measurable_observation j T) (measurableSet_singleton z))]
  unfold fullMass
  congr 1
  apply Finset.sum_congr rfl
  intro φ _
  apply spinLaw_finite_event β (lawWindow T)
  intro S R h
  change observation j φ T S = z ↔ observation j φ T R = z
  rw [observation_eq_of_agree j φ T S R h]

/-- The same finite-support projection also preserves actual-read events. -/
theorem sourceLaw_remote (β : Bias) (j : Bool) (R : ℕ) (T : ReadTree) :
    (sourceLaw β).real {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j R a.1} =
      remoteMass β (lawWindow T) j R T := by
  have hm : Measurable (fun s : SourcePoint => T.run (visible s.1 s.2)) :=
    measurable_from_prod_countable_right (T.measurable_source_run)
  rw [sourceLaw_real_sections β {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j R a.1}
    (hm (MeasurableSet.of_discrete (s := {v : Execution | ∃ a ∈ v.record, Far j R a.1})))]
  unfold remoteMass
  congr 1
  apply Finset.sum_congr rfl
  intro φ _
  apply spinLaw_finite_event β (lawWindow T)
  intro S S' h
  have hr := T.source_run_eq_of_agree φ S S' (fun i hi => h i (Finset.mem_union_left _ hi))
  simp only [Set.mem_setOf_eq, hr, remoteEvent]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end
