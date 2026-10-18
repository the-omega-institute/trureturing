/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteTreeLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteTreeLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete finite endpoint-output-count masses imply the two deterministic phase sections. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SpinWindow
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.StoppingStructure

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

theorem split_spin (β : Bias) (V : Finset ℤ) (q : ℤ) (E : Set Spins) :
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

theorem observation_a_iff (j φ s : Bool) (T : ReadTree) (S : Spins)
    (o : Option Hidden) (n : ℕ) :
    observation j φ T S = ⟨.a s, o, o.isSome, n⟩ ↔
      φ = j ∧ S (targetIndex j j) = s ∧
        (T.run (visible j S)).output = o ∧ (T.run (visible j S)).paid = n := by
  cases j <;> cases φ <;>
    simp [observation, hidden, Bool.toInt, targetClass, targetIndex,
      Observation.mk.injEq, Execution.returned] <;> aesop

theorem observation_b_iff (j φ s : Bool) (T : ReadTree) (S : Spins)
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

theorem stopping_law_b_depth (β : Bias) (V : Finset ℤ) (j s : Bool) (k i : ℕ)
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

theorem stopping_law_sections (β : Bias) (V : Finset ℤ) (j : Bool) (k : ℕ)
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
