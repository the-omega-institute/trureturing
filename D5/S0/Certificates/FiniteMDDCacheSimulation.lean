/- GID: D5/S0/Certificates/FiniteMDDCacheSimulation
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteMDDCacheSimulation
   mirror-E: none(waiver:finite-value-diagram-certificate)
   anchors: []
   utility: none
   digest: A checked value-diagram simulation retains actual cache contexts and transfers their lower bounds to activation outputs. -/

/- WIP for the same EJM certificate. No concrete diagram, simulation receipt,
CNF, LRAT refutation or global acceptance is asserted here. The actual numeric
consumer and complete kernel receipts are required before delivery. -/

import D5.S0.Certificates.FiniteSymmetryBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteMDDCacheSimulation
open D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {Coord Value Cache : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

inductive Node (N : ℕ) (Coord Value : Type*) where
  | leaf (value : ℤ)
  | branch (coordinate : Coord) (children : Value → Fin N)

/-- Fuel zero rejects even a leaf; no cyclic or truncated diagram is accepted. -/
def eval (nodes : Fin N → Node N Coord Value) :
    ℕ → Fin N → Event Coord Value → Option ℤ
  | 0, _, _ => none
  | fuel + 1, index, event =>
    match nodes index with
    | .leaf value => some value
    | .branch i children => eval nodes fuel (children (event i)) event

/-- A shared value-diagram node is checked at every distinct actual cache.
In particular, diagram shape never stands in for the earned action or row. -/
def checkSimulation (nodes : Fin N → Node N Coord Value)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ) :
    ℕ → Fin N → Cache → Bool
  | 0, _, _ => false
  | fuel + 1, index, cache =>
    match nodes index with
    | .leaf value => decide (value = lower cache)
    | .branch i children => decide (∀ a,
        checkSimulation nodes step lower fuel (children a) (step cache i a) = true)

/-- A prefix follows the literal diagram and the actual cache simultaneously.
An early leaf stutters, retaining its own actual cache for the final check. -/
def followPrefix (nodes : Fin N → Node N Coord Value)
    (step : Cache → Coord → Value → Cache) :
    (depth : ℕ) → Fin N → Cache → (Fin depth → Value) → Fin N × Cache
  | 0, index, cache, _ => (index, cache)
  | depth + 1, index, cache, path =>
    match nodes index with
    | .leaf _ => (index, cache)
    | .branch i children =>
      followPrefix nodes step depth (children (path 0)) (step cache i (path 0))
        (fun j => path j.succ)

/-- Independent bounded subtree receipts cover the complete simulation when
they quantify over every prefix. No diagram-only or sampled cache check is
substituted for the actual prefix updates in these premises. -/
theorem checked_prefixes
    (nodes : Fin N → Node N Coord Value)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (defaultValue : Value) (depth fuel : ℕ) (index : Fin N) (cache : Cache)
    (accepted : ∀ path : Fin depth → Value,
      checkSimulation nodes step lower (fuel + 1)
        (followPrefix nodes step depth index cache path).1
        (followPrefix nodes step depth index cache path).2 = true) :
    checkSimulation nodes step lower (depth + fuel + 1) index cache = true := by
  induction depth generalizing index cache with
  | zero =>
    simpa only [followPrefix, Nat.zero_add] using
      accepted (fun i => Fin.elim0 i)
  | succ depth ih =>
    have amount : depth + 1 + fuel + 1 = (depth + fuel + 1) + 1 := by omega
    rw [amount, checkSimulation]
    cases hn : nodes index with
    | leaf value =>
      simpa only [followPrefix, hn, checkSimulation] using
        accepted (fun _ => defaultValue)
    | branch i children =>
      apply decide_eq_true
      intro a
      apply ih (children a) (step cache i a)
      intro path
      simpa only [followPrefix, hn, Fin.cases_zero, Fin.cases_succ] using
        accepted (Fin.cases a path)

private theorem compatible_update (p : Partial Coord Value)
    (event : Event Coord Value) (compatible : Compatible p event) (i : Coord) :
    Compatible (Function.update p i (some (event i))) event := by
  intro j a assigned
  by_cases same : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using assigned
  · rw [Function.update_of_ne same] at assigned
    exact compatible j a assigned

/-- The cache validity relation supplies the unknown-coordinate obligation
and its full action transport. Numerical simulation checks only actual cache
updates and leaf readouts, avoiding a second enumeration of original scores. -/
theorem checked_simulation_lower_bound
    (score : Event Coord Value → ℤ)
    (nodes : Fin N → Node N Coord Value)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (valid : ℕ → Fin N → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel index cache p event,
      valid fuel index cache p → Compatible p event → lower cache ≤ score event)
    (hstep : ∀ fuel index cache p i children,
      nodes index = .branch i children → valid (fuel + 1) index cache p →
      ∀ a, valid fuel (children a) (step cache i a) (Function.update p i (some a)))
    (fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (accepted : checkSimulation nodes step lower fuel index cache = true)
    (hvalid : valid fuel index cache p) (event : Event Coord Value)
    (compatible : Compatible p event) :
    ∃ value, eval nodes fuel index event = some value ∧ value ≤ score event := by
  induction fuel generalizing index cache p with
  | zero => simp only [checkSimulation, Bool.false_eq_true] at accepted
  | succ fuel ih =>
    cases hn : nodes index with
    | leaf value =>
      simp only [checkSimulation, hn] at accepted
      have value_eq : value = lower cache := of_decide_eq_true accepted
      exact ⟨value, by simp only [eval, hn],
        value_eq.le.trans (hlower (fuel + 1) index cache p event hvalid compatible)⟩
    | branch i children =>
      simp only [checkSimulation, hn] at accepted
      have all : ∀ a,
          checkSimulation nodes step lower fuel (children a) (step cache i a) = true :=
        of_decide_eq_true accepted
      obtain ⟨value, evaluated, bound⟩ := ih (children (event i)) (step cache i (event i))
        (Function.update p i (some (event i))) (all (event i))
        (hstep fuel index cache p i children hn hvalid (event i))
        (compatible_update p event compatible i)
      exact ⟨value, by simpa only [eval, hn] using evaluated, bound⟩

/-- Activation clauses need only force the selected child. The successful
evaluation fixes its leaf, so extra activated nodes cannot change the readout. -/
theorem activation_forces_evaluation
    (nodes : Fin N → Node N Coord Value) (event : Event Coord Value)
    (active : Fin N → Prop) (readout : ℤ)
    (hbranch : ∀ index i children, nodes index = .branch i children →
      active index → active (children (event i)))
    (hleaf : ∀ index value, nodes index = .leaf value → active index → readout = value)
    (fuel : ℕ) (index : Fin N) (value : ℤ)
    (evaluated : eval nodes fuel index event = some value) (activated : active index) :
    readout = value := by
  induction fuel generalizing index with
  | zero => simp only [eval, reduceCtorEq] at evaluated
  | succ fuel ih =>
    cases hn : nodes index with
    | leaf leafValue =>
      simp only [eval, hn, Option.some.injEq] at evaluated
      exact (hleaf index leafValue hn activated).trans evaluated
    | branch i children =>
      simp only [eval, hn] at evaluated
      exact ih (children (event i)) evaluated (hbranch index i children hn activated)

/-- Successful evaluations supply an activation valuation: activate exactly
the nodes which can evaluate to the chosen readout at the fixed event. This
also covers shared nodes, without enumerating or selecting a path witness. -/
theorem activation_model_of_evaluation
    (nodes : Fin N → Node N Coord Value) (event : Event Coord Value)
    (fuel : ℕ) (root : Fin N) (readout : ℤ)
    (evaluated : eval nodes fuel root event = some readout) :
    ∃ active : Fin N → Prop, active root ∧
      (∀ index i children, nodes index = .branch i children →
        active index → active (children (event i))) ∧
      (∀ index value, nodes index = .leaf value → active index → readout = value) := by
  refine ⟨fun index => ∃ fuel, eval nodes fuel index event = some readout,
    ⟨fuel, evaluated⟩, ?_, ?_⟩
  · intro index i children branch activated
    obtain ⟨fuel, evaluation⟩ := activated
    cases fuel with
    | zero => simp only [eval, reduceCtorEq] at evaluation
    | succ fuel =>
      exact ⟨fuel, by simpa only [eval, branch] using evaluation⟩
  · intro index value leaf activated
    obtain ⟨fuel, evaluation⟩ := activated
    cases fuel with
    | zero => simp only [eval, reduceCtorEq] at evaluation
    | succ fuel =>
      simp only [eval, leaf, Option.some.injEq] at evaluation
      exact evaluation.symm

#print axioms checked_simulation_lower_bound
#print axioms checked_prefixes
#print axioms activation_forces_evaluation
#print axioms activation_model_of_evaluation

end D5.S0.Certificates.FiniteMDDCacheSimulation
