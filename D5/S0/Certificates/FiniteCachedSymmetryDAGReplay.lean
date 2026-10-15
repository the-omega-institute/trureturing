/- GID: D5/S0/Certificates/FiniteCachedSymmetryDAGReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteCachedSymmetryDAGReplay
   mirror-E: none(waiver:finite-cached-certificate-replay)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMOriginalCachedGlobalReplay.accepted_prefix_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/EJMOriginalGlobalDAGData.root
   digest: Checked finite local transitions retain their actual-context association through exhaustive cached replay. -/

/- Draft only: not compiled, not a canonical module and not a delivered
certificate. The coordinator chooses this representation only after actual
leaf timing. A concrete application must supply every cache invariant proof
and kernel-check its complete actual replay; an external table or producer
acceptance is never a premise. -/

import D5.S0.Certificates.FiniteSymmetryDAGNode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)

variable {Coord Value Sym Cache : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- The cache changes on every actual value branch. A shared node index
continues to be evaluated with its own actual partial assignment and cache. -/
def check
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ) :
    ℕ → Fin N → Cache → Partial Coord Value → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, p =>
    match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominates s p
    | .split i children => decide (∀ a,
        check nodes step lower dominates gap fuel (children a)
          (step cache i a) (Function.update p i (some a)) = true)

/-- Four independently checked actual child contexts assemble at their literal
split. A shared shape alone supplies neither the node equality nor the child
cache and partial assignment used in these premises. -/
theorem checked_split
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (i : Coord) (children : Value → Fin N)
    (node : nodes (fuel + 1) index = .split i children)
    (branches : ∀ a, check nodes step lower dominates gap fuel (children a)
      (step cache i a) (Function.update p i (some a)) = true) :
    check nodes step lower dominates gap (fuel + 1) index cache p = true := by
  simp only [check, node]
  exact decide_eq_true branches

/-- A finite prefix keeps the original bound and symmetry tests. At its
frontier it passes the complete actual fuel, node, cache and partial event to
the suffix receipt selector. No node shape or hash transfers acceptance. -/
def checkPrefix
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool) :
    ℕ → ℕ → Fin N → Cache → Partial Coord Value → Bool
  | 0, fuel, index, cache, p => frontier fuel index cache p
  | _ + 1, 0, _, _, _ => false
  | depth + 1, fuel + 1, index, cache, p =>
    match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominates s p
    | .split i children => decide (∀ a,
        checkPrefix nodes step lower dominates gap frontier depth fuel (children a)
          (step cache i a) (Function.update p i (some a)) = true)

/-- Complete separately checked suffixes splice into the existing replay.
The actual EJM consumer can earn each bounded suffix once and combine it with
the prefix without running a second numeric decision over the entire tree.
Its selector must preserve every actual cache row and action, not only an
index proposal. The existing global rank-descent theorem then applies without
any additional mathematical premise. -/
theorem checked_prefix_and_frontier
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool)
    (suffixes : ∀ fuel index cache p, frontier fuel index cache p = true →
      check nodes step lower dominates gap fuel index cache p = true)
    (depth fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (accepted : checkPrefix nodes step lower dominates gap frontier
      depth fuel index cache p = true) :
    check nodes step lower dominates gap fuel index cache p = true := by
  induction depth generalizing fuel index cache p with
  | zero => exact suffixes fuel index cache p accepted
  | succ depth ih =>
    cases fuel with
    | zero => simp only [checkPrefix, Bool.false_eq_true] at accepted
    | succ fuel =>
      cases hn : nodes (fuel + 1) index with
      | bound => simpa only [checkPrefix, check, hn] using accepted
      | symmetry s => simpa only [checkPrefix, check, hn] using accepted
      | split i children =>
        simp only [checkPrefix, hn] at accepted
        have all := of_decide_eq_true accepted
        simp only [check, hn]
        apply decide_eq_true
        intro a
        exact ih fuel (children a) (step cache i a)
          (Function.update p i (some a)) (all a)

private theorem compatible_update (p : Partial Coord Value)
    (e : Event Coord Value) (hp : Compatible p e) (i : Coord) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a ha
  by_cases same : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using ha
  · rw [Function.update_of_ne same] at ha
    exact hp j a ha

/-- Fuel-indexed validity permits a concrete prefix invariant to ensure that
every actually split coordinate was unknown, without verifying irrelevant
known-coordinate transitions. The relation is a proved invariant, not an
untrusted equality guard or imported Boolean acceptance assertion. -/
theorem checked_forces_smaller_bad_event
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (valid : ℕ → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel cache p e, valid fuel cache p → Compatible p e →
      lower cache ≤ score e)
    (hstep : ∀ fuel index cache p i children,
      nodes (fuel + 1) index = .split i children →
      0 < fuel →
      valid (fuel + 1) cache p → ∀ a,
        valid fuel (step cache i a) (Function.update p i (some a)))
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (accepted : check nodes step lower dominates gap fuel index cache p = true)
    (hvalid : valid fuel cache p) (e : Event Coord Value)
    (hp : Compatible p e) (hbad : score e < gap) :
    ∃ e', score e' < gap ∧ rank e' < rank e := by
  induction fuel generalizing index cache p with
  | zero => simp only [check, Bool.false_eq_true] at accepted
  | succ fuel ih =>
    cases hn : nodes (fuel + 1) index with
    | bound =>
      simp only [check, hn] at accepted
      have hg : gap ≤ lower cache := of_decide_eq_true accepted
      exact False.elim ((not_lt_of_ge
        (hg.trans (hlower (fuel + 1) cache p e hvalid hp))) hbad)
    | symmetry s =>
      simp only [check, hn] at accepted
      exact ⟨act s e, by simpa only [hscore] using hbad,
        hdominates s p accepted e hp⟩
    | split i children =>
      simp only [check, hn] at accepted
      have all := of_decide_eq_true accepted
      cases fuel with
      | zero =>
        have impossible := all (e i)
        simp only [check, Bool.false_eq_true] at impossible
      | succ fuel =>
        exact ih (children (e i)) (step cache i (e i))
          (Function.update p i (some (e i))) (all (e i))
          (hstep (fuel + 1) index cache p i children hn (Nat.zero_lt_succ _)
            hvalid (e i))
          (compatible_update p e hp i)

/-- Actual full replay acceptance and a proved cache invariant preserve the
complete global lower bound. Symmetry cuts remain protected by rank descent. -/
theorem checked_global_lower_bound
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (valid : ℕ → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel cache p e, valid fuel cache p → Compatible p e →
      lower cache ≤ score e)
    (hstep : ∀ fuel index cache p i children,
      nodes (fuel + 1) index = .split i children →
      0 < fuel →
      valid (fuel + 1) cache p → ∀ a,
        valid fuel (step cache i a) (Function.update p i (some a)))
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (fuel : ℕ) (root : Fin N) (initial : Cache)
    (initialValid : valid fuel initial (fun _ => none))
    (accepted : check nodes step lower dominates gap fuel root initial
      (fun _ => none) = true) :
    ∀ e, gap ≤ score e := by
  have all : ∀ k : ℕ, ∀ e : Event Coord Value, rank e = k → gap ≤ score e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he
      by_contra bad
      have hbad : score e < gap := lt_of_not_ge bad
      have hp : Compatible (fun _ => none) e := by
        intro i a ha
        cases ha
      obtain ⟨e', hbad', hrank⟩ := checked_forces_smaller_bad_event
        score rank act nodes step lower dominates gap valid hlower hstep hscore
        hdominates fuel root initial (fun _ => none) accepted initialValid e hp hbad
      exact (not_lt_of_ge (ih (rank e') (he ▸ hrank) e' rfl)) hbad'
  intro e
  exact all (rank e) e rfl

#print axioms checked_forces_smaller_bad_event
#print axioms checked_global_lower_bound
#print axioms checked_prefix_and_frontier
#print axioms checked_split

end D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
