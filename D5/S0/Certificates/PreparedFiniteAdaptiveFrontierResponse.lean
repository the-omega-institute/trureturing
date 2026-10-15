/- Prepared, uncompiled source. This extends the receipt theorem and reuses
the same executable Adaptive.check. No complete EJM acceptance asserted. -/
import D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.PreparedFiniteAdaptiveFrontierResponse
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay (check)

universe u v w x
variable {Coord : Type u} {Value : Type v} {Sym : Type w} {Cache : Type x}
  [Fintype Value] [DecidableEq Coord] [DecidableEq Value] {N : Nat}

/-- A marked context can supply a proved response to every compatible bad
event. This includes semantic contradiction and canonical-cache raw suffixes;
it does not require raw check=true at another associated cache. -/
theorem checked_forces_smaller_bad_event
    (score : Event Coord Value → Int) (rank : Event Coord Value → Nat)
    (act : Sym → Event Coord Value → Event Coord Value)
    (nodes : Nat → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → Int)
    (dominates : Sym → Partial Coord Value → Bool) (gap : Int)
    (valid : Nat → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel cache p e, valid fuel cache p → Compatible p e → lower cache ≤ score e)
    (hstep : ∀ fuel index cache p i children,
      nodes (fuel + 1) index = .split i children → 0 < fuel →
      valid (fuel + 1) cache p → ∀ a,
        valid fuel (step cache i a) (Function.update p i (some a)))
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (frontier : Nat → Fin N → Cache → Partial Coord Value → Bool)
    (responses : ∀ fuel index cache p, valid fuel cache p →
      frontier fuel index cache p = true → ∀ e,
      Compatible p e → score e < gap → ∃ e', score e' < gap ∧ rank e' < rank e)
    (fuel : Nat) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (accepted : check nodes step lower dominates gap frontier fuel index cache p = true)
    (hvalid : valid fuel cache p) (e : Event Coord Value)
    (hp : Compatible p e) (hbad : score e < gap) :
    ∃ e', score e' < gap ∧ rank e' < rank e := by
  induction fuel generalizing index cache p with
  | zero => simp only [check, Bool.false_eq_true] at accepted
  | succ fuel ih =>
      by_cases marked : frontier (fuel + 1) index cache p = true
      · exact responses (fuel + 1) index cache p hvalid marked e hp hbad
      · cases hn : nodes (fuel + 1) index with
        | bound =>
            simp only [check, marked, ite_false, hn] at accepted
            have hg : gap ≤ lower cache := of_decide_eq_true accepted
            exact False.elim ((not_lt_of_ge
              (hg.trans (hlower (fuel + 1) cache p e hvalid hp))) hbad)
        | symmetry s =>
            simp only [check, marked, ite_false, hn] at accepted
            exact ⟨act s e, by simpa only [hscore] using hbad,
              hdominates s p accepted e hp⟩
        | split i children =>
            simp only [check, marked, ite_false, hn] at accepted
            obtain ⟨positive, branches⟩ := of_decide_eq_true accepted
            have hchildValid := hstep fuel index cache p i children hn positive hvalid (e i)
            have hchildCompatible : Compatible (Function.update p i (some (e i))) e := by
              intro j a ha
              by_cases same : j = i
              · subst j
                simpa only [Function.update_self, Option.some.injEq] using ha
              · rw [Function.update_of_ne same] at ha
                exact hp j a ha
            exact ih (children (e i)) (step cache i (e i))
              (Function.update p i (some (e i))) (branches (e i))
              hchildValid hchildCompatible

/-- The same complete Adaptive.check plus actual bad-event responses excludes
all bad events by strict natural rank induction at the original empty root. -/
theorem checked_global_lower_bound
    (score : Event Coord Value → Int) (rank : Event Coord Value → Nat)
    (act : Sym → Event Coord Value → Event Coord Value)
    (nodes : Nat → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → Int)
    (dominates : Sym → Partial Coord Value → Bool) (gap : Int)
    (valid : Nat → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel cache p e, valid fuel cache p → Compatible p e → lower cache ≤ score e)
    (hstep : ∀ fuel index cache p i children,
      nodes (fuel + 1) index = .split i children → 0 < fuel →
      valid (fuel + 1) cache p → ∀ a,
        valid fuel (step cache i a) (Function.update p i (some a)))
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (frontier : Nat → Fin N → Cache → Partial Coord Value → Bool)
    (responses : ∀ fuel index cache p, valid fuel cache p →
      frontier fuel index cache p = true → ∀ e,
      Compatible p e → score e < gap → ∃ e', score e' < gap ∧ rank e' < rank e)
    (fuel : Nat) (root : Fin N) (initial : Cache)
    (initialValid : valid fuel initial (fun _ => none))
    (accepted : check nodes step lower dominates gap frontier fuel root initial (fun _ => none) = true) :
    ∀ e, gap ≤ score e := by
  have all : ∀ k : Nat, ∀ e : Event Coord Value, rank e = k → gap ≤ score e := by
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
          hdominates frontier responses fuel root initial (fun _ => none)
          accepted initialValid e hp hbad
        exact (not_lt_of_ge (ih (rank e') (he ▸ hrank) e' rfl)) hbad'
  intro e
  exact all (rank e) e rfl

#print axioms checked_forces_smaller_bad_event
#print axioms checked_global_lower_bound
end D5.S0.Certificates.PreparedFiniteAdaptiveFrontierResponse
