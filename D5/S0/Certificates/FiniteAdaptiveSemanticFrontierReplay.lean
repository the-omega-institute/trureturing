/- GID: D5/S0/Certificates/FiniteAdaptiveSemanticFrontierReplay
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteAdaptiveSemanticFrontierReplay
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.accepted_original_root
   digest: A fuel-indexed adaptive replay checks actual bound, symmetry and split nodes, with a separately supplied semantic frontier. -/

import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

/-!
Library search: FiniteCachedSymmetryDAGReplay.checkPrefix consumes frontier
only at its single fixed depth zero. Its checked_prefix_and_frontier accepts
only raw suffixes. Neither covers a frontier whose actual cuts have different
depths and whose receipts may be semantic bounds. The already proved raw
checked_forces_smaller_bad_event is reused at raw frontier leaves below.

admission_basis: escape-witness
checked_forces_smaller_bad_event: proof_shape: content; escape_witness: every
accepted adaptive context, with its exact valid cache, turns each compatible
bad event into a strictly smaller-rank bad event, regardless of cut depth.
Consumer: checked_global_lower_bound uses that response at the empty root.
checked_global_lower_bound: proof_shape: content; escape_witness: natural rank
induction excludes all bad events after every symmetry transformation restarts
at the empty root. A transformed event need not remain in its previous partial.
checked_split: proof_shape: bind-only; intended actual consumer: the prepared
EJM adaptive assembly at every interior node of the cap4096 cover. This helper
retains the exact literal split and all actual child contexts.

The prepared EJM consumer keeps the original twenty coordinates, four values,
F1/F2, thirty-two blocks, scale 6987435, root and initial cache. The proposed
52,867 cut count and native depth histogram are not premises of any theorem.
A complete original adaptive check and every reached valid-context frontier
receipt are still required. Checker first-freeze admission requires an actual
complete accepted input and its live soundness application; these sources supply no
such receipt. No literature novelty is claimed for induction or rank descent.
The three new public theorem registrations lack compiled source-owned evidence
and current binding. Unfinished four-slot audit is associated with
https://github.com/the-omega-institute/trureturing/issues/16309
No audit success or declared_validated status is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)

universe u v w x
variable {Coord : Type u} {Value : Type v} {Sym : Type w} {Cache : Type x}
  [Fintype Value] [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- At every positive fuel, an exact-context frontier may terminate replay.
Otherwise the original bound, symmetry and all finite value branches remain.
Every actual split requires positive child fuel; fuel zero always rejects. -/
def check
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool) :
    ℕ → Fin N → Cache → Partial Coord Value → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, p =>
    if frontier (fuel + 1) index cache p = true then true
    else match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominates s p
    | .split i children => decide (0 < fuel ∧ ∀ a,
        check nodes step lower dominates gap frontier fuel (children a)
          (step cache i a) (Function.update p i (some a)) = true)

/-- Assemble every actual child context at an unmarked original split.
This is the composition door for mixed-depth cut receipts. -/
theorem checked_split
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool)
    (fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (i : Coord) (children : Value → Fin N)
    (unmarked : frontier (fuel + 1) index cache p = false)
    (node : nodes (fuel + 1) index = .split i children)
    (positive : 0 < fuel)
    (branches : ∀ a, check nodes step lower dominates gap frontier fuel (children a)
      (step cache i a) (Function.update p i (some a)) = true) :
    check nodes step lower dominates gap frontier (fuel + 1) index cache p = true := by
  simp only [check, unmarked, Bool.false_eq_true, ite_false, node]
  exact decide_eq_true ⟨positive, branches⟩

/-- A semantic frontier contradicts a bad completion; an exact raw frontier
reuses cached replay descent. All other nodes follow the original semantics. -/
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
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool)
    (frontierReceipts : ∀ fuel index cache p, valid fuel cache p →
      frontier fuel index cache p = true →
      (∀ e, Compatible p e → gap ≤ score e) ∨
        D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
          nodes step lower dominates gap fuel index cache p = true)
    (fuel : ℕ) (index : Fin N) (cache : Cache) (p : Partial Coord Value)
    (accepted : check nodes step lower dominates gap frontier fuel index cache p = true)
    (hvalid : valid fuel cache p) (e : Event Coord Value)
    (hp : Compatible p e) (hbad : score e < gap) :
    ∃ e', score e' < gap ∧ rank e' < rank e := by
  induction fuel generalizing index cache p with
  | zero => simp only [check, Bool.false_eq_true] at accepted
  | succ fuel ih =>
    by_cases marked : frontier (fuel + 1) index cache p = true
    · rcases frontierReceipts (fuel + 1) index cache p hvalid marked with semantic | raw
      · exact False.elim ((not_lt_of_ge (semantic e hp)) hbad)
      · exact D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.checked_forces_smaller_bad_event
          score rank act nodes step lower dominates gap valid hlower hstep hscore hdominates
          (fuel + 1) index cache p raw hvalid e hp hbad
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
          (Function.update p i (some (e i))) (branches (e i)) hchildValid hchildCompatible

/-- Complete adaptive root acceptance excludes every event below the gap.
Every valid-context frontier receipt, invariant and symmetry obligation
stays explicit. -/
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
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool)
    (frontierReceipts : ∀ fuel index cache p, valid fuel cache p →
      frontier fuel index cache p = true →
      (∀ e, Compatible p e → gap ≤ score e) ∨
        D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check
          nodes step lower dominates gap fuel index cache p = true)
    (fuel : ℕ) (root : Fin N) (initial : Cache)
    (initialValid : valid fuel initial (fun _ => none))
    (accepted : check nodes step lower dominates gap frontier fuel root initial
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
        hdominates frontier frontierReceipts fuel root initial (fun _ => none) accepted initialValid e hp hbad
      exact (not_lt_of_ge (ih (rank e') (he ▸ hrank) e' rfl)) hbad'
  intro e
  exact all (rank e) e rfl


#print axioms checked_split
#print axioms checked_forces_smaller_bad_event
#print axioms checked_global_lower_bound
end D5.S0.Certificates.FiniteAdaptiveSemanticFrontierReplay
