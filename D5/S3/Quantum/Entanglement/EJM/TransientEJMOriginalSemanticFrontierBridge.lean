/- Prepared transient semantic-frontier bridge; uncompiled.
The existing checkPrefix still checks every actual value branch and every
internal bound or symmetry cut. A frontier receipt is either a kernel-proved
semantic score bound for that exact partial assignment, or the original raw
replay acceptance for that exact fuel, node, cache and partial assignment.
Semantic bounds never imply raw check=true. Global coverage is conditional on
the full prefix check and receipts for every frontier it actually reaches.
This module changes none of the original score, scale, domain or DAG inputs. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMScopedMinCandidate171040

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalSemanticFrontierBridge
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

section Generic
variable {Coord Value Sym Cache : Type*} [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- Semantic terminal bounds and original replay suffixes can share one actual
prefix. The strict depth/fuel budget preserves the original positive-child-fuel
condition on cache transitions, including the final frontier boundary. -/
theorem checked_prefix_global_lower_bound
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (nodes : ℕ → Fin N → Node N Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (valid : ℕ → Cache → Partial Coord Value → Prop)
    (hlower : ∀ fuel cache p e, valid fuel cache p → Compatible p e →
      lower cache ≤ score e)
    (hstep : ∀ fuel index cache p i children,
      nodes (fuel + 1) index = .split i children → 0 < fuel →
      valid (fuel + 1) cache p → ∀ a,
        valid fuel (step cache i a) (Function.update p i (some a)))
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (frontier : ℕ → Fin N → Cache → Partial Coord Value → Bool)
    (frontierReceipts : ∀ fuel index cache p, frontier fuel index cache p = true →
      (∀ e, Compatible p e → gap ≤ score e) ∨
        check nodes step lower dominates gap fuel index cache p = true)
    (depth fuel : ℕ) (root : Fin N) (initial : Cache)
    (budget : depth < fuel)
    (initialValid : valid fuel initial (fun _ => none))
    (accepted : checkPrefix nodes step lower dominates gap frontier depth fuel
      root initial (fun _ => none) = true) :
    ∀ e, gap ≤ score e := by
  have smaller : ∀ d currentFuel index cache p, d < currentFuel →
      checkPrefix nodes step lower dominates gap frontier d currentFuel index cache p = true →
      valid currentFuel cache p → ∀ e, Compatible p e → score e < gap →
        ∃ e', score e' < gap ∧ rank e' < rank e := by
    intro d
    induction d with
    | zero =>
      intro currentFuel index cache p _budget hchecked hvalid e hp hbad
      rcases frontierReceipts currentFuel index cache p hchecked with semantic | raw
      · exact False.elim ((not_lt_of_ge (semantic e hp)) hbad)
      · exact checked_forces_smaller_bad_event score rank act nodes step lower
          dominates gap valid hlower hstep hscore hdominates currentFuel index cache p
          raw hvalid e hp hbad
    | succ d ih =>
      intro currentFuel index cache p hbudget hchecked hvalid e hp hbad
      cases currentFuel with
      | zero => omega
      | succ currentFuel =>
        cases hn : nodes (currentFuel + 1) index with
        | bound =>
          simp only [checkPrefix, hn] at hchecked
          have hg : gap ≤ lower cache := of_decide_eq_true hchecked
          exact False.elim ((not_lt_of_ge
            (hg.trans (hlower (currentFuel + 1) cache p e hvalid hp))) hbad)
        | symmetry s =>
          simp only [checkPrefix, hn] at hchecked
          exact ⟨act s e, by simpa only [hscore] using hbad,
            hdominates s p hchecked e hp⟩
        | split i children =>
          simp only [checkPrefix, hn] at hchecked
          have branches := of_decide_eq_true hchecked
          have childBudget : d < currentFuel := by omega
          have positive : 0 < currentFuel := by omega
          have hchildValid := hstep currentFuel index cache p i children hn positive hvalid (e i)
          have hchildCompatible : Compatible (Function.update p i (some (e i))) e := by
            intro j a ha
            by_cases same : j = i
            · subst j
              simpa only [Function.update_self, Option.some.injEq] using ha
            · rw [Function.update_of_ne same] at ha
              exact hp j a ha
          exact ih currentFuel (children (e i)) (step cache i (e i))
            (Function.update p i (some (e i))) childBudget (branches (e i))
            hchildValid e hchildCompatible hbad
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
      obtain ⟨e', hbad', hrank⟩ := smaller depth fuel root initial (fun _ => none)
        budget accepted initialValid e hp hbad
      exact (not_lt_of_ge (ih (rank e') (he ▸ hrank) e' rfl)) hbad'
  intro e
  exact all (rank e) e rfl
end Generic

open D5.S0.Certificates
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache step lower)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (initial)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay
  (Valid valid_lower_le_score step_valid initial_valid)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixCache prefixPartial)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

/-- The original F1/F2, twenty coordinates, four outcomes, scale and full root
are retained. No prefix coverage or frontier acceptance is assumed from a
native producer: both remain explicit kernel proof obligations. -/
theorem original_prefix_score_lower_bound
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (frontierReceipts : ∀ fuel index cache p, frontier fuel index cache p = true →
      (∀ e, Compatible p e → scale ≤ score F1 F2 e) ∨
        check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
          scale fuel index cache p = true)
    (depth : ℕ) (budget : depth < 21)
    (accepted : checkPrefix EJMOriginalGlobalDAGData.nodes step lower
      EJMGlobalScoreSymmetry.dominates scale frontier depth 21
      EJMOriginalGlobalDAGData.root initial (fun _ => none) = true) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact checked_prefix_global_lower_bound (score F1 F2) FiniteLexSymmetry.rank
    EJMGlobalScoreSymmetry.act EJMOriginalGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Valid valid_lower_le_score step_valid
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    frontier frontierReceipts depth 21 EJMOriginalGlobalDAGData.root initial
    budget initial_valid accepted

/-- An original actual-context Accepted proof inhabits the raw side of the
same frontier interface. No context equality or shared shape substitutes for
its complete original prefix cache and partial assignment. -/
theorem accepted_suffix_frontier_receipt (depth code : ℕ)
    (index : Fin EJMOriginalGlobalDAGData.Size)
    (accepted : EJMOriginalReplayAssembly.Accepted depth code index) :
    (∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial depth code) e →
      scale ≤ score F1 F2 e) ∨
      check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
        scale (21 - depth) index (prefixCache depth code) (prefixPartial depth code) = true := by
  exact Or.inr accepted

/-- A raw suffix receipt responds to a compatible bad event by strict rank
descent. Unlike a semantic terminal bound, its symmetry cuts need the global
rank argument; this lemma does not assert a score bound on the partial event. -/
theorem accepted_suffix_bad_event_response (depth code : ℕ)
    (index : Fin EJMOriginalGlobalDAGData.Size)
    (accepted : EJMOriginalReplayAssembly.Accepted depth code index)
    (hvalid : Valid (21 - depth) (prefixCache depth code) (prefixPartial depth code))
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible (prefixPartial depth code) e)
    (hbad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  exact checked_forces_smaller_bad_event (score F1 F2) FiniteLexSymmetry.rank
    EJMGlobalScoreSymmetry.act EJMOriginalGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Valid valid_lower_le_score step_valid
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    (21 - depth) index (prefixCache depth code) (prefixPartial depth code)
    accepted hvalid e hp hbad

/-- This one actual scoped-min candidate inhabits the semantic side of the
frontier interface. It supplies neither a raw Accepted proof nor coverage of
the other original contexts. Its score bound is independent of a cache value. -/
theorem actual_171040_frontier_receipt (cache : Cache) :
    (∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial 17 1040) e →
      scale ≤ score F1 F2 e) ∨
      check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
        scale 4 (440 : Fin EJMOriginalGlobalDAGData.Size) cache (prefixPartial 17 1040) = true := by
  exact Or.inl TransientEJMScopedMinCandidate171040.actual_prefix_score_lower_bound

#print axioms checked_prefix_global_lower_bound
#print axioms original_prefix_score_lower_bound
#print axioms accepted_suffix_frontier_receipt
#print axioms accepted_suffix_bad_event_response
#print axioms actual_171040_frontier_receipt
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalSemanticFrontierBridge
