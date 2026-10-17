/- GID: D5/S0/Certificates/FinitePartialBoundDAG
   generality: G
   mirror-B: D5/B/S0/Certificates/FinitePartialBoundDAG
   mirror-E: none(waiver:finite-symmetry-partial-bound-replay)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.associated_lower_le_score; instance=D5/S3/Quantum/Entanglement/EJM/EJMLocalBoundAcceptance.triangle_accepted
   digest: A topologically ordered local DAG checks every value branch and earns partial lower bounds using actual score-preserving symmetries. -/

import D5.S0.Certificates.FiniteSymmetryBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FinitePartialBoundDAG
open D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {Coord Value Sym : Type*} [Fintype Coord] [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- Each split lists all value choices, and references an earlier checked row. -/
inductive Rule (N : ℕ) (Coord Value Sym : Type*) where
  | complete (e : Event Coord Value)
  | split (i : Coord) (child : Value → Fin N) (symmetry : Value → Sym)

structure Row (N : ℕ) (Coord Value Sym : Type*) where
  assignment : Partial Coord Value
  lower : ℤ
  rule : Rule N Coord Value Sym

/-- Neither child coverage, topological order nor local canonicalization is trusted. -/
def checkRow (score : Event Coord Value → ℤ)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym) (j : Fin N) : Bool :=
  match (rows j).rule with
  | .complete e => decide ((rows j).assignment = completed e ∧ (rows j).lower ≤ score e)
  | .split i child sym => decide (∀ a, (child a).val < j.val ∧
      (rows j).lower ≤ (rows (child a)).lower ∧
      (rows (child a)).assignment = partialAct (sym a)
        (Function.update (rows j).assignment i (some a)))

/-- Topology and exact assignment transport are independent of terminal score evaluation.
Split rows still check every value, earlier indices, and the inherited lower bound. -/
def checkStructure
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym) (j : Fin N) : Bool :=
  match (rows j).rule with
  | .complete e => decide ((rows j).assignment = completed e)
  | .split i child sym => decide (∀ a, (child a).val < j.val ∧
      (rows j).lower ≤ (rows (child a)).lower ∧
      (rows (child a)).assignment = partialAct (sym a)
        (Function.update (rows j).assignment i (some a)))

/-- A structurally accepted DAG becomes fully accepted once each completed event's
actual score is checked against that row's recorded lower bound. -/
theorem checked_structure_and_terminals
    (score : Event Coord Value → ℤ)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym)
    (structureAccepted : ∀ j, checkStructure partialAct rows j = true)
    (terminalBounds : ∀ j e, (rows j).rule = .complete e → (rows j).lower ≤ score e) :
    ∀ j, checkRow score partialAct rows j = true := by
  intro j
  have hs := structureAccepted j
  cases hrule : (rows j).rule with
  | complete e =>
    simp only [checkStructure, hrule] at hs
    have hp : (rows j).assignment = completed e := of_decide_eq_true hs
    simp only [checkRow, hrule, hp, terminalBounds j e hrule, and_self, decide_true]
  | split i child sym =>
    simpa only [checkStructure, checkRow, hrule] using hs

private theorem compatible_update (p : Partial Coord Value) (e : Event Coord Value)
    (hp : Compatible p e) (i : Coord) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a ha
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using ha
  · rw [Function.update_of_ne hji] at ha
    exact hp j a ha

/-- Every accepted row bounds every actual completion of its own partial event.
A canonicalization edge must transport compatibility and preserve the score. -/
theorem checked_rows_lower_bound
    (score : Event Coord Value → ℤ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (hact : ∀ s p e, Compatible p e → Compatible (partialAct s p) (act s e))
    (hscore : ∀ s e, score (act s e) = score e)
    (rows : Fin N → Row N Coord Value Sym)
    (accepted : ∀ j, checkRow score partialAct rows j = true)
    (j : Fin N) (e : Event Coord Value) (hp : Compatible (rows j).assignment e) :
    (rows j).lower ≤ score e := by
  have all : ∀ m : ℕ, ∀ k : Fin N, k.val = m → ∀ e : Event Coord Value,
      Compatible (rows k).assignment e → (rows k).lower ≤ score e := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hkm e hp
      have hc := accepted k
      cases hrule : (rows k).rule with
      | complete base =>
        simp only [checkRow, hrule] at hc
        obtain ⟨hpartial, hbound⟩ := of_decide_eq_true hc
        have he : e = base := by
          funext i
          exact hp i (base i) (by rw [hpartial]; rfl)
        simpa only [he] using hbound
      | split i child sym =>
        simp only [checkRow, hrule] at hc
        have branches : ∀ a, (child a).val < k.val ∧
            (rows k).lower ≤ (rows (child a)).lower ∧
            (rows (child a)).assignment = partialAct (sym a)
              (Function.update (rows k).assignment i (some a)) := of_decide_eq_true hc
        obtain ⟨hshort, hbound, hpartial⟩ := branches (e i)
        have hcompat : Compatible (rows (child (e i))).assignment (act (sym (e i)) e) := by
          rw [hpartial]
          exact hact _ _ _ (compatible_update _ _ hp i)
        have hchild := ih (child (e i)).val (hkm ▸ hshort)
          (child (e i)) rfl (act (sym (e i)) e) hcompat
        exact hbound.trans (by simpa only [hscore] using hchild)
  exact all j.val j rfl e hp

#print axioms checked_rows_lower_bound
#print axioms checked_structure_and_terminals

end D5.S0.Certificates.FinitePartialBoundDAG
