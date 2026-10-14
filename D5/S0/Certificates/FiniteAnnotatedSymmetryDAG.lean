/- GID: D5/S0/Certificates/FiniteAnnotatedSymmetryDAG
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteAnnotatedSymmetryDAG
   mirror-E: none(waiver:finite-annotated-symmetry-dag)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.accepted_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/EJMGlobalDAGData.root
   digest: Explicit partial contexts and checked child edges permit direct leaf certificates without replaying a recursive cache. -/

/- Prepared, not yet compiled or admitted. Proposed new fact: independently
checked partial-context rows, strictly decreasing child levels, exact coverage
of every value and sound leaf certificates force a smaller bad event. This
supports the original global score bound through rank descent. Sharing a rule
shape or leaf number never shares a numerical context. The concrete EJM
consumer must still supply every actual leaf, child edge and root receipt. -/

import D5.S0.Certificates.FiniteSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)

variable {Coord Value Sym : Type*} [Fintype Coord] [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

/-- The index identifies an actual partial context. A separately shared rule
table may be used by `node`, but does not identify the assignment or certificate. -/
structure Row (N : ℕ) (Coord Value Sym : Type*) where
  assignment : Partial Coord Value
  level : ℕ
  node : Node N Coord Value Sym

/-- Bounds consume the certificate for this exact row. Every split checks its
complete value domain, a strictly smaller child level, and exact assignment
update. No recursive cache expression is evaluated by this structural checker. -/
def checkRow (rows : Fin N → Row N Coord Value Sym)
    (bound : Fin N → Partial Coord Value → Bool)
    (dominates : Sym → Partial Coord Value → Bool) (index : Fin N) : Bool :=
  match (rows index).node with
  | .bound => bound index (rows index).assignment
  | .symmetry s => dominates s (rows index).assignment
  | .split i children => decide (∀ a,
      (rows (children a)).level < (rows index).level ∧
      (rows (children a)).assignment =
        Function.update (rows index).assignment i (some a))

private theorem compatible_update (p : Partial Coord Value)
    (e : Event Coord Value) (hp : Compatible p e) (i : Coord) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a ha
  by_cases same : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using ha
  · rw [Function.update_of_ne same] at ha
    exact hp j a ha

/-- A checked row either excludes a bad completion by its own sound leaf
certificate or yields a score-preserving event of strictly smaller rank.
Topological descent follows annotated levels, independently of shared shapes. -/
theorem checked_forces_smaller_bad_event
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value) (gap : ℤ)
    (rows : Fin N → Row N Coord Value Sym)
    (bound : Fin N → Partial Coord Value → Bool)
    (dominates : Sym → Partial Coord Value → Bool)
    (hbound : ∀ index p e, bound index p = true → Compatible p e → gap ≤ score e)
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (accepted : ∀ index, checkRow rows bound dominates index = true)
    (index : Fin N) (e : Event Coord Value)
    (hp : Compatible (rows index).assignment e) (hbad : score e < gap) :
    ∃ e', score e' < gap ∧ rank e' < rank e := by
  have all : ∀ level : ℕ, ∀ k : Fin N, (rows k).level = level →
      ∀ e : Event Coord Value, Compatible (rows k).assignment e →
      score e < gap → ∃ e', score e' < gap ∧ rank e' < rank e := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro k hk e hp hbad
      have checked := accepted k
      cases hn : (rows k).node with
      | bound =>
        simp only [checkRow, hn] at checked
        exact False.elim ((not_lt_of_ge (hbound k _ e checked hp)) hbad)
      | symmetry s =>
        simp only [checkRow, hn] at checked
        exact ⟨act s e, by simpa only [hscore] using hbad,
          hdominates s _ checked e hp⟩
      | split i children =>
        simp only [checkRow, hn] at checked
        have branches := of_decide_eq_true checked
        obtain ⟨shorter, context⟩ := branches (e i)
        apply ih (rows (children (e i))).level (hk ▸ shorter) (children (e i)) rfl e
        · rw [context]
          exact compatible_update _ _ hp i
        · exact hbad
  exact all (rows index).level index rfl e hp hbad

/-- A fully checked static context DAG with an all-unknown root proves the
original universal score bound. The theorem checks symmetry cuts by global
rank descent; it does not incorrectly assert local bounds for symmetry leaves. -/
theorem checked_global_lower_bound
    (score : Event Coord Value → ℤ) (rank : Event Coord Value → ℕ)
    (act : Sym → Event Coord Value → Event Coord Value) (gap : ℤ)
    (rows : Fin N → Row N Coord Value Sym)
    (bound : Fin N → Partial Coord Value → Bool)
    (dominates : Sym → Partial Coord Value → Bool)
    (hbound : ∀ index p e, bound index p = true → Compatible p e → gap ≤ score e)
    (hscore : ∀ s e, score (act s e) = score e)
    (hdominates : ∀ s p, dominates s p = true →
      ∀ e, Compatible p e → rank (act s e) < rank e)
    (accepted : ∀ index, checkRow rows bound dominates index = true)
    (root : Fin N) (rootAssignment : (rows root).assignment = fun _ => none) :
    ∀ e, gap ≤ score e := by
  have all : ∀ k : ℕ, ∀ e : Event Coord Value, rank e = k → gap ≤ score e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro e he
      by_contra bad
      have hbad : score e < gap := lt_of_not_ge bad
      have hp : Compatible (rows root).assignment e := by
        intro i a ha
        rw [rootAssignment] at ha
        cases ha
      obtain ⟨e', hbad', hrank⟩ := checked_forces_smaller_bad_event
        score rank act gap rows bound dominates hbound hscore hdominates
        accepted root e hp hbad
      exact (not_lt_of_ge (ih (rank e') (he ▸ hrank) e' rfl)) hbad'
  intro e
  exact all (rank e) e rfl

#print axioms checked_forces_smaller_bad_event
#print axioms checked_global_lower_bound

end D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
