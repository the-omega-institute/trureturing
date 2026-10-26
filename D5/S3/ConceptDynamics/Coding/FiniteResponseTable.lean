/- GID: D5/S3/ConceptDynamics/Coding/FiniteResponseTable
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteResponseTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/Coding/FiniteResponseTable.finite_response_table_refinement; instance=D5/S3/ConceptDynamics/Coding/FiniteResponseTable.parallelIdentityFlipTables
   digest: Numbered incoming lifts admit finite response tables, least forgetting depths and sorted quotient sections. -/

import D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion
import D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FiniteResponseTable

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound

/-- Pathwise forgetting and equality of the response kernel use the same paths. -/
theorem forgets_iff_response {p : ℕ} {A : CountMat p p} {Q : Type}
    (L : IncomingLift A Q) (d : ℕ) :
    Forgets L d ↔ L.response d = Setoid.ker L.project := by
  constructor
  · intro h
    apply Setoid.ext
    intro u v
    constructor
    · exact fun huv => congrArg Prod.fst huv
    · intro hp
      change L.responseReadout d u = L.responseReadout d v
      apply Prod.ext hp
      funext i j path
      by_cases hu : L.project u = j
      · have hv : L.project v = j := hp.symm.trans hu
        simp only [IncomingLift.responseReadout, dif_pos hu, dif_pos hv]
        exact congrArg (fun x : {q : Q // L.project q = i} => some x.val)
          (h i j path ⟨u, hu⟩ ⟨v, hv⟩)
      · have hv : L.project v ≠ j := fun hv => hu (hp.trans hv)
        simp only [IncomingLift.responseReadout, dif_neg hu, dif_neg hv]
  · intro h i j path u v
    have hp : L.project u.val = L.project v.val := u.property.trans v.property.symm
    have hr : L.response d u.val v.val := by rw [h]; exact hp
    have obs : L.responseReadout d u.val = L.responseReadout d v.val := hr
    have ho := congrArg (fun z : Fin p ×
      ((i j : Fin p) → FinitePath A d i j → Option Q) => z.2 i j path) obs
    apply Subtype.ext
    simpa only [IncomingLift.responseReadout, dif_pos u.property,
      dif_pos v.property, Option.some.injEq] using ho

variable {n q : ℕ} {A : CountMat n n}

/-- Rectangular input arrays: invalid source-fiber entries are ignored only
    after checking the matching target, never by merging parallel edge numbers. -/
structure LiftTables (n q : ℕ) (A : CountMat n n) where
  project : Fin q → Fin n
  predecessor : (i j : Fin n) → Fin (A i j) → Fin q → Fin q

/-- Finite validation includes surjectivity and exact lift-incidence coherence. -/
def LiftTables.valid (T : LiftTables n q A) : Bool := by
  letI : Decidable (∀ i : Fin n, ∃ u : Fin q, T.project u = i) :=
    @Fintype.decidableForallFintype (Fin n) _
      (fun i => Fintype.decidableExistsFintype) inferInstance
  letI : Decidable (∀ (i j : Fin n) (a : Fin (A i j)) (u : Fin q),
      T.project u = j → T.project (T.predecessor i j a u) = i) :=
    @Fintype.decidableForallFintype (Fin n) _ (fun i =>
      @Fintype.decidableForallFintype (Fin n) _ (fun j =>
        @Fintype.decidableForallFintype (Fin (A i j)) _ (fun a =>
          Fintype.decidableForallFintype) inferInstance) inferInstance) inferInstance
  exact decide ((∀ i : Fin n, ∃ u : Fin q, T.project u = i) ∧
    ∀ (i j : Fin n) (a : Fin (A i j)) (u : Fin q),
      T.project u = j → T.project (T.predecessor i j a u) = i)

/-- The typed lift contains the supplied array entries themselves. -/
def LiftTables.toLift (T : LiftTables n q A) (h : T.valid = true) :
    IncomingLift A (Fin q) := by
  have checked : (∀ i : Fin n, ∃ u : Fin q, T.project u = i) ∧
      ∀ (i j : Fin n) (a : Fin (A i j)) (u : Fin q),
        T.project u = j → T.project (T.predecessor i j a u) = i := by
    simpa only [LiftTables.valid, decide_eq_true_eq] using h
  exact {
    project := T.project
    onto := checked.1
    lift := fun a u => ⟨T.predecessor a.source a.target a.number u.val,
      checked.2 a.source a.target a.number u.val u.property⟩ }

/-- Ordered finite recursion through each actual numbered edge. The two lifts
    in a comparison always use the SAME edge, including its parallel number. -/
def table (L : IncomingLift A (Fin q)) : ℕ → Fin q → Fin q → Bool
  | 0, u, v => decide (u = v)
  | d + 1, u, v => decide (L.project u = L.project v) &&
      @decide (∀ (i j : Fin n) (a : Fin (A i j)),
        if hu : L.project u = j then
          if hv : L.project v = j then
            table L d (L.lift ⟨i, j, a⟩ ⟨u, hu⟩).val
              (L.lift ⟨i, j, a⟩ ⟨v, hv⟩).val = true
          else True
        else True)
        (@Fintype.decidableForallFintype (Fin n) _ (fun i =>
          @Fintype.decidableForallFintype (Fin n) _ (fun j =>
            @Fintype.decidableForallFintype (Fin (A i j)) _
              (fun a => inferInstance) inferInstance) inferInstance) inferInstance)

private theorem table_spec (L : IncomingLift A (Fin q)) (d : ℕ) (u v : Fin q) :
    table L d u v = true ↔ L.response d u v := by
  induction d generalizing u v with
  | zero =>
      rw [(response_zero_and_step L).1]
      simp [table]
  | succ d ih =>
      rw [response_successor_iff]
      simp only [table, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, h⟩
        refine ⟨hp, ?_⟩
        intro a hu hv
        apply (ih _ _).mp
        simpa only [dif_pos hu, dif_pos hv] using h a.source a.target a.number
      · rintro ⟨hp, h⟩
        refine ⟨hp, ?_⟩
        intro i j a
        split_ifs with hu hv
        exact (ih _ _).mpr (h ⟨i, j, a⟩ hu hv)

/-- Equality with the whole fiber kernel, not a marginal response count. -/
def forgets (L : IncomingLift A (Fin q)) (d : ℕ) : Bool :=
  decide (∀ u v : Fin q, L.project u = L.project v → table L d u v = true)

private theorem forgets_spec (L : IncomingLift A (Fin q)) (d : ℕ) :
    forgets L d = true ↔ Forgets L d := by
  rw [forgets_iff_response]
  simp only [forgets, decide_eq_true_eq, table_spec]
  constructor
  · intro h
    apply Setoid.ext
    intro u v
    exact ⟨fun huv => congrArg Prod.fst huv, h u v⟩
  · intro h u v hp
    rw [h]
    exact hp

/-- The finite, inclusive search domain is 0,...,q-n. -/
def successes (L : IncomingLift A (Fin q)) : Finset ℕ :=
  (Finset.range (q - n + 1)).filter (fun d => forgets L d = true)

/-- The least successful entry in a bounded, completely enumerated table. -/
def minimumDepth (L : IncomingLift A (Fin q)) : Option ℕ :=
  if h : (successes L).Nonempty then some ((successes L).min' h) else none

private theorem mem_successes (L : IncomingLift A (Fin q)) (d : ℕ) :
    d ∈ successes L ↔ d ≤ q - n ∧ Forgets L d := by
  simp only [successes, Finset.mem_filter, Finset.mem_range, forgets_spec,
    Nat.lt_succ_iff]

private theorem bounded_least (L : IncomingLift A (Fin q))
    (h : ∃ d, Forgets L d) : ∃ d ≤ q - n, IsLeast {j | Forgets L j} d := by
  have supplied := common_nilpotency_forgetting_bound L
  have bound := supplied.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
  simpa only [Fintype.card_fin] using bound

private theorem successes_nonempty (L : IncomingLift A (Fin q)) :
    (successes L).Nonempty ↔ ∃ d, Forgets L d := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, ((mem_successes L d).mp hd).2⟩
  · intro h
    obtain ⟨d, hd, least⟩ := bounded_least L h
    exact ⟨d, (mem_successes L d).mpr ⟨hd, least.1⟩⟩

private theorem minimum_some (L : IncomingLift A (Fin q)) (d : ℕ) :
    minimumDepth L = some d ↔ IsLeast {j | Forgets L j} d := by
  unfold minimumDepth
  split_ifs with h
  · have hm := (mem_successes L _).mp ((successes L).min'_mem h)
    have least : IsLeast {j | Forgets L j} ((successes L).min' h) := by
      refine ⟨hm.2, ?_⟩
      intro j hj
      by_cases hjb : j ≤ q - n
      · exact (successes L).min'_le j ((mem_successes L j).mpr ⟨hjb, hj⟩)
      · omega
    constructor
    · intro he
      have he' := Option.some.inj he
      exact he' ▸ least
    · intro hd
      exact congrArg some (le_antisymm (least.2 hd.1) (hd.2 least.1))
  · constructor
    · intro he
      cases he
    · intro hd
      exact (h ((successes_nonempty L).mpr ⟨d, hd.1⟩)).elim

private theorem minimum_none (L : IncomingLift A (Fin q)) :
    minimumDepth L = none ↔ ¬ ∃ d, Forgets L d := by
  by_cases h : (successes L).Nonempty
  · rw [minimumDepth, dif_pos h]
    constructor
    · intro impossible
      cases impossible
    · intro noDepth
      exact (noDepth ((successes_nonempty L).mp h)).elim
  · rw [minimumDepth, dif_neg h]
    constructor
    · intro _ he
      exact h ((successes_nonempty L).mpr he)
    · intro _
      rfl

/-- A table fixed point persists under the identical actual-edge recursion. -/
private theorem stable (L : IncomingLift A (Fin q)) (d : ℕ)
    (h : table L (d + 1) = table L d) :
    ∀ t, table L (d + t) = table L d := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        table L (d + (t + 1)) = table L (d + t + 1) := by rw [Nat.add_assoc]
        _ = table L (d + 1) := by
          funext u v
          simp only [table]
          rw [ih]
        _ = table L d := h

/-- Nonempty class membership is certified using the actual response relation. -/
def members (L : IncomingLift A (Fin q)) (d : ℕ) (u : Fin q) : Finset (Fin q) :=
  Finset.univ.filter (fun v => table L d v u = true)

private theorem members_nonempty (L : IncomingLift A (Fin q)) (d : ℕ) (u : Fin q) :
    (members L d u).Nonempty := by
  refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact (table_spec L d u u).mpr ((L.response d).refl u)

/-- Least original state number in the response class; empty Q needs no choice. -/
def representative (L : IncomingLift A (Fin q)) (d : ℕ) (u : Fin q) : Fin q :=
  (members L d u).min' (members_nonempty L d u)

private theorem representative_related (L : IncomingLift A (Fin q)) (d : ℕ)
    (u : Fin q) : L.response d (representative L d u) u := by
  exact (table_spec L d _ _).mp
    (Finset.mem_filter.mp ((members L d u).min'_mem (members_nonempty L d u))).2

private theorem representative_eq (L : IncomingLift A (Fin q)) (d : ℕ)
    (u v : Fin q) : representative L d u = representative L d v ↔ L.response d u v := by
  constructor
  · intro h
    have hu := representative_related L d u
    have hv := representative_related L d v
    rw [h] at hu
    exact (L.response d).trans ((L.response d).symm hu) hv
  · intro h
    apply le_antisymm
    · apply (members L d u).min'_le
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (table_spec L d _ _).mpr
        ((L.response d).trans (representative_related L d v) ((L.response d).symm h))⟩
    · apply (members L d v).min'_le
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (table_spec L d _ _).mpr
        ((L.response d).trans (representative_related L d u) h)⟩

private theorem representative_idem (L : IncomingLift A (Fin q)) (d : ℕ) (u : Fin q) :
    representative L d (representative L d u) = representative L d u :=
  (representative_eq L d _ _).mpr (representative_related L d u)

/-- Sorted fixed points of the least-representative operation. -/
def representatives (L : IncomingLift A (Fin q)) (d : ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun u => representative L d u = u)

/-- Dense class numbers follow the original numeric state order. -/
def classOf (L : IncomingLift A (Fin q)) (d : ℕ) (u : Fin q) :
    Fin (representatives L d).card :=
  ((representatives L d).orderIsoOfFin rfl).symm
    ⟨representative L d u, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, representative_idem L d u⟩⟩

def representativeAt (L : IncomingLift A (Fin q)) (d : ℕ)
    (i : Fin (representatives L d).card) : Fin q :=
  ((representatives L d).orderIsoOfFin rfl i).val

private theorem representativeAt_classOf (L : IncomingLift A (Fin q))
    (d : ℕ) (u : Fin q) : representativeAt L d (classOf L d u) = representative L d u := by
  simp only [representativeAt, classOf, OrderIso.apply_symm_apply]

private theorem classOf_representativeAt (L : IncomingLift A (Fin q))
    (d : ℕ) (i : Fin (representatives L d).card) :
    classOf L d (representativeAt L d i) = i := by
  apply ((representatives L d).orderIsoOfFin rfl).injective
  apply Subtype.ext
  change representativeAt L d (classOf L d (representativeAt L d i)) =
    representativeAt L d i
  rw [representativeAt_classOf]
  exact (Finset.mem_filter.mp
    (((representatives L d).orderIsoOfFin rfl i).property)).2

private theorem classOf_eq (L : IncomingLift A (Fin q)) (d : ℕ) (u v : Fin q) :
    classOf L d u = classOf L d v ↔ L.response d u v := by
  constructor
  · intro h
    apply (representative_eq L d u v).mp
    simpa only [representativeAt_classOf] using congrArg (representativeAt L d) h
  · intro h
    apply ((representatives L d).orderIsoOfFin rfl).injective
    apply Subtype.ext
    change representativeAt L d (classOf L d u) =
      representativeAt L d (classOf L d v)
    rw [representativeAt_classOf, representativeAt_classOf]
    exact (representative_eq L d u v).mpr h

/-- Explicit semantic transport. Its inverse uses the computed representative,
    never Quotient.out or an asserted equality with the classical numbering. -/
def quotientEquiv (L : IncomingLift A (Fin q)) (d : ℕ) :
    Quotient (L.response d) ≃ Fin (representatives L d).card where
  toFun := Quotient.lift (classOf L d) (fun _ _ h => (classOf_eq L d _ _).mpr h)
  invFun := fun i => Quotient.mk _ (representativeAt L d i)
  left_inv := by
    intro c
    refine Quotient.inductionOn c ?_
    intro u
    apply Quotient.sound
    change L.response d (representativeAt L d (classOf L d u)) u
    rw [representativeAt_classOf]
    exact representative_related L d u
  right_inv := classOf_representativeAt L d

/-- One owning relation: actual numbered-edge table, persistent fixed points,
    complete bounded least-depth decision, and deterministic quotient section.
    This is not yet a controlled-matrix trace exporter. -/
theorem finite_response_table_refinement (L : IncomingLift A (Fin q)) :
    (∀ d u v, table L d u v = true ↔ L.response d u v) ∧
    (∀ d, forgets L d = true ↔ Forgets L d) ∧
    (∀ d, minimumDepth L = some d ↔ IsLeast {j | Forgets L j} d) ∧
    (minimumDepth L = none ↔ ¬ ∃ d, Forgets L d) ∧
    (∀ d, minimumDepth L = some d → d ≤ q - n) ∧
    (∀ d, table L (d + 1) = table L d → ∀ t, table L (d + t) = table L d) ∧
    (∀ d u v, classOf L d u = classOf L d v ↔ L.response d u v) ∧
    (∀ d i, classOf L d (representativeAt L d i) = i) ∧
    (∀ d u, representativeAt L d (classOf L d u) = representative L d u) ∧
    (∀ d u, L.response d (representative L d u) u) ∧
    (∀ d u v, L.response d v u → representative L d u ≤ v) := by
  refine ⟨table_spec L, forgets_spec L, minimum_some L, minimum_none L,
    ?_, stable L, classOf_eq L, classOf_representativeAt L,
    representativeAt_classOf L, representative_related L, ?_⟩
  · intro d hd
    have least := (minimum_some L d).mp hd
    obtain ⟨b, hb, hleast⟩ := bounded_least L ⟨d, least.1⟩
    exact (least.2 hleast.1).trans hb
  · intro d u v h
    exact (members L d u).min'_le v
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (table_spec L d v u).mpr h⟩)

/-- Numbered form of the identity/flip parallel-edge example in
CommonNilpotencyForgettingBound: averaging loses the distinction between the
edges, whereas the pathwise checker keeps both actual edge numbers. -/
def parallelIdentityFlipTables : LiftTables 1 2 (fun _ _ => 2) where
  project := fun _ => 0
  predecessor := fun _ _ a u => if a = 0 then u else if u = 0 then 1 else 0

end D5.S3.ConceptDynamics.Coding.FiniteResponseTable
