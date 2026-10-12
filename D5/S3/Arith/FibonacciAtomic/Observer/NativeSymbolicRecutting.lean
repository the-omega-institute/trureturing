/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact symbolic recutting before residual variables and the independent native row record. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder
open NativeGroundSeparation (Term evaluate)

/-- Finite symbolic navigation never descends into a residual variable. -/
def termAt {X : Type} : Address → Term X → Option (Term X)
  | [], t => some t
  | _ :: _, .of _ => none
  | false :: p, .mul l _ => termAt p l
  | true :: p, .mul _ r => termAt p r

/-- Every residual occurrence lies at or beyond original depth d. -/
def DeepAt {X : Type} (d : Nat) : Address → Term X → Prop
  | _, .of (.inl _) => True
  | a, .of (.inr _) => d ≤ a.length
  | a, .mul l r => DeepAt d (a ++ [false]) l ∧ DeepAt d (a ++ [true]) r

private theorem termAt_fill {X : Type} (d : Nat) (a p : Address) (t : Term X)
    (deep : DeepAt d a t) (bound : a.length + p.length < d) (v : X → Source) :
    subtree p (evaluate v t) = (termAt p t).map (evaluate v) := by
  induction p generalizing a t with
  | nil => rfl
  | cons b p ih =>
      cases t with
      | of c => cases c with
        | inl c => rfl
        | inr x => simp only [DeepAt] at deep; simp only [List.length_cons] at bound; omega
      | mul l r =>
          have bd : (a ++ [b]).length + p.length < d := by
            simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *; omega
          cases b
          · exact ih (a ++ [false]) l deep.1 bd
          · exact ih (a ++ [true]) r deep.2 bd

theorem original_fill_reply {X : Type} (d : Nat) (a p : Address) (t : Term X)
    (deep : DeepAt d a t) (bound : a.length + p.length < d) (v w : X → Source) :
    readout p (evaluate v t) = readout p (evaluate w t) := by
  induction p generalizing a t with
  | nil => cases t with
    | of c => cases c with
      | inl b => rfl
      | inr x => simp only [DeepAt] at deep; simp only [List.length_nil, Nat.add_zero] at bound; omega
    | mul l r => rfl
  | cons b p ih => cases t with
    | of c => cases c with
      | inl b => rfl
      | inr x => simp only [DeepAt] at deep; simp only [List.length_cons] at bound; omega
    | mul l r =>
        have bd : (a ++ [b]).length + p.length < d := by
          simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *; omega
        cases b
        · exact ih (a ++ [false]) l deep.1 bd
        · exact ih (a ++ [true]) r deep.2 bd

/-- The complete mixed-epoch test is constant over every filling, even when
its chosen test filling violates an old-class inequality. -/
theorem symbolic_history_constant {X : Type} (d : Nat) (t : Term X)
    (deep : DeepAt d [] t) (H : NativeDepthPatterns.History)
    (bound : ∀ e ∈ H, e.2.1.length < d) (test v : X → Source) :
    NativeDepthPatterns.Consistent H (evaluate test t) ↔
      NativeDepthPatterns.Consistent H (evaluate v t) := by
  have same (e : Nat × Address × Reply) (he : e ∈ H) :
      readout e.2.1 (substitution^[e.1] (evaluate test t)) =
        readout e.2.1 (substitution^[e.1] (evaluate v t)) := by
    apply NativeDepthPatterns.original_prefix_locality
    intro a ha
    exact original_fill_reply d [] a t deep (by simpa using lt_of_le_of_lt ha (bound e he)) test v
  constructor <;> intro h e he
  · rw [← same e he]; exact h e he
  · rw [same e he]; exact h e he

/-- New holes and residual variables are separate symbols. -/
abbrev SymbolicExterior (X : Type) := FreeMagma ((Bool ⊕ X) ⊕ Address)

def symbolicExterior {X : Type} (Q : CutSet) : Address → Term X → SymbolicExterior X
  | a, .of b => if a ∈ Q then .of (.inr a) else .of (.inl b)
  | a, .mul l r => if a ∈ Q then .of (.inr a) else
      .mul (symbolicExterior Q (a ++ [false]) l) (symbolicExterior Q (a ++ [true]) r)

/-- Only residual variables are filled. New address-marked holes stay holes. -/
def exteriorFill {X : Type} (v : X → Source) : SymbolicExterior X →ₙ* HoleExterior :=
  FreeMagma.lift (fun b => match b with
    | .inl (.inl b) => .of (.inl b)
    | .inl (.inr x) => FreeMagma.map Sum.inl (v x)
    | .inr q => .of (.inr q))

def symbolicOrdered {X : Type} (Q : CutSet) (t : Term X) : List Address :=
  (Q.filter (fun q => (termAt q t).isSome)).sort (fun a b : Address => a ≤ b)

private theorem exterior_uncut (Q : CutSet) (a : Address) (u : Source)
    (clear : ∀ r : Address, a ++ r ∉ Q) : cutExterior Q a u = FreeMagma.map Sum.inl u := by
  induction u generalizing a with
  | of b =>
      have ha : a ∉ Q := by simpa using clear []
      simp [cutExterior, ha]
  | mul l r ihl ihr =>
      have ha : a ∉ Q := by simpa using clear []
      simp only [cutExterior, ha, ↓reduceIte]
      exact congrArg₂ FreeMagma.mul
        (ihl _ (fun r => by simpa [List.append_assoc] using clear (false :: r)))
        (ihr _ (fun r => by simpa [List.append_assoc] using clear (true :: r)))

private theorem exterior_commute {X : Type} (d : Nat) (Q : CutSet)
    (bound : ∀ q ∈ Q, q.length < d) (a : Address) (t : Term X)
    (deep : DeepAt d a t) (v : X → Source) :
    cutExterior Q a (evaluate v t) = exteriorFill v (symbolicExterior Q a t) := by
  induction t generalizing a with
  | of b => cases b with
    | inl b => by_cases ha : a ∈ Q <;> simp [evaluate, symbolicExterior, exteriorFill, cutExterior, ha]
    | inr x =>
        have no (r : Address) : a ++ r ∉ Q := by
          intro mem
          have := bound _ mem
          simp only [DeepAt] at deep
          simp only [List.length_append] at this
          omega
        have ha : a ∉ Q := by simpa using no []
        simpa [evaluate, symbolicExterior, exteriorFill, ha] using exterior_uncut Q a (v x) no
  | mul l r ihl ihr =>
      by_cases ha : a ∈ Q
      · simp [evaluate, symbolicExterior, exteriorFill, cutExterior, ha]
      · simp only [evaluate, FreeMagma.mul_eq, map_mul, cutExterior, ha, ↓reduceIte,
          symbolicExterior, exteriorFill]
        exact congrArg₂ FreeMagma.mul (ihl _ deep.1) (ihr _ deep.2)

/-- The symbolic full partition tests every ordered reached pair after filling. -/
def symbolicPartition {X : Type} (Q : CutSet) (t : Term X) (v : X → Source) :
    Finset (Address × Address) :=
  ((symbolicOrdered Q t).toFinset.product (symbolicOrdered Q t).toFinset).filter
    (fun pq => (termAt pq.1 t).map (evaluate v) = (termAt pq.2 t).map (evaluate v))

def symbolicRecord {X : Type} (Q : CutSet) (t : Term X) (v : X → Source) :
    HoleExterior × Finset (Address × Address) :=
  (exteriorFill v (symbolicExterior Q [] t), symbolicPartition Q t v)

/-- Exact fieldwise new-row recutting, including reached ordering, concrete
exterior, actual hole subtrees and every equality/disequality pair. -/
theorem symbolic_recut_exact {X : Type} (d : Nat) (Q : CutSet) (hQ : CutPrefixFree Q)
    (bound : ∀ q ∈ Q, q.length < d) (t : Term X) (deep : DeepAt d [] t)
    (v : X → Source) :
    orderedHoles Q (evaluate v t) = symbolicOrdered Q t ∧
    cutExterior Q [] (evaluate v t) = exteriorFill v (symbolicExterior Q [] t) ∧
    (∀ q ∈ Q, subtree q (evaluate v t) = (termAt q t).map (evaluate v)) ∧
    literalRecord Q (evaluate v t) = symbolicRecord Q t v := by
  have atQ (q : Address) (hq : q ∈ Q) :
      subtree q (evaluate v t) = (termAt q t).map (evaluate v) :=
    termAt_fill d [] q t deep (by simpa using bound q hq) v
  have order : orderedHoles Q (evaluate v t) = symbolicOrdered Q t := by
    unfold orderedHoles symbolicOrdered
    congr 1
    ext q
    rw [Finset.mem_filter, List.mem_toFinset]
    have actual := orderedHoles_mem Q hQ (evaluate v t) q
    have mem : q ∈ reachedHoles Q [] (evaluate v t) ↔ q ∈ Q ∧ (subtree q (evaluate v t)).isSome := by
      simpa [orderedHoles] using actual
    rw [mem]
    by_cases hq : q ∈ Q
    · rw [atQ q hq]; simp
    · simp [hq]
  have ext := exterior_commute d Q bound [] t deep v
  refine ⟨order, ext, atQ, ?_⟩
  apply Prod.ext ext
  ext pq
  simp only [literalRecord, actualPartition, symbolicRecord, symbolicPartition, order,
    Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, List.mem_toFinset]
  constructor
  · rintro ⟨⟨hp,hq⟩, eq⟩
    refine ⟨⟨hp,hq⟩, ?_⟩
    have pp : pq.1 ∈ Q := by
      have hh : pq.1 ∈ Q.filter (fun q => (termAt q t).isSome) := by simpa [symbolicOrdered] using hp
      exact (Finset.mem_filter.mp hh).1
    have qq : pq.2 ∈ Q := by
      have hh : pq.2 ∈ Q.filter (fun q => (termAt q t).isSome) := by simpa [symbolicOrdered] using hq
      exact (Finset.mem_filter.mp hh).1
    rwa [← atQ _ pp, ← atQ _ qq]
  · rintro ⟨⟨hp,hq⟩, eq⟩
    refine ⟨⟨hp,hq⟩, ?_⟩
    have pp : pq.1 ∈ Q := by
      have hh : pq.1 ∈ Q.filter (fun q => (termAt q t).isSome) := by simpa [symbolicOrdered] using hp
      exact (Finset.mem_filter.mp hh).1
    have qq : pq.2 ∈ Q := by
      have hh : pq.2 ∈ Q.filter (fun q => (termAt q t).isSome) := by simpa [symbolicOrdered] using hq
      exact (Finset.mem_filter.mp hh).1
    rwa [atQ _ pp, atQ _ qq]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicRecutting
