/- GID: D5/S0/Certificates/TracePartitionRefutation
   generality: G
   mirror-B: D5/B/S0/Certificates/TracePartitionRefutation
   mirror-E: none(waiver:trace-congruence-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   digest: Congruence closure, existing-state cases and one fresh-state case soundly refute bounded trace realizations, with an exact output-return signature cost bound. -/

import D5.S0.Certificates.SkeletonSlotCNF
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/- The existing Trace, Edge, Observation, FitsTrace and Skeleton remain the
   semantic owners. This is a finite proof calculus for equality-based search.
   The external rollback checker is a separate implementation: its parser,
   union-find refinement and concrete numerical proofs are not asserted to have
   been elaborated in Lean. No Lean executable was run in this session. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.TracePartitionRefutation

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Automata.FiniteSampleSkeletonTotalization
open D5.S0.Certificates.SkeletonSlotCNF

/-- Equalities accumulated by branch choices. -/
def Respects {n : Nat} {Q : Type*} (color : Fin n → Q)
    (equations : List (Fin n × Fin n)) : Prop :=
  ∀ p ∈ equations, color p.1 = color p.2

/-- Finite derivations of state equality from the actual trace equations. -/
inductive Equality {n : Nat} (T : Trace n)
    (equations : List (Fin n × Fin n)) : Fin n → Fin n → Prop
  | assumed {u v} : (u, v) ∈ equations → Equality T equations u v
  | refl (u) : Equality T equations u u
  | symm {u v} : Equality T equations u v → Equality T equations v u
  | trans {u v w} : Equality T equations u v → Equality T equations v w →
      Equality T equations u w
  | roots {u v} : u ∈ T.roots → v ∈ T.roots → Equality T equations u v
  | step (a b : Edge n) : a ∈ T.edges → b ∈ T.edges → a.block = b.block →
      Equality T equations a.source b.source → Equality T equations a.target b.target

/-- Congruence closure is sound for the existing partial block semantics. -/
theorem equality_sound {n : Nat} {Q : Type*} {T : Trace n}
    {equations : List (Fin n × Fin n)} {u v : Fin n}
    (derivation : Equality T equations u v)
    (K : Skeleton (Fin 4) Q) (color : Fin n → Q)
    (fits : FitsTrace K T color) (equations_hold : Respects color equations) :
    color u = color v := by
  induction derivation with
  | assumed h => exact equations_hold _ h
  | refl u => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | roots hu hv => exact (fits.roots _ hu).trans (fits.roots _ hv).symm
  | step a b ha hb hblock hsource ih =>
      have left := fits.edges a ha
      have right := fits.edges b hb
      rw [hblock, ih] at left
      exact Option.some.inj (left.symm.trans right)

/-- Every branch either reuses a distinguished state or makes its vertex fresh.
Fresh cases are present whenever capacity permits; equal outputs alone never
justify merging states. -/
inductive Refutation {n : Nat} (T : Trace n) (capacity : Nat) :
    List (Fin n × Fin n) → Finset (Fin n) → Prop
  | outputs {equations red} (a b : Observation n)
      (ha : a ∈ T.observations) (hb : b ∈ T.observations)
      (channel : a.channel = b.channel) (different : a.label ≠ b.label)
      (same : Equality T equations a.node b.node) : Refutation T capacity equations red
  | distinguished {equations red} (u v : Fin n)
      (hu : u ∈ red) (hv : v ∈ red) (different : u ≠ v)
      (same : Equality T equations u v) : Refutation T capacity equations red
  | split {equations red} (u : Fin n)
      (reuse : ∀ v ∈ red, Refutation T capacity ((u, v) :: equations) red)
      (fresh : red.card < capacity → Refutation T capacity equations (insert u red)) :
      Refutation T capacity equations red

private theorem injOn_insert {n : Nat} {Q : Type*} {color : Fin n → Q}
    {red : Finset (Fin n)} {u : Fin n}
    (old : Set.InjOn color (red : Set (Fin n)))
    (fresh : ∀ v ∈ red, color u ≠ color v) :
    Set.InjOn color (insert u red : Finset (Fin n)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · rfl
    · exact False.elim (fresh y hy hxy)
  · rcases hy with rfl | hy
    · exact False.elim (fresh x hx hxy.symm)
    · exact old hx hy hxy

private theorem fresh_fits_capacity {n : Nat} {Q : Type*} [Fintype Q]
    {color : Fin n → Q} {red : Finset (Fin n)} {u : Fin n} {capacity : Nat}
    (budget : Fintype.card Q ≤ capacity)
    (old : Set.InjOn color (red : Set (Fin n)))
    (fresh : ∀ v ∈ red, color u ≠ color v) : red.card < capacity := by
  classical
  have absent : u ∉ red := fun hu => fresh u hu rfl
  have injective := injOn_insert old fresh
  have card : (insert u red).card ≤ Fintype.card Q := by
    rw [← Finset.card_image_of_injOn injective]
    exact Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem absent] at card
  omega

/-- Complete reuse/fresh branching excludes every realization within capacity.
No ordering of actual machine states or reachability assumption is required. -/
theorem refutation_sound {n : Nat} {Q : Type*} [Fintype Q]
    {T : Trace n} {capacity : Nat}
    (K : Skeleton (Fin 4) Q) (budget : Fintype.card Q ≤ capacity)
    {equations : List (Fin n × Fin n)} {red : Finset (Fin n)}
    (certificate : Refutation T capacity equations red) :
    ∀ color : Fin n → Q, FitsTrace K T color → Respects color equations →
      Set.InjOn color (red : Set (Fin n)) → False := by
  induction certificate with
  | outputs a b ha hb channel different same =>
      intro color fits eqs _
      have hc := equality_sound same K color fits eqs
      have left := fits.observations a ha
      have right := fits.observations b hb
      rw [channel, hc] at left
      exact different (Option.some.inj (left.symm.trans right))
  | distinguished u v hu hv different same =>
      intro color fits eqs separate
      exact different (separate hu hv (equality_sound same K color fits eqs))
  | @split equations red u reuse fresh ihReuse ihFresh =>
      intro color fits eqs separate
      by_cases found : ∃ v ∈ red, color u = color v
      · obtain ⟨v, hv, huv⟩ := found
        apply ihReuse v hv color fits
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact huv
          · exact eqs p hp
        · exact separate
      · have different : ∀ v ∈ red, color u ≠ color v := by
          intro v hv same
          exact found ⟨v, hv, same⟩
        have enough := fresh_fits_capacity budget separate different
        exact ihFresh enough color fits eqs (injOn_insert separate different)

/-- An empty-assumption certificate with one distinguished root refutes the
existing FitsTrace problem for every recurrent carrier up to the stated size. -/
theorem refutation_excludes_fitted_skeleton {n r capacity : Nat} (T : Trace n)
    (root : Fin n) (certificate : Refutation T capacity [] {root})
    (small : r ≤ capacity) :
    ¬ ∃ K : Skeleton (Fin 4) (Fin r), ∃ color, FitsTrace K T color := by
  rintro ⟨K, color, fits⟩
  apply refutation_sound K (by simpa using small) certificate color fits
  · simp [Respects]
  · intro u hu v hv _
    have eu : u = root := by simpa using hu
    have ev : v = root := by simpa using hv
    exact eu.trans ev.symm

/-- A finite clique of distinct actual output-return pairs forces the
corresponding number of existing signature slots. The pair carrier is reused. -/
theorem signature_clique_card_le {r s k : Nat}
    {K : Skeleton (Fin 4) (Fin r)} (W : SlotWitness K s)
    (sources : Fin k → Fin r)
    (apart : ∀ i j : Fin k, i ≠ j →
      (W.transientOutput (W.slotOf (sources i)), W.returnTarget (W.slotOf (sources i))) ≠
      (W.transientOutput (W.slotOf (sources j)), W.returnTarget (W.slotOf (sources j)))) :
    k ≤ Fintype.card (ReturnPairFiber K) := by
  classical
  let pair : Fin k → ReturnPairFiber K := fun i =>
    ⟨(W.transientOutput (W.slotOf (sources i)), W.returnTarget (W.slotOf (sources i))),
      ⟨sources i, W.one_eq (sources i)⟩⟩
  have injective : Function.Injective pair := by
    intro i j h
    by_contra different
    exact apart i j different (congrArg Subtype.val h)
  simpa using Fintype.card_le_of_injective pair injective

/-- Distinguished recurrent states and a signature clique contribute to the
same canonical cost, even when the clique uses a different list of sources. -/
theorem simultaneous_state_signature_cost {r s a b : Nat}
    {K : Skeleton (Fin 4) (Fin r)} (W : SlotWitness K s)
    (states : Fin a → Fin r) (states_injective : Function.Injective states)
    (sources : Fin b → Fin r)
    (apart : ∀ i j : Fin b, i ≠ j →
      (W.transientOutput (W.slotOf (sources i)), W.returnTarget (W.slotOf (sources i))) ≠
      (W.transientOutput (W.slotOf (sources j)), W.returnTarget (W.slotOf (sources j)))) :
    a + b ≤ r + Fintype.card (ReturnPairFiber K) := by
  have left : a ≤ r := by simpa using Fintype.card_le_of_injective states states_injective
  exact Nat.add_le_add left (signature_clique_card_le W sources apart)

#print axioms equality_sound
#print axioms refutation_sound
#print axioms simultaneous_state_signature_cost

end D5.S0.Certificates.TracePartitionRefutation
