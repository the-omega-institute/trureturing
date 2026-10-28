/- GID: D5/S3/Observer/Separation/ExecutableCapacityJoin
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/ExecutableCapacityJoin
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Sets]
   utility: none
   digest: Finite active response tables supply the exact original-tree separator solver. -/

import D5.S3.Observer.Separation.CapacitySensitiveSupport
import D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection

/-! Finite presentations of the original active capacities and local relations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Separation.ExecutableCapacityJoin

open D5.S3.Observer.Separation.FixedTreeCommonExtension
open D5.S3.Observer.Separation.CapacitySensitiveSupport
open D5.S3.ConceptDynamics.Observation.HistoryPayloadFactorization
open D5.S3.ConceptDynamics.Gluing.RunningIntersectionRecords
open D5.S3.ConceptDynamics.Gluing.FiniteRunningIntersection

/-- Compute descendant-leaf coordinates without inspecting vertex labels. -/
private def leafTable {I V : Type} [DecidableEq I] : Tree I V → Finset I
  | .leaf _ i => {i}
  | .node _ _ c => Finset.univ.biUnion (fun j => leafTable (c j))

private theorem leaf_table_eq {I V : Type} [DecidableEq I] (s : Tree I V) :
    leafTable s = leaves s := by
  induction s with
  | leaf v i => rfl
  | node v n c ih =>
    ext i
    simp [leafTable, leaves, ih]

private instance leafDecidable {I V : Type} [DecidableEq I] (s : Tree I V) :
    DecidablePred (fun i => i ∈ leaves s) := fun i =>
  decidable_of_iff (i ∈ leafTable s) (by rw [leaf_table_eq])

/-- Totalize the prescribed task using exactly the supplied illegal-cell values. -/
private def completeTable {C O : Type} (D : Set C) [DecidablePred (· ∈ D)]
    (f : D → O) (h : ↥(Dᶜ) → O) : C → O :=
  fun x => if hx : x ∈ D then f ⟨x, hx⟩ else h ⟨x, hx⟩

/-- A full complementary response for an actually promised input. -/
private def responseRow {I V O : Type} [DecidableEq I] {X : I → Type}
    (H : (∀ i, X i) → O) (s : Tree I V) (x : ∀ i, X i) :
    (∀ i : {i // i ∉ leaves s}, X i.val) → O := fun b =>
  H (fun i => if hi : i ∈ leaves s then x i else b ⟨i, hi⟩)

variable {I V O : Type} [Fintype I] [DecidableEq I] {X : I → Type}
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [Fintype O] [DecidableEq O]

/-- Count distinct complete response functions reached by D, rather than all
possible prefixes. The complement quantifier includes all complementary inputs. -/
def costTable (t : Tree I V) (D : Set (∀ i, X i)) [DecidablePred (· ∈ D)]
    (f : D → O) : Nodes t → (↥(Dᶜ) → O) → ℕ := fun v h =>
  (Finset.univ.image (fun x : D => responseRow (completeTable D f h) v.val x.val)).card

private theorem response_row_eq (H : (∀ i, X i) → O) (s : Tree I V)
    (x : ∀ i, X i) :
    responseRow H s x = (responseMessage H s x).val := by
  classical
  funext b
  unfold responseRow responseMessage
  change H _ = D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response X H
    (fun i => i ∈ leaves s) (fun i => x i.val) b
  unfold D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response
  apply congrArg H
  funext i
  simp only [Equiv.piEquivPiSubtypeProd_symm_apply]

/-- The computable response count is precisely the original active capacity. -/
private theorem cost_table_eq (t : Tree I V) (D : Set (∀ i, X i))
    [DecidablePred (· ∈ D)] (f : D → O) : costTable t D f = sourceCost t D f := by
  classical
  funext v h
  have complete_eq : completeTable D f h = complete D f h := by
    funext x
    by_cases hx : x ∈ D <;> simp [completeTable, complete, hx]
  let H := completeTable D f h
  let R := Finset.univ.image (fun x : D => responseRow H v.val x.val)
  let A := Set.range (fun x : D => responseMessage H v.val x.val)
  let g : A → R := fun q => ⟨q.val.val, by
    obtain ⟨x, hx⟩ := q.property
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by
      rw [response_row_eq]
      exact congrArg Subtype.val hx⟩⟩
  have bij : Function.Bijective g := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : R => z.val) hab
    · intro b
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp b.property
      refine ⟨⟨responseMessage H v.val x.val, x, rfl⟩, ?_⟩
      apply Subtype.ext
      exact (response_row_eq H v.val x.val).symm.trans hx
  change R.card = activeCapacity D (complete D f h) v.val
  rw [← complete_eq]
  change R.card = Nat.card A
  calc
    R.card = Nat.card R := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card A := Nat.card_congr (Equiv.ofBijective g bij).symm

section FiniteRelations

variable {U N : Type} [Fintype U] [DecidableEq U] [Fintype N]

/-- Sensitivity is tested by finite pairs of assignments, with no support oracle. -/
instance sensitiveDecidable (c : (U → O) → ℕ) : DecidablePred (· ∈ sensitive c) :=
  fun u => inferInstanceAs (Decidable (∃ h h' : U → O,
    (∀ j, j ≠ u → h j = h' j) ∧ c h ≠ c h'))

/-- The original universal-extension definition is decided over the enumerated
finite assignment carrier; it is not replaced by pairwise consistency. -/
def localTable (c : N → (U → O) → ℕ) (k : ℕ) (v : N) :
    Finset (sensitive (c v) → O) :=
  Finset.univ.filter (fun s => ∀ h : U → O,
    (∀ u : sensitive (c v), h u.val = s u) → c v h ≤ k)

end FiniteRelations

private theorem local_table_mem {U N : Type} [Fintype U] [DecidableEq U]
    [Fintype N] (c : N → (U → O) → ℕ) (k : ℕ) (v : N)
    (s : sensitive (c v) → O) : s ∈ localTable c k v ↔ s ∈ localFeasible c k v := by
  simp only [localTable, Finset.mem_filter, Finset.mem_univ, true_and,
    localFeasible, Set.mem_setOf_eq]

/-- A base output is read from the supplied finite alphabet. Nonemptiness follows
from the original nonempty promise; no choice of an extension is performed. -/
private def baseOutput (D : Set (∀ i, X i)) (hD : D.Nonempty) (f : D → O)
    (values : List O) (hValues : ∀ o, o ∈ values) : O :=
  values.head (by
    intro he
    obtain ⟨x, hx⟩ := hD
    have hm := hValues (f ⟨x, hx⟩)
    rw [he] at hm
    exact List.not_mem_nil hm)

variable [∀ i, Nonempty (X i)]
  (t : Tree I V) (D : Set (∀ i, X i)) [DecidablePred (· ∈ D)]
  (hD : D.Nonempty) (f : D → O)
  [Fintype (Nodes t)] [DecidableEq (Nodes t)]
  (G : SimpleGraph (Nodes t)) [DecidableRel G.Adj]

/-- The complete finite source computation uses the original implementation
tree's actual active capacities and a separate, arbitrary support tree. -/
def sourceSolve (hG : G.IsTree)
    (hRI : RunningIntersection G (fun v => sensitive (sourceCost t D f v)))
    (r : Nodes t) (nodes : List (Nodes t)) (hNodes : ∀ n, n ∈ nodes)
    (vars : List ↥(Dᶜ)) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) (k : ℕ) :=
  solve G (fun v => sensitive (costTable t D f v)) (localTable (costTable t D f) k)
    hG (by simpa only [cost_table_eq] using hRI) r
    nodes hNodes vars hVars values hValues (baseOutput D hD f values hValues)

/-- Exact finite computation, witness reconstruction and separator bounds for
every budget of the full original implementation tree, including its root. -/
theorem source_solver_spec (ht : Full t) (hall : leaves t = Finset.univ)
    (hG : G.IsTree)
    (hRI : RunningIntersection G (fun v => sensitive (sourceCost t D f v)))
    (r : Nodes t) (nodes : List (Nodes t)) (hNodes : ∀ n, n ∈ nodes)
    (vars : List ↥(Dᶜ)) (hVars : ∀ x, x ∈ vars)
    (values : List O) (hValues : ∀ o, o ∈ values) :
    costTable t D f = sourceCost t D f ∧
    (∀ k : ℕ,
      (sourceSolve t D hD f G hG hRI r nodes hNodes vars hVars values hValues k).isSome =
        true ↔ minimumPeak t D f ≤ k) ∧
    (∀ k j, sourceSolve t D hD f G hG hRI r nodes hNodes vars hVars values hValues k =
      some j → j ∈ rawJoin (fun _ => O) (fun v => sensitive (costTable t D f v))
        (fun v => localFeasible (costTable t D f) k v) Set.univ) ∧
    (∀ (k : ℕ) (e : G.Dart),
      (∀ a, a ∈ messageTable G (fun v => sensitive (costTable t D f v))
        (localTable (costTable t D f) k) hG e ↔
          a ∈ D5.S3.ConceptDynamics.Gluing.RunningIntersectionMessages.separatorMessages
            G (fun _ => O) (fun v => sensitive (costTable t D f v))
            (fun v => localFeasible (costTable t D f) k v) hG e) ∧
      (messageTable G (fun v => sensitive (costTable t D f v))
        (localTable (costTable t D f) k) hG e).card ≤
          Fintype.card O ^ Fintype.card
            ↥(sensitive (costTable t D f e.snd) ∩ sensitive (costTable t D f e.fst)) ∧
      Fintype.card
        ↥(sensitive (costTable t D f e.snd) ∩ sensitive (costTable t D f e.fst)) ≤
          separatorWidth G (fun v => sensitive (costTable t D f v))) := by
  classical
  let c := costTable t D f
  let S := fun v => sensitive (c v)
  have hRIc : RunningIntersection G S := by simpa only [S, c, cost_table_eq] using hRI
  have tables (k : ℕ) : (fun v => (↑(localTable c k v) : Set (S v → O))) =
      (fun v => localFeasible c k v) := by
    funext v
    ext a
    exact local_table_mem c k v a
  have joins (k : ℕ) :
      (rawJoin (fun _ => O) S (fun v => ↑(localTable c k v)) Set.univ).Nonempty ↔
        (sensitiveJoin c k).Nonempty := by
    rw [tables k]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨fun u => j ⟨u.val, ?_⟩, ?_⟩
      · obtain ⟨v, hv⟩ := u.property
        exact ⟨v, Set.mem_univ _, hv⟩
      · intro v
        exact hj v (Set.mem_univ _)
    · rintro ⟨j, hj⟩
      refine ⟨fun u => j ⟨u.val, ?_⟩, ?_⟩
      · obtain ⟨v, _, hv⟩ := u.property
        exact ⟨v, hv⟩
      · intro v _
        exact hj v
  refine ⟨cost_table_eq t D f, ?_, ?_, ?_⟩
  · intro k
    have spec := (solve_spec G S (localTable c k) hG hRIc r
      nodes hNodes vars hVars values hValues (baseOutput D hD f values hValues)).1
    change (solve G S (localTable c k) hG hRIc r nodes hNodes vars hVars values hValues
      (baseOutput D hD f values hValues)).isSome = true ↔ _
    rw [spec, joins k]
    change (sensitiveJoin (costTable t D f) k).Nonempty ↔ minimumPeak t D f ≤ k
    rw [cost_table_eq t D f]
    exact ((source_result t ht hall D hD f).2 k).symm
  · intro k j hj
    have sound := (solve_spec G S (localTable c k) hG hRIc r
      nodes hNodes vars hVars values hValues (baseOutput D hD f values hValues)).2.1 j hj
    rw [tables k] at sound
    exact sound
  · intro k e
    have spec := message_table_spec G S (localTable c k) hG e
    rw [tables k] at spec
    exact ⟨spec.1, spec.2,
      Finset.le_sup (f := fun e : G.Dart => Fintype.card ↥(S e.snd ∩ S e.fst))
        (Finset.mem_univ e)⟩

#print axioms cost_table_eq
#print axioms source_solver_spec

end D5.S3.Observer.Separation.ExecutableCapacityJoin
