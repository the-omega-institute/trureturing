/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact legal old-class valuations and the actual complete native row fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder

/-- All and only class names actually appearing in the retained row. -/
def labels : LiteralRow → Finset Nat
  | .of (.inl _) => ∅
  | .of (.inr n) => {n}
  | .mul l r => labels l ∪ labels r

abbrev Classes (C : LiteralRow) := {n : Nat // n ∈ labels C}

/-- Repeated occurrences use the same value; all different old classes remain unequal. -/
abbrev LegalValues (C : LiteralRow) := {v : Classes C → Source // Function.Injective v}

def extend (C : LiteralRow) (v : Classes C → Source) (n : Nat) : Source :=
  if h : n ∈ labels C then v ⟨n,h⟩ else .of true

private theorem labels_literal (P : CutSet) (root : Source) (a : Address) (t : Source) :
    labels (literalRow P root a t) =
      (reachedHoles P a t).toFinset.image (classOrdinal P root) := by
  induction t generalizing a with
  | of b => by_cases ha : a ∈ P <;> simp [literalRow, labels, reachedHoles, ha]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P <;> simp [literalRow, labels, reachedHoles, ha, ihl, ihr, Finset.image_union]

theorem labels_canonical (P : CutSet) (u : Source) :
    labels (canonicalRow P u) = (orderedHoles P u).toFinset.image (classOrdinal P u) := by
  rw [canonicalRow, labels_literal]
  simp [orderedHoles]

private theorem ordinal_mem (P : CutSet) (u : Source) (p : Address)
    (hp : p ∈ orderedHoles P u) : classOrdinal P u p ∈ labels (canonicalRow P u) := by
  rw [labels_canonical]
  exact Finset.mem_image.mpr ⟨p, by simpa using hp, rfl⟩

private theorem evaluate_congr (C : LiteralRow) (f g : Nat → Source)
    (same : ∀ n ∈ labels C, f n = g n) : evaluateRow f C = evaluateRow g C := by
  induction C with
  | of b => cases b with
    | inl b => rfl
    | inr n => exact same n (by simp [labels])
  | mul l r ihl ihr =>
      exact congrArg₂ FreeMagma.mul (ihl (fun n hn => same n (Finset.mem_union_left _ hn)))
        (ihr (fun n hn => same n (Finset.mem_union_right _ hn)))

theorem rowAt_evaluate (C : LiteralRow) (f : Nat → Source)
    (p : Address) (t : LiteralRow) (ht : rowAt p C = some t) :
    subtree p (evaluateRow f C) = some (evaluateRow f t) := by
  induction p generalizing C with
  | nil => simpa [rowAt, subtree] using congrArg (Option.map (evaluateRow f)) ht
  | cons b p ih =>
      cases C with
      | of c => simp [rowAt] at ht
      | mul l r => cases b <;> exact ih _ ht

private theorem filled_exterior (P : CutSet) (root : Source) (f : Nat → Source)
    (a : Address) (t : Source) :
    cutExterior P a (evaluateRow f (literalRow P root a t)) = cutExterior P a t := by
  induction t generalizing a with
  | of b =>
      by_cases ha : a ∈ P
      · simp only [literalRow, ha, ↓reduceIte, evaluateRow, FreeMagma.lift_of, Sum.elim_inr]
        cases f (classOrdinal P root a) <;> simp [cutExterior, ha]
      · simp [literalRow, ha, evaluateRow, cutExterior]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · simp only [literalRow, ha, ↓reduceIte, evaluateRow, FreeMagma.lift_of, Sum.elim_inr]
        cases f (classOrdinal P root a) <;> simp [cutExterior, ha]
      · simpa only [literalRow, ha, ↓reduceIte, evaluateRow, FreeMagma.mul_eq, map_mul,
          cutExterior] using congrArg₂ FreeMagma.mul (ihl _) (ihr _)

/-- Filling the complete old row preserves its concrete exterior and its full
partition exactly when all old class values stay distinct. -/
theorem legal_values_row (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (v : LegalValues (canonicalRow P u)) :
    canonicalRow P (evaluateRow (extend (canonicalRow P u) v.val) (canonicalRow P u)) =
      canonicalRow P u := by
  let C := canonicalRow P u
  let f := extend C v.val
  let w := evaluateRow f C
  have exterior : cutExterior P [] w = cutExterior P [] u := filled_exterior P u f [] u
  have ord : orderedHoles P w = orderedHoles P u := by
    unfold orderedHoles
    rw [← exteriorHoles_cut P [] w, ← exteriorHoles_cut P [] u, exterior]
  have value (p : Address) (hp : p ∈ orderedHoles P u) :
      subtree p w = some (v.val ⟨classOrdinal P u p, ordinal_mem P u p hp⟩) := by
    have mem := (orderedHoles_mem P hP u p).mp hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp mem.2
    have marker : rowAt p C = some (.of (.inr (classOrdinal P u p))) := by
      rw [canonicalRow_at_cut P hP u p mem.1, ht]; rfl
    have oc : classOrdinal P u p ∈ labels C := ordinal_mem P u p hp
    simpa [w, f, extend, oc, evaluateRow] using rowAt_evaluate C f p _ marker
  apply (canonicalRow_record_iff P hP w u).mpr
  apply Prod.ext exterior
  ext pq
  simp only [actualPartition, literalRecord, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    List.mem_toFinset, ord]
  constructor
  · rintro ⟨⟨hp,hq⟩, eq⟩
    refine ⟨⟨hp,hq⟩, ?_⟩
    rw [value _ hp, value _ hq, Option.some.injEq] at eq
    have cls := congrArg Subtype.val (v.property eq)
    exact (classOrdinal_eq_iff P u hp hq).mp cls
  · rintro ⟨⟨hp,hq⟩, eq⟩
    refine ⟨⟨hp,hq⟩, ?_⟩
    rw [value _ hp, value _ hq, Option.some.injEq]
    apply congrArg v.val
    apply Subtype.ext
    exact (classOrdinal_eq_iff P u hp hq).mpr eq

private theorem classValue_distinct (P : CutSet) (hP : CutPrefixFree P) (u : Source) :
    Function.Injective (fun b : Classes (canonicalRow P u) => classValue P u b.val) := by
  intro b c eq
  dsimp only at eq
  have hb : b.val ∈ (orderedHoles P u).toFinset.image (classOrdinal P u) := by
    simpa only [labels_canonical P u] using b.property
  obtain ⟨p,hp,ep⟩ := Finset.mem_image.mp hb
  have hc : c.val ∈ (orderedHoles P u).toFinset.image (classOrdinal P u) := by
    simpa only [labels_canonical P u] using c.property
  obtain ⟨q,hq,eqc⟩ := Finset.mem_image.mp hc
  have pp := (orderedHoles_mem P hP u p).mp (by simpa using hp)
  have pq := (orderedHoles_mem P hP u q).mp (by simpa using hq)
  obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp pp.2
  obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp pq.2
  rw [← ep, ← eqc, classValue_at P hP u p s pp.1 hs,
    classValue_at P hP u q t pq.1 ht] at eq
  apply Subtype.ext
  rw [← ep, ← eqc]
  exact (classOrdinal_eq_iff P u (by simpa using hp) (by simpa using hq)).mpr
    (by rw [hs, ht, eq])

/-- Entire actual source fiber; hidden sizes and values are unrestricted. -/
abbrev RowFiber (P : CutSet) (C : LiteralRow) := {u : Source // canonicalRow P u = C}

/-- The inverse reads mathematical class values from a source, not from a service port. -/
def recover (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow) (u : RowFiber P C) :
    LegalValues C := ⟨fun b => classValue P u.val b.val, by
  intro b c eq
  let b' : Classes (canonicalRow P u.val) := ⟨b.val, by simpa only [u.property] using b.property⟩
  let c' : Classes (canonicalRow P u.val) := ⟨c.val, by simpa only [u.property] using c.property⟩
  exact Subtype.ext (congrArg (fun z : Classes (canonicalRow P u.val) => z.val) (classValue_distinct P hP u.val (a₁ := b') (a₂ := c') eq))⟩

theorem recover_fill (P : CutSet) (hP : CutPrefixFree P) (C : LiteralRow)
    (u : RowFiber P C) : evaluateRow (extend C (recover P hP C u).val) C = u.val := by
  calc
    _ = evaluateRow (classValue P u.val) C := evaluate_congr C _ _ (by
      intro n hn; simp [extend, hn, recover])
    _ = evaluateRow (classValue P u.val) (canonicalRow P u.val) :=
      congrArg (evaluateRow (classValue P u.val)) u.property.symm
    _ = u.val := literalRow_evaluate P hP u.val [] u.val rfl

private theorem fill_injective (P : CutSet) (hP : CutPrefixFree P) (u : Source) :
    Function.Injective (fun v : LegalValues (canonicalRow P u) =>
      evaluateRow (extend (canonicalRow P u) v.val) (canonicalRow P u)) := by
  intro v w eq
  dsimp only at eq
  apply Subtype.ext
  funext b
  have hb : b.val ∈ (orderedHoles P u).toFinset.image (classOrdinal P u) := by
    simpa only [labels_canonical P u] using b.property
  obtain ⟨p,hp,ep⟩ := Finset.mem_image.mp hb
  have mem := (orderedHoles_mem P hP u p).mp (by simpa using hp)
  obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp mem.2
  have marker : rowAt p (canonicalRow P u) = some (.of (.inr b.val)) := by
    rw [canonicalRow_at_cut P hP u p mem.1, ht, ep]; rfl
  have a := rowAt_evaluate (canonicalRow P u) (extend _ v.val) p _ marker
  have c := rowAt_evaluate (canonicalRow P u) (extend _ w.val) p _ marker
  rw [eq] at a
  have res := a.symm.trans c
  simpa [evaluateRow, extend, b.property] using res

/-- Exact legal-valuation/source equivalence for the actual complete retained
row, with every cross-class disequality and absent-cut guard retained. -/
def rowFiberEquiv (P : CutSet) (hP : CutPrefixFree P) (u : Source) :
    LegalValues (canonicalRow P u) ≃ RowFiber P (canonicalRow P u) where
  toFun v := ⟨evaluateRow (extend _ v.val) (canonicalRow P u), legal_values_row P hP u v⟩
  invFun := recover P hP _
  left_inv v := fill_injective P hP u (recover_fill P hP _
    ⟨_, legal_values_row P hP u v⟩)
  right_inv v := Subtype.ext (recover_fill P hP _ v)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
