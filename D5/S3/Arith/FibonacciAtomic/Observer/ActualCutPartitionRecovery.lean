/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native literal cut rows with lexicographic reached-hole classes and a source-value bridge. -/

import D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation
import D5.S0.Computability.Coding.PrefixFreeCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)

/-- Finite cut sets are native address sets; the empty and root cuts are allowed. -/
abbrev CutSet := Finset Address

/-- Prefix freedom is the repository's exact finite-set specialization of the
canonical prefix-free supplier. -/
abbrev CutPrefixFree (P : CutSet) : Prop := IsPrefixFree (P : Set Address)

/-- The finite addresses at which the native tree is stopped by a cut.
The traversal is structural; the later `Finset.sort` gives the canonical
lexicographic order used for class names. -/
def reachedHoles (P : CutSet) : Address → Source → List Address
  | a, .of _ => if a ∈ P then [a] else []
  | a, .mul l r =>
      if a ∈ P then [a]
      else reachedHoles P (a ++ [false]) l ++ reachedHoles P (a ++ [true]) r

/-- Reached cuts in canonical lexicographic order, with address duplicates removed. -/
def orderedHoles (P : CutSet) (u : Source) : List Address :=
  (reachedHoles P [] u).toFinset.sort (fun a b : Address => a ≤ b)

/-- The first index at which a value occurs in a finite list.  An occurring
value receives the minimum reached-hole ordinal of its equality class. -/
def firstEqIndex {α : Type} [BEq α] (a : α) (xs : List α) : Nat :=
  xs.idxOf a

/-- Canonical class number for a reached native hole.  Only the ordered
address list and equality of native subtree options enter this number. -/
def classOrdinal (P : CutSet) (u : Source) (p : Address) : Nat :=
  firstEqIndex (subtree p u)
    ((orderedHoles P u).map (fun q => subtree q u))

theorem classOrdinal_eq_iff (P : CutSet) (u : Source)
    {p q : Address} (hp : p ∈ orderedHoles P u) (hq : q ∈ orderedHoles P u) :
    classOrdinal P u p = classOrdinal P u q ↔ subtree p u = subtree q u := by
  exact List.idxOf_inj (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- A literal row is a `FreeMagma (Bool ⊕ Nat)`: `inl b` is a concrete
leaf label and `inr n` is a canonical equality-class hole marker. -/
abbrev LiteralRow := FreeMagma (Bool ⊕ Nat)

def literalRow (P : CutSet) (root : Source) : Address → Source → LiteralRow
  | a, .of b => if a ∈ P then .of (.inr (classOrdinal P root a)) else .of (.inl b)
  | a, .mul l r =>
      if a ∈ P then .of (.inr (classOrdinal P root a))
      else .mul (literalRow P root (a ++ [false]) l)
        (literalRow P root (a ++ [true]) r)

def canonicalRow (P : CutSet) (u : Source) : LiteralRow := literalRow P u [] u

/-- Addresses recovered from the hole markers of a literal row. -/
def holeAddresses : Address → LiteralRow → List Address
  | a, .of (.inl _) => []
  | a, .of (.inr _) => [a]
  | a, .mul l r =>
      holeAddresses (a ++ [false]) l ++ holeAddresses (a ++ [true]) r

theorem literalRow_hole_support_aux (P : CutSet) (root : Source) (a : Address) (u : Source) :
    (holeAddresses a (literalRow P root a u)).toFinset =
      (reachedHoles P a u).toFinset := by
  induction u generalizing root a with
  | of b =>
      by_cases ha : a ∈ P <;> simp [literalRow, holeAddresses, reachedHoles, ha]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · simp [literalRow, holeAddresses, reachedHoles, ha]
      · simp [literalRow, holeAddresses, reachedHoles, ha, ihl, ihr]

theorem literalRow_hole_support (P : CutSet) (u : Source) :
    (holeAddresses [] (canonicalRow P u)).toFinset =
      (reachedHoles P [] u).toFinset := by
  exact literalRow_hole_support_aux P u [] u

/-- Native finite navigation of the retained expression; no source is an input. -/
def rowAt : Address → LiteralRow → Option LiteralRow
  | [], t => some t
  | _ :: _, .of _ => none
  | false :: r, .mul l _ => rowAt r l
  | true :: r, .mul _ t => rowAt r t

/-- Extract an actually retained hole label. -/
def holeLabel (p : Address) (C : LiteralRow) : Option Nat :=
  match rowAt p C with
  | some (.of (.inr n)) => some n
  | _ => none

theorem literalRow_at (P : CutSet) (root : Source) (a r : Address)
    (u : Source)
    (avoid : ∀ s : Address, s.IsPrefix r → s ≠ r → a ++ s ∉ P) :
    rowAt r (literalRow P root a u) =
      (subtree r u).map (literalRow P root (a ++ r)) := by
  induction r generalizing a u with
  | nil => simp [rowAt, subtree]
  | cons d r ih =>
      have ha : a ∉ P := by
        simpa using avoid [] (List.nil_prefix) (by simp)
      have down : ∀ s : Address, s.IsPrefix r → s ≠ r → (a ++ [d]) ++ s ∉ P := by
        intro s hs hne
        have hp : (d :: s).IsPrefix (d :: r) := by simpa using hs
        have hn : d :: s ≠ d :: r := by simpa using hne
        simpa [List.append_assoc] using avoid (d :: s) hp hn
      cases u with
      | of b => simp [literalRow, ha, rowAt, subtree]
      | mul l t =>
          cases d <;> simpa [literalRow, ha, rowAt, subtree, List.append_assoc]
            using ih (a ++ [_]) _ down

private theorem prefixFree_avoid (P : CutSet) (hP : CutPrefixFree P)
    (p : Address) (hp : p ∈ P) :
    ∀ s : Address, s.IsPrefix p → s ≠ p → s ∉ P := by
  intro s hs hne hm
  exact hne (hP hm hp hs)

/-- At a public cut the term itself contains precisely its reached class marker. -/
theorem canonicalRow_at_cut (P : CutSet) (hP : CutPrefixFree P)
    (u : Source) (p : Address) (hp : p ∈ P) :
    rowAt p (canonicalRow P u) =
      (subtree p u).map (fun _ => .of (.inr (classOrdinal P u p))) := by
  rw [canonicalRow, literalRow_at P u [] p u (by
    simpa using prefixFree_avoid P hP p hp)]
  cases h : subtree p u with
  | none => rfl
  | some t => cases t <;> simp [literalRow, hp]

private theorem reachedHoles_mem (P : CutSet) (a : Address) (u : Source) (p : Address) :
    p ∈ reachedHoles P a u → p ∈ P ∧ a.IsPrefix p := by
  induction u generalizing a with
  | of b =>
      by_cases ha : a ∈ P
      · simpa [reachedHoles, ha] using (fun h : p = a =>
          ⟨h ▸ ha, h ▸ List.prefix_rfl⟩)
      · simp [reachedHoles, ha]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · intro h
        have he : p = a := by simpa [reachedHoles, ha] using h
        subst p
        exact ⟨ha, List.prefix_rfl⟩
      · intro h
        rcases (show p ∈ reachedHoles P (a ++ [false]) l ∨
            p ∈ reachedHoles P (a ++ [true]) r by
            simpa [reachedHoles, ha] using h) with h | h
        · obtain ⟨hp, hab⟩ := ihl (a ++ [false]) h
          exact ⟨hp, (List.prefix_append _ _).trans hab⟩
        · obtain ⟨hp, hab⟩ := ihr (a ++ [true]) h
          exact ⟨hp, (List.prefix_append _ _).trans hab⟩

private theorem reachedHoles_subtree (P : CutSet) (a r : Address) (u : Source)
    (avoid : ∀ s : Address, s.IsPrefix r → s ≠ r → a ++ s ∉ P) :
    a ++ r ∈ reachedHoles P a u ↔ a ++ r ∈ P ∧ (subtree r u).isSome := by
  induction r generalizing a u with
  | nil =>
      cases u with
      | of b => by_cases ha : a ∈ P <;> simp [reachedHoles, ha, subtree]
      | mul l t =>
          by_cases ha : a ∈ P
          · simp [reachedHoles, ha, subtree]
          · have absent : a ∉ reachedHoles P a (.mul l t) := by
              intro h
              exact ha (reachedHoles_mem P a (.mul l t) a h).1
            simpa [subtree, ha] using absent
  | cons d r ih =>
      have ha : a ∉ P := by simpa using avoid [] (List.nil_prefix) (by simp)
      have down : ∀ s : Address, s.IsPrefix r → s ≠ r → (a ++ [d]) ++ s ∉ P := by
        intro s hs hne
        simpa [List.append_assoc] using
          avoid (d :: s) (by simpa using hs) (by simpa using hne)
      cases u with
      | of b => simp [reachedHoles, ha, subtree]
      | mul l t =>
          have leftNe : ¬ (a ++ [!d]).IsPrefix (a ++ d :: r) := by
            simp
          have outside : a ++ d :: r ∉ reachedHoles P (a ++ [!d]) (if d then l else t) := by
            intro h
            exact leftNe (reachedHoles_mem P _ _ _ h).2
          cases d with
          | false =>
              simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at outside
              simpa [reachedHoles, ha, subtree, List.append_assoc, outside]
                using ih (a ++ [false]) l down
          | true =>
              simp only [Bool.not_true, ↓reduceIte] at outside
              simpa [reachedHoles, ha, subtree, List.append_assoc, outside]
                using ih (a ++ [true]) t down

/-- The reached holes extracted from the retained term are exactly P ∩ Pos(u). -/
theorem canonicalRow_reached (P : CutSet) (hP : CutPrefixFree P)
    (u : Source) (p : Address) :
    p ∈ holeAddresses [] (canonicalRow P u) ↔ p ∈ P ∧ (subtree p u).isSome := by
  have support := literalRow_hole_support P u
  have same : (p ∈ holeAddresses [] (canonicalRow P u)) ↔ p ∈ reachedHoles P [] u := by
    simpa using Finset.ext_iff.mp support p
  rw [same]
  by_cases hp : p ∈ P
  · simpa using reachedHoles_subtree P [] p u (by
      simpa using prefixFree_avoid P hP p hp)
  · exact ⟨fun h => False.elim (hp (reachedHoles_mem P [] u p h).1), by simp [hp]⟩

theorem orderedHoles_mem (P : CutSet) (hP : CutPrefixFree P)
    (u : Source) (p : Address) :
    p ∈ orderedHoles P u ↔ p ∈ P ∧ (subtree p u).isSome := by
  simpa [orderedHoles, ← literalRow_hole_support P u] using canonicalRow_reached P hP u p

/-- Equality and disequality of labels read from the term are the complete
actual partition, rather than extra source-indexed packaging. -/
theorem canonicalRow_partition (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (p q : Address) (hp : p ∈ P) (hq : q ∈ P)
    (pp : (subtree p u).isSome) (pq : (subtree q u).isSome) :
    (holeLabel p (canonicalRow P u) = holeLabel q (canonicalRow P u) ↔
      subtree p u = subtree q u) ∧
    (holeLabel p (canonicalRow P u) ≠ holeLabel q (canonicalRow P u) ↔
      subtree p u ≠ subtree q u) := by
  have readp : holeLabel p (canonicalRow P u) = some (classOrdinal P u p) := by
    simp only [holeLabel, canonicalRow_at_cut P hP u p hp]
    cases h : subtree p u <;> simp_all
  have readq : holeLabel q (canonicalRow P u) = some (classOrdinal P u q) := by
    simp only [holeLabel, canonicalRow_at_cut P hP u q hq]
    cases h : subtree q u <;> simp_all
  have cls := classOrdinal_eq_iff P u ((orderedHoles_mem P hP u p).mpr ⟨hp, pp⟩)
    ((orderedHoles_mem P hP u q).mpr ⟨hq, pq⟩)
  simp only [readp, readq, Option.some.injEq, cls, ne_eq, iff_self, and_self]

/-- Every absent public cut retains a concrete strict-prefix leaf guard. -/
theorem canonicalRow_absent_guard (P : CutSet) (hP : CutPrefixFree P)
    (u : Source) (p : Address) (hp : p ∈ P) (missing : subtree p u = none) :
    ∃ a : Address, ∃ b : Bool, a.IsPrefix p ∧ a ≠ p ∧
      rowAt a (canonicalRow P u) = some (.of (.inl b)) := by
  obtain ⟨_, _, _, _, _, _, _, absence, _⟩ :=
    D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry
  obtain ⟨a, b, r, leaf, rfl, nonempty⟩ := (absence u p).mp missing
  have strict : a ≠ a ++ r := by
    intro h
    have : r = [] := List.append_cancel_left (show a ++ r = a ++ [] by simpa using h.symm)
    exact nonempty this
  have avoid : ∀ s : Address, s.IsPrefix a → s ≠ a → s ∉ P := by
    intro s hs _ hmem
    have eq := hP hmem hp (hs.trans (List.prefix_append _ _))
    have len : (a ++ r).length ≤ a.length := (eq.symm ▸ hs).length_le
    have rl : r.length = 0 := by simpa using len
    exact nonempty (List.length_eq_zero_iff.mp rl)
  have ha : a ∉ P := by
    intro hmem
    exact strict (hP hmem hp (List.prefix_append _ _))
  refine ⟨a, b, List.prefix_append _ _, strict, ?_⟩
  rw [canonicalRow, literalRow_at P u [] a u (by simpa using avoid), leaf]
  simp [literalRow, ha]

/-- A proof valuation of old classes. It is never an input to the decoder. -/
def classValue (P : CutSet) (u : Source) (n : Nat) : Source :=
  (((orderedHoles P u).map (fun p => subtree p u))[n]?.join).getD (.of true)

/-- Substitution is used to justify expression equality, without assuming it is injective. -/
def evaluateRow (values : Nat → Source) : LiteralRow → Source :=
  FreeMagma.lift (Sum.elim FreeMagma.of values)

theorem classValue_at (P : CutSet) (hP : CutPrefixFree P) (u : Source)
    (p : Address) (t : Source) (hp : p ∈ P) (ht : subtree p u = some t) :
    classValue P u (classOrdinal P u p) = t := by
  have mem : p ∈ orderedHoles P u :=
    (orderedHoles_mem P hP u p).mpr ⟨hp, by simp [ht]⟩
  have val : some t ∈ (orderedHoles P u).map (fun p => subtree p u) :=
    List.mem_map.mpr ⟨p, mem, ht⟩
  unfold classValue classOrdinal firstEqIndex
  rw [ht, List.getElem?_idxOf val]
  rfl

theorem literalRow_evaluate (P : CutSet) (hP : CutPrefixFree P)
    (root : Source) (a : Address) (u : Source) (hu : subtree a root = some u) :
    evaluateRow (classValue P root) (literalRow P root a u) = u := by
  induction u generalizing a with
  | of b =>
      by_cases ha : a ∈ P
      · simpa [literalRow, ha, evaluateRow, FreeMagma.lift_of] using
          classValue_at P hP root a (.of b) ha hu
      · simp [literalRow, ha, evaluateRow, FreeMagma.lift_of]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · simpa only [literalRow, ha, ↓reduceIte, evaluateRow, FreeMagma.lift_of,
          Sum.elim_inr] using classValue_at P hP root a (.mul l r) ha hu
      · have app := D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hl : subtree (a ++ [false]) root = some l := by rw [app, hu]; rfl
        have hr : subtree (a ++ [true]) root = some r := by rw [app, hu]; rfl
        simpa only [literalRow, ha, ↓reduceIte, evaluateRow, FreeMagma.mul_eq, map_mul] using
          congrArg₂ FreeMagma.mul (ihl _ hl) (ihr _ hr)

/-- The suffix left after a fixed native prefix. -/
def cutSection (P : CutSet) (q : Address) : CutSet :=
  (P.filter (fun p => q.IsPrefix p)).image (List.drop q.length)

theorem mem_cutSection_iff (P : CutSet) (q s : Address) :
    s ∈ cutSection P q ↔ q ++ s ∈ P ∧ q.IsPrefix (q ++ s) := by
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨p, hp, hs_eq⟩
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hpq : q.IsPrefix p := (Finset.mem_filter.mp hp).2
    have hpq' : q ++ List.drop q.length p = p :=
      List.prefix_iff_eq_append.mp hpq
    refine ⟨?_, List.prefix_append _ _⟩
    rw [← hs_eq, hpq']
    exact hpP
  · intro hs
    have hprefix : q.IsPrefix (q ++ s) := List.prefix_append _ _
    have hmem : q ++ s ∈ P.filter (fun p => q.IsPrefix p) :=
      Finset.mem_filter.mpr ⟨hs.1, hprefix⟩
    apply Finset.mem_image.mpr
    refine ⟨q ++ s, hmem, ?_⟩
    exact List.drop_left

theorem cutSection_mem_append (P : CutSet) (q s : Address) (hs : s ∈ cutSection P q) :
    q ++ s ∈ P := by
  exact (mem_cutSection_iff P q s).mp hs |>.1

/-- The exact common-suffix condition of Theorem 64.2, expressed on native
finite cuts.  This is the finite combinatorial predicate consumed by the
future native kernel theorem. -/
def HasCommonSuffix (P Q : CutSet) : Prop :=
  ∃ S : CutSet, CutPrefixFree S ∧
    ∀ p : Address, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s

theorem commonSuffix_empty_right (P : CutSet) :
    HasCommonSuffix P ∅ ↔ P = ∅ := by
  constructor
  · rintro ⟨S, hS, hPQ⟩
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, s, hs, he⟩ := (hPQ p).mp hp
      simp at hq
    · intro hp
      simp at hp
  · intro hP
    subst P
    refine ⟨∅, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro p
      simp

theorem commonSuffix_root_right (P : CutSet) (hP : CutPrefixFree P) :
    HasCommonSuffix P {[]} := by
  refine ⟨P, hP, ?_⟩
  intro p
  constructor
  · intro hp
    refine ⟨[], by simp, p, hp, ?_⟩
    simp
  · rintro ⟨q, hq, s, hs, rfl⟩
    have hq' : q = [] := by simpa using hq
    subst q
    simpa using hs

theorem cutSection_prefixFree (P : CutSet) (hP : CutPrefixFree P) (q : Address) :
    CutPrefixFree (cutSection P q) := by
  intro s hs t ht hst
  have hsP : q ++ s ∈ P := cutSection_mem_append P q s hs
  have htP : q ++ t ∈ P := cutSection_mem_append P q t ht
  have hqst : (q ++ s).IsPrefix (q ++ t) := by
    rcases hst with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [List.append_assoc] using congrArg (fun z => q ++ z) hr
  have heq := hP hsP htP hqst
  exact List.append_cancel_left heq

/-- A finite prefix trie. The unused branches are concrete alpha leaves. -/
def prefixTrie : Nat → CutSet → Address → (Address → Source) → Source
  | 0, P, a, f => if a ∈ P then f a else .of true
  | n + 1, P, a, f =>
      if a ∈ P then f a
      else if ∃ p ∈ P, a.IsPrefix p then
        .mul (prefixTrie n P (a ++ [false]) f) (prefixTrie n P (a ++ [true]) f)
      else .of true

theorem prefixTrie_at (n : Nat) (P : CutSet) (a r : Address)
    (f : Address → Source) (hp : a ++ r ∈ P) (bound : r.length ≤ n)
    (avoid : ∀ s : Address, s.IsPrefix r → s ≠ r → a ++ s ∉ P) :
    subtree r (prefixTrie n P a f) = some (f (a ++ r)) := by
  induction r generalizing n a with
  | nil =>
      have ha : a ∈ P := by simpa using hp
      cases n <;> simp [prefixTrie, ha, subtree]
  | cons d r ih =>
      cases n with
      | zero => simp at bound
      | succ n =>
        have ha : a ∉ P := by simpa using avoid [] List.nil_prefix (by simp)
        have ext : ∃ p ∈ P, a.IsPrefix p := ⟨a ++ d :: r, hp, List.prefix_append _ _⟩
        have down : ∀ s : Address, s.IsPrefix r → s ≠ r → (a ++ [d]) ++ s ∉ P := by
          intro s hs hne
          simpa [List.append_assoc] using avoid (d :: s) (by simpa using hs) (by simpa using hne)
        cases d <;> simpa [prefixTrie, ha, ext, subtree, List.append_assoc] using
          ih n (a ++ [_]) (by simpa [List.append_assoc] using hp) (by simpa using bound) down

/-- Public depth bound is computed from the finite cut set. -/
def cutDepth (P : CutSet) : Nat := P.sup List.length

private theorem prefixTrie_cut (P : CutSet) (hP : CutPrefixFree P)
    (f : Address → Source) (p : Address) (hp : p ∈ P) :
    subtree p (prefixTrie (cutDepth P) P [] f) = some (f p) := by
  simpa using prefixTrie_at (cutDepth P) P [] p f (by simpa using hp)
    (Finset.le_sup (f := List.length) hp) (by simpa using prefixFree_avoid P hP p hp)

private theorem uniform_ordered (P : CutSet) (hP : CutPrefixFree P) (t : Source) :
    orderedHoles P (prefixTrie (cutDepth P) P [] (fun _ => t)) =
      P.sort (fun a b : Address => a ≤ b) := by
  unfold orderedHoles
  congr 1
  ext p
  have reached := canonicalRow_reached P hP
    (prefixTrie (cutDepth P) P [] (fun _ => t)) p
  have support := Finset.ext_iff.mp (literalRow_hole_support P
    (prefixTrie (cutDepth P) P [] (fun _ => t))) p
  simp only [List.mem_toFinset] at support ⊢
  rw [support] at reached
  constructor
  · intro h
    exact (reached.mp h).1
  · intro hp
    exact reached.mpr ⟨hp, by rw [prefixTrie_cut P hP _ p hp]; rfl⟩

private theorem uniform_class (P : CutSet) (hP : CutPrefixFree P) (t : Source)
    (p : Address) (hp : p ∈ P) :
    classOrdinal P (prefixTrie (cutDepth P) P [] (fun _ => t)) p = 0 := by
  unfold classOrdinal firstEqIndex
  rw [uniform_ordered P hP t, prefixTrie_cut P hP _ p hp]
  have same : ∀ q ∈ P.sort (fun a b : Address => a ≤ b),
      subtree q (prefixTrie (cutDepth P) P [] (fun _ => t)) = some t := by
    intro q hq
    exact prefixTrie_cut P hP _ q (by simpa using hq)
  have nonempty : P.sort (fun a b : Address => a ≤ b) ≠ [] := by
    intro h
    have : p ∈ P.sort (fun a b : Address => a ≤ b) := by simpa using hp
    simpa [h] using this
  cases hs : P.sort (fun a b : Address => a ≤ b) with
  | nil => exact False.elim (nonempty hs)
  | cons q qs =>
      have sq := same q (by simp [hs])
      simp [List.map_cons, sq, List.idxOf_cons]

private theorem uniform_row_aux (P : CutSet) (hP : CutPrefixFree P)
    (t z : Source) (n : Nat) (a : Address) :
    literalRow P (prefixTrie (cutDepth P) P [] (fun _ => t)) a
      (prefixTrie n P a (fun _ => t)) =
    literalRow P (prefixTrie (cutDepth P) P [] (fun _ => z)) a
      (prefixTrie n P a (fun _ => z)) := by
  induction n generalizing a with
  | zero =>
      by_cases ha : a ∈ P
      · have lt := uniform_class P hP t a ha
        have lz := uniform_class P hP z a ha
        have stopped (root v : Source) : literalRow P root a v = .of (.inr (classOrdinal P root a)) := by
          cases v <;> simp only [literalRow, ha, ↓reduceIte]
        simp only [prefixTrie, ha, ↓reduceIte, stopped, lt, lz]
      · simp [prefixTrie, literalRow, ha]
  | succ n ih =>
      by_cases ha : a ∈ P
      · have lt := uniform_class P hP t a ha
        have lz := uniform_class P hP z a ha
        have stopped (root v : Source) : literalRow P root a v = .of (.inr (classOrdinal P root a)) := by
          cases v <;> simp only [literalRow, ha, ↓reduceIte]
        simp only [prefixTrie, ha, ↓reduceIte, stopped, lt, lz]
      · by_cases he : ∃ p ∈ P, a.IsPrefix p
        · simp [prefixTrie, literalRow, ha, he, ih]
        · simp [prefixTrie, literalRow, ha, he]

/-- Filling all reached trie holes by one value retains the same complete row. -/
theorem uniform_trie_row (P : CutSet) (hP : CutPrefixFree P) (t z : Source) :
    canonicalRow P (prefixTrie (cutDepth P) P [] (fun _ => t)) =
      canonicalRow P (prefixTrie (cutDepth P) P [] (fun _ => z)) := by
  exact uniform_row_aux P hP t z (cutDepth P) []

/-- Concrete coverage failure: all old holes change together, while the
uncovered leaf remains a visible Boolean leaf in the new exterior. -/
theorem coverage_failure_pair (P Q : CutSet) (hP : CutPrefixFree P)
    (p : Address) (hp : p ∈ P) (uncovered : ∀ q ∈ Q, ¬ q.IsPrefix p) :
    let u := prefixTrie (cutDepth P) P [] (fun _ => .of true)
    let v := prefixTrie (cutDepth P) P [] (fun _ => .of false)
    canonicalRow P u = canonicalRow P v ∧ canonicalRow Q u ≠ canonicalRow Q v := by
  dsimp
  refine ⟨uniform_trie_row P hP _ _, ?_⟩
  intro heq
  have reads := congrArg (rowAt p) heq
  have avoid : ∀ s : Address, s.IsPrefix p → s ≠ p → s ∉ Q := by
    intro s hs _ hm
    exact uncovered s hm hs
  have pq : p ∉ Q := by intro hm; exact uncovered p hm List.prefix_rfl
  simp only [canonicalRow, literalRow_at Q _ [] p _ (by simpa using avoid),
    prefixTrie_cut P hP _ p hp, List.nil_append, Option.map_some,
    literalRow, pq, ↓reduceIte] at reads
  cases reads

theorem idxOf_map_relation {A B I : Type} [BEq A] [LawfulBEq A]
    [BEq B] [LawfulBEq B] (L : List I) (f : I → A) (g : I → B) (p : I)
    (rel : ∀ q ∈ L, f q = f p ↔ g q = g p) :
    (L.map f).idxOf (f p) = (L.map g).idxOf (g p) := by
  induction L with
  | nil => rfl
  | cons q L ih =>
      have head := rel q (by simp)
      have tail : ∀ r ∈ L, f r = f p ↔ g r = g p := by
        intro r hr
        exact rel r (by simp [hr])
      simp only [List.map_cons, List.idxOf_cons]
      by_cases h : f q = f p
      · have h' := head.mp h
        simp [h, h']
      · have h' : g q ≠ g p := fun hg => h (head.mpr hg)
        simp only [beq_false_of_ne h, beq_false_of_ne h', Bool.false_eq_true, cond_false, ih tail]


/-- The native one-hole path context, with beta in every unused sibling. -/
def markerContext : Address → D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext
  | [] => .hole
  | false :: s => .left (markerContext s) (.of false)
  | true :: s => .right (.of false) (markerContext s)

private theorem marker_at (s : Address) (t : Source) :
    subtree s ((markerContext s).plug t) = some t := by
  induction s with
  | nil => rfl
  | cons d s ih => cases d <;> simp [markerContext,
      D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug, subtree, ih]

/-- Alpha occurs as a complete subtree at precisely the selected suffix. -/
private theorem marker_alpha_unique (s r : Address) :
    subtree r ((markerContext s).plug (.of true)) = some (.of true) ↔ r = s := by
  induction s generalizing r with
  | nil => cases r <;> simp [markerContext,
      D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug, subtree]
  | cons d s ih =>
      cases r with
      | nil => cases d <;> simp [markerContext,
          D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug, subtree]
      | cons e r =>
          cases d <;> cases e
          · simpa only [markerContext,
              D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
              subtree, List.cons.injEq, true_and] using ih r
          · cases r <;> simp [markerContext,
              D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug, subtree] <;> try { intro h; injection h with hb; cases hb }
          · cases r <;> simp [markerContext,
              D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug, subtree] <;> try { intro h; injection h with hb; cases hb }
          · simpa only [markerContext,
              D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
              subtree, List.cons.injEq, true_and] using ih r

private theorem marker_length (s : Address) (t : Source) :
    ((markerContext s).plug t).length = s.length + t.length := by
  induction s with
  | nil => simp [markerContext,
      D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug]
  | cons d s ih => cases d <;> simp [markerContext,
      D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
      FreeMagma.length, ih] <;> omega

/-- Recovery is equality-kernel inclusion on the common source-free row codomain. -/
def Recovers (P Q : CutSet) : Prop :=
  ∀ u v : Source, canonicalRow P u = canonicalRow P v → canonicalRow Q u = canonicalRow Q v

/-- Every recovering cut covers every old hole. -/
theorem recovery_covers (P Q : CutSet) (hP : CutPrefixFree P) (recover : Recovers P Q) :
    ∀ p ∈ P, ∃ q ∈ Q, q.IsPrefix p := by
  intro p hp
  by_contra h
  have uncovered : ∀ q ∈ Q, ¬ q.IsPrefix p := by simpa using h
  have pair := coverage_failure_pair P Q hP p hp uncovered
  exact pair.2 (recover _ _ pair.1)

/-- Option values are changed only for the one distinguished old class. -/
def changeClass (z : Source) (v : Option Source) : Option Source :=
  if v = some (.of true) then some z else v

private theorem marker_incomparable (s r : Address) (a b : Source)
    (noLeft : ¬ s.IsPrefix r) (noRight : ¬ r.IsPrefix s) :
    subtree r ((markerContext s).plug a) = subtree r ((markerContext s).plug b) := by
  induction s generalizing r with
  | nil => exact False.elim (noLeft List.nil_prefix)
  | cons d s ih =>
      cases r with
      | nil => exact False.elim (noRight List.nil_prefix)
      | cons e r =>
          cases d <;> cases e
          · exact ih r (by simpa using noLeft) (by simpa using noRight)
          · rfl
          · rfl
          · exact ih r (by simpa using noLeft) (by simpa using noRight)

private theorem marker_fresh (s r : Address) :
    subtree r ((markerContext s).plug (.of true)) ≠
      some (.mul ((markerContext s).plug (.of true)) (.of false)) := by
  intro eq
  have bound := D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.subtree_leaf_count
    ((markerContext s).plug (.of true)) r _ eq
  simp only [FreeMagma.length] at bound
  omega

private theorem trie_below (Q : CutSet) (hQ : CutPrefixFree Q)
    (f : Address → Source) (q r : Address) (hq : q ∈ Q) :
    subtree (q ++ r) (prefixTrie (cutDepth Q) Q [] f) = subtree r (f q) := by
  have app := D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [app, prefixTrie_cut Q hQ f q hq]
  rfl

private theorem changed_trie_values (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (cover : ∀ p ∈ P, ∃ q ∈ Q, q.IsPrefix p) (s p : Address) (hp : p ∈ P) :
    let t := (markerContext s).plug (.of true)
    let z : Source := .mul t (.of false)
    let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
    let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
    subtree p v = changeClass z (subtree p u) := by
  dsimp
  obtain ⟨q, hq, r, rfl⟩ : ∃ q ∈ Q, ∃ r, p = q ++ r := by
    obtain ⟨q, hq, pre⟩ := cover p hp
    obtain ⟨r, eq⟩ := pre
    exact ⟨q, hq, r, eq.symm⟩
  rw [trie_below Q hQ _ q r hq, trie_below Q hQ _ q r hq]
  by_cases selected : q ++ s ∈ P
  · rw [if_pos selected]
    by_cases rs : r = s
    · subst r
      simp only [marker_at, changeClass, ↓reduceIte]
    · have noneAlpha : subtree r ((markerContext s).plug (.of true)) ≠ some (.of true) := by
        exact fun h => rs ((marker_alpha_unique s r).mp h)
      have nr : ¬ r.IsPrefix s := by
        intro h
        have pre : (q ++ r).IsPrefix (q ++ s) := by
          obtain ⟨a, eq⟩ := h
          exact ⟨a, by simpa [List.append_assoc] using congrArg (q ++ ·) eq⟩
        exact rs (List.append_cancel_left (hP hp selected pre))
      have ns : ¬ s.IsPrefix r := by
        intro h
        have pre : (q ++ s).IsPrefix (q ++ r) := by
          obtain ⟨a, eq⟩ := h
          exact ⟨a, by simpa [List.append_assoc] using congrArg (q ++ ·) eq⟩
        exact rs (List.append_cancel_left (hP selected hp pre)).symm
      rw [changeClass, if_neg noneAlpha]
      exact marker_incomparable s r _ _ ns nr
  · rw [if_neg selected]
    have rs : r ≠ s := by intro eq; exact selected (eq ▸ hp)
    rw [changeClass, if_neg (fun h => rs ((marker_alpha_unique s r).mp h))]

private theorem changeClass_kernel (s : Address) (a b : Option Source)
    (fa : a ≠ some (.mul ((markerContext s).plug (.of true)) (.of false)))
    (fb : b ≠ some (.mul ((markerContext s).plug (.of true)) (.of false))) :
    changeClass (.mul ((markerContext s).plug (.of true)) (.of false)) a =
      changeClass (.mul ((markerContext s).plug (.of true)) (.of false)) b ↔ a = b := by
  by_cases ha : a = some (.of true) <;> by_cases hb : b = some (.of true)
  · subst a; subst b; simp
  · subst a
    simp only [changeClass, hb, ↓reduceIte]
    constructor
    · intro h; exact (fb h.symm).elim
    · intro h; exact (hb h.symm).elim
  · subst b
    simp only [changeClass, ha, ↓reduceIte]
    constructor
    · intro h; exact (fa h).elim
    · intro h; exact h.elim
  · simp [changeClass, ha, hb]

private theorem marker_reached_change (P : CutSet) (hP : CutPrefixFree P)
    (a s : Address) (x y : Source) (cut : a ++ s ∈ P) :
    reachedHoles P a ((markerContext s).plug x) = reachedHoles P a ((markerContext s).plug y) := by
  induction s generalizing a with
  | nil =>
      have ha : a ∈ P := by simpa using cut
      cases x <;> cases y <;> simp only [markerContext,
        D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
        reachedHoles, ha, ↓reduceIte]
  | cons d s ih =>
      have ha : a ∉ P := by
        intro mem
        have eq := hP mem cut (List.prefix_append a (d :: s))
        have len := congrArg List.length eq
        simp only [List.length_append, List.length_cons] at len
        omega
      cases d <;> simp only [markerContext,
        D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
        reachedHoles, ha, ↓reduceIte]
      · rw [ih (a ++ [false]) (by simpa [List.append_assoc] using cut)]
      · rw [ih (a ++ [true]) (by simpa [List.append_assoc] using cut)]

private theorem changed_trie_reached (P Q : CutSet) (hP : CutPrefixFree P)
    (s : Address) :
    let t := (markerContext s).plug (.of true)
    let z : Source := .mul t (.of false)
    reachedHoles P [] (prefixTrie (cutDepth Q) Q [] (fun _ => t)) =
      reachedHoles P [] (prefixTrie (cutDepth Q) Q []
        (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)) := by
  dsimp
  have aux (n : Nat) (a : Address) :
      reachedHoles P a (prefixTrie n Q a (fun _ => (markerContext s).plug (.of true))) =
      reachedHoles P a (prefixTrie n Q a (fun q => if q ++ s ∈ P then
        (markerContext s).plug (.mul ((markerContext s).plug (.of true)) (.of false))
        else (markerContext s).plug (.of true))) := by
    induction n generalizing a with
    | zero =>
        by_cases qa : a ∈ Q
        · by_cases sel : a ++ s ∈ P
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using marker_reached_change P hP a s _ _ sel
          · simp only [prefixTrie, qa, sel, ↓reduceIte]
        · simp only [prefixTrie, qa, ↓reduceIte]
    | succ n ih =>
        by_cases qa : a ∈ Q
        · by_cases sel : a ++ s ∈ P
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using marker_reached_change P hP a s _ _ sel
          · simp only [prefixTrie, qa, sel, ↓reduceIte]
        · by_cases ext : ∃ q ∈ Q, a.IsPrefix q
          · by_cases pa : a ∈ P
            · simp only [prefixTrie, qa, ext, reachedHoles, pa, ↓reduceIte]
            · simp only [prefixTrie, qa, ext, reachedHoles, pa, ↓reduceIte, ih]
          · simp only [prefixTrie, qa, ext, ↓reduceIte]
  exact aux (cutDepth Q) []

private theorem changed_trie_ordinals (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (cover : ∀ p ∈ P, ∃ q ∈ Q, q.IsPrefix p) (s p : Address) (hp : p ∈ P) :
    let t := (markerContext s).plug (.of true)
    let z : Source := .mul t (.of false)
    let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
    let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
    classOrdinal P u p = classOrdinal P v p := by
  dsimp
  let t := (markerContext s).plug (.of true)
  let z : Source := .mul t (.of false)
  let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
  let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
  change classOrdinal P u p = classOrdinal P v p
  have ord : orderedHoles P u = orderedHoles P v := by
    unfold orderedHoles
    rw [changed_trie_reached P Q hP s]
  have fresh (p : Address) (hp : p ∈ P) : subtree p u ≠ some z := by
    obtain ⟨q, hq, pre⟩ := cover p hp
    obtain ⟨r, eq⟩ := pre
    subst p
    rw [trie_below Q hQ _ q r hq]
    exact marker_fresh s r
  unfold classOrdinal firstEqIndex
  rw [← ord]
  apply idxOf_map_relation (orderedHoles P u) (fun r => subtree r u) (fun r => subtree r v) p
  intro r hr
  have rp := ((orderedHoles_mem P hP u r).mp hr).1
  rw [changed_trie_values P Q hP hQ cover s p hp,
    changed_trie_values P Q hP hQ cover s r rp]
  exact (changeClass_kernel s _ _ (fresh r rp) (fresh p hp)).symm

private theorem marker_row_change (P : CutSet) (hP : CutPrefixFree P) (u v : Source)
    (ord : ∀ p ∈ P, classOrdinal P u p = classOrdinal P v p)
    (a s : Address) (x y : Source) (cut : a ++ s ∈ P) :
    literalRow P u a ((markerContext s).plug x) = literalRow P v a ((markerContext s).plug y) := by
  induction s generalizing a with
  | nil =>
      have ha : a ∈ P := by simpa using cut
      cases x <;> cases y <;> simp only [markerContext,
        D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
        literalRow, ha, ↓reduceIte, ord a ha]
  | cons d s ih =>
      have ha : a ∉ P := by
        intro mem
        have eq := hP mem cut (List.prefix_append a (d :: s))
        have len := congrArg List.length eq
        simp only [List.length_append, List.length_cons] at len
        omega
      have beta (a : Address) : literalRow P u a (.of false) = literalRow P v a (.of false) := by
        by_cases ha : a ∈ P
        · simp only [literalRow, ha, ↓reduceIte, ord a ha]
        · simp only [literalRow, ha, ↓reduceIte]
      cases d <;> simp only [markerContext,
        D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.OutputContext.plug,
        literalRow, ha, ↓reduceIte]
      · have eq := congrArg₂ FreeMagma.mul
          (ih (a ++ [false]) (by simpa [List.append_assoc] using cut)) (beta (a ++ [true]))
        simpa only [literalRow] using eq
      · have eq := congrArg₂ FreeMagma.mul
          (beta (a ++ [false])) (ih (a ++ [true]) (by simpa [List.append_assoc] using cut))
        simpa only [literalRow] using eq

/-- The nonuniform construction changes precisely a whole old class, including
preservation of absent cuts and all class disequalities. -/
theorem nonuniform_old_row (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (cover : ∀ p ∈ P, ∃ q ∈ Q, q.IsPrefix p) (s : Address) :
    let t := (markerContext s).plug (.of true)
    let z : Source := .mul t (.of false)
    let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
    let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
    canonicalRow P u = canonicalRow P v := by
  dsimp
  let t := (markerContext s).plug (.of true)
  let z : Source := .mul t (.of false)
  let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
  let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
  have ord : ∀ p ∈ P, classOrdinal P u p = classOrdinal P v p := by
    intro p hp
    exact changed_trie_ordinals P Q hP hQ cover s p hp
  have beta (a : Address) : literalRow P u a (.of true) = literalRow P v a (.of true) := by
    by_cases ha : a ∈ P <;> simp only [literalRow, ha, ↓reduceIte]
    exact congrArg (fun n => FreeMagma.of (Sum.inr n : Bool ⊕ Nat)) (ord a ha)
  have identical (a : Address) (w : Source) : literalRow P u a w = literalRow P v a w := by
    induction w generalizing a with
    | of b =>
        by_cases ha : a ∈ P <;> simp only [literalRow, ha, ↓reduceIte]
        exact congrArg (fun n => FreeMagma.of (Sum.inr n : Bool ⊕ Nat)) (ord a ha)
    | mul l r ihl ihr =>
        by_cases ha : a ∈ P
        · simp only [literalRow, ha, ↓reduceIte, ord a ha]
        · simp only [literalRow, ha, ↓reduceIte, ihl, ihr]
  have aux (n : Nat) (a : Address) :
      literalRow P u a (prefixTrie n Q a (fun _ => t)) =
      literalRow P v a (prefixTrie n Q a (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)) := by
    induction n generalizing a with
    | zero =>
        by_cases qa : a ∈ Q
        · by_cases sel : a ++ s ∈ P
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using marker_row_change P hP u v ord a s _ _ sel
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using identical a t
        · simpa only [prefixTrie, qa, ↓reduceIte] using beta a
    | succ n ih =>
        by_cases qa : a ∈ Q
        · by_cases sel : a ++ s ∈ P
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using marker_row_change P hP u v ord a s _ _ sel
          · simpa only [prefixTrie, qa, sel, ↓reduceIte] using identical a t
        · by_cases ext : ∃ q ∈ Q, a.IsPrefix q
          · by_cases pa : a ∈ P
            · simp only [prefixTrie, qa, ext, literalRow, pa, ↓reduceIte, ord a pa]
            · simp only [prefixTrie, qa, ext, literalRow, pa, ↓reduceIte, ih]
          · simpa only [prefixTrie, qa, ext, ↓reduceIte] using beta a
  exact aux (cutDepth Q) []

/-- A nonuniform suffix has two actual sources with equal old rows and unequal
new partitions. Their constructors and all hole values are native finite trees. -/
theorem nonuniform_failure_pair (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (cover : ∀ p ∈ P, ∃ q ∈ Q, q.IsPrefix p)
    (x y s : Address) (hx : x ∈ Q) (hy : y ∈ Q) (xs : x ++ s ∈ P) (ys : y ++ s ∉ P) :
    ∃ u v : Source, canonicalRow P u = canonicalRow P v ∧ canonicalRow Q u ≠ canonicalRow Q v := by
  let t := (markerContext s).plug (.of true)
  let z : Source := .mul t (.of false)
  let u := prefixTrie (cutDepth Q) Q [] (fun _ => t)
  let v := prefixTrie (cutDepth Q) Q []
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t)
  refine ⟨u, v, nonuniform_old_row P Q hP hQ cover s, ?_⟩
  have ux : subtree x u = some t := prefixTrie_cut Q hQ _ x hx
  have uy : subtree y u = some t := prefixTrie_cut Q hQ _ y hy
  have vx : subtree x v = some ((markerContext s).plug z) := by
    simpa only [xs, ↓reduceIte] using prefixTrie_cut Q hQ
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t) x hx
  have vy : subtree y v = some t := by
    simpa only [ys, ↓reduceIte] using prefixTrie_cut Q hQ
      (fun q => if q ++ s ∈ P then (markerContext s).plug z else t) y hy
  have diff : (markerContext s).plug z ≠ t := by
    intro eq
    have len := congrArg FreeMagma.length eq
    rw [marker_length] at len
    change s.length + (t.length + 1) = t.length at len
    omega
  intro rows
  have oldEq : holeLabel x (canonicalRow Q u) = holeLabel y (canonicalRow Q u) :=
    (canonicalRow_partition Q hQ u x y hx hy (by simp [ux]) (by simp [uy])).1.mpr (ux.trans uy.symm)
  have newEq : holeLabel x (canonicalRow Q v) = holeLabel y (canonicalRow Q v) := by simpa [rows] using oldEq
  have subEq := (canonicalRow_partition Q hQ v x y hx hy (by simp [vx]) (by simp [vy])).1.mp newEq
  rw [vx, vy, Option.some.injEq] at subEq
  exact diff subEq

#print axioms classOrdinal_eq_iff

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
