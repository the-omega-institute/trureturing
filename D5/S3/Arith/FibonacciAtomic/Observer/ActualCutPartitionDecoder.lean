/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Source-free finite recutting and exact common-suffix local kernels. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery

/-- New reached holes are computed solely by finite navigation of the old term. -/
def decoderHoles (Q : CutSet) (C : LiteralRow) : List Address :=
  (Q.filter (fun q => (rowAt q C).isSome)).sort (fun a b : Address => a ≤ b)

/-- Global old labels remain in each local expression until new classes are named. -/
def decoderClass (Q : CutSet) (C : LiteralRow) (q : Address) : Nat :=
  ((decoderHoles Q C).map (fun r => rowAt r C)).idxOf (rowAt q C)

/-- Finite recutting copies exterior syntax and compares retained local terms. -/
def recutRow (Q : CutSet) (C : LiteralRow) : Address → LiteralRow → LiteralRow
  | a, .of b => if a ∈ Q then .of (.inr (decoderClass Q C a)) else .of b
  | a, .mul l r => if a ∈ Q then .of (.inr (decoderClass Q C a)) else
      .mul (recutRow Q C (a ++ [false]) l) (recutRow Q C (a ++ [true]) r)

/-- A total raw decoder; correctness is required on realized rows. -/
def rowDecoder (Q : CutSet) (C : LiteralRow) : LiteralRow := recutRow Q C [] C

private theorem common_cut_section (P Q S : CutSet) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (q : Address) (hq : q ∈ Q) (s : Address) : q ++ s ∈ P ↔ s ∈ S := by
  constructor
  · intro hp
    obtain ⟨r, hr, t, ht, eq⟩ := (prod _).mp hp
    have own := D5.S0.Computability.Coding.PrefixFreeCode.isPrefixFree_first_codeword hQ hq hr eq
    simpa [own.2] using ht
  · intro hs
    exact (prod _).mpr ⟨q, hq, s, hs, rfl⟩

private theorem common_no_ancestor (P Q S : CutSet) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (q : Address) (hq : q ∈ Q) :
    ∀ a : Address, a.IsPrefix q → a ≠ q → a ∉ P := by
  intro a ha ne mem
  obtain ⟨r, hr, s, hs, rfl⟩ := (prod a).mp mem
  have rq := (List.prefix_append r s).trans ha
  have eq : r = q := hQ hr hq rq
  subst r
  have sl : s.length = 0 := by have := ha.length_le; simp only [List.length_append] at this; omega
  exact ne (by simp [List.length_eq_zero_iff.mp sl])

private theorem local_terms_equal (P : CutSet) (hP : CutPrefixFree P) (root : Source)
    (t : Source) (a b : Address) (ha : subtree a root = some t) (hb : subtree b root = some t)
    (cuts : ∀ s : Address, a ++ s ∈ P ↔ b ++ s ∈ P) :
    literalRow P root a t = literalRow P root b t := by
  induction t generalizing a b with
  | of bit =>
      have same : a ∈ P ↔ b ∈ P := by simpa using cuts []
      by_cases hp : a ∈ P
      · have hq := same.mp hp
        have ord := (classOrdinal_eq_iff P root
          ((orderedHoles_mem P hP root a).mpr ⟨hp, by simp [ha]⟩)
          ((orderedHoles_mem P hP root b).mpr ⟨hq, by simp [hb]⟩)).mpr (ha.trans hb.symm)
        simp only [literalRow, hp, hq, ↓reduceIte, ord]
      · have hq : b ∉ P := fun h => hp (same.mpr h)
        simp [literalRow, hp, hq]
  | mul l r ihl ihr =>
      have same : a ∈ P ↔ b ∈ P := by simpa using cuts []
      by_cases hp : a ∈ P
      · have hq := same.mp hp
        have ord := (classOrdinal_eq_iff P root
          ((orderedHoles_mem P hP root a).mpr ⟨hp, by simp [ha]⟩)
          ((orderedHoles_mem P hP root b).mpr ⟨hq, by simp [hb]⟩)).mpr (ha.trans hb.symm)
        simp only [literalRow, hp, hq, ↓reduceIte, ord]
      · have hq : b ∉ P := fun h => hp (same.mpr h)
        have app := D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have al : subtree (a ++ [false]) root = some l := by rw [app, ha]; rfl
        have bl : subtree (b ++ [false]) root = some l := by rw [app, hb]; rfl
        have ar : subtree (a ++ [true]) root = some r := by rw [app, ha]; rfl
        have br : subtree (b ++ [true]) root = some r := by rw [app, hb]; rfl
        simp only [literalRow, hp, hq, ↓reduceIte]
        exact congrArg₂ FreeMagma.mul
          (ihl _ _ al bl (by intro s; simpa [List.append_assoc] using cuts (false :: s)))
          (ihr _ _ ar br (by intro s; simpa [List.append_assoc] using cuts (true :: s)))

private theorem rowAt_common (P Q S : CutSet) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (u : Source) (q : Address) (hq : q ∈ Q) :
    rowAt q (canonicalRow P u) = (subtree q u).map (literalRow P u q) := by
  simpa [canonicalRow] using literalRow_at P u [] q u
    (by simpa using common_no_ancestor P Q S hQ prod q hq)

/-- On common-suffix cuts, equality of extracted finite local terms is exactly
actual subtree equality, including absent addresses. -/
theorem common_local_kernel (P Q S : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (u : Source) (q r : Address) (hq : q ∈ Q) (hr : r ∈ Q) :
    rowAt q (canonicalRow P u) = rowAt r (canonicalRow P u) ↔ subtree q u = subtree r u := by
  rw [rowAt_common P Q S hQ prod u q hq, rowAt_common P Q S hQ prod u r hr]
  cases sq : subtree q u with
  | none => cases sr : subtree r u <;> simp
  | some t =>
    cases sr : subtree r u with
    | none => simp
    | some z =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h
        have eq := congrArg (evaluateRow (classValue P u)) h
        rw [literalRow_evaluate P hP u q t sq, literalRow_evaluate P hP u r z sr] at eq
        exact eq
      · intro eq
        subst z
        exact local_terms_equal P hP u t q r sq sr (by
          intro s
          rw [common_cut_section P Q S hQ prod q hq, common_cut_section P Q S hQ prod r hr])

private theorem decoderHoles_correct (P Q S : CutSet) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s) (u : Source) :
    decoderHoles Q (canonicalRow P u) = orderedHoles Q u := by
  unfold decoderHoles orderedHoles
  congr 1
  ext q
  simp only [Finset.mem_filter, List.mem_toFinset]
  have support := Finset.ext_iff.mp (literalRow_hole_support Q u) q
  simp only [List.mem_toFinset] at support
  rw [← support, canonicalRow_reached Q hQ u q]
  by_cases hq : q ∈ Q
  · rw [rowAt_common P Q S hQ prod u q hq]
    cases subtree q u <;> simp [hq]
  · simp [hq]

private theorem decoderClass_correct (P Q S : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (u : Source) (q : Address) (hq : q ∈ Q) :
    decoderClass Q (canonicalRow P u) q = classOrdinal Q u q := by
  unfold decoderClass classOrdinal firstEqIndex
  rw [decoderHoles_correct P Q S hQ prod u]
  apply idxOf_map_relation (orderedHoles Q u)
    (fun r => rowAt r (canonicalRow P u)) (fun r => subtree r u) q
  intro r hr
  have rq : r ∈ Q := ((orderedHoles_mem Q hQ u r).mp hr).1
  exact common_local_kernel P Q S hP hQ prod u r q rq hq

private theorem recutRow_stop (Q : CutSet) (C t : LiteralRow) (a : Address) (ha : a ∈ Q) :
    recutRow Q C a t = .of (.inr (decoderClass Q C a)) := by
  cases t <;> simp only [recutRow, ha, ↓reduceIte]

private theorem decoder_correct_aux (P Q S : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (root : Source) (t : Source) (a : Address)
    (outside : ∀ q ∈ Q, q.IsPrefix a → q = a) :
    recutRow Q (canonicalRow P root) a (literalRow P root a t) = literalRow Q root a t := by
  induction t generalizing a with
  | of b =>
      by_cases qa : a ∈ Q
      · simp only [recutRow_stop Q _ _ a qa, literalRow, qa, ↓reduceIte,
          decoderClass_correct P Q S hP hQ prod root a qa]
      · have pa : a ∉ P := by
          intro hp
          obtain ⟨q, hq, s, hs, eq⟩ := (prod _).mp hp
          have pre : q.IsPrefix a := eq ▸ List.prefix_append _ _
          exact qa (outside q hq pre ▸ hq)
        simp only [literalRow, pa, qa, ↓reduceIte, recutRow]
  | mul l r ihl ihr =>
      by_cases qa : a ∈ Q
      · simp only [recutRow_stop Q _ _ a qa, literalRow, qa, ↓reduceIte,
          decoderClass_correct P Q S hP hQ prod root a qa]
      · have pa : a ∉ P := by
          intro hp
          obtain ⟨q, hq, s, hs, eq⟩ := (prod _).mp hp
          have pre : q.IsPrefix a := eq ▸ List.prefix_append _ _
          exact qa (outside q hq pre ▸ hq)
        have down (d : Bool) : ∀ q ∈ Q, q.IsPrefix (a ++ [d]) → q = a ++ [d] := by
          intro q hq pre
          rcases List.prefix_or_prefix_of_prefix pre (List.prefix_append a [d]) with h | h
          · exact False.elim (qa (outside q hq h ▸ hq))
          · have plen := pre.length_le
            have alen := h.length_le
            by_cases len : a.length = q.length
            · have aq := h.eq_of_length len
              exact False.elim (qa (aq.symm ▸ hq))
            · exact pre.eq_of_length (by simp only [List.length_append, List.length_singleton] at plen ⊢; omega)
        simp only [literalRow, pa, qa, ↓reduceIte, recutRow]
        exact congrArg₂ FreeMagma.mul (ihl _ (down false)) (ihr _ (down true))

/-- The decoder runs on the retained finite term and returns the precise new row. -/
theorem commonSuffix_decoder_correct (P Q S : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s) (u : Source) :
    rowDecoder Q (canonicalRow P u) = canonicalRow Q u := by
  exact decoder_correct_aux P Q S hP hQ prod u u [] (by
    intro q _ hq
    exact List.prefix_nil.mp hq)

/-- Common-suffix cuts supply recovery by a finite expression computation. -/
theorem commonSuffix_recovers (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (suffix : HasCommonSuffix P Q) : Recovers P Q := by
  obtain ⟨S, hS, prod⟩ := suffix
  intro u v eq
  rw [← commonSuffix_decoder_correct P Q S hP hQ prod u,
    ← commonSuffix_decoder_correct P Q S hP hQ prod v, eq]

private theorem suffix_is_section (P Q S : CutSet) (hQ : CutPrefixFree Q)
    (prod : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (q : Address) (hq : q ∈ Q) : S = cutSection P q := by
  ext s
  rw [mem_cutSection_iff, common_cut_section P Q S hQ prod q hq]
  simp

/-- For nonempty Q, the public section computes the unique possible suffix. -/
theorem commonSuffix_unique (P Q S T : CutSet) (hQ : CutPrefixFree Q) (nonempty : Q.Nonempty)
    (ps : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s)
    (pt : ∀ p, p ∈ P ↔ ∃ q ∈ Q, ∃ t ∈ T, p = q ++ t) : S = T := by
  obtain ⟨q, hq⟩ := nonempty
  exact (suffix_is_section P Q S hQ ps q hq).trans (suffix_is_section P Q T hQ pt q hq).symm

/-- Finite concatenation of public address sets. -/
def cutProduct (Q S : CutSet) : CutSet :=
  Q.biUnion (fun q => S.image (q ++ ·))

private theorem cutProduct_mem (Q S : CutSet) (p : Address) :
    p ∈ cutProduct Q S ↔ ∃ q ∈ Q, ∃ s ∈ S, p = q ++ s := by
  simp only [cutProduct, Finset.mem_biUnion, Finset.mem_image]
  constructor <;> rintro ⟨q, hq, s, hs, eq⟩ <;> exact ⟨q, hq, s, hs, eq.symm⟩

/-- Boolean comparison of finitely many suffix sections; no source is inspected. -/
def commonSuffixTest (P Q : CutSet) : Bool :=
  match Q.sort (fun a b : Address => a ≤ b) with
  | [] => decide (P = ∅)
  | q :: _ => decide (P = cutProduct Q (cutSection P q))

/-- The full common-suffix predicate has an actual finite decision procedure. -/
theorem commonSuffixTest_correct (P Q : CutSet) (hP : CutPrefixFree P) (hQ : CutPrefixFree Q) :
    commonSuffixTest P Q = true ↔ HasCommonSuffix P Q := by
  unfold commonSuffixTest
  cases he : Q.sort (fun a b : Address => a ≤ b) with
  | nil =>
      have qe : Q = ∅ := by
        ext q
        have hm : q ∈ Q.sort (fun a b : Address => a ≤ b) ↔ q ∈ Q := by simp
        simp [he] at hm
        simp [hm]
      simp only [qe, decide_eq_true_eq, commonSuffix_empty_right]
  | cons q qs =>
      have hq : q ∈ Q := by
        have : q ∈ Q.sort (fun a b : Address => a ≤ b) := by simp [he]
        simpa using this
      simp only [decide_eq_true_eq]
      constructor
      · intro hp
        refine ⟨cutSection P q, cutSection_prefixFree P hP q, ?_⟩
        intro p
        calc
          p ∈ P ↔ p ∈ cutProduct Q (cutSection P q) :=
            Iff.of_eq (congrArg (fun R : CutSet => p ∈ R) hp)
          _ ↔ ∃ r ∈ Q, ∃ s ∈ cutSection P q, p = r ++ s :=
            cutProduct_mem Q (cutSection P q) p
      · rintro ⟨S, _, prod⟩
        have es := suffix_is_section P Q S hQ prod q hq
        ext p
        rw [cutProduct_mem, ← es]
        exact prod p

/-- The independent literal exterior gives each hole its native address.
Lexicographic indexing of these addresses is the unique-hole numbering. -/
abbrev HoleExterior := FreeMagma (Bool ⊕ Address)

def cutExterior (P : CutSet) : Address → Source → HoleExterior
  | a, .of b => if a ∈ P then .of (.inr a) else .of (.inl b)
  | a, .mul l r => if a ∈ P then .of (.inr a) else
      .mul (cutExterior P (a ++ [false]) l) (cutExterior P (a ++ [true]) r)

def exteriorHoles : Address → HoleExterior → List Address
  | _, .of (.inl _) => []
  | _, .of (.inr p) => [p]
  | a, .mul l r => exteriorHoles (a ++ [false]) l ++ exteriorHoles (a ++ [true]) r

private def eraseClasses : Address → LiteralRow → HoleExterior
  | _, .of (.inl b) => .of (.inl b)
  | a, .of (.inr _) => .of (.inr a)
  | a, .mul l r =>
      .mul (eraseClasses (a ++ [false]) l) (eraseClasses (a ++ [true]) r)

private theorem eraseClasses_literal (P : CutSet) (root : Source) (a : Address) (t : Source) :
    eraseClasses a (literalRow P root a t) = cutExterior P a t := by
  induction t generalizing a with
  | of b => by_cases ha : a ∈ P <;> simp [literalRow, eraseClasses, cutExterior, ha]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P <;> simp [literalRow, eraseClasses, cutExterior, ha, ihl, ihr]

theorem exteriorHoles_cut (P : CutSet) (a : Address) (t : Source) :
    exteriorHoles a (cutExterior P a t) = reachedHoles P a t := by
  induction t generalizing a with
  | of b => by_cases ha : a ∈ P <;> simp [cutExterior, exteriorHoles, reachedHoles, ha]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P <;> simp [cutExterior, exteriorHoles, reachedHoles, ha, ihl, ihr]

/-- The finite partition lists exactly the pairs of reached holes with equal
actual values. Nonmembership among reached pairs records disequality. -/
def actualPartition (P : CutSet) (u : Source) : Finset (Address × Address) :=
  ((orderedHoles P u).toFinset.product (orderedHoles P u).toFinset).filter
    (fun pq => subtree pq.1 u = subtree pq.2 u)

/-- An independently computed exterior and complete finite hole partition. -/
def literalRecord (P : CutSet) (u : Source) : HoleExterior × Finset (Address × Address) :=
  (cutExterior P [] u, actualPartition P u)

def nameExterior (names : Address → Nat) : HoleExterior → LiteralRow :=
  FreeMagma.lift (fun x => .of (Sum.map id names x))

theorem nameExterior_correct (P : CutSet) (hP : CutPrefixFree P) (root : Source)
    (names : Address → Nat)
    (labels : ∀ p ∈ orderedHoles P root, names p = classOrdinal P root p)
    (a : Address) (t : Source) (ht : subtree a root = some t) :
    nameExterior names (cutExterior P a t) = literalRow P root a t := by
  induction t generalizing a with
  | of b =>
      by_cases ha : a ∈ P
      · have mem := (orderedHoles_mem P hP root a).mpr ⟨ha, by simp [ht]⟩
        simp [cutExterior, literalRow, ha, nameExterior, FreeMagma.lift_of, labels a mem]
      · simp [cutExterior, literalRow, ha, nameExterior, FreeMagma.lift_of]
  | mul l r ihl ihr =>
      by_cases ha : a ∈ P
      · have mem := (orderedHoles_mem P hP root a).mpr ⟨ha, by simp [ht]⟩
        simp [cutExterior, literalRow, ha, nameExterior, FreeMagma.lift_of, labels a mem]
      · have app := D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hl : subtree (a ++ [false]) root = some l := by rw [app, ht]; rfl
        have hr : subtree (a ++ [true]) root = some r := by rw [app, ht]; rfl
        simpa only [cutExterior, literalRow, ha, ↓reduceIte, nameExterior,
          FreeMagma.mul_eq, map_mul] using
          congrArg₂ FreeMagma.mul (ihl _ hl) (ihr _ hr)

/-- Canonical rows have exactly the information in the literal exterior and
complete partition. No source value, size or acquisition trace is added. -/
theorem canonicalRow_record_iff (P : CutSet) (hP : CutPrefixFree P) (u v : Source) :
    canonicalRow P u = canonicalRow P v ↔ literalRecord P u = literalRecord P v := by
  constructor
  · intro rows
    have ord : orderedHoles P u = orderedHoles P v := by
      unfold orderedHoles
      rw [← literalRow_hole_support P u, ← literalRow_hole_support P v, rows]
    apply Prod.ext
    · exact (eraseClasses_literal P u [] u).symm.trans
        ((congrArg (eraseClasses []) rows).trans (eraseClasses_literal P v [] v))
    · change actualPartition P u = actualPartition P v
      ext ⟨p, q⟩
      simp only [actualPartition, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, List.mem_toFinset,
        ← ord]
      by_cases hp : p ∈ orderedHoles P u
      · by_cases hq : q ∈ orderedHoles P u
        · obtain ⟨pp, ps⟩ := (orderedHoles_mem P hP u p).mp hp
          obtain ⟨qp, qs⟩ := (orderedHoles_mem P hP u q).mp hq
          have pv := (orderedHoles_mem P hP v p).mp (ord ▸ hp)
          have qv := (orderedHoles_mem P hP v q).mp (ord ▸ hq)
          have ku := (canonicalRow_partition P hP u p q pp qp ps qs).1
          have kv := (canonicalRow_partition P hP v p q pp qp pv.2 qv.2).1
          simpa only [hp, hq, true_and] using (ku.symm.trans (by rw [rows])).trans kv
        · simp [hq]
      · simp [hp]
  · intro records
    have exterior : cutExterior P [] u = cutExterior P [] v := congrArg Prod.fst records
    have partition : actualPartition P u = actualPartition P v := congrArg Prod.snd records
    have ord : orderedHoles P u = orderedHoles P v := by
      have holes := congrArg (fun C => (exteriorHoles [] C).toFinset.sort
        (fun a b : Address => a ≤ b)) exterior
      simpa only [exteriorHoles_cut, orderedHoles] using holes
    have labels (p : Address) (hp : p ∈ orderedHoles P u) :
        classOrdinal P v p = classOrdinal P u p := by
      symm
      unfold classOrdinal firstEqIndex
      rw [← ord]
      apply idxOf_map_relation (orderedHoles P u) (fun r => subtree r u)
        (fun r => subtree r v) p
      intro q hq
      have same := Finset.ext_iff.mp partition (q, p)
      simpa only [actualPartition, Finset.mem_filter, Finset.product_eq_sprod,
        Finset.mem_product, List.mem_toFinset,
        ← ord, hp, hq, true_and] using same
    have left := nameExterior_correct P hP u (classOrdinal P v) labels [] u rfl
    have right := nameExterior_correct P hP v (classOrdinal P v) (by intro p _; rfl) [] v rfl
    exact left.symm.trans ((congrArg (nameExterior (classOrdinal P v)) exterior).trans right)

end D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
