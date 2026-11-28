/- GID: D5/S3/Combinatorics/Partitions/WisemanA261041
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/WisemanA261041
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Logic.Equiv.Fintype, mathlib/module/Mathlib.SetTheory.Cardinal.NatCard]
   utility: none
   digest: The swap scan gives a reversible equivalence between the two partition classes. -/

import OmegaBuild.Commands
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Fintype
import Mathlib.SetTheory.Cardinal.NatCard

compile_only_with_mathlib

/-! Gus Wiseman's conjecture in OEIS A261041, comment dated November 25, 2019.
https://oeis.org/A261041/internal
https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7225772584
-/

namespace D5.S3.Combinatorics.Partitions.WisemanA261041

set_option autoImplicit false
set_option relaxedAutoImplicit false

section Swap

variable {α : Type*} [Zero α] [DecidableEq α]

/-- The permutation after processing positions 1 through i. -/
private def state (a : ℕ → α) : ℕ → Equiv.Perm α
  | 0 => Equiv.refl α
  | i + 1 => (Equiv.swap 0 (a (i + 1))).trans (state a i)

private def output (a : ℕ → α) (i : ℕ) : α := state a i 0

private theorem output_succ (a : ℕ → α) (i : ℕ) :
    output a (i + 1) = state a i (a (i + 1)) := by
  simp [output, state]

/-- Inverse scan. The second component records the label recovered at position i. -/
private def inverseScan (b : ℕ → α) : ℕ → Equiv.Perm α × α
  | 0 => (Equiv.refl α, 0)
  | i + 1 =>
    let p := (inverseScan b i).1
    let x := p.symm (b (i + 1))
    ((Equiv.swap 0 x).trans p, x)

private theorem inverseScan_output (a : ℕ → α) (ha : a 0 = 0) (i : ℕ) :
    inverseScan (output a) i = (state a i, a i) := by
  induction i with
  | zero => simp [inverseScan, state, ha]
  | succ i ih => simp [inverseScan, state, output_succ, ih]

private theorem output_inverseScan (b : ℕ → α) (hb : b 0 = 0) (i : ℕ) :
    output (fun j => (inverseScan b j).2) i = b i := by
  have hstate (j : ℕ) : state (fun k => (inverseScan b k).2) j = (inverseScan b j).1 := by
    induction j with
    | zero => rfl
    | succ j ih => simp [state, inverseScan, ih]
  cases i with
  | zero => exact hb.symm
  | succ i => simp [output_succ, hstate, inverseScan]

private theorem state_congr {a b : ℕ → α} (i : ℕ) (h : ∀ j ≤ i, a j = b j) :
    state a i = state b i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp [state, h (i + 1) le_rfl, ih (fun j hj => h j (Nat.le.step hj))]

private theorem inverseScan_congr {a b : ℕ → α} (i : ℕ) (h : ∀ j ≤ i, a j = b j) :
    inverseScan a i = inverseScan b i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp [inverseScan, h (i + 1) le_rfl, ih (fun j hj => h j (Nat.le.step hj))]

private theorem state_rename (p : Equiv.Perm α) (hp : p 0 = 0) (a : ℕ → α)
    (i : ℕ) (x : α) : state (p ∘ a) i (p x) = p (state a i x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    change state (p ∘ a) i (Equiv.swap 0 (p (a (i + 1))) (p x)) =
      p (state a i (Equiv.swap 0 (a (i + 1)) x))
    have hswap : Equiv.swap 0 (p (a (i + 1))) (p x) =
        p (Equiv.swap 0 (a (i + 1)) x) := by
      simpa only [hp] using p.injective.swap_apply 0 (a (i + 1)) x
    rw [hswap, ih]

private theorem output_rename (p : Equiv.Perm α) (hp : p 0 = 0) (a : ℕ → α) (i : ℕ) :
    output (p ∘ a) i = p (output a i) := by
  simpa only [output, hp] using state_rename p hp a i 0

/-- The forbidden right triple corresponds exactly to repeating a nonzero input label. -/
private theorem forbidden_triple (a : ℕ → α) (i : ℕ) :
    (output a i = output a (i + 2) ∧ output a i ≠ output a (i + 1)) ↔
      (a (i + 1) = a (i + 2) ∧ a (i + 1) ≠ 0) := by
  rw [output_succ a (i + 1), output_succ a i]
  change (state a i 0 = state a i (Equiv.swap 0 (a (i + 1)) (a (i + 2))) ∧
    state a i 0 ≠ state a i (a (i + 1))) ↔ _
  simp only [Equiv.apply_eq_iff_eq, ne_eq]
  rw [eq_comm (a := 0), Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  tauto

end Swap

/-- The leading zero marks the omission class on the input and the first point on the output. -/
private abbrev Word (n : ℕ) := {a : Fin (n + 1) → Fin (n + 1) // a 0 = 0}

private def readWord {n : ℕ} (a : Word n) (i : ℕ) : Fin (n + 1) :=
  if h : i < n + 1 then a.val ⟨i, h⟩ else 0

@[simp] private theorem readWord_fin {n : ℕ} (a : Word n) (i : Fin (n + 1)) :
    readWord a i.val = a.val i := dite_eq_left i.isLt

@[simp] private theorem readWord_zero {n : ℕ} (a : Word n) : readWord a 0 = 0 := by
  simpa only [Fin.val_zero, a.property] using readWord_fin a 0

private def encode {n : ℕ} (a : Word n) : Word n :=
  ⟨fun i => output (readWord a) i.val, rfl⟩

private def decode {n : ℕ} (b : Word n) : Word n :=
  ⟨fun i => (inverseScan (readWord b) i.val).2, rfl⟩

private theorem decode_encode {n : ℕ} (a : Word n) : decode (encode a) = a := by
  apply Subtype.ext
  funext i
  have h (j : ℕ) (hj : j ≤ i.val) :
      readWord (encode a) j = output (readWord a) j := dite_eq_left (lt_of_le_of_lt hj i.isLt)
  change (inverseScan (readWord (encode a)) i.val).2 = a.val i
  rw [inverseScan_congr _ h, inverseScan_output _ (readWord_zero a), readWord_fin]

private theorem encode_decode {n : ℕ} (b : Word n) : encode (decode b) = b := by
  apply Subtype.ext
  funext i
  have h (j : ℕ) (hj : j ≤ i.val) :
      readWord (decode b) j = (inverseScan (readWord b) j).2 := dite_eq_left (lt_of_le_of_lt hj i.isLt)
  change state (readWord (decode b)) i.val 0 = b.val i
  rw [state_congr _ h]
  exact (output_inverseScan (readWord b) (readWord_zero b) i.val).trans (readWord_fin b i)

private theorem encode_rename {n : ℕ} {a b : Word n} (p : Equiv.Perm (Fin (n + 1)))
    (hp : p 0 = 0) (h : ∀ i, p (a.val i) = b.val i) (i : Fin (n + 1)) :
    p ((encode a).val i) = (encode b).val i := by
  have hr (j : ℕ) (hj : j ≤ i.val) : (p ∘ readWord a) j = readWord b j := by
    have hj' : j < n + 1 := lt_of_le_of_lt hj i.isLt
    simp only [Function.comp_apply, readWord, dite_eq_left hj']
    exact h ⟨j, hj'⟩
  change p (output (readWord a) i.val) = state (readWord b) i.val 0
  rw [← output_rename p hp, output, state_congr _ hr]

private noncomputable def blockFinset {n : ℕ} (s : Setoid (Fin (n + 1)))
    (i : Fin (n + 1)) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (s i)

private theorem mem_blockFinset {n : ℕ} (s : Setoid (Fin (n + 1))) (i j : Fin (n + 1)) :
    j ∈ blockFinset s i ↔ s i j := by
  classical
  simp [blockFinset]

private theorem blockFinset_nonempty {n : ℕ} (s : Setoid (Fin (n + 1))) (i : Fin (n + 1)) :
    (blockFinset s i).Nonempty :=
  ⟨i, (mem_blockFinset s i i).2 (s.iseqv.refl i)⟩

/-- Label each block by its least position. The block of the first point has label zero. -/
private noncomputable def labelPartition {n : ℕ} (s : Setoid (Fin (n + 1))) : Word n := by
  refine ⟨fun i => (blockFinset s i).min' (blockFinset_nonempty s i), ?_⟩
  apply (Finset.min'_eq_iff _ _ _).2
  exact ⟨(mem_blockFinset s 0 0).2 (s.iseqv.refl 0), fun j _ => Fin.zero_le j⟩

private theorem wordPartition_label {n : ℕ} (s : Setoid (Fin (n + 1))) :
    (Setoid.ker (labelPartition s).val) = s := by
  apply Setoid.ext
  intro i j
  change (labelPartition s).val i = (labelPartition s).val j ↔ s i j
  have mem (k : Fin (n + 1)) : (labelPartition s).val k ∈ blockFinset s k :=
    Finset.min'_mem (blockFinset s k) (blockFinset_nonempty s k)
  constructor
  · intro hij
    have hi := (mem_blockFinset s i _).1 (mem i)
    have hj := (mem_blockFinset s j _).1 (mem j)
    rw [← hij] at hj
    exact s.iseqv.trans hi (s.iseqv.symm hj)
  · intro hij
    have hcls : blockFinset s i = blockFinset s j := by
      ext k
      rw [mem_blockFinset, mem_blockFinset]
      exact ⟨s.iseqv.trans (s.iseqv.symm hij), s.iseqv.trans hij⟩
    exact le_antisymm
      (Finset.min'_le _ _ (hcls.symm ▸ mem j))
      (Finset.min'_le _ _ (hcls ▸ mem i))

private theorem wordPartition_eq_iff {n : ℕ} (a b : Word n) :
    (Setoid.ker a.val) = (Setoid.ker b.val) ↔
      ∃ p : Equiv.Perm (Fin (n + 1)), p 0 = 0 ∧ ∀ i, p (a.val i) = b.val i := by
  constructor
  · intro h
    let s := (Setoid.ker a.val)
    have hb (i j : Fin (n + 1)) (hij : s i j) : b.val i = b.val j := by
      change (Setoid.ker b.val) i j
      rw [← h]
      exact hij
    let fa : Quotient s → Fin (n + 1) := Setoid.kerLift a.val
    let fb : Quotient s → Fin (n + 1) := Quotient.lift b.val hb
    have ha_inj : Function.Injective fa := Setoid.kerLift_injective _
    have hb_inj : Function.Injective fb := by
      intro x y hxy
      induction x using Quotient.inductionOn with
      | _ i =>
        induction y using Quotient.inductionOn with
        | _ j =>
          apply Quotient.sound
          change (Setoid.ker a.val) i j
          rw [h]
          exact hxy
    obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair fa fb ha_inj hb_inj
    have hp' (i : Fin (n + 1)) : p (a.val i) = b.val i := hp (Quotient.mk s i)
    exact ⟨p, by simpa only [a.property, b.property] using hp' 0, hp'⟩
  · rintro ⟨p, _, h⟩
    exact Setoid.ext fun i j => by
      change a.val i = a.val j ↔ b.val i = b.val j
      rw [← h i, ← h j, p.apply_eq_iff_eq]

private theorem encode_partition_eq_iff {n : ℕ} (a b : Word n) :
    (Setoid.ker (encode a).val) = (Setoid.ker (encode b).val) ↔ (Setoid.ker a.val) = (Setoid.ker b.val) := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := (wordPartition_eq_iff _ _).1 h
    let c : Word n := ⟨fun i => p (a.val i), by simp only [a.property, hp]⟩
    have hc : encode c = encode b :=
      Subtype.ext (funext fun i => (encode_rename p hp (fun _ => rfl) i).symm.trans (he i))
    have hcb : c = b := by
      simpa only [decode_encode] using congrArg decode hc
    exact (wordPartition_eq_iff _ _).2 ⟨p, hp, fun i => congrArg (fun w : Word n => w.val i) hcb⟩
  · intro h
    obtain ⟨p, hp, hw⟩ := (wordPartition_eq_iff _ _).1 h
    exact (wordPartition_eq_iff _ _).2 ⟨p, hp, encode_rename p hp hw⟩

/-- The swap scan induces a permutation of the unlabelled partitions of the padded interval. -/
private noncomputable def partitionEquiv (n : ℕ) : Setoid (Fin (n + 1)) ≃ Setoid (Fin (n + 1)) :=
  Equiv.ofBijective (fun s => (Setoid.ker (encode (labelPartition s)).val)) (by
    constructor
    · intro s t h
      have h' := (encode_partition_eq_iff _ _).1 h
      simpa only [wordPartition_label] using h'
    · intro t
      let a := decode (labelPartition t)
      refine ⟨(Setoid.ker a.val), ?_⟩
      change (Setoid.ker (encode (labelPartition (Setoid.ker a.val))).val) = t
      rw [(encode_partition_eq_iff _ _).2 (wordPartition_label ((Setoid.ker a.val)))]
      rw [show encode a = labelPartition t from encode_decode _, wordPartition_label])

private theorem partitionEquiv_word {n : ℕ} (a : Word n) :
    partitionEquiv n ((Setoid.ker a.val)) = (Setoid.ker (encode a).val) :=
  (encode_partition_eq_iff _ _).2 (wordPartition_label _)

/-- A literal partition of a subset of the positions, given by its equivalence relation. -/
structure PartialPartition (n : ℕ) where
  carrier : Set (Fin n)
  blocks : Setoid carrier

def PartialPartition.SameBlock {n : ℕ} (p : PartialPartition n) (i j : Fin n) : Prop :=
  ∃ (hi : i ∈ p.carrier) (hj : j ∈ p.carrier), p.blocks ⟨i, hi⟩ ⟨j, hj⟩

private theorem partialPartition_ext_sameBlock {n : ℕ} {p q : PartialPartition n}
    (h : ∀ i j, p.SameBlock i j ↔ q.SameBlock i j) : p = q := by
  cases p with
  | mk p rp =>
    cases q with
    | mk q rq =>
      have heq : p = q := Set.ext fun i => by
        constructor
        · intro hi
          exact ((h i i).1 ⟨hi, hi, rp.iseqv.refl _⟩).choose
        · intro hi
          exact ((h i i).2 ⟨hi, hi, rq.iseqv.refl _⟩).choose
      subst q
      congr 1
      apply Setoid.ext
      intro i j
      have hsame (r : Setoid p) :
          (PartialPartition.mk p r).SameBlock i.val j.val ↔ r i j :=
        ⟨fun ⟨_, _, h'⟩ => h', fun h' => ⟨i.property, j.property, h'⟩⟩
      exact (hsame rp).symm.trans ((h i.val j.val).trans (hsame rq))

private noncomputable def padLabels {n : ℕ} (p : PartialPartition n) :
    Fin (n + 1) → Option (Quotient p.blocks) := by
  classical
  exact Fin.cons none
    (fun i => if hi : i ∈ p.carrier then some (Quotient.mk p.blocks ⟨i, hi⟩) else none)

/-- Add a first position and place all omitted points in its block. -/
private noncomputable def pad {n : ℕ} (p : PartialPartition n) : Setoid (Fin (n + 1)) :=
  Setoid.ker (padLabels p)

private def unpad {n : ℕ} (s : Setoid (Fin (n + 1))) : PartialPartition n where
  carrier := {i | ¬ s i.succ 0}
  blocks := Setoid.comap (fun i => i.val.succ) s

private theorem unpad_sameBlock {n : ℕ} (s : Setoid (Fin (n + 1))) (i j : Fin n) :
    (unpad s).SameBlock i j ↔ ¬ s i.succ 0 ∧ s i.succ j.succ := by
  constructor
  · rintro ⟨hi, _, hij⟩
    exact ⟨hi, hij⟩
  · rintro ⟨hi, hij⟩
    exact ⟨hi, fun hj => hi (s.iseqv.trans hij hj), hij⟩

private theorem pad_succ_zero {n : ℕ} (p : PartialPartition n) (i : Fin n) :
    pad p i.succ 0 ↔ i ∉ p.carrier := by
  classical
  unfold pad padLabels Setoid.ker
  change (if hi : i ∈ p.carrier then some (Quotient.mk p.blocks ⟨i, hi⟩) else none) = none ↔ _
  by_cases hi : i ∈ p.carrier <;> simp [hi]

private theorem pad_succ_succ {n : ℕ} (p : PartialPartition n) (i j : Fin n) :
    pad p i.succ j.succ ↔ (i ∉ p.carrier ∧ j ∉ p.carrier) ∨ p.SameBlock i j := by
  classical
  unfold pad padLabels Setoid.ker
  change (if hi : i ∈ p.carrier then some (Quotient.mk p.blocks ⟨i, hi⟩) else none) =
    (if hj : j ∈ p.carrier then some (Quotient.mk p.blocks ⟨j, hj⟩) else none) ↔ _
  by_cases hi : i ∈ p.carrier <;> by_cases hj : j ∈ p.carrier <;>
    simp [hi, hj, PartialPartition.SameBlock, Quotient.eq]

private theorem unpad_pad {n : ℕ} (p : PartialPartition n) : unpad (pad p) = p := by
  classical
  apply partialPartition_ext_sameBlock
  intro i j
  rw [unpad_sameBlock, pad_succ_zero, pad_succ_succ]
  constructor
  · exact fun ⟨hi, h⟩ => h.resolve_left fun h' => hi h'.1
  · exact fun h => ⟨fun hi => hi h.choose, Or.inr h⟩

private theorem pad_unpad {n : ℕ} (s : Setoid (Fin (n + 1))) : pad (unpad s) = s := by
  classical
  apply Setoid.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact iff_of_true ((pad (unpad s)).iseqv.refl _) (s.iseqv.refl _)
    · rw [show pad (unpad s) 0 j.succ ↔ pad (unpad s) j.succ 0 from
        ⟨(pad (unpad s)).iseqv.symm, (pad (unpad s)).iseqv.symm⟩, pad_succ_zero]
      change (¬ ¬ s j.succ 0) ↔ s 0 j.succ
      exact ⟨fun h => s.iseqv.symm (not_not.mp h), fun h hn => hn (s.iseqv.symm h)⟩
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [pad_succ_zero]
      exact not_not
    · rw [pad_succ_succ, unpad_sameBlock]
      change ((¬ ¬ s i.succ 0 ∧ ¬ ¬ s j.succ 0) ∨
        (¬ s i.succ 0 ∧ s i.succ j.succ)) ↔ s i.succ j.succ
      simp only [not_not]
      constructor
      · rintro (⟨hi, hj⟩ | ⟨_, hij⟩)
        · exact s.iseqv.trans hi (s.iseqv.symm hj)
        · exact hij
      · intro hij
        by_cases hi : s i.succ 0
        · exact Or.inl ⟨hi, s.iseqv.trans (s.iseqv.symm hij) hi⟩
        · exact Or.inr ⟨hi, hij⟩

private noncomputable def padEquiv (n : ℕ) : PartialPartition n ≃ Setoid (Fin (n + 1)) :=
  ⟨pad, unpad, unpad_pad, pad_unpad⟩

/-- The position `i : Fin n` represents the integer `i.val + 1`. -/
def NoConsecutive {n : ℕ} (p : PartialPartition n) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < n), ¬ p.SameBlock ⟨i, by omega⟩ ⟨i + 1, h⟩

/-- Equal endpoints of a length-three consecutive triple force its middle into their block. -/
def TripleCondition {n : ℕ} (s : Setoid (Fin (n + 1))) : Prop :=
  ∀ (i : ℕ) (h : i + 2 < n + 1), s ⟨i, by omega⟩ ⟨i + 2, h⟩ →
    s ⟨i, by omega⟩ ⟨i + 1, by omega⟩

private theorem noConsecutive_iff_triple_word {n : ℕ} (a : Word n) :
    NoConsecutive (unpad ((Setoid.ker a.val))) ↔ TripleCondition ((Setoid.ker (encode a).val)) := by
  have localLeft (i : ℕ) (h : i + 1 < n) :
      (unpad ((Setoid.ker a.val))).SameBlock ⟨i, by omega⟩ ⟨i + 1, h⟩ ↔
        (readWord a (i + 1) = readWord a (i + 2) ∧ readWord a (i + 1) ≠ 0) := by
    rw [unpad_sameBlock]
    change (a.val ⟨i + 1, by omega⟩ ≠ a.val 0 ∧
      a.val ⟨i + 1, by omega⟩ = a.val ⟨i + 2, by omega⟩) ↔ _
    have read1 := readWord_fin a ⟨i + 1, by omega⟩
    have read2 := readWord_fin a ⟨i + 2, by omega⟩
    rw [a.property, show readWord a (i + 1) = _ from read1,
      show readWord a (i + 2) = _ from read2, and_comm]
  constructor
  · intro hleft i hi hends
    change output (readWord a) i = output (readWord a) (i + 2) at hends
    change output (readWord a) i = output (readWord a) (i + 1)
    by_contra hmid
    exact hleft i (by omega) ((localLeft i (by omega)).2
      ((forbidden_triple (readWord a) i).1 ⟨hends, hmid⟩))
  · intro hright i hi hab
    have hbad := (forbidden_triple (readWord a) i).2 ((localLeft i hi).1 hab)
    exact hbad.2 (hright i (by omega) hbad.1)

private theorem noConsecutive_iff_triple {n : ℕ} (p : PartialPartition n) :
    NoConsecutive p ↔ TripleCondition (partitionEquiv n (pad p)) := by
  let a := labelPartition (pad p)
  have ha : (Setoid.ker a.val) = pad p := wordPartition_label _
  rw [← ha, partitionEquiv_word]
  simpa only [ha, unpad_pad] using noConsecutive_iff_triple_word a

/-- All literal partitions of all subsets of the first n positive integers. -/
abbrev Left (n : ℕ) := {p : PartialPartition n // NoConsecutive p}

/-- All literal full partitions of the first n+1 positive integers with the triple condition. -/
abbrev Right (n : ℕ) := {s : Setoid (Fin (n + 1)) // TripleCondition s}

/- The literal bijection induced by padding and the swap scan. -/
noncomputable def wisemanBijection (n : ℕ) : Left n ≃ Right n :=
  ((padEquiv n).trans (partitionEquiv n)).subtypeEquiv noConsecutive_iff_triple

/-- Gus Wiseman's published counting identity for every natural number. -/
theorem result (n : ℕ) : Nat.card (Left n) = Nat.card (Right n) :=
  Nat.card_congr (wisemanBijection n)

end D5.S3.Combinatorics.Partitions.WisemanA261041
