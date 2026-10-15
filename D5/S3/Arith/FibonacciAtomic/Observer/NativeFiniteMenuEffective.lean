/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuEffective
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A total primitive-recursive fixed-menu decoder validates represented input and predicts all native epochs. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree
import Mathlib.Computability.Partrec

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualImageAddressCertificate (height)
open NativeFiniteMenuCode NativeFiniteMenuReconstruction NativeUniformAnalysis
open NativeUniformInput (replyEquiv replyPrimcodable)

/-- Lookup uses the first occurrence in the original public order. -/
def lookup (S : Menu) (xs : List Reply) (q : Address) : Reply :=
  xs.getD (S.idxOf q) .absent

private theorem lookup_initial (S : Menu) (u : Source) (q : Address) (hq : q ∈ S) :
    lookup S (initial S u) q = readout q u := by
  unfold lookup initial
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf hq]
  rfl

/-- Fixed public depth and menu admit a finite reconstruction table on full reply vectors. -/
def table (D : Nat) (S : Menu) (v : Fin S.length → Reply) : Option Source :=
  let xs := List.ofFn v
  if S.map (lookup S xs) = xs then reconstruct D S (lookup S xs) else none

/-- All list lengths are represented; wrong lengths reject before reconstruction. -/
def restore (D : Nat) (S : Menu) (xs : List Reply) : Option Source :=
  if xs.length = S.length then table D S (fun i => xs.getD i.val .absent) else none

private theorem table_prim (D : Nat) (S : Menu) : Primrec (table D S) :=
  Primrec.dom_finite _

private theorem restore_prim (D : Nat) (S : Menu) : Primrec (restore D S) := by
  have hv : Primrec (fun xs : List Reply => fun i : Fin S.length => xs.getD i.val .absent) :=
    Primrec.fin_curry.mpr (((Primrec.list_getD Reply.absent).comp Primrec.fst
      (Primrec.fin_val.comp Primrec.snd)).to₂)
  exact Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const S.length))
    ((table_prim D S).comp hv) (Primrec.const none)

private theorem restore_exact (D : Nat) (S : Menu) (xs : List Reply) (h : xs.length = S.length) :
    restore D S xs =
      if S.map (lookup S xs) = xs then reconstruct D S (lookup S xs) else none := by
  have he : List.ofFn (fun i : Fin S.length => xs.getD i.val .absent) = xs := by
    have general (n : Nat) (ys : List Reply) (hn : ys.length = n) :
        List.ofFn (fun i : Fin n => ys.getD i.val .absent) = ys := by
      subst n
      simpa only [List.getD_eq_get] using List.ofFn_get ys
    exact general S.length xs h
  simp only [restore, h, ↓reduceIte, table, he]

private theorem restore_attained (D : Nat) (S : Menu) (u : Source) :
    restore D S (initial S u) = reconstruct D S (lookup S (initial S u)) := by
  rw [restore_exact D S _ (by simp [initial])]
  have coherent : S.map (lookup S (initial S u)) = initial S u :=
    List.map_congr_left (fun q hq => lookup_initial S u q hq)
  rw [if_pos coherent]

private theorem reconstruction_sound (h : Nat) (S : Menu) (f : Address → Reply)
    (t : Source) (accepted : reconstruct h S f = some t) :
    height t ≤ h ∧ ∀ q ∈ S, readout q t = f q := by
  induction h generalizing S f t with
  | zero =>
    by_cases hs : S = []
    · subst S
      simp only [reconstruct, ↓reduceIte, Option.some.injEq] at accepted
      subst t
      exact ⟨by simp [height, GenealogicalFiberTransport.decompose, BinaryTree.height], by simp⟩
    · simp [reconstruct, hs] at accepted
  | succ h ih =>
    by_cases hs : S = []
    · subst S
      simp only [reconstruct, ↓reduceIte, Option.some.injEq] at accepted
      subst t
      exact ⟨by simp [height, GenealogicalFiberTransport.decompose, BinaryTree.height], by simp⟩
    · have leaf (b : Bool) (root : f [] = readout [] (.of b))
          (valid : leafValid S f = true) :
          height (.of b) ≤ h + 1 ∧ ∀ q ∈ S, readout q (.of b) = f q := by
        refine ⟨by simp [height, GenealogicalFiberTransport.decompose, BinaryTree.height], ?_⟩
        intro q hq
        cases q with
        | nil => exact root.symm
        | cons c q =>
          have hv := List.all_eq_true.mp valid (c :: q) hq
          have hfq : f (c :: q) = .absent := by simpa using hv
          exact hfq.symm
      cases hf : f [] with
      | alpha =>
        by_cases hv : leafValid S f = true
        · have ht : t = .of true := by simpa [reconstruct, hs, hf, hv] using accepted.symm
          subst t
          exact leaf true hf hv
        · simp [reconstruct, hs, hf, hv] at accepted
      | beta =>
        by_cases hv : leafValid S f = true
        · have ht : t = .of false := by simpa [reconstruct, hs, hf, hv] using accepted.symm
          subst t
          exact leaf false hf hv
        · simp [reconstruct, hs, hf, hv] at accepted
      | absent => simp [reconstruct, hs, hf] at accepted
      | branch =>
        cases hl : reconstruct h (child false S) (fun q => f (false :: q)) with
        | none => simp [reconstruct, hs, hf, hl] at accepted
        | some l =>
          cases hr : reconstruct h (child true S) (fun q => f (true :: q)) with
          | none => simp [reconstruct, hs, hf, hl, hr] at accepted
          | some r =>
            have ht : t = .mul l r := by simpa [reconstruct, hs, hf, hl, hr] using accepted.symm
            subst t
            obtain ⟨hhl, hal⟩ := ih _ _ _ hl
            obtain ⟨hhr, har⟩ := ih _ _ _ hr
            refine ⟨Nat.add_le_add_right (max_le hhl hhr) 1, ?_⟩
            intro q hq
            cases q with
            | nil => exact hf.symm
            | cons b q =>
              cases b
              · exact hal q ((mem_child false S q).mpr hq)
              · exact har q ((mem_child true S q).mpr hq)

private theorem restore_sound (D : Nat) (S : Menu) (xs : List Reply) (t : Source)
    (accepted : restore D S xs = some t) : height t ≤ D ∧ initial S t = xs := by
  have len : xs.length = S.length := by
    by_contra hn
    simp [restore, hn] at accepted
  rw [restore_exact D S xs len] at accepted
  split at accepted
  next coherent =>
    obtain ⟨ht, hagree⟩ := reconstruction_sound D S (lookup S xs) t accepted
    exact ⟨ht, (List.map_congr_left (fun q hq => hagree q hq)).trans coherent⟩
  next => contradiction

/-- Rejection returns a fixed vector of the public required size. -/
def decode (D : Nat) (S : Menu) (xs : List Reply) (k : Nat) : List Reply :=
  match restore D S xs with
  | none => List.replicate S.length .absent
  | some t => future S t k

private theorem future_prim (S : Menu) : Primrec₂ (future S) := by
  have hi : Primrec₂ (fun (n : Nat) (t : Source) => substitution^[n] t) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd (substitution_prim.comp Primrec.snd).to₂
  exact Primrec.list_map (Primrec.const S)
    (readout_prim.comp Primrec.snd (hi.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.fst))).to₂

private theorem decode_prim (D : Nat) (S : Menu) : Primrec₂ (decode D S) := by
  apply Primrec₂.mk
  exact (Primrec.option_casesOn ((restore_prim D S).comp Primrec.fst)
    (Primrec.const (List.replicate S.length Reply.absent))
    ((future_prim S).comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).of_eq
    (fun p => by cases hh : restore D S p.1 <;> simp [decode, hh])

/-- Raw symbols outside 0,1,2,3 are rejected. -/
def rawValid (S : Menu) (xs : List Nat) : Bool :=
  decide (xs.length = S.length) && xs.all (fun n => decide (n < 4))

def rawReply (n : Nat) : Reply :=
  if n = 0 then .alpha else if n = 1 then .beta else if n = 2 then .branch else .absent

/-- The represented input includes every natural-number tuple and every count. -/
def rawDecode (D : Nat) (S : Menu) (xs : List Nat) (k : Nat) : List Reply :=
  if rawValid S xs then decode D S (xs.map rawReply) k else List.replicate S.length .absent

def rawVector (S : Menu) (u : Source) : List Nat :=
  (initial S u).map (fun r => (replyEquiv r).val)

private theorem raw_reply_prim : Primrec rawReply := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const Reply.alpha)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const Reply.beta)
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2))
        (Primrec.const Reply.branch) (Primrec.const Reply.absent)))

private theorem raw_valid_prim (S : Menu) : Primrec (rawValid S) := by
  have hall : Primrec (fun xs : List Nat => decide (∀ n ∈ xs, n < 4)) :=
    ((Primrec.nat_lt.comp Primrec.id (Primrec.const 4)).forall_mem_list.decide)
  have he : ∀ xs : List Nat, decide (∀ n ∈ xs, n < 4) = xs.all (fun n => decide (n < 4)) := by
    intro xs
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.all_eq_true]
  exact Primrec.and.comp (Primrec.eq.comp Primrec.list_length (Primrec.const S.length)).decide
    (hall.of_eq he)

private theorem raw_decode_prim (D : Nat) (S : Menu) : Primrec₂ (rawDecode D S) := by
  apply Primrec₂.mk
  exact (Primrec.cond ((raw_valid_prim S).comp Primrec.fst)
    ((decode_prim D S).comp (Primrec.list_map Primrec.fst (raw_reply_prim.comp Primrec.snd).to₂)
      Primrec.snd) (Primrec.const (List.replicate S.length Reply.absent))).of_eq
    (fun p => by cases hh : rawValid S p.1 <;> simp [rawDecode, hh])

/-- Genuine total computability covers validation, rejected tuples, inconsistent
valid symbols, and every attained vector, with no bound on the supplied count. -/
theorem total_native_menu_decoder (D : Nat) (S : Menu) (closed : PrefixClosed S)
    (depth : ∀ q ∈ S, q.length < D) :
    Computable₂ (decode D S) ∧
    (∀ u : Source, ∀ k : Nat, decode D S (initial S u) k = future S u k) ∧
    Primrec₂ (rawDecode D S) ∧ Computable₂ (rawDecode D S) ∧
    (∀ xs k, rawValid S xs = false → rawDecode D S xs k = List.replicate S.length .absent) ∧
    (∀ xs k, restore D S (xs.map rawReply) = none →
      rawDecode D S xs k = List.replicate S.length .absent) ∧
    (∀ u : Source, ∀ k : Nat, rawDecode D S (rawVector S u) k = future S u k) ∧
    (∀ u v : Source, initial S u = initial S v → code S u = code S v) ∧
    (∀ xs t, restore D S xs = some t → height t ≤ D ∧ initial S t = xs) ∧
    (∀ xs, restore D S xs = none ↔ ¬ ∃ u : Source, initial S u = xs) := by
  have proof := raw_decode_prim D S
  refine ⟨(decode_prim D S).to_comp, ?_, proof, proof.to_comp, ?_, ?_, ?_, ?_, restore_sound D S, ?_⟩
  · intro u k
    obtain ⟨t, ht, _, _, hf⟩ := prefix_menu_reconstruction D S u
      (lookup S (initial S u)) closed depth (lookup_initial S u)
    rw [decode, restore_attained D S u, ht]
    exact List.map_congr_left (fun q hq => hf q hq k)
  · intro xs k h; simp [rawDecode, h]
  · intro xs k h
    by_cases hv : rawValid S xs = true <;> simp [rawDecode, decode, h, hv]
  · intro u k
    have hv : rawValid S (rawVector S u) = true := by
      simp only [rawValid, rawVector, initial, List.length_map, decide_true, Bool.true_and]
      apply List.all_eq_true.mpr
      intro n hn
      rcases List.mem_map.mp hn with ⟨r, _, rfl⟩
      exact decide_eq_true (replyEquiv r).isLt
    have hm : (rawVector S u).map rawReply = initial S u := by
      simp only [rawVector, List.map_map, Function.comp_def]
      have he : (fun r : Reply => rawReply (replyEquiv r).val) = id := by
        funext r; cases r <;> rfl
      rw [he, List.map_id]
    obtain ⟨t, ht, _, _, hf⟩ := prefix_menu_reconstruction D S u
      (lookup S (initial S u)) closed depth (lookup_initial S u)
    simp only [rawDecode, hv, ↓reduceIte, hm, decode]
    rw [restore_attained D S u, ht]
    exact List.map_congr_left (fun q hq => hf q hq k)
  · intro u v he
    obtain ⟨t, ht, _, hcu, _⟩ := prefix_menu_reconstruction D S u
      (lookup S (initial S u)) closed depth (lookup_initial S u)
    obtain ⟨t', ht', _, hcv, _⟩ := prefix_menu_reconstruction D S v
      (lookup S (initial S v)) closed depth (lookup_initial S v)
    rw [he, ht'] at ht
    have te : t = t' := (Option.some.inj ht).symm
    exact hcu.symm.trans (te ▸ hcv)
  · intro xs
    constructor
    · intro rejected ⟨u, hu⟩
      obtain ⟨t, ht, _, _, _⟩ := prefix_menu_reconstruction D S u
        (lookup S (initial S u)) closed depth (lookup_initial S u)
      rw [← hu, restore_attained D S u, ht] at rejected
      contradiction
    · intro impossible
      cases hr : restore D S xs with
      | none => rfl
      | some t => exact (impossible ⟨t, (restore_sound D S xs t hr).2⟩).elim

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective
