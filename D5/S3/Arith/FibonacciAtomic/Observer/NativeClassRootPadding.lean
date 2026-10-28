/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Deep finite image fillings and exact native query reduction to class roots. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualImageSevenLeafSeparation (leafLabel)
open ActualCutPartitionRecovery (LiteralRow evaluateRow CutSet CutPrefixFree canonicalRow)
open NativeCutFibers
open NativeClassRootImage

/-- The constructor reply associated with a reached class root. -/
def rootReply : Option Bool → Reply
  | some true => .alpha
  | some false => .beta
  | none => .branch

/-- Exterior navigation uses a constant reply or the type of the first class
entered. A nonempty suffix is absent at a leaf and a branch in a deep class. -/
def queryReply (θ : Nat → Option Bool) : Address → LiteralRow → Reply
  | a, .of (.inl b) => readout a (.of b)
  | [], .of (.inr n) => rootReply (θ n)
  | _ :: _, .of (.inr n) => if θ n = none then .branch else .absent
  | [], .mul _ _ => .branch
  | false :: a, .mul l _ => queryReply θ a l
  | true :: a, .mul _ r => queryReply θ a r

/-- All native addresses through the inclusive bound are reached branches
inside every branch-valued appearing class. -/
def DeepValues (C : LiteralRow) (L : Nat) (v : Classes C → Source) : Prop :=
  ∀ d, rootType (v d) = none → ∀ a : Address,
    a.length ≤ L → readout a (v d) = .branch

def pad : Nat → Source → Source
  | 0, t => t
  | n+1, t => .mul (pad n t) (pad n t)

private theorem pad_injective (n : Nat) : Function.Injective (pad n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
      intro s t h
      exact ih (by injection h)

private theorem pad_image (n : Nat) (t : Source) (ht : Image t) : Image (pad n t) := by
  induction n with
  | zero => exact ht
  | succ n ih =>
      obtain ⟨u,hu⟩ := ih
      exact ⟨.mul u u, by simp only [FreeMagma.mul_eq, map_mul, hu, pad]⟩

private theorem pad_reply (n : Nat) (t : Source) (a : Address)
    (h : a.length < n) : readout a (pad n t) = .branch := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
      cases a with
      | nil => rfl
      | cons b a =>
          have ha : a.length < n := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using h
          cases b <;> exact ih a ha

private theorem padded_values (C : LiteralRow) (L : Nat)
    (θ : Classes C → Option Bool) (ha : Admissible C θ) :
    ∃ v : ImageValues C, types C v.val.val = θ ∧ DeepValues C L v.val.val := by
  classical
  let e := Fintype.equivFin (Classes C)
  let k := Fintype.card (Classes C)
  let w (d : Classes C) := pad (L+1) (substitution (NativeGroundSeparation.code k (e d)))
  have wr (d : Classes C) : rootType (w d) = none := rfl
  have wi : Function.Injective w := by
    intro d c h
    have hs : Function.Injective substitution :=
      SourceTransportCentralizer.source_transport_centralizer.2.2.1 substitution
        ⟨substitution.map_mul, fun _ => rfl⟩
    exact e.injective (NativeGroundSeparation.code_injective k
      (hs (pad_injective (L+1) h)))
  have wm (d : Classes C) : Image (w d) :=
    pad_image (L+1) _ ⟨_,rfl⟩
  let v (d : Classes C) : Source := match θ d with
    | some b => .of b
    | none => w d
  have vt (d : Classes C) : rootType (v d) = θ d := by
    dsimp [v]
    cases h : θ d with
    | none => exact wr d
    | some b => cases b <;> rfl
  have vi : Function.Injective v := by
    intro d c h
    have rt : θ d = θ c := (vt d).symm.trans ((congrArg rootType h).trans (vt c))
    cases hd : θ d with
    | none =>
        have hc : θ c = none := rt.symm.trans hd
        apply wi
        simpa [v,hd,hc] using h
    | some b =>
        have hc : θ c = some b := rt.symm.trans hd
        have bound : (Finset.univ.filter (fun d => θ d = some b)).card ≤ 1 := by
          cases b
          · exact ha.2.2
          · exact ha.2.1
        exact Finset.card_le_one.mp bound d (by simp [hd]) c (by simp [hc])
  have roots : (fun n => rootType (extend C v n)) = typeExtend C θ := by
    funext n
    by_cases hn : n ∈ labels C
    · simpa [extend,typeExtend,hn] using vt ⟨n,hn⟩
    · simp [extend,typeExtend,hn,rootType,leafLabel,readout]
  have image : Image (evaluateRow (extend C v) C) := by
    apply (filling_image_iff C _).mpr
    refine ⟨?_, by rw [roots]; exact ha.1⟩
    intro n hn hr
    let d : Classes C := ⟨n,hn⟩
    have hd : θ d = none := by simpa [extend,hn,← vt d] using hr
    simpa [extend,hn,v,hd,d] using wm d
  refine ⟨⟨⟨v,vi⟩,image⟩,funext vt,?_⟩
  intro d hd a hlen
  have ht : θ d = none := (vt d).symm.trans hd
  have hp := pad_reply (L+1) (substitution (NativeGroundSeparation.code k (e d))) a (by omega)
  simpa [v,ht,w] using hp

private theorem query_reply (C : LiteralRow) (L : Nat) (f : Nat → Source)
    (deep : ∀ n ∈ labels C, rootType (f n) = none →
      ∀ a : Address, a.length ≤ L → readout a (f n) = .branch)
    (a : Address) (hlen : a.length ≤ L) :
    readout a (evaluateRow f C) =
      queryReply (fun n => rootType (f n)) a C := by
  induction C generalizing a with
  | of c => cases c with
    | inl b => cases a <;> rfl
    | inr n =>
        cases hf : f n with
        | of b =>
            cases a <;> cases b <;>
              simp [evaluateRow,hf,queryReply,rootReply,rootType,leafLabel,readout]
        | mul l r =>
            have hroot : rootType (f n) = none := by simp [hf,rootType,leafLabel,readout]
            have h := deep n (by simp [labels]) hroot a hlen
            cases a with
            | nil => simp [evaluateRow,hf,queryReply,rootReply,rootType,leafLabel,readout]
            | cons b a =>
                simpa [evaluateRow,hf,queryReply,rootType,leafLabel,readout] using h
  | mul l r ihl ihr =>
      have dl : ∀ n ∈ labels l, rootType (f n) = none →
          ∀ a : Address, a.length ≤ L → readout a (f n) = .branch :=
        fun n hn => deep n (Finset.mem_union_left _ hn)
      have dr : ∀ n ∈ labels r, rootType (f n) = none →
          ∀ a : Address, a.length ≤ L → readout a (f n) = .branch :=
        fun n hn => deep n (Finset.mem_union_right _ hn)
      cases a with
      | nil => rfl
      | cons b a =>
          have ha : a.length ≤ L := by simp only [List.length_cons] at hlen; omega
          cases b
          · exact ihl dl a ha
          · exact ihr dr a ha

/-- Every admissible class-root assignment has an actual finite image filling
with arbitrary uniform branch depth, and every bounded native query on that
same image agrees with the finite exterior/root-type rule. -/
theorem padded_native_query_chart (P : CutSet) (hP : CutPrefixFree P)
    (t₀ : Source) (L : Nat) (θ : Classes (canonicalRow P t₀) → Option Bool)
    (ha : Admissible (canonicalRow P t₀) θ) :
    ∃ v : ImageValues (canonicalRow P t₀), ∃ u : OriginFiber P (canonicalRow P t₀),
      substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀) ∧
      types (canonicalRow P t₀) v.val.val = θ ∧
      DeepValues (canonicalRow P t₀) L v.val.val ∧
      ∀ a : Address, a.length ≤ L →
        readout a (substitution u.val) =
          queryReply (typeExtend (canonicalRow P t₀) θ) a (canonicalRow P t₀) := by
  let C := canonicalRow P t₀
  obtain ⟨v,ht,hd⟩ := padded_values C L θ ha
  obtain ⟨u,hu⟩ := v.property
  have row : canonicalRow P (substitution u) = C := by
    rw [hu]
    exact legal_values_row P hP t₀ v.val
  refine ⟨v,⟨u,row⟩,hu,ht,hd,?_⟩
  intro a hlen
  rw [hu]
  have roots : (fun n => rootType (extend C v.val.val n)) = typeExtend C θ := by
    funext n
    by_cases hn : n ∈ labels C
    · simpa [extend,typeExtend,types,hn] using congrFun ht ⟨n,hn⟩
    · simp [extend,typeExtend,hn,rootType,leafLabel,readout]
  rw [← roots]
  apply query_reply C L _ _ a hlen
  intro n hn hr a hlen
  have hr' : rootType (v.val.val ⟨n,hn⟩) = none := by simpa [extend,hn] using hr
  simpa [extend,hn] using hd ⟨n,hn⟩ hr' a hlen

#print axioms padded_native_query_chart
end D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
