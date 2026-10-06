/- GID: D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native address geometry, leaf-report block forcing, covered recovery, and literal contexts. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout leaves Positive)
open ActualImageSevenLeafSeparation (thirdImage E A C leafAddresses)

/-- An arbitrary finite history, including repeated and nonleaf reports. -/
abbrev LeafHistory := List (Address × Reply)

/-- The positive comparison family retains only alpha and beta reports. -/
def Compatible (H : LeafHistory) (P : Source) : Prop :=
  Positive P ∧ ∀ (u : Address) (y : Reply), (u, y) ∈ H →
    (y = .alpha ∨ y = .beta) → readout u P = y

/-- Literal block kinds in the five-row leaf-report table. -/
inductive BlockKind
  | a | c
  deriving DecidableEq

/-- A block denotes the existing literal output A or C. -/
def BlockKind.tree : BlockKind → Source
  | .a => A
  | .c => C

/-- Decode only the report label and its original five possible suffixes. -/
def decodeBlock (u : Address) (y : Reply) : Option (Address × BlockKind) :=
  match y, u.reverse with
  | .beta, true :: v => some (v.reverse, .a)
  | .beta, false :: false :: v => some (v.reverse, .a)
  | .alpha, true :: false :: v => some (v.reverse, .a)
  | .beta, false :: true :: v => some (v.reverse, .c)
  | .alpha, true :: true :: v => some (v.reverse, .c)
  | _, _ => none

/-- Repeated decoded blocks occur once in the finite set. -/
def forcedBlocks (H : LeafHistory) : Finset (Address × BlockKind) :=
  (H.filterMap fun r => decodeBlock r.1 r.2).toFinset

/-- Actual alpha leaf addresses of a literal native tree. -/
def alphaLeaves (P : Source) : Finset Address :=
  (leafAddresses P).filter fun u => readout u P = .alpha

/-- Covered alphas are a set union of the prefixed alpha frontiers of decoded blocks. -/
def gamma (H : LeafHistory) : Finset Address :=
  (forcedBlocks H).biUnion fun b =>
    (alphaLeaves b.2.tree).image (b.1 ++ ·)

/-- The residual alpha set is computed in the chosen reference output tree. -/
def uncovered (H : LeafHistory) (P : Source) : Finset Address :=
  alphaLeaves P \ gamma H

/-- A finite ordered literal output context stores its actual native siblings. -/
inductive OutputContext
  | hole
  | left (inner : OutputContext) (sibling : Source)
  | right (sibling : Source) (inner : OutputContext)

/-- Filling the single hole preserves every ordered sibling and label. -/
def OutputContext.plug : OutputContext → Source → Source
  | .hole, X => X
  | .left J R, X => .mul (J.plug X) R
  | .right L J, X => .mul L (J.plug X)

/-- The empty context has its hole at the root. -/
def OutputContext.holeAddress : OutputContext → Address
  | .hole => []
  | .left J _ => false :: J.holeAddress
  | .right _ J => true :: J.holeAddress

/-- Only actual sibling leaves contribute outside the hole. -/
def OutputContext.outsideLeaves : OutputContext → Nat
  | .hole => 0
  | .left J R => J.outsideLeaves + R.length
  | .right L J => L.length + J.outsideLeaves


/-- Native subtree navigation; crossing a leaf returns no subtree. -/
def subtree : Address → Source → Option Source
  | [], p => some p
  | _ :: _, .of _ => none
  | false :: u, .mul p _ => subtree u p
  | true :: u, .mul _ q => subtree u q

/-- All existing offsets in a canonical third-image leaf block. -/
def BlockOffset (b : Bool) (z : Address) (Y : Source) : Prop :=
  if b then
    (z = [] ∧ Y = A) ∨ (z = [false] ∧ Y = E) ∨
    (z = [false, false] ∧ Y = .of false) ∨
    (z = [false, true] ∧ Y = .of true) ∨
    (z = [true] ∧ Y = .of false)
  else
    (z = [] ∧ Y = C) ∨ (z = [false] ∧ Y = A) ∨
    (z = [false, false] ∧ Y = E) ∨
    (z = [false, false, false] ∧ Y = .of false) ∨
    (z = [false, false, true] ∧ Y = .of true) ∨
    (z = [false, true] ∧ Y = .of false) ∨
    (z = [true] ∧ Y = E) ∨
    (z = [true, false] ∧ Y = .of false) ∨
    (z = [true, true] ∧ Y = .of true)

/-- A preimage branch or an actual canonical leaf block accounts for a node. -/
def ImagePosition (Q : Source) (u : Address) (Y : Source) : Prop :=
  (∃ q r, subtree u Q = some (.mul q r) ∧
    Y = .mul (thirdImage q) (thirdImage r)) ∨
  ∃ v b z, subtree v Q = some (.of b) ∧ u = v ++ z ∧ BlockOffset b z Y

set_option maxHeartbeats 1000000 in
-- Native preimage induction and complete literal offset classification share the proof budget.
/-- Complete native address classification and ambient-image small-subtree uniqueness. -/
theorem actual_address_geometry :
    (∀ (Q : Source) (u : Address) (Y : Source),
      subtree u (thirdImage Q) = some Y ↔ ImagePosition Q u Y) ∧
    (∀ (P : Source), Positive P → ∀ (u : Address) (Y : Source),
      subtree u P = some Y → (Y.length = 2 → Y = E) ∧ (Y.length = 3 → Y = A)) ∧
    (∀ (P : Source), Positive P → ∀ w : Address,
      (readout (w ++ [true]) P = .beta → subtree w P = some A) ∧
      (readout (w ++ [false, false]) P = .beta → subtree w P = some A) ∧
      (readout (w ++ [false, true]) P = .alpha → subtree w P = some A) ∧
      (readout (w ++ [true, false]) P = .beta → subtree w P = some C) ∧
      (readout (w ++ [true, true]) P = .alpha → subtree w P = some C)) ∧
    (∀ (P : Source), Positive P → ∀ (u : Address) (y : Reply),
      (y = .alpha ∨ y = .beta) → readout u P = y →
      ∃! d : Address × BlockKind,
        decodeBlock u y = some d ∧ subtree d.1 P = some d.2.tree) ∧
    (∀ (H : LeafHistory) (P : Source), Compatible H P →
      (∀ d ∈ forcedBlocks H, subtree d.1 P = some d.2.tree) ∧
      gamma H ⊆ alphaLeaves P) ∧
    (∀ (P : Source) (u v : Address) (S T : Source),
      (S = A ∨ S = C) → (T = A ∨ T = C) →
      subtree u P = some S → subtree v P = some T →
      (u = v ∧ S = T) ∨ (¬ u.IsPrefix v ∧ ¬ v.IsPrefix u) ∨
      (S = C ∧ T = A ∧ v = u ++ [false]) ∨
      (S = A ∧ T = C ∧ u = v ++ [false])) ∧
    (∀ (H : LeafHistory) (P : Source), Compatible H P →
      (uncovered H P).card = 0 → ∀ P' : Source, Compatible H P' → P' = P) ∧
    (∀ (P : Source) (u : Address), subtree u P = none ↔
      ∃ (v : Address) (b : Bool) (z : Address),
        subtree v P = some (.of b) ∧ u = v ++ z ∧ z ≠ []) ∧
    (∀ (P : Source) (u v : Address) (b c : Bool),
      subtree u P = some (.of b) → subtree v P = some (.of c) →
      u.IsPrefix v → u = v ∧ b = c) ∧
    (∀ (h : Address) (V X : Source), subtree h V = some X →
      ∃ J : OutputContext, J.holeAddress = h ∧ J.plug X = V ∧
        ∀ U : Source,
          (∀ u ∈ leaves V, ¬ h.IsPrefix u → readout u U = readout u V) →
          ∃ Y : Source, subtree h U = some Y ∧ J.plug Y = U) ∧
    (∀ (H : LeafHistory) (u : Address), u ∈ gamma H ↔
      (∃ w, (w, BlockKind.a) ∈ forcedBlocks H ∧ u = w ++ [false, true]) ∨
      (∃ w, (w, BlockKind.c) ∈ forcedBlocks H ∧
        (u = w ++ [false, false, true] ∨ u = w ++ [true, true]))) ∧
    (∀ (H : LeafHistory) (w : Address),
      (w ++ [true, true] ∈ gamma H → (w, BlockKind.c) ∈ forcedBlocks H) ∧
      (w ++ [false, true] ∈ gamma H →
        (w, BlockKind.a) ∈ forcedBlocks H ∨
        ∃ v, w = v ++ [false] ∧ (v, BlockKind.c) ∈ forcedBlocks H)) ∧
    (∀ (H : LeafHistory) (P : Source), Compatible H P →
      (uncovered H P).card = 1 → ∃ x : Address, uncovered H P = {x} ∧
        ((∃ v, subtree v P = some A ∧ x = v ++ [false, true]) ∨
         (∃ v, subtree v P = some C ∧ x = v ++ [true, true] ∧
           v ++ [false, false, true] ∈ gamma H ∧
           ∀ P' : Source, Compatible H P' → subtree (v ++ [false]) P' = some A))) ∧
    (∀ (v z : Address) (P : Source), readout (v ++ z) P =
      match subtree v P with
      | none => .absent
      | some Y => readout z Y) ∧
    (∀ (v z : Address) (P : Source),
      subtree (v ++ z) P = (subtree v P).bind (subtree z)) ∧
    (∀ (P : Source) (u : Address) (b : Bool),
      readout u P = (if b then .alpha else .beta) → subtree u P = some (.of b)) ∧
    (∀ (P : Source) (u : Address), u ∈ alphaLeaves P ↔ readout u P = .alpha) := by
  have leafEq (b c : Bool) : (FreeMagma.of b : Source) = .of c ↔ b = c := by
    constructor
    · intro h
      injection h
    · rintro rfl
      rfl
  have nodeEq (p q r s : Source) :
      FreeMagma.mul p q = .mul r s ↔ p = r ∧ q = s := by
    constructor
    · intro h
      injection h with hp hq
      exact ⟨hp, hq⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have mulImage (q r : Source) :
      thirdImage (.mul q r) = .mul (thirdImage q) (thirdImage r) :=
    Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun s t => substitution.map_mul s t) 3 q r
  have block (b : Bool) (z : Address) (Y : Source) :
      subtree z (thirdImage (.of b)) = some Y ↔ BlockOffset b z Y := by
    have atomImage (c : Bool) : thirdImage (.of c) = (if c then A else C) := by
      cases c <;> rfl
    rw [atomImage]
    cases b <;>
      cases z with
      | nil => simp [BlockOffset, A, C, E, subtree] <;> exact eq_comm
      | cons d z =>
        cases d <;> cases z with
        | nil => simp [BlockOffset, A, C, E, subtree] <;> exact eq_comm
        | cons d z =>
          cases d <;> cases z with
          | nil => simp [BlockOffset, A, C, E, subtree] <;> exact eq_comm
          | cons d z =>
            cases d <;> cases z <;>
              simp [BlockOffset, A, C, E, subtree] <;> exact eq_comm
  have classify : ∀ (Q : Source) (u : Address) (Y : Source),
      subtree u (thirdImage Q) = some Y ↔ ImagePosition Q u Y := by
    intro Q
    induction Q with
    | of b =>
      intro u Y
      constructor
      · intro h
        exact Or.inr ⟨[], b, u, rfl, rfl, (block b u Y).mp h⟩
      · rintro (⟨q, r, h, _⟩ | ⟨v, c, z, h, hu, hz⟩)
        · cases u <;> simp [subtree] at h
        · cases v with
          | nil =>
            simp only [subtree, Option.some.injEq] at h
            injection h with hc
            subst c
            simp only [List.nil_append] at hu
            subst u
            exact (block b z Y).mpr hz
          | cons d v => simp [subtree] at h
    | mul q r ihq ihr =>
      intro u Y
      constructor
      · intro h
        cases u with
        | nil =>
          rw [mulImage] at h
          simp only [subtree, Option.some.injEq] at h
          exact Or.inl ⟨q, r, rfl, h.symm⟩
        | cons d u =>
          rw [mulImage] at h
          cases d with
          | false =>
            rcases (ihq u Y).mp h with ⟨s, t, hs, hy⟩ | ⟨v, b, z, hv, hu, hz⟩
            · exact Or.inl ⟨s, t, hs, hy⟩
            · exact Or.inr ⟨false :: v, b, z, hv, congrArg (false :: ·) hu, hz⟩
          | true =>
            rcases (ihr u Y).mp h with ⟨s, t, hs, hy⟩ | ⟨v, b, z, hv, hu, hz⟩
            · exact Or.inl ⟨s, t, hs, hy⟩
            · exact Or.inr ⟨true :: v, b, z, hv, congrArg (true :: ·) hu, hz⟩
      · rintro (⟨s, t, hs, hy⟩ | ⟨v, b, z, hv, hu, hz⟩)
        · cases u with
          | nil =>
            simp only [subtree, Option.some.injEq] at hs
            injection hs with hq hr
            subst s
            subst t
            rw [mulImage, hy]
            rfl
          | cons d u =>
            rw [mulImage]
            cases d with
            | false => exact (ihq u Y).mpr (Or.inl ⟨s, t, hs, hy⟩)
            | true => exact (ihr u Y).mpr (Or.inl ⟨s, t, hs, hy⟩)
        · cases v with
          | nil => simp [subtree] at hv
          | cons d v =>
            subst u
            rw [mulImage]
            cases d with
            | false => exact (ihq (v ++ z) Y).mpr (Or.inr ⟨v, b, z, hv, rfl, hz⟩)
            | true => exact (ihr (v ++ z) Y).mpr (Or.inr ⟨v, b, z, hv, rfl, hz⟩)
  have coarse (q : Source) : 2 ≤ (thirdImage q).length := by
    cases q with
    | of b => cases b <;> decide
    | mul q r =>
      rw [mulImage]
      have hq := FreeMagma.length_pos (thirdImage q)
      have hr := FreeMagma.length_pos (thirdImage r)
      change 2 ≤ (thirdImage q).length + (thirdImage r).length
      omega
  have three (q : Source) : 3 ≤ (thirdImage q).length := by
    cases q with
    | of b => cases b <;> decide
    | mul q r =>
      rw [mulImage]
      have hq := coarse q
      have hr := coarse r
      change 3 ≤ (thirdImage q).length + (thirdImage r).length
      omega
  have small : ∀ (P : Source), Positive P → ∀ (u : Address) (Y : Source),
      subtree u P = some Y → (Y.length = 2 → Y = E) ∧ (Y.length = 3 → Y = A) := by
    intro P hP u Y hY
    obtain ⟨Q, rfl⟩ := hP
    rcases (classify Q u Y).mp hY with ⟨q, r, _, rfl⟩ | ⟨v, b, z, _, _, hz⟩
    · have hq := three q
      have hr := three r
      constructor <;> intro h <;> simp only [FreeMagma.length] at h <;> omega
    · cases b with
      | false =>
        simp only [BlockOffset, Bool.false_eq_true, if_false] at hz
        rcases hz with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        all_goals simp [A, C, E, FreeMagma.length]
      | true =>
        simp only [BlockOffset, if_true] at hz
        rcases hz with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        all_goals simp [A, C, E, FreeMagma.length]

  have readAt (v z : Address) (P : Source) :
      readout (v ++ z) P =
        match subtree v P with
        | none => .absent
        | some Y => readout z Y := by
    induction v generalizing P with
    | nil => rfl
    | cons d v ih =>
      cases P with
      | of b => rfl
      | mul p q => cases d <;> simpa [subtree, readout] using ih _
  have rootReply (q : Source) : readout [] (thirdImage q) = .branch := by
    have hq := three q
    cases h : thirdImage q with
    | of b => simp [h, FreeMagma.length] at hq
    | mul p r => rfl
  have profile (q : Source) :
      readout [false] (thirdImage q) = .branch ∧
      readout [true] (thirdImage q) ≠ .alpha := by
    cases q with
    | of b => cases b <;> decide
    | mul q r =>
      rw [mulImage]
      change readout [] (thirdImage q) = .branch ∧
        readout [] (thirdImage r) ≠ .alpha
      rw [rootReply, rootReply]
      exact ⟨rfl, by decide⟩
  have localRows (Q : Source) (w : Address) (Y : Source)
      (hY : subtree w (thirdImage Q) = some Y) :
      (readout [true] Y = .beta → Y = A) ∧
      (readout [false, false] Y = .beta → Y = A) ∧
      (readout [false, true] Y = .alpha → Y = A) ∧
      (readout [true, false] Y = .beta → Y = C) ∧
      (readout [true, true] Y = .alpha → Y = C) := by
    rcases (classify Q w Y).mp hY with ⟨q, r, _, rfl⟩ | ⟨v, b, z, _, _, hz⟩
    · change (readout [] (thirdImage r) = .beta → _) ∧
        (readout [false] (thirdImage q) = .beta → _) ∧
        (readout [true] (thirdImage q) = .alpha → _) ∧
        (readout [false] (thirdImage r) = .beta → _) ∧
        (readout [true] (thirdImage r) = .alpha → _)
      simp only [rootReply, (profile q).1, (profile q).2,
        (profile r).1, (profile r).2, reduceCtorEq, false_implies, and_self]
    · cases b with
      | false =>
        simp only [BlockOffset, Bool.false_eq_true, if_false] at hz
        rcases hz with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        all_goals simp [A, C, E, readout]
      | true =>
        simp only [BlockOffset, if_true] at hz
        rcases hz with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        all_goals simp [A, C, E, readout]
  have rows : ∀ (P : Source), Positive P → ∀ w : Address,
      (readout (w ++ [true]) P = .beta → subtree w P = some A) ∧
      (readout (w ++ [false, false]) P = .beta → subtree w P = some A) ∧
      (readout (w ++ [false, true]) P = .alpha → subtree w P = some A) ∧
      (readout (w ++ [true, false]) P = .beta → subtree w P = some C) ∧
      (readout (w ++ [true, true]) P = .alpha → subtree w P = some C) := by
    intro P hP w
    obtain ⟨Q, rfl⟩ := hP
    change (readout (w ++ [true]) (thirdImage Q) = .beta →
        subtree w (thirdImage Q) = some A) ∧
      (readout (w ++ [false, false]) (thirdImage Q) = .beta →
        subtree w (thirdImage Q) = some A) ∧
      (readout (w ++ [false, true]) (thirdImage Q) = .alpha →
        subtree w (thirdImage Q) = some A) ∧
      (readout (w ++ [true, false]) (thirdImage Q) = .beta →
        subtree w (thirdImage Q) = some C) ∧
      (readout (w ++ [true, true]) (thirdImage Q) = .alpha →
        subtree w (thirdImage Q) = some C)
    cases hw : subtree w (thirdImage Q) with
    | none => simp only [readAt, hw, reduceCtorEq, false_implies, and_self]
    | some Y =>
      have hr := localRows Q w Y hw
      simp only [readAt, hw]
      exact ⟨fun h => congrArg some (hr.1 h),
        fun h => congrArg some (hr.2.1 h),
        fun h => congrArg some (hr.2.2.1 h),
        fun h => congrArg some (hr.2.2.2.1 h),
        fun h => congrArg some (hr.2.2.2.2 h)⟩
  have decodeCorrect (P : Source) (hP : Positive P) (u : Address) (y : Reply)
      (w : Address) (k : BlockKind) (hy : readout u P = y)
      (hd : decodeBlock u y = some (w, k)) : subtree w P = some k.tree := by
    cases y with
    | branch => simp [decodeBlock] at hd
    | absent => simp [decodeBlock] at hd
    | beta =>
      cases hu : u.reverse with
      | nil => simp [decodeBlock, hu] at hd
      | cons d v =>
        cases d with
        | true =>
          simp only [decodeBlock, hu, Option.some.injEq, Prod.mk.injEq] at hd
          rcases hd with ⟨hw, hk⟩
          subst w
          subst k
          have he : u = v.reverse ++ [true] := by
            simpa using congrArg List.reverse hu
          exact (rows P hP v.reverse).1 (by simpa only [he] using hy)
        | false =>
          cases v with
          | nil => simp [decodeBlock, hu] at hd
          | cons d v =>
            cases d with
            | false =>
              simp only [decodeBlock, hu, Option.some.injEq, Prod.mk.injEq] at hd
              rcases hd with ⟨hw, hk⟩
              subst w
              subst k
              have he : u = v.reverse ++ [false, false] := by
                simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hu
              exact (rows P hP v.reverse).2.1 (by simpa only [he] using hy)
            | true =>
              simp only [decodeBlock, hu, Option.some.injEq, Prod.mk.injEq] at hd
              rcases hd with ⟨hw, hk⟩
              subst w
              subst k
              have he : u = v.reverse ++ [true, false] := by
                simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hu
              exact (rows P hP v.reverse).2.2.2.1 (by simpa only [he] using hy)
    | alpha =>
      cases hu : u.reverse with
      | nil => simp [decodeBlock, hu] at hd
      | cons d v =>
        cases d with
        | false => simp [decodeBlock, hu] at hd
        | true =>
          cases v with
          | nil => simp [decodeBlock, hu] at hd
          | cons d v =>
            cases d with
            | false =>
              simp only [decodeBlock, hu, Option.some.injEq, Prod.mk.injEq] at hd
              rcases hd with ⟨hw, hk⟩
              subst w
              subst k
              have he : u = v.reverse ++ [false, true] := by
                simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hu
              exact (rows P hP v.reverse).2.2.1 (by simpa only [he] using hy)
            | true =>
              simp only [decodeBlock, hu, Option.some.injEq, Prod.mk.injEq] at hd
              rcases hd with ⟨hw, hk⟩
              subst w
              subst k
              have he : u = v.reverse ++ [true, true] := by
                simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hu
              exact (rows P hP v.reverse).2.2.2.2 (by simpa only [he] using hy)
  have leafNode (P : Source) (u : Address) (b : Bool)
      (hr : readout u P = if b then .alpha else .beta) :
      subtree u P = some (.of b) := by
    have he := readAt u [] P
    simp only [List.append_nil] at he
    rw [he] at hr
    cases hs : subtree u P with
    | none => cases b <;> simp [hs] at hr
    | some Y =>
      rw [hs] at hr
      cases Y with
      | of c => cases b <;> cases c <;> simp [readout] at hr ⊢
      | mul p q => cases b <;> simp [readout] at hr
  have reportExists (Q : Source) (u : Address) (b : Bool)
      (hu : subtree u (thirdImage Q) = some (.of b)) :
      ∃ d, decodeBlock u (if b then .alpha else .beta) = some d := by
    rcases (classify Q u (.of b)).mp hu with ⟨q, r, _, hy⟩ | ⟨v, c, z, _, he, hz⟩
    · cases hy
    · subst u
      cases c with
      | false =>
        cases b with
        | false =>
          simp [BlockOffset, A, C, E, leafEq, nodeEq] at hz
          rcases hz with rfl | rfl | rfl
          · exact ⟨(v ++ [false], .a), by simp [decodeBlock, List.reverse_append]⟩
          · exact ⟨(v ++ [false], .a), by simp [decodeBlock, List.reverse_append]⟩
          · exact ⟨(v, .c), by simp [decodeBlock, List.reverse_append]⟩
        | true =>
          simp [BlockOffset, A, C, E, leafEq, nodeEq] at hz
          rcases hz with rfl | rfl
          · exact ⟨(v ++ [false], .a), by simp [decodeBlock, List.reverse_append]⟩
          · exact ⟨(v, .c), by simp [decodeBlock, List.reverse_append]⟩
      | true =>
        cases b with
        | false =>
          simp [BlockOffset, A, C, E, leafEq, nodeEq] at hz
          rcases hz with rfl | rfl
          · exact ⟨(v, .a), by simp [decodeBlock, List.reverse_append]⟩
          · exact ⟨(v, .a), by simp [decodeBlock, List.reverse_append]⟩
        | true =>
          simp [BlockOffset, A, C, E, leafEq, nodeEq] at hz
          subst z
          exact ⟨(v, .a), by simp [decodeBlock, List.reverse_append]⟩
  have reportForcing (P : Source) (hP : Positive P) (u : Address) (y : Reply)
      (hl : y = .alpha ∨ y = .beta) (hy : readout u P = y) :
      ∃! d : Address × BlockKind,
        decodeBlock u y = some d ∧ subtree d.1 P = some d.2.tree := by
    have hd : ∃ d, decodeBlock u y = some d := by
      obtain ⟨Q, rfl⟩ := hP
      rcases hl with rfl | rfl
      · exact reportExists Q u true (leafNode _ u true hy)
      · exact reportExists Q u false (leafNode _ u false hy)
    obtain ⟨⟨w, k⟩, hd⟩ := hd
    refine ⟨(w, k), ⟨hd, decodeCorrect P hP u y w k hy hd⟩, ?_⟩
    intro d hd'
    exact Option.some.inj (hd'.1.symm.trans hd)
  have historyBlocks (H : LeafHistory) (P : Source) (hP : Compatible H P)
      (d : Address × BlockKind) (hd : d ∈ forcedBlocks H) :
      subtree d.1 P = some d.2.tree := by
    have hd' : d ∈ H.filterMap (fun r => decodeBlock r.1 r.2) := by
      simpa only [forcedBlocks, List.mem_toFinset] using hd
    obtain ⟨⟨u, y⟩, hmem, hdec⟩ := List.mem_filterMap.mp hd'
    have hl : y = .alpha ∨ y = .beta := by
      cases y with
      | alpha => exact Or.inl rfl
      | beta => exact Or.inr rfl
      | branch => simp [decodeBlock] at hdec
      | absent => simp [decodeBlock] at hdec
    exact decodeCorrect P hP.1 u y d.1 d.2 (hP.2 u y hmem hl) hdec
  have appendSubtree (v z : Address) (P : Source) :
      subtree (v ++ z) P = (subtree v P).bind (subtree z) := by
    induction v generalizing P with
    | nil => rfl
    | cons d v ih =>
      cases P with
      | of b => simp [subtree]
      | mul p q => cases d <;> simpa [subtree] using ih _
  have within (S T : Source) (hS : S = A ∨ S = C) (hT : T = A ∨ T = C)
      (z : Address) (hz : subtree z S = some T) :
      (z = [] ∧ S = T) ∨ (z = [false] ∧ S = C ∧ T = A) := by
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;>
      cases z with
      | nil => simp only [subtree, A, C, E, Option.some.injEq, leafEq, nodeEq, reduceCtorEq] at hz ⊢ <;> simp at hz ⊢
      | cons d z =>
        cases d <;> cases z with
        | nil => simp only [subtree, A, C, E, Option.some.injEq, leafEq, nodeEq, reduceCtorEq] at hz ⊢ <;> simp at hz ⊢
        | cons d z =>
          cases d <;> cases z with
          | nil => simp only [subtree, A, C, E, Option.some.injEq, leafEq, nodeEq, reduceCtorEq] at hz ⊢ <;> simp at hz ⊢
          | cons d z =>
            cases d <;> cases z <;> simp only [subtree, A, C, E, Option.some.injEq, leafEq, nodeEq, reduceCtorEq] at hz ⊢ <;> simp at hz ⊢
  have overlap (P : Source) (u v : Address) (S T : Source)
      (hS : S = A ∨ S = C) (hT : T = A ∨ T = C)
      (hu : subtree u P = some S) (hv : subtree v P = some T) :
      (u = v ∧ S = T) ∨ (¬ u.IsPrefix v ∧ ¬ v.IsPrefix u) ∨
      (S = C ∧ T = A ∧ v = u ++ [false]) ∨
      (S = A ∧ T = C ∧ u = v ++ [false]) := by
    by_cases huv : u.IsPrefix v
    · have he := List.prefix_append_drop huv
      have hst : subtree (v.drop u.length) S = some T := by
        have h := hv
        rw [he, appendSubtree, hu] at h
        exact h
      rcases within S T hS hT _ hst with ⟨hz, hST⟩ | ⟨hz, hSC, hTA⟩
      · rw [hz, List.append_nil] at he
        exact Or.inl ⟨he.symm, hST⟩
      · rw [hz] at he
        exact Or.inr (Or.inr (Or.inl ⟨hSC, hTA, he⟩))
    · by_cases hvu : v.IsPrefix u
      · have he := List.prefix_append_drop hvu
        have hts : subtree (u.drop v.length) T = some S := by
          have h := hu
          rw [he, appendSubtree, hv] at h
          exact h
        rcases within T S hT hS _ hts with ⟨hz, hTS⟩ | ⟨hz, hTC, hSA⟩
        · rw [hz, List.append_nil] at he
          exact Or.inl ⟨he, hTS.symm⟩
        · rw [hz] at he
          exact Or.inr (Or.inr (Or.inr ⟨hSA, hTC, he⟩))
      · exact Or.inr (Or.inl ⟨huv, hvu⟩)
  have historyLaw : ∀ (H : LeafHistory) (P : Source), Compatible H P →
      (∀ d ∈ forcedBlocks H, subtree d.1 P = some d.2.tree) ∧
      gamma H ⊆ alphaLeaves P := by
    intro H P hP
    refine ⟨historyBlocks H P hP, ?_⟩
    intro u hu
    obtain ⟨d, hd, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hvα : readout v d.2.tree = .alpha := (Finset.mem_filter.mp hv).2
    have hα : readout (d.1 ++ v) P = .alpha := by
      rw [readAt, historyBlocks H P hP d hd]
      exact hvα
    apply Finset.mem_filter.mpr
    refine ⟨?_, hα⟩
    exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 (d.1 ++ v) |>.mpr
      ⟨true, by simp only [ActualImageSevenLeafSeparation.leafLabel, hα]⟩
  have alphaSem (P : Source) (u : Address) :
      u ∈ alphaLeaves P ↔ readout u P = .alpha := by
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · intro hu
      apply Finset.mem_filter.mpr
      refine ⟨?_, hu⟩
      exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 u |>.mpr
        ⟨true, by simp only [ActualImageSevenLeafSeparation.leafLabel, hu]⟩
  have zeroRecovery (H : LeafHistory) (P : Source) (hP : Compatible H P)
      (hz : (uncovered H P).card = 0) : ∀ P' : Source, Compatible H P' → P' = P := by
    have hempty : alphaLeaves P \ gamma H = ∅ := Finset.card_eq_zero.mp hz
    have hcover : alphaLeaves P ⊆ gamma H := Finset.sdiff_eq_empty_iff_subset.mp hempty
    intro P' hP'
    have gammaRead (u : Address) (hu : u ∈ gamma H) : readout u P' = .alpha :=
      (alphaSem P' u).mp ((historyLaw H P' hP').2 hu)
    have frontier : ∀ (Q : Source) (v : Address),
        subtree v P = some (thirdImage Q) →
        ∀ u ∈ leaves (thirdImage Q), readout (v ++ u) P' = readout u (thirdImage Q) := by
      intro Q
      induction Q with
      | of b =>
        intro v hv
        cases b with
        | false =>
          change subtree v P = some C at hv
          have hc : readout (v ++ [true, true]) P' = .alpha := by
            apply gammaRead
            apply hcover
            apply (alphaSem P _).mpr
            rw [readAt, hv]
            rfl
          have hfixed := (rows P' hP'.1 v).2.2.2.2 hc
          intro u _
          rw [readAt, hfixed]
          rfl
        | true =>
          change subtree v P = some A at hv
          have hc : readout (v ++ [false, true]) P' = .alpha := by
            apply gammaRead
            apply hcover
            apply (alphaSem P _).mpr
            rw [readAt, hv]
            rfl
          have hfixed := (rows P' hP'.1 v).2.2.1 hc
          intro u _
          rw [readAt, hfixed]
          rfl
      | mul q r ihq ihr =>
        intro v hv u hu
        rw [mulImage] at hv hu ⊢
        simp only [leaves, List.mem_append, List.mem_map] at hu
        rcases hu with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · have hvq : subtree (v ++ [false]) P = some (thirdImage q) := by
            rw [appendSubtree, hv]
            rfl
          change readout (v ++ (false :: t)) P' = readout t (thirdImage q)
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            ihq (v ++ [false]) hvq t ht
        · have hvr : subtree (v ++ [true]) P = some (thirdImage r) := by
            rw [appendSubtree, hv]
            rfl
          change readout (v ++ (true :: t)) P' = readout t (thirdImage r)
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            ihr (v ++ [true]) hvr t ht
    obtain ⟨Q, hQ⟩ := hP.1
    change thirdImage Q = P at hQ
    apply ActualTreeReadoutAcquisition.source_foundation.2.2.1 P P'
    intro u hu
    have hroot : subtree [] P = some (thirdImage Q) := by rw [hQ]; rfl
    have h := frontier Q [] hroot u (by simpa only [hQ] using hu)
    simpa only [List.nil_append, hQ] using h
  have absent : ∀ (P : Source) (u : Address), subtree u P = none ↔
      ∃ (v : Address) (b : Bool) (z : Address),
        subtree v P = some (.of b) ∧ u = v ++ z ∧ z ≠ [] := by
    intro P
    induction P with
    | of b =>
      intro u
      constructor
      · intro h
        cases u with
        | nil => simp [subtree] at h
        | cons d u => exact ⟨[], b, d :: u, rfl, rfl, by simp⟩
      · rintro ⟨v, c, z, hv, hu, hz⟩
        subst u
        rw [appendSubtree, hv]
        cases z with
        | nil => exact False.elim (hz rfl)
        | cons d z => rfl
    | mul p q ihp ihq =>
      intro u
      constructor
      · intro h
        cases u with
        | nil => simp [subtree] at h
        | cons d u =>
          cases d with
          | false =>
            obtain ⟨v, b, z, hv, hu, hz⟩ := (ihp u).mp h
            exact ⟨false :: v, b, z, hv, congrArg (false :: ·) hu, hz⟩
          | true =>
            obtain ⟨v, b, z, hv, hu, hz⟩ := (ihq u).mp h
            exact ⟨true :: v, b, z, hv, congrArg (true :: ·) hu, hz⟩
      · rintro ⟨v, b, z, hv, hu, hz⟩
        subst u
        rw [appendSubtree, hv]
        cases z with
        | nil => exact False.elim (hz rfl)
        | cons d z => rfl
  have leafPrefix (P : Source) (u v : Address) (b c : Bool)
      (hu : subtree u P = some (.of b)) (hv : subtree v P = some (.of c))
      (hprefix : u.IsPrefix v) : u = v ∧ b = c := by
    have he := List.prefix_append_drop hprefix
    have h : subtree (v.drop u.length) (.of b) = some (.of c) := by
      have h := hv
      rw [he, appendSubtree, hu] at h
      exact h
    cases hd : v.drop u.length with
    | nil =>
      simp only [hd, List.append_nil] at he
      simp only [hd, subtree, Option.some.injEq, leafEq] at h
      exact ⟨he.symm, h⟩
    | cons d z => simp [hd, subtree] at h
  have leafReply (V : Source) (u : Address) (hu : u ∈ leaves V) :
      readout u V = .alpha ∨ readout u V = .beta := by
    have hm : u ∈ leafAddresses V := by
      simpa only [leafAddresses, List.mem_toFinset] using hu
    obtain ⟨b, hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 V).2 u |>.mp hm
    cases hr : readout u V with
    | alpha => exact Or.inl rfl
    | beta => exact Or.inr rfl
    | branch => simp [ActualImageSevenLeafSeparation.leafLabel, hr] at hb
    | absent => simp [ActualImageSevenLeafSeparation.leafLabel, hr] at hb
  have someLeaf (V : Source) : ∃ u, u ∈ leaves V := by
    have hc : 0 < (leafAddresses V).card := by
      rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.1 V).1]
      exact FreeMagma.length_pos V
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hc
    exact ⟨u, by simpa only [leafAddresses, List.mem_toFinset] using hu⟩
  have contextRecovery : ∀ (h : Address) (V X : Source), subtree h V = some X →
      ∃ J : OutputContext, J.holeAddress = h ∧ J.plug X = V ∧
        ∀ U : Source,
          (∀ u ∈ leaves V, ¬ h.IsPrefix u → readout u U = readout u V) →
          ∃ Y : Source, subtree h U = some Y ∧ J.plug Y = U := by
    intro h
    induction h with
    | nil =>
      intro V X hv
      have hVX : V = X := Option.some.inj hv
      refine ⟨.hole, rfl, hVX.symm, ?_⟩
      intro U _
      exact ⟨U, rfl, rfl⟩
    | cons d h ih =>
      intro V X hv
      cases V with
      | of b => simp [subtree] at hv
      | mul L R =>
        cases d with
        | false =>
          obtain ⟨J, haddr, hplug, hrec⟩ := ih L X hv
          refine ⟨.left J R, congrArg (false :: ·) haddr,
            congrArg (fun l => FreeMagma.mul l R) hplug, ?_⟩
          intro U hm
          cases U with
          | of b =>
            obtain ⟨u, hu⟩ := someLeaf R
            have hfull : true :: u ∈ leaves (.mul L R) := by
              simp [leaves, List.mem_map, hu]
            have hnot : ¬ (false :: h).IsPrefix (true :: u) := by
              simp [List.cons_prefix_cons]
            have he := hm (true :: u) hfull hnot
            change Reply.absent = readout u R at he
            rcases leafReply R u hu with hl | hl <;> rw [hl] at he <;> cases he
          | mul L' R' =>
            have hR : R' = R := by
              apply ActualTreeReadoutAcquisition.source_foundation.2.2.1 R R'
              intro u hu
              apply hm (true :: u)
              · simp [leaves, List.mem_map, hu]
              · simp [List.cons_prefix_cons]
            have hmatch : ∀ u ∈ leaves L, ¬ h.IsPrefix u →
                readout u L' = readout u L := by
              intro u hu hn
              apply hm (false :: u)
              · simp [leaves, List.mem_map, hu]
              · simpa [List.cons_prefix_cons] using hn
            obtain ⟨Y, hat, he⟩ := hrec L' hmatch
            refine ⟨Y, hat, ?_⟩
            change FreeMagma.mul (J.plug Y) R = .mul L' R'
            rw [he, hR]
        | true =>
          obtain ⟨J, haddr, hplug, hrec⟩ := ih R X hv
          refine ⟨.right L J, congrArg (true :: ·) haddr,
            congrArg (fun r => FreeMagma.mul L r) hplug, ?_⟩
          intro U hm
          cases U with
          | of b =>
            obtain ⟨u, hu⟩ := someLeaf L
            have hfull : false :: u ∈ leaves (.mul L R) := by
              simp [leaves, List.mem_map, hu]
            have hnot : ¬ (true :: h).IsPrefix (false :: u) := by
              simp [List.cons_prefix_cons]
            have he := hm (false :: u) hfull hnot
            change Reply.absent = readout u L at he
            rcases leafReply L u hu with hl | hl <;> rw [hl] at he <;> cases he
          | mul L' R' =>
            have hL : L' = L := by
              apply ActualTreeReadoutAcquisition.source_foundation.2.2.1 L L'
              intro u hu
              apply hm (false :: u)
              · simp [leaves, List.mem_map, hu]
              · simp [List.cons_prefix_cons]
            have hmatch : ∀ u ∈ leaves R, ¬ h.IsPrefix u →
                readout u R' = readout u R := by
              intro u hu hn
              apply hm (true :: u)
              · simp [leaves, List.mem_map, hu]
              · simpa [List.cons_prefix_cons] using hn
            obtain ⟨Y, hat, he⟩ := hrec R' hmatch
            refine ⟨Y, hat, ?_⟩
            change FreeMagma.mul L (J.plug Y) = .mul L' R'
            rw [he, hL]
  have gammaShape (H : LeafHistory) (u : Address) :
      u ∈ gamma H ↔
      (∃ w, (w, BlockKind.a) ∈ forcedBlocks H ∧ u = w ++ [false, true]) ∨
      (∃ w, (w, BlockKind.c) ∈ forcedBlocks H ∧
        (u = w ++ [false, false, true] ∨ u = w ++ [true, true])) := by
    constructor
    · intro hu
      obtain ⟨⟨w, k⟩, hk, hv⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hv
      cases k with
      | a =>
        simp [alphaLeaves, BlockKind.tree, A, E, leafAddresses, leaves] at hv
        have hv' : v = [false, true] := by
          rcases hv with ⟨rfl | rfl | rfl, hr⟩
          all_goals first | rfl | cases hr
        subst v
        exact Or.inl ⟨w, hk, he.symm⟩
      | c =>
        simp [alphaLeaves, BlockKind.tree, A, C, E, leafAddresses, leaves] at hv
        have hv' : v = [false, false, true] ∨ v = [true, true] := by
          rcases hv with ⟨rfl | rfl | rfl | rfl | rfl, hr⟩
          all_goals first | exact Or.inl rfl | exact Or.inr rfl | cases hr
        rcases hv' with rfl | rfl
        · exact Or.inr ⟨w, hk, Or.inl he.symm⟩
        · exact Or.inr ⟨w, hk, Or.inr he.symm⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl | rfl⟩)
      all_goals
        apply Finset.mem_biUnion.mpr
        refine ⟨(w, _), hw, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨_, ?_, rfl⟩
        simp [alphaLeaves, BlockKind.tree, A, C, E, leafAddresses, leaves, readout]
  have gammaBlocks (H : LeafHistory) (w : Address) :
      (w ++ [true, true] ∈ gamma H → (w, BlockKind.c) ∈ forcedBlocks H) ∧
      (w ++ [false, true] ∈ gamma H →
        (w, BlockKind.a) ∈ forcedBlocks H ∨
        ∃ v, w = v ++ [false] ∧ (v, BlockKind.c) ∈ forcedBlocks H) := by
    constructor
    · intro hw
      rcases (gammaShape H _).mp hw with ⟨v, hv, he⟩ | ⟨v, hv, he | he⟩
      · have hr := congrArg List.reverse he
        simp [List.reverse_append] at hr
      · have hr := congrArg List.reverse he
        simp [List.reverse_append] at hr
      · have he' : w = v := List.append_left_injective [true, true] he
        simpa [he'] using hv
    · intro hw
      rcases (gammaShape H _).mp hw with ⟨v, hv, he⟩ | ⟨v, hv, he | he⟩
      · exact Or.inl (by simpa [List.append_left_injective [false, true] he] using hv)
      · have he' : w = v ++ [false] :=
          List.append_left_injective [false, true] (by simpa [List.append_assoc] using he)
        exact Or.inr ⟨v, he', hv⟩
      · have hr := congrArg List.reverse he
        simp [List.reverse_append] at hr
  have singletonPosition (H : LeafHistory) (P : Source) (hP : Compatible H P)
      (hc : (uncovered H P).card = 1) : ∃ x : Address, uncovered H P = {x} ∧
        ((∃ v, subtree v P = some A ∧ x = v ++ [false, true]) ∨
         (∃ v, subtree v P = some C ∧ x = v ++ [true, true] ∧
           v ++ [false, false, true] ∈ gamma H ∧
           ∀ P' : Source, Compatible H P' → subtree (v ++ [false]) P' = some A)) := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have hxm : x ∈ uncovered H P := by rw [hx]; simp
    have hxα := (Finset.mem_sdiff.mp hxm).1
    have hxng := (Finset.mem_sdiff.mp hxm).2
    have other (u : Address) (hu : u ∈ alphaLeaves P) (hne : u ≠ x) :
        u ∈ gamma H := by
      by_contra hn
      have hm : u ∈ uncovered H P := Finset.mem_sdiff.mpr ⟨hu, hn⟩
      rw [hx] at hm
      exact hne (Finset.mem_singleton.mp hm)
    obtain ⟨Q, hQ⟩ := hP.1
    change thirdImage Q = P at hQ
    have hleaf : subtree x (thirdImage Q) = some (.of true) := by
      rw [hQ]
      exact leafNode P x true ((alphaSem P x).mp hxα)
    refine ⟨x, hx, ?_⟩
    rcases (classify Q x (.of true)).mp hleaf with ⟨q, r, _, hbad⟩ | ⟨v, b, z, hv, he, hz⟩
    · cases hbad
    · have hvout : subtree v P = some (thirdImage (.of b)) := by
        rw [← hQ]
        apply (classify Q v _).mpr
        exact Or.inr ⟨v, b, [], hv, by simp, (block b [] _).mp rfl⟩
      cases b with
      | true =>
        simp [BlockOffset, A, C, E, leafEq] at hz
        subst z
        exact Or.inl ⟨v, hvout, he⟩
      | false =>
        change subtree v P = some C at hvout
        simp [BlockOffset, A, C, E, leafEq] at hz
        rcases hz with rfl | rfl
        · have hright : v ++ [true, true] ∈ gamma H := by
            apply other
            · apply (alphaSem P _).mpr
              rw [readAt, hvout]
              rfl
            · rw [he]
              intro hh
              have hr := congrArg List.reverse hh
              simp [List.reverse_append] at hr
          have hb := (gammaBlocks H v).1 hright
          have hleft : x ∈ gamma H := by
            apply (gammaShape H x).mpr
            exact Or.inr ⟨v, hb, Or.inl he⟩
          exact False.elim (hxng hleft)
        · have hleft : v ++ [false, false, true] ∈ gamma H := by
            apply other
            · apply (alphaSem P _).mpr
              rw [readAt, hvout]
              rfl
            · rw [he]
              intro hh
              have hr := congrArg List.reverse hh
              simp [List.reverse_append] at hr
          refine Or.inr ⟨v, hvout, he, hleft, ?_⟩
          intro P' hP'
          apply (rows P' hP'.1 (v ++ [false])).2.2.1
          have hα := (alphaSem P' _).mp ((historyLaw H P' hP').2 hleft)
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hα
  exact ⟨classify, small, rows, reportForcing, historyLaw, overlap, zeroRecovery,
    absent, leafPrefix, contextRecovery, gammaShape, gammaBlocks, singletonPosition,
    readAt, appendSubtree, leafNode, alphaSem⟩

end D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity

#print axioms D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.actual_address_geometry
