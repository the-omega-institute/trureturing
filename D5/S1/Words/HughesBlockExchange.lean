/- GID: D5/S1/Words/HughesBlockExchange
   generality: G
   mirror-B: D5/B/S1/Words/HughesBlockExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual source masks determine the maximal separating block exchange obstruction. -/

import D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Nat.Find
import Mathlib.Order.WithBot
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.HughesBlockExchange

open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation

variable {α : Type*}

/-- The ordered letters assigned to one source; exact lengths are checked separately. -/
def projection (q : Side) (w : List α) (s : List Side) : List α :=
  (w.zip s).filterMap (fun p => if p.2 = q then some p.1 else none)

/-- Native source validity includes evaluation to the actual word. -/
def ValidMask (u v w : List α) (s : List Side) : Prop :=
  ValidTwoSchedule u v s ∧ evaluateTwo u v s = some w

private theorem shifted_read (u v : List α) (i j : Nat) (s : List Side) :
    (annotateTwoFrom i j s).mapM (readTwo u v) =
      evaluateTwo (u.drop i) (v.drop j) s := by
  rw [show annotateTwoFrom i j s = (annotateTwo s).map (shiftPairOccurrences i j) by
    simpa [annotateTwo] using annotateTwoFrom_add i j s 0 0]
  simp only [List.mapM_map, evaluateTwo]
  congr 1
  funext p
  rcases p with ⟨q, k⟩
  cases q <;> simp [Function.comp_def, readTwo, shiftPairOccurrences,
    List.getElem?_drop, Nat.add_comm]

private theorem eval_first (a : α) (u v : List α) (s : List Side) :
    evaluateTwo (a :: u) v (.first :: s) =
      (evaluateTwo u v s).map (a :: ·) := by
  simp only [evaluateTwo, annotateTwo, annotateTwoFrom, List.mapM_cons, readTwo,
    List.getElem?_cons_zero]
  rw [shifted_read]
  change ((evaluateTwo u v s).bind fun t => some (a :: t)) =
    (evaluateTwo u v s).map (a :: ·)
  cases evaluateTwo u v s <;> rfl

private theorem eval_second (a : α) (u v : List α) (s : List Side) :
    evaluateTwo u (a :: v) (.second :: s) =
      (evaluateTwo u v s).map (a :: ·) := by
  simp only [evaluateTwo, annotateTwo, annotateTwoFrom, List.mapM_cons, readTwo,
    List.getElem?_cons_zero]
  rw [shifted_read]
  change ((evaluateTwo u v s).bind fun t => some (a :: t)) =
    (evaluateTwo u v s).map (a :: ·)
  cases evaluateTwo u v s <;> rfl

private theorem map_cons_eq (o : Option (List α)) (a b : α) (w : List α) :
    o.map (a :: ·) = some (b :: w) ↔ a = b ∧ o = some w := by
  cases o <;> simp [and_comm]

theorem mask_projections (u v w : List α) (s : List Side) :
    ValidMask u v w s ↔ s.length = w.length ∧
      projection .first w s = u ∧ projection .second w s = v := by
  induction s generalizing u v w with
  | nil =>
      cases u <;> cases v <;> cases w <;>
        simp [ValidMask, ValidTwoSchedule, evaluateTwo, annotateTwo,
          annotateTwoFrom, projection]
  | cons q s ih =>
      cases q with
      | first =>
          cases u with
          | nil => cases w <;> simp [ValidMask, ValidTwoSchedule, projection]
          | cons a u =>
              cases w with
              | nil => simp [ValidMask, eval_first, projection]
              | cons b w =>
                  have hvm : ValidMask (a :: u) v (b :: w) (.first :: s) ↔
                      a = b ∧ ValidMask u v w s := by
                    unfold ValidMask ValidTwoSchedule
                    rw [eval_first,map_cons_eq]
                    simp only [List.count_cons,List.length_cons,beq_self_eq_true,
                      show (Side.first == Side.second) = false from rfl,
                      if_true,if_false,Nat.add_zero,Nat.add_right_cancel_iff]
                    tauto
                  rw [hvm,ih]
                  change (a = b ∧ (s.length = w.length ∧
                    projection .first w s = u ∧ projection .second w s = v)) ↔
                    (s.length + 1 = w.length + 1 ∧
                      b :: projection .first w s = a :: u ∧ projection .second w s = v)
                  simp only [Nat.add_right_cancel_iff,List.cons.injEq]
                  constructor
                  · rintro ⟨hab,hl,hp,hv⟩
                    exact ⟨hl,⟨hab.symm,hp⟩,hv⟩
                  · rintro ⟨hl,⟨hab,hp⟩,hv⟩
                    exact ⟨hab.symm,hl,hp,hv⟩
      | second =>
          cases v with
          | nil => cases w <;> simp [ValidMask, ValidTwoSchedule, projection]
          | cons a v =>
              cases w with
              | nil => simp [ValidMask, eval_second, projection]
              | cons b w =>
                  have hvm : ValidMask u (a :: v) (b :: w) (.second :: s) ↔
                      a = b ∧ ValidMask u v w s := by
                    unfold ValidMask ValidTwoSchedule
                    rw [eval_second,map_cons_eq]
                    simp only [List.count_cons,List.length_cons,beq_self_eq_true,
                      show (Side.second == Side.first) = false from rfl,
                      if_true,if_false,Nat.add_zero,Nat.add_right_cancel_iff]
                    tauto
                  rw [hvm,ih]
                  change (a = b ∧ (s.length = w.length ∧
                    projection .first w s = u ∧ projection .second w s = v)) ↔
                    (s.length + 1 = w.length + 1 ∧ projection .first w s = u ∧
                      b :: projection .second w s = a :: v)
                  simp only [Nat.add_right_cancel_iff,List.cons.injEq]
                  constructor <;> rintro ⟨h1,h2,h3,h4⟩
                  · exact ⟨h2,h3,h1.symm,h4⟩
                  · exact ⟨h3.symm,h1,h2,h4⟩

def step (p q : Side) : Nat := if p = .second ∧ q = .first then 1 else 0

def starts : Side → List Side → Nat
  | _, [] => 0
  | p, q :: s => step p q + starts q s

def lastSide (p : Side) (s : List Side) : Side := s.getLast?.getD p

/-- Number of maximal nonempty runs of the inserted source. -/
def rho (s : List Side) : Nat :=
  (s.splitBy (fun x y => decide (x = y))).countP
    (fun block => decide (block.head? = some .first))

private theorem last_independent (p q : Side) (s : List Side) (hs : s ≠ []) :
    lastSide p s = lastSide q s := by
  simp [lastSide, List.getLast?_eq_getLast hs]

theorem starts_append (p : Side) (s t : List Side) :
    starts p (s ++ t) = starts p s + starts (lastSide p s) t := by
  induction s generalizing p with
  | nil => simp [starts, lastSide]
  | cons a s ih =>
      cases s with
      | nil => simp [starts, lastSide]
      | cons b s =>
          have he := last_independent p a (b :: s) (by simp)
          simp only [lastSide] at he
          simpa [starts, lastSide, Nat.add_assoc, he] using ih a

private theorem starts_change (p q : Side) (s : List Side) :
    (starts p s : Int) - starts q s =
      (step p (s.head?.getD .second) : Int) - step q (s.head?.getD .second) := by
  cases s with
  | nil => cases p <;> cases q <;> simp [starts,step]
  | cons a s => simp [starts] <;> omega

private def countU (bs : List (List Side)) : Nat :=
  bs.countP (fun b => decide (b.head? = some .first))

private theorem pure_head (a : Side) (g : List Side) (hg : ∀ b ∈ g, b = a) :
    (a :: g).reverse.head? = some a := by
  have hh : ∀ b ∈ a :: g, b = a := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · exact hg b hb
  rw [List.eq_replicate_of_mem hh,List.reverse_replicate]
  simp [List.head?_replicate]

private theorem loop_count (l : List Side) (a : Side) (g : List Side)
    (gs : List (List Side)) (hg : ∀ b ∈ g, b = a) :
    countU (List.splitBy.loop (fun x y : Side => decide (x = y)) l a g gs) =
      countU gs + step .second a + starts a l := by
  induction l generalizing a g gs with
  | nil =>
      simp only [List.splitBy.loop,countU,List.countP_reverse,List.countP_cons]
      rw [pure_head a g hg]
      cases a <;> simp [starts,step]
  | cons b l ih =>
      by_cases hab : a = b
      · subst b
        simp only [List.splitBy.loop,decide_true]
        rw [ih a (a :: g) gs (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact hg x hx)]
        cases a <;> simp [starts,step,Nat.add_assoc]
      · simp only [List.splitBy.loop,hab,decide_false]
        rw [ih b [] ((a :: g).reverse :: gs) (by simp)]
        simp only [countU,List.countP_cons,pure_head a g hg]
        cases a <;> cases b <;> simp_all [starts,step] <;> omega

theorem rho_starts (s : List Side) : rho s = starts .second s := by
  cases s with
  | nil => rfl
  | cons a s =>
      unfold rho
      change countU (List.splitBy.loop (fun x y : Side => decide (x = y)) s a [] []) = _
      rw [loop_count s a [] [] (by simp)]
      simp [countU,starts]

private theorem last_append (p : Side) (P Q : List Side) (hQ : Q ≠ []) :
    lastSide p (P ++ Q) = lastSide .second Q := by
  simp [lastSide,List.getLast?_eq_getLast hQ]

private theorem transport_bound (P Q R S : List Side) (hQ : Q ≠ []) (hR : R ≠ []) :
    rho (P ++ Q ++ R ++ S) ≤ rho (P ++ R ++ Q ++ S) + 1 ∧
    rho (P ++ R ++ Q ++ S) ≤ rho (P ++ Q ++ R ++ S) + 1 := by
  simp only [rho_starts, starts_append]
  rw [last_append .second (P ++ Q) R hR,last_append .second P Q hQ,
    last_append .second (P ++ R) Q hQ,last_append .second P R hR]
  have q1 := starts_change (lastSide .second P) (lastSide .second R) Q
  have r1 := starts_change (lastSide .second Q) (lastSide .second P) R
  have s1 := starts_change (lastSide .second R) (lastSide .second Q) S
  generalize hl : lastSide .second P = l at *
  generalize hq : lastSide .second Q = q at *
  generalize hr : lastSide .second R = r at *
  generalize ha : Q.head?.getD .second = a at *
  generalize hb : R.head?.getD .second = b at *
  generalize ht : S.head?.getD .second = t at *
  cases l <;> cases q <;> cases r <;> cases a <;> cases b <;> cases t <;>
    simp [step] at * <;>
    omega

/-- Letter blocks in their original order. -/
structure BlockCut (α : Type*) where
  X : List α
  A : List α
  B : List α
  Y : List α

def original (E : BlockCut α) : List α := E.X ++ E.A ++ E.B ++ E.Y

def successor (E : BlockCut α) : List α := E.X ++ E.B ++ E.A ++ E.Y

/-- Complete position-label blocks in the original cut order. -/
structure Labels where
  X : List Side
  A : List Side
  B : List Side
  Y : List Side

private def Fits (E : BlockCut α) (C : Labels) : Prop :=
  C.X.length = E.X.length ∧ C.A.length = E.A.length ∧
    C.B.length = E.B.length ∧ C.Y.length = E.Y.length

private def oldMask (C : Labels) : List Side := C.X ++ C.A ++ C.B ++ C.Y
private def newMask (C : Labels) : List Side := C.X ++ C.B ++ C.A ++ C.Y

private def labels (E : BlockCut α) (N : List Side) : Labels where
  X := N.take E.X.length
  B := (N.drop E.X.length).take E.B.length
  A := (N.drop (E.X.length + E.B.length)).take E.A.length
  Y := N.drop (E.X.length + E.B.length + E.A.length)

/-- Back-transport moves the actual position labels with the exchanged letters. -/
def back (E : BlockCut α) (N : List Side) : List Side := oldMask (labels E N)

/-- Both ordered source projections in the new mask must commute. -/
def Commuting (E : BlockCut α) (N : List Side) : Prop :=
  let C := labels E N
  (projection .first E.A C.A ++ projection .first E.B C.B =
    projection .first E.B C.B ++ projection .first E.A C.A) ∧
  (projection .second E.A C.A ++ projection .second E.B C.B =
    projection .second E.B C.B ++ projection .second E.A C.A)

/-- Exact pure blocks and exterior boundaries encode a maximal separating exchange. -/
private def EndpointExchange (E : BlockCut α) (M : List Side) : Prop :=
  E.A ≠ [] ∧ E.B ≠ [] ∧ ∃ C : Labels, Fits E C ∧ M = oldMask C ∧
    ((C.A = List.replicate E.A.length .first ∧
      C.B = List.replicate E.B.length .second ∧
      C.X.getLast? ≠ some .first ∧ C.Y.head? = some .first) ∨
     (C.A = List.replicate E.A.length .second ∧
      C.B = List.replicate E.B.length .first ∧
      C.X.getLast? = some .first ∧ C.Y.head? ≠ some .first))

private theorem split_pure (q : Side) (n : Nat) (hn : 0 < n) :
    (List.replicate n q).splitBy (fun x y : Side => decide (x = y)) =
      [List.replicate n q] := by
  apply List.splitBy_of_isChain (by simp [hn.ne'])
  exact List.isChain_replicate_of_rel n (by simp)

private theorem split_four (P S : List Side) (a b : Nat) (q t : Side)
    (ha : 0 < a) (hb : 0 < b) (hqt : q ≠ t) :
    (P ++ List.replicate a q ++ List.replicate b t ++ S).splitBy
        (fun x y : Side => decide (x = y)) =
      P.splitBy (fun x y : Side => decide (x = y)) ++
        [List.replicate a q,List.replicate b t] ++
        S.splitBy (fun x y : Side => decide (x = y)) ↔
      P.getLast? ≠ some q ∧ S.head? ≠ some t := by
  constructor
  · intro he
    have hc := (List.splitBy_eq_iff.mp he).2.2.2
    constructor
    · intro hp
      have hpn : P ≠ [] := by intro h; simp [h] at hp
      have hlast : P.getLast hpn = q := by simpa [List.getLast?_eq_getLast hpn] using hp
      have hcp := (List.isChain_append.mp (show
          (P.splitBy (fun x y : Side => decide (x = y)) ++
            ([List.replicate a q,List.replicate b t] ++
              S.splitBy (fun x y : Side => decide (x = y)))).IsChain _ by
                simpa only [List.append_assoc] using hc)).2.2
      obtain ⟨hx,hy,hbad⟩ := hcp
        ((P.splitBy (fun x y : Side => decide (x = y))).getLast
          (List.splitBy_ne_nil.mpr hpn)) (List.getLast_mem_getLast? _)
        (List.replicate a q) (by simp)
      simp only [List.head_replicate,decide_eq_false_iff_not] at hbad
      exact hbad (by rw [List.getLast_getLast_splitBy _ hpn,hlast])
    · intro hs
      have hsn : S ≠ [] := by intro h; simp [h] at hs
      have hhead : S.head hsn = t := by simpa [List.head?_eq_head hsn] using hs
      have hcs := (List.isChain_append.mp hc).2.2
      obtain ⟨hx,hy,hbad⟩ := hcs (List.replicate b t) (by simp)
        ((S.splitBy (fun x y : Side => decide (x = y))).head
          (List.splitBy_ne_nil.mpr hsn)) (List.head_mem_head? _)
      simp only [List.getLast_replicate,decide_eq_false_iff_not] at hbad
      exact hbad (by rw [List.head_head_splitBy _ hsn,hhead])
  · rintro ⟨hp,hs⟩
    have h1 := List.splitBy_append (r := fun x y : Side => decide (x = y))
      (l := P) (m := List.replicate a q) (by
        intro x hx y hy
        simp only [List.head?_replicate,ha.ne',if_false,Option.mem_some_iff] at hy
        subst y
        apply decide_eq_false_iff_not.mpr
        intro he
        subst x
        exact hp (by simpa only [Option.mem_def,eq_comm] using hx))
    have h2 := List.splitBy_append (r := fun x y : Side => decide (x = y))
      (l := P ++ List.replicate a q) (m := List.replicate b t) (by
        intro x hx y hy
        simp only [List.getLast?_append,List.getLast?_replicate,ha.ne',if_false,
          Option.some_or,Option.mem_some_iff] at hx
        simp only [List.head?_replicate,hb.ne',if_false,Option.mem_some_iff] at hy
        subst x; subst y
        exact decide_eq_false_iff_not.mpr hqt)
    have h3 := List.splitBy_append (r := fun x y : Side => decide (x = y))
      (l := P ++ List.replicate a q ++ List.replicate b t) (m := S) (by
        intro x hx y hy
        simp only [List.getLast?_append,List.getLast?_replicate,hb.ne',if_false,
          Option.some_or,Option.mem_some_iff] at hx
        subst x
        apply decide_eq_false_iff_not.mpr
        intro he
        subst y
        exact hs (by simpa only [Option.mem_def,eq_comm] using hy))
    rw [h3,h2,h1,split_pure q a ha,split_pure t b hb]
    simp [List.append_assoc]

/-- The two exchanged blocks occur as whole consecutive maximal runs. -/
def Admissible (E : BlockCut α) (M : List Side) : Prop :=
  E.A ≠ [] ∧ E.B ≠ [] ∧ ∃ C : Labels, Fits E C ∧ M = oldMask C ∧
    M.splitBy (fun x y : Side => decide (x = y)) =
      C.X.splitBy (fun x y : Side => decide (x = y)) ++ [C.A,C.B] ++
        C.Y.splitBy (fun x y : Side => decide (x = y)) ∧
    ((C.A = List.replicate E.A.length .first ∧
      C.B = List.replicate E.B.length .second ∧ C.Y.head? = some .first) ∨
     (C.A = List.replicate E.A.length .second ∧
      C.B = List.replicate E.B.length .first ∧ C.X.getLast? = some .first))

private theorem admissible_endpoints (E : BlockCut α) (M : List Side) :
    Admissible E M ↔ EndpointExchange E M := by
  constructor
  · rintro ⟨ha,hb,C,hf,hM,hsplit,hcase⟩
    refine ⟨ha,hb,C,hf,hM,?_⟩
    have hapos := List.length_pos_iff.mpr ha
    have hbpos := List.length_pos_iff.mpr hb
    rcases hcase with ⟨hA,hB,hS⟩ | ⟨hA,hB,hP⟩
    · have hs := (split_four C.X C.Y E.A.length E.B.length .first .second
        hapos hbpos (by decide)).mp (by simpa [hM,oldMask,hA,hB] using hsplit)
      exact Or.inl ⟨hA,hB,hs.1,hS⟩
    · have hs := (split_four C.X C.Y E.A.length E.B.length .second .first
        hapos hbpos (by decide)).mp (by simpa [hM,oldMask,hA,hB] using hsplit)
      exact Or.inr ⟨hA,hB,hP,hs.2⟩
  · rintro ⟨ha,hb,C,hf,hM,hcase⟩
    refine ⟨ha,hb,C,hf,hM,?_,?_⟩
    · rcases hcase with ⟨hA,hB,hP,hS⟩ | ⟨hA,hB,hP,hS⟩
      · simpa [hM,oldMask,hA,hB] using
          (split_four C.X C.Y E.A.length E.B.length .first .second
            (List.length_pos_iff.mpr ha) (List.length_pos_iff.mpr hb) (by decide)).mpr
              ⟨hP,by simp [hS]⟩
      · simpa [hM,oldMask,hA,hB] using
          (split_four C.X C.Y E.A.length E.B.length .second .first
            (List.length_pos_iff.mpr ha) (List.length_pos_iff.mpr hb) (by decide)).mpr
              ⟨by simp [hP],hS⟩
    · rcases hcase with ⟨hA,hB,hP,hS⟩ | ⟨hA,hB,hP,hS⟩
      · exact Or.inl ⟨hA,hB,hS⟩
      · exact Or.inr ⟨hA,hB,hP⟩

private theorem labels_new (E : BlockCut α) (C : Labels) (h : Fits E C) :
    labels E (newMask C) = C := by
  rcases C with ⟨P,Q,R,S⟩
  rcases h with ⟨hP,hQ,hR,hS⟩
  simp only [Fits] at *
  simp only [labels, newMask]
  congr <;> simp [← hP, ← hQ, ← hR, List.append_assoc,
    List.take_append, List.drop_append, List.drop_drop]
  simpa only [List.length_append,List.drop_append,List.append_assoc,Nat.sub_sub,Nat.add_assoc] using (List.drop_left (l₁ := P ++ R ++ Q) (l₂ := S))

private theorem labels_full (E : BlockCut α) (N : List Side)
    (h : N.length = (successor E).length) :
    Fits E (labels E N) ∧ newMask (labels E N) = N := by
  have ht : N.length = E.X.length + E.B.length + E.A.length + E.Y.length := by
    simpa only [successor,List.length_append,List.length_append,Nat.add_assoc] using h
  constructor
  · simp [Fits, labels, List.length_take, List.length_drop]
    omega
  · simp only [newMask, labels]
    rw [show N.drop (E.X.length + E.B.length) =
        (N.drop E.X.length).drop E.B.length by simp [List.drop_drop]]
    rw [show N.drop (E.X.length + E.B.length + E.A.length) =
        ((N.drop E.X.length).drop E.B.length).drop E.A.length by
          simp [List.drop_drop, Nat.add_assoc]]
    simp only [List.append_assoc, List.take_append_drop]

theorem projection_append (q : Side) (a b : List α) (s t : List Side)
    (h : a.length = s.length) :
    projection q (a ++ b) (s ++ t) = projection q a s ++ projection q b t := by
  simp [projection, List.zip_append h]

private theorem old_projection (q : Side) (E : BlockCut α) (C : Labels)
    (h : Fits E C) :
    projection q (original E) (oldMask C) =
      projection q E.X C.X ++ projection q E.A C.A ++
        projection q E.B C.B ++ projection q E.Y C.Y := by
  rcases h with ⟨hX,hA,hB,hY⟩
  simp only [original, oldMask]
  rw [projection_append, projection_append, projection_append] <;>
    simp [List.length_append,hX,hA,hB]

private theorem new_projection (q : Side) (E : BlockCut α) (C : Labels)
    (h : Fits E C) :
    projection q (successor E) (newMask C) =
      projection q E.X C.X ++ projection q E.B C.B ++
        projection q E.A C.A ++ projection q E.Y C.Y := by
  rcases h with ⟨hX,hA,hB,hY⟩
  simp only [successor, newMask]
  rw [projection_append, projection_append, projection_append] <;>
    simp [List.length_append,hX,hA,hB]

private theorem back_valid (u v : List α) (E : BlockCut α) (N : List Side)
    (hN : ValidMask u v (successor E) N) :
    ValidMask u v (original E) (back E N) ↔ Commuting E N := by
  obtain ⟨hf,hn⟩ := labels_full E N (mask_projections u v _ N |>.mp hN |>.1)
  have hnp := (mask_projections u v _ N).mp hN
  rw [← hn] at hnp
  simp only [back, Commuting]
  rw [mask_projections]
  have hlen : (oldMask (labels E N)).length = (original E).length := by
    rcases hf with ⟨hX,hA,hB,hY⟩
    simp [oldMask,original,List.length_append,hX,hA,hB,hY]
  rw [old_projection _ E _ hf,old_projection _ E _ hf,hlen]
  rw [new_projection _ E _ hf,new_projection _ E _ hf] at hnp
  rw [← hnp.2.1,← hnp.2.2]
  simp only [true_and, List.append_assoc, List.append_cancel_left_eq]
  simp only [← List.append_assoc,List.append_cancel_right_eq]

theorem projection_pure (q t : Side) (a : List α) :
    projection q a (List.replicate a.length t) = if t = q then a else [] := by
  induction a with
  | nil => simp [projection]
  | cons x a ih =>
      cases q <;> cases t <;>
        simp only [projection,List.length_cons,List.replicate_succ,List.zip_cons_cons,
          List.filterMap_cons,reduceCtorEq,if_true,if_false] at * <;>
        first | exact congrArg (x :: ·) ih | exact ih

private theorem swap_valid (u v : List α) (E : BlockCut α) (C : Labels)
    (hf : Fits E C) (hM : ValidMask u v (original E) (oldMask C))
    (hc : ∀ q : Side, projection q E.A C.A ++ projection q E.B C.B =
      projection q E.B C.B ++ projection q E.A C.A) :
    ValidMask u v (successor E) (newMask C) := by
  obtain ⟨hl,hU,hV⟩ := (mask_projections u v _ _).mp hM
  apply (mask_projections u v _ _).mpr
  have hlen : (newMask C).length = (successor E).length := by
    rcases hf with ⟨hX,hA,hB,hY⟩
    simp [newMask,successor,List.length_append,hX,hA,hB,hY]
  refine ⟨hlen,?_,?_⟩
  · rw [new_projection _ E C hf,← hU,old_projection _ E C hf]
    simpa only [List.append_assoc] using
      congrArg (fun t => projection .first E.X C.X ++ t ++ projection .first E.Y C.Y)
        (hc .first).symm
  · rw [new_projection _ E C hf,← hV,old_projection _ E C hf]
    simpa only [List.append_assoc] using
      congrArg (fun t => projection .second E.X C.X ++ t ++ projection .second E.Y C.Y)
        (hc .second).symm

private theorem starts_self (q : Side) (n : Nat) :
    starts q (List.replicate n q) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases q <;> simp_all [starts,step,List.replicate_succ]

theorem starts_pure (p q : Side) (n : Nat) (hn : 0 < n) :
    starts p (List.replicate n q) = step p q := by
  cases n with
  | zero => omega
  | succ n => simp [starts,List.replicate_succ,starts_self]

private theorem last_pure (p q : Side) (n : Nat) (hn : 0 < n) :
    lastSide p (List.replicate n q) = q := by
  cases n with
  | zero => omega
  | succ n => simp [lastSide,List.getLast?_replicate]

private theorem pure_decrease (P S : List Side) (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (q : Side)
    (hP : lastSide .second P = q)
    (hS : S.head?.getD .second = if q = .first then .second else .first) :
    rho (P ++ List.replicate a (if q = .first then .second else .first) ++
      List.replicate b q ++ S) =
    rho (P ++ List.replicate b q ++
      List.replicate a (if q = .first then .second else .first) ++ S) + 1 := by
  have hna : List.replicate a (if q = .first then Side.second else Side.first) ≠ [] := by
    simp [ha.ne']
  have hnb : List.replicate b q ≠ [] := by simp [hb.ne']
  simp only [rho_starts,starts_append]
  rw [last_append .second _ _ hnb,last_append .second _ _ hna,
    last_append .second _ _ hna,last_append .second _ _ hnb]
  simp only [last_pure _ _ _ ha,last_pure _ _ _ hb,hP,
    starts_pure _ _ _ ha, starts_pure _ _ _ hb]
  have hdiff := starts_change q (if q = .first then .second else .first) S
  rw [hS] at hdiff
  cases q <;> simp [step] at * <;> omega

theorem intended_successor (u v : List α) (E : BlockCut α) (M : List Side)
    (hM : ValidMask u v (original E) M) (hE : Admissible E M) :
    ∃ N, ValidMask u v (successor E) N ∧ Commuting E N ∧ rho N + 1 = rho M := by
  obtain ⟨ha,hb,C,hf,hMC,hcase⟩ := (admissible_endpoints E M).mp hE
  have hapos : 0 < E.A.length := List.length_pos_iff.mpr ha
  have hbpos : 0 < E.B.length := List.length_pos_iff.mpr hb
  have hc : ∀ q : Side, projection q E.A C.A ++ projection q E.B C.B =
      projection q E.B C.B ++ projection q E.A C.A := by
    intro q
    rcases hcase with ⟨hA,hB,hP,hS⟩ | ⟨hA,hB,hP,hS⟩ <;>
      rw [hA,hB,projection_pure,projection_pure] <;> cases q <;> simp
  refine ⟨newMask C,swap_valid u v E C hf (hMC ▸ hM) hc,?_,?_⟩
  · simp only [Commuting,labels_new E C hf]
    exact ⟨hc .first,hc .second⟩
  · rw [hMC]
    rcases hcase with ⟨hA,hB,hP,hS⟩ | ⟨hA,hB,hP,hS⟩
    · have hp : lastSide .second C.X = .second := by
        cases he : C.X.getLast? with
        | none => simp [lastSide,he]
        | some q => cases q <;> simp_all [lastSide]
      -- Left exchange has an exterior V (or the empty context) and a following U.
      have d := pure_decrease C.X C.Y E.A.length E.B.length hapos hbpos .second hp
        (by simp [hS])
      simpa [oldMask,newMask,hA,hB] using d.symm
    · have hp : lastSide .second C.X = .first := by simp [lastSide,hP]
      have hs : C.Y.head?.getD .second = .second := by
        cases he : C.Y.head? with
        | none => simp [he]
        | some q => cases q <;> simp_all
      have d := pure_decrease C.X C.Y E.A.length E.B.length hapos hbpos .first hp hs
      simpa [oldMask,newMask,hA,hB] using d.symm

/-- A chosen mask attains the minimum among all actual masks of the word. -/
def IsMinimumMask (u v w : List α) (M : List Side) (r : Nat) : Prop :=
  ValidMask u v w M ∧ rho M = r ∧
    ∀ N, ValidMask u v w N → r ≤ rho N

/-- Literal attained minimum, with the empty family assigned infinity. -/
noncomputable def minRuns (P : List Side → Prop) : WithTop Nat := by
  classical
  exact if h : ∃ n : Nat, ∃ s, P s ∧ rho s = n then (Nat.find h : WithTop Nat) else ⊤

noncomputable def degree (u v w : List α) : WithTop Nat := minRuns (ValidMask u v w)

noncomputable def c (E : BlockCut α) (u v : List α) : WithTop Nat :=
  minRuns (fun N => ValidMask u v (successor E) N ∧ Commuting E N)

noncomputable def b (E : BlockCut α) (u v : List α) : WithTop Nat :=
  minRuns (fun N => ValidMask u v (successor E) N ∧ ¬ Commuting E N)

theorem le_minRuns (P : List Side → Prop) (k : WithTop Nat) :
    k ≤ minRuns P ↔ ∀ N, P N → k ≤ (rho N : WithTop Nat) := by
  classical
  unfold minRuns
  split
  · rename_i h
    obtain ⟨M,hM,he⟩ := Nat.find_spec h
    constructor
    · intro hk N hN
      exact hk.trans (by exact_mod_cast Nat.find_min' h ⟨N,hN,rfl⟩)
    · intro hk
      simpa [he] using hk M hM
  · rename_i h
    simp only [le_top,true_iff]
    intro N hN
    exact (h ⟨rho N,N,hN,rfl⟩).elim

theorem minRuns_le (P : List Side → Prop) (N : List Side) (hN : P N) :
    minRuns P ≤ (rho N : WithTop Nat) :=
  (le_minRuns P _).mp le_rfl N hN

private theorem min_partition (P Q : List Side → Prop) :
    minRuns P = min (minRuns (fun N => P N ∧ Q N))
      (minRuns (fun N => P N ∧ ¬ Q N)) := by
  classical
  apply le_antisymm
  · apply le_min
    · exact (le_minRuns _ _).mpr (fun N hN => minRuns_le P N hN.1)
    · exact (le_minRuns _ _).mpr (fun N hN => minRuns_le P N hN.1)
  · apply (le_minRuns P _).mpr
    intro N hN
    by_cases hQ : Q N
    · exact (min_le_left _ _).trans (minRuns_le _ N ⟨hN,hQ⟩)
    · exact (min_le_right _ _).trans (minRuns_le _ N ⟨hN,hQ⟩)

/-- The exact obstruction is the least run count of a noncommuting actual mask. -/
theorem result (α : Type*) (u v w z : List α) (E : BlockCut α)
    (M : List Side) (r : Nat) (hu : u ≠ []) (hv : v ≠ [])
    (hw : w = original E) (hz : z = successor E)
    (hM : IsMinimumMask u v w M r) (hr : 1 < r) (hE : Admissible E M) :
    c E u v = ((r - 1 : Nat) : WithTop Nat) ∧
    degree u v z = min ((r - 1 : Nat) : WithTop Nat) (b E u v) ∧
    (degree u v z = ((r - 1 : Nat) : WithTop Nat) ↔
      ((r - 1 : Nat) : WithTop Nat) ≤ b E u v) := by
  subst w
  subst z
  obtain ⟨N0,hN0,hC0,hR0⟩ := intended_successor u v E M hM.1 hE
  have hR : rho N0 = r - 1 := by have := hM.2.1; omega
  have hc : c E u v = ((r - 1 : Nat) : WithTop Nat) := by
    apply le_antisymm
    · have he := minRuns_le (fun N => ValidMask u v (successor E) N ∧ Commuting E N)
        N0 ⟨hN0,hC0⟩
      simpa [c,hR] using he
    · apply (le_minRuns _ _).mpr
      intro N hN
      have hback := (back_valid u v E N hN.1).mpr hN.2
      have hmin := hM.2.2 (back E N) hback
      obtain ⟨hf,hfull⟩ := labels_full E N ((mask_projections u v _ _).mp hN.1).1
      have hA : (labels E N).A ≠ [] := by
        intro he
        have hh := hf.2.1
        rw [he] at hh
        exact hE.1 (List.length_eq_zero_iff.mp hh.symm)
      have hB : (labels E N).B ≠ [] := by
        intro he
        have hh := hf.2.2.1
        rw [he] at hh
        exact hE.2.1 (List.length_eq_zero_iff.mp hh.symm)
      have ht := (transport_bound (labels E N).X (labels E N).A
        (labels E N).B (labels E N).Y hA hB).1
      change rho (back E N) ≤ rho (newMask (labels E N)) + 1 at ht
      rw [hfull] at ht
      exact_mod_cast (show r - 1 ≤ rho N by omega)
  have hd : degree u v (successor E) =
      min ((r - 1 : Nat) : WithTop Nat) (b E u v) := by
    have hp := min_partition (ValidMask u v (successor E)) (Commuting E)
    change degree u v (successor E) = min (c E u v) (b E u v) at hp
    simpa [hc] using hp
  refine ⟨hc,hd,?_⟩
  rw [hd]
  constructor
  · intro he
    have hh := min_le_right ((r - 1 : Nat) : WithTop Nat) (b E u v)
    simpa only [he] using hh
  · exact min_eq_left

end D5.S1.Words.HughesBlockExchange
