/- GID: D5/S3/Combinatorics/Transportation/SupportedBooleanCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/SupportedBooleanCycles
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Arbitrary supported Boolean fibers have target-conformal bounded simple cycle paths. -/

import D5.S3.Combinatorics.Transportation.SupportedCycleSupplier
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.SDiff

/-! Supported Boolean tables with equal labeled margins admit target-conformal
simple cycle flips and a finite chain bounded by one quarter of their distance. -/

set_option autoImplicit false
namespace D5.S3.Combinatorics.Transportation.SupportedBooleanCycles
noncomputable section
open SupportedCycleSupplier
universe u v
variable {R : Type u} {C : Type v} [Fintype R] [Fintype C]

abbrev Table (R : Type u) (C : Type v) := R → C → Bool

def Supported (E : R → C → Prop) (M : Table R C) : Prop :=
  ∀ a b, M a b = true → E a b

def SameMargins (M B : Table R C) : Prop :=
  (∀ a, rowSum M a = rowSum B a) ∧ (∀ b, colSum M b = colSum B b)

open Classical in
noncomputable def disagreements (M B : Table R C) : Finset (R × C) :=
  Finset.univ.filter fun x => M x.1 x.2 ≠ B x.1 x.2

noncomputable def distance (M B : Table R C) : ℕ := (disagreements M B).card

structure Cycle (R : Type u) (C : Type v) where
  k : ℕ
  minimum : 2 ≤ k
  row : Fin k → R
  col : Fin k → C
  row_injective : Function.Injective row
  col_injective : Function.Injective col

open Classical in
noncomputable def red (w : Cycle R C) : Finset (R × C) :=
  Finset.univ.image fun i => (w.row i, w.col i)
open Classical in
noncomputable def blue (w : Cycle R C) : Finset (R × C) :=
  Finset.univ.image fun i => (w.row i, w.col (finRotate w.k i))
open Classical in
noncomputable def cells (w : Cycle R C) : Finset (R × C) := red w ∪ blue w
noncomputable def flip (w : Cycle R C) (M : Table R C) : Table R C := by
  classical
  exact fun a b => if (a,b) ∈ cells w then !(M a b) else M a b

/-- Both alternating polarities are allowed, with every changed cell corrected. -/
def LegalStep (E : R → C → Prop) (B M N : Table R C) (k : ℕ) : Prop :=
  ∃ w : Cycle R C, w.k = k ∧ ∃ p : Bool,
    (∀ i, E (w.row i) (w.col i) ∧ E (w.row i) (w.col (finRotate w.k i))) ∧
    (∀ i, M (w.row i) (w.col i) = p ∧ B (w.row i) (w.col i) = !p ∧
      M (w.row i) (w.col (finRotate w.k i)) = !p ∧
      B (w.row i) (w.col (finRotate w.k i)) = p) ∧ N = flip w M

/-- A finite chain ending at B; support and each individual margin hold at every node. -/
inductive Chain (E : R → C → Prop) (B : Table R C) : Table R C → ℕ → Prop
  | done (hs : Supported E B) : Chain E B B 0
  | step {M N : Table R C} {n k : ℕ} (hs : Supported E M)
      (hm : SameMargins M B) (move : LegalStep E B M N k)
      (correcting : ∀ a b, N a b ≠ M a b → M a b ≠ B a b ∧ N a b = B a b)
      (tail : Chain E B N n) : Chain E B M (n+1)

open Classical in
private theorem count_move {α : Type*} [Fintype α]
    (f : α → Bool) (a b : α) (ha : f a = true) (hb : f b = false) :
    ((Finset.univ : Finset α).filter fun x =>
      (if x = a then false else if x = b then true else f x) = true).card =
    ((Finset.univ : Finset α).filter fun x => f x = true).card := by
  classical
  let S := (Finset.univ : Finset α).filter fun x => f x = true
  have hab : a ≠ b := by intro h; simp [h, hb] at ha
  have heq : ((Finset.univ : Finset α).filter fun x =>
      (if x = a then false else if x = b then true else f x) = true) =
      insert b (S.erase a) := by
    ext x
    by_cases hxa : x = a
    · subst x; simp [hab]
    · by_cases hxb : x = b
      · subst x; simp [hxa]
      · simp [S, hxa, hxb]
  rw [heq, Finset.card_insert_of_notMem (by simp [S, hb])]
  exact Finset.card_erase_add_one (by simp [S, ha])

omit [Fintype R] [Fintype C] in
private theorem mem_red_row (w : Cycle R C) (i : Fin w.k) (b : C) :
    (w.row i,b) ∈ red w ↔ b = w.col i := by
  classical
  simp only [red, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,hc⟩
    have : j = i := w.row_injective hj
    subst j; exact hc.symm
  · intro h; exact ⟨i,rfl,h.symm⟩

omit [Fintype R] [Fintype C] in
private theorem mem_blue_row (w : Cycle R C) (i : Fin w.k) (b : C) :
    (w.row i,b) ∈ blue w ↔ b = w.col (finRotate w.k i) := by
  classical
  simp only [blue, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,hc⟩
    have : j = i := w.row_injective hj
    subst j; exact hc.symm
  · intro h; exact ⟨i,rfl,h.symm⟩

omit [Fintype R] [Fintype C] in
private theorem mem_red_col (w : Cycle R C) (j : Fin w.k) (a : R) :
    (a,w.col j) ∈ red w ↔ a = w.row j := by
  classical
  simp only [red, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨i,hr,hc⟩
    have : i = j := w.col_injective hc
    subst i; exact hr.symm
  · intro h; exact ⟨j,h.symm,rfl⟩

omit [Fintype R] [Fintype C] in
private theorem mem_blue_col (w : Cycle R C) (j : Fin w.k) (a : R) :
    (a,w.col j) ∈ blue w ↔ a = w.row ((finRotate w.k).symm j) := by
  classical
  simp only [blue, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨i,hr,hc⟩
    have he : finRotate w.k i = j := w.col_injective hc
    have : i = (finRotate w.k).symm j := (Equiv.eq_symm_apply _).mpr he
    subst i; exact hr.symm
  · intro h; exact ⟨(finRotate w.k).symm j,h.symm,by rw [Equiv.apply_symm_apply]⟩

omit [Fintype R] [Fintype C] in
open Classical in
private theorem flip_pattern (w : Cycle R C) (M B : Table R C)
    (hp : ∀ i, M (w.row i) (w.col i) = true ∧ B (w.row i) (w.col i) = false ∧
      M (w.row i) (w.col (finRotate w.k i)) = false ∧
      B (w.row i) (w.col (finRotate w.k i)) = true) :
    (∀ a b, flip w M a b =
      if (a,b) ∈ red w then false else if (a,b) ∈ blue w then true else M a b) ∧
    (∀ a b, (a,b) ∈ cells w → M a b ≠ B a b ∧ flip w M a b = B a b) := by
  classical
  have hr (a : R) (b : C) (h : (a,b) ∈ red w) : M a b = true ∧ B a b = false := by
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp at he1 he2
    simpa only [he1, he2] using And.intro (hp i).1 (hp i).2.1
  have hb (a : R) (b : C) (h : (a,b) ∈ blue w) : M a b = false ∧ B a b = true := by
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp at he1 he2
    simpa only [he1, he2] using (hp i).2.2
  constructor
  · intro a b
    by_cases h : (a,b) ∈ red w
    · simp [flip, cells, h, (hr a b h).1]
    · by_cases h' : (a,b) ∈ blue w
      · simp [flip, cells, h, h', (hb a b h').1]
      · simp [flip, cells, h, h']
  · intro a b h
    rcases Finset.mem_union.mp h with h | h
    · simp [flip, cells, h, (hr a b h).1, (hr a b h).2]
    · simp [flip, cells, h, (hb a b h).1, (hb a b h).2]

private theorem flip_margins (w : Cycle R C) (M B : Table R C)
    (hp : ∀ i, M (w.row i) (w.col i) = true ∧ B (w.row i) (w.col i) = false ∧
      M (w.row i) (w.col (finRotate w.k i)) = false ∧
      B (w.row i) (w.col (finRotate w.k i)) = true) : SameMargins (flip w M) M := by
  classical
  have hf := (flip_pattern w M B hp).1
  constructor
  · intro a
    by_cases h : ∃ i, w.row i = a
    · obtain ⟨i,rfl⟩ := h
      have heq : flip w M (w.row i) = fun b =>
          if b = w.col i then false else
            if b = w.col (finRotate w.k i) then true else M (w.row i) b := by
        funext b; simp only [hf, mem_red_row, mem_blue_row]
      simpa only [rowSum, heq] using count_move (M (w.row i))
        (w.col i) (w.col (finRotate w.k i)) (hp i).1 (hp i).2.2.1
    · have heq : flip w M a = M a := by
        funext b
        have hr : (a,b) ∉ red w := by
          rintro hc; obtain ⟨i,_,he⟩ := Finset.mem_image.mp hc
          exact h ⟨i,congrArg Prod.fst he⟩
        have hb : (a,b) ∉ blue w := by
          rintro hc; obtain ⟨i,_,he⟩ := Finset.mem_image.mp hc
          exact h ⟨i,congrArg Prod.fst he⟩
        simp [hf,hr,hb]
      simp only [rowSum,heq]
  · intro b
    by_cases h : ∃ j, w.col j = b
    · obtain ⟨j,rfl⟩ := h
      have heq (a : R) : flip w M a (w.col j) =
          if a = w.row j then false else
            if a = w.row ((finRotate w.k).symm j) then true else M a (w.col j) := by
        simp only [hf,mem_red_col,mem_blue_col]
      have hb : M (w.row ((finRotate w.k).symm j)) (w.col j) = false := by
        simpa only [Equiv.apply_symm_apply] using (hp ((finRotate w.k).symm j)).2.2.1
      simpa only [colSum,heq] using count_move (fun a => M a (w.col j))
        (w.row j) (w.row ((finRotate w.k).symm j)) (hp j).1 hb
    · have heq (a : R) : flip w M a b = M a b := by
        have hr : (a,b) ∉ red w := by
          rintro hc; obtain ⟨i,_,he⟩ := Finset.mem_image.mp hc
          exact h ⟨i,congrArg Prod.snd he⟩
        have hb : (a,b) ∉ blue w := by
          rintro hc; obtain ⟨i,_,he⟩ := Finset.mem_image.mp hc
          exact h ⟨finRotate w.k i,congrArg Prod.snd he⟩
        simp [hf,hr,hb]
      simp only [colSum,heq]


private theorem flip_distance (w : Cycle R C) (M B : Table R C)
    (hp : ∀ i, M (w.row i) (w.col i) = true ∧ B (w.row i) (w.col i) = false ∧
      M (w.row i) (w.col (finRotate w.k i)) = false ∧
      B (w.row i) (w.col (finRotate w.k i)) = true) :
    distance (flip w M) B + 2*w.k = distance M B := by
  classical
  have hc := (flip_pattern w M B hp).2
  have hsub : cells w ⊆ disagreements M B := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hc x.1 x.2 hx).1⟩
  have hd : Disjoint (red w) (blue w) := by
    apply Finset.disjoint_left.mpr
    intro x hr hb
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hb
    have ht : M x.1 x.2 = true := by
      have hh := (hp i).1
      have he := congrArg (fun z : R × C => M z.1 z.2) hi
      exact he.symm.trans hh
    have hf : M x.1 x.2 = false := by
      have hh := (hp j).2.2.1
      have he := congrArg (fun z : R × C => M z.1 z.2) hj
      exact he.symm.trans hh
    simp [ht] at hf
  have hcard : (cells w).card = 2*w.k := by
    have hr : (red w).card = w.k := by
      rw [red,Finset.card_image_of_injective]
      · exact Finset.card_fin w.k
      · intro i j he; exact w.row_injective (congrArg Prod.fst he)
    have hb : (blue w).card = w.k := by
      rw [blue,Finset.card_image_of_injective]
      · exact Finset.card_fin w.k
      · intro i j he; exact w.row_injective (congrArg Prod.fst he)
    rw [cells,Finset.card_union_of_disjoint hd,hr,hb]
    omega
  have heq : disagreements (flip w M) B = disagreements M B \ cells w := by
    ext x
    by_cases h : x ∈ cells w
    · simp [disagreements,h,(hc x.1 x.2 h).2]
    · simp [disagreements,flip,h]
  rw [distance,heq,← hcard]
  exact Finset.card_sdiff_add_card_eq_card hsub

private theorem find_cycle (M B : Table R C) (hm : SameMargins M B) (hne : M ≠ B) :
    ∃ w : Cycle R C, ∀ i,
      M (w.row i) (w.col i) = true ∧ B (w.row i) (w.col i) = false ∧
      M (w.row i) (w.col (finRotate w.k i)) = false ∧
      B (w.row i) (w.col (finRotate w.k i)) = true := by
  classical
  let model : FixedMarginModel R C := ⟨rowSum B,colSum B⟩
  let X : FixedMarginState model := ⟨M,hm⟩
  let Y : FixedMarginState model := ⟨B,⟨fun _ => rfl,fun _ => rfl⟩⟩
  have hxy : X ≠ Y := fun h => hne (congrArg Subtype.val h)
  obtain ⟨L,r,c,hlen,hr,hb,hclose,hir,hic⟩ := simple_cycle hxy
  have r_inj : Function.Injective (fun i : Fin L => r i.val) := by
    intro i j he
    by_contra h
    have hval : i.val ≠ j.val := fun h' => h (Fin.ext h')
    rcases Nat.lt_or_gt_of_ne hval with h'|h'
    · exact hir i.val j.val h' j.isLt he
    · exact hir j.val i.val h' i.isLt he.symm
  have c_inj : Function.Injective (fun i : Fin L => c i.val) := by
    intro i j he
    by_contra h
    have hval : i.val ≠ j.val := fun h' => h (Fin.ext h')
    rcases Nat.lt_or_gt_of_ne hval with h'|h'
    · exact hic i.val j.val h' j.isLt he
    · exact hic j.val i.val h' i.isLt he.symm
  let w : Cycle R C := ⟨L,hlen,(fun i => r i.val),(fun i => c i.val),r_inj,c_inj⟩
  refine ⟨w,?_⟩
  intro i
  change Fin L at i
  refine ⟨(hr i.val i.isLt).1,(hr i.val i.isLt).2,?_⟩
  have hrot : (finRotate L i).val = if i.val+1<L then i.val+1 else 0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    rw [coe_finRotate]
    split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> omega
  change M (r i.val) (c (finRotate L i).val) = false ∧
    B (r i.val) (c (finRotate L i).val) = true
  rw [hrot]
  split_ifs with h
  · exact hb i.val h
  · have he : i.val = L-1 := by have := i.isLt; omega
    simpa only [he] using hclose

/-- The complete target-conformal step, including the exact decrease. -/
theorem correcting_step (E : R → C → Prop) (M B : Table R C)
    (hs : Supported E M) (ht : Supported E B) (hm : SameMargins M B) (hne : M ≠ B) :
    ∃ N : Table R C, ∃ k : ℕ, 2 ≤ k ∧ LegalStep E B M N k ∧
      Supported E N ∧ SameMargins N B ∧ distance N B + 2*k = distance M B ∧
      ∀ a b, N a b ≠ M a b → M a b ≠ B a b ∧ N a b = B a b := by
  classical
  obtain ⟨w,hp⟩ := find_cycle M B hm hne
  have hc := (flip_pattern w M B hp).2
  refine ⟨flip w M,w.k,w.minimum,?_,?_,?_,flip_distance w M B hp,?_⟩
  · refine ⟨w,rfl,true,?_,hp,rfl⟩
    intro i
    exact ⟨hs _ _ (hp i).1,ht _ _ (hp i).2.2.2⟩
  · intro a b h
    by_cases hcell : (a,b) ∈ cells w
    · exact ht a b ((hc a b hcell).2.symm.trans h)
    · exact hs a b (by simpa [flip,hcell] using h)
  · have hh := flip_margins w M B hp
    exact ⟨fun a => (hh.1 a).trans (hm.1 a),fun b => (hh.2 b).trans (hm.2 b)⟩
  · intro a b h
    by_cases hcell : (a,b) ∈ cells w
    · exact hc a b hcell
    · exact (h (by simp [flip,hcell])).elim

/-- Arbitrary supported Boolean tables in one labeled margin fiber are connected
by simple target-conformal flips, with four initial disagreements paying for each step. -/
theorem bounded_conformal_chain (E : R → C → Prop) (A B : Table R C)
    (ha : Supported E A) (hb : Supported E B) (hm : SameMargins A B) :
    ∃ n : ℕ, Chain E B A n ∧ n ≤ distance A B / 4 := by
  classical
  generalize hd : distance A B = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases he : A = B
    · subst A
      exact ⟨0,Chain.done hb,by omega⟩
    · obtain ⟨N,k,hk,hstep,hn,hmn,hdec,hcorrect⟩ := correcting_step E A B ha hb hm he
      have hlt : distance N B < d := by omega
      obtain ⟨n,hchain,hbound⟩ := ih (distance N B) hlt N hn hmn rfl
      exact ⟨n+1,Chain.step ha hm hstep hcorrect hchain,by omega⟩

#check correcting_step
#print axioms correcting_step
#check bounded_conformal_chain
#print axioms bounded_conformal_chain

end
end D5.S3.Combinatorics.Transportation.SupportedBooleanCycles
