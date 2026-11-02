/- GID: D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Polyomino/IrwinA138099HookSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The square spiral hook increments equal the row-flattened triangle. -/

/-
result
proof_shape: content (literal-walk square and strip induction).
escape_witness: square_invariant, consumed through layer_diagrams and the two blocks.
admission_basis: open-problem-resolution (#23678; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25040
The public definitions retain the source expressions fixed in issue #23678.
Every helper is private. Their classifications below expand same-delivery helpers;
all have Direct frozen dependencies: none and escape_witness: none unless stated.
prefix_succ: proof_shape: bind-only; consumers: prefix_strict, prefix_even, prefix_odd, row_at, address_exists.
prefix_strict: proof_shape: bind-only; consumers: prefix_ge, row_at.
prefix_ge: proof_shape: bind-only; consumers: sourceRow, row_spec, row_min.
prefix_even: proof_shape: bind-only; consumers: prefix_odd, second_block, result.
prefix_odd: proof_shape: bind-only; consumers: first_block, result.
row_spec: proof_shape: bind-only; consumers: row_at, address_exists.
row_min: proof_shape: bind-only; consumers: address_exists.
row_at: proof_shape: bind-only; consumers: arithmetic_source.
arithmetic_source: proof_shape: bind-only; consumers: result.
address_exists: proof_shape: bind-only; consumers: result.
diagram_source: proof_shape: bind-only; consumers: spiral_unique, layer_diagrams, result.
spiral_unique: proof_shape: bind-only; consumers: result.
filter_insert_card: proof_shape: bind-only; consumers: hook_insert_cell.
hook_insert_cell: proof_shape: bind-only; consumers: hook_sum_insert.
row_partition: proof_shape: bind-only; consumers: hook_sum_insert.
col_partition: proof_shape: bind-only; consumers: hook_sum_insert.
hook_sum_insert: proof_shape: bind-only; consumers: column_increment, row_increment.
frame_injective: proof_shape: bind-only; consumers: box_mem, box_row, box_col.
frame_surjective: proof_shape: bind-only; consumers: box_col_extend, box_row_extend, box_flip, column_disjoint, row_disjoint.
box_mem: proof_shape: bind-only; consumers: box_shift_mem, box_col_extend, box_row_extend, box_flip, column_disjoint, column_counts.
box_shift_mem: proof_shape: bind-only; consumers: box_col_extend, box_row_extend, column_disjoint, row_disjoint, column_counts, row_counts.
box_row: proof_shape: bind-only; consumers: column_counts, row_counts.
box_col: proof_shape: bind-only; consumers: column_counts, row_counts.
box_col_extend: proof_shape: bind-only; consumers: layer_diagrams.
box_row_extend: proof_shape: bind-only; consumers: layer_finish.
box_flip: proof_shape: bind-only; consumers: layer_finish.
frame_comp: proof_shape: bind-only; consumers: column_shape_succ, row_shape_succ, column_counts, row_counts, layer_finish.
box_insert_col: proof_shape: bind-only; consumers: column_shape_succ.
box_insert_row: proof_shape: bind-only; consumers: row_shape_succ.
column_shape_succ: proof_shape: bind-only; consumers: column_increment, layer_diagrams.
row_shape_succ: proof_shape: bind-only; consumers: row_increment, layer_diagrams.
filter_union_card: proof_shape: bind-only; consumers: column_counts, row_counts.
column_disjoint: proof_shape: bind-only; consumers: column_counts.
row_disjoint: proof_shape: bind-only; consumers: row_counts.
column_counts: proof_shape: bind-only; consumers: column_increment.
row_counts: proof_shape: bind-only; consumers: row_increment.
column_increment: proof_shape: bind-only; consumers: first_block.
row_increment: proof_shape: bind-only; consumers: second_block.
sign_sq: proof_shape: bind-only; consumers: layer_diagrams, layer_finish, first_block, second_block.
sign_succ: proof_shape: bind-only; consumers: layer_finish.
layer_directions: proof_shape: bind-only; consumers: layer_walk.
walk_state_ext: proof_shape: bind-only; consumers: walk_segment, walk_turn, layer_walk.
walk_segment: proof_shape: content; consumers: walk_turn, layer_walk.
walk_turn: proof_shape: content; consumers: layer_walk.
layer_walk: proof_shape: content; consumers: layer_diagrams, square_invariant.
layer_diagrams: proof_shape: content; consumers: square_invariant, first_block, second_block.
layer_finish: proof_shape: bind-only; consumers: square_invariant.
square_invariant: proof_shape: content; consumers: first_block, second_block.
first_block: proof_shape: content; consumers: result.
second_block: proof_shape: content; consumers: result.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring


/-! Definitions for the unnumbered Irwin conjecture in OEIS A138099.
Coordinates are (horizontal, vertical), with vertical increasing downwards.
The source diagram fixes the walk west, south, east, north with leg lengths
1,1,2,2,3,3,... .
-/

namespace D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum

/-- The source triangle entry, used only at 1 <= k and 1 <= j <= ceil(k/2). -/
def triangleEntry (k j : ℕ) : ℕ := j + k / 2

/-- Number of entries in source rows 1 through k; row 0 is absent. -/
def trianglePrefix (k : ℕ) : ℕ :=
  (Finset.range k).sum (fun i => (i + 2) / 2)

/-- The source's row-flattened sequence, with its one-based offset.
The value at index 0 is deliberately unrestricted and is never used. -/
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, 1 ≤ j → j ≤ (k + 1) / 2 →
    a (trianglePrefix (k - 1) + j) = triangleEntry k j

/-- Leg directions in the displayed spiral: west, south, east, north. -/
def legDirection (leg : ℕ) : ℤ × ℤ :=
  match leg % 4 with
  | 0 => (-1, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | _ => (0, -1)

/-- A cell position and the number of steps already taken on the current leg. -/
structure WalkState where
  cell : ℤ × ℤ
  leg : ℕ
  used : ℕ

/-- Take one unit step, turning after leg/2 + 1 steps. -/
def advance (s : WalkState) : WalkState :=
  let d := legDirection s.leg
  let p := (s.cell.1 + d.1, s.cell.2 + d.2)
  if s.used + 1 = s.leg / 2 + 1 then
    ⟨p, s.leg + 1, 0⟩
  else
    ⟨p, s.leg, s.used + 1⟩

/-- The first cell is the origin; subsequent cells follow the displayed spiral. -/
def walk : ℕ → WalkState
  | 0 => ⟨(0, 0), 0, 0⟩
  | n + 1 => advance (walk n)

/-- T(0) is empty, and T(n+1) inserts the next cell of the literal unit-step walk. -/
def IsSourceSpiral (T : ℕ → Finset (ℤ × ℤ)) : Prop :=
  T 0 = ∅ ∧ ∀ n : ℕ, T (n + 1) = insert (walk n).cell (T n)

/-- Ordinary right/down hook length: its own cell, its arm, and its leg.
This is used only for c in D when taking the hook sum. -/
def hookLength (D : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℕ :=
  1 + (D.filter (fun d => d.2 = c.2 ∧ c.1 < d.1)).card +
    (D.filter (fun d => d.1 = c.1 ∧ c.2 < d.2)).card

/-- The sum of all ordinary hook lengths, including the empty sum 0. -/
def hookSum (D : Finset (ℤ × ℤ)) : ℕ :=
  D.sum (fun c => hookLength D c)

/-- The source assertion, including existence of its two implicitly specified objects.
The subtraction of hook sums is in the integers, not truncated natural subtraction. -/
def claim : Prop :=
  (∃ a : ℕ → ℕ, IsSourceSequence a) ∧
  (∃ T : ℕ → Finset (ℤ × ℤ), IsSourceSpiral T) ∧
  ∀ (a : ℕ → ℕ) (T : ℕ → Finset (ℤ × ℤ)),
    IsSourceSequence a → IsSourceSpiral T →
      ∀ n : ℕ, 1 ≤ n →
        (a n : ℤ) = (hookSum (T n) : ℤ) - (hookSum (T (n - 1)) : ℤ)


open Finset

private theorem prefix_succ (k : ℕ) : trianglePrefix (k+1) = trianglePrefix k + (k+2)/2 := by
  exact Finset.sum_range_succ (fun i => (i+2)/2) k

private theorem prefix_strict : StrictMono trianglePrefix := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [prefix_succ]
  omega

private theorem prefix_ge (k : ℕ) : k ≤ trianglePrefix k := by
  exact prefix_strict.id_le k

private theorem prefix_even (m : ℕ) : trianglePrefix (2*m) = m*m+m := by
  induction m with
  | zero => simp [trianglePrefix]
  | succ m ih =>
    rw [show 2*(m+1) = (2*m+1)+1 by omega, prefix_succ, prefix_succ, ih]
    have h₁ : (2*m+2)/2 = m+1 := by omega
    have h₂ : (2*m+1+2)/2 = m+1 := by omega
    rw [h₁,h₂]
    ring

private theorem prefix_odd (m : ℕ) : trianglePrefix (2*m+1) = (m+1)*(m+1) := by
  rw [prefix_succ, prefix_even]
  have h : (2*m+2)/2 = m+1 := by omega
  rw [h]
  ring

private def sourceRow (n : ℕ) : ℕ := Nat.find (show ∃ k, n ≤ trianglePrefix k from ⟨n, prefix_ge n⟩)

private theorem row_spec (n : ℕ) : n ≤ trianglePrefix (sourceRow n) := by
  unfold sourceRow
  exact Nat.find_spec (show ∃ k, n ≤ trianglePrefix k from ⟨n,prefix_ge n⟩)

private theorem row_min (n k : ℕ) (h : k < sourceRow n) : trianglePrefix k < n := by
  have := Nat.find_min (show ∃ k, n ≤ trianglePrefix k from ⟨n,prefix_ge n⟩) h
  omega

private theorem row_at (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) (hj' : j ≤ (k+1)/2) :
    sourceRow (trianglePrefix (k-1)+j) = k := by
  apply le_antisymm
  · apply Nat.find_min'
    have h : trianglePrefix k = trianglePrefix (k-1)+(k+1)/2 := by
      convert prefix_succ (k-1) using 1 <;> congr 1 <;> omega
    omega
  · by_contra hn
    have hlt : sourceRow (trianglePrefix (k-1)+j) ≤ k-1 := by omega
    have hle := prefix_strict.monotone hlt
    have hs := row_spec (trianglePrefix (k-1)+j)
    omega

private def arithmeticSequence (n : ℕ) : ℕ := n - trianglePrefix (sourceRow n - 1) + sourceRow n / 2

private theorem arithmetic_source : IsSourceSequence arithmeticSequence := by
  intro k hk j hj hj'
  simp only [arithmeticSequence, row_at k j hk hj hj', triangleEntry]
  omega

private theorem address_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ j ≤ (k+1)/2 ∧ n = trianglePrefix (k-1)+j := by
  let k := sourceRow n
  have hk : 1 ≤ k := by
    have hs := row_spec n
    by_contra h
    have hz : sourceRow n = 0 := by exact Nat.eq_zero_of_not_pos h
    rw [hz] at hs
    simp [trianglePrefix] at hs
    omega
  have hp : trianglePrefix (k-1) < n := row_min n (k-1) (by omega)
  have hs := row_spec n
  have he : trianglePrefix k = trianglePrefix (k-1)+(k+1)/2 := by
    convert prefix_succ (k-1) using 1 <;> congr 1 <;> omega
  refine ⟨k,n-trianglePrefix (k-1),hk,by omega,?_,by omega⟩
  change n ≤ trianglePrefix k at hs
  omega

private def diagram (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range n).image (fun i => (walk i).cell)

private theorem diagram_source : IsSourceSpiral diagram := by
  constructor
  · rfl
  · intro n
    simp only [diagram, Finset.range_add_one, Finset.image_insert]

private theorem spiral_unique (T : ℕ → Finset (ℤ × ℤ)) (hT : IsSourceSpiral T) (n : ℕ) :
    T n = diagram n := by
  induction n with
  | zero => exact hT.1
  | succ n ih => rw [hT.2,diagram_source.2,ih]


open Finset

private theorem filter_insert_card (D : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∉ D)
    (P : ℤ × ℤ → Prop) [DecidablePred P] :
    ((insert p D).filter P).card = (D.filter P).card + if P p then 1 else 0 := by
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hp])]
  · omega

private theorem hook_insert_cell (D : Finset (ℤ × ℤ)) (p c : ℤ × ℤ) (hp : p ∉ D) :
    hookLength (insert p D) c = hookLength D c +
      (if p.2 = c.2 ∧ c.1 < p.1 then 1 else 0) +
      (if p.1 = c.1 ∧ c.2 < p.2 then 1 else 0) := by
  simp only [hookLength, filter_insert_card D p hp]
  omega

private theorem row_partition (D : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∉ D) :
    (D.filter (fun c => c.2 = p.2)).card =
      (D.filter (fun c => c.2 = p.2 ∧ c.1 < p.1)).card +
      (D.filter (fun c => c.2 = p.2 ∧ p.1 < c.1)).card := by
  have he : D.filter (fun c => c.2 = p.2) =
      D.filter (fun c => c.2 = p.2 ∧ c.1 < p.1) ∪
      D.filter (fun c => c.2 = p.2 ∧ p.1 < c.1) := by
    ext c
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hc,hy⟩
      have hx : c.1 ≠ p.1 := by
        intro hx
        have : c = p := Prod.ext hx hy
        subst c
        exact hp hc
      by_cases h : c.1 < p.1
      · exact Or.inl ⟨hc,hy,h⟩
      · exact Or.inr ⟨hc,hy,by omega⟩
    · tauto
  rw [he,card_union_of_disjoint]
  apply disjoint_left.mpr
  intro c hc hc'
  simp only [mem_filter] at hc hc'
  omega

private theorem col_partition (D : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∉ D) :
    (D.filter (fun c => c.1 = p.1)).card =
      (D.filter (fun c => c.1 = p.1 ∧ c.2 < p.2)).card +
      (D.filter (fun c => c.1 = p.1 ∧ p.2 < c.2)).card := by
  have he : D.filter (fun c => c.1 = p.1) =
      D.filter (fun c => c.1 = p.1 ∧ c.2 < p.2) ∪
      D.filter (fun c => c.1 = p.1 ∧ p.2 < c.2) := by
    ext c
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hc,hx⟩
      have hy : c.2 ≠ p.2 := by
        intro hy
        have : c = p := Prod.ext hx hy
        subst c
        exact hp hc
      by_cases h : c.2 < p.2
      · exact Or.inl ⟨hc,hx,h⟩
      · exact Or.inr ⟨hc,hx,by omega⟩
    · tauto
  rw [he,card_union_of_disjoint]
  apply disjoint_left.mpr
  intro c hc hc'
  simp only [mem_filter] at hc hc'
  omega

private theorem hook_sum_insert (D : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (hp : p ∉ D) :
    hookSum (insert p D) = hookSum D + 1 +
      (D.filter (fun c => c.2 = p.2)).card +
      (D.filter (fun c => c.1 = p.1)).card := by
  unfold hookSum
  rw [sum_insert hp]
  simp_rw [hook_insert_cell D p _ hp]
  rw [sum_add_distrib,sum_add_distrib]
  have hsum (P : ℤ × ℤ → Prop) [DecidablePred P] :
      ∑ c ∈ D, (if P c then 1 else 0) = (D.filter P).card := by
    exact Finset.sum_boole P D
  rw [hsum,hsum]
  have hr := row_partition D p hp
  have hc := col_partition D p hp
  unfold hookLength
  have he₂ : (D.filter (fun c => p.2 = c.2 ∧ c.1 < p.1)) =
      D.filter (fun c => c.2 = p.2 ∧ c.1 < p.1) := by ext c; simp [eq_comm]
  have he₃ : (D.filter (fun c => p.1 = c.1 ∧ c.2 < p.2)) =
      D.filter (fun c => c.1 = p.1 ∧ c.2 < p.2) := by ext c; simp [eq_comm]
  rw [he₂,he₃]
  simp only [lt_self_iff_false,and_false,ite_false,add_zero]
  omega


open Finset

private def frame (o : ℤ × ℤ) (s : ℤ) (u : ℤ × ℤ) : ℤ × ℤ :=
  o + (s, s) * u

private def box (w h : ℕ) (o : ℤ × ℤ) (s : ℤ) : Finset (ℤ × ℤ) :=
  ((Ico 0 (w : ℤ)) ×ˢ (Ico 0 (h : ℤ))).image (frame o s)

private theorem frame_injective (o : ℤ × ℤ) {s : ℤ} (hs : s ≠ 0) :
    Function.Injective (frame o s) := by
  intro u v he
  apply Prod.ext
  · apply mul_left_cancel₀ hs
    exact add_left_cancel (congrArg Prod.fst he)
  · apply mul_left_cancel₀ hs
    exact add_left_cancel (congrArg Prod.snd he)

private theorem frame_surjective (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    Function.Surjective (frame o s) := by
  intro c
  refine ⟨(s*(c.1-o.1),s*(c.2-o.2)),?_⟩
  apply Prod.ext <;> simp only [frame,Prod.fst_add,Prod.snd_add,Prod.fst_mul,Prod.snd_mul]
  · calc o.1+s*(s*(c.1-o.1)) = o.1+(s*s)*(c.1-o.1) := by ring
         _ = c.1 := by rw [hs]; ring
  · calc o.2+s*(s*(c.2-o.2)) = o.2+(s*s)*(c.2-o.2) := by ring
         _ = c.2 := by rw [hs]; ring

private theorem box_mem (w h : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s ≠ 0) (a b : ℤ) :
    frame o s (a,b) ∈ box w h o s ↔ 0 ≤ a ∧ a < w ∧ 0 ≤ b ∧ b < h := by
  simp [box,Finset.mem_image, (frame_injective o hs).eq_iff,and_assoc]

private theorem box_shift_mem (w h : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s ≠ 0) (a b i j : ℤ) :
    frame o s (i,j) ∈ box w h (frame o s (a,b)) s ↔
      a ≤ i ∧ i < a+w ∧ b ≤ j ∧ j < b+h := by
  have he : frame o s (i,j) = frame (frame o s (a,b)) s (i-a,j-b) := by
    apply Prod.ext <;> dsimp [frame] <;> ring
  rw [he,box_mem w h _ hs]
  omega

private theorem box_row (w h : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s ≠ 0) (a b : ℤ) :
    ((box w h o s).filter (fun c => c.2 = (frame o s (a,b)).2)).card =
      if 0 ≤ b ∧ b < h then w else 0 := by
  have he (u : ℤ × ℤ) : (frame o s u).2 = (frame o s (a,b)).2 ↔ u.2 = b := by
    simp only [frame,Prod.snd_add,Prod.snd_mul,add_right_inj]
    exact ⟨mul_left_cancel₀ hs, fun h => congrArg (s * ·) h⟩
  simp only [box,filter_image,he]
  rw [card_image_of_injective _ (frame_injective o hs),
    filter_product_right (s := Ico 0 (w:ℤ)) (t := Ico 0 (h:ℤ)) (fun y : ℤ => y=b)]
  by_cases hb : 0 ≤ b ∧ b < h <;> simp [Finset.filter_eq',Int.card_Ico,hb]

private theorem box_col (w h : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s ≠ 0) (a b : ℤ) :
    ((box w h o s).filter (fun c => c.1 = (frame o s (a,b)).1)).card =
      if 0 ≤ a ∧ a < w then h else 0 := by
  have he (u : ℤ × ℤ) : (frame o s u).1 = (frame o s (a,b)).1 ↔ u.1 = a := by
    simp only [frame,Prod.fst_add,Prod.fst_mul,add_right_inj]
    exact ⟨mul_left_cancel₀ hs, fun h => congrArg (s * ·) h⟩
  simp only [box,filter_image,he]
  rw [card_image_of_injective _ (frame_injective o hs),
    filter_product_left (s := Ico 0 (w:ℤ)) (t := Ico 0 (h:ℤ)) (fun x : ℤ => x=a)]
  by_cases ha : 0 ≤ a ∧ a < w <;> simp [Finset.filter_eq',Int.card_Ico,ha]

private theorem box_col_extend (m h : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    box m h o s ∪ box 1 h (frame o s (-1,0)) s =
      box (m+1) h (frame o s (-1,0)) s := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  ext c
  obtain ⟨⟨a,b⟩,rfl⟩ := frame_surjective o hs c
  simp only [mem_union,box_mem _ _ _ hs0,box_shift_mem _ _ _ hs0]
  push_cast
  omega

private theorem box_row_extend (w m : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    box w m o s ∪ box w 1 (frame o s (0,m)) s = box w (m+1) o s := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  ext c
  obtain ⟨⟨a,b⟩,rfl⟩ := frame_surjective o hs c
  simp only [mem_union,box_mem _ _ _ hs0,box_shift_mem _ _ _ hs0]
  push_cast
  omega

private theorem box_flip (m : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    box m m o s = box m m (frame o s ((m:ℤ)-1,(m:ℤ)-1)) (-s) := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  ext c
  obtain ⟨⟨a,b⟩,rfl⟩ := frame_surjective o hs c
  have he : frame o s (a,b) =
      frame (frame o s ((m:ℤ)-1,(m:ℤ)-1)) (-s) ((m:ℤ)-1-a,(m:ℤ)-1-b) := by
    apply Prod.ext <;> dsimp [frame] <;> ring
  rw [box_mem _ _ _ hs0,he,box_mem _ _ _ (neg_ne_zero.mpr hs0)]
  omega

private def columnShape (m t : ℕ) (o : ℤ × ℤ) (s : ℤ) : Finset (ℤ × ℤ) :=
  box m m o s ∪ box 1 t (frame o s (-1,0)) s

private def rowShape (m t : ℕ) (o : ℤ × ℤ) (s : ℤ) : Finset (ℤ × ℤ) :=
  box (m+1) m (frame o s (-1,0)) s ∪ box t 1 (frame o s (-1,m)) s

private theorem frame_comp (o : ℤ × ℤ) (s a b i j : ℤ) :
    frame (frame o s (a,b)) s (i,j) = frame o s (a+i,b+j) := by
  apply Prod.ext <;> dsimp [frame] <;> ring

private theorem box_insert_col (t : ℕ) (o : ℤ × ℤ) (s : ℤ) :
    insert (frame o s (0,t)) (box 1 t o s) = box 1 (t+1) o s := by
  have he : (Finset.Ico (0:ℤ) 1) ×ˢ (Finset.Ico 0 ((t+1:ℕ):ℤ)) =
      insert (0,(t:ℤ)) ((Finset.Ico (0:ℤ) 1) ×ˢ (Finset.Ico 0 (t:ℤ))) := by
    ext u
    rcases u with ⟨x,y⟩
    simp only [Finset.mem_product,Finset.mem_Ico,Finset.mem_insert,Prod.mk.injEq]
    push_cast
    omega
  simp only [box,Nat.cast_one,he,Finset.image_insert]

private theorem box_insert_row (t : ℕ) (o : ℤ × ℤ) (s : ℤ) :
    insert (frame o s (t,0)) (box t 1 o s) = box (t+1) 1 o s := by
  have he : (Finset.Ico (0:ℤ) ((t+1:ℕ):ℤ)) ×ˢ (Finset.Ico (0:ℤ) 1) =
      insert ((t:ℤ),0) ((Finset.Ico (0:ℤ) (t:ℤ)) ×ˢ (Finset.Ico (0:ℤ) 1)) := by
    ext u
    rcases u with ⟨x,y⟩
    simp only [Finset.mem_product,Finset.mem_Ico,Finset.mem_insert,Prod.mk.injEq]
    push_cast
    omega
  simp only [box,Nat.cast_one,he,Finset.image_insert]

private theorem column_shape_succ (m t : ℕ) (o : ℤ × ℤ) (s : ℤ) :
    insert (frame o s (-1,t)) (columnShape m t o s) = columnShape m (t+1) o s := by
  unfold columnShape
  rw [← Finset.union_insert, ← box_insert_col]
  congr 2
  rw [frame_comp]
  simp

private theorem row_shape_succ (m t : ℕ) (o : ℤ × ℤ) (s : ℤ) :
    insert (frame o s ((t:ℤ)-1,m)) (rowShape m t o s) = rowShape m (t+1) o s := by
  unfold rowShape
  rw [← Finset.union_insert, ← box_insert_row]
  congr 2
  rw [frame_comp]
  congr 1


open Finset

private theorem filter_union_card (D E : Finset (ℤ × ℤ)) (hd : Disjoint D E)
    (P : ℤ × ℤ → Prop) [DecidablePred P] :
    ((D ∪ E).filter P).card = (D.filter P).card + (E.filter P).card := by
  rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _))]

private theorem column_disjoint (m t : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    Disjoint (box m m o s) (box 1 t (frame o s (-1,0)) s) := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  apply disjoint_left.mpr
  intro c hc hc'
  obtain ⟨⟨a,b⟩,rfl⟩ := frame_surjective o hs c
  rw [box_mem _ _ _ hs0] at hc
  rw [box_shift_mem _ _ _ hs0] at hc'
  norm_num at hc'
  omega

private theorem row_disjoint (m t : ℕ) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    Disjoint (box (m+1) m (frame o s (-1,0)) s) (box t 1 (frame o s (-1,m)) s) := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  apply disjoint_left.mpr
  intro c hc hc'
  obtain ⟨⟨a,b⟩,rfl⟩ := frame_surjective o hs c
  rw [box_shift_mem _ _ _ hs0] at hc hc'
  omega

private theorem column_counts (m t : ℕ) (ht : t < m) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    frame o s (-1,t) ∉ columnShape m t o s ∧
    ((columnShape m t o s).filter (fun c => c.2 = (frame o s (-1,t)).2)).card = m ∧
    ((columnShape m t o s).filter (fun c => c.1 = (frame o s (-1,t)).1)).card = t := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  have hp : frame o s (-1,t) = frame (frame o s (-1,0)) s (0,t) := by
    rw [frame_comp]; simp
  have hr₁ := box_row m m o hs0 (-1) t
  have hc₁ := box_col m m o hs0 (-1) t
  have hr₂ := box_row 1 t (frame o s (-1,0)) hs0 0 t
  have hc₂ := box_col 1 t (frame o s (-1,0)) hs0 0 t
  rw [← hp] at hr₂ hc₂
  refine ⟨?_,?_,?_⟩
  · simp only [columnShape,mem_union,box_mem _ _ _ hs0,box_shift_mem _ _ _ hs0]
    omega
  · rw [columnShape,filter_union_card _ _ (column_disjoint m t o hs),hr₁,hr₂]
    split_ifs <;> omega
  · rw [columnShape,filter_union_card _ _ (column_disjoint m t o hs),hc₁,hc₂]
    norm_num

private theorem row_counts (m t : ℕ) (ht : t ≤ m) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    frame o s ((t:ℤ)-1,m) ∉ rowShape m t o s ∧
    ((rowShape m t o s).filter (fun c => c.2 = (frame o s ((t:ℤ)-1,m)).2)).card = t ∧
    ((rowShape m t o s).filter (fun c => c.1 = (frame o s ((t:ℤ)-1,m)).1)).card = m := by
  have hs0 : s ≠ 0 := by exact left_ne_zero_of_mul_eq_one hs
  have hp₁ : frame o s ((t:ℤ)-1,m) = frame (frame o s (-1,0)) s (t,m) := by
    rw [frame_comp]; congr 1 <;> simp <;> omega
  have hp₂ : frame o s ((t:ℤ)-1,m) = frame (frame o s (-1,m)) s (t,0) := by
    rw [frame_comp]; congr 1 <;> simp <;> omega
  have hr₁ := box_row (m+1) m (frame o s (-1,0)) hs0 t m
  have hc₁ := box_col (m+1) m (frame o s (-1,0)) hs0 t m
  have hr₂ := box_row t 1 (frame o s (-1,m)) hs0 t 0
  have hc₂ := box_col t 1 (frame o s (-1,m)) hs0 t 0
  rw [← hp₁] at hr₁ hc₁
  rw [← hp₂] at hr₂ hc₂
  refine ⟨?_,?_,?_⟩
  · simp only [rowShape,mem_union,box_shift_mem _ _ _ hs0]
    omega
  · rw [rowShape,filter_union_card _ _ (row_disjoint m t o hs),hr₁,hr₂]
    norm_num
  · rw [rowShape,filter_union_card _ _ (row_disjoint m t o hs),hc₁,hc₂]
    split_ifs <;> omega

private theorem column_increment (m t : ℕ) (ht : t < m) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    hookSum (columnShape m (t+1) o s) = hookSum (columnShape m t o s) + (m+t+1) := by
  obtain ⟨hp,hr,hc⟩ := column_counts m t ht o hs
  rw [← column_shape_succ, hook_sum_insert _ _ hp,hr,hc]
  omega

private theorem row_increment (m t : ℕ) (ht : t ≤ m) (o : ℤ × ℤ) {s : ℤ} (hs : s*s = 1) :
    hookSum (rowShape m (t+1) o s) = hookSum (rowShape m t o s) + (m+t+1) := by
  obtain ⟨hp,hr,hc⟩ := row_counts m t ht o hs
  rw [← row_shape_succ, hook_sum_insert _ _ hp,hr,hc]
  omega


private def corner : ℕ → ℤ × ℤ
  | 0 => (0,0)
  | m+1 => if m=0 then (0,0) else frame (corner m) (if m%2 = 0 then (-1:ℤ) else 1) ((m:ℤ)-1,m)

private theorem sign_sq (m : ℕ) : (if m%2 = 0 then (-1:ℤ) else 1) * (if m%2 = 0 then (-1:ℤ) else 1) = 1 := by
  split_ifs <;> norm_num

private theorem sign_succ (m : ℕ) : (if (m+1)%2 = 0 then (-1:ℤ) else 1) = -(if m%2 = 0 then (-1:ℤ) else 1) := by
  split_ifs <;> norm_num <;> omega

private theorem layer_directions (m : ℕ) (hm : 1 ≤ m) :
    legDirection (2*m-2) = (-(if m%2 = 0 then (-1:ℤ) else 1),0) ∧
    legDirection (2*m-1) = (0,(if m%2 = 0 then (-1:ℤ) else 1)) ∧
    legDirection (2*m) = ((if m%2 = 0 then (-1:ℤ) else 1),0) := by
  have h₀ : (2*m-2)%4 = if m%2=0 then 2 else 0 := by split_ifs <;> omega
  have h₁ : (2*m-1)%4 = if m%2=0 then 3 else 1 := by split_ifs <;> omega
  have h₂ : (2*m)%4 = if m%2=0 then 0 else 2 := by split_ifs <;> omega
  by_cases he : m%2=0 <;> simp [legDirection,h₀,h₁,h₂,he]

private theorem walk_state_ext {a b : WalkState} (hc : a.cell = b.cell)
    (hl : a.leg = b.leg) (hu : a.used = b.used) : a=b := by
  cases a
  cases b
  simp_all

private theorem walk_segment (N l u t : ℕ) (o : ℤ × ℤ)
    (hw : walk N = ⟨o,l,u⟩) (ht : u+t < l/2+1) :
    walk (N+t) = ⟨(o.1+(t:ℤ)*(legDirection l).1,
      o.2+(t:ℤ)*(legDirection l).2),l,u+t⟩ := by
  induction t with
  | zero => simpa using hw
  | succ t ih =>
    have he : u+t < l/2+1 := by exact Nat.lt_of_succ_lt ht
    have ht' : u+t+1 ≠ l/2+1 := by exact Nat.ne_of_lt ht
    rw [show N+(t+1) = (N+t)+1 by omega,walk,ih he]
    unfold advance
    dsimp only
    rw [ite_eq_right ht']
    apply walk_state_ext
    · apply Prod.ext <;> dsimp <;> push_cast <;> ring
    · rfl
    · dsimp; omega

private theorem walk_turn (N l : ℕ) (o : ℤ × ℤ) (hw : walk N = ⟨o,l,0⟩) :
    walk (N+(l/2+1)) = ⟨(o.1+((l/2+1:ℕ):ℤ)*(legDirection l).1,
      o.2+((l/2+1:ℕ):ℤ)*(legDirection l).2),l+1,0⟩ := by
  have hseg := walk_segment N l 0 (l/2) o hw (by omega)
  rw [show N+(l/2+1) = (N+l/2)+1 by omega,walk,hseg]
  unfold advance
  dsimp only
  rw [ite_eq_left (by omega)]
  apply walk_state_ext
  · apply Prod.ext <;> dsimp <;> push_cast <;> ring
  · rfl
  · rfl

private theorem layer_walk (m : ℕ) (hm : 1 ≤ m) (o : ℤ × ℤ)
    (hw : walk (m*m-1) = ⟨o,2*m-2,m-1⟩) :
    (∀ t, t < m → walk (m*m+t) = ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,t),2*m-1,t⟩) ∧
    (∀ t, t ≤ m → walk (m*m+m+t) = ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) ((t:ℤ)-1,m),2*m,t⟩) := by
  obtain ⟨hd₀,hd₁,hd₂⟩ := layer_directions m hm
  have hl₀ : (2*m-2)/2+1 = m := by omega
  have hl₁ : (2*m-1)/2+1 = m := by omega
  have hl₂ : (2*m)/2+1 = m+1 := by omega
  have hstart : walk (m*m) = ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,0),2*m-1,0⟩ := by
    have hmul : 1 ≤ m*m := by exact Left.one_le_mul hm hm
    rw [show m*m = (m*m-1)+1 by omega,walk,hw]
    unfold advance
    dsimp only
    rw [ite_eq_left (by omega)]
    apply walk_state_ext
    · apply Prod.ext <;> dsimp [frame] <;> rw [hd₀] <;> dsimp <;> ring
    · dsimp; omega
    · rfl
  have hcol : ∀ t, t < m → walk (m*m+t) = ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,t),2*m-1,t⟩ := by
    intro t ht
    have he := walk_segment (m*m) (2*m-1) 0 t (frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,0)) hstart (by rw [hl₁]; omega)
    rw [hd₁] at he
    rw [he]
    apply walk_state_ext
    · apply Prod.ext <;> dsimp [frame] <;> ring
    · rfl
    · dsimp; omega
  have hrowstart : walk (m*m+m) = ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,m),2*m,0⟩ := by
    have he := walk_turn (m*m) (2*m-1) (frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,0)) hstart
    rw [hl₁,hd₁] at he
    rw [he]
    apply walk_state_ext
    · apply Prod.ext <;> dsimp [frame] <;> ring
    · dsimp; omega
    · rfl
  refine ⟨hcol,?_⟩
  intro t ht
  have he := walk_segment (m*m+m) (2*m) 0 t (frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,m)) hrowstart (by rw [hl₂]; omega)
  rw [hd₂] at he
  rw [he]
  apply walk_state_ext
  · apply Prod.ext <;> dsimp [frame] <;> ring
  · rfl
  · dsimp; omega

private theorem layer_diagrams (m : ℕ) (hm : 1 ≤ m) (o : ℤ × ℤ)
    (hw : walk (m*m-1) = ⟨o,2*m-2,m-1⟩)
    (hD : diagram (m*m) = box m m o (if m%2 = 0 then (-1:ℤ) else 1)) :
    (∀ t, t ≤ m → diagram (m*m+t) = columnShape m t o (if m%2 = 0 then (-1:ℤ) else 1)) ∧
    (∀ t, t ≤ m+1 → diagram (m*m+m+t) = rowShape m t o (if m%2 = 0 then (-1:ℤ) else 1)) := by
  obtain ⟨hc,hr⟩ := layer_walk m hm o hw
  have hcol : ∀ t, t ≤ m → diagram (m*m+t) = columnShape m t o (if m%2 = 0 then (-1:ℤ) else 1) := by
    intro t
    induction t with
    | zero => simpa [columnShape,box] using hD
    | succ t ih =>
      intro ht
      rw [show m*m+(t+1) = (m*m+t)+1 by omega,diagram_source.2,hc t (by omega),ih (by omega)]
      exact column_shape_succ m t o (if m%2 = 0 then (-1:ℤ) else 1)
  have hend : diagram (m*m+m) = box (m+1) m (frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,0)) (if m%2 = 0 then (-1:ℤ) else 1) := by
    rw [hcol m (by rfl),columnShape,box_col_extend m m o (sign_sq m)]
  refine ⟨hcol,?_⟩
  intro t
  induction t with
  | zero => simpa [rowShape,box] using hend
  | succ t ih =>
    intro ht
    rw [show m*m+m+(t+1) = (m*m+m+t)+1 by omega,diagram_source.2,hr t (by omega),ih (by omega)]
    exact row_shape_succ m t o (if m%2 = 0 then (-1:ℤ) else 1)

private theorem layer_finish (m : ℕ) (o : ℤ × ℤ) :
    rowShape m (m+1) o (if m%2 = 0 then (-1:ℤ) else 1) =
      box (m+1) (m+1) (frame o (if m%2 = 0 then (-1:ℤ) else 1) ((m:ℤ)-1,m)) (if (m+1)%2 = 0 then (-1:ℤ) else 1) := by
  have he : frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,m) = frame (frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,0)) (if m%2 = 0 then (-1:ℤ) else 1) (0,m) := by
    rw [frame_comp]; simp
  rw [rowShape,he,box_row_extend _ _ _ (sign_sq m),box_flip _ _ (sign_sq m),sign_succ]
  congr 1
  rw [frame_comp]
  push_cast
  congr 1 <;> simp <;> omega

private theorem square_invariant (m : ℕ) (hm : 1 ≤ m) :
    walk (m*m-1) = ⟨corner m,2*m-2,m-1⟩ ∧
    diagram (m*m) = box m m (corner m) (if m%2 = 0 then (-1:ℤ) else 1) := by
  induction m,hm using Nat.le_induction with
  | base =>
    constructor
    · rfl
    · simp [diagram,corner,walk,box,show Finset.Ico (0:ℤ) 1 = {0} from Finset.val_eq_singleton_iff.mp rfl,frame]
  | succ m hm ih =>
    have hc : corner (m+1) = frame (corner m) (if m%2 = 0 then (-1:ℤ) else 1) ((m:ℤ)-1,m) := by
      simp [corner,show m ≠ 0 by omega]
    obtain ⟨_,hr⟩ := layer_walk m hm (corner m) ih.1
    obtain ⟨_,hR⟩ := layer_diagrams m hm (corner m) ih.1 ih.2
    have ht₁ : (m+1)*(m+1)-1 = m*m+m+m := by
      have he : (m+1)*(m+1) = (m*m+m+m)+1 := by exact Nat.succ_mul_succ m m
      omega
    have ht₂ : (m+1)*(m+1) = m*m+m+(m+1) := by exact Nat.succ_mul_succ m m
    constructor
    · rw [ht₁,hr m (by rfl),hc]
      congr 1 <;> omega
    · rw [ht₂,hR (m+1) (by rfl),layer_finish,hc]


open Finset

private theorem first_block (a : ℕ → ℕ) (ha : IsSourceSequence a) (m j : ℕ)
    (hm : 1 ≤ m) (hj : 1 ≤ j) (hj' : j ≤ m) :
    (a (m*m+j) : ℤ) = (hookSum (diagram (m*m+j)) : ℤ) -
      (hookSum (diagram (m*m+j-1)) : ℤ) := by
  have hp : trianglePrefix (2*m-1) = m*m := by
    have he := prefix_odd (m-1)
    have hk : 2*(m-1)+1 = 2*m-1 := by omega
    rw [hk] at he
    convert he using 1 <;> congr 1 <;> omega
  have he := ha (2*m) (by omega) j hj (by omega)
  rw [hp] at he
  have he' : triangleEntry (2*m) j = m+j := by unfold triangleEntry; omega
  rw [he'] at he
  obtain ⟨hw,hD⟩ := square_invariant m hm
  obtain ⟨hcol,_⟩ := layer_diagrams m hm (corner m) hw hD
  have hinc := column_increment m (j-1) (by omega) (corner m) (sign_sq m)
  have hn : m*m+j-1 = m*m+(j-1) := by exact Nat.add_sub_assoc hj (m * m)
  rw [show j-1+1 = j by omega, ← hcol j hj', ← hcol (j-1) (by omega)] at hinc
  rw [he,hn]
  omega

private theorem second_block (a : ℕ → ℕ) (ha : IsSourceSequence a) (m j : ℕ)
    (hj : 1 ≤ j) (hj' : j ≤ m+1) :
    (a (m*m+m+j) : ℤ) = (hookSum (diagram (m*m+m+j)) : ℤ) -
      (hookSum (diagram (m*m+m+j-1)) : ℤ) := by
  have he := ha (2*m+1) (by omega) j hj (by omega)
  rw [show 2*m+1-1 = 2*m by omega,prefix_even] at he
  have he' : triangleEntry (2*m+1) j = m+j := by unfold triangleEntry; omega
  rw [he'] at he
  by_cases hm : m=0
  · subst m
    have hj₁ : j=1 := by exact Eq.symm (Nat.le_antisymm hj hj')
    subst j
    norm_num [diagram,walk,hookSum,hookLength] at *
    exact_mod_cast he
  · have hm' : 1 ≤ m := by exact Nat.one_le_iff_ne_zero.mpr hm
    obtain ⟨hw,hD⟩ := square_invariant m hm'
    obtain ⟨_,hrow⟩ := layer_diagrams m hm' (corner m) hw hD
    have hinc := row_increment m (j-1) (by omega) (corner m) (sign_sq m)
    have hn : m*m+m+j-1 = m*m+m+(j-1) := by exact Nat.add_sub_assoc hj (m * m + m)
    rw [show j-1+1 = j by omega, ← hrow j hj', ← hrow (j-1) (by omega)] at hinc
    rw [he,hn]
    omega

theorem result : D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum.claim := by
  refine ⟨⟨arithmeticSequence,arithmetic_source⟩,⟨diagram,diagram_source⟩,?_⟩
  intro a T ha hT n hn
  rw [spiral_unique T hT n,spiral_unique T hT (n-1)]
  obtain ⟨k,j,hk,hj,hj',hnj⟩ := address_exists n hn
  by_cases he : k%2=0
  · let m := k/2
    have hkm : k=2*m := by dsimp [m]; omega
    have hm : 1 ≤ m := by omega
    have hp : trianglePrefix (k-1) = m*m := by
      rw [hkm]
      have he := prefix_odd (m-1)
      rw [show 2*(m-1)+1 = 2*m-1 by omega] at he
      convert he using 1 <;> congr 1 <;> omega
    rw [hp] at hnj
    rw [hnj]
    apply first_block a ha m j hm hj
    omega
  · let m := k/2
    have hkm : k=2*m+1 := by dsimp [m]; omega
    have hp : trianglePrefix (k-1) = m*m+m := by
      rw [hkm,show 2*m+1-1 = 2*m by omega,prefix_even]
    rw [hp] at hnj
    rw [hnj]
    apply second_block a ha m j hj
    omega


end D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum
