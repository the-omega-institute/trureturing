/- GID: D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Rounding
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SparseNecklaceRounding/Rounding
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Simultaneous two-coordinate rounding with unchanged block totals and local corners. -/
import D5.S3.Combinatorics.Circle.SourceWidth
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Card

/-! Simultaneous whole-label rounding of fractional blocks. -/
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.SparseNecklaceRounding

/-- A whole label, or one positive label cut by one negative terminal. The
fraction is auxiliary; both rounded words consist solely of whole labels. -/
inductive RoundBlock (α : Type*)
  | one (i : α)
  | cut (i j : α) (fraction : ℚ)

def plusWord {α : Type*} : List (RoundBlock α) → List α
  | [] => []
  | .one i :: bs => i :: plusWord bs
  | .cut i j _ :: bs => i :: j :: plusWord bs

def minusWord {α : Type*} : List (RoundBlock α) → List α
  | [] => []
  | .one i :: bs => i :: minusWord bs
  | .cut i j _ :: bs => j :: i :: minusWord bs

def splitPairs {α : Type*} : List (RoundBlock α) → List (α × α)
  | [] => []
  | .one _ :: bs => splitPairs bs
  | .cut i j _ :: bs => (i,j) :: splitPairs bs

/-- Literal label transpositions in list order, equivalently a left fold. -/
def swapAlong {α : Type*} [DecidableEq α] : List (α × α) → List α → List α
  | [], w => w
  | ij :: ps, w => swapAlong ps (w.map (Equiv.swap ij.1 ij.2))

/-- Old-word prefixSum lengths of the unique new state in each rounded block. -/
def cornerPositions {α : Type*} : List (RoundBlock α) → List ℕ
  | [] => []
  | .one _ :: bs => (cornerPositions bs).map (fun n => n + 1)
  | .cut _ _ _ :: bs => 1 :: (cornerPositions bs).map (fun n => n + 2)

def prefixSum {α : Type*} (f : α → ℚ) (w : List α) (n : ℕ) : ℚ :=
  ((w.take n).map f).sum

def Rectangle (H N x y : ℚ) : Prop := 0 ≤ x ∧ x ≤ H ∧ 0 ≤ y ∧ y ≤ N

/-- All four vertices of a fractional cut block, and all unchanged boundary
vertices, lie in the same rectangle. This is an internal geometric hypothesis
for the rounding lemma, not an assumption of the physical necklace target. -/
def FractionalFits {α : Type*} (f g : α → ℚ) (H N : ℚ) :
    ℚ → ℚ → List (RoundBlock α) → Prop
  | x, y, [] => Rectangle H N x y
  | x, y, .one i :: bs =>
      Rectangle H N x y ∧ FractionalFits f g H N (x + f i) (y + g i) bs
  | x, y, .cut i j t :: bs =>
      0 < f i ∧ 0 < g i ∧ f j < 0 ∧ g j < 0 ∧ 0 < t ∧ t < 1 ∧
      Rectangle H N x y ∧
      Rectangle H N (x + t * f i) (y + t * g i) ∧
      Rectangle H N (x + t * f i + f j) (y + t * g i + g j) ∧
      FractionalFits f g H N (x + f i + f j) (y + g i + g j) bs

private theorem rounded_perm {α : Type*} (bs : List (RoundBlock α)) :
    (plusWord bs).Perm (minusWord bs) := by
  induction bs with
  | nil => exact .refl _
  | cons b bs ih =>
    cases b with
    | one i => exact ih.cons i
    | cut i j t =>
      exact (List.Perm.swap _ _ _).trans ((ih.cons i).cons j)

private theorem corner_length {α : Type*} (bs : List (RoundBlock α)) :
    (cornerPositions bs).length = (splitPairs bs).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [cornerPositions, splitPairs, ih]

private theorem corner_range {α : Type*} (bs : List (RoundBlock α)) :
    ∀ n ∈ cornerPositions bs, 1 ≤ n ∧ n < (plusWord bs).length := by
  induction bs with
  | nil => simp [cornerPositions]
  | cons b bs ih =>
    cases b with
    | one i =>
      intro n hn
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      have := ih m hm
      simp only [plusWord, List.length_cons]
      omega
    | cut i j t =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · simp [plusWord]
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
        have := ih m hm
        simp only [plusWord, List.length_cons]
        omega

private theorem corner_nodup {α : Type*} (bs : List (RoundBlock α)) :
    (cornerPositions bs).Nodup := by
  induction bs with
  | nil => exact .nil
  | cons b bs ih =>
    cases b with
    | one i =>
      exact ih.map (by intro a b hab; dsimp at hab; omega)
    | cut i j t =>
      refine List.nodup_cons.mpr ⟨?_, ih.map (by intro a b hab; dsimp at hab; omega)⟩
      intro hm
      obtain ⟨n, hn, he⟩ := List.mem_map.mp hm
      omega

private theorem pair_inventory_sublist {α : Type*} (bs : List (RoundBlock α)) :
    ((splitPairs bs).flatMap (fun ij => [ij.1, ij.2])).Sublist (plusWord bs) := by
  induction bs with
  | nil => exact .refl _
  | cons b bs ih =>
    cases b with
    | one i => exact List.Sublist.cons i ih
    | cut i j t => exact (ih.cons_cons j).cons_cons i

private theorem swapAlong_cons {α : Type*} [DecidableEq α]
    (ps : List (α × α)) (a : α) (w : List α)
    (ha : a ∉ ps.flatMap (fun ij => [ij.1,ij.2])) :
    swapAlong ps (a :: w) = a :: swapAlong ps w := by
  revert ha
  induction ps generalizing w with
  | nil => intro _; rfl
  | cons ij ps ih =>
    intro ha
    have h1 : a ≠ ij.1 := by intro he; apply ha; simp [he]
    have h2 : a ≠ ij.2 := by intro he; apply ha; simp [he]
    have ht : a ∉ ps.flatMap (fun ij => [ij.1,ij.2]) := by
      intro hm; apply ha; simp [hm]
    simp only [swapAlong, List.map_cons, Equiv.swap_apply_of_ne_of_ne h1 h2]
    exact ih _ ht

private theorem literal_swaps {α : Type*} [DecidableEq α]
    (bs : List (RoundBlock α)) (hnd : (plusWord bs).Nodup) :
    swapAlong (splitPairs bs) (plusWord bs) = minusWord bs := by
  revert hnd
  induction bs with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hnd
    have hsub := pair_inventory_sublist bs
    cases b with
    | one i =>
      have hn := List.nodup_cons.mp hnd
      have hi : i ∉ (splitPairs bs).flatMap (fun ij => [ij.1,ij.2]) := by
        intro hm; exact hn.1 (hsub.subset hm)
      change swapAlong (splitPairs bs) (i :: plusWord bs) = i :: minusWord bs
      rw [swapAlong_cons _ _ _ hi, ih hn.2]
    | cut i j t =>
      have hn := List.nodup_cons.mp hnd
      have hn' := List.nodup_cons.mp hn.2
      have hi : i ∉ plusWord bs := by intro hm; exact hn.1 (by simp [hm])
      have hj : j ∉ plusWord bs := hn'.1
      have hip : i ∉ (splitPairs bs).flatMap (fun ij => [ij.1,ij.2]) :=
        fun hm => hi (hsub.subset hm)
      have hjp : j ∉ (splitPairs bs).flatMap (fun ij => [ij.1,ij.2]) :=
        fun hm => hj (hsub.subset hm)
      have hmap : (plusWord bs).map (Equiv.swap i j) = plusWord bs := by
        calc
          _ = (plusWord bs).map id := List.map_congr_left (by
            intro a ha
            exact Equiv.swap_apply_of_ne_of_ne
              (by intro he; exact hi (he ▸ ha))
              (by intro he; exact hj (he ▸ ha)))
          _ = _ := List.map_id _
      change swapAlong ((i,j) :: splitPairs bs) (i :: j :: plusWord bs) =
        j :: i :: minusWord bs
      simp only [swapAlong, List.map_cons, Equiv.swap_apply_left,
        Equiv.swap_apply_right, hmap]
      rw [swapAlong_cons _ _ _ hjp, swapAlong_cons _ _ _ hip, ih hn'.2]

private theorem pair_locations {α : Type*} (bs : List (RoundBlock α)) :
    ∀ ij ∈ splitPairs bs, ∃ u v u' v' : List α,
      plusWord bs = u ++ [ij.1, ij.2] ++ v ∧
      minusWord bs = u' ++ [ij.2, ij.1] ++ v' ∧ u.length = u'.length := by
  induction bs with
  | nil => simp [splitPairs]
  | cons b bs ih =>
    cases b with
    | one i =>
      intro ij hij
      obtain ⟨u,v,u',v',hp,hm,hlen⟩ := ih ij hij
      refine ⟨i :: u,v,i :: u',v',?_,?_,by simpa using hlen⟩
      · simpa [plusWord] using congrArg (List.cons i) hp
      · simpa [minusWord] using congrArg (List.cons i) hm
    | cut i j t =>
      intro ij hij
      rcases List.mem_cons.mp hij with rfl | hij
      · exact ⟨[],plusWord bs,[],minusWord bs,rfl,rfl,rfl⟩
      · obtain ⟨u,v,u',v',hp,hm,hlen⟩ := ih ij hij
        refine ⟨i :: j :: u,v,j :: i :: u',v',?_,?_,by simpa using hlen⟩
        · simpa [plusWord] using congrArg (fun w => i :: j :: w) hp
        · simpa [minusWord] using congrArg (fun w => j :: i :: w) hm

private theorem corner_locations {α : Type*} (bs : List (RoundBlock α)) :
    ∀ n ∈ cornerPositions bs, ∃ ij ∈ splitPairs bs, ∃ u v u' v' : List α,
      plusWord bs = u ++ [ij.1, ij.2] ++ v ∧
      minusWord bs = u' ++ [ij.2, ij.1] ++ v' ∧
      u.length + 1 = n ∧ u'.length + 1 = n := by
  induction bs with
  | nil => simp [cornerPositions]
  | cons b bs ih =>
    cases b with
    | one i =>
      intro n hn
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hn
      obtain ⟨ij,hij,u,v,u',v',hp,hm,he,he'⟩ := ih m hm
      refine ⟨ij,hij,i :: u,v,i :: u',v',?_,?_,?_,?_⟩
      · simpa [plusWord] using congrArg (List.cons i) hp
      · simpa [minusWord] using congrArg (List.cons i) hm
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
    | cut i j t =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨(i,j),by simp [splitPairs],[],plusWord bs,[],minusWord bs,rfl,rfl,rfl,rfl⟩
      · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hn
        obtain ⟨ij,hij,u,v,u',v',hp,hm,he,he'⟩ := ih m hm
        refine ⟨ij,by simp [splitPairs,hij],i :: j :: u,v,j :: i :: u',v',?_,?_,?_,?_⟩
        · simpa [plusWord] using congrArg (fun w => i :: j :: w) hp
        · simpa [minusWord] using congrArg (fun w => j :: i :: w) hm
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega

private theorem pair_signs {α : Type*} (f g : α → ℚ) (H N x y : ℚ)
    (bs : List (RoundBlock α)) (hf : FractionalFits f g H N x y bs) :
    ∀ ij ∈ splitPairs bs, 0 < f ij.1 ∧ 0 < g ij.1 ∧ f ij.2 < 0 ∧ g ij.2 < 0 := by
  induction bs generalizing x y with
  | nil => simp [splitPairs]
  | cons b bs ih =>
    cases b with
    | one i => exact ih _ _ hf.2
    | cut i j t =>
      rcases hf with ⟨hi,hgi,hj,hgj,ht,ht1,hA,hB,hC,hD⟩
      intro ij hij
      rcases List.mem_cons.mp hij with rfl | hij
      · exact ⟨hi,hgi,hj,hgj⟩
      · exact ih _ _ hD ij hij

private theorem prefix_control {α : Type*} (f g : α → ℚ) (H N x y : ℚ)
    (bs : List (RoundBlock α)) (hf : FractionalFits f g H N x y bs) :
    ∀ n : ℕ,
      0 ≤ x + prefixSum f (plusWord bs) n ∧
      0 ≤ y + prefixSum g (plusWord bs) n ∧
      x + prefixSum f (minusWord bs) n ≤ H ∧
      y + prefixSum g (minusWord bs) n ≤ N ∧
      (n ∉ cornerPositions bs →
        x + prefixSum f (plusWord bs) n ≤ H ∧
        y + prefixSum g (plusWord bs) n ≤ N ∧
        0 ≤ x + prefixSum f (minusWord bs) n ∧
        0 ≤ y + prefixSum g (minusWord bs) n ∧
        prefixSum f (plusWord bs) n = prefixSum f (minusWord bs) n ∧
        prefixSum g (plusWord bs) n = prefixSum g (minusWord bs) n) := by
  induction bs generalizing x y with
  | nil =>
    intro n
    rcases hf with ⟨hx,hxH,hy,hyN⟩
    simp [plusWord,minusWord,prefixSum,hx,hxH,hy,hyN]
  | cons b bs ih =>
    cases b with
    | one i =>
      rcases hf with ⟨hA,hT⟩
      intro n
      cases n with
      | zero =>
        rcases hA with ⟨hx,hxH,hy,hyN⟩
        simp [prefixSum,hx,hxH,hy,hyN]
      | succ n =>
        have hh := ih (x + f i) (y + g i) hT n
        simpa [plusWord,minusWord,prefixSum,cornerPositions,add_assoc] using hh
    | cut i j t =>
      rcases hf with ⟨hi,hgi,hj,hgj,ht,ht1,hA,hB,hC,hT⟩
      intro n
      cases n with
      | zero =>
        rcases hA with ⟨hx,hxH,hy,hyN⟩
        simp [prefixSum,hx,hxH,hy,hyN]
      | succ n =>
        cases n with
        | zero =>
          rcases hB with ⟨hxB,hxBH,hyB,hyBN⟩
          rcases hC with ⟨hxC,hxCH,hyC,hyCN⟩
          have hxU : 0 ≤ x + f i := by nlinarith
          have hyU : 0 ≤ y + g i := by nlinarith
          have hxV : x + f j ≤ H := by nlinarith
          have hyV : y + g j ≤ N := by nlinarith
          simp [plusWord,minusWord,prefixSum,cornerPositions,hxU,hyU,hxV,hyV]
        | succ n =>
          have hh := ih (x + f i + f j) (y + g i + g j) hT n
          have he : n + 1 + 1 ≠ 1 := by omega
          simpa [plusWord,minusWord,prefixSum,cornerPositions,he,
            add_assoc,add_comm,add_left_comm] using hh

private theorem finite_error_card (m : ℕ) (P : Fin m → Prop) [DecidablePred P]
    (corners : List ℕ) (h : ∀ q, P q → q.val ∈ corners) :
    (Finset.univ.filter P).card ≤ corners.length := by
  have hc : (Finset.univ.filter P).card ≤ corners.toFinset.card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro q hq
      exact List.mem_toFinset.mpr (h q (Finset.mem_filter.mp hq).2)
    · intro a _ b _ he
      exact Fin.ext he
  exact hc.trans (List.toFinset_card_le _)

/-- The complete conclusion with the two word outputs explicit. -/
def RoundingConclusion {α : Type*} [DecidableEq α]
    (f g : α → ℚ) (H N x y : ℚ) (bs : List (RoundBlock α))
    (wp wm : List α) : Prop :=
    wp.Perm wm ∧
    (wp.map f).sum = (wm.map f).sum ∧
    (wp.map g).sum = (wm.map g).sum ∧
    ((splitPairs bs).flatMap (fun ij => [ij.1,ij.2])).Nodup ∧
    swapAlong (splitPairs bs) wp = wm ∧
    (cornerPositions bs).Nodup ∧
    (cornerPositions bs).length = (splitPairs bs).length ∧
    (∀ n ∈ cornerPositions bs, 1 ≤ n ∧ n < wp.length) ∧
    (∀ ij ∈ splitPairs bs,
      0 < f ij.1 ∧ 0 < g ij.1 ∧ f ij.2 < 0 ∧ g ij.2 < 0) ∧
    (∀ n : ℕ,
      0 ≤ x + prefixSum f wp n ∧
      0 ≤ y + prefixSum g wp n ∧
      x + prefixSum f wm n ≤ H ∧
      y + prefixSum g wm n ≤ N ∧
      (n ∉ cornerPositions bs →
        x + prefixSum f wp n ≤ H ∧
        y + prefixSum g wp n ≤ N ∧
        0 ≤ x + prefixSum f wm n ∧
        0 ≤ y + prefixSum g wm n ∧
        prefixSum f wp n = prefixSum f wm n ∧
        prefixSum g wp n = prefixSum g wm n)) ∧
    (∀ n ∈ cornerPositions bs, ∃ ij ∈ splitPairs bs, ∃ u v u' v' : List α,
      wp = u ++ [ij.1,ij.2] ++ v ∧
      wm = u' ++ [ij.2,ij.1] ++ v' ∧
      u.length + 1 = n ∧ u'.length + 1 = n) ∧
    (∀ ij ∈ splitPairs bs, ∃ u v u' v' : List α,
      wp = u ++ [ij.1,ij.2] ++ v ∧
      wm = u' ++ [ij.2,ij.1] ++ v' ∧ u.length = u'.length) ∧
    (∀ m : ℕ,
      (Finset.univ.filter (fun q : Fin m =>
        H < x + prefixSum f wp q.val ∨
        N < y + prefixSum g wp q.val)).card ≤ (splitPairs bs).length) ∧
    (∀ m : ℕ,
      (Finset.univ.filter (fun q : Fin m =>
        x + prefixSum f wm q.val < 0 ∨
        y + prefixSum g wm q.val < 0)).card ≤ (splitPairs bs).length)

/-- Simultaneous rounding for an arbitrary finite list of split blocks. There
is one possible corner for each split, not one accumulating error per prefixSum.
The adjacency relation is represented by the very same list of one-label
and two-label blocks in the two expansions. -/
theorem simultaneous_rounding {α : Type*} [DecidableEq α]
    (f g : α → ℚ) (H N x y : ℚ) (bs : List (RoundBlock α))
    (hf : FractionalFits f g H N x y bs) (hnd : (plusWord bs).Nodup) :
    RoundingConclusion f g H N x y bs (plusWord bs) (minusWord bs) := by
  unfold RoundingConclusion
  have hp := rounded_perm bs
  have hc := prefix_control f g H N x y bs hf
  refine ⟨hp,(hp.map f).sum_eq,(hp.map g).sum_eq,
    List.Nodup.sublist (pair_inventory_sublist bs) hnd,literal_swaps bs hnd,
    corner_nodup bs,corner_length bs,corner_range bs,
    pair_signs f g H N x y bs hf,hc,corner_locations bs,pair_locations bs,?_,?_⟩
  · intro m
    rw [← corner_length bs]
    apply finite_error_card
    intro q hq
    by_contra hn
    have hh := (hc q.val).2.2.2.2 hn
    rcases hq with hq | hq <;> linarith [hh.1,hh.2.1]
  · intro m
    rw [← corner_length bs]
    apply finite_error_card
    intro q hq
    by_contra hn
    have hh := (hc q.val).2.2.2.2 hn
    rcases hq with hq | hq <;> linarith [hh.2.2.1,hh.2.2.2.1]

end D5.S3.Combinatorics.Circle.SparseNecklaceRounding
