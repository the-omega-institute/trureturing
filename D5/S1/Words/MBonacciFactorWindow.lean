/- GID: D5/S1/Words/MBonacciFactorWindow
   generality: I
   mirror-B: D5/B/S1/Words/MBonacciFactorWindow
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Every actual m-bonacci factor has an occurrence within the exact image-weight window. -/
import D5.S1.Words.MBonacciMinimumGreedy
import D5.S1.Words.GoldenUniformRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciFactorWindow

open MBonacciSentinelDesubstitution
open MBonacciMinimumGreedy (U)
open RankOneMorphismIterationBound (subst image image_add subst_append)
open AbelianBorders.AbelianBorderQuestionDefs (factor)

variable {m : ℕ} (hm : 2 ≤ m)

private theorem common_prefix_window {α β : Type*} {f : α → List β}
    {l : List α} {c : List β} {q n : ℕ}
    (hn : 0 < n) (hsize : n ≤ c.length)
    (hcommon : ∀ a, c <+: f a) (hend : q + n ≤ (l.flatMap f).length) :
    ∃ a, ((l.flatMap f).drop q).take n <:+: f a ++ c := by
  have hq : q < (l.flatMap f).length := by omega
  obtain ⟨pre, a, post, he, hlo, hhi⟩ := exists_flatMap_block hq
  subst l
  let offset := q - (pre.flatMap f).length
  have hqeq : q = (pre.flatMap f).length + offset := by dsimp [offset]; omega
  have hoff : offset < (f a).length := by dsimp [offset]; omega
  have hdrop : (((pre ++ a :: post).flatMap f).drop q).take n =
      (((a :: post).flatMap f).drop offset).take n := by
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hqeq, ← List.drop_drop]
    simp
  refine ⟨a, ?_⟩
  rw [hdrop]
  cases post with
  | nil =>
    have he : offset + n ≤ (f a).length := by
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.length_append] at hend
      omega
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← take_drop_append_eq_left (y := c) he]
    exact take_drop_isInfix _ _ _
  | cons b tail =>
    obtain ⟨v, hv⟩ := hcommon b
    have hbound : offset + n ≤ (f a ++ c).length := by
      simp only [List.length_append]; omega
    simp only [List.flatMap_cons]
    rw [← hv]
    rw [show f a ++ ((c ++ v) ++ tail.flatMap f) =
      (f a ++ c) ++ (v ++ tail.flatMap f) by simp [List.append_assoc]]
    rw [take_drop_append_eq_left hbound]
    exact take_drop_isInfix _ _ _

private theorem letter_mem_own_iterate (a : Fin m) :
    a ∈ image (phi hm) a.val (zero hm) := by
  have h : ∀ i (hi : i < m), (⟨i, hi⟩ : Fin m) ∈ image (phi hm) i (zero hm) := by
    intro i
    induction i with
    | zero => intro hi; simp [image, zero]
    | succ i ih =>
      intro hi
      have hi' : i < m := by omega
      have hp := ih hi'
      change (⟨i + 1, hi⟩ : Fin m) ∈ (image (phi hm) i (zero hm)).flatMap (phi hm)
      apply List.mem_flatMap.mpr
      refine ⟨⟨i, hi'⟩, hp, ?_⟩
      simp [phi, hi]
  exact h a.val a.isLt

private theorem letter_mem_control (a : Fin m) :
    a ∈ image (phi hm) (m - 1) (zero hm) := by
  exact (iterate_prefix hm (show a.val ≤ m - 1 by have := a.isLt; omega)).sublist.subset
    (letter_mem_own_iterate hm a)

private theorem sentinel_image_infix_control (a : Fin m) :
    phi hm a ++ [zero hm] <:+: image (phi hm) m (zero hm) ++ [zero hm] := by
  obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp (letter_mem_control hm a)
  have hstep : image (phi hm) m (zero hm) =
      subst (phi hm) (image (phi hm) (m - 1) (zero hm)) := by
    calc
      image (phi hm) m (zero hm) = image (phi hm) ((m - 1) + 1) (zero hm) :=
        congrArg (fun j => image (phi hm) j (zero hm)) (by omega)
      _ = _ := rfl
  obtain ⟨v, hv⟩ := t_head hm post
  refine ⟨subst (phi hm) pre, v, ?_⟩
  rw [hstep, he]
  simp only [subst_append, RankOneMorphismIterationBound.subst_cons]
  simpa only [T, List.append_assoc, List.singleton_append] using
    congrArg (fun t => subst (phi hm) pre ++ (phi hm a ++ t)) hv.symm

private theorem image_common_prefix (k : ℕ) (a : Fin m) :
    image (phi hm) k (zero hm) <+: image (phi hm) (k + 1) a := by
  rw [image_add _ k 1]
  unfold phi
  simp only [RankOneMorphismIterationBound.image_one]
  split_ifs
  · simp only [subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.prefix_append _ _
  · simp [subst]

private theorem factor_eq_take_drop (L q n : ℕ)
    (hend : q + n ≤ (image (phi hm) L (zero hm)).length) :
    factor (word hm) q n = ((image (phi hm) L (zero hm)).drop q).take n := by
  apply List.ext_getElem
  · simp only [factor, List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro i hi hj
    have hin : i < n := by simpa [factor] using hi
    rw [factor_get _ _ _ _ hin]
    rw [List.getElem_take, List.getElem_drop]
    exact word_eq_iterate hm L (q + i) (by omega)

private theorem control_image (k : ℕ) :
    subst (image (phi hm) k) (image (phi hm) m (zero hm) ++ [zero hm]) =
      image (phi hm) (k + m) (zero hm) ++ image (phi hm) k (zero hm) := by
  rw [subst_append, ← image_add]
  simp [subst]

private theorem factor_infix_control (k n q : ℕ) (hn : 0 < n) (hsize : n ≤ U hm k) :
    factor (word hm) q n <:+:
      image (phi hm) (k + m) (zero hm) ++ image (phi hm) k (zero hm) := by
  let L := (k + 1) + (q + n + 1)
  have hend : q + n ≤ (image (phi hm) L (zero hm)).length := by
    have h := iterate_growth hm L
    dsimp [L] at h ⊢
    omega
  have hdecomp : image (phi hm) L (zero hm) =
      (image (phi hm) (q + n + 1) (zero hm)).flatMap (image (phi hm) (k + 1)) := by
    exact image_add _ _ _ _
  have hfinite : q + n ≤
      ((image (phi hm) (q + n + 1) (zero hm)).flatMap (image (phi hm) (k + 1))).length := by
    rw [← hdecomp]
    exact hend
  obtain ⟨a, ha⟩ := common_prefix_window hn hsize (image_common_prefix hm k) hfinite
  rw [factor_eq_take_drop hm L q n hend, hdecomp]
  have hs : image (phi hm) (k + 1) a ++ image (phi hm) k (zero hm) =
      subst (image (phi hm) k) (phi hm a ++ [zero hm]) := by
    rw [image_add _ k 1]
    simp [subst]
  have ht := (sentinel_image_infix_control hm a).flatMap (image (phi hm) k)
  rw [hs] at ha
  change subst (image (phi hm) k) (phi hm a ++ [zero hm]) <:+:
    subst (image (phi hm) k) (image (phi hm) m (zero hm) ++ [zero hm]) at ht
  rw [control_image hm k] at ht
  exact ha.trans ht

private theorem control_prefix :
    image (phi hm) m (zero hm) ++ [zero hm] <+:
      image (phi hm) (m + 1) (zero hm) := by
  let one : Fin m := ⟨1, by omega⟩
  have hzero : [zero hm] <+: image (phi hm) m one := by
    have h := (iterate_prefix hm (k := 0) (t := m - 1) (by omega)).trans
      (image_common_prefix hm (m - 1) one)
    simpa only [RankOneMorphismIterationBound.image_zero,
      show m - 1 + 1 = m by omega] using h
  obtain ⟨v, hv⟩ := hzero
  refine ⟨v, ?_⟩
  rw [image_add _ m 1]
  simp only [RankOneMorphismIterationBound.image_one, phi, zero,
    show 0 + 1 < m by omega, ↓reduceDIte, subst,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (image (phi hm) m (zero hm) ++ [zero hm]) ++ v =
    image (phi hm) m (zero hm) ++ image (phi hm) m one
  rw [List.append_assoc, hv]

/-- Every positive window no longer than the kth actual image weight has an
identical occurrence at a start at most the (k+m)th weight. -/
theorem factor_window (k n : ℕ) (hn : 1 ≤ n) (hsize : n ≤ U hm k) (q : ℕ) :
    ∃ p : ℕ, p ≤ U hm (k + m) ∧ factor (word hm) q n = factor (word hm) p n := by
  let A := image (phi hm) (k + m) (zero hm)
  let C := A ++ image (phi hm) k (zero hm)
  have hcontrol : C <+: image (phi hm) (k + (m + 1)) (zero hm) := by
    have h := (control_prefix hm).flatMap (image (phi hm) k)
    change subst (image (phi hm) k) (image (phi hm) m (zero hm) ++ [zero hm]) <+:
      subst (image (phi hm) k) (image (phi hm) (m + 1) (zero hm)) at h
    rw [control_image hm k, ← image_add] at h
    exact h
  obtain ⟨pre, post, hsplit⟩ := factor_infix_control hm k n q (by omega) hsize
  let r := pre.length
  have hlen : (factor (word hm) q n).length = n := by simp [factor]
  have hrn : r + n ≤ C.length := by
    have h := congrArg List.length hsplit
    simp only [List.length_append, hlen] at h
    change r + n ≤ C.length
    dsimp [r, C, A]
    simp only [List.length_append]
    omega
  have htake : (C.drop r).take n = factor (word hm) q n := by
    change ((image (phi hm) (k + m) (zero hm) ++ image (phi hm) k (zero hm)).drop
      pre.length).take n = _
    rw [← hsplit]
    simp [hlen]
  by_cases hr : r ≤ A.length
  · refine ⟨r, hr, ?_⟩
    have hbig : r + n ≤ (image (phi hm) (k + (m + 1)) (zero hm)).length :=
      hrn.trans hcontrol.length_le
    obtain ⟨v, hv⟩ := hcontrol
    rw [factor_eq_take_drop hm _ r n hbig, ← hv,
      take_drop_append_eq_left hrn, htake]
  · let p := r - A.length
    have hp : p + n ≤ (image (phi hm) k (zero hm)).length := by
      simp only [C, List.length_append] at hrn
      dsimp [p]
      omega
    have hweights : (image (phi hm) k (zero hm)).length ≤ A.length :=
      (iterate_prefix hm (show k ≤ k + m by omega)).length_le
    refine ⟨p, ?_, ?_⟩
    · change p ≤ A.length
      omega
    · rw [factor_eq_take_drop hm k p n hp, ← htake]
      dsimp only [C, p]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]

end D5.S1.Words.MBonacciFactorWindow
