/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native Fibonacci defects form orthogonal cubes with exact intrinsic volume. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.ActualHistorySingleHoleRecovery
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube

open GenealogicalFiberTransport (Source)
open ActualLeafHistoryRigidity (OutputContext subtree)
open ActualTreeReadoutAcquisition (Address)
open GenealogicalFiberTransport (substitution)
open D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)
open AncestorAreaInstability (T depth)
open ActualImageAddressCertificate (replace)
open scoped BigOperators symmDiff Pointwise

noncomputable section
open AncestorAreaInterval (coordinates offset)

/- The two three-leaf trees in the defect. -/
def defectB : Source := .mul (.mul (.of false) (.of true)) (.of false)
def defectD : Source := .mul (.of false) (.mul (.of true) (.of false))

private theorem coordinate_list_length (t : Source) : (coordinates t).length = t.length - 1 := by
  induction t with
  | of b => rfl
  | mul l r hl hr =>
      have hlp := FreeMagma.length_pos l
      have hrp := FreeMagma.length_pos r
      simp only [coordinates, List.length_append, List.length_singleton, hl, hr,
        FreeMagma.length]
      omega

private theorem equal_length_coordinate_splice
    (C : OutputContext) (x y : Source) (hxy : x.length = y.length) :
    ∃ L R : List ℕ,
      coordinates (C.plug x) = L ++ coordinates x ++ R ∧
      coordinates (C.plug y) = L ++ coordinates y ++ R ∧
      L.length = offset (C.plug x) C.holeAddress := by
  induction C generalizing x y with
  | hole =>
      exact ⟨[], [], by simp [OutputContext.plug], by simp [OutputContext.plug],
        by simp [OutputContext.holeAddress, offset]⟩
  | left C r ih =>
      obtain ⟨L, R, hx, hy, hL⟩ := ih x y hxy
      have hlen : (C.plug x).length = (C.plug y).length := by
        rw [ActualHistorySingleHoleRecovery.context_length,
          ActualHistorySingleHoleRecovery.context_length, hxy]
      let Q : List ℕ := R ++ [(C.plug x).length * r.length] ++ coordinates r
      refine ⟨L, Q, ?_, ?_, ?_⟩
      · simp only [OutputContext.plug, coordinates, Q, hx, List.append_assoc]
      · simp only [OutputContext.plug, coordinates, Q, hy, hlen, List.append_assoc]
      · simpa only [OutputContext.holeAddress, OutputContext.plug, offset] using hL
  | right l C ih =>
      obtain ⟨L, R, hx, hy, hL⟩ := ih x y hxy
      have hlen : (C.plug x).length = (C.plug y).length := by
        rw [ActualHistorySingleHoleRecovery.context_length,
          ActualHistorySingleHoleRecovery.context_length, hxy]
      let P : List ℕ := coordinates l ++ [l.length * (C.plug x).length] ++ L
      refine ⟨P, R, ?_, ?_, ?_⟩
      · simp only [OutputContext.plug, coordinates, P, hx, List.append_assoc]
      · simp only [OutputContext.plug, coordinates, P, hy, hlen, List.append_assoc]
      · have hcoord : (coordinates l).length = l.length - 1 := coordinate_list_length l
        have hlpos := l.length_pos
        simp only [OutputContext.holeAddress, OutputContext.plug, offset, P,
          List.length_append, List.length_singleton, hcoord] at hL ⊢
        omega

private theorem defect_coordinates :
    coordinates defectB = [1, 2] ∧ coordinates defectD = [2, 1] := by
  decide

private theorem defect_length : defectB.length = defectD.length := by decide

/-- All actual occurrences of the three-leaf source, with their literal addresses. -/
def positions : Source → Finset Address
  | .of _ => ∅
  | .mul l r => (if .mul l r = defectB then {[]} else ∅) ∪
      (positions l).image (false :: ·) ∪ (positions r).image (true :: ·)

/-- Simultaneous choices are read at their original addresses in the source. -/
def fill : Source → (Address → Bool) → Source
  | .of b, _ => .of b
  | .mul l r, a => if .mul l r = defectB then
      (if a [] then defectD else defectB)
    else .mul (fill l (fun p => a (false :: p))) (fill r (fun p => a (true :: p)))

/-- The selected finite subset specifies the actual simultaneous substitutions. -/
def variant (t : Source) (A : Finset Address) : Source := fill t (fun p => decide (p ∈ A))

private theorem positions_B : positions defectB = {[]} := by decide

private theorem mem_positions (t : Source) (p : Address) :
    p ∈ positions t ↔ subtree p t = some defectB := by
  induction t generalizing p with
  | of b => cases p <;> simp [positions, subtree, defectB]
  | mul l r hl hr =>
    cases p with
    | nil => by_cases h : l * r = defectB <;> simp [positions, subtree, h]
    | cons b p =>
      by_cases h : l * r = defectB <;> cases b <;>
        simp [positions, subtree, hl, hr, h]

private theorem fill_length_word (t : Source) (a : Address → Bool) :
    (fill t a).length = t.length ∧ wd (fill t a) = wd t := by
  induction t generalizing a with
  | of b => exact ⟨rfl, rfl⟩
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · rw [fill, if_pos h, h]
      cases a [] <;> exact ⟨rfl, rfl⟩
    · rw [fill, if_neg h]
      exact ⟨by simp only [FreeMagma.length, (hl _).1, (hr _).1],
        by simpa [wd, map_mul] using congrArg₂ (· ++ ·) (hl _).2 (hr _).2⟩

theorem fill_at (t : Source) (a : Address → Bool) (p : Address)
    (hp : p ∈ positions t) :
    subtree p (fill t a) = some (if a p then defectD else defectB) := by
  induction t generalizing a p with
  | of b => simp [positions] at hp
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · have he : p = [] := by simpa only [h, positions_B, Finset.mem_singleton] using hp
      subst p
      simp only [fill, if_pos h, subtree]
    · rw [fill, if_neg h]
      cases p with
      | nil =>
        have hx := (mem_positions (.mul l r) []).mp hp
        exact False.elim (h (Option.some.inj hx))
      | cons b p =>
        cases b with
        | false =>
          apply hl
          exact (mem_positions l p).mpr ((mem_positions (.mul l r) (false :: p)).mp hp)
        | true =>
          apply hr
          exact (mem_positions r p).mpr ((mem_positions (.mul l r) (true :: p)).mp hp)

private theorem fill_unchanged (t : Source) (a : Address → Bool)
    (ha : ∀ p ∈ positions t, a p = false) : fill t a = t := by
  induction t generalizing a with
  | of b => rfl
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · have hz := ha [] (by rw [h, positions_B]; simp)
      simp only [fill, if_pos h, hz, Bool.false_eq_true, ↓reduceIte]
      exact h.symm
    · rw [fill, if_neg h, hl, hr]
      · intro p hp
        exact ha (true :: p) ((mem_positions _ _).mpr ((mem_positions r p).mp hp))
      · intro p hp
        exact ha (false :: p) ((mem_positions _ _).mpr ((mem_positions l p).mp hp))

private theorem variant_injective (t : Source) :
    Function.Injective (fun A : {A : Finset Address // A ⊆ positions t} => variant t A.val) := by
  intro A B h
  change variant t A.val = variant t B.val at h
  apply Subtype.ext
  apply Finset.ext
  intro p
  by_cases hp : p ∈ positions t
  · have ha := fill_at t (fun p => decide (p ∈ A.val)) p hp
    have hb := fill_at t (fun p => decide (p ∈ B.val)) p hp
    change subtree p (variant t A.val) = _ at ha
    change subtree p (variant t B.val) = _ at hb
    rw [h, hb] at ha
    have hne : defectB ≠ defectD := by decide
    by_cases hA : p ∈ A.val <;> by_cases hB : p ∈ B.val
    · exact iff_of_true hA hB
    · exact False.elim (hne (by simpa [hA,hB] using Option.some.inj ha))
    · exact False.elim (hne (by simpa [hA,hB] using (Option.some.inj ha).symm))
    · exact iff_of_false hA hB
  · exact iff_of_false (fun h => hp (A.property h)) (fun h => hp (B.property h))

private theorem defect_not_image : ¬ ∃ x : Source, substitution x = defectD := by
  intro h
  rcases (SourceCoordinates.IntrinsicSubstitutionCoordinates.pair_image _ _).mp h with h | ⟨_,h⟩
  · cases h.2
  · rcases (SourceCoordinates.IntrinsicSubstitutionCoordinates.pair_image _ _).mp h with h | ⟨h,_⟩
    · cases h.1
    · obtain ⟨x,hx⟩ := h
      exact SourceCoordinates.IntrinsicSubstitutionCoordinates.no_alpha x hx

private theorem containing_defect_not_image (t : Source) (p : Address)
    (hp : subtree p t = some defectD) : ¬ ∃ x : Source, substitution x = t := by
  induction p generalizing t with
  | nil => exact (Option.some.inj hp) ▸ defect_not_image
  | cons b p ih =>
    cases t with
    | of c => simp [subtree] at hp
    | mul l r =>
      intro h
      rcases (SourceCoordinates.IntrinsicSubstitutionCoordinates.pair_image l r).mp h with
        h | ⟨hl,hr⟩
      · obtain ⟨rfl,rfl⟩ := h
        cases b <;> cases p <;> simp [subtree, defectD] at hp
      · cases b with
        | false => exact ih l hp hl
        | true => exact ih r hp hr

private theorem variant_depth (t : Source) (A : Finset Address)
    (hA : A ⊆ positions t) (hne : A.Nonempty) : depth (variant t A) = 0 := by
  obtain ⟨p,hp⟩ := hne
  have hat := fill_at t (fun p => decide (p ∈ A)) p (hA hp)
  have hsub : subtree p (variant t A) = some defectD := by simpa [variant, hp] using hat
  have hn := containing_defect_not_image _ _ hsub
  have h := (SourceCoordinates.IntrinsicSubstitutionCoordinates.intrinsic_coordinates
    (variant t A)).1 1
  have hz : ¬ 1 ≤ depth (variant t A) := by
    intro hh
    obtain ⟨x,hx⟩ := h.mpr hh
    exact hn ⟨x,hx⟩
  omega

private theorem positions_card (n : ℕ) :
    (positions (T (n+3))).card = Nat.fib (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n hn hn1 =>
    have recurrence :=
      (SourceTransportCentralizer.source_transport_centralizer.1 (T (n+3))).mpr ⟨n+3,rfl⟩
    have ht : T (n+2+3) = .mul (T (n+1+3)) (T (n+3)) := by
      simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using recurrence
    have hne : .mul (T (n+1+3)) (T (n+3)) ≠ defectB := by
      intro h
      have he := congrArg FreeMagma.length (ht.trans h)
      rw [(AncestorAreaInstability.result.1 _ (by omega)).2.1] at he
      have hf := Nat.fib_mono (show 6 ≤ n+2+3+1 by omega)
      norm_num [defectB, FreeMagma.length] at he hf
      omega
    have hd : Disjoint ((positions (T (n+1+3))).image (false :: ·))
        ((positions (T (n+3))).image (true :: ·)) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hq
      cases hy
    rw [ht, positions, if_neg hne, Finset.empty_union, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (by intro a b h; exact (List.cons.inj h).2),
      Finset.card_image_of_injective _ (by intro a b h; exact (List.cons.inj h).2), hn, hn1,
      show n+2+1 = n+1+2 by omega]
    rw [Nat.fib_add_two (n := n+1), Nat.fib_add_two (n := n)]
    omega

private theorem native_source_family (n : ℕ) (hn : 3 ≤ n) :
    (positions (T n)).card = Nat.fib (n-2) ∧
    Function.Injective
      (fun A : {A : Finset Address // A ⊆ positions (T n)} => variant (T n) A.val) ∧
    ∀ (A : Finset Address), A ⊆ positions (T n) →
      wd (variant (T n) A) = wd (T n) ∧
      (variant (T n) A).length = Nat.fib (n+1) ∧
      depth (variant (T n) A) = if A = ∅ then n else 0 := by
  have hc := positions_card (n-3)
  rw [show n-3+3 = n by omega, show n-3+1 = n-2 by omega] at hc
  refine ⟨hc, variant_injective _, ?_⟩
  intro A hA
  have ht := AncestorAreaInstability.result.1 n hn
  refine ⟨(fill_length_word _ _).2, ((fill_length_word _ _).1).trans ht.2.1, ?_⟩
  by_cases h : A = ∅
  · subst A
    have hv : variant (T n) ∅ = T n := fill_unchanged _ _ (by simp)
    simpa only [hv, if_true] using ht.2.2.2.1
  · rw [if_neg h]
    exact variant_depth _ _ hA (Finset.nonempty_iff_ne_empty.mpr h)

/-- The native ancestor areas in a finite Euclidean ambient space. -/
def areaVector (m : ℕ) (t : Source) : EuclideanSpace ℝ (Fin (m-1)) :=
  WithLp.toLp 2 (fun i => ((coordinates t).getD i.val 0 : ℝ))

/-- The signed unit transfer at the two gaps beginning at a leaf offset. -/
def gapVector (m j : ℕ) : EuclideanSpace ℝ (Fin (m-1)) :=
  WithLp.toLp 2 (fun i => (if i.val = j then (1 : ℝ) else 0) -
    (if i.val = j+1 then 1 else 0))

private theorem list_splice_difference (L R : List ℕ) (j : ℕ) :
    ((L ++ [2,1] ++ R).getD j 0 : ℝ) - ((L ++ [1,2] ++ R).getD j 0 : ℝ) =
      (if j = L.length then (1 : ℝ) else 0) -
      (if j = L.length+1 then 1 else 0) := by
  induction L generalizing j with
  | nil => cases j with
    | zero => norm_num
    | succ j => cases j <;> norm_num
  | cons l L ih => cases j with
    | zero => simp
    | succ j => simpa using ih j

private theorem context_vector_difference (m : ℕ) (C : OutputContext) :
    areaVector m (C.plug defectD) = areaVector m (C.plug defectB) +
      gapVector m (offset (C.plug defectB) C.holeAddress) := by
  obtain ⟨L,R,hx,hy,hL⟩ := equal_length_coordinate_splice C defectB defectD defect_length
  obtain ⟨hB,hD⟩ := defect_coordinates
  rw [hB] at hx
  rw [hD] at hy
  ext i
  change ((coordinates (C.plug defectD)).getD i.val 0 : ℝ) =
    ((coordinates (C.plug defectB)).getD i.val 0 : ℝ) +
      ((if i.val = offset (C.plug defectB) C.holeAddress then (1 : ℝ) else 0) -
       (if i.val = offset (C.plug defectB) C.holeAddress+1 then 1 else 0))
  rw [hx,hy,← hL]
  linarith [list_splice_difference L R i.val]

private theorem fill_offset (t : Source) (a : Address → Bool) (p : Address)
    (hp : p ∈ positions t) : offset (fill t a) p = offset t p := by
  induction t generalizing a p with
  | of b => simp [positions] at hp
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · have he : p = [] := by simpa only [h, positions_B, Finset.mem_singleton] using hp
      subst p
      simp [offset]
    · rw [fill,if_neg h]
      cases p with
      | nil => rfl
      | cons b p =>
        cases b with
        | false => exact hl _ p ((mem_positions l p).mpr
            ((mem_positions (.mul l r) (false :: p)).mp hp))
        | true =>
          change (fill l _).length + offset (fill r _) p = l.length + offset r p
          rw [(fill_length_word l _).1]
          congr 1
          exact hr _ p ((mem_positions r p).mpr
            ((mem_positions (.mul l r) (true :: p)).mp hp))

private theorem fill_update (t : Source) (a : Address → Bool) (p : Address)
    (hp : p ∈ positions t) (b : Bool) :
    fill t (Function.update a p b) = replace (fill t a) p (if b then defectD else defectB) := by
  induction t generalizing a p with
  | of c => simp [positions] at hp
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · have he : p = [] := by simpa only [h, positions_B, Finset.mem_singleton] using hp
      subst p
      simp only [fill, if_pos h, Function.update_self, replace]
    · simp only [fill, if_neg h]
      cases p with
      | nil => exact False.elim (h (Option.some.inj ((mem_positions _ []).mp hp)))
      | cons c p =>
        cases c with
        | false =>
          have hleft : (fun q => Function.update a (false :: p) b (false :: q)) =
              Function.update (fun q => a (false :: q)) p b := by
            funext q
            by_cases hq : q = p <;> simp [Function.update, hq]
          have hright : (fun q => Function.update a (false :: p) b (true :: q)) =
              (fun q => a (true :: q)) := by funext q; simp [Function.update]
          rw [hleft, hright, replace, hl _ p ((mem_positions l p).mpr
            ((mem_positions (.mul l r) (false :: p)).mp hp))]
        | true =>
          have hright : (fun q => Function.update a (true :: p) b (true :: q)) =
              Function.update (fun q => a (true :: q)) p b := by
            funext q
            by_cases hq : q = p <;> simp [Function.update, hq]
          have hleft : (fun q => Function.update a (true :: p) b (false :: q)) =
              (fun q => a (false :: q)) := by funext q; simp [Function.update]
          rw [hleft, hright, replace, hr _ p ((mem_positions r p).mpr
            ((mem_positions (.mul l r) (true :: p)).mp hp))]

private theorem variant_insert_vector (t : Source) (A : Finset Address)
    (p : Address) (hp : p ∈ positions t) (hpa : p ∉ A) (m : ℕ) :
    areaVector m (variant t (insert p A)) =
      areaVector m (variant t A) + gapVector m (offset t p) := by
  have hab : (fun q => decide (q ∈ insert p A)) =
      Function.update (fun q => decide (q ∈ A)) p true := by
    funext q
    by_cases hq : q = p <;> simp [Function.update, hq]
  have hat := fill_at t (fun q => decide (q ∈ A)) p hp
  have hsub : subtree p (variant t A) = some defectB := by simpa [variant, hpa] using hat
  obtain ⟨_,_,_,_,_,_,_,_,_,context,_⟩ := ActualLeafHistoryRigidity.actual_address_geometry
  obtain ⟨C,hC,hplug,_⟩ := context p (variant t A) defectB hsub
  have hnew : variant t (insert p A) = C.plug defectD := by
    unfold variant
    rw [hab, fill_update t _ p hp true]
    change replace (variant t A) p defectD = C.plug defectD
    rw [← hplug, ← hC]
    simpa only [List.append_nil, replace] using
      ActualImageAlphaSeparation.path_replace C defectB defectD []
  rw [hnew, context_vector_difference, hplug, hC]
  congr 1
  exact congrArg (gapVector m) (fill_offset t _ p hp)

private theorem affine_formula (t : Source) (A : Finset Address)
    (hA : A ⊆ positions t) (m : ℕ) :
    areaVector m (variant t A) = areaVector m t + ∑ p ∈ A, gapVector m (offset t p) := by
  induction A using Finset.induction_on with
  | empty =>
    have hv : variant t ∅ = t := fill_unchanged _ _ (by simp)
    simp [hv]
  | @insert p A hp ih =>
    rw [variant_insert_vector t A p (hA (by simp)) hp m,
      ih (fun q hq => hA (Finset.mem_insert_of_mem hq)), Finset.sum_insert hp]
    abel

private theorem occurrence_bound (t : Source) (p : Address) (hp : p ∈ positions t) :
    offset t p + 3 ≤ t.length := by
  induction p generalizing t with
  | nil =>
    have ht : t = defectB := Option.some.inj ((mem_positions t []).mp hp)
    simp [ht, offset, defectB, FreeMagma.length]
  | cons b p ih =>
    cases t with
    | of c => simp [positions] at hp
    | mul l r =>
      cases b with
      | false =>
        have hx := ih l ((mem_positions l p).mpr
          ((mem_positions (.mul l r) (false :: p)).mp hp))
        simpa only [offset, FreeMagma.length] using hx.trans (Nat.le_add_right _ _)
      | true =>
        have hx := ih r ((mem_positions r p).mpr
          ((mem_positions (.mul l r) (true :: p)).mp hp))
        simp only [offset, FreeMagma.length]
        omega

private theorem separated_offsets (t : Source) (p q : Address)
    (hp : p ∈ positions t) (hq : q ∈ positions t) (hne : p ≠ q) :
    offset t p + 3 ≤ offset t q ∨ offset t q + 3 ≤ offset t p := by
  induction t generalizing p q with
  | of b => simp [positions] at hp
  | mul l r hl hr =>
    by_cases h : .mul l r = defectB
    · rw [h,positions_B] at hp hq
      exact False.elim (hne ((Finset.mem_singleton.mp hp).trans
        (Finset.mem_singleton.mp hq).symm))
    · cases p with
      | nil => exact False.elim (h (Option.some.inj ((mem_positions _ []).mp hp)))
      | cons b p =>
        cases q with
        | nil => exact False.elim (h (Option.some.inj ((mem_positions _ []).mp hq)))
        | cons c q =>
          have hp' := (mem_positions (.mul l r) (b :: p)).mp hp
          have hq' := (mem_positions (.mul l r) (c :: q)).mp hq
          cases b <;> cases c
          · exact hl p q ((mem_positions l p).mpr hp') ((mem_positions l q).mpr hq')
              (fun he => hne (congrArg (false :: ·) he))
          · have hx := occurrence_bound l p ((mem_positions l p).mpr hp')
            left
            simp only [offset]
            omega
          · have hx := occurrence_bound l q ((mem_positions l q).mpr hq')
            right
            simp only [offset]
            omega
          · have hx := hr p q ((mem_positions r p).mpr hp') ((mem_positions r q).mpr hq')
              (fun he => hne (congrArg (true :: ·) he))
            simp only [offset]
            omega

private theorem gap_single (m j : ℕ) (hj : j + 1 < m - 1) :
    gapVector m j = EuclideanSpace.single ⟨j,by omega⟩ 1 -
      EuclideanSpace.single ⟨j+1,hj⟩ 1 := by
  ext i
  simp [gapVector, PiLp.single_apply, Fin.ext_iff]

private theorem direction_inner (t : Source) (p q : Address)
    (hp : p ∈ positions t) (hq : q ∈ positions t) :
    inner ℝ (gapVector t.length (offset t p)) (gapVector t.length (offset t q)) =
      if p = q then 2 else 0 := by
  have hb := occurrence_bound t p hp
  rw [gap_single t.length (offset t p) (by omega), inner_sub_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  by_cases h : p = q
  · subst q
    norm_num [gapVector]
  · have hs := separated_offsets t p q hp hq h
    have h₁ : offset t p ≠ offset t q := by omega
    have h₂ : offset t p ≠ offset t q+1 := by omega
    have h₃ : offset t p+1 ≠ offset t q := by omega
    simp [gapVector,h,h₁,h₂,h₃]

private theorem inner_direction_sums (t : Source) (A B : Finset Address)
    (hA : A ⊆ positions t) (hB : B ⊆ positions t) :
    inner ℝ (∑ p ∈ A, gapVector t.length (offset t p))
      (∑ p ∈ B, gapVector t.length (offset t p)) = 2 * ((A ∩ B).card : ℝ) := by
  rw [sum_inner]
  have hp (p : Address) (hp : p ∈ A) :
      inner ℝ (gapVector t.length (offset t p))
        (∑ q ∈ B, gapVector t.length (offset t q)) = if p ∈ B then 2 else 0 := by
    rw [inner_sum]
    calc
      _ = ∑ q ∈ B, if p = q then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact direction_inner t p q (hA hp) (hB hq)
      _ = _ := by simp
  rw [Finset.sum_congr rfl hp, ← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter, mul_comm]

private theorem squared_distance (t : Source) (A B : Finset Address)
    (hA : A ⊆ positions t) (hB : B ⊆ positions t) :
    ‖areaVector t.length (variant t A) - areaVector t.length (variant t B)‖ ^ 2 =
      2 * ((A ∆ B).card : ℝ) := by
  rw [affine_formula t A hA, affine_formula t B hB,
    add_sub_add_left_eq_sub, norm_sub_sq_real,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_direction_sums t A A hA hA, inner_direction_sums t B B hB hB,
    inner_direction_sums t A B hA hB]
  simp only [Finset.inter_self]
  have h₁ := Finset.card_sdiff_add_card_inter A B
  have h₂ := Finset.card_sdiff_add_card_inter B A
  have hc : (A ∆ B).card = (A \ B).card + (B \ A).card :=
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  rw [hc]
  have he₁ : ((A \ B).card : ℝ) + ((A ∩ B).card : ℝ) = A.card := by exact_mod_cast h₁
  have he₂ : ((B \ A).card : ℝ) + ((A ∩ B).card : ℝ) = B.card := by
    rw [Finset.inter_comm] at h₂
    exact_mod_cast h₂
  push_cast
  nlinarith

private theorem total_area (t : Source) : (coordinates t).sum = t.length.choose 2 := by
  have hleaf : (ActualTreeReadoutAcquisition.leaves t).length = t.length := by
    rw [← List.toFinset_card_of_nodup (ActualJointResponseCostCore.cost_foundation.1 t).1]
    exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 t).1
  have hp := t.length_pos
  have hc : AncestorAreaInterval.CompleteSubtree t 1 t.length :=
    ⟨[],t,rfl,by simp [offset],by simp [offset],by
      simp [hleaf, show t.length-1+1 = t.length by omega]⟩
  have h := (AncestorAreaInterval.ancestor_area_interval t 1 t.length
    (by omega) t.length_pos (by omega)).2.mpr hc
  have harea : AncestorAreaInterval.area t 1 t.length = (coordinates t).sum := by
    simp only [AncestorAreaInterval.area, Nat.sub_self, List.drop_zero,
      ← coordinate_list_length t, List.take_length]
  rw [harea, show t.length-1+1 = t.length by omega] at h
  exact h

private theorem vector_total_area (t : Source) :
    ∑ i, areaVector t.length t i = (t.length.choose 2 : ℝ) := by
  have hs : (∑ i : Fin (coordinates t).length, (coordinates t).getD i.val 0) =
      (coordinates t).sum := by
    simpa only [List.getD_eq_getElem _ _ (Fin.isLt _)] using
      Fin.sum_univ_getElem (coordinates t)
  change (∑ i : Fin (t.length-1), ((coordinates t).getD i.val 0 : ℝ)) = _
  rw [← coordinate_list_length t]
  exact_mod_cast hs.trans (total_area t)

/-- All actual sources obtained from independent subsets of the literal positions. -/
def sourceFamily (t : Source) : Finset Source := (positions t).powerset.image (variant t)

/-- The full finite set of Euclidean area vectors. -/
def areaVertices (t : Source) : Finset (EuclideanSpace ℝ (Fin (t.length-1))) := by
  classical
  exact (positions t).powerset.image (fun A => areaVector t.length (variant t A))

/-- The actual area family divided by the total number of leaf pairs. -/
def normalizedAreaFamily (n : ℕ) : Set (EuclideanSpace ℝ (Fin ((T n).length-1))) :=
  ((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ • (areaVertices (T n) : Set _)

private theorem sourceFamily_card (t : Source) : (sourceFamily t).card = 2^(positions t).card := by
  unfold sourceFamily
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro A hA B hB h
  exact congrArg Subtype.val (variant_injective t
    (a₁ := ⟨A,Finset.mem_powerset.mp hA⟩) (a₂ := ⟨B,Finset.mem_powerset.mp hB⟩) h)

private theorem vertices_eq (t : Source) :
    (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))) =
      {areaVector t.length t} +
        ∑ p ∈ positions t, ({0, gapVector t.length (offset t p)} : Set _) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    have hAp := Finset.mem_powerset.mp hA
    apply Set.mem_add.mpr
    refine ⟨areaVector t.length t, by simp,
      ∑ p ∈ A, gapVector t.length (offset t p), ?_, (affine_formula t A hAp _).symm⟩
    apply (Set.mem_finsetSum _ _ _).mpr
    refine ⟨fun p => if p ∈ A then gapVector t.length (offset t p) else 0, ?_, ?_⟩
    · intro p hp
      dsimp only
      split_ifs <;> simp
    · rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hAp h,h⟩⟩
  · intro hx
    obtain ⟨b,hb,y,hy,hxy⟩ := Set.mem_add.mp hx
    obtain rfl := Set.mem_singleton_iff.mp hb
    obtain ⟨g,hg,rfl⟩ := (Set.mem_finsetSum _ _ _).mp hy
    let A := (positions t).filter (fun p => g p = gapVector t.length (offset t p))
    have hA : A ⊆ positions t := Finset.filter_subset _ _
    have he : ∑ p ∈ positions t, g p = ∑ p ∈ A, gapVector t.length (offset t p) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : g p = gapVector t.length (offset t p)
      · simp [h]
      · have hz : g p = 0 := by simpa only [Set.mem_insert_iff,
          Set.mem_singleton_iff, or_false, h] using hg hp
        simp [hz]
    apply Finset.mem_image.mpr
    refine ⟨A, Finset.mem_powerset.mpr hA, ?_⟩
    rw [affine_formula t A hA _]
    rwa [he] at hxy

private theorem cube_hull (t : Source) :
    convexHull ℝ (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))) =
      {areaVector t.length t} +
        parallelepiped (fun p : positions t => gapVector t.length (offset t p.val)) := by
  rw [vertices_eq, convexHull_add, convexHull_singleton, parallelepiped_eq_convexHull]
  rw [Finset.sum_coe_sort (positions t)
    (fun p : Address => ({0, gapVector t.length (offset t p)} : Set _))]

/-- The unit vectors in the independent native gap directions. -/
def unitDirection (t : Source) (p : positions t) : EuclideanSpace ℝ (Fin (t.length-1)) :=
  (Real.sqrt 2)⁻¹ • gapVector t.length (offset t p.val)

/-- The Euclidean direction space of the native area cube. -/
def directionSpan (t : Source) := Submodule.span ℝ (Set.range (unitDirection t))

private theorem unit_orthonormal (t : Source) : Orthonormal ℝ (unitDirection t) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  simp only [unitDirection, real_inner_smul_left, real_inner_smul_right]
  rw [direction_inner t p.val q.val p.property q.property]
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  · have hpq : p.val ≠ q.val := fun he => h (Subtype.ext he)
    simp [h,hpq]

private theorem direction_dimension (t : Source) :
    Module.finrank ℝ (directionSpan t) = (positions t).card := by
  unfold directionSpan
  rw [finrank_span_eq_card (unit_orthonormal t).linearIndependent, Fintype.card_coe]

private theorem direction_span_eq (t : Source) : directionSpan t =
    Submodule.span ℝ (Set.range (fun p : positions t =>
      gapVector t.length (offset t p.val))) := by
  unfold directionSpan unitDirection
  rw [Set.range_smul, Submodule.span_smul_eq_of_isUnit]
  exact isUnit_iff_ne_zero.mpr (by positivity)

private theorem affine_direction (t : Source) :
    (affineSpan ℝ (convexHull ℝ (areaVertices t :
      Set (EuclideanSpace ℝ (Fin (t.length-1)))))).direction = directionSpan t := by
  classical
  have h0 : areaVector t.length t ∈ areaVertices t := Finset.mem_image.mpr
    ⟨∅, by simp, by simpa only [Finset.sum_empty,add_zero] using
      affine_formula t ∅ (Finset.empty_subset _) t.length⟩
  rw [affineSpan_convexHull,direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ h0,direction_span_eq]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hy
    rw [affine_formula t A (Finset.mem_powerset.mp hA) _]
    simp only [vsub_eq_sub,add_sub_cancel_left]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.subset_span ⟨⟨p,Finset.mem_powerset.mp hA hp⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨p,rfl⟩
    apply Submodule.subset_span
    refine ⟨areaVector t.length (variant t {p.val}), Finset.mem_image.mpr
      ⟨{p.val}, Finset.mem_powerset.mpr (by simp),rfl⟩, ?_⟩
    rw [affine_formula t {p.val} (by simp) _]
    simp

/-- The convex cube translated to its own Euclidean direction space. -/
def intrinsicCube (t : Source) : Set (directionSpan t) :=
  {x | areaVector t.length t + (x : EuclideanSpace ℝ (Fin (t.length-1))) ∈
    convexHull ℝ (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1))))}

private theorem intrinsic_volume (t : Source) :
    MeasureTheory.volume (intrinsicCube t) =
      ENNReal.ofReal ((Real.sqrt 2) ^ (positions t).card) := by
  classical
  let B : Module.Basis (positions t) ℝ (directionSpan t) :=
    Module.Basis.span (unit_orthonormal t).linearIndependent
  have hco (p : positions t) : (B p : EuclideanSpace ℝ (Fin (t.length-1))) =
      unitDirection t p := Module.Basis.coe_span_apply _ p
  have hB : Orthonormal ℝ B := by
    rw [orthonormal_iff_ite]
    intro p q
    change inner ℝ (B p : EuclideanSpace ℝ (Fin (t.length-1))) (B q) = _
    rw [hco,hco]
    exact orthonormal_iff_ite.mp (unit_orthonormal t) p q
  let b := B.toOrthonormalBasis hB
  have hb (p : positions t) : (b p : EuclideanSpace ℝ (Fin (t.length-1))) =
      unitDirection t p := by
    have he : b p = B p := congrFun (Module.Basis.coe_toOrthonormalBasis B hB) p
    exact (congrArg Subtype.val he).trans (hco p)
  have hd : (fun p : positions t => gapVector t.length (offset t p.val)) =
      fun p => Real.sqrt 2 • (b p : EuclideanSpace ℝ (Fin (t.length-1))) := by
    funext p
    rw [hb,unitDirection,smul_smul,mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_smul]
  have him : (directionSpan t).subtype '' (Real.sqrt 2 • parallelepiped b) =
      parallelepiped (fun p : positions t => gapVector t.length (offset t p.val)) := by
    calc
      _ = ((Real.sqrt 2 • (directionSpan t).subtype :
          directionSpan t →ₗ[ℝ] EuclideanSpace ℝ (Fin (t.length-1))) :
          directionSpan t → EuclideanSpace ℝ (Fin (t.length-1))) ''
          parallelepiped b := by
        rw [← Set.image_smul, ← Set.image_comp]
        rfl
      _ = _ := by
        rw [image_parallelepiped, hd]
        rfl
  have hset : intrinsicCube t = Real.sqrt 2 • parallelepiped b := by
    ext x
    simp only [intrinsicCube, Set.mem_ofPred_eq]
    rw [cube_hull, ← him]
    constructor
    · intro hx
      obtain ⟨a,ha,y,hy,he⟩ := Set.mem_add.mp hx
      obtain rfl := Set.mem_singleton_iff.mp ha
      obtain ⟨z,hz,hzval⟩ := hy
      have hzx : z = x := Subtype.ext (hzval.trans (add_left_cancel he))
      simpa only [hzx] using hz
    · intro hx
      exact Set.add_mem_add (Set.mem_singleton _) ⟨x,hx,rfl⟩
  rw [hset, MeasureTheory.Measure.addHaar_smul_of_nonneg MeasureTheory.volume
    (Real.sqrt_nonneg 2), b.volume_parallelepiped, mul_one, direction_dimension]

private theorem diameter_exact (t : Source) :
    Metric.diam (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))) =
      Real.sqrt (2 * ((positions t).card : ℝ)) := by
  classical
  have mem (A : Finset Address) (hA : A ⊆ positions t) :
      areaVector t.length (variant t A) ∈ areaVertices t :=
    Finset.mem_image.mpr ⟨A,Finset.mem_powerset.mpr hA,rfl⟩
  have upper : ∀ x ∈ (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))),
      ∀ y ∈ (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))),
      dist x y ≤ Real.sqrt (2 * ((positions t).card : ℝ)) := by
    intro x hx y hy
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hy
    have hAp := Finset.mem_powerset.mp hA
    have hBp := Finset.mem_powerset.mp hB
    have hs := squared_distance t A B hAp hBp
    have hsub : A ∆ B ⊆ positions t := by
      intro p hp
      rcases Finset.mem_symmDiff.mp hp with ⟨ha,_⟩ | ⟨hb,_⟩
      · exact hAp ha
      · exact hBp hb
    have hc : ((A ∆ B).card : ℝ) ≤ (positions t).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    rw [dist_eq_norm]
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * ((positions t).card : ℝ)),
      Real.sqrt_nonneg (2 * ((positions t).card : ℝ)), norm_nonneg
        (areaVector t.length (variant t A) - areaVector t.length (variant t B))]
  apply le_antisymm (Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _) upper)
  have hl := Metric.dist_le_diam_of_mem (areaVertices t).finite_toSet.isBounded
    (mem ∅ (Finset.empty_subset _)) (mem (positions t) (Finset.Subset.refl _))
  have hs := squared_distance t ∅ (positions t) (Finset.empty_subset _) (Finset.Subset.refl _)
  rw [show (∅ : Finset Address) ∆ positions t = positions t from bot_symmDiff _] at hs
  rw [dist_eq_norm] at hl
  have he : ‖areaVector t.length (variant t ∅) -
      areaVector t.length (variant t (positions t))‖ =
      Real.sqrt (2 * ((positions t).card : ℝ)) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * ((positions t).card : ℝ)),
      Real.sqrt_nonneg (2 * ((positions t).card : ℝ)), norm_nonneg
        (areaVector t.length (variant t ∅) - areaVector t.length (variant t (positions t)))]
  rwa [he] at hl

/-- The actual independent family and its orthogonal cube with canonical intrinsic volume. -/
theorem native_area_cube (n : ℕ) (hn : 3 ≤ n) :
    (positions (T n)).card = Nat.fib (n-2) ∧
    Function.Injective
      (fun A : {A : Finset Address // A ⊆ positions (T n)} => variant (T n) A.val) ∧
    (∀ (A : Finset Address), A ⊆ positions (T n) →
      wd (variant (T n) A) = wd (T n) ∧
      (variant (T n) A).length = Nat.fib (n+1) ∧
      depth (variant (T n) A) = (if A = ∅ then n else 0) ∧
      areaVector (Nat.fib (n+1)) (variant (T n) A) =
        areaVector (Nat.fib (n+1)) (T n) +
          ∑ p ∈ A, gapVector (Nat.fib (n+1)) (offset (T n) p) ∧
      (∑ i, areaVector (Nat.fib (n+1)) (variant (T n) A) i) =
        ((Nat.fib (n+1)).choose 2 : ℝ) ∧
      (coordinates (variant (T n) A)).length = Nat.fib (n+1)-1 ∧
      ∀ B ⊆ positions (T n),
        ‖areaVector (Nat.fib (n+1)) (variant (T n) A) -
          areaVector (Nat.fib (n+1)) (variant (T n) B)‖ ^ 2 = 2 * ((A ∆ B).card : ℝ)) ∧
    (∀ p, p ∈ positions (T n) ↔ subtree p (T n) = some defectB) ∧
    (∀ p ∈ positions (T n), offset (T n) p < Nat.fib (n+1)-1 ∧
      offset (T n) p+1 < Nat.fib (n+1)-1) ∧
    (∀ p ∈ positions (T n), ∀ q ∈ positions (T n), p ≠ q →
      offset (T n) p+3 ≤ offset (T n) q ∨ offset (T n) q+3 ≤ offset (T n) p) ∧
    convexHull ℝ (areaVertices (T n) : Set (EuclideanSpace ℝ (Fin ((T n).length-1)))) =
      {areaVector (T n).length (T n)} +
        parallelepiped (fun p : positions (T n) =>
          gapVector (T n).length (offset (T n) p.val)) ∧
    (affineSpan ℝ (convexHull ℝ (areaVertices (T n) :
      Set (EuclideanSpace ℝ (Fin ((T n).length-1)))))).direction = directionSpan (T n) ∧
    Orthonormal ℝ (unitDirection (T n)) ∧
    directionSpan (T n) = Submodule.span ℝ (Set.range (fun p : positions (T n) =>
      gapVector (T n).length (offset (T n) p.val))) ∧
    Module.finrank ℝ (directionSpan (T n)) = Nat.fib (n-2) ∧
    (∀ p : positions (T n), ‖gapVector (T n).length (offset (T n) p.val)‖ = Real.sqrt 2) ∧
    MeasureTheory.volume (intrinsicCube (T n)) =
      ENNReal.ofReal ((2:ℝ) ^ ((Nat.fib (n-2):ℝ)/2)) := by
  obtain ⟨hc,hi,hf⟩ := native_source_family n hn
  have ht := (AncestorAreaInstability.result.1 n hn).2.1
  refine ⟨hc,hi,?_,mem_positions (T n),?_,
    (fun p hp q hq hne => separated_offsets (T n) p q hp hq hne),cube_hull (T n),
    affine_direction (T n),
    unit_orthonormal (T n),direction_span_eq (T n),?_,?_,?_⟩
  · intro A hA
    obtain ⟨hw,hl,hd⟩ := hf A hA
    refine ⟨hw,hl,hd,affine_formula _ _ hA _,?_,?_,?_⟩
    · rw [← hl]
      exact vector_total_area _
    · rw [coordinate_list_length, hl]
    · intro B hB
      rw [← ht]
      exact squared_distance _ _ _ hA hB
  · intro p hp
    have hb := occurrence_bound (T n) p hp
    rw [ht] at hb
    omega
  · rw [direction_dimension,hc]
  · intro p
    have he := direction_inner (T n) p.val p.val p.property p.property
    rw [real_inner_self_eq_norm_sq, if_pos rfl] at he
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
      norm_nonneg (gapVector (T n).length (offset (T n) p.val))]
  · rw [intrinsic_volume, ← Real.rpow_natCast,
      ← Real.rpow_div_two_eq_sqrt _ (by norm_num : (0:ℝ) ≤ 2), hc]

private theorem endpoint_distance (t : Source) :
    dist (areaVector t.length (variant t ∅))
      (areaVector t.length (variant t (positions t))) =
        Metric.diam (areaVertices t : Set (EuclideanSpace ℝ (Fin (t.length-1)))) := by
  have he := squared_distance t ∅ (positions t) (Finset.empty_subset _) (Finset.Subset.refl _)
  rw [show (∅ : Finset Address) ∆ positions t = positions t from bot_symmDiff _] at he
  rw [dist_eq_norm,diameter_exact]
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2*((positions t).card : ℝ)),
    Real.sqrt_nonneg (2*((positions t).card : ℝ)), norm_nonneg
      (areaVector t.length (variant t ∅) - areaVector t.length (variant t (positions t)))]

/-- The exact diameter and the number and depth endpoints of the normalized native family. -/
private theorem normalized_family (n : ℕ) (hn : 3 ≤ n) :
    Metric.diam (normalizedAreaFamily n) =
      Real.sqrt (2 * (Nat.fib (n-2) : ℝ)) / ((Nat.fib (n+1)).choose 2 : ℝ) ∧
    (sourceFamily (T n)).card = 2 ^ Nat.fib (n-2) ∧
    depth (variant (T n) ∅) = n ∧ depth (variant (T n) (positions (T n))) = 0 ∧
    ‖((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ • areaVector (T n).length (variant (T n) ∅) -
      ((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ •
        areaVector (T n).length (variant (T n) (positions (T n)))‖ =
      Metric.diam (normalizedAreaFamily n) := by
  have hc := (native_area_cube n hn).1
  have hs := (native_source_family n hn).2.2
  have hp : (positions (T n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hc]
    exact Nat.fib_pos.mpr (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [normalizedAreaFamily, diam_smul₀, diameter_exact, hc]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((Nat.fib (n+1)).choose 2 : ℝ)⁻¹)]
    ring
  · rw [sourceFamily_card,hc]
  · simpa only [if_true] using (hs ∅ (Finset.empty_subset _)).2.2
  · simpa only [if_neg (Finset.nonempty_iff_ne_empty.mp hp)] using
      (hs (positions (T n)) (Finset.Subset.refl _)).2.2
  · rw [← smul_sub,norm_smul, ← dist_eq_norm,endpoint_distance,
      normalizedAreaFamily,diam_smul₀]

private theorem diameter_decay (n : ℕ) (hn : 3 ≤ n) :
    Metric.diam (normalizedAreaFamily n) ≤
      (4 * Real.sqrt 2) * (Nat.fib (n+1) : ℝ) ^ (-(3/2 : ℝ)) := by
  let m : ℝ := Nat.fib (n+1)
  let k : ℝ := Nat.fib (n-2)
  have hm : 2 ≤ m := by
    have h := Nat.fib_mono (show 3 ≤ n+1 by omega)
    change (2:ℝ) ≤ (Nat.fib (n+1) : ℝ)
    exact_mod_cast (show 2 ≤ Nat.fib (n+1) by
      simpa only [show Nat.fib 3 = 2 from rfl] using h)
  have hk : k ≤ m := by
    change (Nat.fib (n-2) : ℝ) ≤ Nat.fib (n+1)
    exact_mod_cast Nat.fib_mono (show n-2 ≤ n+1 by omega)
  have hmp : 0 < m := by linarith
  have hsp : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmp
  have hc : ((Nat.fib (n+1)).choose 2 : ℝ) = m * (m-1) / 2 :=
    Nat.cast_choose_two ℝ _
  have hcp : 0 < ((Nat.fib (n+1)).choose 2 : ℝ) := by
    rw [hc]
    exact div_pos (mul_pos hmp (by linarith)) (by norm_num)
  have hsq : m*m ≤ 4*((Nat.fib (n+1)).choose 2 : ℝ) := by rw [hc]; nlinarith
  have hs : Real.sqrt (2*k) ≤ Real.sqrt 2 * Real.sqrt m := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hr : m ^ (-(3/2 : ℝ)) = (m * Real.sqrt m)⁻¹ := by
    rw [Real.rpow_neg hmp.le, show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add hmp, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [(normalized_family n hn).1, hr]
  apply (div_le_iff₀ hcp).mpr
  have hbound : Real.sqrt 2 * Real.sqrt m ≤
      (4 * Real.sqrt 2) * (m * Real.sqrt m)⁻¹ *
        ((Nat.fib (n+1)).choose 2 : ℝ) := by
    have he : (Real.sqrt 2 * Real.sqrt m) * (m * Real.sqrt m) =
        Real.sqrt 2 * (m*m) := by
      calc
        _ = Real.sqrt 2 * m * (Real.sqrt m ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hmp.le]; ring
    calc
      _ ≤ (4 * Real.sqrt 2 * ((Nat.fib (n+1)).choose 2 : ℝ)) / (m * Real.sqrt m) := by
        apply (le_div_iff₀ (mul_pos hmp hsp)).mpr
        rw [he]
        nlinarith [Real.sqrt_nonneg 2]
      _ = _ := by ring
  exact hs.trans hbound

/-- Exact normalized diameter, exponential source count, depth endpoints and decay. -/
theorem normalized_cube_diameter :
    (∀ n : ℕ, 3 ≤ n →
      Metric.diam (normalizedAreaFamily n) =
        Real.sqrt (2 * (Nat.fib (n-2) : ℝ)) / ((Nat.fib (n+1)).choose 2 : ℝ) ∧
      (sourceFamily (T n)).card = 2 ^ Nat.fib (n-2) ∧
      depth (variant (T n) ∅) = n ∧ depth (variant (T n) (positions (T n))) = 0 ∧
      ‖((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ • areaVector (T n).length (variant (T n) ∅) -
        ((Nat.fib (n+1)).choose 2 : ℝ)⁻¹ •
          areaVector (T n).length (variant (T n) (positions (T n)))‖ =
        Metric.diam (normalizedAreaFamily n)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => Metric.diam (normalizedAreaFamily n))
      (fun n => (Nat.fib (n+1) : ℝ) ^ (-(3/2 : ℝ))) ∧
    Filter.Tendsto (fun n => Metric.diam (normalizedAreaFamily n))
      Filter.atTop (nhds 0) := by
  have hb : Asymptotics.IsBigO Filter.atTop (fun n => Metric.diam (normalizedAreaFamily n))
      (fun n => (Nat.fib (n+1) : ℝ) ^ (-(3/2 : ℝ))) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨4 * Real.sqrt 2, (Filter.eventually_ge_atTop 3).mono ?_⟩
    intro n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg Metric.diam_nonneg,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using diameter_decay n hn
  have hm : Filter.Tendsto (fun n : ℕ => (Nat.fib (n+1) : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop ?_
      (tendsto_natCast_atTop_atTop : Filter.Tendsto
        (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
    filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    exact_mod_cast (Nat.le_fib_self hn).trans (Nat.fib_mono (by omega : n ≤ n+1))
  exact ⟨normalized_family, hb, hb.trans_tendsto
    ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/2)).comp hm)⟩

end
end D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.native_area_cube

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.normalized_cube_diameter
