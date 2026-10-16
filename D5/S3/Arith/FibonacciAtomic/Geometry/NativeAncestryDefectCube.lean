/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Equal-length context substitutions preserve a common coordinate exterior while the three-leaf defect swaps its two internal areas. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInterval
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
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
open scoped BigOperators

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

private theorem plug_length (C : OutputContext) (x : Source) :
    (C.plug x).length = C.outsideLeaves + x.length := by
  induction C with
  | hole => simp [OutputContext.plug, OutputContext.outsideLeaves]
  | left C r ih =>
      simp only [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length]
      omega
  | right l C ih =>
      simp only [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length]
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
        rw [plug_length, plug_length, hxy]
      let Q : List ℕ := R ++ [(C.plug x).length * r.length] ++ coordinates r
      refine ⟨L, Q, ?_, ?_, ?_⟩
      · simp only [OutputContext.plug, coordinates, Q, hx, List.append_assoc]
      · simp only [OutputContext.plug, coordinates, Q, hy, hlen, List.append_assoc]
      · simpa only [OutputContext.holeAddress, OutputContext.plug, offset] using hL
  | right l C ih =>
      obtain ⟨L, R, hx, hy, hL⟩ := ih x y hxy
      have hlen : (C.plug x).length = (C.plug y).length := by
        rw [plug_length, plug_length, hxy]
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

private theorem fill_at (t : Source) (a : Address → Bool) (p : Address)
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
    by_cases hA : p ∈ A.val <;> by_cases hB : p ∈ B.val <;>
      simp [hA, hB, defectB, defectD] at ha ⊢ <;> cases ha
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
      rcases (SourceCoordinates.IntrinsicSubstitutionCoordinates.pair_image l r).mp h with h | ⟨hl,hr⟩
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
  have h := (SourceCoordinates.IntrinsicSubstitutionCoordinates.intrinsic_coordinates (variant t A)).1 1
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

/-- The actual independent source family and its affine ancestor-area formula. -/
theorem native_area_cube (n : ℕ) (hn : 3 ≤ n) :
    (positions (T n)).card = Nat.fib (n-2) ∧
    Function.Injective
      (fun A : {A : Finset Address // A ⊆ positions (T n)} => variant (T n) A.val) ∧
    ∀ (A : Finset Address), A ⊆ positions (T n) →
      wd (variant (T n) A) = wd (T n) ∧
      (variant (T n) A).length = Nat.fib (n+1) ∧
      depth (variant (T n) A) = (if A = ∅ then n else 0) ∧
      areaVector (Nat.fib (n+1)) (variant (T n) A) =
        areaVector (Nat.fib (n+1)) (T n) +
          ∑ p ∈ A, gapVector (Nat.fib (n+1)) (offset (T n) p) := by
  obtain ⟨hc,hi,hf⟩ := native_source_family n hn
  refine ⟨hc,hi,?_⟩
  intro A hA
  obtain ⟨hw,hl,hd⟩ := hf A hA
  exact ⟨hw,hl,hd,affine_formula _ _ hA _⟩

end
end D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.native_area_cube
