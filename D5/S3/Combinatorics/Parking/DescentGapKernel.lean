/- GID: D5/S3/Combinatorics/Parking/DescentGapKernel
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Parking/DescentGapKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered gap factors for maximum-letter insertion. -/

import D5.S1.Words.UnaryGapWords
import D5.S3.Combinatorics.ShankarWords.ActualWordExtremal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Ring

/-! The boundary gaps, interior comparisons and old peaks determine the insertion weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Parking.DescentRefinement

open D5.S1.Words.UnaryGapWords
open PowerSeries
open Finset (antidiagonal)
open scoped BigOperators

inductive Edge where
  | up | tie | down
  deriving DecidableEq, Repr

private def edge (a b : Nat) : Edge :=
  if a < b then .up else if b < a then .down else .tie

private def edgesFrom (a : Nat) : List Nat → List Edge
  | [] => []
  | b :: bs => edge a b :: edgesFrom b bs

def edges : List Nat → List Edge
  | [] => []
  | a :: as => edgesFrom a as

def peaks : List Nat → Nat
  | a :: b :: c :: cs => (if a < b ∧ c < b then 1 else 0) + peaks (b :: c :: cs)
  | _ => 0

def ties (w : List Nat) : Nat :=
  ((w.zip w.tail).filter (fun p => p.1 == p.2)).length

open D5.S3.Combinatorics.ShankarWords.ActualWordExtremal (descents)

private def peakEdges (wasUp : Bool) : List Edge → Nat
  | [] => 0
  | e :: es => (if wasUp && decide (e = .down) then 1 else 0) +
      peakEdges (decide (e = .up)) es

@[simp] private theorem edge_up (a b : Nat) : edge a b = .up ↔ a < b := by
  unfold edge
  split_ifs <;> simp_all

@[simp] private theorem edge_down (a b : Nat) : edge a b = .down ↔ b < a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [edge, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
  · simp [edge]
  · simp [edge, h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

private theorem peakEdges_eq (w : List Nat) : peakEdges false (edges w) = peaks w := by
  induction w using peaks.induct with
  | case1 a b c cs ih =>
    simp only [edges, edgesFrom, peakEdges] at ih ⊢
    rw [peaks, ← ih]
    simp
  | case2 w hw =>
    cases w with
    | nil => rfl
    | cons a w =>
      cases w with
      | nil => rfl
      | cons b w =>
        cases w with
        | nil => rfl
        | cons c cs => exact (hw a b c cs rfl).elim

private theorem count_edgesFrom (a : Nat) (w : List Nat) :
    (edgesFrom a w).count .tie = (((a :: w).zip w).filter (fun p => p.1 == p.2)).length ∧
    (edgesFrom a w).count .down = (((a :: w).zip w).filter (fun p => p.2 < p.1)).length := by
  induction w generalizing a with
  | nil => simp [edgesFrom]
  | cons b bs ih =>
    obtain ⟨ht, hd⟩ := ih b
    simp only [edgesFrom, List.zip_cons_cons, List.filter_cons, List.count_cons]
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp [edge, hab, hab.ne, Nat.not_lt_of_ge (Nat.le_of_lt hab), ht, hd]
    · simp [edge, ht, hd, Nat.add_comm]
    · simp [edge, hba, hba.ne.symm, Nat.not_lt_of_ge (Nat.le_of_lt hba), ht, hd, Nat.add_comm]

private theorem count_edges (w : List Nat) :
    (edges w).count .tie = ties w ∧ (edges w).count .down = descents w := by
  cases w with
  | nil => exact ⟨rfl, rfl⟩
  | cons a w => exact count_edgesFrom a w

variable {R : Type*} [CommSemiring R]

def wordWeight (t u v : R) (w : List Nat) : R :=
  t ^ peaks w * u ^ ties w * v ^ descents w

private def edgeWeight (u v : R) : Edge → R
  | .up => 1
  | .tie => u
  | .down => v

private def peakFactor (t : R) (wasUp : Bool) (e : Edge) : R :=
  if wasUp && decide (e = .down) then t else 1

private def weightFrom (t u v : R) (wasUp : Bool) : List Edge → R
  | [] => 1
  | e :: es => (peakFactor t wasUp e * edgeWeight u v e) *
      weightFrom t u v (decide (e = .up)) es

private theorem weightFrom_eq (t u v : R) (wasUp : Bool) (es : List Edge) :
    weightFrom t u v wasUp es =
      t ^ peakEdges wasUp es * u ^ es.count .tie * v ^ es.count .down := by
  induction es generalizing wasUp with
  | nil => simp [weightFrom, peakEdges]
  | cons e es ih =>
    cases wasUp <;> cases e <;>
      simp [weightFrom, peakEdges, peakFactor, edgeWeight, ih, pow_succ, pow_add,
        mul_assoc, mul_comm, mul_left_comm]

private theorem wordWeight_eq (t u v : R) (w : List Nat) :
    wordWeight t u v w = weightFrom t u v false (edges w) := by
  rw [weightFrom_eq, peakEdges_eq, (count_edges w).1, (count_edges w).2, wordWeight]

private def leftExpansion : Nat → List Edge
  | 0 => []
  | j + 1 => List.replicate j .tie ++ [.down]

private def rightExpansion : Nat → List Edge
  | 0 => []
  | j + 1 => .up :: List.replicate j .tie

private def expansion (e : Edge) : Nat → List Edge
  | 0 => [e]
  | j + 1 => .up :: List.replicate j .tie ++ [.down]

private def expandedTail : List Edge → List Nat → List Edge
  | [], hs => rightExpansion (hs.headD 0)
  | e :: es, hs => expansion e (hs.headD 0) ++ expandedTail es hs.tail

private theorem edgesFrom_replicate (m k : Nat) (w : List Nat) :
    edgesFrom m (List.replicate k m ++ w) =
      List.replicate k .tie ++ edgesFrom m w := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, edgesFrom, edge, ih]

private theorem edgesFrom_gap (m a : Nat) (cs hs : List Nat)
    (ha : a < m) (hcs : ∀ x ∈ cs, x < m) (hh : hs.length = cs.length + 1) :
    edgesFrom a (gap m cs hs) = expandedTail (edgesFrom a cs) hs := by
  induction cs generalizing a hs with
  | nil =>
    cases hs with
    | nil => simp at hh
    | cons j js =>
      cases j with
      | zero => rfl
      | succ j =>
        change edge a m :: edgesFrom m (List.replicate j m) =
          .up :: List.replicate j .tie
        have he := edgesFrom_replicate m j []
        simp only [List.append_nil, edgesFrom] at he
        rw [he, (edge_up a m).mpr ha]
  | cons b cs ih =>
    cases hs with
    | nil => simp at hh
    | cons j js =>
      have hb : b < m := hcs b (by simp)
      have he : edge m b = .down := by simp [edge, Nat.not_lt_of_ge (Nat.le_of_lt hb), hb]
      have ht := ih b js hb (fun x hx => hcs x (by simp [hx])) (by simpa using hh)
      cases j with
      | zero => simpa [gap, edgesFrom, expandedTail, expansion] using congrArg (edge a b :: ·) ht
      | succ j =>
        simp only [gap, List.headD_cons, List.tail_cons, List.replicate_succ, List.cons_append,
          edgesFrom, expandedTail, expansion]
        have ha' : edge a m = .up := by simp [edge, ha]
        rw [ha', edgesFrom_replicate, edgesFrom, he, ht]
        simp

private theorem edges_gap (m a : Nat) (cs : List Nat) (j : Nat) (hs : List Nat)
    (ha : a < m) (hcs : ∀ x ∈ cs, x < m) (hh : hs.length = cs.length + 1) :
    edges (gap m (a :: cs) (j :: hs)) =
      leftExpansion j ++ expandedTail (edgesFrom a cs) hs := by
  have ht := edgesFrom_gap m a cs hs ha hcs hh
  cases j with
  | zero => exact ht
  | succ j =>
    simp only [gap, List.headD_cons, List.tail_cons, List.replicate_succ, List.cons_append, edges,
      leftExpansion]
    rw [edgesFrom_replicate, edgesFrom, ht]
    have he : edge m a = .down := by simp [edge, Nat.not_lt_of_ge (Nat.le_of_lt ha), ha]
    rw [he]
    simp

private def boundaryWeight (u : R) : Nat → R
  | 0 => 1
  | j + 1 => u ^ j

private def leftWeight (u v : R) : Nat → R
  | 0 => 1
  | j + 1 => u ^ j * v

private def rightWeight (u : R) : Nat → R := boundaryWeight u

private def occupied (t u : R) : Nat → R
  | 0 => 0
  | 1 => t
  | j + 2 => u ^ (j + 1)

private def singleWeight (t u v : R) (e : Edge) : Nat → R
  | 0 => edgeWeight u v e
  | j + 1 => v * occupied t u (j + 1)

private def pairWeight (t u v : R) (i j : Nat) : R :=
  if i = 0 ∧ j = 0 then t * v
  else singleWeight t u v .up i * singleWeight t u v .down j

private theorem weight_repeat_ties (t u v : R) (b : Bool) (j : Nat) (es : List Edge) :
    weightFrom t u v b (List.replicate j .tie ++ es) =
      u ^ j * weightFrom t u v (if j = 0 then b else false) es := by
  induction j generalizing b with
  | zero => simp
  | succ j ih =>
    simp [List.replicate_succ, weightFrom, peakFactor, edgeWeight, ih, pow_succ',
      mul_assoc]

private theorem left_gap_weight (t u v : R) (j : Nat) (es : List Edge) :
    weightFrom t u v false (leftExpansion j ++ es) =
      leftWeight u v j * weightFrom t u v false es := by
  cases j with
  | zero => simp [leftExpansion, leftWeight]
  | succ j =>
    simp [leftExpansion, leftWeight, weight_repeat_ties, weightFrom, peakFactor,
      edgeWeight, mul_assoc]

private theorem right_gap_weight (t u v : R) (b : Bool) (j : Nat) :
    weightFrom t u v b (rightExpansion j) = rightWeight u j := by
  cases j with
  | zero => rfl
  | succ j =>
    have h := weight_repeat_ties t u v true j []
    simp only [List.append_nil] at h
    have he : weightFrom t u v (if j = 0 then true else false) [] = 1 := rfl
    rw [he, mul_one] at h
    simpa [rightExpansion, rightWeight, boundaryWeight, weightFrom, peakFactor, edgeWeight] using h

private def endsUp (e : Edge) (j : Nat) : Bool :=
  decide (e = .up) && decide (j = 0)

private def entryFactor (t : R) (b : Bool) (e : Edge) (j : Nat) : R :=
  if j = 0 then peakFactor t b e else 1

private theorem interior_gap_weight (t u v : R) (b : Bool) (e : Edge) (j : Nat) (es : List Edge) :
    weightFrom t u v b (expansion e j ++ es) =
      entryFactor t b e j * singleWeight t u v e j *
        weightFrom t u v (endsUp e j) es := by
  cases j with
  | zero => simp [weightFrom, expansion, entryFactor, singleWeight, endsUp]
  | succ j =>
    cases j with
    | zero =>
      simp [weightFrom, expansion, entryFactor, singleWeight, occupied, endsUp, peakFactor,
        edgeWeight, mul_comm]
    | succ j =>
      simp [expansion, entryFactor, singleWeight, occupied, endsUp, weightFrom, peakFactor,
        edgeWeight, List.replicate_succ, weight_repeat_ties, pow_succ', mul_assoc, mul_comm,
        mul_left_comm]

private inductive Block where
  | single (e : Edge)
  | peak
  deriving DecidableEq, Repr

/-- The scan consumes both edges of each old strict peak before scanning the suffix. -/
private def blocks : List Edge → List Block
  | .up :: .down :: es => .peak :: blocks es
  | e :: es => .single e :: blocks es
  | [] => []

private def blockWeights (t u v : R) : List Block → List Nat → R
  | [], hs => rightWeight u (hs.headD 0)
  | .single e :: bs, hs =>
      singleWeight t u v e (hs.headD 0) * blockWeights t u v bs hs.tail
  | .peak :: bs, hs =>
      pairWeight t u v (hs.headD 0) (hs.tail.headD 0) *
        blockWeights t u v bs hs.tail.tail

private def initialFactor (t : R) (b : Bool) (es : List Edge) (hs : List Nat) : R :=
  match es with
  | [] => 1
  | e :: _ => entryFactor t b e (hs.headD 0)

private theorem blocks_cons_of_not_peak (e : Edge) (es : List Edge)
    (h : ¬ (e = .up ∧ es.head? = some .down)) :
    blocks (e :: es) = .single e :: blocks es := by
  cases e <;> cases es with
  | nil => rfl
  | cons f fs => cases f <;> simp_all [blocks]

@[simp] private theorem entryFactor_up (t : R) (b : Bool) (j : Nat) :
    entryFactor t b .up j = 1 := by simp [entryFactor, peakFactor]

@[simp] private theorem initialFactor_false (t : R) (es : List Edge) (hs : List Nat) :
    initialFactor t false es hs = 1 := by cases es <;> simp [initialFactor, entryFactor, peakFactor]

private theorem initial_ne_peak (t : R) (e : Edge) (es : List Edge) (i : Nat) (hs : List Nat)
    (h : ¬ (e = .up ∧ es.head? = some .down)) :
    initialFactor t (endsUp e i) es hs = 1 := by
  cases es with
  | nil => rfl
  | cons f fs =>
    change ¬ (e = .up ∧ some f = some .down) at h
    cases e <;> cases f <;> simp_all [initialFactor, endsUp, entryFactor, peakFactor]

private theorem pairWeight_eq (t u v : R) (i j : Nat) :
    singleWeight t u v .up i * entryFactor t (endsUp .up i) .down j *
        singleWeight t u v .down j = pairWeight t u v i j := by
  cases i <;> cases j <;>
    simp [pairWeight, singleWeight, edgeWeight, entryFactor, peakFactor, endsUp]

private theorem expanded_weight (t u v : R) (b : Bool) (es : List Edge) (hs : List Nat) :
    weightFrom t u v b (expandedTail es hs) =
      initialFactor t b es hs * blockWeights t u v (blocks es) hs := by
  induction es using blocks.induct generalizing b hs with
  | case1 es ih =>
    simp only [expandedTail, interior_gap_weight, blocks, blockWeights, initialFactor]
    rw [ih]
    have he : endsUp .down (hs.tail.headD 0) = false := rfl
    simp only [he, initialFactor_false, entryFactor_up, one_mul]
    rw [← mul_assoc, ← mul_assoc, pairWeight_eq]
  | case2 e es hne ih =>
    have h : ¬ (e = .up ∧ es.head? = some .down) := by
      rintro ⟨rfl, h⟩
      cases es with
      | nil => contradiction
      | cons f fs =>
        simp only [List.head?_cons, Option.some.injEq] at h
        subst f
        exact hne fs rfl rfl
    rw [blocks_cons_of_not_peak e es h]
    simp only [expandedTail, interior_gap_weight, blockWeights, ih]
    rw [initial_ne_peak t e es _ _ h, one_mul, mul_assoc]
    rfl
  | case3 => simp [expandedTail, blocks, blockWeights, initialFactor, right_gap_weight]

/-- The weight of the actual reconstructed word for every labelled gap profile. -/
private theorem labelled_kernel (t u v : R) (m a : Nat) (cs : List Nat) (j : Nat) (hs : List Nat)
    (ha : a < m) (hcs : ∀ x ∈ cs, x < m) (hh : hs.length = cs.length + 1) :
    wordWeight t u v (gap m (a :: cs) (j :: hs)) =
      leftWeight u v j * blockWeights t u v (blocks (edges (a :: cs))) hs := by
  rw [wordWeight_eq, edges_gap m a cs j hs ha hcs hh, left_gap_weight, expanded_weight]
  simp only [edges, initialFactor_false, one_mul]

private theorem edgesFrom_replicate_self (a n : Nat) :
    edgesFrom a (List.replicate n a) = List.replicate n .tie := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, edgesFrom, edge, ih]

private theorem peaks_replicate_ties (n : Nat) :
    peakEdges false (List.replicate n .tie) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, peakEdges, ih]

/-- A constant word of length n has exactly n − 1 ties. -/
theorem wordWeight_replicate (t u v : R) (n : Nat) :
    wordWeight t u v (List.replicate n 1) = u ^ (n - 1) := by
  rw [wordWeight_eq]
  cases n with
  | zero => simp [edges, weightFrom]
  | succ n =>
    simp [List.replicate_succ, edges, edgesFrom_replicate_self, weightFrom_eq,
      List.count_replicate, peaks_replicate_ties]

noncomputable section

def consEmbedding (i : Nat) : List Nat ↪ List Nat :=
  ⟨(i :: ·), fun _ _ h => (List.cons.inj h).2⟩

/-- Ordered gap counts with exact total, indexed by the number of gaps. -/
def profiles : Nat → Nat → Finset (List Nat)
  | 0, r => if r = 0 then {[]} else ∅
  | k + 1, r => (antidiagonal r).biUnion fun p =>
      (profiles k p.2).map (consEmbedding p.1)

theorem mem_profiles (k r : Nat) (hs : List Nat) :
    hs ∈ profiles k r ↔ hs.length = k ∧ hs.sum = r := by
  induction k generalizing r hs with
  | zero =>
    cases hs with
    | nil => by_cases h : r = 0 <;> simp [profiles, h, eq_comm]
    | cons j js => by_cases h : r = 0 <;> simp [profiles, h]
  | succ k ih =>
    cases hs with
    | nil => simp [profiles, Finset.mem_biUnion, consEmbedding]
    | cons j js =>
      simp only [profiles, Finset.mem_biUnion, Finset.mem_map, Finset.mem_antidiagonal,
        List.length_cons, Nat.add_right_cancel_iff, List.sum_cons]
      constructor
      · rintro ⟨⟨i, s⟩, h, ls, hm, he⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hl, hz⟩ := (ih s ls).mp hm
        exact ⟨hl, by simpa [hz] using h⟩
      · rintro ⟨hl, h⟩
        exact ⟨(j, js.sum), h, js, (ih js.sum js).mpr ⟨hl, rfl⟩, rfl⟩

private theorem sum_profiles_succ (k r : Nat) (f : List Nat → R) :
    ∑ h ∈ profiles (k + 1) r, f h =
      ∑ p ∈ antidiagonal r, ∑ h ∈ profiles k p.2, f (p.1 :: h) := by
  rw [profiles, Finset.sum_biUnion]
  · simp only [Finset.sum_map]
    rfl
  · intro p _ q _ hpq
    refine Finset.disjoint_left.mpr ?_
    intro h hp hq
    obtain ⟨xs, hx, hpx⟩ := Finset.mem_map.mp hp
    obtain ⟨ys, hy, hqy⟩ := Finset.mem_map.mp hq
    change p.1 :: xs = h at hpx
    change q.1 :: ys = h at hqy
    obtain ⟨he, rfl⟩ := List.cons.inj (hpx.trans hqy.symm)
    exact hpq (Prod.ext he (((mem_profiles _ _ _).mp hx).2.symm.trans
      ((mem_profiles _ _ _).mp hy).2))

private theorem profiles_one (r : Nat) : profiles 1 r = {[r]} := by
  ext hs
  rw [mem_profiles, Finset.mem_singleton]
  cases hs with
  | nil => simp
  | cons j js => cases js <;> simp

/-- Cauchy multiplication with one new labelled gap. -/
private theorem coeff_cons_gap (k r : Nat) (f : Nat → R) (g : R⟦X⟧) (w : List Nat → R)
    (hg : ∀ s, coeff s g = ∑ hs ∈ profiles k s, w hs) :
    coeff r (mk f * g) = ∑ hs ∈ profiles (k + 1) r, f (hs.headD 0) * w hs.tail := by
  rw [coeff_mul, sum_profiles_succ]
  simp only [coeff_mk, hg, Finset.mul_sum, List.headD_cons, List.tail_cons]

def boundarySeries (u : R) : R⟦X⟧ :=
  mk (fun j => u ^ j) * X

def occupiedSeries (t u : R) : R⟦X⟧ :=
  C t * X + C u * X ^ 2 * mk (fun j => u ^ j)

private theorem boundarySeries_coeff (u : R) (j : Nat) :
    coeff j (boundarySeries u) = match j with | 0 => 0 | i + 1 => u ^ i := by
  cases j <;> simp [boundarySeries]

private theorem occupiedSeries_mk (t u : R) : occupiedSeries t u = mk (occupied t u) := by
  have he : occupiedSeries t u = C t * X + (C u * mk (fun j => u ^ j) * X) * X := by
    unfold occupiedSeries
    ring
  rw [he]
  ext j
  cases j with
  | zero => simp [occupied]
  | succ j =>
    cases j with
    | zero => simp [occupied]
    | succ j => simp [occupied, pow_succ', coeff_C_mul]

def leftSeries (u v : R) : R⟦X⟧ := 1 + C v * boundarySeries u

def rightSeries (u : R) : R⟦X⟧ := 1 + boundarySeries u

def singleSeries (t u v : R) (e : Edge) : R⟦X⟧ :=
  C (edgeWeight u v e) + C v * occupiedSeries t u

def peakSeries (t u v : R) : R⟦X⟧ :=
  C (t * v) + C v * (1 + C v) * occupiedSeries t u +
    (C v) ^ 2 * (occupiedSeries t u) ^ 2

private theorem leftSeries_mk (u v : R) : leftSeries u v = mk (leftWeight u v) := by
  ext j
  rw [leftSeries, map_add, coeff_one, coeff_C_mul, boundarySeries_coeff, coeff_mk]
  cases j <;> simp [leftWeight, mul_comm]

private theorem rightSeries_mk (u : R) : rightSeries u = mk (rightWeight u) := by
  ext j
  rw [rightSeries, map_add, coeff_one, boundarySeries_coeff, coeff_mk]
  cases j <;> simp [rightWeight, boundaryWeight]

private theorem singleSeries_mk (t u v : R) (e : Edge) :
    singleSeries t u v e = mk (singleWeight t u v e) := by
  ext j
  cases j <;> simp [singleSeries, occupiedSeries_mk, singleWeight, coeff_C_mul, occupied]

private def weightedOccupied (t u v : R) : Nat → R := fun j => v * occupied t u j

private theorem weightedOccupied_mk (t u v : R) :
    C v * occupiedSeries t u = mk (weightedOccupied t u v) := by
  ext j
  simp [occupiedSeries_mk, weightedOccupied, coeff_C_mul]

private def atZero (a : R) (j : Nat) : R := if j = 0 then a else 0

private theorem atZero_mk (a : R) : mk (atZero a) = C a := by
  ext n
  rw [coeff_mk, coeff_C, atZero]

private theorem pairWeight_cases (t u v : R) (i j : Nat) :
    pairWeight t u v i j =
      atZero t i * atZero v j +
      atZero 1 i * weightedOccupied t u v j +
      weightedOccupied t u v i * atZero v j +
      weightedOccupied t u v i * weightedOccupied t u v j := by
  cases i <;> cases j <;>
    simp [pairWeight, singleWeight, edgeWeight, occupied, weightedOccupied, atZero]

private theorem coeff_two_gaps (k r : Nat) (f g : Nat → R) (s : R⟦X⟧) (w : List Nat → R)
    (hs : ∀ j, coeff j s = ∑ h ∈ profiles k j, w h) :
    coeff r (mk f * mk g * s) =
      ∑ h ∈ profiles (k + 2) r, (f (h.headD 0) * g (h.tail.headD 0)) * w h.tail.tail := by
  rw [mul_assoc, coeff_cons_gap (k + 1) r f _ _ (fun j => coeff_cons_gap k j g s w hs)]
  simp only [mul_assoc]

private theorem coeff_pair_gap (t u v : R) (k r : Nat) (s : R⟦X⟧) (w : List Nat → R)
    (hs : ∀ j, coeff j s = ∑ h ∈ profiles k j, w h) :
    coeff r (peakSeries t u v * s) =
      ∑ h ∈ profiles (k + 2) r, pairWeight t u v (h.headD 0) (h.tail.headD 0) * w h.tail.tail := by
  let z := mk (weightedOccupied t u v)
  have he : peakSeries t u v =
      mk (atZero t) * mk (atZero v) + mk (atZero 1) * z + z * mk (atZero v) + z * z := by
    dsimp only [z]
    simp only [atZero_mk, ← weightedOccupied_mk, ← map_mul]
    unfold peakSeries
    simp only [map_one]
    ring
  rw [he]
  dsimp only [z]
  simp only [add_mul, map_add, coeff_two_gaps _ _ _ _ _ _ hs, pairWeight_cases,
    Finset.sum_add_distrib]

private def blockGaps : List Block → Nat
  | [] => 1
  | .single _ :: bs => blockGaps bs + 1
  | .peak :: bs => blockGaps bs + 2

private def blockSeries (t u v : R) : List Block → R⟦X⟧
  | [] => rightSeries u
  | .single e :: bs => singleSeries t u v e * blockSeries t u v bs
  | .peak :: bs => peakSeries t u v * blockSeries t u v bs

private theorem blockSeries_coeff (t u v : R) (bs : List Block) (r : Nat) :
    coeff r (blockSeries t u v bs) =
      ∑ hs ∈ profiles (blockGaps bs) r, blockWeights t u v bs hs := by
  induction bs generalizing r with
  | nil => simp [blockSeries, blockGaps, blockWeights, rightSeries_mk, profiles_one]
  | cons b bs ih =>
    cases b with
    | single e =>
      simp only [blockSeries, blockGaps, singleSeries_mk, coeff_cons_gap _ _ _ _ _ ih,
        blockWeights]
    | peak =>
      exact coeff_pair_gap t u v _ r _ _ ih

def insertionSeries (t u v : R) (es : List Edge) : R⟦X⟧ :=
  leftSeries u v * blockSeries t u v (blocks es)

private theorem blockGaps_blocks (es : List Edge) : blockGaps (blocks es) = es.length + 1 := by
  induction es using blocks.induct with
  | case1 es ih => simp [blocks, blockGaps, ih, Nat.add_assoc]
  | case2 e es hne ih =>
    have h : ¬ (e = .up ∧ es.head? = some .down) := by
      rintro ⟨rfl, h⟩
      cases es with
      | nil => contradiction
      | cons f fs =>
        simp only [List.head?_cons, Option.some.injEq] at h
        subst f
        exact hne fs rfl rfl
    simp [blocks_cons_of_not_peak e es h, blockGaps, ih]
  | case3 => rfl

private theorem edgesFrom_length (a : Nat) (cs : List Nat) : (edgesFrom a cs).length = cs.length := by
  induction cs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [edgesFrom, ih]

private theorem insertionSeries_coeff (t u v : R) (m a : Nat) (cs : List Nat) (r : Nat)
    (ha : a < m) (hcs : ∀ x ∈ cs, x < m) :
    coeff r (insertionSeries t u v (edges (a :: cs))) =
      ∑ hs ∈ profiles ((a :: cs).length + 1) r, wordWeight t u v (D5.S1.Words.UnaryGapWords.gap m (a :: cs) hs) := by
  rw [insertionSeries, leftSeries_mk, coeff_cons_gap _ _ _ _ _ (blockSeries_coeff t u v _),
    blockGaps_blocks]
  simp only [edges, edgesFrom_length, List.length_cons]
  apply Finset.sum_congr rfl
  intro hs h
  have hl := ((mem_profiles _ _ _).mp h).1
  cases hs with
  | nil => simp at hl
  | cons j hs =>
    exact (labelled_kernel t u v m a cs j hs ha hcs (by simpa using hl)).symm

private theorem peakEdges_noPeak (e : Edge) (es : List Edge)
    (h : ¬ (e = .up ∧ es.head? = some .down)) :
    peakEdges (decide (e = .up)) es = peakEdges false es := by
  cases es with
  | nil => rfl
  | cons f fs =>
    change ¬ (e = .up ∧ some f = some .down) at h
    cases e <;> cases f <;> simp_all [peakEdges]

private theorem blocksStats (es : List Edge) :
    let bs := blocks es
    peakEdges false es = bs.count .peak ∧
    es.count .tie = bs.count (.single .tie) ∧
    es.count .down = bs.count (.single .down) + bs.count .peak ∧
    es.length = bs.count (.single .up) + bs.count (.single .down) +
      bs.count (.single .tie) + 2 * bs.count .peak := by
  induction es using blocks.induct with
  | case1 es ih =>
    dsimp only at ih
    obtain ⟨hp, hk, hd, hl⟩ := ih
    simp [blocks, peakEdges, hp, hk, hd, hl]
    omega
  | case2 e es hne ih =>
    have h : ¬ (e = .up ∧ es.head? = some .down) := by
      rintro ⟨rfl, h⟩
      cases es with
      | nil => contradiction
      | cons f fs =>
        simp only [List.head?_cons, Option.some.injEq] at h
        subst f
        exact hne fs rfl rfl
    dsimp only at ih ⊢
    rw [blocks_cons_of_not_peak e es h]
    have hp' := peakEdges_noPeak e es h
    obtain ⟨hp, hk, hd, hl⟩ := ih
    rw [peakEdges, hp']
    cases e <;> simp [hp, hk, hd, hl] <;> omega
  | case3 => simp [blocks, peakEdges]

private theorem blockSeries_counts (t u v : R) (bs : List Block) :
    blockSeries t u v bs =
      rightSeries u * singleSeries t u v .up ^ bs.count (.single .up) *
      singleSeries t u v .down ^ bs.count (.single .down) *
      singleSeries t u v .tie ^ bs.count (.single .tie) * peakSeries t u v ^ bs.count .peak := by
  induction bs with
  | nil => simp [blockSeries]
  | cons b bs ih =>
    cases b with
    | peak => simp [blockSeries, ih, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    | single e =>
      cases e <;> simp [blockSeries, ih, pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- The six local series, with exponents computed from the literal word. -/
def closedKernel (t u v : R) (ℓ p k d : Nat) : R⟦X⟧ :=
  leftSeries u v * rightSeries u *
    singleSeries t u v .up ^ (ℓ - 1 - d - k - p) *
    singleSeries t u v .down ^ (d - p) *
    singleSeries t u v .tie ^ k * peakSeries t u v ^ p

theorem insertionSeries_closed (t u v : R) (a : Nat) (cs : List Nat) :
    insertionSeries t u v (edges (a :: cs)) =
      closedKernel t u v (a :: cs).length (peaks (a :: cs)) (ties (a :: cs))
        (descents (a :: cs)) := by
  let es := edges (a :: cs)
  let bs := blocks es
  have he : es.length = cs.length := edgesFrom_length a cs
  have hs := blocksStats es
  change peakEdges false es = bs.count .peak ∧ _ at hs
  obtain ⟨hp, hk, hd, hl⟩ := hs
  have hc := count_edges (a :: cs)
  have hpeak : peaks (a :: cs) = bs.count .peak := (peakEdges_eq _).symm.trans hp
  have htie : ties (a :: cs) = bs.count (.single .tie) := hc.1.symm.trans hk
  have hdesc : descents (a :: cs) = bs.count (.single .down) + bs.count .peak := hc.2.symm.trans hd
  change es.length = bs.count (.single .up) + bs.count (.single .down) +
    bs.count (.single .tie) + 2 * bs.count .peak at hl
  have hasc : (a :: cs).length - 1 - descents (a :: cs) - ties (a :: cs) - peaks (a :: cs) =
      bs.count (.single .up) := by
    simp only [List.length_cons]
    omega
  have hdown : descents (a :: cs) - peaks (a :: cs) = bs.count (.single .down) := by omega
  unfold insertionSeries closedKernel
  rw [blockSeries_counts, hasc, hdown, htie, hpeak]
  simp only [bs, es, mul_assoc]

theorem closedKernel_coeff (t u v : R) (m a : Nat) (cs : List Nat) (r : Nat)
    (ha : a < m) (hcs : ∀ x ∈ cs, x < m) :
    coeff r (closedKernel t u v (a :: cs).length (peaks (a :: cs)) (ties (a :: cs))
      (descents (a :: cs))) =
      ∑ hs ∈ profiles ((a :: cs).length + 1) r,
        wordWeight t u v (D5.S1.Words.UnaryGapWords.gap m (a :: cs) hs) := by
  rw [← insertionSeries_closed]
  exact insertionSeries_coeff t u v m a cs r ha hcs

private theorem peak_tie_capacity (a : Nat) (cs : List Nat) :
    2 * peaks (a :: cs) + ties (a :: cs) ≤ (a :: cs).length - 1 := by
  let es := edges (a :: cs)
  have he : es.length = cs.length := edgesFrom_length a cs
  obtain ⟨hp, hk, _, hl⟩ := blocksStats es
  rw [← peakEdges_eq, ← (count_edges (a :: cs)).1]
  change 2 * peakEdges false es + es.count .tie ≤ (a :: cs).length - 1
  simp only [List.length_cons]
  omega

section Ring

variable {S : Type*} [CommRing S]

private theorem geometric_mul (u : S) : mk (fun j => u ^ j) * (1 - C u * X) = 1 := by
  have h := congrArg (rescale u) (mk_one_mul_one_sub_eq_one S)
  simpa [map_mul, map_sub, rescale_X, rescale_mk] using h

/-- The denominator in the gap series is a formal-series unit. -/
def geometricDenominator (u : S) : S⟦X⟧ˣ :=
  Units.mkOfMulEqOne (1 - C u * X) (mk (fun j => u ^ j)) (by
    rw [mul_comm]
    exact geometric_mul u)

private theorem peakSeries_one (t u : S) :
    peakSeries t u 1 = (1 + occupiedSeries t u) ^ 2 + C t - 1 := by
  simp [peakSeries]
  ring

/-- The boundary factor in equation (10). -/
def bivarE (u : S) : S⟦X⟧ := 1 + boundarySeries u
def bivarA (t u : S) : S⟦X⟧ := 1 + occupiedSeries t u
def bivarC (t u : S) : S⟦X⟧ := C u + occupiedSeries t u
def bivarB (t u : S) : S⟦X⟧ := bivarA t u ^ 2 + C t - 1

/-- The four factors in equation (10), using a unit for the geometric denominator. -/
theorem bivariateFactors_eq10 (t u : S) :
    let inverse := (↑((geometricDenominator u)⁻¹) : S⟦X⟧)
    let A := 1 + C t * X + C u * X ^ 2 * inverse
    bivarE u = 1 + X * inverse ∧ bivarA t u = A ∧
      bivarC t u = C u + C t * X + C u * X ^ 2 * inverse ∧
      bivarB t u = A ^ 2 + C t - 1 := by
  dsimp only
  have hE : boundarySeries u = X * (↑((geometricDenominator u)⁻¹) : S⟦X⟧) := by
    change mk (fun j => u ^ j) * X = X * mk (fun j => u ^ j)
    exact mul_comm _ _
  have hS : occupiedSeries t u =
      C t * X + C u * X ^ 2 * (↑((geometricDenominator u)⁻¹) : S⟦X⟧) := rfl
  simp only [bivarE, bivarA, bivarB, bivarC, hE, hS, add_assoc, and_self]

private theorem closedKernel_one (t u : S) (ℓ p k d : Nat) (h₁ : p ≤ d)
    (h₂ : d + k + p ≤ ℓ - 1) :
    closedKernel t u 1 ℓ p k d =
      bivarE u ^ 2 * bivarA t u ^ (ℓ - 1 - 2 * p - k) *
        bivarC t u ^ k * bivarB t u ^ p := by
  have h : (ℓ - 1 - d - k - p) + (d - p) = ℓ - 1 - 2 * p - k := by omega
  rw [← h, pow_add]
  simp only [closedKernel, leftSeries, rightSeries, singleSeries, edgeWeight, map_one, one_mul,
    peakSeries_one, bivarE, bivarA, bivarC, bivarB]
  ring

private theorem insertionSeries_one (t u : S) (a : Nat) (cs : List Nat) :
    insertionSeries t u 1 (edges (a :: cs)) =
      bivarE u ^ 2 * bivarA t u ^ ((a :: cs).length - 1 - 2 * peaks (a :: cs) - ties (a :: cs)) *
        bivarC t u ^ ties (a :: cs) * bivarB t u ^ peaks (a :: cs) := by
  rw [insertionSeries_closed]
  apply closedKernel_one
  · obtain ⟨hp, _, hd, _⟩ := blocksStats (edges (a :: cs))
    rw [← peakEdges_eq, ← (count_edges (a :: cs)).2, hp, hd]
    omega
  · obtain ⟨hp, hk, hd, hl⟩ := blocksStats (edges (a :: cs))
    have he : (edges (a :: cs)).length = cs.length := edgesFrom_length a cs
    rw [← peakEdges_eq, ← (count_edges (a :: cs)).1, ← (count_edges (a :: cs)).2, hp, hk, hd]
    simp only [List.length_cons]
    omega

def ascentUnit (t u : S) : S⟦X⟧ˣ :=
  Units.mkOfMulEqOne (bivarA t u) (invOfUnit (bivarA t u) 1) (by
    apply mul_invOfUnit
    simp [bivarA, occupiedSeries])

/-- Equation (11) on the monomial t^p u^k, written using the inverse of an actual unit. -/
theorem insertionSeries_eq11 (t u : S) (a : Nat) (cs : List Nat) :
    let p := peaks (a :: cs)
    let k := ties (a :: cs)
    let A := ascentUnit t u
    insertionSeries t u 1 (edges (a :: cs)) =
      bivarE u ^ 2 * (A : S⟦X⟧) ^ ((a :: cs).length - 1) *
        (bivarB t u * (↑(A⁻¹) : S⟦X⟧) ^ 2) ^ p *
        (bivarC t u * (↑(A⁻¹) : S⟦X⟧)) ^ k := by
  dsimp only
  let p := peaks (a :: cs)
  let k := ties (a :: cs)
  let A := ascentUnit t u
  let d := (a :: cs).length - 1 - 2 * p - k
  have he : (a :: cs).length - 1 = d + (2 * p + k) := by
    have h := peak_tie_capacity a cs
    simp only [List.length_cons, Nat.add_sub_cancel] at h
    simp only [d, p, k, List.length_cons, Nat.add_sub_cancel]
    omega
  have hc : (A : S⟦X⟧) ^ (2 * p + k) * ((↑(A⁻¹) : S⟦X⟧) ^ 2) ^ p *
      (↑(A⁻¹) : S⟦X⟧) ^ k = 1 := by
    have hA : (A : S⟦X⟧) * (↑(A⁻¹) : S⟦X⟧) = 1 := by simp
    rw [← pow_mul, mul_assoc, ← pow_add, ← mul_pow, hA, one_pow]
  rw [insertionSeries_one]
  change bivarE u ^ 2 * (A : S⟦X⟧) ^ d * bivarC t u ^ k * bivarB t u ^ p =
    bivarE u ^ 2 * (A : S⟦X⟧) ^ ((a :: cs).length - 1) *
      (bivarB t u * (↑(A⁻¹) : S⟦X⟧) ^ 2) ^ p *
      (bivarC t u * (↑(A⁻¹) : S⟦X⟧)) ^ k
  rw [he, pow_add, mul_pow, mul_pow]
  calc
    _ = bivarE u ^ 2 * (A : S⟦X⟧) ^ d * bivarC t u ^ k * bivarB t u ^ p *
        ((A : S⟦X⟧) ^ (2 * p + k) * ((↑(A⁻¹) : S⟦X⟧) ^ 2) ^ p *
          (↑(A⁻¹) : S⟦X⟧) ^ k) := by rw [hc, mul_one]
    _ = _ := by ring

end Ring

end
end D5.S3.Combinatorics.Parking.DescentRefinement
