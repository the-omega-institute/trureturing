/- GID: D5/S3/Combinatorics/Parking/PeakTieDescentRecurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Parking/PeakTieDescentRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The bounded parking-word recurrence for strict peaks, ties, and descents. -/

import D5.S3.Combinatorics.Parking.MaximumLetterGaps
import D5.S3.Combinatorics.Parking.DescentGapKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MonoidAlgebra.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Parking.DescentRefinement

open scoped BigOperators
open PowerSeries
open D5.S1.Words.UnaryGapWords
open D5.S3.Combinatorics.ShankarWords.ActualWordExtremal (descents)

local notation "sorted" => List.insertionSort (· ≤ ·)

noncomputable section

def alphabetWords (m : Nat) : Nat → Finset (List Nat)
  | 0 => {[]}
  | n + 1 => (Finset.Icc 1 m).biUnion fun x =>
      (alphabetWords m n).map (consEmbedding x)

private theorem mem_alphabetWords (n m : Nat) (w : List Nat) :
    w ∈ alphabetWords m n ↔ w.length = n ∧ ∀ x ∈ w, 1 ≤ x ∧ x ≤ m := by
  induction n generalizing w with
  | zero => cases w <;> simp [alphabetWords]
  | succ n ih =>
    cases w with
    | nil => simp [alphabetWords, Finset.mem_biUnion, consEmbedding]
    | cons a as =>
      simp only [alphabetWords, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_map,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨x, hx, w, hw, he⟩
        have he' : x :: w = a :: as := he
        obtain ⟨rfl, rfl⟩ := List.cons.inj he'
        obtain ⟨hl, ha⟩ := (ih w).mp hw
        exact ⟨hl, fun y hy => (List.mem_cons.mp hy).elim (fun h => h.symm ▸ hx) (ha y)⟩
      · rintro ⟨hl, ha⟩
        exact ⟨a, ha a (by simp), as, (ih as).mpr
          ⟨hl, fun x hx => ha x (List.mem_cons_of_mem _ hx)⟩, rfl⟩

/-- All bounded parking words as a finite set of literal words. -/
def literalParking (n m : Nat) : Finset (List Nat) := by
  classical
  exact (alphabetWords m n).filter (fun w => RankBound (sorted w))

theorem mem_literalParking (n m : Nat) (w : List Nat) :
    w ∈ literalParking n m ↔ BoundedParking n m w := by
  simp [literalParking, mem_alphabetWords, BoundedParking, and_assoc]

private theorem count_zero_parking {n m : Nat} (hm : 1 ≤ m) (w : List Nat) :
    BoundedParking n m w ∧ w.count m = 0 ↔ BoundedParking n (m - 1) w := by
  rw [List.count_eq_zero]
  constructor
  · rintro ⟨⟨hl, hcap, hrank⟩, hz⟩
    refine ⟨hl, ?_, hrank⟩
    intro x hx
    obtain ⟨hpos, hxmax⟩ := hcap x hx
    have hne : x ≠ m := fun h => hz (h ▸ hx)
    exact ⟨hpos, by omega⟩
  · rintro ⟨hl, hcap, hrank⟩
    refine ⟨⟨hl, ?_, hrank⟩, ?_⟩
    · intro x hx
      obtain ⟨hp, hc⟩ := hcap x hx
      exact ⟨hp, by omega⟩
    · intro hx
      have h := (hcap m hx).2
      omega

/-- The first occurrence of m in the sorted word gives the literal multiplicity cutoff. -/
theorem max_count_cut {n m : Nat} (hmn : m ≤ n) (w : List Nat) (hw : BoundedParking n m w) :
    w.count m ≤ n - m + 1 := by
  by_cases hzero : w.count m = 0
  · omega
  obtain ⟨cs, hs, hne, hshape, he⟩ := gap_exists m w
  have hbound : ∀ x ∈ cs, x ≤ m := by
    intro x hx
    by_contra! h
    have hcount := (List.count_pos_iff.mpr hx : 0 < cs.count x)
    have hg := gap_counts m cs hs hshape x
    rw [← he] at hg
    have hwmem : x ∈ w := List.count_pos_iff.mp (by omega)
    exact (Nat.not_lt_of_ge (hw.2.1 x hwmem).2) h
  have hsum : hs.sum = w.count m := by
    rw [he, gap_counts m cs hs hshape m, List.count_eq_zero_of_not_mem (fun h => hne m h rfl)]
    simp
  have hsort : sorted w = sorted cs ++ List.replicate hs.sum m := by
    rw [he, sorted_gap_reconstruction m cs hs hshape hbound]
  have hlen : (sorted w).length = n := (List.length_insertionSort _ _).trans hw.1
  rw [hsort, List.length_append, List.length_replicate] at hlen
  have hrank := hw.2.2
  rw [hsort, rank_append_replicate _ _ _ (by omega)] at hrank
  omega

variable {R : Type*} [CommSemiring R]

def G (t u v : R) (n m : Nat) : R :=
  ∑ w ∈ literalParking n m, wordWeight t u v w

def topFiber (n m r : Nat) : Finset (List Nat) :=
  (literalParking n m).filter (fun w => w.count m = r)

private theorem mem_topFiber (n m r : Nat) (w : List Nat) :
    w ∈ topFiber n m r ↔ BoundedParking n m w ∧ w.count m = r := by
  simp [topFiber, mem_literalParking]

def retainedProfiles (n m r : Nat) : Finset (List Nat × List Nat) :=
  (literalParking (n - r) (m - 1)) ×ˢ profiles (n - r + 1) r

private theorem mem_retainedProfiles (n m r : Nat) (p : List Nat × List Nat) :
    p ∈ retainedProfiles n m r ↔
      BoundedParking (n - r) (m - 1) p.1 ∧ p.2.length = n - r + 1 ∧ p.2.sum = r := by
  simp [retainedProfiles, Finset.mem_product, mem_literalParking, mem_profiles]

theorem coefficient_fiber (t u v : R) {n m r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hr : 1 ≤ r) (hcut : r ≤ n - m + 1) :
    ∑ w ∈ topFiber n m r, wordWeight t u v w =
      ∑ w ∈ literalParking (n - r) (m - 1),
        coeff r (closedKernel t u v (n - r) (peaks w) (ties w) (descents w)) := by
  let : Fintype (Original n m r) := Fintype.ofFinset (topFiber n m r) (mem_topFiber n m r)
  let : Fintype (Retained n m r) :=
    Fintype.ofFinset (retainedProfiles n m r) (mem_retainedProfiles n m r)
  have hf :
      ∑ w ∈ topFiber n m r, wordWeight t u v w =
        ∑ p ∈ retainedProfiles n m r, wordWeight t u v (gap m p.1 p.2) := by
    rw [Finset.sum_subtype _ (mem_topFiber n m r), Finset.sum_subtype _ (mem_retainedProfiles n m r)]
    let e := parkingGapEquiv hm hmn hr hcut
    apply Fintype.sum_equiv e
    intro w
    have he := e.symm_apply_apply w
    exact (congrArg (fun x : Original n m r => wordWeight t u v x.val) he).symm
  rw [hf, retainedProfiles, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w hw
  obtain ⟨hlen, hmax, _⟩ := (mem_literalParking _ _ _).mp hw
  have hbound : ∀ x ∈ w, x < m := by
    intro x hx
    have := (hmax x hx).2
    omega
  cases w with
  | nil => simp at hlen; omega
  | cons a cs =>
    rw [← hlen, closedKernel_coeff t u v m a cs r (hbound a (by simp))
      (fun x hx => hbound x (by simp [hx]))]

/-- The literal bounded-parking enumerator satisfies the six-factor recurrence. -/
private theorem parking_recurrence (t u v : R) {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) :
    G t u v n m = G t u v n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1),
        ∑ w ∈ literalParking (n - r) (m - 1),
          coeff r (closedKernel t u v (n - r) (peaks w) (ties w) (descents w)) := by
  have maps : ∀ w ∈ literalParking n m, w.count m ∈ Finset.Icc 0 (n - m + 1) := by
    intro w hw
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, max_count_cut hmn w ((mem_literalParking _ _ _).mp hw)⟩
  have hsplit : (Finset.Icc 0 (n - m + 1)) = Insert.insert 0 (Finset.Icc 1 (n - m + 1)) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hzero : topFiber n m 0 = literalParking n (m - 1) := by
    ext w
    rw [mem_topFiber, mem_literalParking, count_zero_parking (by omega)]
  calc
    G t u v n m = ∑ r ∈ Finset.Icc 0 (n - m + 1), ∑ w ∈ topFiber n m r, wordWeight t u v w :=
      (Finset.sum_fiberwise_of_maps_to maps (wordWeight t u v)).symm
    _ = G t u v n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1), ∑ w ∈ topFiber n m r, wordWeight t u v w := by
      rw [hsplit, Finset.sum_insert (by simp), hzero, G]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact coefficient_fiber t u v hm hmn (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2

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

/-- The initial polynomial, including the singleton and empty word cases. -/
theorem parking_base (t u v : R) (n : Nat) : G t u v n 1 = u ^ (n - 1) := by
  have h : literalParking n 1 = {List.replicate n 1} := by
    ext w
    rw [mem_literalParking, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, hmax, _⟩
      rw [List.eq_replicate_iff]
      exact ⟨hl, fun x hx => by have := hmax x hx; omega⟩
    · rintro rfl
      refine ⟨by simp, ?_, ?_⟩
      · intro x hx
        simp [List.eq_of_mem_replicate hx]
      · have hs : sorted (List.replicate n 1) = List.replicate n 1 := by
          apply List.eq_replicate_iff.mpr
          exact ⟨List.length_insertionSort _ _ |>.trans (by simp),
            fun x hx => List.eq_of_mem_replicate ((List.perm_insertionSort _ _).mem_iff.mp hx)⟩
        rw [hs]
        intro i hi
        simp
  rw [G, h, Finset.sum_singleton, wordWeight_eq]
  cases n with
  | zero => simp [edges, weightFrom]
  | succ n =>
    simp [List.replicate_succ, edges, edgesFrom_replicate_self, weightFrom_eq,
      List.count_replicate, peaks_replicate_ties]

/-- A literal multivariate polynomial enumerator, with separate variables for all statistics. -/
def parkingPolynomial (n m : Nat) : MvPolynomial (Fin 3) ℕ :=
  G (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) n m

private theorem parkingPolynomial_recurrence {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) :
    parkingPolynomial n m = parkingPolynomial n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1),
        ∑ w ∈ literalParking (n - r) (m - 1),
          coeff r (closedKernel (MvPolynomial.X (0 : Fin 3)) (MvPolynomial.X 1)
            (MvPolynomial.X 2) (n - r) (peaks w) (ties w) (descents w)) :=
  parking_recurrence _ _ _ hm hmn

abbrev ParkingPolynomial := MvPolynomial (Fin 3) ℕ

/-- The operator on the polynomial alone. Each input monomial records the three
statistics needed by the six gap factors, with ordinary multiplicity as its coefficient. -/
def insertionOperator (ℓ r : Nat) : ParkingPolynomial →+ ParkingPolynomial :=
  AddMonoidAlgebra.liftNC (Nat.castAddMonoidHom ParkingPolynomial) fun a =>
    coeff r (closedKernel (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
      ℓ (a.toAdd 0) (a.toAdd 1) (a.toAdd 2))

theorem insertionOperator_monomial (ℓ r p k d : Nat) :
    insertionOperator ℓ r
      ((MvPolynomial.X 0 : ParkingPolynomial) ^ p * MvPolynomial.X 1 ^ k * MvPolynomial.X 2 ^ d) =
    coeff r (closedKernel (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) ℓ p k d) := by
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]
  change AddMonoidAlgebra.liftNC _ _
    (AddMonoidAlgebra.single (Finsupp.single (0 : Fin 3) p +
      Finsupp.single 1 k + Finsupp.single 2 d) (1 : Nat)) = _
  simp

/-- Closed recurrence using only the smaller literal enumerator polynomials. -/
theorem parkingPolynomial_operator_recurrence {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) :
    parkingPolynomial n m = parkingPolynomial n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1),
        insertionOperator (n - r) r (parkingPolynomial (n - r) (m - 1)) := by
  rw [parkingPolynomial_recurrence hm hmn]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  unfold parkingPolynomial G
  rw [map_sum]
  simp only [wordWeight, insertionOperator_monomial]

section Bivariate

variable {S : Type*} [CommRing S]

/-- The insertion operator in equation (11) applied to the literal bivariate
enumerator at length ℓ. The substitution takes place in the series ring. -/
def insertEq11 (t u : S) (ℓ m r : Nat) : S :=
  let A := ascentUnit t u
  coeff r (bivarE u ^ 2 * (A : S⟦X⟧) ^ (ℓ - 1) *
    G (bivarB t u * (↑(A⁻¹) : S⟦X⟧) ^ 2) (bivarC t u * (↑(A⁻¹) : S⟦X⟧)) 1 ℓ m)

private theorem insertEq11_coeff (t u : S) {ℓ m : Nat} (hl : 0 < ℓ) (r : Nat) :
    insertEq11 t u ℓ m r =
      ∑ w ∈ literalParking ℓ m, coeff r (closedKernel t u 1 ℓ (peaks w) (ties w) (descents w)) := by
  unfold insertEq11 G
  dsimp only
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have he := ((mem_literalParking _ _ _).mp hw).1
  cases w with
  | nil => simp at he; omega
  | cons a cs =>
    have h := insertionSeries_eq11 t u a cs
    dsimp only at h
    rw [← he, ← insertionSeries_closed, h, wordWeight, one_pow, mul_one]
    simp only [mul_assoc]

/-- Theorem 1.2 at v = 1, with its equation (11) operator and literal domain. -/
theorem parking_recurrence_eq11 (t u : S) {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) :
    G t u 1 n m = G t u 1 n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1), insertEq11 t u (n - r) (m - 1) r := by
  rw [parking_recurrence t u 1 hm hmn]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hcut := (Finset.mem_Icc.mp hr).2
  exact (insertEq11_coeff t u (by omega) r).symm

end Bivariate

end
end D5.S3.Combinatorics.Parking.DescentRefinement
