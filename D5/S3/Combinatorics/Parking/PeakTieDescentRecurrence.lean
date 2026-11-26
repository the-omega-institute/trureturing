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
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MonoidAlgebra.Lift

/-! Counting words by maximum-letter multiplicity gives a recurrence on trivariate polynomials. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Parking.DescentRefinement

open scoped BigOperators
open PowerSeries
open D5.S1.Words.UnaryGapWords
open D5.S3.Combinatorics.ShankarWords.ActualWordExtremal (descents)

local notation "sorted" => List.insertionSort (· ≤ ·)

noncomputable section

private def alphabetWords (m : Nat) : Nat → Finset (List Nat)
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

variable {R : Type*} [CommSemiring R]

def G (t u v : R) (n m : Nat) : R :=
  ∑ w ∈ literalParking n m, wordWeight t u v w

def topFiber (n m r : Nat) : Finset (List Nat) :=
  (literalParking n m).filter (fun w => w.count m = r)

private theorem mem_topFiber (n m r : Nat) (w : List Nat) :
    w ∈ topFiber n m r ↔ BoundedParking n m w ∧ w.count m = r := by
  simp [topFiber, mem_literalParking]

private def retainedProfiles (n m r : Nat) : Finset (List Nat × List Nat) :=
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
  rw [G, h, Finset.sum_singleton, wordWeight_replicate]

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

/-- Equation (11) on an arbitrary bivariate polynomial over the coefficient ring. -/
def bivariateInsertionOperator (t u : S) (ℓ r : Nat) (F : MvPolynomial (Fin 2) S) : S :=
  let A := ascentUnit t u
  let substitution := MvPolynomial.eval₂Hom C ![
    bivarB t u * (↑(A⁻¹) : S⟦X⟧) ^ 2, bivarC t u * (↑(A⁻¹) : S⟦X⟧)]
  coeff r (bivarE u ^ 2 * (A : S⟦X⟧) ^ (ℓ - 1) * substitution F)

/-- The literal bivariate enumerator is obtained by setting the descent marker to one. -/
def bivariateParkingPolynomial (ℓ m : Nat) : MvPolynomial (Fin 2) S :=
  G (MvPolynomial.X 0) (MvPolynomial.X 1) 1 ℓ m

/-- The specialization is coefficientwise polynomial substitution. -/
theorem specialize_descent (ℓ m : Nat) :
    MvPolynomial.eval₂Hom (Nat.castRingHom (MvPolynomial (Fin 2) S))
      ![MvPolynomial.X 0, MvPolynomial.X 1, 1] (parkingPolynomial ℓ m) =
      (bivariateParkingPolynomial ℓ m : MvPolynomial (Fin 2) S) := by
  simp [parkingPolynomial, bivariateParkingPolynomial, G, wordWeight, map_sum]

/-- Equation (11) applied to the literal bivariate enumerator. -/
def insertEq11 (t u : S) (ℓ m r : Nat) : S :=
  bivariateInsertionOperator t u ℓ r (bivariateParkingPolynomial ℓ m)

theorem insertEq11_coeff (t u : S) {ℓ m : Nat} (hl : 0 < ℓ) (r : Nat) :
    insertEq11 t u ℓ m r =
      ∑ w ∈ literalParking ℓ m, coeff r (closedKernel t u 1 ℓ (peaks w) (ties w) (descents w)) := by
  unfold insertEq11 bivariateInsertionOperator bivariateParkingPolynomial G
  dsimp only
  rw [map_sum]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have he := ((mem_literalParking _ _ _).mp hw).1
  cases w with
  | nil => simp at he; omega
  | cons a cs =>
    have h := insertionSeries_eq11 t u a cs
    dsimp only at h
    rw [← he, ← insertionSeries_closed, h, wordWeight]
    simp [mul_assoc]

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

/-- The bound-one initial value, the trivariate recurrence, and its recovery of Theorem 1.2. -/
theorem result :
    (∀ n, parkingPolynomial n 1 = (MvPolynomial.X (1 : Fin 3)) ^ (n - 1)) ∧
    (∀ n m, 2 ≤ m → m ≤ n →
      parkingPolynomial n m = parkingPolynomial n (m - 1) +
        ∑ r ∈ Finset.Icc 1 (n - m + 1),
          insertionOperator (n - r) r (parkingPolynomial (n - r) (m - 1))) ∧
    (∀ n m, MvPolynomial.eval₂Hom (Nat.castRingHom (MvPolynomial (Fin 2) S))
      ![MvPolynomial.X 0, MvPolynomial.X 1, 1] (parkingPolynomial n m) =
        (bivariateParkingPolynomial n m : MvPolynomial (Fin 2) S)) ∧
    (∀ (t u : S),
      let inverse := (↑((geometricDenominator u)⁻¹) : S⟦X⟧)
      let A := 1 + C t * X + C u * X ^ 2 * inverse
      bivarE u = 1 + X * inverse ∧ bivarA t u = A ∧
        bivarC t u = C u + C t * X + C u * X ^ 2 * inverse ∧
        bivarB t u = A ^ 2 + C t - 1) ∧
    (∀ (t u : S) n, G t u 1 n 1 = u ^ (n - 1)) ∧
    (∀ (t u : S) n m, 2 ≤ m → m ≤ n →
      G t u 1 n m = G t u 1 n (m - 1) +
        ∑ r ∈ Finset.Icc 1 (n - m + 1), insertEq11 t u (n - r) (m - 1) r) :=
  ⟨fun n => parking_base _ _ _ n,
    fun _ _ hm hmn => parkingPolynomial_operator_recurrence hm hmn,
    specialize_descent, bivariateFactors_eq10,
    fun t u n => parking_base t u 1 n,
    fun t u _ _ hm hmn => parking_recurrence_eq11 t u hm hmn⟩

end Bivariate

end
end D5.S3.Combinatorics.Parking.DescentRefinement
