/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeResourceEnvelope
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Joint active polling, update, trial-read and literal resource ledger. -/

import D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeResourceEnvelope

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address)
open DelayedOriginalReadout
open BoundedPreorderTrial

/-- The candidate offsets in one first-completion interval, with repeats retained
by the concrete offset map rather than quotienting physical calls. -/
def trialIndices (start K : Nat) : Finset Nat := Finset.range (K - start + 1)

/-- The actual physical query list submitted by candidate `start+i`. -/
def trialQueries (h τ start : Nat) (u : Source) (i : Nat) : List Address :=
  physicalQueries (start + i) (trial h (virtualSource u τ (start + i)))

/-- Total source Reads in all candidates through the first completion. -/
def trialReadTotal (h τ start K : Nat) (u : Source) : Nat :=
  Finset.sum (trialIndices start K) (fun i => (trialQueries h τ start u i).length)

/-- Total submitted literal length in all those decoder calls. -/
def trialLiteralTotal (h τ start K : Nat) (u : Source) : Nat :=
  Finset.sum (trialIndices start K) (fun i =>
    ((trialQueries h τ start u i).map List.length).sum)

/-- Polling plus trial Reads; Updates are accounted separately in `U`. -/
def activeReadCount (U q : Nat) : Nat := U + 1 + q

private theorem list_map_sum_le {α : Type} (f : α → Nat) (xs : List α) (c : Nat)
    (bound : ∀ x ∈ xs, f x ≤ c) :
    (xs.map f).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := bound x (by simp)
      have hxs : ∀ y ∈ xs, f y ≤ c := by
        intro y hy
        exact bound y (by simp [hy])
      have hi := ih hxs
      calc
        f x + (xs.map f).sum ≤ c + xs.length * c := Nat.add_le_add hx hi
        _ = (xs.length + 1) * c := by ring

private theorem halfCeil_le_even {N B : Nat} (hN : N ≤ B) (hB : B % 2 = 0) :
    halfCeil N ≤ B / 2 := by
  have hmod : N % 2 < 2 := Nat.mod_lt N (by decide : 0 < 2)
  have hdiv : N / 2 ≤ B / 2 := Nat.div_le_div_right hN
  unfold halfCeil
  omega

/--
The active ledger is a single relation over the exact first-completion interval.
It joins the stationary decoder contracts to the polling/update prefix and keeps
all repeated physical literals in the sums.  No installation or routing row is
silently elided: those are separate inputs to the eventual complete-word
construction, while this theorem closes the source-side budget consumed by it.
-/
theorem active_resource_ledger
    (h τ start t B k : Nat) (u y : Source)
    (hu : u.length = h)
    (hy : y = substitution^[τ] u)
    (hstartτ : start ≤ τ)
    (hentry : t + rightClock u < B)
    (hτclock : τ = B - rightClock u)
    (hstart : start = B - 2*h + 1)
    (hBeven : B % 2 = 0) :
    ∃ K, start ≤ K ∧ K ≤ τ ∧
      let U := B - t - rightClock u
      let P := h - 1 + B / 2
      let q := trialReadTotal h τ start K u
      let a := trialLiteralTotal h τ start K u
      let Q := activeReadCount U q
      let H := 2*B + 1 + 2*h*(4*h-2)
      let R := 2*k + 7
      (1 ≤ U ∧ U ≤ B) ∧
      (K - start + 1 ≤ 2*h) ∧
      (q ≤ 2*h*(4*h-2)) ∧
      (Q + U ≤ R*H) ∧
      (Q + U = (2*U + 1) + q) ∧
      (∀ i ∈ trialIndices start K, ∀ p ∈ trialQueries h τ start u i,
        p.length ≤ P) ∧
      ((U+1)*(B/2) + a ≤ (B+1)*B/2 + 2*h*(4*h-2)*P) := by
  have hh : 0 < h := by
    rw [← hu]
    exact u.length_pos
  obtain ⟨all, licensed, K, hKstart, hKτ, hKcomplete, hminimal, hKcount,
      hKpoly, hprefix⟩ := bounded_preorder_trial h τ start u y hu hy hstartτ
  have hτB : τ ≤ B := by
    rw [hτclock]
    exact Nat.sub_le _ _
  have hKcount' : K - start + 1 ≤ 2*h := by
    have : K - start + 1 ≤ τ - start + 1 := hKcount
    omega
  let U := B - t - rightClock u
  let P := h - 1 + B / 2
  let q := trialReadTotal h τ start K u
  let a := trialLiteralTotal h τ start K u
  let Q := activeReadCount U q
  let H := 2*B + 1 + 2*h*(4*h-2)
  let R := 2*k + 7
  have hU : 1 ≤ U ∧ U ≤ B := by
    dsimp [U]
    omega
  have eachSpec (i : Nat) (hi : i ∈ trialIndices start K) :
      TrialSpec h τ (start+i) u y := by
    have hi' : i < K - start + 1 := by simpa [trialIndices] using hi
    have hNstart : start ≤ start+i := by omega
    have hNK : start+i ≤ K := by omega
    exact (hprefix (start+i) hNstart hNK).2
  have eachRead (i : Nat) (hi : i ∈ trialIndices start K) :
      (trialQueries h τ start u i).length ≤ 4*h-2 := by
    exact (eachSpec i hi).reads_bound
  have eachQueryLength (i : Nat) (hi : i ∈ trialIndices start K)
      (p : Address) (hp : p ∈ trialQueries h τ start u i) : p.length ≤ P := by
    have hs := (eachSpec i hi).literal_bound p hp
    have hi' : i < K - start + 1 := by simpa [trialIndices] using hi
    have hN : start+i ≤ K := by omega
    have hKB : K ≤ B := hKτ.trans hτB
    have hNB : start+i ≤ B := hN.trans hKB
    dsimp [P]
    have hc := halfCeil_le_even hNB hBeven
    omega
  have qBound : q ≤ 2*h*(4*h-2) := by
    dsimp [q, trialReadTotal]
    calc
      Finset.sum (trialIndices start K) (fun i => (trialQueries h τ start u i).length) ≤
          Finset.sum (trialIndices start K) (fun _i => (4*h-2)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact eachRead i hi
      _ = (K-start+1)*(4*h-2) := by simp [trialIndices, Nat.mul_comm]
      _ ≤ 2*h*(4*h-2) := by
        exact Nat.mul_le_mul_right (4*h-2) hKcount'
  have aEach (i : Nat) (hi : i ∈ trialIndices start K) :
      ((trialQueries h τ start u i).map List.length).sum ≤ (4*h-2)*P := by
    have hm := list_map_sum_le List.length (trialQueries h τ start u i) P
      (eachQueryLength i hi)
    exact hm.trans (Nat.mul_le_mul_right P (eachRead i hi))
  have aBound : a ≤ 2*h*(4*h-2)*P := by
    dsimp [a, trialLiteralTotal]
    calc
      Finset.sum (trialIndices start K) (fun i =>
          ((trialQueries h τ start u i).map List.length).sum) ≤
          Finset.sum (trialIndices start K) (fun _i => ((4*h-2)*P)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact aEach i hi
      _ = (K-start+1)*((4*h-2)*P) := by simp [trialIndices, Nat.mul_comm]
      _ ≤ (2*h)*((4*h-2)*P) := by
        exact Nat.mul_le_mul_right ((4*h-2)*P) hKcount'
      _ = 2*h*(4*h-2)*P := by ring
  have callsBound : Q + U ≤ H := by
    dsimp [Q, activeReadCount, H]
    have hq := qBound
    omega
  have rpos : 1 ≤ R := by dsimp [R]; omega
  have callsScaled : Q + U ≤ R*H := by
    have hRH : H ≤ R*H := by
      simpa [Nat.one_mul] using (Nat.mul_le_mul_right H rpos)
    exact callsBound.trans hRH
  have pollBound : (U+1)*(B/2) ≤ (B+1)*B/2 := by
    have hu' : U+1 ≤ B+1 := by omega
    have hpoll : (U+1)*(B/2) ≤ (B+1)*(B/2) :=
      Nat.mul_le_mul_right (B/2) hu'
    have heq : (B+1)*(B/2) = (B+1)*B/2 := by
      exact (Nat.mul_div_assoc (B+1) (Nat.dvd_of_mod_eq_zero hBeven)).symm
    exact hpoll.trans_eq heq
  have totalLiteralBound : (U+1)*(B/2) + a ≤
      (B+1)*B/2 + 2*h*(4*h-2)*P := by
    exact Nat.add_le_add pollBound aBound
  have qEq : Q + U = (2*U + 1) + q := by
    dsimp [Q, activeReadCount]
    omega
  refine ⟨K, hKstart, hKτ, ?_⟩
  dsimp [U, P, q, a, Q, H, R]
  refine ⟨hU, hKcount', qBound, ?_, ?_, ?_, totalLiteralBound⟩
  · exact callsScaled
  · simpa [U, Q, activeReadCount, q] using qEq
  · intro i hi p hp
    exact eachQueryLength i hi p hp

end D5.S3.Arith.FibonacciAtomic.Observer.NativeResourceEnvelope
