/- GID: D5/S3/Fourier/Concentration/HomometricTripleCollision
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/HomometricTripleCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/Concentration/HomometricTripleCollision.differencesDetermineTripleMass; result=D5/S3/Fourier/Concentration/HomometricTripleCollision.differences_do_not_determine_triple_mass; claim=D5/S3/Fourier/Concentration/HomometricTripleCollision.differencesDetermineTripleMass
   digest: Equal signed difference profiles allow unequal disjoint triple collision counts. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! A finite obstruction to determining the disjoint triple count from pair differences. -/

open Finset

set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.HomometricTripleCollision

private abbrev Point := Fin 9
private abbrev Triple := Point × Point × Point
private abbrev Grid := Fin 3 × Fin 3

private def directedDifferenceCount (g : Point → ℕ) (gap : ℤ) : ℕ :=
  ∑ p : Point × Point, if (g p.1 : ℤ) - g p.2 = gap then 1 else 0

private def tripleSum (g : Point → ℕ) (u : Triple) : ℕ :=
  g u.1 + g u.2.1 + g u.2.2

private def avoids (i : Point) (u : Triple) : Bool :=
  i != u.1 && i != u.2.1 && i != u.2.2

private def rightCount (g : Point → ℕ) (u : Triple) : ℕ :=
  (univ.filter fun v : Triple =>
    tripleSum g u == tripleSum g v && avoids u.1 v && avoids u.2.1 v && avoids u.2.2 v).card

private def rowCount (g : Point → ℕ) (i : Point) : ℕ :=
  ∑ j : Point, ∑ k : Point, rightCount g (i, j, k)

private def disjointTripleMass (g : Point → ℕ) : ℕ := ∑ i, rowCount g i

/-- The claim that knowing the number of occurrences of each signed pair
difference determines the disjoint equal-sum triple count for nine-point spectra. -/
def differencesDetermineTripleMass : Prop :=
  ∀ a b : Fin 9 → ℕ, Function.Injective a → Function.Injective b →
    (∀ gap : ℤ, directedDifferenceCount a gap = directedDifferenceCount b gap) →
    disjointTripleMass a = disjointTripleMass b

private def first : Point → ℕ := ![0, 1, 3, 4, 5, 7, 9, 10, 12]
private def second : Point → ℕ := ![9, 10, 12, 5, 6, 8, 0, 1, 3]
private def small : Fin 3 → ℤ := ![0, 1, 3]
private def large : Fin 3 → ℤ := ![0, 4, 9]
private def gridIndex : Grid ≃ Point := finProdFinEquiv

private theorem first_on_grid (p : Grid) :
    (first (gridIndex p) : ℤ) = small p.2 + large p.1 := by
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> decide

private theorem second_on_grid (p : Grid) :
    (second (gridIndex p) : ℤ) = 9 + small p.2 - large p.1 := by
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> decide

private def swapRows : Grid × Grid ≃ Grid × Grid where
  toFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  invFun p := ((p.2.1, p.1.2), (p.1.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem equal_difference_counts (gap : ℤ) :
    directedDifferenceCount first gap = directedDifferenceCount second gap := by
  unfold directedDifferenceCount
  let productIndex := Equiv.prodCongr gridIndex gridIndex
  let swap := (productIndex.symm.trans swapRows).trans productIndex
  apply Fintype.sum_equiv swap
  intro p
  obtain ⟨q, rfl⟩ := productIndex.surjective p
  simp only [swap, Equiv.trans_apply, Equiv.symm_apply_apply]
  change (if (first (gridIndex q.1) : ℤ) - first (gridIndex q.2) = gap
      then 1 else 0) = (if (second (gridIndex (swapRows q).1) : ℤ) -
      second (gridIndex (swapRows q).2) = gap then 1 else 0)
  have heq : (first (gridIndex q.1) : ℤ) - first (gridIndex q.2) =
      (second (gridIndex (swapRows q).1) : ℤ) - second (gridIndex (swapRows q).2) := by
    rw [first_on_grid, first_on_grid, second_on_grid, second_on_grid]
    dsimp [swapRows]
    ring
  rw [heq]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
-- Kernel reduction checks nine fixed rows of pairs of triples.
private theorem first_rows (i : Point) :
    rowCount first i = (![604, 654, 684, 748, 716, 682, 688, 657, 543] : Point → ℕ) i := by
  fin_cases i <;> decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
-- The second spectrum has the same finite enumeration size.
private theorem second_rows (i : Point) :
    rowCount second i = (![700, 659, 563, 718, 727, 717, 602, 641, 625] : Point → ℕ) i := by
  fin_cases i <;> decide

private theorem exact_masses :
    disjointTripleMass first = 5976 ∧ disjointTripleMass second = 5952 := by
  simp only [disjointTripleMass, first_rows, second_rows]
  decide

/-- Full signed difference counts do not determine the disjoint degree-three mass. -/
theorem differences_do_not_determine_triple_mass : ¬ differencesDetermineTripleMass := by
  intro determines
  have hfirst : Function.Injective first := by
    change ∀ i j : Point, first i = first j → i = j
    decide
  have hsecond : Function.Injective second := by
    change ∀ i j : Point, second i = second j → i = j
    decide
  have h := determines first second hfirst hsecond equal_difference_counts
  rw [exact_masses.1, exact_masses.2] at h
  exact (by decide : (5976 : ℕ) ≠ 5952) h

end D5.S3.Fourier.Concentration.HomometricTripleCollision
