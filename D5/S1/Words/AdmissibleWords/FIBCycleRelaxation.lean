/- GID: D5/S1/Words/AdmissibleWords/FIBCycleRelaxation
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBCycleRelaxation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A real family passes all cycle inequalities but has no joint cut law. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.FIBCycleRelaxation

open scoped BigOperators

private def cut (x y : Bool) : ℕ := (x != y).toNat

/-- A linear inequality satisfied by each cut, with the reference vertex on the false side. -/
private theorem cutSeparates : ∀ s h k t w : Bool,
    cut w s + cut t h + h.toNat + k.toNat ≤
      cut s h + cut s k + cut w h + cut w k + cut t k + s.toNat + w.toNat := by
  decide

private def event (x : Fin 5 → Bool) (v : Fin 6) : Bool :=
  if h : v.val = 0 then false else x ⟨v.val - 1, by omega⟩

private theorem allCuts (x : Fin 5 → Bool) :
    cut (event x 5) (event x 1) + cut (event x 4) (event x 2) +
        cut (event x 0) (event x 2) + cut (event x 0) (event x 3) ≤
      cut (event x 1) (event x 2) + cut (event x 1) (event x 3) +
        cut (event x 5) (event x 2) + cut (event x 5) (event x 3) +
        cut (event x 4) (event x 3) + cut (event x 0) (event x 1) +
        cut (event x 0) (event x 5) := by
  have hfalse (b : Bool) : cut false b = b.toNat := by cases b <;> rfl
  simpa only [show event x 0 = false from rfl, hfalse] using
    cutSeparates (event x 1) (event x 2) (event x 3) (event x 4) (event x 5)

private def mixture {I : Type*} [Fintype I] (x : I → Fin 5 → Bool) (weight : I → ℝ)
    (u v : Fin 6) : ℝ := ∑ j, weight j * cut (event (x j) u) (event (x j) v)

private theorem mixtureBound {I : Type*} [Fintype I]
    (x : I → Fin 5 → Bool) (weight : I → ℝ) (nonneg : ∀ j, 0 ≤ weight j) :
    mixture x weight 5 1 + mixture x weight 4 2 + mixture x weight 0 2 +
        mixture x weight 0 3 ≤
      mixture x weight 1 2 + mixture x weight 1 3 + mixture x weight 5 2 +
        mixture x weight 5 3 + mixture x weight 4 3 + mixture x weight 0 1 +
        mixture x weight 0 5 := by
  let d (j : I) (u v : Fin 6) : ℝ := cut (event (x j) u) (event (x j) v)
  have termwise (j : I) : d j 5 1 + d j 4 2 + d j 0 2 + d j 0 3 ≤
      d j 1 2 + d j 1 3 + d j 5 2 + d j 5 3 + d j 4 3 + d j 0 1 + d j 0 5 := by
    dsimp only [d]
    exact_mod_cast allCuts (x j)
  have weighted := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => mul_le_mul_of_nonneg_left (termwise j) (nonneg j))
  simpa only [d, mul_add, Finset.sum_add_distrib, mixture] using weighted

private def star (u v : Fin 6) : ℕ := cut (u == 0) (v == 0)

private def corner : Fin 6 → Fin 6 → ℕ :=
  ![![0, 1, 2, 2, 1, 1],
    ![1, 0, 1, 1, 2, 2],
    ![2, 1, 0, 2, 3, 1],
    ![2, 1, 2, 0, 1, 1],
    ![1, 2, 3, 1, 0, 2],
    ![1, 2, 1, 1, 2, 0]]

private theorem starTriangle : ∀ u v w : Fin 6, star u w ≤ star u v + star v w := by decide
private theorem cornerTriangle : ∀ u v w : Fin 6,
    corner u w ≤ corner u v + corner v w := by decide
private theorem starPerimeter : ∀ u v w : Fin 6,
    star u v + star v w + star w u ≤ 2 := by decide
private theorem cornerPerimeter : ∀ u v w : Fin 6,
    corner u v + corner v w + corner w u ≤ 6 := by decide

def family (q c : ℝ) (u v : Fin 6) : ℝ :=
  (q - c) * star u v + c * corner u v

private theorem familyTriangles {q c : ℝ} (hc : 0 ≤ c) (hqc : c ≤ q) (hunit : q + 2 * c ≤ 1) :
    (∀ u v w, family q c u w ≤ family q c u v + family q c v w) ∧
    (∀ u v w, family q c u v + family q c v w + family q c w u ≤ 2) := by
  have hdiff : 0 ≤ q - c := sub_nonneg.mpr hqc
  constructor
  · intro u v w
    have hs : (star u w : ℝ) ≤ star u v + star v w := by exact_mod_cast starTriangle u v w
    have hp : (corner u w : ℝ) ≤ corner u v + corner v w := by
      exact_mod_cast cornerTriangle u v w
    calc
      family q c u w ≤ (q - c) * (star u v + star v w) + c * (corner u v + corner v w) :=
        add_le_add (mul_le_mul_of_nonneg_left hs hdiff) (mul_le_mul_of_nonneg_left hp hc)
      _ = _ := by unfold family; ring
  · intro u v w
    have hs : (star u v : ℝ) + star v w + star w u ≤ 2 := by exact_mod_cast starPerimeter u v w
    have hp : (corner u v : ℝ) + corner v w + corner w u ≤ 6 := by
      exact_mod_cast cornerPerimeter u v w
    calc
      _ = (q - c) * (star u v + star v w + star w u) +
          c * (corner u v + corner v w + corner w u) := by unfold family; ring
      _ ≤ (q - c) * 2 + c * 6 :=
        add_le_add (mul_le_mul_of_nonneg_left hs hdiff) (mul_le_mul_of_nonneg_left hp hc)
      _ ≤ _ := by linarith

private theorem familyOutside {q c : ℝ} (hc : 0 < c) :
    ¬ (family q c 5 1 + family q c 4 2 + family q c 0 2 + family q c 0 3 ≤
      family q c 1 2 + family q c 1 3 + family q c 5 2 + family q c 5 3 +
        family q c 4 3 + family q c 0 1 + family q c 0 5) := by
  norm_num [family, star, corner, cut]
  linarith

/-- In vertex order reference, S, H, K, T, W, retain the marginal, edge and query pairs. -/
def observed : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (5, 2), (5, 3), (4, 3),
    (5, 1), (4, 2)}

private theorem familyUnrealizable {q c : ℝ} (hc : 0 < c) (I : Type*) [Fintype I] :
    ¬ ∃ (outcome : I → Fin 5 → Bool) (weight : I → ℝ), (∀ i, 0 ≤ weight i) ∧
      ∀ p ∈ observed, mixture outcome weight p.1 p.2 = family q c p.1 p.2 := by
  rintro ⟨outcome, weight, nonneg, fit⟩
  have law := mixtureBound outcome weight nonneg
  have edgeReadout (a b : Fin 6) (h : (a, b) ∈ observed) :
      mixture outcome weight a b = family q c a b := fit (a, b) h
  rw [edgeReadout 5 1 (by decide), edgeReadout 4 2 (by decide), edgeReadout 0 2 (by decide),
    edgeReadout 0 3 (by decide), edgeReadout 1 2 (by decide), edgeReadout 1 3 (by decide),
    edgeReadout 5 2 (by decide), edgeReadout 5 3 (by decide), edgeReadout 4 3 (by decide),
    edgeReadout 0 1 (by decide), edgeReadout 0 5 (by decide)] at law
  exact familyOutside hc law

private def signedDistance {V : Type*} (d : V → V → ℝ) (u v : V × Bool) : ℝ :=
  if u.2 = v.2 then d u.1 v.1 else 1 - d u.1 v.1

private theorem signedTriangle {V : Type*} (d : V → V → ℝ)
    (symmetric : ∀ u v, d u v = d v u)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (perimeter : ∀ u v w, d u v + d v w + d w u ≤ 2)
    (u v w : V × Bool) :
    signedDistance d u w ≤ signedDistance d u v + signedDistance d v w := by
  rcases u with ⟨u, uSide⟩
  rcases v with ⟨v, vSide⟩
  rcases w with ⟨w, wSide⟩
  have direct := triangle u v w
  have viaW := triangle u w v
  have viaU := triangle v u w
  have circ := perimeter u v w
  rw [symmetric w v] at viaW
  rw [symmetric v u] at viaU
  rw [symmetric w u] at circ
  cases uSide <;> cases vSide <;> cases wSide <;>
    simp [signedDistance] <;> linarith

private def walkCost {V : Type*} (d : V → V → ℝ) :
    V → List V → V → ℝ
  | u, [], v => d u v
  | u, x :: rest, v => d u x + walkCost d x rest v

private theorem direct_le_walk {V : Type*} (d : V → V → ℝ)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (u : V) (middle : List V) (v : V) : d u v ≤ walkCost d u middle v := by
  induction middle generalizing u with
  | nil => exact le_rfl
  | cons x rest ih =>
    exact (triangle u x v).trans (add_le_add_right (ih x) (d u x))

private theorem starSymmetric : ∀ u v : Fin 6, star u v = star v u := by decide
private theorem cornerSymmetric : ∀ u v : Fin 6, corner u v = corner v u := by decide
private theorem starDiagonal : ∀ u : Fin 6, star u u = 0 := by decide
private theorem cornerDiagonal : ∀ u : Fin 6, corner u u = 0 := by decide

private theorem familyCycle {q c : ℝ} (hc : 0 ≤ c) (hqc : c ≤ q) (hunit : q + 2 * c ≤ 1)
    (u : Fin 6) (middle : List (Fin 6 × Bool)) :
    1 ≤ walkCost (signedDistance (family q c)) (u, false) middle (u, true) := by
  have symmetric (u v : Fin 6) : family q c u v = family q c v u := by
    simp only [family, starSymmetric u v, cornerSymmetric u v]
  obtain ⟨triangle, perimeter⟩ := familyTriangles hc hqc hunit
  have bound := direct_le_walk (signedDistance (family q c))
    (signedTriangle (family q c) symmetric triangle perimeter) (u, false) middle (u, true)
  simpa [signedDistance, family, starDiagonal, cornerDiagonal] using bound

/-- On a walk returning to the same vertex with the opposite side, pay each
unchanged-side edge its distance and each changed-side edge its complement.
The unit lower bound is the corresponding odd-subset cycle inequality. -/
def CycleConsistent (d : Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ u middle, 1 ≤ walkCost (signedDistance d) (u, false) middle (u, true)

/-- The observations come from a common normalized law on the five binary events. -/
def HasJointLaw (d : Fin 6 → Fin 6 → ℝ) : Prop :=
  ∃ weight : (Fin 5 → Bool) → ℝ, (∀ x, 0 ≤ weight x) ∧ (∑ x, weight x) = 1 ∧
    ∀ p ∈ observed, mixture id weight p.1 p.2 = d p.1 p.2

/-- At positive slack, every odd-subset cycle check accepts the displayed family,
although the observed pairs admit no common law. -/
theorem cycle_consistent_without_joint_law {q c : ℝ}
    (hc : 0 < c) (hqc : c ≤ q) (hunit : q + 2 * c ≤ 1) :
    CycleConsistent (family q c) ∧ ¬ HasJointLaw (family q c) := by
  refine ⟨familyCycle hc.le hqc hunit, ?_⟩
  rintro ⟨weight, nonneg, _, fit⟩
  exact familyUnrealizable hc (Fin 5 → Bool) ⟨id, weight, nonneg, fit⟩

end D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
