/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryQuadraticMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset]
   utility: none
   digest: Quadratic moments of binary cube adjacency fixed words satisfy the triangle equations. -/

module

public import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Orthogonality and quadratic moments for fixed words of unsigned binary cube
adjacency, as used in the nine-cube case of Hong, Wu and Xia's Problem 2. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments

open BinaryKernelCoordinateMoment Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

/-- Unsigned binary cube adjacency is self-adjoint for the sum of pointwise
products. Each singleton flip is an involution of the vertex set. -/
private theorem adjacency_self_adjoint (f g : Finset (Fin n) → ZMod 2) :
    (∑ x, adjacency f x * g x) = ∑ x, f x * adjacency g x := by
  calc
    (∑ x, adjacency f x * g x) = ∑ i : Fin n, ∑ x, f (x ∆ {i}) * g x := by
      simp only [adjacency, sum_mul]
      exact sum_comm
    _ = ∑ i : Fin n, ∑ x, f x * g (x ∆ {i}) := by
      apply sum_congr rfl
      intro i _
      let flip := Function.Involutive.toPerm (fun x : Finset (Fin n) => x ∆ {i})
        (fun x => symmDiff_symmDiff_cancel_right {i} x)
      apply Fintype.sum_equiv flip
      intro x
      change f (x ∆ {i}) * g x = f (x ∆ {i}) * g ((x ∆ {i}) ∆ {i})
      rw [symmDiff_symmDiff_cancel_right]
    _ = ∑ x, f x * adjacency g x := by
      simp only [adjacency, mul_sum]
      exact sum_comm

/-- Any two fixed words of binary cube adjacency have zero pairing. -/
private theorem sum_mul_eq_zero_of_adjacency_eq_self {q f : Finset (Fin n) → ZMod 2}
    (hq : adjacency q = q) (hf : adjacency f = f) :
    (∑ x, q x * f x) = 0 := by
  by_cases hn : n = 0
  · subst n
    have hf₀ : f = 0 := hf.symm.trans (by funext x; simp [adjacency])
    simp [hf₀]
  · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let g := coordinateContraction i f
    have h : adjacency g + g = f := by
      simpa only [hf, g] using adjacency_coordinateContraction i f
    calc
      (∑ x, q x * f x) = ∑ x, q x * (adjacency g x + g x) := by
        exact sum_congr rfl fun x _ => congrArg (q x * ·) (congrFun h x).symm
      _ = (∑ x, q x * adjacency g x) + ∑ x, q x * g x := by
        simp only [mul_add, sum_add_distrib]
      _ = 0 := by rw [← adjacency_self_adjoint q g, hq, ZModModule.add_self]

private theorem adjacency_coordinate_pair (hn : Odd n) {i j : Fin n} (hij : i ≠ j)
    (x : Finset (Fin n)) :
    adjacency (fun y => coordinateBit i y * coordinateBit j y) x =
      coordinateBit i x * coordinateBit j x + (coordinateBit i x + coordinateBit j x) := by
  unfold adjacency
  calc
    _ = ∑ l : Fin n, (coordinateBit i x * coordinateBit j x +
          (if l = j then coordinateBit i x else 0) +
          (if l = i then coordinateBit j x else 0)) := by
      apply sum_congr rfl
      intro l _
      change coordinateBit i (x ∆ {l}) * coordinateBit j (x ∆ {l}) = _
      rw [coordinateBit_toggle, coordinateBit_toggle]
      by_cases hli : l = i
      · subst l
        simp [hij, add_mul]
      · by_cases hlj : l = j
        · subst l
          simp [Ne.symm hij, mul_add]
        · simp [hli, hlj]
    _ = _ := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        hn.natCast_zmod_two, one_mul, sum_ite_eq', mem_univ, ite_true, add_assoc]

private theorem adjacency_triangle_eq_self (hn : Odd n) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    let q := fun x => coordinateBit i x * coordinateBit j x +
      coordinateBit j x * coordinateBit k x + coordinateBit k x * coordinateBit i x
    adjacency q = q := by
  dsimp only
  funext x
  simp only [adjacency, sum_add_distrib]
  change adjacency (fun y => coordinateBit i y * coordinateBit j y) x +
      adjacency (fun y => coordinateBit j y * coordinateBit k y) x +
      adjacency (fun y => coordinateBit k y * coordinateBit i y) x = _
  rw [adjacency_coordinate_pair hn hij, adjacency_coordinate_pair hn hjk,
    adjacency_coordinate_pair hn hki]
  calc
    _ = (coordinateBit i x * coordinateBit j x + coordinateBit j x * coordinateBit k x +
        coordinateBit k x * coordinateBit i x) +
        ((coordinateBit i x + coordinateBit i x) + (coordinateBit j x + coordinateBit j x) +
          (coordinateBit k x + coordinateBit k x)) := by ac_rfl
    _ = _ := by simp only [ZModModule.add_self, add_zero]

/-- The second moment across two different coordinates, with zero diagonal. -/
def pairMoment (f : Finset (Fin n) → ZMod 2) (i j : Fin n) : ZMod 2 :=
  if i = j then 0 else ∑ x, coordinateBit i x * coordinateBit j x * f x

private theorem pairMoment_comm (f : Finset (Fin n) → ZMod 2) (i j : Fin n) :
    pairMoment f i j = pairMoment f j i := by
  simp only [pairMoment, eq_comm (a := i) (b := j),
    mul_comm (coordinateBit i _) (coordinateBit j _)]

/-- In odd dimension the three pair moments on distinct coordinates sum to zero. -/
private theorem pairMoment_triangle (hn : Odd n) {f : Finset (Fin n) → ZMod 2}
    (hf : adjacency f = f)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    pairMoment f i j + pairMoment f j k + pairMoment f k i = 0 := by
  simpa only [pairMoment, ite_eq_right hij, ite_eq_right hjk, ite_eq_right hki,
    add_mul, sum_add_distrib] using
    sum_mul_eq_zero_of_adjacency_eq_self (adjacency_triangle_eq_self hn hij hjk hki) hf

/-- The pair moments of a fixed word on an odd-dimensional cube are sums of one
potential per endpoint. This includes the zero diagonal. -/
theorem exists_pairMoment_eq_add (hn : Odd n) {f : Finset (Fin n) → ZMod 2}
    (hf : adjacency f = f) :
    ∃ t : Fin n → ZMod 2, ∀ i j, pairMoment f i j = t i + t j := by
  let a : Fin n := ⟨0, hn.pos⟩
  refine ⟨fun i => pairMoment f i a, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [pairMoment, ite_true, ZModModule.add_self]
  by_cases hia : i = a
  · subst i
    rw [pairMoment_comm f a j]
    simp only [pairMoment, ite_true, zero_add]
  by_cases hja : j = a
  · subst j
    simp only [pairMoment, ite_true, add_zero]
  have h := pairMoment_triangle hn hf hij hja (Ne.symm hia)
  rw [pairMoment_comm f a i, add_assoc, add_comm (pairMoment f j a)] at h
  exact sub_eq_zero.mp (by simpa only [ZModModule.sub_eq_add] using h)

#print axioms exists_pairMoment_eq_add

end D5.S3.Combinatorics.Graph.Hypercube.BinaryQuadraticMoments
