/- GID: D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/PosteriorMomentDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact squared distance from five-cycle moments to the fixed-prior finite posterior family. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The five-cycle edge bound specializes Motzkin–Straus, §1, Theorem 1.
The exact distance and attaining mixture are repository-derived.

proof_shape: content
admission_basis: escape-witness
The two cyclic orbits in orbit_attains realize the exact projected matrix
and its uniform prior throughout the closed interval.

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31536
-/

open scoped BigOperators

namespace D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentDistance

noncomputable section

private abbrev Moment := Matrix (Fin 5) (Fin 5) ℝ

private def edge (i j : Fin 5) : Prop := j = i + 1 ∨ i = j + 1

private instance (i j : Fin 5) : Decidable (edge i j) := by
  unfold edge
  infer_instance

/-- The input with a prescribed row sum and a common cycle edge entry. -/
def cycleMoment (t : ℝ) : Moment :=
  fun i j => if i = j then 1 / 5 - 2 * t else if edge i j then t else 0

/-- The nearest finite posterior moment in the stated parameter range. -/
def projectedMoment (t : ℝ) : Moment :=
  fun i j =>
    if i = j then 1 / 10 - (20 * t - 1) / 15
    else if edge i j then 1 / 20 else (20 * t - 1) / 30

/-- The sum of the squares of differences over all ordered entries. -/
def squaredDistance (X Y : Moment) : ℝ :=
  ∑ i, ∑ j, (X i j - Y i j) ^ 2

/-- Finite posterior mixtures on five targets with the exact uniform barycenter. -/
def IsUniformPosteriorMoment (X : Moment) : Prop :=
  ∃ (m : ℕ) (mass : Fin m → ℝ) (p : Fin m → Fin 5 → ℝ),
    (∀ a, 0 ≤ mass a) ∧ (∑ a, mass a) = 1 ∧
    (∀ a i, 0 ≤ p a i) ∧ (∀ a, (∑ i, p a i) = 1) ∧
    (∀ i, ∑ a, mass a * p a i = 1 / 5) ∧
    ∀ i j, X i j = ∑ a, mass a * p a i * p a j

private def normal : Moment := fun i j => if edge i j then -(6 / 5) else 4 / 5

private def pairing (X Y : Moment) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

private theorem edge_bound (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 + x 4 * x 0 ≤
      (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 / 4 := by
  rcases le_total (x 3) (x 4) with h | h
  · have hgap := add_nonneg (mul_nonneg (hx 2) (sub_nonneg.mpr h))
      (mul_nonneg (hx 1) (hx 3))
    nlinarith only [hgap, sq_nonneg (x 0 + x 2 + x 3 - (x 1 + x 4))]
  · have hgap := add_nonneg (mul_nonneg (hx 0) (sub_nonneg.mpr h))
      (mul_nonneg (hx 1) (hx 4))
    nlinarith only [hgap, sq_nonneg (x 2 + x 0 + x 4 - (x 1 + x 3))]

private theorem normal_on_posterior (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hxsum : ∑ i, x i = 1) :
    -(1 / 5) ≤ pairing normal (fun i j => x i * x j) := by
  have h := edge_bound x hx
  have hs : (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 = 1 := by
    norm_num [Fin.sum_univ_succ] at hxsum
    nlinarith only [hxsum, congrArg (fun z : ℝ => z ^ 2) hxsum]
  rw [hs] at h
  have hcalc : pairing normal (fun i j => x i * x j) =
      (4 / 5) * (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 -
        4 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 + x 4 * x 0) := by
    norm_num [pairing, normal, edge, Fin.sum_univ_succ]
    ring
  rw [hcalc, hs]
  linarith only [h]

private theorem normal_on_moment {X : Moment} (hX : IsUniformPosteriorMoment X) :
    -(1 / 5) ≤ pairing normal X := by
  obtain ⟨m, mass, p, hm, hmass, hp, hpsum, _, hX⟩ := hX
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) fun a _ =>
    mul_le_mul_of_nonneg_left (normal_on_posterior (p a) (hp a) (hpsum a)) (hm a)
  rw [← Finset.sum_mul, hmass, one_mul] at h
  have hlinear : pairing normal X =
      ∑ a, mass a * pairing normal (fun i j => p a i * p a j) := by
    simp only [pairing, hX, Finset.mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm (t := (Finset.univ : Finset (Fin m)))]
    conv_lhs =>
      rw [Finset.sum_comm (t := (Finset.univ : Finset (Fin m)))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlinear]
  exact h

private abbrev Orbit := Fin 5 ⊕ Fin 5

private def edgePosterior (a i : Fin 5) : ℝ :=
  if i = a ∨ i = a + 1 then 1 / 2 else 0

private def pathPosterior (a i : Fin 5) : ℝ :=
  if i = a + 1 then 1 / 2 else if i = a ∨ i = a + 2 then 1 / 4 else 0

private def orbitPosterior : Orbit → Fin 5 → ℝ :=
  Sum.elim edgePosterior pathPosterior

private theorem orbit_attains (t : ℝ) (ht : 1 / 20 ≤ t) (hu : t ≤ 11 / 160) :
    IsUniformPosteriorMoment (projectedMoment t) := by
  let w := (8 / 3) * (20 * t - 1)
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hw' : w ≤ 1 := by dsimp [w]; linarith
  let m : Orbit → ℝ := Sum.elim (fun _ => (1 - w) / 5) (fun _ => w / 5)
  let e : Fin 10 ≃ Orbit := (finSumFinEquiv (m := 5) (n := 5)).symm
  refine ⟨10, m ∘ e, orbitPosterior ∘ e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change 0 ≤ m (e a)
    cases e a <;> dsimp [m] <;> linarith only [hw, hw']
  · change (∑ a, m (e a)) = 1
    rw [Equiv.sum_comp e m, Fintype.sum_sum_type]
    simp [m]
    ring
  · intro a i
    change 0 ≤ orbitPosterior (e a) i
    rcases e a with b | b <;> simp only [orbitPosterior, Sum.elim_inl, Sum.elim_inr]
    · unfold edgePosterior
      split <;> norm_num
    · unfold pathPosterior
      split <;> try norm_num
      split <;> norm_num
  · intro a
    change (∑ i, orbitPosterior (e a) i) = 1
    rcases e a with b | b <;> fin_cases b <;>
      norm_num [orbitPosterior, edgePosterior, pathPosterior, Fin.sum_univ_succ]
  · intro i
    change (∑ a, m (e a) * orbitPosterior (e a) i) = 1 / 5
    rw [Equiv.sum_comp e (fun a => m a * orbitPosterior a i), Fintype.sum_sum_type]
    fin_cases i <;>
      norm_num [orbitPosterior, edgePosterior, pathPosterior, m, Fin.sum_univ_succ] <;> ring
  · intro i j
    change projectedMoment t i j = ∑ a, m (e a) * orbitPosterior (e a) i * orbitPosterior (e a) j
    rw [Equiv.sum_comp e (fun a => m a * orbitPosterior a i * orbitPosterior a j),
      Fintype.sum_sum_type]
    fin_cases i <;> fin_cases j <;>
      norm_num [projectedMoment, edge, orbitPosterior, edgePosterior, pathPosterior,
        m, w, Fin.sum_univ_succ] <;> ring

private theorem normal_projection (t : ℝ) :
    pairing normal (projectedMoment t) = -(1 / 5) := by
  norm_num [pairing, normal, projectedMoment, edge, Fin.sum_univ_succ]
  ring

private theorem projection_difference (t : ℝ) (i j : Fin 5) :
    projectedMoment t i j - cycleMoment t i j = (20 * t - 1) / 24 * normal i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [projectedMoment, cycleMoment, normal, edge] <;> ring

private theorem normal_squared : (∑ i, ∑ j, (normal i j) ^ 2) = 24 := by
  norm_num [normal, edge, Fin.sum_univ_succ]

private theorem energy_identity (X : Moment) (t : ℝ) :
    squaredDistance X (cycleMoment t) =
      squaredDistance X (projectedMoment t) + (20 * t - 1) ^ 2 / 24 +
        2 * ((20 * t - 1) / 24) * (pairing normal X - pairing normal (projectedMoment t)) := by
  let scale := (20 * t - 1) / 24
  have h (i j : Fin 5) :
      (X i j - cycleMoment t i j) ^ 2 =
        (X i j - projectedMoment t i j) ^ 2 + scale ^ 2 * (normal i j) ^ 2 +
        2 * scale * (normal i j * X i j - normal i j * projectedMoment t i j) := by
    have hsplit : X i j - cycleMoment t i j =
        X i j - projectedMoment t i j + scale * normal i j := by
      have hd := projection_difference t i j
      change projectedMoment t i j - cycleMoment t i j = scale * normal i j at hd
      linarith only [hd]
    rw [hsplit]
    ring
  simp only [squaredDistance, h, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, pairing]
  rw [normal_squared]
  dsimp [scale]
  ring

private theorem squaredDistance_nonneg (X Y : Moment) : 0 ≤ squaredDistance X Y :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (X i j - Y i j)

private theorem squaredDistance_zero {X Y : Moment} (h : squaredDistance X Y = 0) : X = Y := by
  ext i j
  have hi : (∑ b, (X i b - Y i b) ^ 2) = 0 := by
    have hnonneg (a : Fin 5) : 0 ≤ ∑ b, (X a b - Y a b) ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg (X a b - Y a b)
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 5)))
      (fun a _ => hnonneg a) (Finset.mem_univ i)
    exact le_antisymm (hle.trans_eq h) (hnonneg i)
  exact sub_eq_zero.mp ((Finset.sum_sq_eq_zero_iff _ _).mp hi j (Finset.mem_univ j))

/-- The fixed-prior projection attains the lower bound and is the unique minimizer. -/
theorem projected_moment_unique (t : ℝ) (ht : 1 / 20 ≤ t) (hu : t ≤ 11 / 160) :
    IsUniformPosteriorMoment (projectedMoment t) ∧
    squaredDistance (projectedMoment t) (cycleMoment t) = (20 * t - 1) ^ 2 / 24 ∧
    ∀ X, IsUniformPosteriorMoment X →
      (20 * t - 1) ^ 2 / 24 ≤ squaredDistance X (cycleMoment t) ∧
      (squaredDistance X (cycleMoment t) = (20 * t - 1) ^ 2 / 24 → X = projectedMoment t) := by
  refine ⟨orbit_attains t ht hu, ?_, ?_⟩
  · rw [energy_identity]
    simp [squaredDistance]
  · intro X hX
    have hscale : 0 ≤ 2 * ((20 * t - 1) / 24) := by linarith
    have hnormal : 0 ≤ pairing normal X - pairing normal (projectedMoment t) := by
      rw [normal_projection]
      exact sub_nonneg.mpr (normal_on_moment hX)
    have hcross := mul_nonneg hscale hnormal
    have henergy := energy_identity X t
    have hsq := squaredDistance_nonneg X (projectedMoment t)
    refine ⟨by linarith only [henergy, hsq, hcross], ?_⟩
    intro heq
    exact squaredDistance_zero (by linarith only [heq, henergy, hsq, hcross])


end
end D5.S3.ConceptDynamics.ObservationOrder.PosteriorMomentDistance
