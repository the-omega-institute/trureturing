/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed lifts of actual cube symmetries for Huang's fixed adjacency operator. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

/-! Flat integration lifts actual cube symmetries to Huang's signed operator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
local notation "flip" => BalancedCriticalSpectrum.flip
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private theorem flip_cons_zero {n : ℕ} (b : Bool) (u : Q n) :
    flip (Fin.cons b u) 0 = Fin.cons (!b) u := by
  funext j
  induction j using Fin.cases <;> simp [BalancedCriticalSpectrum.flip]

private theorem flip_cons_succ {n : ℕ} (b : Bool) (u : Q n) (i : Fin n) :
    flip (Fin.cons b u) i.succ = Fin.cons b (flip u i) := by
  simp only [BalancedCriticalSpectrum.flip, ← Fin.cons_update, Fin.cons_succ]

/-- Integrate a reciprocal unit flat signing by adjoining its head coordinate.
Only the actual covariance construction below consumes this helper. -/
private theorem integrate_flat (n : ℕ) (r : Q n → Fin n → ℝ)
    (hunit : ∀ x i, r x i ^ 2 = 1)
    (hrec : ∀ x i, r (flip x i) i = r x i)
    (hflat : ∀ x i j, i ≠ j →
      r x i * r (flip x i) j = r x j * r (flip x j) i) :
    ∃ theta : Q n → ℝ, (∀ x, theta x ^ 2 = 1) ∧
      ∀ x i, r x i = theta x * theta (flip x i) := by
  induction n with
  | zero =>
      exact ⟨fun _ => 1, by simp, fun _ i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨t, ht, he⟩ := ih (fun u i => r (Fin.cons true u) i.succ)
        (fun u i => hunit _ _)
        (by
          intro u i
          simpa only [flip_cons_succ] using hrec (Fin.cons true u) i.succ)
        (by
          intro u i j hij
          simpa only [flip_cons_succ] using
            hflat (Fin.cons true u) i.succ j.succ (fun h => hij (Fin.succ_inj.mp h)))
      let theta : Q (n + 1) → ℝ := fun x =>
        if x 0 then t (Fin.tail x)
        else r (Fin.cons true (Fin.tail x)) 0 * t (Fin.tail x)
      have htheta (b : Bool) (u : Q n) :
          theta (Fin.cons b u) = if b then t u else r (Fin.cons true u) 0 * t u := by
        simp [theta]
      refine ⟨theta, ?_, ?_⟩
      · intro x
        rw [← Fin.cons_self_tail x, htheta]
        cases x 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [mul_pow, hunit, ht, mul_one]
        · exact ht _
      · intro x i
        rw [← Fin.cons_self_tail x]
        generalize x 0 = b
        generalize Fin.tail x = u
        induction i using Fin.cases with
        | zero =>
            rw [flip_cons_zero, htheta, htheta]
            have hr := hrec (Fin.cons true u) 0
            simp only [flip_cons_zero, Bool.not_true] at hr
            cases b <;> simp only [Bool.not_false, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte]
            · rw [hr]
              calc
                r (Fin.cons true u) 0 = r (Fin.cons true u) 0 * t u ^ 2 := by
                  rw [ht, mul_one]
                _ = _ := by ring
            · calc
                r (Fin.cons true u) 0 = r (Fin.cons true u) 0 * t u ^ 2 := by
                  rw [ht, mul_one]
                _ = _ := by ring
        | succ i =>
            rw [flip_cons_succ, htheta, htheta]
            cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
            · have hf := hflat (Fin.cons true u) 0 i.succ (Fin.succ_ne_zero i).symm
              simp only [flip_cons_zero, Bool.not_true, flip_cons_succ] at hf
              calc
                r (Fin.cons false u) i.succ =
                    r (Fin.cons true u) 0 *
                      (r (Fin.cons true u) 0 * r (Fin.cons false u) i.succ) := by
                  rw [← mul_assoc, ← pow_two, hunit, one_mul]
                _ = r (Fin.cons true u) 0 *
                    (r (Fin.cons true u) i.succ * r (Fin.cons true (flip u i)) 0) := by
                  rw [hf]
                _ = _ := by rw [he]; ring
            · exact he u i

private abbrev edge {n : ℕ} (x : Q n) (i : Fin n) : ℝ :=
  huangMatrix n x (flip x i)

private theorem edge_sq {n : ℕ} (x : Q n) (i : Fin n) : edge x i ^ 2 = 1 :=
  SupportedEigenSaturation.matrix_sq_of_adj (BalancedCriticalSpectrum.flip_adj x i)

private theorem edge_reciprocal {n : ℕ} (x : Q n) (i : Fin n) :
    edge (flip x i) i = edge x i := by
  simp only [edge, BalancedCriticalSpectrum.flip_flip]
  exact huangMatrix_symmetric _ _

private theorem edge_curvature {n : ℕ} (x : Q n) {i j : Fin n} (hij : i ≠ j) :
    edge x i * edge (flip x i) j = -(edge x j * edge (flip x j) i) := by
  simpa only [BalancedCriticalSpectrum.gamma_apply, Pi.neg_apply, mul_one] using
    congrFun (BalancedCubeGirth.gamma_anticommute hij (fun _ => (1 : ℝ))) x

private theorem exists_edge_gauge {n : ℕ} (g : Q n ≃ Q n) (pi : Fin n ≃ Fin n)
    (hg : ∀ x i, g (flip x i) = flip (g x) (pi i)) :
    ∃ theta : Q n → ℝ, (∀ x, theta x ^ 2 = 1) ∧
      ∀ x i, edge (g x) (pi i) = theta x * edge x i * theta (flip x i) := by
  let r : Q n → Fin n → ℝ := fun x i => edge x i * edge (g x) (pi i)
  have hunit : ∀ x i, r x i ^ 2 = 1 := by
    intro x i
    dsimp only [r]
    rw [mul_pow, edge_sq, edge_sq, mul_one]
  have hrec : ∀ x i, r (flip x i) i = r x i := by
    intro x i
    dsimp only [r]
    rw [hg, edge_reciprocal, edge_reciprocal]
  have hflat : ∀ x i j, i ≠ j →
      r x i * r (flip x i) j = r x j * r (flip x j) i := by
    intro x i j hij
    dsimp only [r]
    rw [hg, hg]
    calc
      (edge x i * edge (g x) (pi i)) *
          (edge (flip x i) j * edge (flip (g x) (pi i)) (pi j)) =
        (edge x i * edge (flip x i) j) *
          (edge (g x) (pi i) * edge (flip (g x) (pi i)) (pi j)) := by ring
      _ = _ := by
        rw [edge_curvature x hij,
          edge_curvature (g x) (fun h => hij (pi.injective h))]
        ring
  obtain ⟨theta, ht, he⟩ := integrate_flat n r hunit hrec hflat
  refine ⟨theta, ht, fun x i => ?_⟩
  have h := he x i
  change edge x i * edge (g x) (pi i) = theta x * theta (flip x i) at h
  calc
    edge (g x) (pi i) = edge x i * (edge x i * edge (g x) (pi i)) := by
      rw [← mul_assoc, ← pow_two, edge_sq, one_mul]
    _ = _ := by rw [h]; ring

/-- Reindex the actual nonzero matrix row by the distinct coordinate neighbors. -/
private theorem matrix_row {n : ℕ} (z : Q n → ℝ) (x : Q n) :
    (huangMatrix n).mulVec z x = ∑ i : Fin n, edge x i * z (flip x i) := by
  classical
  change (∑ y, huangMatrix n x y * z y) = _
  calc
    (∑ y, huangMatrix n x y * z y) =
        ∑ y ∈ (hypercube n).neighborFinset x, huangMatrix n x y * z y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hn : ¬ (hypercube n).Adj x y := fun h =>
        hy (by simpa only [SimpleGraph.mem_neighborFinset] using h)
      rw [SupportedEigenSaturation.matrix_eq_zero_of_not_adj hn, zero_mul]
    _ = _ := by
      symm
      apply Finset.sum_bij (fun i _ => flip x i)
      · intro i _
        simpa only [SimpleGraph.mem_neighborFinset] using BalancedCriticalSpectrum.flip_adj x i
      · intro i _ j _ h
        change Function.update x i (!x i) = Function.update x j (!x j) at h
        rcases Function.update_eq_update_iff.mp h with h | h
        · exact h.1
        · have hbad := h.1
          cases hxi : x i <;> simp [hxi] at hbad
      · intro y hy
        obtain ⟨i, hi⟩ := adjacent_exists_flip
          (by simpa only [SimpleGraph.mem_neighborFinset] using hy)
        exact ⟨i, Finset.mem_univ _, hi.symm⟩
      · intro i _
        rfl

/-- Every actual cube equivalence intertwining flips by a coordinate permutation
has a sign gauge, and its signed pushforward commutes with the full Huang matrix.
The gauge is evaluated in the source coordinates. Dimension zero is included. -/
theorem exists_signed_covariance {n : ℕ} (g : Q n ≃ Q n) (pi : Fin n ≃ Fin n)
    (hg : ∀ x i, g (flip x i) = flip (g x) (pi i)) :
    ∃ theta : Q n → ℝ,
      (∀ x, theta x = 1 ∨ theta x = -1) ∧
      (∀ x i, huangMatrix n (g x) (g (flip x i)) =
        theta x * huangMatrix n x (flip x i) * theta (flip x i)) ∧
      ∀ z : Q n → ℝ,
        (huangMatrix n).mulVec (fun y => theta (g.symm y) * z (g.symm y)) =
          fun y => theta (g.symm y) * ((huangMatrix n).mulVec z) (g.symm y) := by
  obtain ⟨theta, ht, he⟩ := exists_edge_gauge g pi hg
  refine ⟨theta, ?_, ?_, ?_⟩
  · intro x
    have h := ht x
    rcases (sq_eq_one_iff).mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro x i
    rw [hg]
    exact he x i
  · intro z
    funext y
    obtain ⟨x, rfl⟩ := g.surjective y
    simp only [Equiv.symm_apply_apply]
    rw [matrix_row, matrix_row, Finset.mul_sum]
    calc
      (∑ j : Fin n, edge (g x) j *
          (theta (g.symm (flip (g x) j)) * z (g.symm (flip (g x) j)))) =
        ∑ i : Fin n, edge (g x) (pi i) *
          (theta (g.symm (flip (g x) (pi i))) * z (g.symm (flip (g x) (pi i)))) :=
        (Equiv.sum_comp pi _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hg, Equiv.symm_apply_apply, he]
        calc
          (theta x * edge x i * theta (flip x i)) *
              (theta (flip x i) * z (flip x i)) =
            theta x * (edge x i * z (flip x i)) * theta (flip x i) ^ 2 := by ring
          _ = _ := by rw [ht, mul_one]

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
