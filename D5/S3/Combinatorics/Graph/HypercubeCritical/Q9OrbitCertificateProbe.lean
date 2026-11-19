module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Logic.Equiv.Basic

/-! Finite group averaging for the lifted linear inequalities on Q9 supports. -/

open scoped BigOperators
open Finset

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private lemma orbit_sum_invariant {G V : Type*} [Group G] [Fintype G] [MulAction G V]
    (x : V → ℤ) (g : G) (v : V) :
    (∑ h : G, x (h • (g • v))) = ∑ h : G, x (h • v) := by
  simp only [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight g) (fun h : G => x (h • v))

/-- A lifted vector that satisfies every transported row supplies integer
orbit totals. These have a common denominator equal to the group order. -/
public theorem exists_orbit_totals {G V R : Type*} [Group G] [Fintype G] [MulAction G V]
    [Fintype V] (a : R → V → ℤ) (b : R → ℤ) (x : V → ℤ)
    (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1)
    (hrows : ∀ (g : G) (r : R), (∑ v : V, a r v * x (g • v)) ≤ b r) :
    ∃ y : V → ℤ, (∀ v, 0 ≤ y v ∧ y v ≤ Fintype.card G) ∧
      (∀ (g : G) v, y (g • v) = y v) ∧
      ∀ r, (∑ v : V, a r v * y v) ≤ Fintype.card G * b r := by
  let y (v : V) : ℤ := ∑ g : G, x (g • v)
  refine ⟨y, ?_, orbit_sum_invariant x, ?_⟩
  · intro v
    refine ⟨sum_nonneg fun g _ => (hx (g • v)).1, ?_⟩
    have h := sum_le_sum (s := (univ : Finset G)) (fun g _ => (hx (g • v)).2)
    simpa [y] using h
  · intro r
    have h := sum_le_sum (s := (univ : Finset G)) (fun g _ => hrows g r)
    simpa only [y, mul_sum, sum_comm (s := (univ : Finset V)) (t := (univ : Finset G)),
      sum_const, card_univ, nsmul_eq_mul] using h

/-- A positive integer multiple of the unit box is incompatible with a
certificate whose combined row bound is below the minimum on the unit box. -/
public theorem no_scaled_unit_box_solution {V R : Type*} [Fintype V] [Fintype R]
    (a : R → V → ℤ) (b : R → ℤ) (weights : R → ℤ)
    (hw : ∀ r, 0 ≤ weights r)
    (hgap : (∑ r, weights r * b r) < ∑ v, min 0 (∑ r, weights r * a r v))
    (d : ℤ) (hd : 0 < d) (y : V → ℤ) (hy : ∀ v, 0 ≤ y v ∧ y v ≤ d) :
    ¬ ∀ r, (∑ v, a r v * y v) ≤ d * b r := by
  intro hrows
  let c (v : V) : ℤ := ∑ r, weights r * a r v
  have hScale : (∑ v, c v * y v) ≤ d * ∑ r, weights r * b r := by
    have h := sum_le_sum (s := (univ : Finset R))
      (fun r _ => mul_le_mul_of_nonneg_left (hrows r) (hw r))
    simp only [mul_sum, ← mul_assoc] at h
    simpa only [c, sum_mul, mul_sum, mul_comm d (weights _), ← mul_assoc,
      sum_comm (s := (univ : Finset V)) (t := (univ : Finset R))] using h
  have hMin : d * (∑ v, min 0 (c v)) ≤ ∑ v, c v * y v := by
    rw [mul_sum]
    apply sum_le_sum
    intro v _
    by_cases h : 0 ≤ c v
    · simpa [min_eq_left h] using mul_nonneg h (hy v).1
    · rw [min_eq_right (le_of_not_ge h), mul_comm d]
      exact mul_le_mul_of_nonpos_left (hy v).2 (le_of_not_ge h)
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hgap hd)) (hMin.trans hScale)

#print axioms exists_orbit_totals
#print axioms no_scaled_unit_box_solution

/-- Aggregate the coefficients in each orbit before checking the integer
certificate. Orbit indices may be supplied by any convenient enumeration. -/
public theorem no_orbit_certificate_solution {G V W R : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [Fintype W] [Fintype R] [DecidableEq W]
    (orbit : V → W) (representative : W → V)
    (hrep : ∀ v, ∃ g : G, g • representative (orbit v) = v)
    (a : R → V → ℤ) (b : R → ℤ) (weights : R → ℤ)
    (hw : ∀ r, 0 ≤ weights r)
    (hgap : (∑ r, weights r * b r) <
      ∑ w, min 0 (∑ r, weights r * ∑ v, if orbit v = w then a r v else 0))
    (x : V → ℤ) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1) :
    ¬ ∀ (g : G) r, (∑ v, a r v * x (g • v)) ≤ b r := by
  intro hrows
  obtain ⟨y, hy, hinv, hrow⟩ := exists_orbit_totals a b x hx hrows
  have hcard : 0 < (Fintype.card G : ℤ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  apply no_scaled_unit_box_solution
    (fun r w => ∑ v, if orbit v = w then a r v else 0)
    b weights hw hgap _ hcard (y ∘ representative) (fun w => hy (representative w))
  intro r
  have he (v : V) : y (representative (orbit v)) = y v := by
    obtain ⟨g, hg⟩ := hrep v
    simpa only [hg] using (hinv g (representative (orbit v))).symm
  calc
    _ = ∑ v, a r v * y v := by
      simp_rw [Function.comp_apply, sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      simp only [Finset.sum_ite_eq, mem_univ, if_true, he]
    _ ≤ _ := hrow r

#print axioms no_orbit_certificate_solution

/-- Equal counts of every coordinate color allow a permutation matching the
colored coordinates. For a lifted vertex pair, use the color consisting of
the deficit and the two bits. -/
public theorem exists_perm_of_coordinate_color_counts {I A : Type*}
    [Fintype I] [DecidableEq A] (f g : I → A)
    (h : ∀ a, (univ.filter (fun i => f i = a)).card =
      (univ.filter (fun i => g i = a)).card) :
    ∃ p : Equiv.Perm I, ∀ i, g (p i) = f i := by
  let e (a : A) : {i // f i = a} ≃ {i // g i = a} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact h a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

#print axioms exists_perm_of_coordinate_color_counts

/-- For two ordered pairs of cube vertices, the counts of the joint bit
patterns within each deficit class determine their simultaneous orbit. -/
public theorem exists_deficit_perm_of_joint_bit_counts {I : Type*} [Fintype I]
    (r : I → ℤ) (x y u v : I → Bool)
    (h : ∀ d a b, (univ.filter (fun i => r i = d ∧ x i = a ∧ y i = b)).card =
      (univ.filter (fun i => r i = d ∧ u i = a ∧ v i = b)).card) :
    ∃ p : Equiv.Perm I, ∀ i, r (p i) = r i ∧ u (p i) = x i ∧ v (p i) = y i := by
  obtain ⟨p, hp⟩ := exists_perm_of_coordinate_color_counts
    (fun i => (r i, x i, y i)) (fun i => (r i, u i, v i)) (by
      rintro ⟨d, a, b⟩
      simpa only [Prod.mk.injEq] using h d a b)
  exact ⟨p, fun i => by simpa only [Prod.mk.injEq] using hp i⟩

#print axioms exists_deficit_perm_of_joint_bit_counts

end D5.S3.Combinatorics.Graph.HypercubeCritical
