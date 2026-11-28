/- GID: D5/S3/Combinatorics/Graph/GroupWordMetric
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The word metric of a symmetric conjugation-invariant generating set. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Group

compile_only_with_mathlib

/-!
Omega original.

The word metric of a symmetric conjugation-invariant generating set.
-/

namespace GroupWordMetric

variable {H : Type*} [Group H] {U : Set H}

/-- A word of length at most the specified budget. -/
def Fits (U : Set H) (n : ℕ) (x : H) : Prop :=
  ∃ l : List H, (∀ y ∈ l, y ∈ U) ∧ l.length ≤ n ∧ l.prod = x

/-- Every group element is represented by a word in the generating set. -/
def Generates (U : Set H) : Prop := ∀ x : H, ∃ n, Fits U n x

theorem Fits.mono {n m : ℕ} {x : H} (h : Fits U n x) (hn : n ≤ m) : Fits U m x := by
  obtain ⟨l, hu, hl, hp⟩ := h
  exact ⟨l, hu, hl.trans hn, hp⟩

theorem Fits.one : Fits U 0 (1 : H) := ⟨[], by simp, by simp, rfl⟩

theorem Fits.of_mem {x : H} (hx : x ∈ U) : Fits U 1 x :=
  ⟨[x], by simpa, by simp, by simp⟩

theorem Fits.mul {m n : ℕ} {x y : H} (hx : Fits U m x) (hy : Fits U n y) :
    Fits U (m + n) (x * y) := by
  obtain ⟨l, hlu, hll, hlp⟩ := hx
  obtain ⟨q, hqu, hql, hqp⟩ := hy
  refine ⟨l ++ q, ?_, ?_, by simp [hlp, hqp]⟩
  · intro z hz
    exact (List.mem_append.mp hz).elim (hlu z) (hqu z)
  · rw [List.length_append]
    exact add_le_add hll hql

theorem Fits.inv (hu : ∀ u ∈ U, u⁻¹ ∈ U) {n : ℕ} {x : H} (hx : Fits U n x) :
    Fits U n x⁻¹ := by
  obtain ⟨l, hmem, hl, rfl⟩ := hx
  have hinv (l : List H) : ((l.reverse.map fun a => a⁻¹).prod) = l.prod⁻¹ := by
    induction l with
    | nil => simp
    | cons _ _ ih => simp only [List.reverse_cons, List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ih, mul_inv_rev]
  refine ⟨l.reverse.map (fun a => a⁻¹), ?_, by simpa, hinv l⟩
  rintro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact hu y (hmem y (List.mem_reverse.mp hy))

theorem Fits.conj (hu : ∀ a, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    {n : ℕ} {x : H} (hx : Fits U n x) (a : H) :
    Fits U n (a * x * a⁻¹) := by
  obtain ⟨l, hmem, hl, rfl⟩ := hx
  have he (l : List H) : (l.map fun y => a * y * a⁻¹).prod = a * l.prod * a⁻¹ := by
    induction l with
    | nil => simp
    | cons _ _ ih => simp only [List.map_cons, List.prod_cons, ih]; group
  refine ⟨l.map (fun y => a * y * a⁻¹), ?_, by simpa, he l⟩
  rintro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  exact hu a y (hmem y hy)

/-- The minimum length among all representative words. -/
noncomputable def length (gU : Generates U) (x : H) : ℕ := by
  classical
  exact Nat.find (gU x)

theorem length_spec (gU : Generates U) (x : H) : Fits U (length gU x) x := by
  classical
  exact Nat.find_spec (gU x)

theorem length_le_iff (gU : Generates U) (n : ℕ) (x : H) : length gU x ≤ n ↔ Fits U n x := by
  classical
  exact ⟨fun h => (length_spec gU x).mono h, fun h => Nat.find_min' (gU x) h⟩

theorem length_one (gU : Generates U) : length gU (1 : H) = 0 :=
  Nat.eq_zero_of_le_zero ((length_le_iff gU 0 1).2 Fits.one)

theorem eq_one_of_length_zero (gU : Generates U) {x : H} (hx : length gU x = 0) : x = 1 := by
  obtain ⟨l, _, hl, hp⟩ := (length_le_iff gU 0 x).1 hx.le
  have he : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
  simpa [he] using hp.symm

theorem length_inv (gU : Generates U) (hu : ∀ u ∈ U, u⁻¹ ∈ U) (x : H) :
    length gU x⁻¹ = length gU x := by
  apply le_antisymm
  · exact (length_le_iff gU _ _).2 ((length_spec gU x).inv hu)
  · apply (length_le_iff gU _ _).2
    simpa only [inv_inv] using (length_spec gU x⁻¹).inv hu

theorem length_mul_le (gU : Generates U) (x y : H) :
    length gU (x * y) ≤ length gU x + length gU y :=
  (length_le_iff gU _ _).2 ((length_spec gU x).mul (length_spec gU y))

theorem length_conj (gU : Generates U) (hu : ∀ a, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (a x : H) : length gU (a * x * a⁻¹) = length gU x := by
  apply le_antisymm
  · exact (length_le_iff gU _ _).2 ((length_spec gU x).conj hu a)
  · apply (length_le_iff gU _ _).2
    have h := (length_spec gU (a * x * a⁻¹)).conj hu a⁻¹
    rwa [show a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x by group] at h

/-- The metric given by minimum word length of the residual between two points. -/
@[instance_reducible]
noncomputable def metric (gU : Generates U) (hu : ∀ u ∈ U, u⁻¹ ∈ U) : MetricSpace H where
  dist x y := length gU (x⁻¹ * y)
  dist_self x := by rw [inv_mul_cancel, length_one, Nat.cast_zero]
  dist_comm x y := by
    rw [← length_inv gU hu (y⁻¹ * x)]
    simp
  dist_triangle x y z := by
    have h := length_mul_le gU (x⁻¹ * y) (y⁻¹ * z)
    rw [show (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z by group] at h
    exact_mod_cast h
  eq_of_dist_eq_zero := by
    intro x y h
    have hz : length gU (x⁻¹ * y) = 0 := by exact_mod_cast h
    have he := eq_one_of_length_zero gU hz
    rwa [inv_mul_eq_one] at he

theorem left_isometric (gU : Generates U) (hu : ∀ u ∈ U, u⁻¹ ∈ U) :
    let := metric gU hu
    IsIsometricSMul H H := by
  let := metric gU hu
  constructor
  intro a
  apply Isometry.of_dist_eq
  intro x y
  change (length gU ((a * x)⁻¹ * (a * y)) : ℝ) = length gU (x⁻¹ * y)
  rw [show (a * x)⁻¹ * (a * y) = x⁻¹ * y by group]

theorem right_isometric (gU : Generates U) (hu : ∀ u ∈ U, u⁻¹ ∈ U)
    (hn : ∀ a, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    let := metric gU hu
    IsIsometricSMul Hᵐᵒᵖ H := by
  let := metric gU hu
  constructor
  intro a
  apply Isometry.of_dist_eq
  intro x y
  let b := MulOpposite.unop a
  change (length gU ((x * b)⁻¹ * (y * b)) : ℝ) = length gU (x⁻¹ * y)
  rw [show (x * b)⁻¹ * (y * b) = b⁻¹ * (x⁻¹ * y) * (b⁻¹)⁻¹ by group,
    length_conj gU hn]

end GroupWordMetric
