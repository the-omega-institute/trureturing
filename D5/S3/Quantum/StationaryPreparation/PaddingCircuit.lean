/- GID: D5/S3/Quantum/StationaryPreparation/PaddingCircuit
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingCircuit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary word-length circuit coefficients for residual padding. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PaddingCircuit

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v w

section
variable {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K]

private def blankMemory (blank : A) : Space K →ₗᵢ[ℂ] Space (A × K) :=
  coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))

theorem circuit_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ n t b, b.card = n → b ≤ a → ∀ (w : Word A n) k,
      circuit (fun _ => U) n t (initialized blank n (r b)) (w, k) =
        if occupation w = b then f k else 0 := by
  have initialized_apply_all {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (n : ℕ) (x : Space K)
      (w : Fin n → A) (k : K) :
      initialized blank n x (w, k) = if w = (fun _ => blank) then x k else 0 := by
    classical
    conv_lhs => rw [basis_expansion x]
    simp only [map_sum, map_smul, initialize_basis]
    by_cases hw : w = (fun _ => blank) <;>
      simp [blankState, basis_apply, Prod.mk.injEq, hw]
  have blank_memory_apply {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (x : Space K) (i : A) (k : K) :
      blankMemory blank x (i, k) = if i = blank then x k else 0 := by
    by_cases hi : i = blank
    · subst i
      simpa [blankMemory, blankInjection] using
        (coordinate_embedding_apply (blankInjection blank (Function.Embedding.refl K)) x k)
    · rw [if_neg hi]
      apply coordinate_embedding_off_range
      rintro ⟨j, hj⟩
      exact hi (congrArg Prod.fst hj).symm
  have first_gate_initialized {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (n : ℕ) (U : Unitary (A × K))
      (x : Space K) (w : Fin (n + 1) → A) (k : K) :
      firstGate n U (initialized blank (n + 1) x) (w, k) =
        if Fin.tail w = (fun _ => blank) then U (blankMemory blank x) (w 0, k) else 0 := by
    rw [first_gate_apply]
    have hc (i : A) (u : Fin n → A) :
        Fin.cons i u = (fun _ => blank) ↔ i = blank ∧ u = (fun _ => blank) := by
      simp [funext_iff, Fin.forall_fin_succ]
    have hv : (WithLp.toLp 2 (fun p : A × K =>
        initialized blank (n + 1) x (Fin.cons p.1 (Fin.tail w), p.2))) =
        if Fin.tail w = (fun _ => blank) then blankMemory blank x else 0 := by
      ext p
      rcases p with ⟨i, j⟩
      by_cases ht : Fin.tail w = (fun _ => blank) <;>
        simp [initialized_apply_all, hc, ht, blank_memory_apply]
    rw [hv]
    split <;> simp_all
  have circuit_initialized_step {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (U : ℕ → Unitary (A × K))
      (n t : ℕ) (x : Space K) (w : Fin (n + 1) → A) (k : K) :
      circuit U (n + 1) t (initialized blank (n + 1) x) (w, k) =
        circuit U n (t + 1)
          (initialized blank n (WithLp.toLp 2
            (fun j : K => U t (blankMemory blank x) (w 0, j)))) (Fin.tail w, k) := by
    simp only [circuit, LinearIsometryEquiv.trans_apply, tail_gate_apply]
    have hv : (WithLp.toLp 2 (fun p : Register A K n =>
        firstGate n (U t) (initialized blank (n + 1) x) (Fin.cons (w 0) p.1, p.2))) =
        initialized blank n (WithLp.toLp 2
          (fun j : K => U t (blankMemory blank x) (w 0, j))) := by
      ext p
      rcases p with ⟨u, j⟩
      simp [first_gate_initialized, initialized_apply_all]
    rw [hv]
  have occupation_cons_eq {A : Type u} [Fintype A] [DecidableEq A] {n : ℕ} (i : A) (w : Word A n) :
      occupation (Fin.cons i w) = i ::ₘ occupation w := by
    simp only [occupation, List.ofFn_cons]
    rfl
  have occupation_head_tail_iff {A : Type u} [Fintype A] [DecidableEq A] {n : ℕ} (w : Word A (n + 1)) (b : Multiset A) :
      occupation w = b ↔ w 0 ∈ b ∧ occupation (Fin.tail w) = b.erase (w 0) := by
    conv_lhs => rw [← Fin.cons_self_tail w, occupation_cons_eq]
    rw [← Multiset.singleton_add, add_comm ({w 0} : Multiset A),
      Multiset.add_singleton_eq_iff]

  intro n
  induction n with
  | zero =>
    intro t b hb hba w k
    have hb0 : b = 0 := Multiset.card_eq_zero.mp hb
    subst b
    have hw : w = (fun _ => blank) := Subsingleton.elim _ _
    simp [circuit, initialized_apply_all, hzero, hw, occupation]
  | succ n ih =>
    intro t b hb hba w k
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb
    rw [circuit_initialized_step]
    have hv : (WithLp.toLp 2
        (fun j : K => U (blankMemory blank (r b)) (w 0, j))) =
        if w 0 ∈ b then r (b.erase (w 0)) else 0 := by
      ext j
      by_cases hi : w 0 ∈ b <;> simp [hstep b hba hb0, hi]
    rw [hv]
    by_cases hi : w 0 ∈ b
    · rw [if_pos hi]
      have hcard : (b.erase (w 0)).card = n := by
        simp [Multiset.card_erase_of_mem hi, hb]
      rw [ih (t + 1) (b.erase (w 0)) hcard ((Multiset.erase_le _ _).trans hba)]
      simp only [occupation_head_tail_iff w b, hi, true_and]
    · have hw : occupation w ≠ b := fun h => hi ((occupation_head_tail_iff w b).mp h).1
      simp [hi, hw]

end

end D5.S3.Quantum.StationaryPreparation.PaddingCircuit
