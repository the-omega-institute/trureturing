/- GID: D5/S3/Quantum/Optimization/GlobalZZGateTimeBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Optimization/GlobalZZGateTimeBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every global ZZ coupling has a nonnegative sign schedule within the sharp parity bound. -/

import Mathlib.Data.Matrix.Symmetric
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Optimization.GlobalZZGateTimeBound

def SignVec (n : ℕ) :=
  {s : Fin n → Bool // ∀ i, i.val + 1 = n → s i = false}

def IsFeasible {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (λ : SignVec n → ℝ) : Prop :=
  (∀ m, 0 ≤ λ m) ∧ ∀ i j, i < j →
    M i j = ∑ m, λ m * ((-1 : ℝ) ^ (m.val i).toNat * (-1 : ℝ) ^ (m.val j).toNat)

def offDiagSup {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Option (Fin n × Fin n) =>
    match p with
    | none => 0
    | some (i, j) => if i < j then |M i j| else 0)

def gateBound (n : ℕ) : ℝ := ((if Even n then n - 1 else n : ℕ) : ℝ)

def claim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ M : Matrix (Fin n) (Fin n) ℝ,
    M.IsSymm → (∀ i, M i i = 0) →
    ∃ λ, IsFeasible M λ ∧ ∑ m, λ m ≤ gateBound n * offDiagSup M

private def IsMatching {n : ℕ} (R : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ R, e.1 < e.2) ∧
    ∀ e ∈ R, ∀ f ∈ R, e ≠ f →
      Disjoint ({e.1, e.2} : Finset (Fin n)) {f.1, f.2}

private theorem round_robin_partition (n : ℕ) (hn : 2 ≤ n) :
    ∃ R : Fin (if Even n then n - 1 else n) → Finset (Fin n × Fin n),
      (∀ r, IsMatching (R r)) ∧
      ∀ i j, i < j → ∃! r, (i, j) ∈ R r := by
  sorry

private theorem matching_law {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, i < j → |c i j| ≤ 1) :
    ∃ p : (Fin n → Bool) → ℝ,
      (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
      ∀ i j, i < j →
        (∑ s, p s * ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat)) =
          if (i, j) ∈ R then c i j else 0 := by
  sorry

private theorem fold_law {n : ℕ} (hn : 2 ≤ n) (p : (Fin n → Bool) → ℝ)
    (hp : ∀ s, 0 ≤ p s) :
    ∃ q : SignVec n → ℝ,
      (∀ m, 0 ≤ q m) ∧ (∑ m, q m = ∑ s, p s) ∧
      ∀ i j, (∑ m, q m * ((-1 : ℝ) ^ (m.val i).toNat * (-1 : ℝ) ^ (m.val j).toNat)) =
        ∑ s, p s * ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat) := by
  sorry

private theorem offDiagSup_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ offDiagSup M := by
  sorry

private theorem entry_le_offDiagSup {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i < j) : |M i j| ≤ offDiagSup M := by
  sorry

private theorem assemble_schedule (n : ℕ) (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin (if Even n then n - 1 else n) → Finset (Fin n × Fin n))
    (hR : ∀ r, IsMatching (R r))
    (hcover : ∀ i j, i < j → ∃! r, (i, j) ∈ R r) :
    ∃ λ, IsFeasible M λ ∧ ∑ m, λ m ≤ gateBound n * offDiagSup M := by
  have hd := offDiagSup_nonneg M
  have hentries := entry_le_offDiagSup M
  have hmatching := fun r => matching_law (R r) (hR r)
  have hfold := fold_law hn
  sorry

theorem result : claim := by
  intro n hn M _ _
  obtain ⟨R, hR, hcover⟩ := round_robin_partition n hn
  exact assemble_schedule n hn M R hR hcover

end D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
