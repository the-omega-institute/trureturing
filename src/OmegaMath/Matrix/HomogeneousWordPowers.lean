import OmegaBuild.Commands
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NoncommRing

/-! Omega original.

Persistence and dimension growth for exact powers of algebra subspaces. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped Pointwise

namespace OmegaMath.HomogeneousWordPowers

section Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Fullness at a positive exact length persists at every larger length. -/
theorem pow_eq_top_of_le (L : Submodule K A) {m k : ℕ}
    (hm : 0 < m) (hfull : L ^ m = ⊤) (hk : m ≤ k) : L ^ k = ⊤ := by
  have htop : (⊤ : Submodule K A) * L = ⊤ := by
    apply top_unique
    calc
      ⊤ = L ^ (m - 1) * L := by rw [← pow_succ, Nat.sub_add_cancel hm, hfull]
      _ ≤ ⊤ * L := by gcongr; exact le_top
  induction k, hk using Nat.le_induction with
  | base => exact hfull
  | succ k hk ih => rw [pow_succ, ih, htop]

/-- A unit in degree `s` forces strict growth over `s` steps from every proper power
of an eventually full subspace. -/
theorem finrank_pow_lt_of_unit_mem [FiniteDimensional K A]
    (L : Submodule K A) (j s : ℕ) (u : Aˣ)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hs : 0 < s) (hu : (u : A) ∈ L ^ s) (hj : L ^ j ≠ ⊤) :
    Module.finrank K ↥(L ^ j) < Module.finrank K ↥(L ^ (j + s)) := by
  let U := Submodule.span K ({(u : A)} : Set A)
  let e := u.mulLeftLinearEquiv K A
  have hmap (V : Submodule K A) : U * V = V.map e.toLinearMap := by
    ext x
    rw [Submodule.mem_span_singleton_mul, Submodule.mem_map]
    rfl
  have hle : U * L ^ j ≤ L ^ (j + s) := by
    rw [Nat.add_comm j s, pow_add]
    gcongr
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hu
  by_contra! hrank
  have hstep : U * L ^ j = L ^ (j + s) :=
    Submodule.eq_of_le_of_finrank_le hle (by rwa [hmap, LinearEquiv.finrank_map_eq])
  have hproper (n : ℕ) : L ^ (j + n * s) ≠ ⊤ := by
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      have hindex : j + (n + 1) * s = (j + s) + n * s := by
        rw [Nat.add_mul]
        simp only [one_mul]
        omega
      rw [hindex, pow_add, ← hstep, mul_assoc, ← pow_add, hmap]
      exact fun h => ih (Submodule.map_eq_top_iff.mp h)
  obtain ⟨m, hm, hfull⟩ := hfull
  have hle : m ≤ j + m * s :=
    (Nat.le_mul_of_pos_right m hs).trans (Nat.le_add_left _ _)
  exact hproper m (pow_eq_top_of_le L hm hfull hle)

/-- An invertible element in degree one bounds the remaining length by the dimension deficit. -/
theorem pow_eq_top_of_finrank_add_le [FiniteDimensional K A]
    (L : Submodule K A) (u : Aˣ) (hu : (u : A) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) {j t : ℕ} (hj : 0 < j)
    (hbound : Module.finrank K A ≤ Module.finrank K ↥(L ^ j) + t) :
    L ^ (j + t) = ⊤ := by
  by_contra hproper
  have hg (k : ℕ) (hk : k ≤ t) :
      Module.finrank K ↥(L ^ j) + k ≤ Module.finrank K ↥(L ^ (j + k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hp : L ^ (j + k) ≠ ⊤ := by
          intro heq
          exact hproper (pow_eq_top_of_le L (by omega) heq (by omega))
        have hs := finrank_pow_lt_of_unit_mem L (j + k) 1 u hfull (by decide)
          (by simpa using hu) hp
        have hb := ih (by omega)
        rw [show j + (k + 1) = (j + k) + 1 by omega]
        omega
  exact hproper (Submodule.eq_of_le_of_finrank_le le_top
    (by simpa only [finrank_top] using hbound.trans (hg t le_rfl)))

end Algebra

end OmegaMath.HomogeneousWordPowers
