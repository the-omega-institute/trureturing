import D5.S1.Recurrence.Algebraic.OEISA289916StrictIncrease
import D5.S1.Recurrence.Asymptotic.DominantRootForcing
import D5.S1.Recurrence.OEISA400645
import Mathlib.LinearAlgebra.Lagrange

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.Algebraic.OEISA289916Asymptotics

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.Asymptotic.DominantRootForcing (shift aeval_apply aeval_X_sub_C_apply)

/-- If a complex polynomial has only simple roots, every sequence annihilated by it is a linear
combination of the geometric sequences of its roots. -/
private theorem geom_decomp (p : ℂ[X]) (hp : p ≠ 0) (hnd : p.roots.Nodup) (u : ℕ → ℂ)
    (hu : aeval shift p u = 0) :
    ∃ α : ℂ → ℂ, ∀ n, u n = ∑ z ∈ p.roots.toFinset, α z * z ^ n := by
  classical
  set s := p.roots.toFinset with hs
  have hsplit : Multiset.card p.roots = p.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hroots : p.roots = s.val := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hnodal : p = C p.leadingCoeff * Lagrange.nodal s id := by
    conv_lhs => rw [← hprod]
    rw [hroots, Lagrange.nodal]
    rfl
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hN : aeval shift (Lagrange.nodal s id) u = 0 := by
    have h := hu
    rw [hnodal, map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply] at h
    exact (smul_eq_zero.mp h).resolve_left hlc
  rcases s.eq_empty_or_nonempty with he | hne
  · refine ⟨0, fun n => ?_⟩
    have h1 : Lagrange.nodal s id = 1 := by rw [he]; simp [Lagrange.nodal]
    rw [h1, map_one, Module.End.one_apply] at hN
    rw [hN]
    simp
  · have hgeom : ∀ i ∈ s, ∀ n, aeval shift (Lagrange.basis s id i) u n =
        aeval shift (Lagrange.basis s id i) u 0 * i ^ n := by
      intro i hi
      have hstep : aeval shift (X - C i) (aeval shift (Lagrange.basis s id i) u) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul, Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
          mul_left_comm]
        have hdvd := Lagrange.X_sub_C_dvd_nodal (s := s) id hi
        rw [id, EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero i) hdvd, map_mul,
          Module.End.mul_apply, hN, map_zero]
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h := congrFun hstep n
        rw [aeval_X_sub_C_apply] at h
        simp only [Pi.zero_apply] at h
        rw [pow_succ, ← mul_assoc, ← ih]
        linear_combination h
    refine ⟨fun i => aeval shift (Lagrange.basis s id i) u 0, fun n => ?_⟩
    have hsum := Lagrange.sum_basis (v := id) (Set.injOn_id _) hne
    have hu1 : u = aeval shift (∑ i ∈ s, Lagrange.basis s id i) u := by
      rw [hsum, map_one, Module.End.one_apply]
    calc u n = aeval shift (∑ i ∈ s, Lagrange.basis s id i) u n := by rw [← hu1]
      _ = ∑ i ∈ s, aeval shift (Lagrange.basis s id i) u n := by
          rw [map_sum, LinearMap.sum_apply, Finset.sum_apply]
      _ = ∑ i ∈ s, aeval shift (Lagrange.basis s id i) u 0 * i ^ n :=
          Finset.sum_congr rfl fun i hi => hgeom i hi n

end D5.S1.Recurrence.Algebraic.OEISA289916Asymptotics
