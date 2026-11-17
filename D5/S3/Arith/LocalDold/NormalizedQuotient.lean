/- GID: D5/S3/Arith/LocalDold/NormalizedQuotient
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/NormalizedQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized impulse terms are actual top-coefficient observations in the monic quotient. -/
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! The coefficient order in LinearRecurrence is ascending: coeffs i is the
coefficient of U(n+i); thus manuscript c_j corresponds to coeffs(k-j). -/
set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.NormalizedQuotient
open Polynomial

/-- The actual integer polynomial quotient, without irreducibility assumptions. -/
abbrev Algebra (E : LinearRecurrence ℤ) := AdjoinRoot E.charPoly

/-- The impulse sequence, with its unique nonzero initial coordinate at order minus one. -/
noncomputable def impulse (E : LinearRecurrence ℤ) : ℕ → ℤ :=
  E.mkSol (fun i => if i.val+1=E.order then 1 else 0)

/-- Take the top coefficient of the canonical monic remainder. -/
noncomputable def observation (E : LinearRecurrence ℤ) : Algebra E →ₗ[ℤ] ℤ :=
  (Polynomial.lcoeff ℤ (E.order-1)).comp (AdjoinRoot.modByMonicHom E.charPoly_monic)

private theorem observation_initial (E : LinearRecurrence ℤ) (hk : 0 < E.order)
    (i : Fin E.order) :
    observation E ((AdjoinRoot.root E.charPoly)^i.val) =
      if i.val+1=E.order then 1 else 0 := by
  have hi : (X^i.val : ℤ[X]).degree < E.charPoly.degree := by
    rw [Polynomial.degree_X_pow, E.charPoly_degree_eq_order]
    exact_mod_cast i.isLt
  have he : (X^i.val : ℤ[X]) %ₘ E.charPoly = X^i.val :=
    (Polynomial.modByMonic_eq_self_iff E.charPoly_monic).mpr hi
  change ((AdjoinRoot.modByMonicHom E.charPoly_monic)
    ((AdjoinRoot.root E.charPoly)^i.val)).coeff (E.order-1) = _
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk, he]
  simp only [Polynomial.coeff_X_pow]
  split_ifs <;> omega

private theorem root_relation (E : LinearRecurrence ℤ) :
    (AdjoinRoot.root E.charPoly)^E.order =
      ∑ i : Fin E.order, algebraMap ℤ (Algebra E) (E.coeffs i) *
        (AdjoinRoot.root E.charPoly)^i.val := by
  have h := AdjoinRoot.eval₂_root E.charPoly
  rw [LinearRecurrence.charPoly] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_monomial,
    Polynomial.eval₂_finsetSum, map_one, one_mul] at h
  exact sub_eq_zero.mp h

/-- The quotient coefficient observation equals the actual impulse sequence at every
natural index. No desired sequence equality is assumed as a formal parameter. -/
theorem observation_eq_impulse (E : LinearRecurrence ℤ) (hk : 0 < E.order) (n : ℕ) :
    observation E ((AdjoinRoot.root E.charPoly)^n) = impulse E n := by
  apply E.eq_mk_of_is_sol_of_eq_init ?_ (observation_initial E hk) n
  intro m
  dsimp only
  rw [pow_add, root_relation, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (AdjoinRoot.root E.charPoly)^m *
      (algebraMap ℤ (Algebra E) (E.coeffs i) * (AdjoinRoot.root E.charPoly)^i.val) =
      (E.coeffs i) • ((AdjoinRoot.root E.charPoly)^(m+i.val)) by
        rw [Algebra.smul_def,pow_add];ring]
  simp only [map_smul, smul_eq_mul]

#print axioms observation_eq_impulse
end D5.S3.Arith.LocalDold.NormalizedQuotient
