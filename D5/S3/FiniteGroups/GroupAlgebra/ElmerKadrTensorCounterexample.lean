/- GID: D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: Polynomial translation duals and the relative trace obstruction for the Elmer--Kadr tensor instance. -/

import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-!
The source conventions are Elmer--Kadr, DOI 10.1007/s13366-026-00855-9,
Section 2.2, Lemma 2.1 and formulas (11)--(12). Polynomial translation on
degree < m is the dehomogenized symmetric power, with z^i corresponding
to X^i Y^(m-1-i); V_m is its actual contragredient dual.

The relative trace argument uses a genuine finite subgroup action. It does
not regard a coefficient operator as primitive on arbitrary tensor factors.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample

open scoped TensorProduct
open Finset

universe uK uG uC uV uX uM

section RelativeTrace

variable {K : Type uK} [Field K]
  {G : Type uG} [Group G] {C : Type uC} [Group C] [Fintype C]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {X : Type uX} [AddCommGroup X] [Module K X]
  {M : Type uM} [AddCommGroup M] [Module K M]

private theorem trace_conjugate (ρ : Representation K G V)
    (t : Module.End K V) (g : G) :
    LinearMap.trace K V ((ρ g).comp (t.comp (ρ g⁻¹))) =
      LinearMap.trace K V t := by
  change LinearMap.trace K V (ρ g * (t * ρ g⁻¹)) = _
  rw [LinearMap.trace_mul_cycle']
  simp only [← map_mul, inv_mul_cancel, map_one, one_mul]

-- Only V has a trace. X and M can be arbitrarily generated, in independent
-- universes; no invalid cyclicity across an infinite-dimensional factor is used.
private theorem trace_tensor_factorization
    (ι : C →* G) (ρ : Representation K G V)
    (σ : Representation K G X) (τ : Representation K G M)
    (t : Module.End K M)
    (ht : (∑ c : C, (τ (ι c)).comp (t.comp (τ (ι c⁻¹)))) = LinearMap.id)
    (hcard : (Fintype.card C : K) = 0)
    (f : ρ.IntertwiningMap (σ.tprod τ))
    (g : (σ.tprod τ).IntertwiningMap ρ) :
    LinearMap.trace K V (g.toLinearMap.comp f.toLinearMap) = 0 := by
  classical
  let T : Module.End K (X ⊗[K] M) := TensorProduct.map LinearMap.id t
  have hT : (∑ c : C,
      ((σ.tprod τ) (ι c)).comp (T.comp ((σ.tprod τ) (ι c⁻¹)))) =
        LinearMap.id := by
    apply TensorProduct.ext'
    intro x m
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      Representation.tprod_apply, TensorProduct.map_tmul, T, LinearMap.id_apply]
    have hc (c : C) : σ (ι c) (σ (ι c⁻¹) x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel,
        map_one, map_one, Module.End.one_apply]
    simp_rw [hc]
    rw [← TensorProduct.tmul_sum]
    congr 1
    exact LinearMap.congr_fun ht m
  have he : g.toLinearMap.comp f.toLinearMap =
      ∑ c : C, (ρ (ι c)).comp
        ((g.toLinearMap.comp (T.comp f.toLinearMap)).comp (ρ (ι c⁻¹))) := by
    apply LinearMap.ext
    intro v
    have hv := congrArg g (LinearMap.congr_fun hT (f v))
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sum] at hv
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply,
      ← f.isIntertwining, g.isIntertwining] using hv.symm
  rw [he, map_sum]
  simp only [trace_conjugate, sum_const, card_univ, nsmul_eq_mul, hcard, zero_mul]

end RelativeTrace

section PolynomialModel

variable (K : Type uK) [Field K]

/-- The primal model of S^(m-1)(W): z^i corresponds to X^i Y^(m-1-i). -/
abbrev Primal (m : ℕ) := Polynomial.degreeLT K m

/-- The original dual module, rather than a separately postulated matrix action. -/
abbrev DualPower (m : ℕ) := Module.Dual K (Primal K m)

/-- Actual polynomial translations by the additive group of the field. -/
def primalAction (m : ℕ) : Representation K (Multiplicative K) (Primal K m) where
  toFun a := (Polynomial.taylorLinearEquiv (Multiplicative.toAdd a) m).toLinearMap
  map_one' := by
    ext q
    apply Subtype.ext
    exact Polynomial.taylor_zero _
  map_mul' a b := by
    ext q
    apply Subtype.ext
    exact (Polynomial.taylor_taylor _ _ _).symm

/-- The contragredient of the actual translation symmetric power. -/
def dualAction (m : ℕ) : Representation K (Multiplicative K) (DualPower K m) :=
  (primalAction K m).dual

/-- The dual monomial basis used in formula (12). -/
def dualBasis (m : ℕ) : Module.Basis (Fin m) K (DualPower K m) :=
  (Polynomial.degreeLT.basis K m).dualBasis

end PolynomialModel

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
