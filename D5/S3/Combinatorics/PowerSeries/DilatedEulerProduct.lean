/- GID: D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/DilatedEulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Dilated Euler products preserve their coefficients under change of scalars. -/

import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-! The dilated Euler product and its unit are defined over any commutative ring. Coefficientwise transport lets the same product identities be used over the rationals, integers and residue rings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

open Filter Finset PowerSeries
open scoped PowerSeries.WithPiTopology

theorem tendsto_expand_discrete {R : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] (d : ℕ) (hd : d ≠ 0) :
    Continuous (expand d hd (R := R)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).2
  intro n
  simp only [coeff_expand]
  split_ifs
  · exact (PowerSeries.WithPiTopology.continuous_coeff R _).continuousAt
  · exact tendsto_const_nhds

noncomputable def euler {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) : PowerSeries R :=
  expand d hd (PowerSeries.pentagonalSeries R)

theorem euler_tendsto {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (d : ℕ) (hd : d ≠ 0) :
    Tendsto (fun N => ∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ (d * (i + 1)) : PowerSeries R))
      atTop (nhds (euler d hd)) := by
  have h := (tendsto_expand_discrete (R := R) d hd).continuousAt.tendsto.comp
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R).tendsto_prod_nat
  simpa only [Function.comp_def, map_prod, map_sub, map_one, map_pow, expand_X,
    ← pow_mul, euler, Nat.mul_comm] using h

theorem euler_const {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) :
    constantCoeff (euler d hd : PowerSeries R) = 1 := by
  rw [euler, constantCoeff_expand, ← coeff_zero_eq_constantCoeff]
  conv_lhs => rw [← show pentagonal 0 = 0 by decide]
  rw [coeff_pentagonalSeries_pentagonal]
  simp

noncomputable def invOne {R : Type*} [CommRing R] (p : PowerSeries R) :=
  p.invOfUnit 1

theorem mul_invOne {R : Type*} [CommRing R] {p : PowerSeries R}
    (hp : constantCoeff p = 1) : p * invOne p = 1 :=
  mul_invOfUnit p 1 hp

noncomputable def etaUnit {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) :
    (PowerSeries R)ˣ where
  val := euler d hd
  inv := invOne (euler d hd)
  val_inv := mul_invOne (euler_const _ _)
  inv_val := by rw [mul_comm]; exact mul_invOne (euler_const _ _)

theorem map_euler {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (d : ℕ) (hd : d ≠ 0) : (euler d hd).map g = euler d hd := by
  rw [euler, euler, map_expand]
  congr 1
  ext n
  classical
  simp only [coeff_map, pentagonalSeries, coeff_mk]
  split_ifs with h
  · simp only [Int.coe_negOnePow, map_pow, map_neg, map_one]
  · simp

@[simp] theorem map_eta {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (d : ℕ) (hd : d ≠ 0) :
    Units.map (PowerSeries.map g).toMonoidHom (etaUnit d hd) = etaUnit d hd := by
  apply Units.ext
  exact map_euler g d hd

@[simp] theorem expand_eta {R : Type*} [CommRing R] (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Units.map (expand a ha (R := R)).toMonoidHom (etaUnit b hb) =
      etaUnit (a*b) (Nat.mul_ne_zero ha hb) := by
  apply Units.ext
  exact (expand_mul a ha b hb _).symm

theorem prod_split_two {M : Type*} [CommMonoid M] (g : ℕ → M) (N : ℕ) :
    (∏ j ∈ range (2*N), g j) =
    (∏ j ∈ range N, g (2*j)) * (∏ j ∈ range N, g (2*j+1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, prod_range_succ, prod_range_succ, ih]
    rw [prod_range_succ, prod_range_succ]
    ac_rfl

end D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct
