/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTernaryRemainder
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTernaryRemainder
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Ternary norm identity on the homogeneous zero locus. -/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
The product of geometric series has coefficients given by evaluations of
`MvPolynomial.hsymm`. With three roots, its cubic denominator gives a
degree-at-most-two formula for the remainder of a power of `Polynomial.X`.
The product of the three evaluations of this remainder gives the norm used
in section 2 of the degree-450 vertical obstruction proof.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTernaryRemainder

open scoped BigOperators Matrix
open PowerSeries (C X coeff)

noncomputable section

section Series

variable {ι : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The geometric series with coefficient `x ^ n` in degree `n`. -/
def geometric (x : R) : PowerSeries R := PowerSeries.mk fun n => x ^ n

/-- The product of the geometric series of the listed roots. -/
def rootSeries [Fintype ι] (x : ι → R) : PowerSeries R := ∏ i, geometric (x i)

private theorem prod_map_eq_prod_pow_count [Fintype ι] [DecidableEq ι]
    (x : ι → R) (s : Multiset ι) : (s.map x).prod = ∏ i, x i ^ s.count i := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.count_cons, pow_add]
    rw [Finset.prod_mul_distrib]
    have h : (∏ j : ι, x j ^ (if j = i then 1 else 0 : ℕ)) = x i := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [h, mul_comm]

/-- Multiplicities identify the distributions in `coeff_prod` with the
multisets indexing the complete homogeneous polynomial. -/
theorem coeff_rootSeries (K : Type*) [CommSemiring K] [Algebra K R]
    [Fintype ι] [DecidableEq ι] (x : ι → R) (n : ℕ) :
    coeff n (rootSeries x) = MvPolynomial.aeval x (MvPolynomial.hsymm ι K n) := by
  rw [rootSeries, PowerSeries.coeff_prod]
  simp only [geometric, PowerSeries.coeff_mk, MvPolynomial.hsymm, map_sum,
    ← Multiset.prod_hom', MvPolynomial.aeval_X]
  let e := Sym.equivNatSum ι n
  have he (s : Sym ι n) : (e s).val ∈ (Finset.univ : Finset ι).finsuppAntidiag n :=
    Finset.mem_finsuppAntidiag'.mpr ⟨(e s).property, Finset.subset_univ _⟩
  symm
  refine Finset.sum_bij (fun s _ => (e s).val) (fun s _ => he s) ?_ ?_ ?_
  · intro a _ b _ hab
    exact e.injective (Subtype.ext hab)
  · intro d hd
    let w : {d : ι →₀ ℕ // d.sum (fun _ => id) = n} :=
      ⟨d, (Finset.mem_finsuppAntidiag'.mp hd).1⟩
    exact ⟨e.symm w, Finset.mem_univ _, congrArg Subtype.val (e.apply_symm_apply w)⟩
  · intro s _
    change (s.val.map (fun i : ι => x i)).prod = ∏ i, x i ^ (e s).val i
    simp only [e, Sym.coe_equivNatSum_apply_apply]
    exact prod_map_eq_prod_pow_count (fun i : ι => x i) s.val

theorem map_rootSeries [Fintype ι] (f : R →+* S) (x : ι → R) :
    PowerSeries.map f (rootSeries x) = rootSeries (fun i => f (x i)) := by
  unfold rootSeries
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  apply PowerSeries.ext
  intro n
  simp [geometric]

end Series

section Ring

variable {ι : Type*} {R S : Type*} [CommRing R] [CommRing S]

theorem rootFactor_mul_geometric (x : R) : (1 - X * C x) * geometric x = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [geometric, sub_mul, mul_assoc]
  | succ n => simp [geometric, sub_mul, mul_assoc, PowerSeries.coeff_C_mul, pow_succ']

theorem rootFactors_mul_rootSeries [Fintype ι] (x : ι → R) :
    (∏ i, (1 - X * C (x i))) * rootSeries x = 1 := by
  rw [rootSeries, ← Finset.prod_mul_distrib]
  simp only [rootFactor_mul_geometric, Finset.prod_const_one]

theorem geometric_zero : geometric (0 : R) = 1 := by
  simpa using (rootFactor_mul_geometric (0 : R))

/-- Complete homogeneous coefficients of the three roots. -/
def ternaryH (r s t : R) (n : ℕ) : R := coeff n (rootSeries ![r, s, t])

private theorem coeff_rootSeries_three (r s t : R) (n : ℕ) :
    coeff n (rootSeries ![r, s, t]) = ternaryH r s t n := rfl

theorem ternaryH_eq_aeval_hsymm (K : Type*) [CommSemiring K] [Algebra K R]
    (r s t : R) (n : ℕ) :
    ternaryH r s t n = MvPolynomial.aeval ![r, s, t] (MvPolynomial.hsymm (Fin 3) K n) :=
  coeff_rootSeries K _ _

theorem map_ternaryH (f : R →+* S) (r s t : R) (n : ℕ) :
    f (ternaryH r s t n) = ternaryH (f r) (f s) (f t) n := by
  have hv : (fun i => f ((![r, s, t] : Fin 3 → R) i)) = ![f r, f s, f t] := by
    funext i
    fin_cases i <;> rfl
  unfold ternaryH
  rw [← PowerSeries.coeff_map, map_rootSeries, hv]

private def rootSum (r s t : R) : R := r + s + t
private def pairSum (r s t : R) : R := r * s + r * t + s * t
private def rootProduct (r s t : R) : R := r * s * t

private def denominator (a b c : R) : PowerSeries R :=
  1 - X ^ 1 * C a + X ^ 2 * C b - X ^ 3 * C c

private theorem denominator_mul_rootSeries (r s t : R) :
    denominator (rootSum r s t) (pairSum r s t) (rootProduct r s t) *
      rootSeries ![r, s, t] = 1 := by
  have h := rootFactors_mul_rootSeries ![r, s, t]
  rw [Fin.prod_univ_three] at h
  have hD : denominator (rootSum r s t) (pairSum r s t) (rootProduct r s t) =
      (1 - X * C r) * (1 - X * C s) * (1 - X * C t) := by
    simp only [denominator, rootSum, pairSum, rootProduct, pow_one, map_add, map_mul]
    ring
  simpa only [hD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

private theorem coeff_shift (F : PowerSeries R) (x : R) {m j : ℕ} (hj : j ≤ m) :
    coeff m (X ^ j * C x * F) = x * coeff (m - j) F := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_left hj, PowerSeries.coeff_C_mul]

/-- The order-three complete homogeneous recurrence from the cubic denominator. -/
theorem ternaryH_add_three (r s t : R) (n : ℕ) :
    ternaryH r s t (n + 3) = (r + s + t) * ternaryH r s t (n + 2) -
      (r * s + r * t + s * t) * ternaryH r s t (n + 1) + (r * s * t) * ternaryH r s t n := by
  have h := congrArg (coeff (n + 3)) (denominator_mul_rootSeries r s t)
  simp only [denominator, sub_mul, add_mul, one_mul, LinearMap.map_add, LinearMap.map_sub,
    coeff_shift _ _ (show 1 ≤ n + 3 by omega), coeff_shift _ _ (show 2 ≤ n + 3 by omega),
    coeff_shift _ _ (show 3 ≤ n + 3 by omega), show n + 3 - 1 = n + 2 by omega,
    show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega,
    PowerSeries.coeff_one, ite_eq_right (show n + 3 ≠ 0 by omega), coeff_rootSeries_three,
    rootSum, pairSum, rootProduct] at h
  linear_combination h

private theorem denominator_mul_geometric (a b c z : R)
    (hz : z ^ 3 = a * z ^ 2 - b * z + c) :
    denominator a b c * geometric z = 1 + X ^ 1 * C (z - a) + X ^ 2 * C (z ^ 2 - a * z + b) := by
  have hD : denominator a b c =
      (1 + X ^ 1 * C (z - a) + X ^ 2 * C (z ^ 2 - a * z + b)) * (1 - X * C z) := by
    have hz' := congrArg (C (R := R)) hz
    simp only [map_pow, map_add, map_sub, map_mul] at hz'
    simp only [denominator, map_pow, map_add, map_sub, map_mul, pow_one]
    linear_combination (X : PowerSeries R) ^ 3 * hz'
  rw [hD, mul_assoc, rootFactor_mul_geometric, mul_one]

private theorem power_eq_of_cubic (r s t z : R)
    (hz : z ^ 3 = (r + s + t) * z ^ 2 - (r * s + r * t + s * t) * z + r * s * t)
    (k : ℕ) :
    z ^ (k + 4) = ternaryH r s t (k + 2) * z ^ 2 +
      (-(r * s + r * t + s * t) * ternaryH r s t (k + 1) +
        (r * s * t) * ternaryH r s t k) * z + (r * s * t) * ternaryH r s t (k + 1) := by
  let a := rootSum r s t
  let b := pairSum r s t
  let c := rootProduct r s t
  have hseries : geometric z =
      (1 + X ^ 1 * C (z - a) + X ^ 2 * C (z ^ 2 - a * z + b)) * rootSeries ![r, s, t] := by
    calc
      geometric z = geometric z * (denominator a b c * rootSeries ![r, s, t]) := by
        rw [denominator_mul_rootSeries, mul_one]
      _ = (denominator a b c * geometric z) * rootSeries ![r, s, t] := by ac_rfl
      _ = _ := by rw [denominator_mul_geometric a b c z hz]
  have h := congrArg (coeff (k + 4)) hseries
  simp only [geometric, PowerSeries.coeff_mk, add_mul, one_mul, LinearMap.map_add,
    coeff_shift _ _ (show 1 ≤ k + 4 by omega), coeff_shift _ _ (show 2 ≤ k + 4 by omega),
    show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    coeff_rootSeries_three, a, b, rootSum, pairSum] at h
  have h₁ := ternaryH_add_three r s t (k + 1)
  have h₂ := ternaryH_add_three r s t k
  change ternaryH r s t (k + 4) = (r + s + t) * ternaryH r s t (k + 3) -
      (r * s + r * t + s * t) * ternaryH r s t (k + 2) +
      (r * s * t) * ternaryH r s t (k + 1) at h₁
  linear_combination h + h₁ + z * h₂

/-- The monic cubic of the three roots. -/
def ternaryChar (r s t : R) : Polynomial R :=
  (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C s) *
    (Polynomial.X - Polynomial.C t)

/-- The power remainder in the basis `X², X, 1`, indexed by `m = k + 4`. -/
def ternaryRemainder (r s t : R) (k : ℕ) : Polynomial R :=
  Polynomial.C (ternaryH r s t (k + 2)) * Polynomial.X ^ 2 +
    Polynomial.C (-(r * s + r * t + s * t) * ternaryH r s t (k + 1) +
      (r * s * t) * ternaryH r s t k) * Polynomial.X +
    Polynomial.C ((r * s * t) * ternaryH r s t (k + 1))

private theorem ternaryChar_dvd_pow_sub_remainder (r s t : R) (k : ℕ) :
    ternaryChar r s t ∣ Polynomial.X ^ (k + 4) - ternaryRemainder r s t k := by
  let I : Ideal (Polynomial R) := Ideal.span {ternaryChar r s t}
  let q := Ideal.Quotient.mk I
  let f : R →+* (Polynomial R ⧸ I) := q.comp Polynomial.C
  let z := q Polynomial.X
  have hχ : q (ternaryChar r s t) = 0 := by
    exact Ideal.Quotient.mk_singleton_self _
  have hprod : (z - f r) * (z - f s) * (z - f t) = 0 := by
    simpa only [ternaryChar, map_mul, map_sub, f, z, RingHom.comp_apply] using hχ
  have hz : z ^ 3 = (f r + f s + f t) * z ^ 2 -
      (f r * f s + f r * f t + f s * f t) * z + f r * f s * f t := by
    linear_combination hprod
  have hp := power_eq_of_cubic (f r) (f s) (f t) z hz k
  have hq (a b c : R) :
      q (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) =
        f a * z ^ 2 + f b * z + f c := by
    simp only [map_add, map_mul, map_pow, f, z, RingHom.comp_apply]
  apply (Ideal.Quotient.eq_zero_iff_dvd _ _).mp
  change q (Polynomial.X ^ (k + 4) - ternaryRemainder r s t k) = 0
  rw [map_sub, sub_eq_zero, map_pow, ternaryRemainder, hq]
  simpa only [z, map_ternaryH, map_add, map_neg, map_mul] using hp

/-- The generating-function calculation supplies the actual monic remainder. -/
theorem pow_modByMonic_ternaryChar [Nontrivial R] (r s t : R) (k : ℕ) :
    Polynomial.X ^ (k + 4) %ₘ ternaryChar r s t = ternaryRemainder r s t k := by
  have hs := Polynomial.monic_X_sub_C s
  have ht := Polynomial.monic_X_sub_C t
  have hχ : (ternaryChar r s t).Monic := ((Polynomial.monic_X_sub_C r).mul hs).mul ht
  have hdegree : (ternaryChar r s t).degree = 3 := by
    rw [ternaryChar, ht.degree_mul, hs.degree_mul]
    simp only [Polynomial.degree_X_sub_C]; decide
  have hsmall : (ternaryRemainder r s t k).natDegree ≤ 2 := by
    unfold ternaryRemainder
    refine (Polynomial.natDegree_add_le _ _).trans
      (max_le ?_ (by simp only [Polynomial.natDegree_C, Nat.zero_le]))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_C_mul_X_pow_le _ 2
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_X_le.trans (by decide))
  have hlt : (ternaryRemainder r s t k).degree < (ternaryChar r s t).degree := by
    rw [hdegree]
    exact (Polynomial.natDegree_le_iff_degree_le.mp hsmall).trans_lt (by decide)
  rw [Polynomial.modByMonic_eq_of_dvd_sub hχ (ternaryChar_dvd_pow_sub_remainder r s t k)]
  exact (Polynomial.modByMonic_eq_self_iff hχ).mpr hlt

/-- The ternary specialization of the middle factor at `m = k + 4`. -/
def ternaryMiddle (r s t : R) (k : ℕ) : R :=
  ternaryH r s t (k + 1) ^ 2 * ternaryH r s t (k + 4) +
    ternaryH r s t (k + 3) ^ 2 * ternaryH r s t k

/-- On the singlet hypersurface the remainder is linear. The product of its
three evaluations is `c² J_m`, and is also `c^m` for `c = r * s * t`. -/
theorem ternaryNorm_of_h_zero (r s t : R) (k : ℕ) (hzero : ternaryH r s t (k + 2) = 0) :
    (r * s * t) ^ (k + 4) = (r * s * t) ^ 2 * ternaryMiddle r s t k := by
  let c := r * s * t
  let constant := c * ternaryH r s t (k + 1)
  let linear := -(r * s + r * t + s * t) * ternaryH r s t (k + 1) + c * ternaryH r s t k
  have hlinear : ternaryH r s t (k + 3) = linear := by
    rw [ternaryH_add_three, hzero]
    simp only [linear, c, mul_zero, zero_sub, neg_mul]
  have hconstant : ternaryH r s t (k + 4) = constant + (r + s + t) * linear := by
    have h := ternaryH_add_three r s t (k + 1)
    change ternaryH r s t (k + 4) = (r + s + t) * ternaryH r s t (k + 3) -
      (r * s + r * t + s * t) * ternaryH r s t (k + 2) + c * ternaryH r s t (k + 1) at h
    simpa only [hlinear, hzero, mul_zero, sub_zero, constant, add_comm] using h
  have hroot (z : R) (hz : z = r ∨ z = s ∨ z = t) :
      z ^ (k + 4) = constant + linear * z := by
    have hχ : (ternaryChar r s t).eval z = 0 := by
      rcases hz with h | h | h <;> simp [ternaryChar, h]
    have h := map_dvd (Polynomial.evalRingHom z) (ternaryChar_dvd_pow_sub_remainder r s t k)
    change (ternaryChar r s t).eval z ∣ (Polynomial.X ^ (k + 4) - ternaryRemainder r s t k).eval z at h
    rw [Polynomial.eval_sub, hχ, zero_dvd_iff, sub_eq_zero] at h
    simpa only [ternaryRemainder, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hzero, zero_mul, zero_add, constant, linear, c,
      add_comm] using h
  calc
    c ^ (k + 4) = r ^ (k + 4) * s ^ (k + 4) * t ^ (k + 4) := by simp [c, mul_pow]
    _ = (constant + linear * r) * (constant + linear * s) * (constant + linear * t) := by
      rw [hroot r (Or.inl rfl), hroot s (Or.inr (Or.inl rfl)), hroot t (Or.inr (Or.inr rfl))]
    _ = constant ^ 3 + (r + s + t) * constant ^ 2 * linear +
          (r * s + r * t + s * t) * constant * linear ^ 2 + c * linear ^ 3 := by
      dsimp only [c]
      ring
    _ = c ^ 2 * ternaryMiddle r s t k := by
      rw [ternaryMiddle, hconstant, hlinear]
      dsimp only [constant, linear]
      ring

end Ring

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTernaryRemainder
