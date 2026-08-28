/- GID: D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bivariate formal Mobius inversion recovers the Monster primitive heat series. -/

import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.PNat.Prime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery

open scoped BigOperators

-- Bivariate formal power series in the source variables `p` and `q`.
abbrev BivariateSeries := MvPowerSeries (Fin 2) ℚ

-- A positive bivariate exponent has positive `p` and `q` coordinates.
def IsPositiveExponent (d : Fin 2 →₀ ℕ) : Prop :=
  0 < d 0 ∧ 0 < d 1

-- The positive exponent pairs occurring in the Monster heat series.
abbrev PositiveExponent := {d : Fin 2 →₀ ℕ // IsPositiveExponent d}

-- A primitive positive ray in the bivariate exponent lattice.
@[ext]
structure PrimitiveRay where
  p : ℕ+
  q : ℕ+
  coprime : p.Coprime q

-- A primitive ray together with its positive dilation degree.
abbrev RayDegree := PrimitiveRay × ℕ+

-- Scaling a primitive ray by its positive degree gives a positive exponent pair.
def rayDegreeToPair (x : RayDegree) : ℕ+ × ℕ+ :=
  (x.2 * x.1.p, x.2 * x.1.q)

private theorem gcd_rayDegreeToPair (x : RayDegree) :
    PNat.gcd (rayDegreeToPair x).1 (rayDegreeToPair x).2 = x.2 := by
  rcases x with ⟨ray, n⟩
  apply PNat.eq
  have hcop : Nat.Coprime (ray.p : ℕ) (ray.q : ℕ) :=
    PNat.coprime_coe.mpr ray.coprime
  simp [rayDegreeToPair, PNat.gcd_coe, Nat.gcd_mul_left, hcop.gcd_eq_one]

private theorem rayDegreeToPair_bijective : Function.Bijective rayDegreeToPair := by
  constructor
  · rintro ⟨ray, n⟩ ⟨ray', n'⟩ h
    have hn : n = n' := by
      calc
        n = PNat.gcd (rayDegreeToPair (ray, n)).1
              (rayDegreeToPair (ray, n)).2 := (gcd_rayDegreeToPair (ray, n)).symm
        _ = PNat.gcd (rayDegreeToPair (ray', n')).1
              (rayDegreeToPair (ray', n')).2 := congrArg (fun x => PNat.gcd x.1 x.2) h
        _ = n' := gcd_rayDegreeToPair (ray', n')
    subst n'
    have hp : ray.p = ray'.p := mul_left_cancel (congrArg Prod.fst h)
    have hq : ray.q = ray'.q := mul_left_cancel (congrArg Prod.snd h)
    exact Prod.ext (PrimitiveRay.ext hp hq) rfl
  · intro x
    let g := PNat.gcd x.1 x.2
    let p := PNat.divExact x.1 g
    let q := PNat.divExact x.2 g
    have hgp : g * p = x.1 :=
      PNat.mul_div_exact (PNat.gcd_dvd_left x.1 x.2)
    have hgq : g * q = x.2 :=
      PNat.mul_div_exact (PNat.gcd_dvd_right x.1 x.2)
    have hpq : p.Coprime q := by
      unfold PNat.Coprime
      apply mul_left_cancel (a := g)
      calc
        g * PNat.gcd p q = PNat.gcd (g * p) (g * q) := by
          apply PNat.eq
          simp [PNat.gcd_coe, Nat.gcd_mul_left]
        _ = PNat.gcd x.1 x.2 := by rw [hgp, hgq]
        _ = g := rfl
        _ = g * 1 := (mul_one g).symm
    refine ⟨(⟨p, q, hpq⟩, g), ?_⟩
    exact Prod.ext hgp hgq

-- The canonical equivalence between ray coordinates and positive exponent pairs.
noncomputable def rayDegreeEquivPositivePair : RayDegree ≃ (ℕ+ × ℕ+) :=
  Equiv.ofBijective rayDegreeToPair rayDegreeToPair_bijective

-- A positive finite-support exponent is exactly a pair of positive naturals.
noncomputable def positiveExponentEquivPositivePair : PositiveExponent ≃ (ℕ+ × ℕ+) where
  toFun d := (⟨d.1 0, d.2.1⟩, ⟨d.1 1, d.2.2⟩)
  invFun d :=
    ⟨(finTwoArrowEquiv' ℕ).symm ((d.1 : ℕ), (d.2 : ℕ)), by
      simp [IsPositiveExponent]⟩
  left_inv d := by
    apply Subtype.ext
    apply (finTwoArrowEquiv' ℕ).injective
    simp
  right_inv d := by
    apply Prod.ext <;> apply PNat.eq <;> simp

-- Every positive bivariate exponent has a unique primitive ray and degree.
noncomputable def positiveExponentRayDegreeEquiv : PositiveExponent ≃ RayDegree :=
  positiveExponentEquivPositivePair.trans rayDegreeEquivPositivePair.symm

-- The positive exponent attached to a primitive ray at a positive degree.
noncomputable def rayExponentPositive (ray : PrimitiveRay) (n : ℕ+) : PositiveExponent :=
  positiveExponentRayDegreeEquiv.symm (ray, n)

-- The underlying finitely supported exponent vector of a ray and degree.
noncomputable def rayExponent (ray : PrimitiveRay) (n : ℕ+) : Fin 2 →₀ ℕ :=
  (rayExponentPositive ray n).1

@[simp]
theorem rayDegree_rayExponentPositive (ray : PrimitiveRay) (n : ℕ+) :
    positiveExponentRayDegreeEquiv (rayExponentPositive ray n) = (ray, n) :=
  positiveExponentRayDegreeEquiv.apply_symm_apply (ray, n)

private theorem positivePair_rayExponentPositive (ray : PrimitiveRay) (n : ℕ+) :
    positiveExponentEquivPositivePair (rayExponentPositive ray n) = rayDegreeToPair (ray, n) := by
  apply rayDegreeEquivPositivePair.symm.injective
  simp [positiveExponentRayDegreeEquiv, rayExponentPositive, rayDegreeEquivPositivePair]

@[simp]
theorem rayExponent_zero (ray : PrimitiveRay) (n : ℕ+) :
    rayExponent ray n 0 = (n : ℕ) * (ray.p : ℕ) := by
  have h := congrArg Prod.fst (positivePair_rayExponentPositive ray n)
  have h' := congrArg PNat.val h
  simpa [positiveExponentEquivPositivePair, rayDegreeToPair, rayExponent] using h'

@[simp]
theorem rayExponent_one (ray : PrimitiveRay) (n : ℕ+) :
    rayExponent ray n 1 = (n : ℕ) * (ray.q : ℕ) := by
  have h := congrArg Prod.snd (positivePair_rayExponentPositive ray n)
  have h' := congrArg PNat.val h
  simpa [positiveExponentEquivPositivePair, rayDegreeToPair, rayExponent] using h'

theorem rayExponent_positive (ray : PrimitiveRay) (n : ℕ+) :
    IsPositiveExponent (rayExponent ray n) :=
  (rayExponentPositive ray n).2

private theorem rayExponent_mul (ray : PrimitiveRay) (k r : ℕ+) :
    rayExponent ray (k * r) = (k : ℕ) • rayExponent ray r := by
  ext i
  fin_cases i <;> simp [mul_assoc]

-- Simultaneous bivariate power substitution `(p,q) -> (p^k,q^k)` using the
-- pinned `MvPowerSeries.expand` algebra homomorphism.
noncomputable def powerSubstitution (k : ℕ+) (F : BivariateSeries) : BivariateSeries :=
  MvPowerSeries.expand (k : ℕ) k.ne_zero F

theorem coeff_powerSubstitution_ray (F : BivariateSeries) (ray : PrimitiveRay) (k r : ℕ+) :
    MvPowerSeries.coeff (rayExponent ray (k * r)) (powerSubstitution k F) =
      MvPowerSeries.coeff (rayExponent ray r) F := by
  rw [rayExponent_mul, powerSubstitution, MvPowerSeries.coeff_expand_smul]

-- A bivariate series with constant coefficient one.
abbrev MonsterDenominator := {D : BivariateSeries // MvPowerSeries.constantCoeff D = 1}

private theorem denominatorSubstitution_hasSubst (D : MonsterDenominator) :
    MvPowerSeries.HasSubst (fun _ : Unit => (D.1 - 1 : BivariateSeries)) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro _
  simp [D.2]

-- The bivariate formal series `-log D`, obtained by substituting `D-1` into
-- the pinned formal series `log(1+X)` and negating.
noncomputable def negativeFormalLog (D : MonsterDenominator) : BivariateSeries :=
  -MvPowerSeries.substAlgHom (denominatorSubstitution_hasSubst D) (PowerSeries.log ℚ)

-- The primitive-root heat series `H(p,q) = sum c(mn) p^m q^n`.
noncomputable def primitiveHeatSeries (c : ℕ → ℤ) : BivariateSeries := by
  classical
  exact fun d => if IsPositiveExponent d then (c (d 0 * d 1) : ℚ) else 0

theorem coeff_primitiveHeatSeries_of_not_positive (c : ℕ → ℤ) (d : Fin 2 →₀ ℕ)
    (hd : ¬IsPositiveExponent d) :
    MvPowerSeries.coeff d (primitiveHeatSeries c) = 0 := by
  simp [MvPowerSeries.coeff_apply, primitiveHeatSeries, hd]

-- The locally finite formal sum `sum_{k>=1} weight(k) F(p^k,q^k)`.
-- Positive exponents pass through the primitive-ray equivalence, making each
-- coefficient a finite divisor-antidiagonal sum.
noncomputable def dilationSum (weight : ℕ → ℚ) (F : BivariateSeries) : BivariateSeries := by
  classical
  exact fun d => if hd : IsPositiveExponent d then
      let rayDegree := positiveExponentRayDegreeEquiv ⟨d, hd⟩
      ∑ kr ∈ (rayDegree.2 : ℕ).divisorsAntidiagonal,
        weight kr.1 * MvPowerSeries.coeff
          (rayExponent rayDegree.1 (Nat.toPNat' kr.2)) F
    else 0

theorem coeff_dilationSum_ray (weight : ℕ → ℚ) (F : BivariateSeries)
    (ray : PrimitiveRay) (n : ℕ+) :
    MvPowerSeries.coeff (rayExponent ray n) (dilationSum weight F) =
      ∑ kr ∈ (n : ℕ).divisorsAntidiagonal,
        weight kr.1 * MvPowerSeries.coeff
          (rayExponent ray (Nat.toPNat' kr.2)) F := by
  simp only [MvPowerSeries.coeff_apply, dilationSum, dif_pos (rayExponent_positive ray n)]
  rw [show positiveExponentRayDegreeEquiv
      ⟨rayExponent ray n, rayExponent_positive ray n⟩ = (ray, n) by
    simpa [rayExponent] using rayDegree_rayExponentPositive ray n]

theorem coeff_dilationSum_eq_powerSubstitutions (weight : ℕ → ℚ) (F : BivariateSeries)
    (ray : PrimitiveRay) (n : ℕ+) :
    MvPowerSeries.coeff (rayExponent ray n) (dilationSum weight F) =
      ∑ kr ∈ (n : ℕ).divisorsAntidiagonal,
        weight kr.1 * MvPowerSeries.coeff (rayExponent ray n)
          (powerSubstitution (Nat.toPNat' kr.1) F) := by
  rw [coeff_dilationSum_ray]
  apply Finset.sum_congr rfl
  intro kr hkr
  congr 1
  have hproduct : kr.1 * kr.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hkr).1
  let k : ℕ+ := Nat.toPNat' kr.1
  let r : ℕ+ := Nat.toPNat' kr.2
  have hkrn : k * r = n := by
    apply PNat.eq
    simpa [k, r, Nat.toPNat'_coe,
      Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr),
      Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hkr)] using hproduct
  rw [← hkrn, coeff_powerSubstitution_ray]

-- The coefficient `1/k` in the formal logarithmic history expansion.
def logarithmicWeight (k : ℕ) : ℚ :=
  if k = 0 then 0 else 1 / (k : ℚ)

-- The coefficient `mu(k)/k` in primitive Möbius recovery.
def mobiusWeight (k : ℕ) : ℚ :=
  if k = 0 then 0 else
    (ArithmeticFunction.moebius k : ℚ) / (k : ℚ)

-- The full bivariate right side of equation (126.2).
noncomputable def logarithmicHistory (H : BivariateSeries) : BivariateSeries :=
  dilationSum logarithmicWeight H

-- The full bivariate right side of boxed equation (126.3).
noncomputable def mobiusRecovery (L : BivariateSeries) : BivariateSeries :=
  dilationSum mobiusWeight L

private noncomputable def rayCoefficient
    (F : BivariateSeries) (ray : PrimitiveRay) (n : ℕ) : ℚ :=
  if hn : 0 < n then MvPowerSeries.coeff (rayExponent ray ⟨n, hn⟩) F else 0

private theorem rayCoefficient_pos (F : BivariateSeries) (ray : PrimitiveRay)
    (n : ℕ) (hn : 0 < n) :
    rayCoefficient F ray n = MvPowerSeries.coeff (rayExponent ray ⟨n, hn⟩) F := by
  simp [rayCoefficient, hn]

private theorem rayCoefficient_dilationSum (weight : ℕ → ℚ) (F : BivariateSeries)
    (ray : PrimitiveRay) (n : ℕ) (hn : 0 < n) :
    rayCoefficient (dilationSum weight F) ray n =
      ∑ kr ∈ n.divisorsAntidiagonal, weight kr.1 * rayCoefficient F ray kr.2 := by
  rw [rayCoefficient_pos _ _ _ hn, coeff_dilationSum_ray]
  apply Finset.sum_congr rfl
  intro kr hkr
  have hr : 0 < kr.2 :=
    Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hkr)
  rw [rayCoefficient_pos _ _ _ hr]
  have hpnat : Nat.toPNat' kr.2 = (⟨kr.2, hr⟩ : ℕ+) := by
    apply PNat.eq
    rw [Nat.toPNat'_coe, if_pos hr]
    rfl
  rw [hpnat]

private theorem logarithmicHistory_ray_expansion (H : BivariateSeries)
    (ray : PrimitiveRay) (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (d : ℚ) * rayCoefficient H ray d =
      (n : ℚ) * rayCoefficient (logarithmicHistory H) ray n := by
  rw [logarithmicHistory, rayCoefficient_dilationSum _ _ _ _ hn, Finset.mul_sum]
  symm
  calc
    ∑ kr ∈ n.divisorsAntidiagonal,
          (n : ℚ) * (logarithmicWeight kr.1 * rayCoefficient H ray kr.2) =
        ∑ kr ∈ n.divisorsAntidiagonal,
          (kr.2 : ℚ) * rayCoefficient H ray kr.2 := by
      apply Finset.sum_congr rfl
      intro kr hkr
      have hproduct : kr.1 * kr.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp hkr).1
      have hk : (kr.1 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr
      rw [← hproduct, Nat.cast_mul, logarithmicWeight,
        if_neg (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr)]
      field_simp
    _ = ∑ d ∈ n.divisors, (d : ℚ) * rayCoefficient H ray d := by
      rw [Nat.sum_divisorsAntidiagonal'
        (f := fun _ r => (r : ℚ) * rayCoefficient H ray r)]

private theorem ray_mobius_recovery (H : BivariateSeries) (ray : PrimitiveRay)
    (n : ℕ) (hn : 0 < n) :
    rayCoefficient H ray n =
      rayCoefficient (mobiusRecovery (logarithmicHistory H)) ray n := by
  have inversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℚ)
      (f := fun n => (n : ℚ) * rayCoefficient H ray n)
      (g := fun n => (n : ℚ) * rayCoefficient (logarithmicHistory H) ray n)).mp
        (logarithmicHistory_ray_expansion H ray)
  rw [mobiusRecovery, rayCoefficient_dilationSum _ _ _ _ hn]
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply mul_left_cancel₀ hn_ne
  rw [Finset.mul_sum]
  calc
    (n : ℚ) * rayCoefficient H ray n =
        ∑ kr ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius kr.1 : ℚ) *
            ((kr.2 : ℚ) * rayCoefficient (logarithmicHistory H) ray kr.2) :=
      (inversion n hn).symm
    _ = ∑ kr ∈ n.divisorsAntidiagonal,
          (n : ℚ) *
            (mobiusWeight kr.1 * rayCoefficient (logarithmicHistory H) ray kr.2) := by
      apply Finset.sum_congr rfl
      intro kr hkr
      have hproduct : kr.1 * kr.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp hkr).1
      have hk : (kr.1 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr
      rw [← hproduct, Nat.cast_mul, mobiusWeight,
        if_neg (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr)]
      field_simp

private theorem primitiveHeatSeries_mobius_recovery (c : ℕ → ℤ) :
    primitiveHeatSeries c = mobiusRecovery (logarithmicHistory (primitiveHeatSeries c)) := by
  apply MvPowerSeries.ext
  intro d
  by_cases hd : IsPositiveExponent d
  · let exponent : PositiveExponent := ⟨d, hd⟩
    let rayDegree := positiveExponentRayDegreeEquiv exponent
    have hd_eq : d = rayExponent rayDegree.1 rayDegree.2 := by
      have h := positiveExponentRayDegreeEquiv.symm_apply_apply exponent
      exact congrArg Subtype.val h.symm
    rw [hd_eq]
    have hnsub : (⟨(rayDegree.2 : ℕ), rayDegree.2.pos⟩ : ℕ+) = rayDegree.2 :=
      Subtype.ext rfl
    simpa [rayCoefficient_pos, hnsub] using
      ray_mobius_recovery (primitiveHeatSeries c) rayDegree.1
        (rayDegree.2 : ℕ) rayDegree.2.pos
  · rw [coeff_primitiveHeatSeries_of_not_positive c d hd]
    simp [mobiusRecovery, dilationSum, MvPowerSeries.coeff_apply, hd]

-- Monster primitive Möbius recovery as the boxed bivariate formal-series
-- identity. Equation (126.2) identifies `L=-log D` with the logarithmic
-- history; Möbius inversion recovers the entire primitive heat series.
theorem monster_primitive_mobius_recovery
    (c : ℕ → ℤ)
    (D : MonsterDenominator)
    (logExpansion : negativeFormalLog D = logarithmicHistory (primitiveHeatSeries c)) :
    primitiveHeatSeries c = mobiusRecovery (negativeFormalLog D) := by
  rw [logExpansion]
  exact primitiveHeatSeries_mobius_recovery c

-- The primitive ray through `(1,1)`, used by the semantic probes.
def diagonalPrimitiveRay : PrimitiveRay :=
  ⟨1, 1, by simp [PNat.Coprime]⟩

-- The unit bivariate denominator, used to rule out a trivial witness.
noncomputable def unitMonsterDenominator : MonsterDenominator :=
  ⟨1, by simp⟩

-- Reverse probe: the public formal-series proposition identifies the `p*q`
-- primitive coefficient with the corresponding coefficient of `-log D`.
example (c : ℕ → ℤ) (D : MonsterDenominator)
    (recovery : primitiveHeatSeries c = mobiusRecovery (negativeFormalLog D)) :
    (c 1 : ℚ) = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
      (negativeFormalLog D) := by
  have h := congrArg
    (fun F => MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1) F) recovery
  calc
    (c 1 : ℚ) = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
        (primitiveHeatSeries c) := by
      simp [MvPowerSeries.coeff_apply, primitiveHeatSeries, IsPositiveExponent,
        diagonalPrimitiveRay]
    _ = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
        (mobiusRecovery (negativeFormalLog D)) := h
    _ = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
        (negativeFormalLog D) := by
      rw [mobiusRecovery, coeff_dilationSum_ray]
      simp [mobiusWeight]
      rw [show Nat.toPNat' 1 = (1 : ℕ+) by rfl]

-- Trivialization probe: with `D = 1`, equation (126.2) cannot hold when the
-- primitive `p*q` coefficient is nonzero.
example (c : ℕ → ℤ) (hc : c 1 ≠ 0) :
    ¬negativeFormalLog unitMonsterDenominator =
      logarithmicHistory (primitiveHeatSeries c) := by
  intro logExpansion
  have recovery :=
    monster_primitive_mobius_recovery c unitMonsterDenominator logExpansion
  have hpq : (c 1 : ℚ) = MvPowerSeries.coeff
      (rayExponent diagonalPrimitiveRay 1)
      (negativeFormalLog unitMonsterDenominator) := by
    have h := congrArg
      (fun F => MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1) F) recovery
    calc
      (c 1 : ℚ) = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
          (primitiveHeatSeries c) := by
        simp [MvPowerSeries.coeff_apply, primitiveHeatSeries, IsPositiveExponent,
          diagonalPrimitiveRay]
      _ = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
          (mobiusRecovery (negativeFormalLog unitMonsterDenominator)) := h
      _ = MvPowerSeries.coeff (rayExponent diagonalPrimitiveRay 1)
          (negativeFormalLog unitMonsterDenominator) := by
        rw [mobiusRecovery, coeff_dilationSum_ray]
        simp [mobiusWeight]
        rw [show Nat.toPNat' 1 = (1 : ℕ+) by rfl]
  have hzero : negativeFormalLog unitMonsterDenominator = 0 := by
    have hsubst : MvPowerSeries.subst
        (fun _ : Unit => (0 : BivariateSeries)) (PowerSeries.log ℚ) = 0 := by
      apply MvPowerSeries.ext
      intro d
      rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero,
        finsum_eq_single _ 0]
      · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          ← PowerSeries.constantCoeff_eq,
          PowerSeries.constantCoeff_log]
        simp
      · intro exponent hexponent
        have hunit : exponent () ≠ 0 := by
          intro hzero
          apply hexponent
          apply Finsupp.ext
          intro i
          rw [Subsingleton.elim i ()]
          exact hzero
        have hproduct : exponent.prod
            (fun _ degree => (0 : BivariateSeries) ^ degree) = 0 := by
          simp only [Finsupp.prod]
          apply Finset.prod_eq_zero (i := ())
          · simpa using hunit
          · exact zero_pow hunit
        rw [hproduct, MvPowerSeries.coeff_zero, smul_zero]
    rw [negativeFormalLog, MvPowerSeries.substAlgHom_apply]
    simpa [unitMonsterDenominator] using congrArg Neg.neg hsubst
  rw [hzero, MvPowerSeries.coeff_zero] at hpq
  apply hc
  exact_mod_cast hpq

#print axioms monster_primitive_mobius_recovery

end D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery
