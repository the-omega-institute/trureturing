/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCreationWordExpansion
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Expand native creation exponential coefficients as finite oscillator word sums. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteWickSum
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Coefficients of the native creation exponential as finite oscillator word sums. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCreationWordExpansion

open LatticeGeneratingFieldLocality (Charge creationSeries creationExponential)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (State)
open P48qAllJetWickField (NativeIndex NativePolynomial nativeWordPolynomial
  nativePolynomialField nativePolynomialField_word oscillatorJet totalLevel
  allJetCoeff allJetField_coeff)

/-- The native oscillator letters that can contribute in source degree `d`. -/
abbrev Letter (d : ℕ) := Fin lattice.rank × Fin d

def letterLevel {d : ℕ} (j : Letter d) : ℕ := j.2.val + 1

def letterIndex {d : ℕ} (j : Letter d) : NativeIndex := (j.1, j.2.val)

def letterWeight {d : ℕ} (a : Charge lattice) (j : Letter d) : ℂ :=
  (a j.1 : ℂ) / (letterLevel j : ℂ)

def word {d m : ℕ} (f : Fin m → Letter d) : List NativeIndex :=
  P48qFiniteWickSum.word letterIndex f

def wordLevel {d m : ℕ} (f : Fin m → Letter d) : ℕ :=
  ∑ i, letterLevel (f i)

def wordWeight {d m : ℕ} (a : Charge lattice) (f : Fin m → Letter d) : ℂ :=
  ∏ i, letterWeight a (f i)

theorem totalLevel_word {d m : ℕ} (f : Fin m → Letter d) :
    totalLevel ((word f).map oscillatorJet) = wordLevel f := by
  induction m with
  | zero =>
    simp only [word, P48qFiniteWickSum.word, List.ofFn_zero, List.map_nil, totalLevel, wordLevel,
      Fin.sum_univ_zero]
  | succ m ih =>
    rw [word, P48qFiniteWickSum.word, List.ofFn_succ, List.map_cons, totalLevel, wordLevel,
      Fin.sum_univ_succ]
    change letterLevel (f 0) + totalLevel ((word (fun i => f i.succ)).map oscillatorJet) =
      letterLevel (f 0) + wordLevel (fun i => f i.succ)
    rw [ih]

private theorem constantCoeff_creationSeries (a : Charge lattice) :
    PowerSeries.constantCoeff (creationSeries lattice a) = 0 := by
  simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem trunc_creationSeries (a : Charge lattice) (d : ℕ) :
    ((PowerSeries.trunc (d + 1) (creationSeries lattice a) : Polynomial NativePolynomial) :
      PowerSeries NativePolynomial) =
      ∑ j : Letter d, PowerSeries.monomial (letterLevel j)
        (letterWeight a j • MvPolynomial.X (letterIndex j)) := by
  have hzero : PowerSeries.coeff 0 (creationSeries lattice a) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_creationSeries]
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range, Finset.sum_range_succ', hzero,
    Polynomial.monomial_zero_right, add_zero, ← Fin.sum_univ_eq_sum_range]
  change Polynomial.coeToPowerSeries.ringHom (∑ n : Fin d,
    Polynomial.monomial (n.val + 1) (PowerSeries.coeff (n.val + 1) (creationSeries lattice a))) = _
  rw [map_sum, Fintype.sum_prod_type_right]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
    creationSeries, PowerSeries.coeff_mk, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [letterLevel, letterWeight, letterIndex, div_eq_mul_inv, smul_smul]
  rw [mul_comm]

private theorem coeff_creationSeries_pow (a : Charge lattice) (d m : ℕ) :
    PowerSeries.coeff d (creationSeries lattice a ^ m) =
      ∑ f ∈ (Finset.univ : Finset (Fin m → Letter d)).filter (fun f => wordLevel f = d),
        wordWeight a f • nativeWordPolynomial (word f) := by
  classical
  let truncated : PowerSeries NativePolynomial :=
    PowerSeries.trunc (d + 1) (creationSeries lattice a)
  have hpow (n : ℕ) (hn : n ≤ d) :
      PowerSeries.coeff n (creationSeries lattice a ^ m) =
        PowerSeries.coeff n (truncated ^ m) := by
    induction m generalizing n with
    | zero => simp only [pow_zero]
    | succ m ih =>
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega),
        show PowerSeries.coeff p.2 truncated = PowerSeries.coeff p.2 (creationSeries lattice a)
          from PowerSeries.coeff_coe_trunc_of_lt (by omega)]
  calc
    _ = PowerSeries.coeff d (truncated ^ m) := hpow d le_rfl
    _ = _ := by
      dsimp only [truncated]
      rw [trunc_creationSeries, Fintype.sum_pow, map_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      rw [PowerSeries.prod_monomial, PowerSeries.coeff_monomial, Finset.prod_smul]
      have hword : nativeWordPolynomial (word f) =
          ∏ i, MvPolynomial.X (letterIndex (f i)) := by
        simp only [nativeWordPolynomial, word, P48qFiniteWickSum.word, List.map_ofFn,
          List.prod_ofFn, Function.comp_apply]
      rw [← hword]
      change (if d = wordLevel f then wordWeight a f • nativeWordPolynomial (word f) else 0) =
        (if wordLevel f = d then wordWeight a f • nativeWordPolynomial (word f) else 0)
      by_cases h : wordLevel f = d
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]

/-- Each ordered word of length `m` and total level `d` contributes its native
polynomial weighted by the product of its letter coefficients and by `1/m!`. -/
theorem coeff_creationExponential (a : Charge lattice) (d : ℕ) :
    PowerSeries.coeff d (creationExponential lattice a) =
      ∑ m ∈ Finset.range (d + 1), (m.factorial : ℂ)⁻¹ •
        ∑ f ∈ (Finset.univ : Finset (Fin m → Letter d)).filter (fun f => wordLevel f = d),
          wordWeight a f • nativeWordPolynomial (word f) := by
  classical
  have hsupport : Function.support (fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.exp NativePolynomial) •
        PowerSeries.coeff d (creationSeries lattice a ^ m)) ⊆
      (Finset.range (d + 1) : Set ℕ) := by
    intro m hm
    change PowerSeries.coeff m (PowerSeries.exp NativePolynomial) •
      PowerSeries.coeff d (creationSeries lattice a ^ m) ≠ 0 at hm
    change m ∈ Finset.range (d + 1)
    rw [Finset.mem_range]
    by_contra h
    have hdm : d < m := by omega
    have hzero : PowerSeries.coeff d (creationSeries lattice a ^ m) = 0 :=
      PowerSeries.coeff_of_lt_order d
        (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr hdm)
          (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m (constantCoeff_creationSeries a)))
    exact hm (by rw [hzero, smul_zero])
  rw [creationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_creationSeries a)),
    finsum_eq_sum_of_support_subset _ hsupport]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_creationSeries_pow, ← PowerSeries.map_exp (algebraMap ℂ NativePolynomial),
    PowerSeries.coeff_map, smul_eq_mul, ← Algebra.smul_def]
  simp only [PowerSeries.coeff_exp, one_div, map_inv₀, map_natCast]

/-- In degree zero the empty word supplies the unit of the native carrier. -/
theorem coeff_zero_creationExponential (a : Charge lattice) :
    PowerSeries.coeff 0 (creationExponential lattice a) = 1 := by
  rw [creationExponential, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_creationSeries a),
    PowerSeries.constantCoeff_exp, map_one]

/-- Reading the source coefficient through the native polynomial field gives
the same finite sum with each word evaluated as its all-jet coefficient. -/
theorem nativePolynomialField_creationExponential_coeff (a c : Charge lattice) (d : ℕ) (k : ℤ) :
    HVertexOperator.coeff (nativePolynomialField c
      (PowerSeries.coeff d (creationExponential lattice a))) k =
      ∑ m ∈ Finset.range (d + 1), (m.factorial : ℂ)⁻¹ •
        ∑ f ∈ (Finset.univ : Finset (Fin m → Letter d)).filter (fun f => wordLevel f = d),
          wordWeight a f • allJetCoeff c k ((word f).map oscillatorJet) := by
  classical
  let readCoeff : NativePolynomial →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj k).comp HVertexOperator.coeff).comp (nativePolynomialField c)
  change readCoeff (PowerSeries.coeff d (creationExponential lattice a)) = _
  rw [coeff_creationExponential]
  simp only [map_sum, map_smul]
  simp only [readCoeff, LinearMap.comp_apply, LinearMap.proj_apply, nativePolynomialField_word,
    allJetField_coeff]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCreationWordExpansion
