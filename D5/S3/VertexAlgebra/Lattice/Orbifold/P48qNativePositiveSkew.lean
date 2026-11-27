import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Cast
import OmegaBuild.Commands

/-! Positive skew in the cover coordinate `z = x^d`. The two translation
orders group into finite antidiagonals. The cubic application uses the
native Virasoro translation and the standard-lift covariance. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePositiveSkew

open Finset
open StateField.BorcherdsPermutations (dividedTranslation)
open StateField.SkewSymmetry (reversal reversalTerm)
open scoped BigOperators

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}

private def skewTerm (d : ℕ) (ξ : ℂ) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) (k : ℤ) (j : ℕ) : V :=
  ξ ^ (k - (d : ℤ) * (j : ℤ)) •
    dividedTranslation T j (s.coeff (k - (d : ℤ) * (j : ℤ)))

private theorem shift_lt {B k : ℤ} {N j : ℕ} (hd : 0 < d)
    (hN : (k - B).toNat ≤ N) (hj : N < j) :
    k - (d : ℤ) * (j : ℤ) < B := by
  have hmul : (j : ℤ) ≤ (d : ℤ) * (j : ℤ) := by
    have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hd' (show (0 : ℤ) ≤ j by positivity)
  omega

private theorem skewTerm_bounded (d : ℕ) (ξ : ℂ) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) :
    BddBelow (Function.support (fun k => ∑ᶠ j : ℕ, skewTerm d ξ T s k j)) := by
  refine ⟨s.order, ?_⟩
  intro k hk
  by_contra! hlt
  apply hk
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  have hc : s.coeff (k - (d : ℤ) * (j : ℤ)) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by
      have hn : 0 ≤ (d : ℤ) * (j : ℤ) := by positivity
      omega)
  simp [skewTerm, hc]

/-- The formal series `exp(x^d T) s(ξ x)` for a positive cover denominator. -/
def positiveSkew (_hd : 0 < d) (ξ : ℂ) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) : HahnSeries ℤ V :=
  HahnSeries.ofSuppBddBelow
    (fun k => ∑ᶠ j : ℕ, skewTerm d ξ T s k j) (skewTerm_bounded d ξ T s)

private theorem coeff_skew_eq_sum (hd : 0 < d) (ξ : ℂ) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) (B k : ℤ) (N : ℕ)
    (hB : ∀ l < B, s.coeff l = 0) (hN : (k - B).toNat ≤ N) :
    (positiveSkew hd ξ T s).coeff k = ∑ j ∈ range (N + 1), skewTerm d ξ T s k j := by
  change (∑ᶠ j : ℕ, skewTerm d ξ T s k j) = _
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Finset.mem_coe, mem_range]
  by_contra! hn
  have hshift := shift_lt (j := j) hd hN (by omega)
  exact hj (by simp [skewTerm, hB _ hshift])

/-- One skew is a finite convolution of the substituted coefficients with the
divided powers of translation. -/
theorem positiveSkew_coeff (hd : 0 < d) (ξ : ℂ) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) (k : ℤ) :
    (positiveSkew hd ξ T s).coeff k =
      ∑ j ∈ range ((k - s.order).toNat + 1),
        ξ ^ (k - (d : ℤ) * (j : ℤ)) •
          dividedTranslation T j (s.coeff (k - (d : ℤ) * (j : ℤ))) :=
  coeff_skew_eq_sum hd ξ T s s.order k _ (fun _ h =>
    HahnSeries.coeff_eq_zero_of_lt_order h) le_rfl

/-- Denominator one recovers the ordinary state-field reversal. -/
theorem positiveSkew_one (T : Module.End ℂ V) (s : HahnSeries ℤ V) :
    positiveSkew (d := 1) (by decide) (-1) T s = reversal T s := by
  apply HahnSeries.ext
  funext k
  change (∑ᶠ j : ℕ, skewTerm 1 (-1) T s k j) = ∑ᶠ j : ℕ, reversalTerm T s k j
  apply finsum_congr
  intro j
  simp [skewTerm, reversalTerm, dividedTranslation, smul_smul, div_eq_mul_inv]

private theorem factorial_antidiagonal (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (-1 : ℂ) ^ p.2 * (p.1.factorial : ℂ)⁻¹ * (p.2.factorial : ℂ)⁻¹) =
      if n = 0 then 1 else 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hpow : (1 + (-1 : ℂ)) ^ n = if n = 0 then 1 else 0 := by
    cases n <;> simp
  calc
    _ = (∑ i ∈ range (n + 1),
          (1 : ℂ) ^ i * (-1 : ℂ) ^ (n - i) * (n.choose i : ℂ)) *
            (n.factorial : ℂ)⁻¹ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      have hfact (m : ℕ) : (m.factorial : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      rw [Nat.cast_choose ℂ (Nat.le_of_lt_succ (mem_range.mp hi))]
      field_simp [hfact] <;> ring
    _ = _ := by
      rw [← add_pow, hpow]
      split <;> simp_all

private theorem skewTerm_comp (ξ : ℂ) (hξ : ξ ^ d = -1) (T : Module.End ℂ V)
    (s : HahnSeries ℤ V) (k : ℤ) (i j : ℕ) :
    ξ ^ (k - (d : ℤ) * (i : ℤ)) •
        dividedTranslation T i (skewTerm d ξ T s (k - (d : ℤ) * (i : ℤ)) j) =
      ((-1 : ℂ) ^ j * (i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) •
        (ξ ^ (2 * (k - (d : ℤ) * ((i + j : ℕ) : ℤ))) •
          (T ^ (i + j)) (s.coeff (k - (d : ℤ) * ((i + j : ℕ) : ℤ)))) := by
  have hnz : ξ ≠ 0 := by
    intro hz
    subst ξ
    by_cases h : d = 0
    · subst d
      norm_num at hξ
    · simp [h] at hξ
  have hshift : k - (d : ℤ) * (i : ℤ) - (d : ℤ) * (j : ℤ) =
      k - (d : ℤ) * ((i + j : ℕ) : ℤ) := by push_cast; ring
  have hphase :
      ξ ^ (k - (d : ℤ) * (i : ℤ)) * ξ ^ (k - (d : ℤ) * ((i + j : ℕ) : ℤ)) =
        ξ ^ (2 * (k - (d : ℤ) * ((i + j : ℕ) : ℤ))) * (-1 : ℂ) ^ j := by
    rw [← zpow_add₀ hnz, show (k - (d : ℤ) * (i : ℤ)) +
        (k - (d : ℤ) * ((i + j : ℕ) : ℤ)) =
        2 * (k - (d : ℤ) * ((i + j : ℕ) : ℤ)) + ((d * j : ℕ) : ℤ) by
          push_cast; ring,
      zpow_add₀ hnz, zpow_natCast, pow_mul, hξ]
  simp only [skewTerm, dividedTranslation, LinearMap.smul_apply, map_smul, smul_smul, hshift]
  rw [pow_add, Module.End.mul_apply]
  congr 1
  linear_combination ((i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹) * hphase

/-- Two positive skews act by one full turn of the physical coordinate.
For each total translation order, the finite antidiagonal is the binomial
coefficient of the product of the positive and negative translation series. -/
theorem positiveSkew_twice_coeff (hd : 0 < d) (ξ : ℂ) (hξ : ξ ^ d = -1)
    (T : Module.End ℂ V) (s : HahnSeries ℤ V) (k : ℤ) :
    (positiveSkew hd ξ T (positiveSkew hd ξ T s)).coeff k = ξ ^ (2 * k) • s.coeff k := by
  let B := s.order
  let N := (k - B).toNat
  let u (n : ℕ) : V :=
    ξ ^ (2 * (k - (d : ℤ) * (n : ℤ))) • (T ^ n) (s.coeff (k - (d : ℤ) * (n : ℤ)))
  let c (p : ℕ × ℕ) : ℂ :=
    (-1 : ℂ) ^ p.2 * (p.1.factorial : ℂ)⁻¹ * (p.2.factorial : ℂ)⁻¹
  let F (p : ℕ × ℕ) : V := c p • u (p.1 + p.2)
  have hB (l : ℤ) (hl : l < B) : s.coeff l = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order hl
  have hBskew (l : ℤ) (hl : l < B) : (positiveSkew hd ξ T s).coeff l = 0 := by
    change (∑ᶠ j : ℕ, skewTerm d ξ T s l j) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hj : 0 ≤ (d : ℤ) * (j : ℤ) := by positivity
    simp [skewTerm, hB _ (by omega : l - (d : ℤ) * (j : ℤ) < B)]
  have hu (n : ℕ) (hn : N < n) : u n = 0 := by
    simp [u, hB _ (shift_lt hd (show (k - B).toNat ≤ N from le_rfl) hn)]
  have hexpand :
      (positiveSkew hd ξ T (positiveSkew hd ξ T s)).coeff k =
        ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), F (i, j) := by
    rw [coeff_skew_eq_sum hd ξ T _ B k N hBskew le_rfl]
    apply sum_congr rfl
    intro i _
    have hi : 0 ≤ (d : ℤ) * (i : ℤ) := by positivity
    have hcut : (k - (d : ℤ) * (i : ℤ) - B).toNat ≤ N := by
      dsimp [N]
      omega
    unfold skewTerm
    rw [coeff_skew_eq_sum hd ξ T s B _ N hB hcut, map_sum, smul_sum]
    exact sum_congr rfl fun j _ => skewTerm_comp ξ hξ T s k i j
  rw [hexpand, ← sum_product (range (N + 1)) (range (N + 1)) F]
  have hmaps : ∀ p ∈ range (N + 1) ×ˢ range (N + 1),
      p.1 + p.2 ∈ range (2 * N + 1) := by
    intro p hp
    simp only [mem_product, mem_range] at hp
    exact mem_range.mpr (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps F]
  have hfiber (n : ℕ) :
      (∑ p ∈ (range (N + 1) ×ˢ range (N + 1)).filter (fun p => p.1 + p.2 = n), F p) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p := by
    apply sum_subset
    · intro p hp
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (mem_filter.mp hp).2
    · intro p hp hnot
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hn : N < n := by
        by_contra! hle
        apply hnot
        simp only [mem_filter, mem_product, mem_range, he, and_true]
        omega
      simp [F, he, hu n hn]
  simp_rw [hfiber]
  have hdiag (n : ℕ) : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p) =
      (if n = 0 then (1 : ℂ) else 0) • u n := by
    calc
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p • u n :=
        sum_congr rfl fun p hp => by
          dsimp only [F]
          rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      _ = _ := by
        rw [← sum_smul, show (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p) =
          (if n = 0 then (1 : ℂ) else 0) from factorial_antidiagonal n]
  simp_rw [hdiag, ite_smul, one_smul, zero_smul]
  rw [sum_eq_single 0]
  · simp [u]
  · intro n _ hn
    simp [hn]
  · simp

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeMonodromy (nativeField_action_coeff)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "σ" => standardLift lattice g g_cube g_isometry

/-- The positive half-turn of the physical variable, lifted to the cubic cover. -/
def cubicHalfTurn : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / 3)

theorem cubicHalfTurn_cube : cubicHalfTurn ^ (3 : ℕ) = -1 := by
  rw [cubicHalfTurn, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 2 <;> norm_num <;> ring

theorem cubicHalfTurn_square : cubicHalfTurn ^ (2 : ℕ) = ζ := by
  change _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)
  rw [cubicHalfTurn, ← Complex.exp_nat_mul]
  congr 1
  norm_num <;> ring

/-- The mode `L(-1)` of the actual conformal field in
`P48qNativeVirasoro.native_conformal_virasoro`. Its cover exponent is
`-3`, since the physical conformal field has powers `z^(-m-2)`. -/
def nativeTranslation : Module.End ℂ State :=
  HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-3)

/-- The native lattice field evaluated on a twisted state. Cover exponent
`k` records the physical power `z^(k/3)`. In
`P48qNativeVirasoro.native_vacuum_minus_two_fractional_mode`, the physical
mode `q - s/3` has cover exponent `k = s - 3 * (q + 1)`. -/
def nativeInsertion (a : NativeStates) (v : State) : HahnSeries ℤ State :=
  (HahnModule.of ℂ).symm (nativeField a v)

/-- Apply the positive half-turn with the actual cubic translation. -/
def nativeSkew (s : HahnSeries ℤ State) : HahnSeries ℤ State :=
  positiveSkew (d := 3) (by decide) cubicHalfTurn nativeTranslation s

/-- Two positive skews of the evaluated native insertion give the field of
the standard-lift transform on the same twisted input, at every cover exponent. -/
theorem nativeInsertion_twice_skew_coeff (a : NativeStates) (v : State) (k : ℤ) :
    (nativeSkew (nativeSkew (nativeInsertion a v))).coeff k =
      (nativeInsertion (σ a) v).coeff k := by
  unfold nativeSkew
  rw [positiveSkew_twice_coeff (d := 3) (by decide) cubicHalfTurn cubicHalfTurn_cube]
  have hcubicHalfTurn_ne_zero : cubicHalfTurn ≠ 0 := by
    rw [cubicHalfTurn]
    exact Complex.exp_ne_zero _
  have hphase : cubicHalfTurn ^ (2 * k : ℤ) = ζ ^ k := by
    rw [show (2 * k : ℤ) = k + k by omega, zpow_add₀ hcubicHalfTurn_ne_zero,
      ← mul_zpow, ← pow_two, cubicHalfTurn_square]
  rw [hphase]
  change ζ ^ k • HVertexOperator.coeff (nativeField a) k v =
    HVertexOperator.coeff (nativeField (σ a)) k v
  rw [nativeField_action_coeff, LinearMap.smul_apply]

#print axioms positiveSkew_twice_coeff
#print axioms nativeInsertion_twice_skew_coeff

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePositiveSkew
