/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPairClassification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetPairClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Derivation.Basic]
   utility: none
   digest: Original exponential actions reconstruct the field and derivation moduli. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity

/-! Fixed-parameter-automorphism classification of the actual highest-jet actions. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification

open Polynomial Finset Module OddPrimeJetDeformation OddPrimeJetDerivationRigidity
open scoped BigOperators

universe uK
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)

private theorem pair_log (q r : K →ₗ[F] K) (φ : E ≃* E) (P : V ≃ₗ[F] V)
    (hP : ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
      originalRepresentation r (φ g) (P v)) (a : K) (v : V) :
    P (jetOperator q a v) = jetOperator r (automorphismLinear (p := p) φ a) (P v) := by
  rw [← polynomial_log_action q a v, map_neg, map_sum]
  simp_rw [map_smul, hP]
  have hφ (i : F) : φ (Multiplicative.ofAdd (i • a)) =
      Multiplicative.ofAdd (i • automorphismLinear (p := p) φ a) := by
    exact congrArg Multiplicative.ofAdd ((automorphismLinear (p := p) φ).map_smul i a)
  simp_rw [hφ]
  exact polynomial_log_action r (automorphismLinear (p := p) φ a) (P v)

theorem commutes_pow (U : V ≃ₗ[F] V)
    (hD : ∀ v, U (D v) = D (U v)) (n : ℕ) (v : V) :
    U ((D^n) v) = (D^n) (U v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hD, ih]

def topShear : Module.End K V :=
  (dividedMonomial 1 (by have : 2 < p := Fact.out; omega)).comp
    (coefficientZero.comp (D^(p-1)))

theorem top_derivative (v : V) :
    (D^(p-1)) v = constantLinear (coefficientZero ((D^(p-1)) v)) := by
  apply Subtype.ext
  apply OddPrimeJetDeformation.derivative_kernel
  rw [← Module.End.mul_apply, ← pow_succ',
    Nat.sub_add_cancel (by have : 2 < p := Fact.out; omega), derivative_pow_prime]
  rfl

theorem topShear_derivative (v : V) : topShear (D v) = 0 := by
  have hp : 2 < p := Fact.out
  change dividedMonomial 1 _ (coefficientZero ((D^(p-1)) (D v))) = 0
  rw [← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p),
    derivative_pow_prime, LinearMap.zero_apply, map_zero, map_zero]

theorem derivative_topShear (v : V) : D (topShear v) = (D^(p-1)) v := by
  change D (dividedMonomial (0+1) _ _) = _
  rw [dividedMonomial_succ, dividedMonomial_zero]
  exact (top_derivative v).symm

theorem top_topShear (v : V) : (D^(p-1)) (topShear v) = 0 := by
  exact dividedMonomial_one_top _

private theorem topShear_top (v : V) : topShear ((D^(p-1)) v) = 0 := by
  have hp : 2 < p := Fact.out
  change dividedMonomial 1 _ (coefficientZero ((D^(p-1)) ((D^(p-1)) v))) = 0
  rw [← Module.End.mul_apply, ← pow_add,
    pow_eq_zero_of_le (by omega : p ≤ (p-1)+(p-1)) derivative_pow_prime,
    LinearMap.zero_apply, map_zero, map_zero]

def shear (b : K) : V ≃ₗ[K] V := by
  let T : Module.End K V := topShear
  have hT : T*T = 0 := by
    apply LinearMap.ext
    intro v
    change dividedMonomial 1 _ (coefficientZero ((D^(p-1)) (topShear v))) = 0
    rw [top_topShear, map_zero, map_zero]
  have hi : (1 + b • T) * (1 - b • T) = 1 ∧
      (1 - b • T) * (1 + b • T) = 1 := by
    constructor <;>
      simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one,
        smul_mul_assoc, mul_smul_comm, smul_smul, hT, smul_zero] <;> abel
  exact LinearEquiv.ofLinearMap (f := 1+b • T) (g := 1-b • T) hi.1 hi.2

theorem shear_operator (b x y : K) (v : V) :
    shear b (x • D v + y • (D^(p-1)) v) =
      x • D (shear b v) + (y-b*x) • (D^(p-1)) (shear b v) := by
  change (x • D v + y • (D^(p-1)) v) +
    b • topShear (x • D v + y • (D^(p-1)) v) =
    x • D (v + b • topShear v) + (y-b*x) • (D^(p-1)) (v + b • topShear v)
  rw [map_add, map_smul, map_smul, topShear_derivative, topShear_top,
    smul_zero, smul_zero, add_zero, smul_zero, add_zero,
    map_add, map_smul, derivative_topShear, map_add, map_smul, top_topShear,
    smul_zero, add_zero, smul_add, sub_smul, smul_smul]
  module

theorem diagonalScale_pow (c : K) (hc : c ≠ 0) (n : ℕ) (v : V) :
    diagonalScale c hc ((D^n) v) = (c⁻¹)^n • (D^n) (diagonalScale c hc v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, diagonalScale_derivative, ih, map_smul,
      smul_smul, pow_succ', Module.End.mul_apply]

private def normalizer (c : K) (hc : c ≠ 0) (d : K) : V ≃ₗ[K] V :=
  (diagonalScale c hc).trans (shear (d / c^(p-1)))

private theorem normalizer_operator (c : K) (hc : c ≠ 0) (d x y : K) (v : V) :
    normalizer c hc d (x • D v + y • (D^(p-1)) v) =
      (c⁻¹*x) • D (normalizer c hc d v) +
        ((c^(p-1))⁻¹*(y-d*(c⁻¹*x))) • (D^(p-1)) (normalizer c hc d v) := by
  simp only [normalizer, LinearEquiv.trans_apply]
  rw [map_add, map_smul, map_smul, diagonalScale_derivative, diagonalScale_pow,
    smul_smul, smul_smul, shear_operator]
  simp only [normalizer, LinearEquiv.trans_apply, inv_pow, div_eq_mul_inv]
  congr 1
  · congr 1; ring
  · congr 1; ring

private theorem normalized_data (q s : K →ₗ[F] K) (e : K ≃ₗ[F] K)
    (he1 : e 1 = 1) (U : V ≃ₗ[F] V) (hD : ∀ v, U (D v) = D (U v))
    (hL : ∀ a v, U (jetOperator q a v) =
      e a • D (U v) + s a • (D^(p-1)) (U v)) :
    ∃ σ : K ≃ₐ[F] K, (∀ a, σ a = e a) ∧
      ∃ δ : Derivation F K K, ∀ a, s a = σ (q a-δ a) := by
  have hp : 2 < p := Fact.out
  let P0 : K ≃ₗ[F] K := constantsEquiv U hD
  have hconst (z : K) : U (constantLinear z) = constantLinear (P0 z) :=
    constant_image U hD z
  have h1D (z : K) : D (dividedMonomial 1 (by omega) z) = constantLinear z := by
    simpa only [dividedMonomial_zero] using
      dividedMonomial_succ (p := p) (K := K) 0 (by omega) z
  have hscalar (a z : K) : P0 (a*z) = e a * P0 z := by
    have h := hL a (dividedMonomial 1 (by omega) z)
    simp only [jetOperator, LinearMap.add_apply, LinearMap.smul_apply] at h
    rw [h1D, dividedMonomial_one_top, smul_zero, add_zero,
      ← hD, h1D, ← commutes_pow U hD, dividedMonomial_one_top, map_zero,
      smul_zero, add_zero, ← (constantLinear (p := p) (K := K)).map_smul,
      hconst, hconst] at h
    simpa [coefficientZero, constantLinear] using
      congrArg (fun v : V => coefficientZero v) h
  have hu : P0 1 ≠ 0 := by
    exact fun h => one_ne_zero (P0.injective (h.trans (map_zero P0).symm))
  have hvalue (a : K) : P0 a = e a * P0 1 := by simpa using hscalar a 1
  have hmul (a b : K) : e (a*b) = e a * e b := by
    apply mul_right_cancel₀ hu
    rw [← hvalue, hscalar, hvalue]
    ring
  let σ : K ≃ₐ[F] K := AlgEquiv.ofLinearEquiv e he1 hmul
  refine ⟨σ, fun _ => rfl, ?_⟩
  let T : K →ₗ[F] K := (coefficientZero.restrictScalars F).comp
    (U.toLinearMap.comp ((dividedMonomial (p-2) (by omega)).restrictScalars F))
  let Q : K →ₗ[F] K := P0.symm.toLinearMap.comp T
  have htopD (z : K) : D (dividedMonomial (p-1) (by omega) z) =
      dividedMonomial (p-2) (by omega) z := by
    simpa only [show p-2+1=p-1 by omega] using
      dividedMonomial_succ (p := p) (K := K) (p-2) (by omega) z
  have htop (a z : K) : T (a*z) + P0 (q a*z) = e a*T z + s a*P0 z := by
    have h := hL a (dividedMonomial (p-1) (by omega) z)
    simp only [jetOperator, LinearMap.add_apply, LinearMap.smul_apply] at h
    rw [htopD, dividedMonomial_top, ← hD, htopD,
      ← commutes_pow U hD, dividedMonomial_top,
      ← (dividedMonomial (p-2) (by omega)).map_smul,
      ← (constantLinear (p := p) (K := K)).map_smul, map_add, hconst, hconst] at h
    simpa [coefficientZero, constantLinear, T] using
      congrArg (fun v : V => coefficientZero v) h
  let δ0 : K →ₗ[F] K := q-σ.symm.toLinearMap.comp s
  have hcomm (a z : K) : a*Q z-Q (a*z) = δ0 a*z := by
    apply P0.injective
    rw [map_sub, hscalar]
    change e a * P0 (P0.symm (T z)) - P0 (P0.symm (T (a*z))) = P0 (δ0 a*z)
    rw [P0.apply_symm_apply, P0.apply_symm_apply]
    have hs : P0 (δ0 a*z) = P0 (q a*z)-s a*P0 z := by
      change P0 ((q a-σ.symm (s a))*z) = _
      rw [sub_mul, map_sub, hscalar (σ.symm (s a)) z]
      change P0 (q a*z) - σ (σ.symm (s a))*P0 z = _
      rw [σ.apply_symm_apply]
    rw [hs]
    linear_combination -(htop a z)
  let δ : Derivation F K K := Derivation.mk' δ0 (by
    intro a b
    exact leibniz_of_commutator δ0 Q hcomm a b)
  refine ⟨δ, ?_⟩
  intro a
  have hz : δ a = q a-σ.symm (s a) := rfl
  rw [hz, sub_sub_cancel, σ.apply_symm_apply]


def coefficientAutomorphism (σ : K ≃ₐ[F] K) : V ≃ₗ[F] V :=
  let e := (degreeLTEquiv K p).restrictScalars F
  e.trans ((LinearEquiv.piCongrRight fun _ : Fin p => σ.toLinearEquiv).trans e.symm)

theorem coefficientAutomorphism_coeff (σ : K ≃ₐ[F] K) (v : V) (n : ℕ) :
    (coefficientAutomorphism σ v : K[X]).coeff n = σ ((v : K[X]).coeff n) := by
  by_cases hn : n < p
  · change (degreeLTEquiv K p) (coefficientAutomorphism σ v) ⟨n,hn⟩ = _
    exact congrFun ((degreeLTEquiv K p).apply_symm_apply
      (fun i => σ ((v : K[X]).coeff i))) ⟨n,hn⟩
  · have hz (w : V) : (w : K[X]).coeff n = 0 :=
      coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp w.property).trans_le
        (by exact_mod_cast (by omega : p ≤ n)))
    rw [hz, hz, map_zero]

theorem coefficientAutomorphism_smul (σ : K ≃ₐ[F] K) (a : K) (v : V) :
    coefficientAutomorphism σ (a • v) = σ a • coefficientAutomorphism σ v := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  simp only [coefficientAutomorphism_coeff, Submodule.coe_smul, coeff_smul,
    smul_eq_mul, map_mul]

theorem coefficientAutomorphism_derivative (σ : K ≃ₐ[F] K) (v : V) :
    coefficientAutomorphism σ (D v) = D (coefficientAutomorphism σ v) := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change (coefficientAutomorphism σ (D v) : K[X]).coeff n =
    (derivative (coefficientAutomorphism σ v : K[X])).coeff n
  rw [coefficientAutomorphism_coeff, coeff_derivative, coefficientAutomorphism_coeff]
  change σ ((derivative (v : K[X])).coeff n) = _
  rw [coeff_derivative]
  simp

private theorem coefficientAutomorphism_operator (σ : K ≃ₐ[F] K)
    (q : K →ₗ[F] K) (a : K) (v : V) :
    coefficientAutomorphism σ (jetOperator q a v) =
      σ a • D (coefficientAutomorphism σ v) +
        σ (q a) • (D^(p-1)) (coefficientAutomorphism σ v) := by
  simp only [jetOperator, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    coefficientAutomorphism_smul, coefficientAutomorphism_derivative,
    commutes_pow _ (coefficientAutomorphism_derivative σ)]

private def parameterEquiv (φ : E ≃* E) : K ≃ₗ[F] K :=
  LinearEquiv.ofBijective (automorphismLinear (p := p) φ) (by
    change Function.Bijective (fun x : K => Multiplicative.toAdd (φ (Multiplicative.ofAdd x)))
    exact (Multiplicative.toAdd : E ≃ K).bijective.comp
      (φ.bijective.comp (Multiplicative.ofAdd : K ≃ E).bijective))

private theorem parameter_one_ne_zero (φ : E ≃* E) : parameterEquiv (p := p) φ 1 ≠ 0 :=
  fun h => one_ne_zero ((parameterEquiv (p := p) φ).injective
    (h.trans (map_zero (parameterEquiv (p := p) φ)).symm))

private theorem necessary_pair (q r : K →ₗ[F] K) (hq1 : q 1 = 0)
    (φ : E ≃* E) (P : V ≃ₗ[F] V)
    (hP : ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
      originalRepresentation r (φ g) (P v)) :
    ∃ (c : Kˣ) (σ : K ≃ₐ[F] K) (δ : Derivation F K K),
      (∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd a)) = (c : K)*σ a) ∧
      ∀ a : K, r ((c : K)*σ a) = σ a*r c + (c : K)^(p-1)*σ (q a-δ a) := by
  let f := parameterEquiv (p := p) φ
  let c : K := f 1
  have hc : c ≠ 0 := parameter_one_ne_zero φ
  let e : K ≃ₗ[F] K := f.trans
    ((LinearEquiv.smulOfNeZero K K c⁻¹ (inv_ne_zero hc)).restrictScalars F)
  have he (a : K) : e a = c⁻¹*f a := rfl
  have he1 : e 1 = 1 := by rw [he]; exact inv_mul_cancel₀ hc
  let s : K →ₗ[F] K := (c^(p-1))⁻¹ • (r.comp f.toLinearMap - r c • e.toLinearMap)
  have hs (a : K) : s a = (c^(p-1))⁻¹*(r (f a)-r c*(c⁻¹*f a)) := rfl
  let C : V ≃ₗ[F] V := (normalizer c hc (r c)).restrictScalars F
  let U := P.trans C
  have hL (a : K) (v : V) : U (jetOperator q a v) =
      e a • D (U v) + s a • (D^(p-1)) (U v) := by
    change C (P (jetOperator q a v)) = _
    rw [pair_log q r φ P hP]
    exact normalizer_operator c hc (r c) (f a) (r (f a)) (P v)
  have hD (v : V) : U (D v) = D (U v) := by
    have h := hL 1 v
    have hs1 : s 1 = 0 := by rw [hs]; simp [← show c = f 1 from rfl, hc]
    simpa only [jetOperator, hq1, zero_smul, add_zero, one_smul,
      he1, hs1, zero_smul, LinearMap.add_apply, LinearMap.smul_apply] using h
  obtain ⟨σ,hσ,δ,hδ⟩ := normalized_data q s e he1 U hD hL
  have hφ (a : K) : f a = c*σ a := by
    rw [hσ, he, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine ⟨Units.mk0 c hc, σ, δ, hφ, ?_⟩
  intro a
  change r (c*σ a) = σ a*r c+c^(p-1)*σ (q a-δ a)
  have h := hδ a
  rw [hs, ← he, ← hσ] at h
  rw [← hφ]
  have hn : c^(p-1) ≠ 0 := pow_ne_zero _ hc
  field_simp at h
  linear_combination h

private theorem sufficient_pair (q r : K →ₗ[F] K) (φ : E ≃* E)
    (c : Kˣ) (σ : K ≃ₐ[F] K) (δ : Derivation F K K)
    (hφ : ∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd a)) = (c : K)*σ a)
    (hr : ∀ a : K, r ((c : K)*σ a) = σ a*r c+(c : K)^(p-1)*σ (q a-δ a)) :
    ∃ P : V ≃ₗ[F] V, ∀ (g : E) (v : V),
      P (originalRepresentation (p := p) q g v) = originalRepresentation r (φ g) (P v) := by
  let C : V ≃ₗ[F] V := (normalizer (c : K) c.ne_zero (r c)).restrictScalars F
  let U : V ≃ₗ[F] V := (gauge δ).trans (coefficientAutomorphism σ)
  let P : V ≃ₗ[F] V := U.trans C.symm
  have hC (a : K) (v : V) :
      C (jetOperator r (automorphismLinear (p := p) φ a) v) =
        σ a • D (C v) + σ (q a-δ a) • (D^(p-1)) (C v) := by
    have h := normalizer_operator (c : K) c.ne_zero (r c)
      ((c : K)*σ a) (r ((c : K)*σ a)) v
    have hcancel : (c : K)⁻¹*((c : K)*σ a) = σ a := by field_simp
    rw [hcancel, hr] at h
    have hscalar : ((c : K)^(p-1))⁻¹ *
        (σ a*r c+(c : K)^(p-1)*σ (q a-δ a)-r c*σ a) = σ (q a-δ a) := by
      field_simp
      ring
    rw [hscalar] at h
    change normalizer (c : K) c.ne_zero (r c)
      (automorphismLinear (p := p) φ a • D v+
        r (automorphismLinear (p := p) φ a) • (D^(p-1)) v) = _
    rw [show automorphismLinear (p := p) φ a = (c : K)*σ a from hφ a, hr]
    exact h
  have hU (a : K) (v : V) : U (jetOperator q a v) =
      σ a • D (U v)+σ (q a-δ a) • (D^(p-1)) (U v) := by
    change coefficientAutomorphism σ (gauge δ (jetOperator q a v)) = _
    rw [gauge_pair_operator, coefficientAutomorphism_operator]
    rfl
  have hP (a : K) (v : V) : P (jetOperator q a v) =
      jetOperator r (automorphismLinear (p := p) φ a) (P v) := by
    apply C.injective
    change C (C.symm (U (jetOperator q a v))) = _
    rw [C.apply_symm_apply, hC]
    change U (jetOperator q a v) =
      σ a • D (C (C.symm (U v))) + σ (q a-δ a) • (D^(p-1)) (C (C.symm (U v)))
    rw [C.apply_symm_apply]
    exact hU a v
  refine ⟨P, ?_⟩
  intro g v
  exact finiteExp_intertwining P.toLinearMap
    (jetOperator q (Multiplicative.toAdd g))
    (jetOperator r (automorphismLinear (p := p) φ (Multiplicative.toAdd g)))
    (hP (Multiplicative.toAdd g)) v

/-- For a fixed arbitrary automorphism of the original additive group, an
arbitrary prime-field-linear equivalence intertwines the actual exponential
representations exactly when the parameter automorphism is scalar-semilinear
and the normalized difference of the highest jets is a field derivation. -/
theorem fixed_automorphism_intertwining_iff
    (q r : K →ₗ[F] K) (hq1 : q 1 = 0) (hr1 : r 1 = 0) (φ : E ≃* E) :
    (∃ P : V ≃ₗ[F] V, ∀ (g : E) (v : V),
      P (originalRepresentation (p := p) q g v) = originalRepresentation r (φ g) (P v)) ↔
    ∃ (c : Kˣ) (σ : K ≃ₐ[F] K) (δ : Derivation F K K),
      (∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd a)) = (c : K)*σ a) ∧
      ∀ a : K, r ((c : K)*σ a) = σ a*r c+(c : K)^(p-1)*σ (q a-δ a) := by
  constructor
  · rintro ⟨P,hP⟩
    exact necessary_pair q r hq1 φ P hP
  · rintro ⟨c,σ,δ,hφ,hr⟩
    exact sufficient_pair q r φ c σ δ hφ hr

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetPairClassification
