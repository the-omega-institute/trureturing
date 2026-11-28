/- GID: D5/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/PetrovBelRobinsonSuperenergy4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Petrov invariants, spinor contraction, and dominant gravitational superenergy. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Geometry.Lorentz.SL2CLorentzCover4D
import D5.S3.Geometry.Lorentz.KerrSchildWeylDoubleCopy4D
import D5.S3.Geometry.Lorentz.PerturbedCausalOrderWeyl4D
import OmegaMath.Geometry.BinaryQuarticSpinor
import OmegaMath.Geometry.HermitianSpinorContraction
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! Binary Weyl spinors and gravitational superenergy in the Pauli realization.
The Lorentz trace reduces to the alternating spinor form, and positive rank-one factorizations
hold for causal vectors in all four slots. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder
open Omega.BinaryQuarticSpinor Omega.HermitianSpinorContraction

namespace D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D

/-- Binomial normalization identifies the screen quartic with the symmetric spinor. -/
def spinorOfQuartic (p : WeylNullScreen.WeylQuartic) : Coefficients :=
  ![p.val.coeff 4, p.val.coeff 3 / 4, p.val.coeff 2 / 6, p.val.coeff 1 / 4, p.val.coeff 0]

def spinorOfWeyl (C : WeylNullScreen.Weyl4) : Coefficients :=
  spinorOfQuartic (WeylNullScreen.weylQuarticEquiv C)

private theorem spinorOfQuartic_polynomial (p : WeylNullScreen.WeylQuartic) :
    weylPolynomial (spinorOfQuartic p) = p.val := by
  ext n
  rw [weylPolynomial_coeff]
  by_cases h : n < 5
  · interval_cases n <;> simp [spinorOfQuartic] <;> ring
  · have h0 : p.val.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact (Polynomial.mem_degreeLT.mp p.property).trans_le (by exact_mod_cast Nat.le_of_not_gt h)
    rw [h0]
    have hn (k : ℕ) (hk : k < 5) : n ≠ k := by omega
    simp [hn 0 (by decide), hn 1 (by decide), hn 2 (by decide), hn 3 (by decide), hn 4 (by decide)]

/-- The affine evaluation of the spinor agrees with the geometric null screen tide. -/
theorem weyl_spinor_null_screen (C : WeylNullScreen.Weyl4) (z : ℂ) :
    weylSpinorForm (spinorOfWeyl C) ![z, 1] ![z, 1] ![z, 1] ![z, 1] =
      WeylNullScreen.complexTide C.val (some z) := by
  rw [← weylPolynomial_eval, spinorOfWeyl, spinorOfQuartic_polynomial]
  exact WeylNullScreen.weylQuarticEquiv_eval C (some z)

/-- The Weyl spinor extracted from the Coulomb square and the one extracted from
the plane wave have their canonical Petrov forms in compatible projective charts. -/
theorem petrov_coulomb_and_wave_spinors (M r A : ℝ) :
    spinorOfWeyl (KerrSchildWeylDoubleCopy4D.schwarzschildWeyl M r) =
      psiD (4 * (M / r ^ 3 : ℝ)) ∧
    sl2cAct (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      (spinorOfWeyl (PerturbedCausalOrderWeyl4D.waveWeyl A)) = psiN (-4 * (A : ℂ)) := by
  constructor
  · unfold spinorOfWeyl spinorOfQuartic
    rw [KerrSchildWeylDoubleCopy4D.schwarzschild_weylQuartic]
    funext i
    fin_cases i <;> norm_num [psiD, Polynomial.coeff_monomial] <;> ring
  · unfold spinorOfWeyl spinorOfQuartic
    rw [PerturbedCausalOrderWeyl4D.wave_quartic]
    simp only [Polynomial.coeff_C_mul_X_pow]
    funext i
    fin_cases i <;> norm_num [psiN, sl2cAct]

/-- In the screen orientation, the five coefficients use the chiral matrix E − iB. -/
theorem weyl_spinor_electric_magnetic (C : WeylNullScreen.Weyl4) :
    let E := (WeylNullScreen.weyl_electric_magnetic_equiv C).1.val
    let B := (WeylNullScreen.weyl_electric_magnetic_equiv C).2.val
    let Q := fun i j => (E i j : ℂ) - Complex.I * (B i j : ℂ)
    spinorOfWeyl C = ![2 * (Q 0 0 - Q 1 1) - 4 * Complex.I * Q 0 1,
      2 * Q 0 2 - 2 * Complex.I * Q 1 2, -2 * (Q 0 0 + Q 1 1),
      -2 * Q 0 2 - 2 * Complex.I * Q 1 2, 2 * (Q 0 0 - Q 1 1) + 4 * Complex.I * Q 0 1] := by
  let E := (WeylNullScreen.weyl_electric_magnetic_equiv C).1.val
  let B := (WeylNullScreen.weyl_electric_magnetic_equiv C).2.val
  let Q := fun i j => Complex.mk (E i j) (-B i j)
  let f : Fin 5 → ℂ := ![2 * (Q 0 0 - Q 1 1) + 4 * Complex.I * Q 0 1,
    -8 * Q 0 2 - 8 * Complex.I * Q 1 2, -12 * (Q 0 0 + Q 1 1),
    8 * Q 0 2 - 8 * Complex.I * Q 1 2, 2 * (Q 0 0 - Q 1 1) - 4 * Complex.I * Q 0 1]
  have h (i : Fin 5) : (WeylNullScreen.weylQuarticEquiv C).val.coeff i = f i :=
    congrFun ((Polynomial.degreeLTEquiv ℂ 5).apply_symm_apply f) i
  have hQ (i j : Fin 3) : Q i j = (E i j : ℂ) - Complex.I * (B i j : ℂ) := by
    apply Complex.ext <;> simp [Q, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have h0 : (WeylNullScreen.weylQuarticEquiv C).val.coeff 0 = f 0 := h 0
  have h1 : (WeylNullScreen.weylQuarticEquiv C).val.coeff 1 = f 1 := h 1
  have h2 : (WeylNullScreen.weylQuarticEquiv C).val.coeff 2 = f 2 := h 2
  have h3 : (WeylNullScreen.weylQuarticEquiv C).val.coeff 3 = f 3 := h 3
  have h4 : (WeylNullScreen.weylQuarticEquiv C).val.coeff 4 = f 4 := h 4
  funext i
  fin_cases i <;> simp [spinorOfWeyl, spinorOfQuartic, h0, h1, h2, h3, h4, f, hQ, E, B] <;> ring


abbrev V4 := Fin 4 → ℝ
abbrev H2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev σMat := SL2CLorentzCover4D.pauliHerm

/-- The coordinate frame for the time-negative Lorentz metric. -/
def coordinateVector (μ : Fin 4) : V4 := Pi.single μ 1

def futureCausal (v : V4) : Prop :=
  0 ≤ v 0 ∧ v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2

private def spinorTensor (ψ : Fin 5 → ℂ) (a : Fin 4 → Fin 2) : ℂ :=
  weylEntry ψ (a 0) (a 1) (a 2) (a 3)

private theorem spinorTensor_perm (ψ : Fin 5 → ℂ) (a : Fin 4 → Fin 2)
    (σ : Equiv.Perm (Fin 4)) : spinorTensor ψ (a ∘ σ) = spinorTensor ψ a := by
  have hs := Equiv.sum_comp σ (fun i => (a i).val)
  simp only [Fin.sum_univ_four] at hs
  unfold spinorTensor weylEntry
  apply congrArg ψ
  apply Fin.ext
  exact hs

/-- The complex contraction before taking the real part. -/
def belRobinsonComplex (ψ : Fin 5 → ℂ) (u : Fin 4 → V4) : ℂ :=
  contract (spinorTensor ψ) (σMat ∘ u)

/-- Bel–Robinson tensor on four vectors, in the Pauli realization of the soldering form. -/
def belRobinson (ψ : Fin 5 → ℂ) (u₁ u₂ u₃ u₄ : V4) : ℝ :=
  (belRobinsonComplex ψ ![u₁,u₂,u₃,u₄]).re

private def pauliLinear : V4 →ₗ[ℝ] H2 where
  toFun := σMat
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σMat, SL2CLorentzCover4D.pauliHerm, Pi.add_apply, Complex.ofReal_add] <;> ring
  map_smul' c u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σMat, SL2CLorentzCover4D.pauliHerm, Pi.smul_apply, Complex.ofReal_mul,
        Matrix.smul_apply, Complex.real_smul] <;> ring

/-- The real multilinear map whose evaluation is the four-vector superenergy form. -/
def belRobinsonMultilinear (ψ : Fin 5 → ℂ) : MultilinearMap ℝ (fun _ : Fin 4 => V4) ℝ :=
  Complex.reLm.compMultilinearMap
    (((contractMultilinear (spinorTensor ψ)).restrictScalars ℝ).compLinearMap fun _ => pauliLinear)

theorem belRobinson_totally_symmetric_and_real (ψ : Fin 5 → ℂ) (u : Fin 4 → V4) :
    (belRobinsonComplex ψ u).im = 0 ∧
    (∀ σ : Equiv.Perm (Fin 4), belRobinsonComplex ψ (u ∘ σ) = belRobinsonComplex ψ u) ∧
    belRobinsonMultilinear ψ u = (belRobinsonComplex ψ u).re := by
  refine ⟨contract_real _ _ (fun i => SL2CLorentzCover4D.pauliHerm_isHermitian (u i)), ?_, rfl⟩
  intro σ
  change contract (spinorTensor ψ) ((σMat ∘ u) ∘ σ) = contract (spinorTensor ψ) (σMat ∘ u)
  exact contract_perm (spinorTensor ψ) (σMat ∘ u) σ (fun a => spinorTensor_perm ψ a σ)

/-- Unit chiral phases rotate the electric and magnetic Weyl parts and preserve the pairing. -/
theorem belRobinson_so2_duality_invariant (ψ : Fin 5 → ℂ) (θ : ℝ)
    (u₁ u₂ u₃ u₄ : V4) :
    belRobinson (Complex.exp ((θ : ℂ) * Complex.I) • ψ) u₁ u₂ u₃ u₄ =
      belRobinson ψ u₁ u₂ u₃ u₄ := by
  unfold belRobinson belRobinsonComplex
  have hu : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  exact congrArg Complex.re (contract_smul_tensor (spinorTensor ψ) _ _ hu)

private theorem pauli_frame_zero : σMat (coordinateVector 0) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coordinateVector, σMat, SL2CLorentzCover4D.pauliHerm]

private theorem pauli_causal_diagonal {v : V4} (h : futureCausal v) :
    0 ≤ v 0 + v 3 ∧ 0 ≤ v 0 - v 3 := by
  have h3 : v 3 ^ 2 ≤ v 0 ^ 2 := by nlinarith [h.2, sq_nonneg (v 1), sq_nonneg (v 2)]
  have ha : |v 3| ≤ v 0 := by
    have hv : 0 ≤ v 0 := h.1
    nlinarith [sq_abs (v 3), abs_nonneg (v 3)]
  have hb := abs_le.mp ha
  constructor <;> linarith

theorem future_causal_spinor_decomposition (v : V4) (h : futureCausal v) :
    ∃ α β : Fin 2 → ℂ, σMat v = rankOne α + rankOne β := by
  let a : ℝ := v 0 + v 3
  let d : ℝ := v 0 - v 3
  let z : ℂ := (v 1 : ℂ) + Complex.I * (v 2 : ℂ)
  have ha : 0 ≤ a := (pauli_causal_diagonal h).1
  have hd : 0 ≤ d := (pauli_causal_diagonal h).2
  have hz : Complex.normSq z = v 1 ^ 2 + v 2 ^ 2 := by
    simp [z, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, pow_two, add_comm]
  have had : Complex.normSq z ≤ a * d := by
    rw [hz]
    dsimp [a, d]
    nlinarith [h.2]
  have hv : σMat v = !![(a : ℂ), conj z; z, (d : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σMat, SL2CLorentzCover4D.pauliHerm, a, d, z, Complex.ofReal_add,
        sub_eq_add_neg]
  rw [hv]
  by_cases hzero : a = 0
  · have hzz : z = 0 := Complex.normSq_eq_zero.mp <|
      le_antisymm (by simpa [hzero] using had) (Complex.normSq_nonneg z)
    refine ⟨0, ![0, (√d : ℝ)], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hzero, hzz, ← Complex.ofReal_mul, Real.mul_self_sqrt hd]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    let s := √a
    have hs : 0 < s := Real.sqrt_pos.2 ha'
    have hss : s * s = a := Real.mul_self_sqrt ha
    have hr : 0 ≤ d - Complex.normSq z / a := by
      exact sub_nonneg.mpr ((div_le_iff₀ ha').2 (by rwa [mul_comm]))
    let t := √(d - Complex.normSq z / a)
    have htt : t * t = d - Complex.normSq z / a := Real.mul_self_sqrt hr
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
    refine ⟨![(s : ℂ), z / s], ![0, (t : ℂ)], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [← Complex.ofReal_mul, hss]
    · simp [div_eq_mul_inv, hsc, mul_comm]
    · simp [div_eq_mul_inv, hsc]
    · change (d : ℂ) = z / (s : ℂ) * conj (z / (s : ℂ)) + (t : ℂ) * conj (t : ℂ)
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_div, Complex.normSq_ofReal,
        Complex.normSq_ofReal, hss, htt, ← Complex.ofReal_add]
      congr 1
      ring

theorem pauli_positive_semidefinite_iff (v : V4) : (σMat v).PosSemidef ↔ futureCausal v := by
  constructor
  · intro h
    have ht := Complex.zero_le_real.mp (by
      rw [Complex.ofReal_mul]
      change (0 : ℂ) ≤ 2 * (v 0 : ℂ)
      rw [← SL2CLorentzCover4D.pauliHerm_trace]
      exact h.trace_nonneg : (0 : ℂ) ≤ (((2 : ℝ) * v 0 : ℝ) : ℂ))
    have hd := Complex.zero_le_real.mp (by
      rw [← SL2CLorentzCover4D.pauliHerm_det]
      exact h.det_nonneg : (0 : ℂ) ≤ (SL2CLorentzCover4D.minkowskiNormSq v : ℂ))
    exact ⟨by linarith, sub_nonneg.mp hd⟩
  · intro h
    obtain ⟨α, β, hαβ⟩ := future_causal_spinor_decomposition v h
    rw [hαβ]
    exact (Matrix.posSemidef_vecMulVec_self_star α).add (Matrix.posSemidef_vecMulVec_self_star β)

theorem belRobinson_dominant_superenergy_condition (ψ : Fin 5 → ℂ) (u : Fin 4 → V4)
    (hu : ∀ i, futureCausal (u i)) : 0 ≤ (belRobinsonComplex ψ u).re := by
  classical
  choose α β h using fun i => future_causal_spinor_decomposition (u i) (hu i)
  let x (i : Fin 4) : Fin 2 → Fin 2 → ℂ := ![α i, β i]
  have hx : σMat ∘ u = fun i => ∑ j, rankOne (x i j) := by
    funext i
    simpa [x, Fin.sum_univ_two] using h i
  simp only [belRobinsonComplex, hx, contract_sum_rankOne, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

def metricSign : Fin 4 → ℝ := ![-1, 1, 1, 1]

private def spinorAlternating (a c : Fin 2) : ℂ :=
  (!![0, 1; -1, 0] : H2) a c

private theorem pauli_trace_kernel (a b c d : Fin 2) :
    ∑ μ, (metricSign μ : ℂ) * (σMat (coordinateVector μ)) a b *
      (σMat (coordinateVector μ)) c d =
    -2 * spinorAlternating a c * spinorAlternating b d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [metricSign, Fin.sum_univ_four, σMat, SL2CLorentzCover4D.pauliHerm,
      coordinateVector, spinorAlternating, Complex.I_sq]

private theorem slot_trace_zero (ψ : Fin 5 → ℂ) (M : Fin 4 → H2) :
    ∑ μ, (metricSign μ : ℂ) *
      contract (spinorTensor ψ)
        (Function.update (Function.update M 0 (σMat (coordinateVector μ)))
          1 (σMat (coordinateVector μ))) = 0 := by
  let K (a b : Fin 4 → Fin 2) : ℂ :=
    spinorTensor ψ a * conj (spinorTensor ψ b) * M 2 (a 2) (b 2) * M 3 (a 3) (b 3)
  let L (a b : Fin 4 → Fin 2) : ℂ :=
    -2 * spinorAlternating (a 0) (a 1) * spinorAlternating (b 0) (b 1)
  have hsum : (∑ μ, (metricSign μ : ℂ) *
      contract (spinorTensor ψ)
        (Function.update (Function.update M 0 (σMat (coordinateVector μ)))
          1 (σMat (coordinateVector μ)))) = ∑ a, ∑ b, K a b * L a b := by
    simp only [contract, Finset.mul_sum, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.succ_zero_eq_one, mul_one]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [show L a b = ∑ μ, (metricSign μ : ℂ) * (σMat (coordinateVector μ)) (a 0) (b 0) *
      (σMat (coordinateVector μ)) (a 1) (b 1) from (pauli_trace_kernel _ _ _ _).symm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    norm_num [K, Function.update]
    ring
  rw [hsum]
  let s : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  let e : Equiv.Perm (Fin 4 → Fin 2) := Equiv.arrowCongr s (Equiv.refl _)
  have he (a : Fin 4 → Fin 2) : e a = a ∘ s := rfl
  have hK (a b : Fin 4 → Fin 2) : K (e a) b = K a b := by
    rw [he]
    have h2 : s 2 = 2 := by decide
    have h3 : s 3 = 3 := by decide
    unfold K
    rw [spinorTensor_perm]
    simp only [Function.comp_apply, h2, h3]
  have hL (a b : Fin 4 → Fin 2) : L (e a) b = -L a b := by
    rw [he]
    have h0 : s 0 = 1 := Equiv.swap_apply_left _ _
    have h1 : s 1 = 0 := Equiv.swap_apply_right _ _
    have halt (x y : Fin 2) : spinorAlternating y x = -spinorAlternating x y := by
      fin_cases x <;> fin_cases y <;> simp [spinorAlternating]
    unfold L
    simp only [Function.comp_apply, h0, h1]
    rw [halt (a 0) (a 1)]
    ring
  have hs := Equiv.sum_comp e (fun a => ∑ b, K a b * L a b)
  simp only [hK, hL, mul_neg, Finset.sum_neg_distrib] at hs
  linear_combination -hs / 2

/-- Every pair of slots has zero trace for the time-negative Lorentz metric. -/
theorem belRobinson_completely_traceless (ψ : Fin 5 → ℂ) (u : Fin 4 → V4)
    (i j : Fin 4) (hij : i ≠ j) :
    ∑ μ, metricSign μ *
      (belRobinsonComplex ψ
        (Function.update (Function.update u i (coordinateVector μ)) j (coordinateVector μ))).re = 0 := by
  let s := Equiv.swap 0 i
  let t := Equiv.swap (s 1) j
  let p := s.trans t
  have hp0 : p 0 = i := by
    change t (s 0) = i
    have h0 : s 0 = i := Equiv.swap_apply_left _ _
    rw [h0]
    apply Equiv.swap_apply_of_ne_of_ne _ hij
    exact (s.injective.ne (by decide : (0 : Fin 4) ≠ 1)) ∘ (h0.trans ·)
  have hp1 : p 1 = j := Equiv.swap_apply_left _ _
  have hperm (v : V4) : (Function.update (Function.update u i v) j v) ∘ p =
      Function.update (Function.update (u ∘ p) 0 v) 1 v := by
    funext k
    by_cases h0 : k = 0
    · subst k
      simp [Function.comp_def, hp0, Function.update_of_ne hij]
    · by_cases h1 : k = 1
      · subst k
        simp [Function.comp_def, hp1]
      · have hi : p k ≠ i := (hp0 ▸ p.injective.ne h0)
        have hj : p k ≠ j := (hp1 ▸ p.injective.ne h1)
        simp [Function.comp_def, Function.update_of_ne, h0, h1, hi, hj]
  have hmat (v : V4) : σMat ∘ (Function.update (Function.update (u ∘ p) 0 v) 1 v) =
      Function.update (Function.update (σMat ∘ (u ∘ p)) 0 (σMat v)) 1 (σMat v) := by
    funext k
    fin_cases k <;> simp [Function.comp_def, Function.update]
  have ht := congrArg Complex.re (slot_trace_zero ψ (σMat ∘ (u ∘ p)))
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.zero_re, ← hmat, ← hperm] at ht
  have hterm (μ : Fin 4) :
      contract (spinorTensor ψ)
          (σMat ∘ ((Function.update (Function.update u i (coordinateVector μ)) j
            (coordinateVector μ)) ∘ p)) =
        belRobinsonComplex ψ
          (Function.update (Function.update u i (coordinateVector μ)) j (coordinateVector μ)) :=
    (belRobinson_totally_symmetric_and_real ψ _).2.1 p
  simpa only [hterm] using ht

/-- The rest-frame density and spatial super-Poynting covector. -/
def superenergy (ψ : Fin 5 → ℂ) : ℝ :=
  belRobinson ψ (coordinateVector 0) (coordinateVector 0) (coordinateVector 0) (coordinateVector 0)

def superPoynting (ψ : Fin 5 → ℂ) (i : Fin 3) : ℝ :=
  belRobinson ψ (coordinateVector 0) (coordinateVector 0) (coordinateVector 0) (coordinateVector i.succ)

private theorem four_constant {A : Type*} (x : A) : ![x, x, x, x] = fun _ => x := by
  funext i
  fin_cases i <;> rfl

theorem belRobinson_superenergy_positive_definite (ψ : Fin 5 → ℂ) :
    superenergy ψ = ‖ψ 0‖ ^ 2 + 4 * ‖ψ 1‖ ^ 2 + 6 * ‖ψ 2‖ ^ 2 +
      4 * ‖ψ 3‖ ^ 2 + ‖ψ 4‖ ^ 2 ∧
    0 ≤ superenergy ψ ∧ (superenergy ψ = 0 ↔ ψ = 0) := by
  have hexp : superenergy ψ = ‖ψ 0‖ ^ 2 + 4 * ‖ψ 1‖ ^ 2 + 6 * ‖ψ 2‖ ^ 2 +
      4 * ‖ψ 3‖ ^ 2 + ‖ψ 4‖ ^ 2 := by
    unfold superenergy belRobinson belRobinsonComplex
    rw [four_constant]
    change (contract (spinorTensor ψ) (fun _ => σMat (coordinateVector 0))).re = _
    rw [pauli_frame_zero, contract_identity, sum_tuple_four]
    norm_num [Fin.sum_univ_two, spinorTensor, weylEntry, Complex.add_re, ← Complex.ofReal_pow]
    ring
  refine ⟨hexp, by rw [hexp]; positivity, ?_⟩
  rw [hexp]
  constructor
  · intro h
    funext i
    suffices hz : ‖ψ i‖ ^ 2 = 0 from norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hsq (j : Fin 5) : 0 ≤ ‖ψ j‖ ^ 2 := sq_nonneg _
    apply le_antisymm _ (hsq i)
    fin_cases i
    · change ‖ψ 0‖ ^ 2 ≤ 0
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    · change ‖ψ 1‖ ^ 2 ≤ 0
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    · change ‖ψ 2‖ ^ 2 ≤ 0
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    · change ‖ψ 3‖ ^ 2 ≤ 0
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    · change ‖ψ 4‖ ^ 2 ≤ 0
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
  · intro h
    subst ψ
    simp

/-- The screen normalization gives sixteen times the sum of the two curvature traces. -/
theorem belRobinson_electric_magnetic_density (C : WeylNullScreen.Weyl4) :
    let E := (WeylNullScreen.weyl_electric_magnetic_equiv C).1.val
    let B := (WeylNullScreen.weyl_electric_magnetic_equiv C).2.val
    superenergy (spinorOfWeyl C) = 16 * ((E * E).trace + (B * B).trace) := by
  let electric := (WeylNullScreen.weyl_electric_magnetic_equiv C).1
  let magnetic := (WeylNullScreen.weyl_electric_magnetic_equiv C).2
  change superenergy (spinorOfWeyl C) = 16 * ((electric.val * electric.val).trace +
    (magnetic.val * magnetic.val).trace)
  have htrace (A : WeylNullScreen.STF3 ℝ) : A.val 2 2 = -A.val 0 0 - A.val 1 1 := by
    have h := A.property.2
    change ∑ i : Fin 3, (1 : ℝ) * A.val i i = 0 at h
    simp only [one_mul, Fin.sum_univ_three] at h
    linarith
  have hsym (A : WeylNullScreen.STF3 ℝ) (i j : Fin 3) : A.val i j = A.val j i := A.property.1 i j
  rw [(belRobinson_superenergy_positive_definite (spinorOfWeyl C)).1,
    weyl_spinor_electric_magnetic]
  change _ = 16 * ((electric.val * electric.val).trace + (magnetic.val * magnetic.val).trace)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.neg_re, Complex.neg_im, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_three, htrace electric, htrace magnetic,
    hsym electric 1 0, hsym electric 2 0, hsym electric 2 1,
    hsym magnetic 1 0, hsym magnetic 2 0, hsym magnetic 2 1]
  dsimp only [electric, magnetic]
  ring

private def restFluxMap (ψ : Fin 5 → ℂ) : V4 →ₗ[ℝ] ℝ :=
  (belRobinsonMultilinear ψ).toLinearMap (fun _ => coordinateVector 0) 3

private theorem restFluxMap_apply (ψ : Fin 5 → ℂ) (v : V4) :
    restFluxMap ψ v =
      belRobinson ψ (coordinateVector 0) (coordinateVector 0) (coordinateVector 0) v := by
  change belRobinsonMultilinear ψ (Function.update (fun _ => coordinateVector 0) 3 v) = _
  rw [show Function.update (fun _ : Fin 4 => coordinateVector 0) 3 v =
      ![coordinateVector 0, coordinateVector 0, coordinateVector 0, v] by
    funext i
    fin_cases i <;> rfl]
  rfl

theorem belRobinson_super_poynting_bound (ψ : Fin 5 → ℂ) :
    superPoynting ψ 0 ^ 2 + superPoynting ψ 1 ^ 2 + superPoynting ψ 2 ^ 2 ≤
      superenergy ψ ^ 2 := by
  let P := superPoynting ψ
  let S := P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2
  let r := √S
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hr : r ^ 2 = S := Real.sq_sqrt hS
  have hr0 : 0 ≤ r := Real.sqrt_nonneg S
  let v : V4 := ![r, -P 0, -P 1, -P 2]
  have hv : futureCausal v := by
    constructor
    · exact hr0
    · simpa [v, S] using hr.ge
  have ht : futureCausal (coordinateVector 0) := by
    norm_num [futureCausal, coordinateVector]
  have hdom := belRobinson_dominant_superenergy_condition ψ
    ![coordinateVector 0, coordinateVector 0, coordinateVector 0, v]
    (by intro i; fin_cases i <;> assumption)
  change 0 ≤ belRobinson ψ (coordinateVector 0) (coordinateVector 0) (coordinateVector 0) v at hdom
  rw [← restFluxMap_apply] at hdom
  have hvec : v = r • coordinateVector 0 - P 0 • coordinateVector 1 -
      P 1 • coordinateVector 2 - P 2 • coordinateVector 3 := by
    funext i
    fin_cases i <;> simp [v, coordinateVector]
  rw [hvec] at hdom
  simp only [map_sub, map_smul, smul_eq_mul, restFluxMap_apply] at hdom
  change 0 ≤ r * superenergy ψ - P 0 * P 0 - P 1 * P 1 - P 2 * P 2 at hdom
  have he : r * r ≤ r * superenergy ψ := by
    nlinarith [hr, hdom, show S = P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 from rfl]
  have hw := (belRobinson_superenergy_positive_definite ψ).2.1
  have hle : r ≤ superenergy ψ := by
    rcases hr0.eq_or_lt with hz | hp
    · rwa [← hz]
    · exact le_of_mul_le_mul_left he hp
  change S ≤ superenergy ψ ^ 2
  rw [← hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ superenergy ψ + r by positivity)]

private theorem superPoynting_contract (ψ : Fin 5 → ℂ) (i : Fin 3) :
    superPoynting ψ i = (∑ a : Fin 4 → Fin 2, ∑ y : Fin 2,
      spinorTensor ψ a * conj (spinorTensor ψ (Function.update a 3 y)) *
        σMat (coordinateVector i.succ) (a 3) y).re := by
  unfold superPoynting belRobinson belRobinsonComplex
  rw [show σMat ∘ ![coordinateVector 0, coordinateVector 0, coordinateVector 0,
        coordinateVector i.succ] =
      Function.update (fun _ => 1) 3 (σMat (coordinateVector i.succ)) by
    funext j
    fin_cases j <;> simp [Function.update, pauli_frame_zero]]
  rw [contract_identityExcept]

private theorem superenergy_canonical (c : ℂ) :
    superenergy (psiN c) = ‖c‖ ^ 2 ∧ superenergy (psiD c) = 6 * ‖c‖ ^ 2 := by
  constructor
  · rw [(belRobinson_superenergy_positive_definite (psiN c)).1]
    norm_num [psiN]
  · rw [(belRobinson_superenergy_positive_definite (psiD c)).1]
    norm_num [psiD]

/-- The canonical type N flux is null, and the canonical type D flux vanishes in this frame. -/
theorem belRobinson_typeN_and_typeD_flux (c : ℂ) :
    superenergy (psiN c) = ‖c‖ ^ 2 ∧ superPoynting (psiN c) = ![0, 0, -(‖c‖ ^ 2)] ∧
    √(superPoynting (psiN c) 0 ^ 2 + superPoynting (psiN c) 1 ^ 2 +
      superPoynting (psiN c) 2 ^ 2) = superenergy (psiN c) ∧
    superenergy (psiD c) = 6 * ‖c‖ ^ 2 ∧ superPoynting (psiD c) = 0 := by
  have hN : superPoynting (psiN c) = ![0, 0, -(‖c‖ ^ 2)] := by
    funext i
    rw [superPoynting_contract, sum_tuple_four]
    fin_cases i <;>
      norm_num [Fin.sum_univ_two, spinorTensor, weylEntry, psiN, coordinateVector,
        σMat, SL2CLorentzCover4D.pauliHerm, Function.update, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.neg_re, ← Complex.ofReal_pow, Pi.single_apply, Fin.succ]
  refine ⟨(superenergy_canonical c).1, hN, ?_, (superenergy_canonical c).2, ?_⟩
  · rw [hN, (superenergy_canonical c).1]
    simp [Real.sqrt_sq (sq_nonneg ‖c‖)]
  · funext i
    rw [superPoynting_contract, sum_tuple_four]
    fin_cases i <;>
      norm_num [Fin.sum_univ_two, spinorTensor, weylEntry, psiD, coordinateVector,
        σMat, SL2CLorentzCover4D.pauliHerm, Function.update, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.neg_re, ← Complex.ofReal_pow, Pi.single_apply, Fin.succ]

end D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
