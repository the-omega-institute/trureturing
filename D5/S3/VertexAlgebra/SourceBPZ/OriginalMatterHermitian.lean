/- GID: D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Frame-free Hermitian form and all-integer matter current/Sugawara adjoints. -/

import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeInvolution
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
open MvPolynomial
open private wick_constant_left wick_constant_right from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

variable {D : LatticeData}

/-! Coefficient conjugation on the original oscillator and finite-charge carrier. -/

def kappaOsc (p : Oscillator D) : Oscillator D :=
  MvPolynomial.map (starRingEnd ℂ) p

def kappaCarrier (x : Carrier D) : Carrier D :=
  x.mapRange kappaOsc (by simp [kappaOsc])

@[simp] theorem kappaOsc_C (c : ℂ) : kappaOsc (C c : Oscillator D) = C (conj c) := by
  simp [kappaOsc]

@[simp] theorem kappaOsc_X (x : Index D) : kappaOsc (X x) = X x := by
  simp [kappaOsc]

@[simp] theorem kappaOsc_add (p q : Oscillator D) :
    kappaOsc (p + q) = kappaOsc p + kappaOsc q := by
  simp [kappaOsc]

@[simp] theorem kappaOsc_mul (p q : Oscillator D) :
    kappaOsc (p * q) = kappaOsc p * kappaOsc q := by
  simp [kappaOsc]

@[simp] theorem kappaOsc_smul (c : ℂ) (p : Oscillator D) :
    kappaOsc (c • p) = conj c • kappaOsc p := by
  simp [kappaOsc, Algebra.smul_def]

@[simp] theorem kappaOsc_coeff (p : Oscillator D) (e : Index D →₀ ℕ) :
    (kappaOsc p).coeff e = conj (p.coeff e) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      by_cases h : d = e
      · subst d
        simp [kappaOsc]
      · simp [kappaOsc, h, Ne.symm h]
  | add p q hp hq => simp [hp, hq]

@[simp] theorem kappaCarrier_zero : kappaCarrier (0 : Carrier D) = 0 := by
  simp [kappaCarrier]

@[simp] theorem kappaCarrier_add (x y : Carrier D) :
    kappaCarrier (x + y) = kappaCarrier x + kappaCarrier y := by
  classical
  apply Finsupp.ext
  intro a
  simp [kappaCarrier]

@[simp] theorem kappaCarrier_smul (c : ℂ) (x : Carrier D) :
    kappaCarrier (c • x) = conj c • kappaCarrier x := by
  classical
  apply Finsupp.ext
  intro a
  simp [kappaCarrier]

@[simp] theorem kappaCarrier_single (a : Charge D) (p : Oscillator D) :
    kappaCarrier (Finsupp.single a p) = Finsupp.single a (kappaOsc p) := by
  simp [kappaCarrier]

theorem kappaOsc_pderiv (i : Index D) (p : Oscillator D) :
    kappaOsc (MvPolynomial.pderiv i p) = MvPolynomial.pderiv i (kappaOsc p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp [kappaOsc, MvPolynomial.pderiv_monomial]
  | add p q hp hq => simp [hp, hq]

theorem kappaOsc_annihilate (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    kappaOsc (LatticeActualAnnihilation.annihilate D i k p) =
      LatticeActualAnnihilation.annihilate D i k (kappaOsc p) := by
  unfold LatticeActualAnnihilation.annihilate
    LatticeSugawaraCurrents.weightedPartial
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  change MvPolynomial.map (starRingEnd ℂ)
      (∑ j : Fin D.rank, (D.G i j : ℂ) • MvPolynomial.pderiv (j,k) p) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change kappaOsc ((D.G i j : ℂ) • MvPolynomial.pderiv (j,k) p) = _
  rw [kappaOsc_smul]
  have hG : conj (D.G i j : ℂ) = (D.G i j : ℂ) := by norm_num
  rw [hG]
  rw [kappaOsc_pderiv]
  simp only [Derivation.coeFn_coe]

theorem kappaOsc_neutralPolynomialMode (i : Fin D.rank) (a : Charge D)
    (m : ℤ) (p : Oscillator D) :
    kappaOsc (neutralPolynomialMode D i a m p) =
      neutralPolynomialMode D i a m (kappaOsc p) := by
  by_cases hm : m < 0
  · rw [show neutralPolynomialMode D i a m =
        LinearMap.mulLeft ℂ (X (i, (-m - 1).toNat)) by
          simp [neutralPolynomialMode, hm]]
    simp only [LinearMap.mulLeft_apply]
    change kappaOsc (X (i, (-m - 1).toNat) * p) =
      X (i, (-m - 1).toNat) * kappaOsc p
    rw [kappaOsc_mul, kappaOsc_X]
  · by_cases hz : m = 0
    · subst m
      rw [show neutralPolynomialMode D i a 0 =
        (bilinear D (unitCharge D i) a : ℂ) • LinearMap.id by
          simp [neutralPolynomialMode]]
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      change kappaOsc ((bilinear D (unitCharge D i) a : ℂ) • p) =
        (bilinear D (unitCharge D i) a : ℂ) • kappaOsc p
      rw [kappaOsc_smul]
      simp
    · have hmpos : 0 < m := by omega
      let n := (m - 1).toNat
      have hm' : m = (n : ℤ) + 1 := by
        dsimp [n]
        omega
      rw [hm', neutralPolynomialMode_positive]
      simp only [LinearMap.smul_apply]
      rw [kappaOsc_smul]
      unfold LatticeSugawaraCurrents.weightedPartial
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
      have hs : conj ((n : ℂ) + 1) = (n : ℂ) + 1 := by simp
      rw [hs]
      congr 1
      change MvPolynomial.map (starRingEnd ℂ)
          (∑ j : Fin D.rank, (D.G i j : ℂ) •
            MvPolynomial.pderiv (j,n) p) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change kappaOsc ((D.G i j : ℂ) • MvPolynomial.pderiv (j,n) p) = _
      rw [kappaOsc_smul]
      have hG : conj (D.G i j : ℂ) = (D.G i j : ℂ) := by norm_num
      rw [hG]
      rw [kappaOsc_pderiv]
      simp only [Derivation.coeFn_coe]

theorem kappaCarrier_neutralMode (i : Fin D.rank) (m : ℤ) (x : Carrier D) :
    kappaCarrier (neutralMode D i m x) =
      neutralMode D i m (kappaCarrier x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, kappaCarrier_add, hx, hy]
  | single a p =>
      simp only [neutralMode_single, kappaCarrier_single]
      rw [kappaOsc_neutralPolynomialMode]

theorem kappaOsc_involutive (p : Oscillator D) :
    kappaOsc (kappaOsc p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => simp [kappaOsc]
  | add p q hp hq => simp [hp, hq]

private theorem integerWick_constant_left (c : ℂ) (q : Oscillator D) :
    integerWick D (C c) q = c * q.coeff 0 := by
  rw [integerWick_apply,
    show retune D (C c) = C c from (retune D).commutes c]
  exact wick_constant_left D c q

private theorem integerWick_constant_right (c : ℂ) (p : Oscillator D) :
    integerWick D p (C c) = c * p.coeff 0 := by
  rw [integerWick_apply]
  rw [wick_constant_right D c (retune D p), retune_constant]

theorem integerWick_kappa (p q : Oscillator D) :
    integerWick D (kappaOsc p) (kappaOsc q) =
      conj (integerWick D p q) := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
      rw [kappaOsc_C, integerWick_constant_left, kappaOsc_coeff,
        integerWick_constant_left]
      simp
  | add p r hp hr =>
      simp only [kappaOsc_add, map_add, LinearMap.add_apply, hp, hr, map_add]
  | mul_X p x hp =>
      rcases x with ⟨i,k⟩
      conv_lhs => rw [mul_comm p]
      conv_rhs => rw [mul_comm p]
      rw [kappaOsc_mul, kappaOsc_X, integerWick_creation]
      have harg : -((k : ℂ) + 1) •
          LatticeActualAnnihilation.annihilate D i k (kappaOsc q) =
        kappaOsc (-((k : ℂ) + 1) •
          LatticeActualAnnihilation.annihilate D i k q) := by
        rw [kappaOsc_smul, kappaOsc_annihilate]
        simp
      rw [harg, hp]
      rw [integerWick_creation]

theorem kappaOsc_sigma (p : Oscillator D) :
    kappaOsc (sigma D p) = sigma D (kappaOsc p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [kappaOsc]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
      rcases x with ⟨i,k⟩
      rw [map_mul, sigma_X, kappaOsc_mul,
        show -X (i,k) = (-1 : ℂ) • X (i,k) by simp,
        kappaOsc_smul, kappaOsc_X, kappaOsc_mul, kappaOsc_X, hp]
      rw [map_mul, sigma_X]
      simp [smul_eq_mul]

theorem kappaCarrier_theta (x : Carrier D) :
    kappaCarrier (theta D x) = theta D (kappaCarrier x) := by
  change kappaCarrier (thetaLinear D x) = thetaLinear D (kappaCarrier x)
  induction x using Finsupp.induction_linear with
  | zero => simp [kappaCarrier]
  | add x y hx hy => simp only [map_add, kappaCarrier_add, hx, hy]
  | single a p =>
      rw [theta_single, kappaCarrier_single, kappaCarrier_single, theta_single]
      rw [kappaOsc_sigma]

theorem sourcePairing_kappa (u v : Carrier D) :
    sourcePairing D (kappaCarrier u) (kappaCarrier v) =
      conj (sourcePairing D u v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw =>
      rw [kappaCarrier_add]
      simp only [LinearMap.add_apply, hu, hw, map_add]
  | single a p =>
      rw [kappaCarrier_single, sourcePairing_single,
        sourcePairing_single]
      simp only [kappaCarrier, Finsupp.mapRange_apply]
      rw [integerWick_kappa]

theorem conjugateH_eq_H (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    H.map (starRingEnd ℂ) = H := by
  have hGconj : (gramComplex D).map (starRingEnd ℂ) = gramComplex D := by
    ext i j
    simp [gramComplex]
  have hconj : H.map (starRingEnd ℂ) * gramComplex D = 1 := by
    calc
      H.map (starRingEnd ℂ) * gramComplex D =
          H.map (starRingEnd ℂ) * (gramComplex D).map (starRingEnd ℂ) := by
            rw [hGconj]
      _ = (H * gramComplex D).map (starRingEnd ℂ) := by
            rw [Matrix.map_mul]
      _ = (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ).map (starRingEnd ℂ) := by
            rw [hHG]
      _ = 1 := by simp
  exact Matrix.left_inv_eq_left_inv hconj hHG

theorem transposeH_eq_H (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    H.transpose = H := by
  have hGt : (gramComplex D).transpose = gramComplex D := by
    ext i j
    simp [gramComplex, D.symmetric]
  have htrans : H.transpose * gramComplex D = 1 := by
    calc
      H.transpose * gramComplex D =
          H.transpose * (gramComplex D).transpose := by rw [hGt]
      _ = (gramComplex D * H).transpose := by rw [Matrix.transpose_mul]
      _ = (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ).transpose := by rw [hGH]
      _ = 1 := by simp
  exact Matrix.left_inv_eq_left_inv htrans hHG

theorem kappaCarrier_involutive (x : Carrier D) :
    kappaCarrier (kappaCarrier x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [kappaCarrier_add, hx, hy, map_add]
  | single a p => simp [kappaCarrier, kappaOsc_involutive]

theorem theta_square (x : Carrier D) : theta D (theta D x) = x := by
  change thetaLinear D (thetaLinear D x) = x
  exact theta_involutive D x

def Hm (x y : Carrier D) : ℂ :=
  sourcePairing D (theta D (kappaCarrier x)) y

theorem Hm_alt (x y : Carrier D) :
    Hm x y = sourcePairing D (kappaCarrier x) (theta D y) := by
  unfold Hm
  conv_lhs => rw [← theta_square y]
  exact sourcePairing_theta D (kappaCarrier x) (theta D y)

theorem Hm_hermitian (x y : Carrier D) :
    Hm x y = conj (Hm y x) := by
  calc
    Hm x y = sourcePairing D (kappaCarrier x) (theta D y) := Hm_alt x y
    _ = sourcePairing D (theta D y) (kappaCarrier x) :=
      sourcePairing_symmetric D _ _
    _ = sourcePairing D (kappaCarrier (theta D (kappaCarrier y)))
        (kappaCarrier x) := by
      simp only [kappaCarrier_theta, kappaCarrier_involutive]
    _ = conj (sourcePairing D (theta D (kappaCarrier y)) x) :=
      sourcePairing_kappa (theta D (kappaCarrier y)) x
    _ = conj (Hm y x) := rfl

theorem Hm_neutralMode (i : Fin D.rank) (m : ℤ) (x y : Carrier D) :
    Hm (neutralMode D i m x) y =
      Hm x (neutralMode D i (-m) y) := by
  calc
    Hm (neutralMode D i m x) y =
        sourcePairing D (theta D (kappaCarrier (neutralMode D i m x))) y := rfl
    _ = sourcePairing D (theta D (neutralMode D i m (kappaCarrier x))) y := by
      rw [kappaCarrier_neutralMode]
    _ = sourcePairing D (-(neutralMode D i m (theta D (kappaCarrier x)))) y := by
      rw [theta_neutralMode]
    _ = -sourcePairing D (neutralMode D i m (theta D (kappaCarrier x))) y := by
      simp
    _ = sourcePairing D (theta D (kappaCarrier x))
        (neutralMode D i (-m) y) := by
      rw [sourcePairing_neutralMode]
      simp
    _ = Hm x (neutralMode D i (-m) y) := rfl

theorem Hm_neutralMode_comp (i j : Fin D.rank) (k l : ℤ)
    (x y : Carrier D) :
    Hm (neutralMode D i k (neutralMode D j l x)) y =
      Hm x (neutralMode D j (-l) (neutralMode D i (-k) y)) := by
  calc
    Hm (neutralMode D i k (neutralMode D j l x)) y =
        Hm (neutralMode D j l x) (neutralMode D i (-k) y) :=
      Hm_neutralMode i k (neutralMode D j l x) y
    _ = Hm x (neutralMode D j (-l) (neutralMode D i (-k) y)) :=
      Hm_neutralMode j l x (neutralMode D i (-k) y)

private theorem neutralMode_commute_of_sum_ne_zero (i j : Fin D.rank)
    (m n : ℤ) (h : m + n ≠ 0) (v : Carrier D) :
    neutralMode D i m (neutralMode D j n v) =
      neutralMode D j n (neutralMode D i m v) := by
  have hc := congrArg (fun f : Module.End ℂ (Carrier D) => f v)
    (neutralMode_heisenberg D i j m n)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply] at hc
  simp [h] at hc
  exact sub_eq_zero.mp hc

theorem normalSummand_adjoint (i j : Fin D.rank) (k l : ℤ)
    (x y : Carrier D) :
    Hm (normalSummand D i j k l x) y =
      Hm x (normalSummand D j i (-l) (-k) y) := by
  by_cases hk : k < 0
  · calc
      Hm (normalSummand D i j k l x) y =
          Hm (neutralMode D i k (neutralMode D j l x)) y := by
            simp [normalSummand, hk, Module.End.mul_apply]
      _ = Hm x (neutralMode D j (-l) (neutralMode D i (-k) y)) :=
        Hm_neutralMode_comp i j k l x y
      _ = Hm x (normalSummand D j i (-l) (-k) y) := by
        by_cases hl : -l < 0
        · have hlpos : 0 < l := by omega
          simp [normalSummand, hlpos, Module.End.mul_apply]
        · rw [normalSummand, if_neg hl]
          simp only [Module.End.mul_apply]
          apply congrArg (Hm x)
          apply neutralMode_commute_of_sum_ne_zero j i (-l) (-k)
          omega
  · calc
      Hm (normalSummand D i j k l x) y =
          Hm (neutralMode D j l (neutralMode D i k x)) y := by
            simp [normalSummand, hk, Module.End.mul_apply]
      _ = Hm x (neutralMode D i (-k) (neutralMode D j (-l) y)) :=
        Hm_neutralMode_comp j i l k x y
      _ = Hm x (normalSummand D j i (-l) (-k) y) := by
        by_cases hl : -l < 0
        · have hlpos : 0 < l := by omega
          simp [normalSummand, hlpos, Module.End.mul_apply]
          apply congrArg (Hm x)
          apply neutralMode_commute_of_sum_ne_zero i j (-k) (-l)
          omega
        · have hlnonpos : ¬ 0 < l := by omega
          simp [normalSummand, hlnonpos, Module.End.mul_apply]

@[simp] theorem Hm_zero_left (y : Carrier D) : Hm (0 : Carrier D) y = 0 := by
  simp [Hm]

@[simp] theorem Hm_zero_right (x : Carrier D) : Hm x 0 = 0 := by
  simp [Hm]

theorem Hm_add_left (x y z : Carrier D) :
    Hm (x + y) z = Hm x z + Hm y z := by
  simp [Hm]

theorem Hm_add_right (x y z : Carrier D) :
    Hm x (y + z) = Hm x y + Hm x z := by
  simp [Hm]

theorem Hm_smul_left (c : ℂ) (x y : Carrier D) :
    Hm (c • x) y = conj c * Hm x y := by
  simp [Hm, smul_eq_mul]

theorem Hm_smul_right (c : ℂ) (x y : Carrier D) :
    Hm x (c • y) = c * Hm x y := by
  simp [Hm, smul_eq_mul]

private def Hm_leftAdd (y : Carrier D) : Carrier D →+ ℂ where
  toFun x := Hm x y
  map_zero' := Hm_zero_left y
  map_add' x z := Hm_add_left x z y

private def Hm_rightAdd (x : Carrier D) : Carrier D →+ ℂ where
  toFun y := Hm x y
  map_zero' := Hm_zero_right x
  map_add' y z := Hm_add_right x y z

private theorem Hm_finsum_left {ι : Type} (f : ι → Carrier D)
    (hf : Function.HasFiniteSupport f) (y : Carrier D) :
    Hm (∑ᶠ a, f a) y = ∑ᶠ a, Hm (f a) y := by
  exact (Hm_leftAdd y).map_finsum hf

private theorem Hm_finsum_right {ι : Type} (f : ι → Carrier D)
    (hf : Function.HasFiniteSupport f) (x : Carrier D) :
    Hm x (∑ᶠ a, f a) = ∑ᶠ a, Hm x (f a) := by
  exact (Hm_rightAdd x).map_finsum hf

private theorem Hm_finset_sum_left {ι : Type} (s : Finset ι)
    (f : ι → Carrier D) (y : Carrier D) :
    Hm (∑ a ∈ s, f a) y = ∑ a ∈ s, Hm (f a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Hm_zero_left]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Hm_add_left, ih]

private theorem Hm_finset_sum_right {ι : Type} (s : Finset ι)
    (f : ι → Carrier D) (x : Carrier D) :
    Hm x (∑ a ∈ s, f a) = ∑ a ∈ s, Hm x (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Hm_zero_right]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Hm_add_right, ih]

private theorem Hm_normal_finsum_reindex (i j : Fin D.rank) (m : ℤ)
    (x y : Carrier D) :
    (∑ᶠ k : ℤ, Hm (normalSummand D i j k (m-k) x) y) =
      ∑ᶠ k : ℤ, Hm x (normalSummand D j i k (-m-k) y) := by
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (-m))]
  apply finsum_congr
  intro k
  have h := normalSummand_adjoint i j k (m-k) x y
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

set_option maxHeartbeats 10000000 in
theorem Hm_sugawaraMode (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m : ℤ) (x y : Carrier D) :
    Hm (sugawaraMode D H m x) y =
      Hm x (sugawaraMode D H (-m) y) := by
  classical
  have hconj := conjugateH_eq_H H hHG hGH
  have htrans := transposeH_eq_H H hHG hGH
  have hcoeff (i j : Fin D.rank) : conj (H j i) = H i j := by
    have hc := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M j i) hconj
    have ht := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i j) htrans
    simpa using hc.trans ht
  have hleft :
      Hm (sugawaraMode D H m x) y =
        (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          conj (H i j) * ∑ᶠ k : ℤ,
            Hm (normalSummand D i j k (m-k) x) y := by
    rw [sugawaraMode_finsum, Hm_smul_left]
    have hc : conj ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      rw [map_inv₀]
      rw [show conj (2 : ℂ) = 2 by
        apply Complex.ext <;> norm_num]
    rw [hc]
    congr 1
    rw [Hm_finset_sum_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Hm_finset_sum_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Hm_smul_left]
    have hf := Hm_finsum_left (fun k : ℤ => normalSummand D i j k (m-k) x)
      (normalSummand_finite D i j m x) y
    exact congrArg (fun z : ℂ => conj (H i j) * z) hf
  have hright :
      Hm x (sugawaraMode D H (-m) y) =
        (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j * ∑ᶠ k : ℤ,
            Hm x (normalSummand D i j k (-m-k) y) := by
    rw [sugawaraMode_finsum, Hm_smul_right]
    rw [Hm_finset_sum_right]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Hm_finset_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Hm_smul_right]
    have hf := Hm_finsum_right (fun k : ℤ => normalSummand D i j k (-m-k) y)
      (normalSummand_finite D i j (-m) y) x
    exact congrArg (fun z : ℂ => H i j * z) hf
  have hreindex :
      (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        conj (H i j) * ∑ᶠ k : ℤ,
          Hm (normalSummand D i j k (m-k) x) y) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        conj (H i j) * ∑ᶠ k : ℤ,
          Hm x (normalSummand D j i k (-m-k) y) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z : ℂ => conj (H i j) * z)
      (Hm_normal_finsum_reindex i j m x y)
  have hswap :
      (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        conj (H i j) * ∑ᶠ k : ℤ,
          Hm x (normalSummand D j i k (-m-k) y)) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j * ∑ᶠ k : ℤ,
          Hm x (normalSummand D i j k (-m-k) y) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff]
  calc
    Hm (sugawaraMode D H m x) y =
        (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          conj (H i j) * ∑ᶠ k : ℤ,
            Hm (normalSummand D i j k (m-k) x) y := hleft
    _ = (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          conj (H i j) * ∑ᶠ k : ℤ,
            Hm x (normalSummand D j i k (-m-k) y) := by rw [hreindex]
    _ = (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j * ∑ᶠ k : ℤ,
            Hm x (normalSummand D i j k (-m-k) y) := by rw [hswap]
    _ = Hm x (sugawaraMode D H (-m) y) := hright.symm

end D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
