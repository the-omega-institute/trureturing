/- GID: D5/S3/VertexAlgebra/OriginalSourcePairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/OriginalSourcePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/algebra/vertex/vertexoperator, mathlib/algebra/mvpolynomial/pderiv]
   utility: none
   digest: Integer-frequency retuning of the signed polynomial Wick form and its finite-charge lift to the original Carrier.
-/

import D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
import D5.S3.VertexAlgebra.LatticeInvolution
import Batteries.Tactic.OpenPrivate

/-!
The literal original Carrier bilinear form is obtained by retuning the existing
signed oscillator Wick supplier from half-frequency to integer-frequency
contractions.  The finite charge lift retains the original Finsupp carrier,
including rank zero, and proves normalization, symmetry and both-sided
nondegeneracy under the supplier's determinant-unit hypothesis.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

namespace D5.S3.VertexAlgebra.OriginalSourcePairing

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeAllStateField
open MvPolynomial
open SignedOscillatorWick
open LatticeInvolution
open private wick_constant_left wick_constant_right from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

/-! The scalar that changes the supplier's half-frequency contraction to the
integer contraction. -/

def integerScale (k : ℕ) : ℂ := ((k : ℂ) + 1) / frequency (k : ℤ)

theorem frequency_nat_ne_zero (k : ℕ) : frequency (k : ℤ) ≠ 0 := by
  rw [frequency]
  intro h
  have hr := congrArg Complex.re h
  have hk : (0 : ℝ) ≤ k := by positivity
  norm_num at hr
  linarith

theorem integerScale_ne_zero (k : ℕ) : integerScale k ≠ 0 := by
  unfold integerScale
  apply div_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    have hk : (0 : ℝ) ≤ k := by positivity
    norm_num at hr
    linarith
  · exact frequency_nat_ne_zero k

theorem integerScale_mul_frequency (k : ℕ) :
    integerScale k * frequency (k : ℤ) = (k : ℂ) + 1 := by
  unfold integerScale
  exact div_mul_cancel₀ _ (frequency_nat_ne_zero k)

def retuneMatrix (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  integerScale k • (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def retuneInverseMatrix (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (integerScale k)⁻¹ • (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem retuneMatrix_mul_inverse (D : LatticeData) (k : ℕ) :
    retuneMatrix D k * retuneInverseMatrix D k = 1 := by
  rw [retuneMatrix, retuneInverseMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_inv_cancel₀ (integerScale_ne_zero k), one_smul,
    Matrix.one_mul]

theorem retuneInverse_mul_matrix (D : LatticeData) (k : ℕ) :
    retuneInverseMatrix D k * retuneMatrix D k = 1 := by
  rw [retuneMatrix, retuneInverseMatrix, smul_mul_assoc, mul_smul_comm,
    smul_smul, inv_mul_cancel₀ (integerScale_ne_zero k), one_smul,
    Matrix.one_mul]

def retune (D : LatticeData) : Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv
    (fun k => retuneMatrix D k) (fun k => retuneInverseMatrix D k)
    (retuneMatrix_mul_inverse D) (retuneInverse_mul_matrix D)

theorem retune_X (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    retune D (X (i,k)) = integerScale k • X (i,k) := by
  change OriginalCurrentMetric.substitution (fun k => retuneMatrix D k) (X (i,k)) = _
  rw [OriginalCurrentMetric.substitution_X,
    OriginalCurrentMetric.variableImage]
  simp [retuneMatrix, Matrix.one_apply, integerScale]

theorem retune_mul (D : LatticeData) (p q : Oscillator D) :
    retune D (p * q) = retune D p * retune D q := by
  exact map_mul (retune D) p q

theorem retune_smul (D : LatticeData) (c : ℂ) (p : Oscillator D) :
    retune D (c • p) = c • retune D p := by
  exact map_smul (retune D) c p

theorem retune_constant (D : LatticeData) (p : Oscillator D) :
    (retune D p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [show retune D (MvPolynomial.C c) = MvPolynomial.C c from
        (retune D).commutes c]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
      rcases x with ⟨i,k⟩
      rw [retune_mul, retune_X]
      rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc]
      rw [MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
      simp

def integerWick (D : LatticeData) :
    LinearMap.BilinForm ℂ (Oscillator D) :=
  (wick D).compLeft (retune D).toLinearMap

@[simp] theorem integerWick_apply (D : LatticeData) (p q : Oscillator D) :
    integerWick D p q = wick D (retune D p) q := rfl

theorem integerWick_creation (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    integerWick D (X (i,k) * p) q =
      integerWick D p (-((k : ℂ) + 1) • LatticeActualAnnihilation.annihilate D i k q) := by
  rw [integerWick_apply, retune_mul, retune_X, smul_mul_assoc,
    map_smul]
  change integerScale k * wick D (X (i,k) * retune D p) q =
    wick D (retune D p) (-((k : ℂ) + 1) • LatticeActualAnnihilation.annihilate D i k q)
  rw [SignedOscillatorWick.wick_creation]
  simp only [LinearMap.map_smul]
  rw [← integerScale_mul_frequency]
  ring

theorem retune_pderiv (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) :
    MvPolynomial.pderiv (i,k) (retune D p) =
      integerScale k • retune D (MvPolynomial.pderiv (i,k) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show retune D (C c) = C c from (retune D).commutes c]
    simp
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    rcases x with ⟨l,m⟩
    rw [retune_mul, retune_X, (MvPolynomial.pderiv (i,k)).leibniz]
    simp only [map_add, map_mul, map_smul, hp]
    by_cases h : k = m
    · subst m
      by_cases hil : i = l
      · subst l
        simp [MvPolynomial.pderiv_X, retune_X, smul_mul_assoc]
      · simp [MvPolynomial.pderiv_X, Prod.mk.injEq, hil, retune_X,
          smul_mul_assoc]
    · simp [MvPolynomial.pderiv_X, Prod.mk.injEq, h, Ne.symm h,
        retune_X]

theorem retune_annihilate (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) :
    retune D (LatticeActualAnnihilation.annihilate D i k p) =
      (integerScale k)⁻¹ •
        LatticeActualAnnihilation.annihilate D i k (retune D p) := by
  rw [← LatticeActualAnnihilation.annihilation_apply]
  rw [← LatticeActualAnnihilation.annihilation_apply]
  unfold LatticeActualAnnihilation.annihilationDerivation
  change retune D ((Derivation.coeFnAddMonoidHom
    (∑ a : Fin D.rank, (D.G i a : ℂ) • MvPolynomial.pderiv (a,k))) p) =
    (integerScale k)⁻¹ •
      (Derivation.coeFnAddMonoidHom
        (∑ a : Fin D.rank, (D.G i a : ℂ) • MvPolynomial.pderiv (a,k))) (retune D p)
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply, map_smul, retune_pderiv]
  rw [Finset.smul_sum]
  rw [map_sum]
  simp only [map_smul, retune_pderiv]
  apply Finset.sum_congr rfl
  intro a ha
  have hscalar : (integerScale k)⁻¹ * ((D.G i a : ℂ) * integerScale k) =
      (D.G i a : ℂ) := by
    field_simp [integerScale_ne_zero]
  simp only [smul_smul]
  rw [hscalar]

theorem integerWick_lowering (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    integerWick D (-((k : ℂ) + 1) • LatticeActualAnnihilation.annihilate D i k p) q =
      integerWick D p (X (i,k) * q) := by
  rw [integerWick_apply, integerWick_apply, retune_smul,
    retune_annihilate]
  have hscale : ((k : ℂ) + 1) * (integerScale k)⁻¹ =
      frequency (k : ℤ) := by
    unfold integerScale
    field_simp [frequency_nat_ne_zero]
  rw [smul_smul]
  have harg : -((k : ℂ) + 1) * (integerScale k)⁻¹ =
      -frequency (k : ℤ) := by
    calc
      -((k : ℂ) + 1) * (integerScale k)⁻¹ =
          -(((k : ℂ) + 1) * (integerScale k)⁻¹) := by ring
      _ = -frequency (k : ℤ) := by rw [hscale]
  rw [harg, SignedOscillatorWick.wick_lowering]

theorem integerWick_symmetric (D : LatticeData) (p q : Oscillator D) :
    integerWick D p q = integerWick D q p := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
      rw [integerWick_apply,
        show retune D (MvPolynomial.C c) = MvPolynomial.C c from
          (retune D).commutes c,
        wick_constant_left, integerWick_apply, wick_constant_right,
        retune_constant]
  | add p r hp hr =>
      simp only [integerWick_apply, map_add, LinearMap.add_apply, hp, hr]
  | mul_X p x hp =>
      rcases x with ⟨i,k⟩
      rw [mul_comm p, integerWick_creation, ← integerWick_lowering]
      exact hp _

theorem integerWick_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det) :
    (integerWick D).Nondegenerate := by
  let h := SignedOscillatorWick.wick_nondegenerate D hu
  constructor
  · intro p hp
    apply (retune D).injective
    exact h.1 _ hp
  · intro q hq
    apply h.2 q
    intro p
    obtain ⟨r, rfl⟩ := (retune D).surjective p
    exact hq r

/-! The charge lift is a finite-support sum. `Finsupp.lsum` supplies the
linearity in the first Carrier slot; the inner linear map supplies the second.
-/

def chargeFunctional (D : LatticeData) (a : Charge D) :
    Oscillator D →ₗ[ℂ] (Carrier D →ₗ[ℂ] ℂ) where
  toFun p := (integerWick D p).comp (Finsupp.lapply (-a))
  map_add' p q := by
    ext v
    simp [LinearMap.BilinForm.add_left]
  map_smul' c p := by
    ext v
    simp [LinearMap.BilinForm.smul_left]

def sourcePairing (D : LatticeData) :
    LinearMap.BilinForm ℂ (Carrier D) :=
  Finsupp.lsum ℂ (chargeFunctional D)

@[simp] theorem sourcePairing_single (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (v : Carrier D) :
    sourcePairing D (Finsupp.single a p) v = integerWick D p (v (-a)) := by
  simp [sourcePairing, chargeFunctional]

theorem sourcePairing_single_single (D : LatticeData) (a b : Charge D)
    (p q : Oscillator D) :
    sourcePairing D (Finsupp.single a p) (Finsupp.single b q) =
      if b = -a then integerWick D p q else 0 := by
  rw [sourcePairing_single]
  by_cases h : b = -a
  · subst b
    simp
  · simp [Finsupp.single_apply, h]

theorem sourcePairing_symmetric (D : LatticeData) (v w : Carrier D) :
    sourcePairing D v w = sourcePairing D w v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw]
  | single a p =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp [map_add, hv, hw]
      | single b q =>
          by_cases h : b = -a
          · subst b
            rw [sourcePairing_single_single, sourcePairing_single_single]
            simp only [neg_neg, if_pos]
            exact integerWick_symmetric D p q
          · have h' : a ≠ -b := by
              intro hab
              apply h
              simpa using (congrArg Neg.neg hab).symm
            simp [sourcePairing_single_single, h, h', integerWick_symmetric]

theorem sourcePairing_vacuum (D : LatticeData) :
    sourcePairing D (vacuum D) (vacuum D) = 1 := by
  change sourcePairing D (Finsupp.single 0 1) (Finsupp.single 0 1) = 1
  rw [sourcePairing_single_single]
  simp only [neg_zero, if_pos]
  change wick D (retune D 1) 1 = 1
  have hone : retune D (1 : Oscillator D) = 1 := (retune D).map_one
  rw [hone]
  change wick D (MvPolynomial.C 1) 1 = 1
  rw [wick_constant_left]
  simp

theorem sourcePairing_charge_single (D : LatticeData) (v : Carrier D)
    (a : Charge D) (q : Oscillator D) :
    sourcePairing D v (Finsupp.single (-a) q) = integerWick D (v a) q := by
  classical
  have hv : (∑ b ∈ v.support, Finsupp.single b (v b)) = v := Finsupp.sum_single v
  conv_lhs => rw [← hv]
  rw [map_sum]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single a]
  · simp [chargeFunctional]
  · intro b hb hba
    rw [sourcePairing_single]
    simp [hba]
  · intro hzero
    rw [sourcePairing_single]
    have hva : v a = 0 := by
      by_contra hva
      exact hzero (Finsupp.mem_support_iff.mpr hva)
    simp [hva]

theorem sourcePairing_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det) :
    (sourcePairing D).Nondegenerate := by
  constructor
  · intro v hv
    apply Finsupp.ext
    intro a
    change v a = 0
    by_contra hne
    have hnot : ¬ ∀ q : Oscillator D, integerWick D (v a) q = 0 := by
      intro hz
      exact hne ((integerWick_nondegenerate D hu).1 (v a) hz)
    obtain ⟨q, hq⟩ := not_forall.mp hnot
    exact hq (sourcePairing_charge_single D v a q ▸ hv (Finsupp.single (-a) q))
  · intro v hv
    apply Finsupp.ext
    intro a
    change v a = 0
    by_contra hne
    have hnot : ¬ ∀ p : Oscillator D, integerWick D p (v a) = 0 := by
      intro hz
      exact hne ((integerWick_nondegenerate D hu).2 (v a) hz)
    obtain ⟨p, hp⟩ := not_forall.mp hnot
    have hzero := hv (Finsupp.single (-a) p)
    rw [sourcePairing_single] at hzero
    exact hp (by simpa using hzero)

end D5.S3.VertexAlgebra.OriginalSourcePairing
