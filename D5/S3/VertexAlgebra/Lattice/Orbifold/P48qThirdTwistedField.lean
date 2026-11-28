/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qThirdTwistedField
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48q charged field on oscillator polynomials and shifted momenta. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeContraction
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
The charged P48q field of Bakalov–Kac, arXiv:math/0402315v3,
(4.26)–(4.29), in the cover coordinate x with z = x^3.
The creation exponential and polynomial evaluation follow the constructions
in LatticeGeneratingFieldLocality, with the actual twisted mode coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum U)
open ThirdEigenspacePairing
open P48qNativeContraction (fourierComponent)
open P48qFixedRankCertificateDraft (nebeOrderThree)
open P48qGramCertificateDraft (nebeGram gram_isometry_certificate)
open Module MvPolynomial
open scoped BigOperators Matrix

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "N" => ThirdTwistedChargeAction.N lattice g

abbrev Cartan := Fin 48 → ℂ
abbrev Fixed := p48qAction.eigenspace (1 : ℂ)

/-- Both bases are in the eigenspace of the actual P48q row action. -/
structure FixedDualBases where
  creators : Basis (Fin 16) ℂ Fixed
  annihilators : Basis (Fin 16) ℂ Fixed
  pairing (i j : Fin 16) :
    p48qForm (creators i : Cartan) (annihilators j : Cartan) = if i = j then 1 else 0

private theorem zetaPrimitive : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

abbrev Mode := Fin 16 × ℕ
abbrev Fock := MvPolynomial Mode ℂ
abbrev State := Momentum →₀ Fock

/-- A variable with second index m is the creation mode of frequency -(m+1)/3. -/
def frequency (j : Mode) : ℕ := j.2 + 1

/-- For n = m+1, the negative mode -n/3 projects onto the ζ^n eigenspace. -/
def creator (B : FixedDualBases) (j : Mode) : Cartan :=
  if frequency j % 3 = 0 then (B.creators j.1 : Cartan)
  else if frequency j % 3 = 1 then (p48qBasis zetaPrimitive j.1 : Cartan)
  else (p48qOppositeBasis zetaPrimitive j.1 : Cartan)

/-- The positive mode n/3 uses the opposite eigenspace and the Gram-dual basis. -/
def annihilatorDual (B : FixedDualBases) (j : Mode) : Cartan :=
  if frequency j % 3 = 0 then (B.annihilators j.1 : Cartan)
  else if frequency j % 3 = 1 then (p48qOppositeBasis zetaPrimitive j.1 : Cartan)
  else (p48qBasis zetaPrimitive j.1 : Cartan)

private theorem formSymmetric : p48qForm.IsSymm := by
  change ((lattice.G.map (Int.castRingHom ℂ)).toBilin').IsSymm
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  exact Matrix.IsSymm.ext fun i j => congrArg (Int.castRingHom ℂ) (lattice.symmetric j i)

theorem pair_modes (B : FixedDualBases) (i j : Fin 16) (m : ℕ) :
    p48qForm (creator B (i, m)) (annihilatorDual B (j, m)) = if i = j then 1 else 0 := by
  by_cases h0 : (m + 1) % 3 = 0
  · simpa only [creator, annihilatorDual, frequency, if_pos h0] using B.pairing i j
  by_cases h1 : (m + 1) % 3 = 1
  · simpa only [creator, annihilatorDual, frequency, if_neg h0, if_pos h1]
      using p48q_pair_bases zetaPrimitive i j
  simp only [creator, annihilatorDual, frequency, if_neg h0, if_neg h1]
  exact (formSymmetric.eq _ _).trans (by
    simpa only [eq_comm] using p48q_pair_bases zetaPrimitive j i)

def chargeVector (a : Charge lattice) : Cartan := fun i => (a i : ℂ)

/-- At cover frequency n this is ζ^n, reduced modulo the order. -/
def modeRoot (j : Mode) : ℂ := ζ ^ (frequency j % 3)

theorem creator_action (B : FixedDualBases) (j : Mode) :
    p48qAction (creator B j) = modeRoot j • creator B j := by
  by_cases h0 : frequency j % 3 = 0
  · simpa [creator, modeRoot, h0]
      using Module.End.mem_eigenspace_iff.mp (B.creators j.1).property
  by_cases h1 : frequency j % 3 = 1
  · simpa [creator, modeRoot, h0, h1]
      using Module.End.mem_eigenspace_iff.mp (p48qBasis zetaPrimitive j.1).property
  have h2 : frequency j % 3 = 2 := by omega
  simpa [creator, modeRoot, h2]
    using Module.End.mem_eigenspace_iff.mp (p48qOppositeBasis zetaPrimitive j.1).property

theorem annihilatorDual_action (B : FixedDualBases) (j : Mode) :
    p48qAction (annihilatorDual B j) = modeRoot j ^ 2 • annihilatorDual B j := by
  by_cases h0 : frequency j % 3 = 0
  · simpa [annihilatorDual, modeRoot, h0]
      using Module.End.mem_eigenspace_iff.mp (B.annihilators j.1).property
  by_cases h1 : frequency j % 3 = 1
  · simpa [annihilatorDual, modeRoot, h0, h1]
      using Module.End.mem_eigenspace_iff.mp (p48qOppositeBasis zetaPrimitive j.1).property
  have h2 : frequency j % 3 = 2 := by omega
  have hpow : (ζ ^ 2) ^ 2 = ζ := by
    calc
      (ζ ^ 2) ^ 2 = ζ ^ 3 * ζ := by ring
      _ = ζ := by rw [zetaPrimitive.pow_eq_one, one_mul]
  simpa [annihilatorDual, modeRoot, h2, hpow]
    using Module.End.mem_eigenspace_iff.mp (p48qBasis zetaPrimitive j.1).property

private theorem formInvariant (v w : Cartan) :
    p48qForm (p48qAction v) (p48qAction w) = p48qForm v w := by
  let c := Int.castRingHom ℂ
  let G := c.mapMatrix nebeGram
  let A := c.mapMatrix nebeOrderThreeᵀ
  have h : Aᵀ * G * A = G := by
    change c.mapMatrix nebeOrderThree * c.mapMatrix nebeGram * c.mapMatrix nebeOrderThreeᵀ = G
    rw [← map_mul, ← map_mul, gram_isometry_certificate]
  change (G.toBilin'.comp A.toLin' A.toLin') v w = G.toBilin' v w
  rw [Matrix.toBilin'_comp, h]

private theorem action_chargeVector (a : Charge lattice) :
    p48qAction (chargeVector a) = chargeVector (g a) := by
  change (nebeOrderThreeᵀ).map (Int.castRingHom ℂ) *ᵥ chargeVector a = chargeVector (g a)
  rw [P48qTwistedChargeAction.g_apply, ← Matrix.mulVec_transpose]
  exact funext fun i => ((Int.castRingHom ℂ).map_mulVec nebeOrderThreeᵀ a i).symm

theorem fourierComponent_mem (a : Charge lattice) (u : ℂ) (hu : u ^ 3 = 1) :
    fourierComponent u a ∈ p48qAction.eigenspace (u ^ 2) := by
  have hu1 : u ^ 2 * u = 1 := by rw [← pow_succ, hu]
  have hu2 : u ^ 2 * u ^ 2 = u := by
    calc
      u ^ 2 * u ^ 2 = u ^ 3 * u := by ring
      _ = u := by rw [hu, one_mul]
  rw [Module.End.mem_eigenspace_iff]
  let s : Cartan := chargeVector a + u • chargeVector (g a) + u ^ 2 • chargeVector (g (g a))
  change p48qAction ((3 : ℂ)⁻¹ • s) = u ^ 2 • ((3 : ℂ)⁻¹ • s)
  rw [map_smul, smul_comm (u ^ 2) ((3 : ℂ)⁻¹)]
  apply congrArg (fun v : Cartan => (3 : ℂ)⁻¹ • v)
  simp only [s, map_add, map_smul, action_chargeVector, g_cube, smul_add, smul_smul,
    hu1, hu2, one_smul]
  abel

private theorem pair_fourierComponent (a : Charge lattice) (u : ℂ) (v : Cartan)
    (hv : p48qAction v = u • v) :
    p48qForm (fourierComponent u a) v = p48qForm (chargeVector a) v := by
  have hstep (b : Charge lattice) :
      u * p48qForm (chargeVector (g b)) v = p48qForm (chargeVector b) v := by
    simpa only [action_chargeVector, hv, LinearMap.BilinForm.smul_right]
      using formInvariant (chargeVector b) v
  have hstep2 : u ^ 2 * p48qForm (chargeVector (g (g a))) v =
      p48qForm (chargeVector a) v := by
    rw [pow_two, mul_assoc, hstep (g a), hstep a]
  change p48qForm ((3 : ℂ)⁻¹ •
    (chargeVector a + u • chargeVector (g a) + u ^ 2 • chargeVector (g (g a)))) v = _
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left,
    hstep2, hstep a]
  ring

/-- Coordinates of the charge in the negative-mode basis, obtained by pairing
against the positive-mode dual vectors. -/
def creationCoordinate (B : FixedDualBases) (a : Charge lattice) (j : Mode) : ℂ :=
  p48qForm (chargeVector a) (annihilatorDual B j)

/-- Pairing of the positive-mode projection of the charge with the creator.
The Heisenberg bracket multiplies this pairing by frequency/3. -/
def annihilationPairing (B : FixedDualBases) (a : Charge lattice) (j : Mode) : ℂ :=
  p48qForm (chargeVector a) (creator B j)

theorem creationCoordinate_projected (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    creationCoordinate B a j =
      p48qForm (fourierComponent (modeRoot j ^ 2) a) (annihilatorDual B j) :=
  (pair_fourierComponent a _ _ (annihilatorDual_action B j)).symm

theorem annihilationPairing_projected (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    annihilationPairing B a j = p48qForm (fourierComponent (modeRoot j) a) (creator B j) :=
  (pair_fourierComponent a _ _ (creator_action B j)).symm

/-- The positive charge mode (m+1)/3 on the Fock polynomial ring. -/
def positiveAnnihilator (B : FixedDualBases) (a : Charge lattice) (m : ℕ) :
    Module.End ℂ Fock :=
  ∑ i : Fin 16, (((frequency (i, m) : ℂ) / 3) * annihilationPairing B a (i, m)) •
    (pderiv (i, m) : Derivation ℂ Fock Fock).toLinearMap

theorem positiveAnnihilator_X (B : FixedDualBases) (a : Charge lattice) (m : ℕ) (j : Mode) :
    positiveAnnihilator B a m (X j) =
      if m = j.2 then
        (((frequency j : ℂ) / 3) * annihilationPairing B a j) • (1 : Fock)
      else 0 := by
  classical
  rcases j with ⟨i, n⟩
  simp only [positiveAnnihilator, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  by_cases h : m = n
  · subst m
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [pderiv_X_self]
    · intro j _ hj
      have hpair : (i, n) ≠ (j, n) := fun he => hj (congrArg Prod.fst he).symm
      rw [pderiv_X_of_ne hpair, smul_zero]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hpair : (i, n) ≠ (j, m) := fun he => h (congrArg Prod.snd he).symm
    rw [pderiv_X_of_ne hpair, smul_zero]

theorem positiveAnnihilator_eq_zero_of_not_mem (B : FixedDualBases) (a : Charge lattice)
    (P : Fock) (m : ℕ) (hm : m ∉ P.vars.image Prod.snd) :
    positiveAnnihilator B a m P = 0 := by
  simp only [positiveAnnihilator, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  apply Finset.sum_eq_zero
  intro i _
  have hi : (i, m) ∉ P.vars := fun h => hm (Finset.mem_image_of_mem Prod.snd h)
  rw [pderiv_eq_zero_of_notMem_vars hi, smul_zero]

/-- The creation exponent is Σ_{n≥1} (3/n) a[-n/3] x^n. -/
def creationSeries (B : FixedDualBases) (a : Charge lattice) : PowerSeries Fock :=
  PowerSeries.mk fun
    | 0 => 0
    | m + 1 => (((m + 1 : ℕ) : ℂ) / 3)⁻¹ •
        ∑ i : Fin 16, creationCoordinate B a (i, m) • (X (i, m) : Fock)

theorem coeff_creationSeries_succ (B : FixedDualBases) (a : Charge lattice) (m : ℕ) :
    PowerSeries.coeff (m + 1) (creationSeries B a) =
      (((m + 1 : ℕ) : ℂ) / 3)⁻¹ •
        ∑ i : Fin 16, creationCoordinate B a (i, m) • (X (i, m) : Fock) :=
  PowerSeries.coeff_mk _ _

private theorem constantCoeff_creationSeries (B : FixedDualBases) (a : Charge lattice) :
    PowerSeries.constantCoeff (creationSeries B a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]

def creationExponential (B : FixedDualBases) (a : Charge lattice) : PowerSeries Fock :=
  (PowerSeries.exp Fock).subst (creationSeries B a)

@[simp] theorem coeff_zero_creationExponential (B : FixedDualBases) (a : Charge lattice) :
    PowerSeries.coeff 0 (creationExponential B a) = 1 := by
  rw [creationExponential, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_creationSeries B a),
    PowerSeries.constantCoeff_exp, map_one]

def creationCoeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) : Fock :=
  if k < 0 then 0 else PowerSeries.coeff k.toNat (creationExponential B a)

/-- The generator substitution in the polynomial coordinate u = x⁻¹. -/
def translationVariable (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    Polynomial Fock :=
  Polynomial.C (X j) -
    Polynomial.C (annihilationPairing B a j • (1 : Fock)) * Polynomial.X ^ frequency j

theorem translationVariable_annihilator (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    translationVariable B a j =
      Polynomial.C (X j) -
        Polynomial.C ((((frequency j : ℂ) / 3)⁻¹) • positiveAnnihilator B a j.2 (X j)) *
          Polynomial.X ^ frequency j := by
  have h : ((frequency j : ℂ) / 3) ≠ 0 := by
    apply div_ne_zero _ (by norm_num)
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j.2)
  rw [translationVariable, positiveAnnihilator_X, if_pos rfl, smul_smul,
    ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The positive exponential is evaluated by finite polynomial substitution.
In u = x⁻¹ each generator gets its own normalized positive mode. -/
def translatedPolynomial (B : FixedDualBases) (a : Charge lattice) :
    Fock →ₐ[ℂ] Polynomial Fock :=
  MvPolynomial.aeval (translationVariable B a)

theorem translatedPolynomial_apply (B : FixedDualBases) (a : Charge lattice) (P : Fock) :
    translatedPolynomial B a P =
      ∑ d ∈ P.support, algebraMap ℂ (Polynomial Fock) (P.coeff d) *
        ∏ j ∈ d.support, translationVariable B a j ^ d j := by
  calc
    translatedPolynomial B a P =
        translatedPolynomial B a (∑ d ∈ P.support, monomial d (P.coeff d)) :=
      congrArg (translatedPolynomial B a) P.as_sum
    _ = _ := by
      rw [map_sum]
      simp only [translatedPolynomial, MvPolynomial.aeval_monomial, Finsupp.prod]

/-- The same finite translation as a Laurent polynomial in x. -/
def translatedLaurent (B : FixedDualBases) (a : Charge lattice) (P : Fock) :
    LaurentPolynomial Fock :=
  LaurentPolynomial.invert (translatedPolynomial B a P).toLaurent

theorem translatedLaurent_X (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    translatedLaurent B a (X j) =
      LaurentPolynomial.C (X j) -
        LaurentPolynomial.C (annihilationPairing B a j • (1 : Fock)) *
          LaurentPolynomial.T (-(frequency j : ℤ)) := by
  simp only [translatedLaurent, translatedPolynomial, MvPolynomial.aeval_X, translationVariable,
    map_sub, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]

theorem coeff_translatedLaurent_neg (B : FixedDualBases) (a : Charge lattice)
    (P : Fock) (d : ℕ) :
    (translatedLaurent B a P).coeff (-(d : ℤ)) = (translatedPolynomial B a P).coeff d := by
  rw [translatedLaurent, LaurentPolynomial.invert_apply, neg_neg, LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding : ℕ ↪ ℤ).injective _ d).trans
    (Polynomial.toFinsupp_apply _ d)

/-- The largest cover energy Σ_j (j.2+1)d_j of an occupied monomial. -/
def occupationBound (P : Fock) : ℕ := P.weightedTotalDegree frequency

theorem occupationBound_eq (P : Fock) :
    occupationBound P = P.support.sup (fun d => ∑ j ∈ d.support, d j * frequency j) := by
  simp only [occupationBound, MvPolynomial.weightedTotalDegree, Finsupp.weight_apply,
    Finsupp.sum, Nat.nsmul_eq_mul]

theorem natDegree_translatedPolynomial_le (B : FixedDualBases) (a : Charge lattice) (P : Fock) :
    (translatedPolynomial B a P).natDegree ≤ occupationBound P := by
  have hvar (j : Mode) : (translationVariable B a j).natDegree ≤ frequency j := by
    unfold translationVariable
    have hconst : (Polynomial.C (X j) : Polynomial Fock).natDegree ≤ frequency j := by
      rw [Polynomial.natDegree_C]
      exact Nat.zero_le _
    simpa only [max_self] using
      Polynomial.natDegree_sub_le_of_le (n := frequency j) (m := frequency j) hconst
        (Polynomial.natDegree_C_mul_X_pow_le (annihilationPairing B a j • (1 : Fock))
          (frequency j))
  rw [translatedPolynomial_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hprod :
      (∏ j ∈ d.support, translationVariable B a j ^ d j).natDegree ≤
        ∑ j ∈ d.support, d j * frequency j := by
    refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum ?_)
    intro j _
    exact Polynomial.natDegree_pow_le_of_le (d j) (hvar j)
  have hweight : (∑ j ∈ d.support, d j * frequency j) ≤ occupationBound P := by
    simpa only [occupationBound, Finsupp.weight_apply, Finsupp.sum, Nat.nsmul_eq_mul] using
      (MvPolynomial.le_weightedTotalDegree frequency hd)
  have hscalar : (algebraMap ℂ (Polynomial Fock) (P.coeff d)).natDegree ≤ 0 := by
    rw [Polynomial.algebraMap_apply, Polynomial.natDegree_C]
  simpa only [zero_add] using Polynomial.natDegree_mul_le_of_le hscalar (hprod.trans hweight)

/-- The coefficient of x^k in the product of creation and translation. -/
def oscillatorCoeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    Fock →ₗ[ℂ] Fock :=
  (Polynomial.lsum fun d => LinearMap.mulLeft ℂ (creationCoeff B a (k + (d : ℤ)))).comp
    (translatedPolynomial B a).toLinearMap

theorem oscillatorCoeff_apply (B : FixedDualBases) (a : Charge lattice) (k : ℤ) (P : Fock) :
    oscillatorCoeff B a k P =
      ∑ d ∈ (translatedPolynomial B a P).support,
        creationCoeff B a (k + (d : ℤ)) * (translatedPolynomial B a P).coeff d :=
  rfl

theorem oscillatorCoeff_eq_zero_below (B : FixedDualBases) (a : Charge lattice) (P : Fock)
    (k : ℤ) (hk : k < -(occupationBound P : ℤ)) : oscillatorCoeff B a k P = 0 := by
  rw [oscillatorCoeff_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hd)
  have hbound : d ≤ occupationBound P :=
    hdegree.trans (natDegree_translatedPolynomial_le B a P)
  have hnegative : k + (d : ℤ) < 0 := by omega
  rw [creationCoeff, if_pos hnegative, zero_mul]

/-- The zero mode acts at p/3 and x^q accounts for the Bakalov–Kac b-shift. -/
def momentumExponent (a : Charge lattice) (p : Momentum) : ℤ :=
  ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1

theorem momentumExponent_eq (a : Charge lattice) (p : Momentum) :
    (momentumExponent a p : ℚ) =
      3 * (ThirdTwistedChargeAction.bShift lattice g a + (bilinear lattice a p.1 : ℚ) / 3) := by
  rw [momentumExponent, Int.cast_add,
    ← ThirdTwistedChargeAction.three_mul_bShift lattice g g_cube g_isometry a]
  ring

/-- Read the charge phase from the already constructed concrete ground operator. -/
def chargePhase (a : Charge lattice) (p : Momentum) : ℂ :=
  U a (Finsupp.single p 1) (shift a p)

theorem U_ground (a : Charge lattice) (p : Momentum) :
    U a (Finsupp.single p 1) = Finsupp.single (shift a p) (chargePhase a p) := by
  unfold chargePhase U
  rw [ThirdTwistedChargeAction.U_single]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.smul_single]

theorem chargePhase_ne_zero (a : Charge lattice) (p : Momentum) : chargePhase a p ≠ 0 := by
  unfold chargePhase U
  rw [ThirdTwistedChargeAction.U_single]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  exact Units.ne_zero _

/-- The coefficient of x^k of the charged field on arbitrary finite states. -/
def fieldCoeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) : Module.End ℂ State :=
  Finsupp.lsum ℂ fun p =>
    chargePhase a p • (Finsupp.lsingle (shift a p)).comp
      (oscillatorCoeff B a (k - momentumExponent a p))

theorem fieldCoeff_single (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (p : Momentum) (P : Fock) :
    fieldCoeff B a k (Finsupp.single p P) =
      Finsupp.single (shift a p)
        (chargePhase a p • oscillatorCoeff B a (k - momentumExponent a p) P) := by
  simp only [fieldCoeff, Finsupp.lsum_single, LinearMap.smul_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, Finsupp.smul_single]

theorem shift_numerator (a : Charge lattice) (p : Momentum) :
    (shift a p).1 = p.1 + N a := rfl

/-- A lower bound on all exponents, with zero included to cover the empty state. -/
def lowerBound (a : Charge lattice) (v : State) : ℤ :=
  (insert 0 (v.support.image fun p => momentumExponent a p - (occupationBound (v p) : ℤ))).min'
    (Finset.insert_nonempty _ _)

theorem fieldCoeff_eq_zero_below (B : FixedDualBases) (a : Charge lattice) (v : State)
    (k : ℤ) (hk : k < lowerBound a v) : fieldCoeff B a k v = 0 := by
  simp only [fieldCoeff, Finsupp.lsum_apply, Finsupp.sum, LinearMap.smul_apply,
    LinearMap.comp_apply, Finsupp.lsingle_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hmem : momentumExponent a p - (occupationBound (v p) : ℤ) ∈
      insert 0 (v.support.image fun q => momentumExponent a q - (occupationBound (v q) : ℤ)) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)
  have hb : lowerBound a v ≤ momentumExponent a p - (occupationBound (v p) : ℤ) :=
    Finset.min'_le _ _ hmem
  have hk' : k - momentumExponent a p < -(occupationBound (v p) : ℤ) := by omega
  rw [oscillatorCoeff_eq_zero_below B a (v p) _ hk', Finsupp.single_zero, smul_zero]

/-- The charged Laurent field on the concrete P48q momentum/Fock carrier. -/
def chargedField (B : FixedDualBases) (a : Charge lattice) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fieldCoeff B a) (by
    intro v
    refine ⟨lowerBound a v, ?_⟩
    intro k hk
    exact le_of_not_gt fun h => hk (fieldCoeff_eq_zero_below B a v k h))

theorem chargedField_coeff (B : FixedDualBases) (a : Charge lattice) (v : State) (k : ℤ) :
    ((HahnModule.of ℂ).symm (chargedField B a v)).coeff k = fieldCoeff B a k v :=
  rfl

theorem oscillatorCoeff_one (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    oscillatorCoeff B a k 1 = creationCoeff B a k := by
  change (translatedPolynomial B a (1 : Fock)).sum
    (fun d b => creationCoeff B a (k + (d : ℤ)) * b) = _
  rw [map_one, ← Polynomial.C_1,
    Polynomial.sum_C_index (f := fun d b => creationCoeff B a (k + (d : ℤ)) * b)
      (mul_zero _)]
  simp

/-- At ground momentum p/3 the positive exponential fixes the Fock vacuum. -/
theorem chargedField_ground (B : FixedDualBases) (a : Charge lattice) (p : Momentum) (k : ℤ) :
    ((HahnModule.of ℂ).symm (chargedField B a (Finsupp.single p 1))).coeff k =
      Finsupp.single (shift a p)
        (chargePhase a p • creationCoeff B a (k - momentumExponent a p)) := by
  rw [chargedField_coeff, fieldCoeff_single, oscillatorCoeff_one]

theorem chargedField_ground_leading (B : FixedDualBases) (a : Charge lattice) (p : Momentum) :
    ((HahnModule.of ℂ).symm
      (chargedField B a (Finsupp.single p 1))).coeff (momentumExponent a p) =
      Finsupp.single (shift a p) (chargePhase a p • (1 : Fock)) := by
  rw [chargedField_ground, sub_self]
  simp [creationCoeff]

theorem chargedField_ground_below (B : FixedDualBases) (a : Charge lattice)
    (p : Momentum) (k : ℤ) (hk : k < momentumExponent a p) :
    ((HahnModule.of ℂ).symm (chargedField B a (Finsupp.single p 1))).coeff k = 0 := by
  rw [chargedField_ground, creationCoeff, if_pos (sub_neg.mpr hk), smul_zero, Finsupp.single_zero]

theorem chargedField_vacuum (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    ((HahnModule.of ℂ).symm (chargedField B a (Finsupp.single 0 1))).coeff k =
      Finsupp.single (ThirdTwistedChargeAction.shift lattice g a 0)
        (chargePhase a 0 • creationCoeff B a (k - ThirdTwistedChargeAction.q lattice g a)) := by
  rw [chargedField_ground]
  simp [momentumExponent, bilinear]

#print axioms creationCoordinate_projected
#print axioms annihilationPairing_projected
#print axioms translationVariable_annihilator
#print axioms natDegree_translatedPolynomial_le
#print axioms fieldCoeff_eq_zero_below
#print axioms chargedField_ground
#print axioms chargedField_vacuum

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
