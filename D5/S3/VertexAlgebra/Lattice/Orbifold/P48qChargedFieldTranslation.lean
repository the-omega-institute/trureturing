/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedFieldTranslation
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed current action and translation identities for the P48q charged field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPositiveCurrentChargedField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMixedCurrentChargedField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
import Mathlib.Tactic.LinearCombination

/-!
The charged-field translation calculation of Bakalov–Kac,
arXiv:math/0402315v3, (3.13), (3.14), (4.26)–(4.32), with `z = x^3`.
The negative current modes act on the output of the charged field. The zero
and positive modes act on its input, as in (2.10)–(2.11).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open P48qThirdTwistedField
open P48qTwistedHeisenberg (mode mode_zero_apply mode_negative_apply mode_positive_apply
  mode_eq_zero_above_coverBound)
open ThirdEigenspacePairing (p48qForm)
open MvPolynomial (X)
open scoped BigOperators

open private gram_on_charges from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
open private action_chargeVector zetaPrimitive from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

noncomputable section

local notation "bShift" => ThirdTwistedChargeAction.bShift lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private def coverFrequency (n : ℕ) : ℤ := ((n + 1 : ℕ) : ℤ)

private def sumModes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : ℕ → Module.End ℂ V)
    (finite : ∀ v, Function.HasFiniteSupport (fun n => A n v)) : Module.End ℂ V where
  toFun v := ∑ᶠ n, A n v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (finite v) (finite w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (finite v)).symm

private def creationPolynomial (B : FixedDualBases) (a : Charge lattice) (n : ℕ) : Fock :=
  ∑ i : Fin 16, creationCoordinate B a (i, n) • X (i, n)

private theorem creationExponential_derivative (B : FixedDualBases) (a : Charge lattice) :
    PowerSeries.derivative (creationExponential B a) =
      PowerSeries.derivative (creationSeries B a) * creationExponential B a := by
  have hzero : PowerSeries.constantCoeff (creationSeries B a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hzero
  unfold creationExponential
  rw [PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp, mul_comm]

private theorem scaled_creationSeries_derivative (B : FixedDualBases) (a : Charge lattice)
    (n : ℕ) :
    (1 / 3 : ℂ) • PowerSeries.coeff n (PowerSeries.derivative (creationSeries B a)) =
      creationPolynomial B a n := by
  have hcast : ((n : Fock) + 1) = algebraMap ℂ Fock ((n + 1 : ℕ) : ℂ) := by simp
  have hscale : (1 / 3 : ℂ) * ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) / 3 := by ring
  have hnonzero : (((n + 1 : ℕ) : ℂ) / 3) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (by norm_num)
  rw [PowerSeries.coeff_derivative, hcast, mul_comm, ← Algebra.smul_def,
    coeff_creationSeries_succ]
  simp only [creationPolynomial, smul_smul, ← mul_assoc, hscale, mul_inv_cancel₀ hnonzero,
    one_smul]

private theorem creationCoeff_euler (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    ((k : ℂ) / 3) • creationCoeff B a k =
      ∑ᶠ n, creationPolynomial B a n * creationCoeff B a (k - coverFrequency n) := by
  have hsupport : Function.support
      (fun n => creationPolynomial B a n * creationCoeff B a (k - coverFrequency n)) ⊆
        (Finset.range k.toNat : Set ℕ) := by
    intro n hn
    change creationPolynomial B a n * creationCoeff B a (k - coverFrequency n) ≠ 0 at hn
    change n ∈ Finset.range k.toNat
    apply Finset.mem_range.mpr
    by_contra! h
    have hz : k - coverFrequency n < 0 := by unfold coverFrequency; omega
    exact hn (by rw [creationCoeff, if_pos hz, mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  cases k with
  | negSucc n =>
    simp [creationCoeff, Int.negSucc_lt_zero]
  | ofNat d =>
    cases d with
    | zero => simp
    | succ d =>
      change ((((d + 1 : ℕ) : ℤ) : ℂ) / 3) • creationCoeff B a ((d + 1 : ℕ) : ℤ) =
        ∑ n ∈ Finset.range (d + 1),
          creationPolynomial B a n * creationCoeff B a (((d + 1 : ℕ) : ℤ) - coverFrequency n)
      have h := congrArg (PowerSeries.coeff d) (creationExponential_derivative B a)
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
      have hscaled := congrArg (fun P : Fock => (1 / 3 : ℂ) • P) h
      change (1 / 3 : ℂ) • PowerSeries.coeff d
          (PowerSeries.derivative (creationExponential B a)) =
        (1 / 3 : ℂ) • ∑ n ∈ Finset.range (d + 1),
          PowerSeries.coeff n (PowerSeries.derivative (creationSeries B a)) *
            PowerSeries.coeff (d - n) (creationExponential B a) at hscaled
      rw [Finset.smul_sum] at hscaled
      simp only [← smul_mul_assoc, scaled_creationSeries_derivative] at hscaled
      have hleft :
          ((((d + 1 : ℕ) : ℤ) : ℂ) / 3) • creationCoeff B a ((d + 1 : ℕ) : ℤ) =
            (1 / 3 : ℂ) • PowerSeries.coeff d
              (PowerSeries.derivative (creationExponential B a)) := by
        have hcast : ((d : Fock) + 1) = algebraMap ℂ Fock ((d + 1 : ℕ) : ℂ) := by simp
        rw [creationCoeff, if_neg (by omega), Int.toNat_natCast, Int.cast_natCast,
          PowerSeries.coeff_derivative, hcast, mul_comm, ← Algebra.smul_def, smul_smul]
        rw [div_eq_inv_mul, one_div]
      rw [hleft, hscaled]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have hindex : (((d + 1 : ℕ) : ℤ) - coverFrequency n) = ((d - n : ℕ) : ℤ) := by
        unfold coverFrequency
        omega
      rw [hindex, creationCoeff, if_neg (by omega), Int.toNat_natCast]

private def oscillatorCreationTerm (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (n : ℕ) : Module.End ℂ Fock :=
  (LinearMap.mulLeft ℂ (creationPolynomial B a n)).comp
    (oscillatorCoeff B a (k - coverFrequency n))

private def oscillatorAnnihilationTerm (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (n : ℕ) : Module.End ℂ Fock :=
  (oscillatorCoeff B a (k + coverFrequency n)).comp (positiveAnnihilator B a n)

private theorem oscillatorCreation_finite (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (P : Fock) : Function.HasFiniteSupport (fun n => oscillatorCreationTerm B a k n P) := by
  refine (Finset.range (k + (occupationBound P : ℤ)).toNat).finite_toSet.subset ?_
  intro n hn
  change n ∈ Finset.range (k + (occupationBound P : ℤ)).toNat
  apply Finset.mem_range.mpr
  by_contra! h
  have hz : k - coverFrequency n < -(occupationBound P : ℤ) := by
    unfold coverFrequency
    omega
  exact hn (by simp [oscillatorCreationTerm, oscillatorCoeff_eq_zero_below B a P _ hz])

private theorem oscillatorAnnihilation_finite (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (P : Fock) : Function.HasFiniteSupport (fun n => oscillatorAnnihilationTerm B a k n P) := by
  classical
  refine (P.vars.image Prod.snd).finite_toSet.subset ?_
  intro n hn
  change n ∈ P.vars.image Prod.snd
  by_contra h
  exact hn (by simp [oscillatorAnnihilationTerm, positiveAnnihilator_eq_zero_of_not_mem B a P n h])

private def oscillatorCreation (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    Module.End ℂ Fock :=
  sumModes (oscillatorCreationTerm B a k) (oscillatorCreation_finite B a k)

private def oscillatorAnnihilation (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    Module.End ℂ Fock :=
  sumModes (oscillatorAnnihilationTerm B a k) (oscillatorAnnihilation_finite B a k)

private theorem oscillatorCoeff_X_mul (B : FixedDualBases) (a : Charge lattice) (j : Mode)
    (k : ℤ) (P : Fock) :
    oscillatorCoeff B a k (X j * P) = X j * oscillatorCoeff B a k P -
      annihilationPairing B a j • oscillatorCoeff B a (k + (frequency j : ℤ)) P := by
  rw [← oscillatorCoeff_commutator_apply B a j k P, sub_sub_cancel]

private theorem oscillatorCreation_X_mul (B : FixedDualBases) (a : Charge lattice) (j : Mode)
    (k : ℤ) (P : Fock) :
    oscillatorCreation B a k (X j * P) = X j * oscillatorCreation B a k P -
      annihilationPairing B a j • oscillatorCreation B a (k + (frequency j : ℤ)) P := by
  let f := fun n => oscillatorCreationTerm B a k n P
  let h := fun n => oscillatorCreationTerm B a (k + (frequency j : ℤ)) n P
  have hf : Function.HasFiniteSupport f := oscillatorCreation_finite B a k P
  have hh : Function.HasFiniteSupport h := oscillatorCreation_finite B a _ P
  have hmul : Function.HasFiniteSupport (fun n => X j * f n) :=
    hf.mul_right (fun _ : ℕ => (X j : Fock))
  have hsmul : Function.HasFiniteSupport (fun n => annihilationPairing B a j • h n) :=
    hh.smul_right (fun _ : ℕ => annihilationPairing B a j)
  change (∑ᶠ n, oscillatorCreationTerm B a k n (X j * P)) =
    X j * (∑ᶠ n, f n) - annihilationPairing B a j • ∑ᶠ n, h n
  rw [mul_finsum' f _ hf, smul_finsum' _ hh, ← finsum_sub_distrib hmul hsmul]
  apply finsum_congr
  intro n
  have hindex : k - coverFrequency n + (frequency j : ℤ) =
      k + (frequency j : ℤ) - coverFrequency n := by omega
  simp only [f, h, oscillatorCreationTerm, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    oscillatorCoeff_X_mul, hindex, mul_sub, mul_smul_comm]
  rw [mul_left_comm (creationPolynomial B a n) (X j)]

private theorem positiveAnnihilator_mul (B : FixedDualBases) (a : Charge lattice) (n : ℕ)
    (P Q : Fock) :
    positiveAnnihilator B a n (P * Q) =
      P * positiveAnnihilator B a n Q + positiveAnnihilator B a n P * Q := by
  rw [add_comm]
  simp only [positiveAnnihilator, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    MvPolynomial.pderiv_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]

private theorem oscillatorAnnihilation_X_mul (B : FixedDualBases) (a : Charge lattice) (j : Mode)
    (k : ℤ) (P : Fock) :
    oscillatorAnnihilation B a k (X j * P) = X j * oscillatorAnnihilation B a k P -
      annihilationPairing B a j • oscillatorAnnihilation B a (k + (frequency j : ℤ)) P +
      (((frequency j : ℂ) / 3) * annihilationPairing B a j) •
        oscillatorCoeff B a (k + (frequency j : ℤ)) P := by
  let f := fun n => oscillatorAnnihilationTerm B a k n P
  let h := fun n => oscillatorAnnihilationTerm B a (k + (frequency j : ℤ)) n P
  let c := annihilationPairing B a j
  let r := (frequency j : ℂ) / 3
  let correction : ℕ →₀ Fock :=
    Finsupp.single j.2 ((r * c) • oscillatorCoeff B a (k + (frequency j : ℤ)) P)
  have hf : Function.HasFiniteSupport f := oscillatorAnnihilation_finite B a k P
  have hh : Function.HasFiniteSupport h := oscillatorAnnihilation_finite B a _ P
  have hcorrection : Function.HasFiniteSupport (correction : ℕ → Fock) :=
    correction.hasFiniteSupport
  have hsum :
      (∑ᶠ n, correction n) = (r * c) • oscillatorCoeff B a (k + (frequency j : ℤ)) P := by
    calc
      (∑ᶠ n, correction n) = correction j.2 :=
        finsum_eq_single (correction : ℕ → Fock) j.2
          (fun _ hn => Finsupp.single_eq_of_ne hn)
      _ = _ := Finsupp.single_eq_same
  change (∑ᶠ n, oscillatorAnnihilationTerm B a k n (X j * P)) =
    X j * (∑ᶠ n, f n) - c • (∑ᶠ n, h n) +
      (r * c) • oscillatorCoeff B a (k + (frequency j : ℤ)) P
  have hmul : Function.HasFiniteSupport (fun n => X j * f n) :=
    hf.mul_right (fun _ : ℕ => (X j : Fock))
  have hsmul : Function.HasFiniteSupport (fun n => c • h n) :=
    hh.smul_right (fun _ : ℕ => c)
  have hsum_add :
      (∑ᶠ n, (X j * f n - c • h n + correction n)) =
        (∑ᶠ n, (X j * f n - c • h n)) + (∑ᶠ n, correction n) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      finsum_add_distrib (hmul.sub hsmul) hcorrection
  rw [mul_finsum' f _ hf, smul_finsum' _ hh, ← finsum_sub_distrib hmul hsmul,
    ← hsum, ← hsum_add]
  apply finsum_congr
  intro n
  have hindex : k + coverFrequency n + (frequency j : ℤ) =
      k + (frequency j : ℤ) + coverFrequency n := add_right_comm _ _ _
  have hcorrectionAt :
      oscillatorCoeff B a (k + coverFrequency n) (positiveAnnihilator B a n (X j) * P) =
        correction n := by
    by_cases hn : n = j.2
    · subst n
      have hfrequency : coverFrequency j.2 = (frequency j : ℤ) := rfl
      simp only [positiveAnnihilator_X, ite_true, smul_mul_assoc, one_mul, map_smul,
        correction, Finsupp.single_eq_same, hfrequency, r, c]
    · simp only [positiveAnnihilator_X, ite_eq_right hn, zero_mul, map_zero, correction,
        Finsupp.single_eq_of_ne hn]
  simp only [f, h, c, oscillatorAnnihilationTerm, LinearMap.comp_apply,
    positiveAnnihilator_mul, map_add, oscillatorCoeff_X_mul, hindex, hcorrectionAt]

private theorem oscillatorCoeff_euler (B : FixedDualBases) (a : Charge lattice) (P : Fock)
    (k : ℤ) :
    ((k : ℂ) / 3) • oscillatorCoeff B a k P =
      oscillatorCreation B a k P + oscillatorAnnihilation B a k P := by
  revert k
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro k
    have hnegative : oscillatorCreation B a k 1 =
        ∑ᶠ n, creationPolynomial B a n * creationCoeff B a (k - coverFrequency n) := by
      change (∑ᶠ n, oscillatorCreationTerm B a k n 1) = _
      simp only [oscillatorCreationTerm, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        oscillatorCoeff_one]
    have hpositive : oscillatorAnnihilation B a k 1 = 0 := by
      change (∑ᶠ n, oscillatorAnnihilationTerm B a k n 1) = 0
      apply finsum_eq_zero_of_forall_eq_zero
      intro n
      simp only [oscillatorAnnihilationTerm, LinearMap.comp_apply, positiveAnnihilator,
        LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
        MvPolynomial.pderiv_one, smul_zero, Finset.sum_const_zero, map_zero]
    simp only [MvPolynomial.C_eq_smul_one, map_smul, smul_comm ((k : ℂ) / 3) c,
      oscillatorCoeff_one, hnegative, hpositive, add_zero, smul_zero, creationCoeff_euler]
  | add P Q hP hQ =>
    intro k
    simp only [map_add, smul_add, hP k, hQ k]
    abel
  | mul_X P j ih =>
    intro k
    rw [mul_comm P (X j), oscillatorCoeff_X_mul, oscillatorCreation_X_mul,
      oscillatorAnnihilation_X_mul]
    calc
      _ = X j * (((k : ℂ) / 3) • oscillatorCoeff B a k P) -
          annihilationPairing B a j •
            ((((k + (frequency j : ℤ) : ℤ) : ℂ) / 3) •
              oscillatorCoeff B a (k + (frequency j : ℤ)) P) +
          (((frequency j : ℂ) / 3) * annihilationPairing B a j) •
            oscillatorCoeff B a (k + (frequency j : ℤ)) P := by
        simp only [smul_sub, mul_smul_comm, smul_smul, Int.cast_add, Int.cast_natCast, add_div,
          mul_add]
        module
      _ = _ := by
        rw [ih k, ih (k + (frequency j : ℤ)), mul_add, smul_add]
        abel

private def creationTerm (a : Charge lattice) (t : ℤ) (n : ℕ) : Module.End ℂ State :=
  (mode (chargeVector a) (.negSucc n)).comp (fieldCoeff fixedDualBases a (t - coverFrequency n))

private def annihilationTerm (a : Charge lattice) (t : ℤ) (n : ℕ) : Module.End ℂ State :=
  (fieldCoeff fixedDualBases a (t + coverFrequency n)).comp
    (mode (chargeVector a) (.ofNat (n + 1)))

private theorem creation_finite (a : Charge lattice) (t : ℤ) (v : State) :
    Function.HasFiniteSupport (fun n => creationTerm a t n v) := by
  refine (Finset.range (t - lowerBound a v).toNat).finite_toSet.subset ?_
  intro n hn
  change n ∈ Finset.range (t - lowerBound a v).toNat
  apply Finset.mem_range.mpr
  by_contra! h
  have hz : t - coverFrequency n < lowerBound a v := by unfold coverFrequency; omega
  exact hn (by simp [creationTerm, fieldCoeff_eq_zero_below fixedDualBases a v _ hz])

private theorem annihilation_finite (a : Charge lattice) (t : ℤ) (v : State) :
    Function.HasFiniteSupport (fun n => annihilationTerm a t n v) := by
  refine (Finset.range (P48qFixedCurrentIterate.coverBound v)).finite_toSet.subset ?_
  intro n hn
  change n ∈ Finset.range (P48qFixedCurrentIterate.coverBound v)
  apply Finset.mem_range.mpr
  by_contra! h
  have hz : (P48qFixedCurrentIterate.coverBound v : ℤ) < coverFrequency n :=
    Int.ofNat_lt.mpr (Nat.lt_succ_of_le h)
  have hmode : mode (chargeVector a) (Int.ofNat (n + 1)) v = 0 :=
    mode_eq_zero_above_coverBound v (chargeVector a) (coverFrequency n) hz
  apply hn
  change fieldCoeff fixedDualBases a (t + coverFrequency n)
    (mode (chargeVector a) (.ofNat (n + 1)) v) = 0
  rw [hmode, map_zero]

/-- The coefficient of `x^k` in the normally ordered current along the charge
times its explicit charged field. Current mode `m` has cover exponent `-m-3`.
The two sums have finite support on each input state. -/
def normalOrderedCurrentCoeff (a : Charge lattice) (k : ℤ) : Module.End ℂ State :=
  sumModes (creationTerm a (k + 3)) (creation_finite a (k + 3)) +
    (fieldCoeff fixedDualBases a (k + 3)).comp (mode (chargeVector a) 0) +
    sumModes (annihilationTerm a (k + 3)) (annihilation_finite a (k + 3))

private theorem mode_negative_single (a : Charge lattice) (n : ℕ) (p : Momentum) (P : Fock) :
    mode (chargeVector a) (.negSucc n) (Finsupp.single p P) =
      Finsupp.single p (creationPolynomial fixedDualBases a n * P) := by
  have hpoint (v : State) (q : Momentum) :
      mode (chargeVector a) (.negSucc n) v q = creationPolynomial fixedDualBases a n * v q := by
    rw [mode_negative_apply, creationPolynomial, Finset.sum_mul]
    simp only [P48qTwistedHeisenberg.creCoordinates, creationCoordinate, smul_mul_assoc]
  apply Finsupp.ext
  intro q
  rw [hpoint]
  by_cases h : q = p
  · subst q
    simp
  · simp [Finsupp.single_eq_of_ne h]

private theorem mode_positive_single (a : Charge lattice) (n : ℕ) (p : Momentum) (P : Fock) :
    mode (chargeVector a) (.ofNat (n + 1)) (Finsupp.single p P) =
      Finsupp.single p (positiveAnnihilator fixedDualBases a n P) := by
  have hpoint (v : State) (q : Momentum) :
      mode (chargeVector a) (.ofNat (n + 1)) v q = positiveAnnihilator fixedDualBases a n (v q) := by
    rw [mode_positive_apply]
    simp only [positiveAnnihilator, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
      P48qTwistedHeisenberg.scale, P48qTwistedHeisenberg.annCoordinates, annihilationPairing, frequency]
  apply Finsupp.ext
  intro q
  rw [hpoint]
  by_cases h : q = p
  · subst q
    simp
  · simp [Finsupp.single_eq_of_ne h]

private theorem charge_pairing (a b : Charge lattice) :
    p48qForm (chargeVector a) (chargeVector b) = (bilinear lattice a b : ℂ) :=
  gram_on_charges ℂ a b

private theorem mode_zero_single (a : Charge lattice) (p : Momentum) (P : Fock) :
    mode (chargeVector a) 0 (Finsupp.single p P) =
      ((bilinear lattice a p.1 : ℂ) / 3) • Finsupp.single p P := by
  apply Finsupp.ext
  intro q
  rw [mode_zero_apply, Finsupp.smul_apply]
  by_cases h : q = p
  · subst q
    have hpair : p48qForm (chargeVector a) (P48qMomentumEnergy.physicalMomentum p : Cartan) =
        (bilinear lattice a p.1 : ℂ) / 3 := by
      change p48qForm (chargeVector a) ((3 : ℂ)⁻¹ • chargeVector p.1) = _
      simp only [LinearMap.BilinForm.smul_right, charge_pairing, div_eq_inv_mul]
    rw [hpair]
  · simp only [Finsupp.single_eq_of_ne h, smul_zero]

private theorem momentumExponent_div (a : Charge lattice) (p : Momentum) :
    (momentumExponent a p : ℂ) / 3 =
      (bilinear lattice a p.1 : ℂ) / 3 + (bShift a : ℂ) := by
  have h : (momentumExponent a p : ℂ) =
      3 * ((bShift a : ℂ) + (bilinear lattice a p.1 : ℂ) / 3) := by
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℂ)) (momentumExponent_eq a p)
  rw [h]
  ring

/-- The translation identity as endomorphisms at each cover coefficient. -/
theorem fieldCoeff_translation (a : Charge lattice) (k : ℤ) :
    ((((k + 3 : ℤ) : ℂ) / 3) • fieldCoeff fixedDualBases a (k + 3)) =
      normalOrderedCurrentCoeff a k + (bShift a : ℂ) • fieldCoeff fixedDualBases a (k + 3) := by
  apply Finsupp.lhom_ext
  intro p P
  let t : ℤ := k + 3
  let l : ℤ := t - momentumExponent a p
  let J : Fock →ₗ[ℂ] State := chargePhase a p • Finsupp.lsingle (shift a p)
  let v : State := Finsupp.single p P
  have hJ (n : ℤ) (Q : Fock) :
      fieldCoeff fixedDualBases a n (Finsupp.single p Q) =
        J (oscillatorCoeff fixedDualBases a (n - momentumExponent a p) Q) := by
    rw [fieldCoeff_single]
    simp only [J, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single]
  have hcreate (n : ℕ) : creationTerm a t n v =
      J (oscillatorCreationTerm fixedDualBases a l n P) := by
    have hindex : t - coverFrequency n - momentumExponent a p = l - coverFrequency n := by
      dsimp [l]
      omega
    simp only [creationTerm, v, LinearMap.comp_apply, fieldCoeff_single, mode_negative_single,
      oscillatorCreationTerm, hindex, LinearMap.mulLeft_apply, J, LinearMap.smul_apply,
      Finsupp.lsingle_apply, Finsupp.smul_single, mul_smul_comm]
  have hannihilate (n : ℕ) : annihilationTerm a t n v =
      J (oscillatorAnnihilationTerm fixedDualBases a l n P) := by
    have hindex : t + coverFrequency n - momentumExponent a p = l + coverFrequency n := by
      dsimp [l]
      omega
    simp only [annihilationTerm, v, LinearMap.comp_apply, mode_positive_single, hJ, hindex,
      oscillatorAnnihilationTerm]
  have hleft : (∑ᶠ n, creationTerm a t n v) = J (oscillatorCreation fixedDualBases a l P) := by
    change (∑ᶠ n, creationTerm a t n v) =
      J (∑ᶠ n, oscillatorCreationTerm fixedDualBases a l n P)
    rw [map_finsum J (oscillatorCreation_finite fixedDualBases a l P)]
    exact finsum_congr hcreate
  have hright : (∑ᶠ n, annihilationTerm a t n v) =
      J (oscillatorAnnihilation fixedDualBases a l P) := by
    change (∑ᶠ n, annihilationTerm a t n v) =
      J (∑ᶠ n, oscillatorAnnihilationTerm fixedDualBases a l n P)
    rw [map_finsum J (oscillatorAnnihilation_finite fixedDualBases a l P)]
    exact finsum_congr hannihilate
  change ((t : ℂ) / 3) • fieldCoeff fixedDualBases a t v =
    (∑ᶠ n, creationTerm a t n v) +
      fieldCoeff fixedDualBases a t (mode (chargeVector a) 0 v) +
      (∑ᶠ n, annihilationTerm a t n v) +
      (bShift a : ℂ) • fieldCoeff fixedDualBases a t v
  have hscalar : (t : ℂ) / 3 =
      (l : ℂ) / 3 + (bilinear lattice a p.1 : ℂ) / 3 + (bShift a : ℂ) := by
    dsimp only [l]
    rw [Int.cast_sub, sub_div, add_assoc, ← momentumExponent_div]
    ring
  have hfield : fieldCoeff fixedDualBases a t v =
      J (oscillatorCoeff fixedDualBases a l P) := hJ t P
  have hEuler := congrArg J (oscillatorCoeff_euler fixedDualBases a P l)
  rw [map_smul, map_add] at hEuler
  rw [hleft, hright, show mode (chargeVector a) 0 v = ((bilinear lattice a p.1 : ℂ) / 3) • v
      from mode_zero_single a p P, map_smul, hfield, hscalar, add_smul, add_smul, hEuler]
  abel

/-- The coefficient of `x^k` in `d/dz` of the concrete charged field on
every finitely supported momentum state with arbitrary polynomial Fock entries. -/
theorem concreteChargedField_coeff_translation (a : Charge lattice) (k : ℤ) (v : State) :
    ((((k + 3 : ℤ) : ℂ) / 3) •
        ((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff (k + 3)) =
      normalOrderedCurrentCoeff a k v +
        (bShift a : ℂ) • ((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff (k + 3) := by
  simpa only [concreteChargedField, chargedField_coeff, LinearMap.add_apply, LinearMap.smul_apply]
    using DFunLike.congr_fun (fieldCoeff_translation a k) v

private theorem moving_projection_pairing (a : Charge lattice) (u : ℂ) (hu : u + u ^ 2 = -1) :
    p48qForm (P48qTwistedHeisenberg.project u (chargeVector a)) (chargeVector a) =
      ((bilinear lattice a a : ℂ) - (bilinear lattice a (g a) : ℂ)) / 3 := by
  have hsymm : bilinear lattice (g a) a = bilinear lattice a (g a) :=
    LatticeFiniteNegativeGeneration.bilinear_symmetric lattice (g a) a
  have horbit : bilinear lattice (g (g a)) a = bilinear lattice a (g a) := by
    simpa only [g_cube] using (g_isometry (g (g a)) a).symm
  simp only [P48qTwistedHeisenberg.project, action_chargeVector, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_left, charge_pairing, hsymm, horbit]
  calc
    _ = (3 : ℂ)⁻¹ * ((bilinear lattice a a : ℂ) +
        (u + u ^ 2) * (bilinear lattice a (g a) : ℂ)) := by ring
    _ = _ := by rw [hu]; ring

/-- Equation (4.32) for the two nonzero Fourier residues of the order-three action. -/
theorem weighted_projection_pairing_eq_neg_bShift (a : Charge lattice) :
    (1 / 3 : ℂ) * p48qForm (P48qTwistedHeisenberg.projectAt 1 (chargeVector a)) (chargeVector a) +
      (2 / 3 : ℂ) * p48qForm (P48qTwistedHeisenberg.projectAt 2 (chargeVector a)) (chargeVector a) =
      -(bShift a : ℂ) := by
  let ζ : ℂ := ThirdTwistedChargeCocycle.zeta
  have hζ : 1 + ζ + ζ ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] using
      zetaPrimitive.geom_sum_eq_zero (by decide : 1 < 3)
  have hζ4 : (ζ ^ 2) ^ 2 = ζ := by
    calc
      (ζ ^ 2) ^ 2 = ζ ^ 3 * ζ := by ring
      _ = ζ := by rw [show ζ ^ 3 = 1 from zetaPrimitive.pow_eq_one, one_mul]
  have h₁ : ζ + ζ ^ 2 = -1 := by linear_combination hζ
  have h₂ : ζ ^ 2 + (ζ ^ 2) ^ 2 = -1 := by
    rw [hζ4]
    linear_combination hζ
  have hb : (3 : ℂ) * (bShift a : ℂ) =
      (bilinear lattice a (g a) : ℂ) - (bilinear lattice a a : ℂ) := by
    have hq : (3 : ℂ) * (bShift a : ℂ) = (ThirdTwistedChargeAction.q lattice g a : ℂ) := by
      simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] using
        congrArg (fun r : ℚ => (r : ℂ))
          (ThirdTwistedChargeAction.three_mul_bShift lattice g g_cube g_isometry a)
    simpa only [ThirdTwistedChargeAction.q, Int.cast_sub] using hq
  rw [P48qTwistedHeisenberg.projectAt_eq_fourier, P48qTwistedHeisenberg.projectAt_eq_fourier,
    show ((1 : ℤ) % 3).toNat = 1 by decide, show ((2 : ℤ) % 3).toNat = 2 by decide, pow_one,
    moving_projection_pairing a ζ h₁, moving_projection_pairing a (ζ ^ 2) h₂]
  linear_combination (1 / 3 : ℂ) * hb

#print axioms concreteChargedField_coeff_translation
#print axioms weighted_projection_pairing_eq_neg_bShift

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
