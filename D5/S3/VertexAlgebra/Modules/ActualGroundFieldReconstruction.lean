/-
SOURCE_ONLY_UNCOMPILED. No elaboration or kernel receipt is asserted.

The finite partition formula below is proved from its factorial products,
then compared with the derivative recurrence of the ORIGINAL creationExponential.
The arbitrary-module field formula subsequently consumes actual Taylor
coefficients and actual Z selection. Neither that formula nor an intertwining
or tensor-module statement is a hypothesis.

Conventions: Bakalov--Kac math/0402315v1 section 4.1, with the original
lower-triangular PLUS half-diagonal cocycle. Imported actual-current and
residue suppliers retain Carnahan/Kytölä attribution. The sealed Pro paper
3dd6298a... is mathematical advice only. See supplier-signatures.json for
literal source headers, context and SHA-256 identities.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundChargedTranslations
import D5.S3.VertexAlgebra.Modules.ActualGroundPartitionScalar
import Mathlib.Algebra.Polynomial.Coeff
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Modules.ActualGroundFieldReconstruction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundTaylorCoefficients
open ActualGroundJointWeights ActualGroundChargedSelection ActualGroundChargedTranslations
open ActualGroundPartitionScalar
open LatticeSugawaraCurrents (gramComplex)
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
open private exponential_derivative logarithm_derivative_coeff
  from D5.S3.VertexAlgebra.LatticeSugawaraConformal

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

def taylorScalar (α : Charge D) (d : Index D →₀ ℕ) : ℂ :=
  (WeylData.factorial d : ℂ)⁻¹ * derivativeScalar α d

def partitionTerm (α : Charge D) (d : Index D →₀ ℕ) : Oscillator D :=
  taylorScalar α d • MvPolynomial.monomial d 1

def creationPartition (α : Charge D) (k : ℕ) : Oscillator D :=
  ∑ d ∈ weightedLevel k, partitionTerm α d

private theorem partition_remove_factor (α : Charge D) (d : Index D →₀ ℕ)
    (x : Index D) :
    (d x + 1 : ℂ) • partitionTerm α (d + Finsupp.single x 1) =
      normalizedCharge α x • (MvPolynomial.X x * partitionTerm α d) := by
  have hc : (d x + 1 : ℂ) * taylorScalar α (d + Finsupp.single x 1) =
      normalizedCharge α x * taylorScalar α d := by
    rw [taylorScalar, WeylData.factorial_add_single, derivativeScalar_add_single]
    push_cast
    have hd := WeylData.factorial_cast_ne_zero (K := ℂ) d
    have hx : (d x + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d x)
    dsimp only [taylorScalar]
    field_simp [hd, hx]
    <;> ring
  have hm : (MvPolynomial.monomial (d + Finsupp.single x 1) 1 : Oscillator D) =
      MvPolynomial.X x * MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.monomial_add_single, pow_one, mul_comm]
  simp only [partitionTerm, hm, smul_smul, mul_smul_comm]
  rw [hc]

private theorem sum_occupied_partition (α : Charge D) (k : ℕ) (x : Index D)
    (hx : x ∈ oscillatorBox k) :
    (∑ d ∈ weightedLevel k, (d x : ℂ) • partitionTerm α d) =
      normalizedCharge α x •
        (MvPolynomial.X x * creationPartition α (k - (x.2 + 1))) := by
  classical
  have hfreq : x.2 + 1 ≤ k := by
    exact Nat.succ_le_of_lt (Finset.mem_range.mp (Finset.mem_product.mp hx).2)
  let occupied := (weightedLevel (D := D) k).filter (fun d => d x ≠ 0)
  have hfilter : (∑ d ∈ weightedLevel k, (d x : ℂ) • partitionTerm α d) =
      ∑ d ∈ occupied, (d x : ℂ) • partitionTerm α d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hz : d x = 0 := by
      by_contra hne
      exact hn (Finset.mem_filter.mpr ⟨hd, hne⟩)
    simp [hz]
  rw [hfilter, creationPartition, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_bij (fun d _ => d - Finsupp.single x 1)
  · intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hd, hdx⟩
    have hw := Finsupp.weight_sub_single_add
      (w := fun y : Index D => y.2 + 1) hdx
    have hk := (mem_weightedLevel k d).mp hd
    rw [mem_weightedLevel]
    change occupationWeight (d - Finsupp.single x 1) + (x.2 + 1) =
      occupationWeight d at hw
    omega
  · intro d hd e he hde
    have hdpos : 0 < d x := Nat.pos_of_ne_zero (Finset.mem_filter.mp hd).2
    have hepos : 0 < e x := Nat.pos_of_ne_zero (Finset.mem_filter.mp he).2
    have h := congrArg (fun f : Index D →₀ ℕ => f + Finsupp.single x 1) hde
    simpa only [WeylData.restore_sub_single d x hdpos,
      WeylData.restore_sub_single e x hepos] using h
  · intro e he
    refine ⟨e + Finsupp.single x 1, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_weightedLevel, occupationWeight_add_single]
      have hew := (mem_weightedLevel _ e).mp he
      exact ⟨by omega, by simp⟩
    · ext y
      by_cases hy : y = x
      · subst y; simp
      · simp [Finsupp.single_apply, hy]
  · intro d hd
    have hp : 0 < d x := Nat.pos_of_ne_zero (Finset.mem_filter.mp hd).2
    have hr := WeylData.restore_sub_single d x hp
    have hs := partition_remove_factor α (d - Finsupp.single x 1) x
    rw [hr] at hs
    have hc : (((d - Finsupp.single x 1 : Index D →₀ ℕ) x : ℂ) + 1) = (d x : ℂ) := by
      have hn : (d - Finsupp.single x 1 : Index D →₀ ℕ) x + 1 = d x := by
        simpa using congrArg (fun f : Index D →₀ ℕ => f x) hr
      exact_mod_cast hn
    rwa [hc] at hs

/-- Finite multiindex/factorial recurrence, before comparison with exp. -/
private theorem creationPartition_recurrence (α : Charge D) (k : ℕ) :
    (k : ℂ) • creationPartition α k =
      ∑ r ∈ Finset.range k,
        (∑ i : Fin D.rank, (α i : ℂ) • (MvPolynomial.X (i,r) : Oscillator D)) *
          creationPartition α (k - (r + 1)) := by
  classical
  calc
    _ = ∑ d ∈ weightedLevel k, ∑ x ∈ oscillatorBox k,
        (x.2 + 1 : ℂ) • ((d x : ℂ) • partitionTerm α d) := by
      rw [creationPartition, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [occupation_mass k d ((mem_weightedLevel k d).mp hd), Finset.sum_smul]
      simp only [smul_smul]
    _ = ∑ x ∈ oscillatorBox k, (x.2 + 1 : ℂ) •
        (normalizedCharge α x •
          (MvPolynomial.X x * creationPartition α (k - (x.2 + 1)))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.smul_sum, sum_occupied_partition α k x hx]
    _ = ∑ x ∈ oscillatorBox k,
        (α x.1 : ℂ) • (MvPolynomial.X x * creationPartition α (k - (x.2 + 1))) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hn : (x.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero x.2
      rw [smul_smul, normalizedCharge, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    _ = _ := by
      rw [oscillatorBox, Finset.sum_product, Finset.sum_comm]
      simp_rw [Finset.sum_mul, smul_mul_assoc]

private theorem creationExponential_recurrence (α : Charge D) (k : ℕ) :
    (k + 1 : ℂ) • PowerSeries.coeff (k + 1) (creationExponential D α) =
      ∑ r ∈ Finset.range (k + 1),
        (∑ i : Fin D.rank, (α i : ℂ) • (MvPolynomial.X (i,r) : Oscillator D)) *
          PowerSeries.coeff (k-r) (creationExponential D α) := by
  have hd := exponential_derivative D α
  have hAn := logarithm_derivative_coeff D α
  have hrec := congrArg (PowerSeries.coeff k) hd
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  have hs : (∑ r ∈ Finset.range (k+1),
      PowerSeries.coeff r (creationExponential D α) *
        PowerSeries.coeff (k-r)
          (PowerSeries.derivative (R := Oscillator D) (creationSeries D α))) =
      ∑ r ∈ Finset.range (k+1),
        (∑ i : Fin D.rank, (α i : ℂ) • (MvPolynomial.X (i,r) : Oscillator D)) *
          PowerSeries.coeff (k-r) (creationExponential D α) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro r hr
    have hrk : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hrk, hAn, mul_comm]
  rw [hs] at hrec
  simpa [Algebra.smul_def, mul_comm] using hrec

/-- Exact original creationCoeff, as a finite partition/factorial sum.
All negative integer cutoffs are zero by the original definition. -/
theorem creationCoeff_partition (α : Charge D) (t : ℤ) :
    creationCoeff D α t =
      if t < 0 then 0 else creationPartition α t.toNat := by
  classical
  have hn : ∀ k : ℕ, PowerSeries.coeff k (creationExponential D α) =
      creationPartition α k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        simp [creationPartition, weightedLevel_zero, partitionTerm, taylorScalar,
          LatticeSugawaraConformal.exponential_constant]
      | succ k =>
        have hrec := creationExponential_recurrence α k
        have hs : (∑ r ∈ Finset.range (k+1),
            (∑ i : Fin D.rank, (α i : ℂ) • (MvPolynomial.X (i,r) : Oscillator D)) *
              PowerSeries.coeff (k-r) (creationExponential D α)) =
            ∑ r ∈ Finset.range (k+1),
              (∑ i : Fin D.rank, (α i : ℂ) • (MvPolynomial.X (i,r) : Oscillator D)) *
                creationPartition α (k + 1 - (r + 1)) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [ih (k-r) (by omega)]
          congr 2
          omega
        rw [hs, ← creationPartition_recurrence] at hrec
        apply smul_right_injective (Oscillator D)
          (show (k + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero k)
        simpa only [Nat.cast_add, Nat.cast_one] using hrec
  by_cases ht : t < 0
  · simp [creationCoeff, ht]
  · simp only [creationCoeff, dif_neg ht, if_neg ht, hn]

variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- Evaluate finite oscillator polynomials in actual commuting creators.
No commutativity instance is imposed on the full endomorphism ring. -/
def polynomialOperator : Oscillator D →ₗ[ℂ] Module.End ℂ M :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun d => (W J hNil H hHG).creation d)

@[simp] theorem polynomialOperator_monomial (d : Index D →₀ ℕ) (c : ℂ) :
    polynomialOperator J hNil H hHG (MvPolynomial.monomial d c) =
      c • (W J hNil H hHG).creation d := by
  have hm : (MvPolynomial.monomial d c : Oscillator D) = c • MvPolynomial.monomial d 1 := by
    simp [MvPolynomial.smul_monomial]
  rw [hm, map_smul]
  congr 1
  exact (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ _ d

@[simp] theorem polynomialOperator_one :
    polynomialOperator J hNil H hHG (1 : Oscillator D) = 1 := by
  simpa using polynomialOperator_monomial J hNil H hHG (0 : Index D →₀ ℕ) 1

theorem polynomialOperator_X_mul (x : Index D) (P : Oscillator D) :
    polynomialOperator J hNil H hHG (MvPolynomial.X x * P) =
      creation J x.1 x.2 * polynomialOperator J hNil H hHG P := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial d c =>
    have hm : (MvPolynomial.X x * MvPolynomial.monomial d c : Oscillator D) =
        MvPolynomial.monomial (d + Finsupp.single x 1) c := by
      rw [MvPolynomial.monomial_add_single, pow_one, mul_comm]
    rw [hm, polynomialOperator_monomial, polynomialOperator_monomial,
      WeylData.creation_add_single, mul_smul_comm]
    rfl

theorem polynomialOperator_mul (P Q : Oscillator D) :
    polynomialOperator J hNil H hHG (P * Q) =
      polynomialOperator J hNil H hHG P * polynomialOperator J hNil H hHG Q := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.C c : Oscillator D) = c • 1 := MvPolynomial.C_eq_smul_one
    simp only [hc, smul_mul_assoc, one_mul, map_smul, polynomialOperator_one]
  | add P R hp hr => simp only [add_mul, map_add, hp, hr]
  | mul_X P x hp =>
    have hmul : (P * MvPolynomial.X x) * Q = MvPolynomial.X x * (P * Q) := by
      rw [mul_comm P (MvPolynomial.X x), mul_assoc]
    have hPX : P * MvPolynomial.X x = MvPolynomial.X x * P := mul_comm _ _
    calc
      polynomialOperator J hNil H hHG ((P * MvPolynomial.X x) * Q) =
          creation J x.1 x.2 * polynomialOperator J hNil H hHG (P * Q) := by
        rw [hmul, polynomialOperator_X_mul]
      _ = creation J x.1 x.2 *
          (polynomialOperator J hNil H hHG P * polynomialOperator J hNil H hHG Q) := by
        rw [hp]
      _ = (creation J x.1 x.2 * polynomialOperator J hNil H hHG P) *
          polynomialOperator J hNil H hHG Q := (mul_assoc _ _ _).symm
      _ = polynomialOperator J hNil H hHG (P * MvPolynomial.X x) *
          polynomialOperator J hNil H hHG Q := by
        rw [hPX, polynomialOperator_X_mul]

/-- Outside the actual finite Taylor box the actual coefficient is zero.
This is the justification for enlarging that box to the universal partition
level; the universal level need not itself fit in the Taylor box. -/
private theorem coefficient_outside_box (v : M) (d : Index D →₀ ℕ)
    (hd : d ∉ Finset.Iic ((W J hNil H hHG).jointCutoff v)) :
    (W J hNil H hHG).coefficient d v = 0 := by
  apply (W J hNil H hHG).coefficient_eq_zero_of_derivative
  exact (W J hNil H hHG).derivative_eq_zero_of_not_le v _ d
    ((W J hNil H hHG).jointCutoff_spec v) (by simpa using hd)

/-- Required arbitrary-J bridge. The cutoff is signed, m is any integer,
and the input is a true original-current joint weight. -/
theorem E_ground (α b : Charge D) (m : ℤ) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    E J α m v.val = polynomialOperator J hNil H hHG
      (creationCoeff D α (-m - 1 - weightPairing α b))
        (S J hNil H hHG hGH α b v : M) := by
  classical
  let t : ℤ := -m - 1 - weightPairing α b
  by_cases ht : t < 0
  · have hz : E J α m v.val = 0 :=
      E_above_leading J hNil H hHG hGH α b m v hv (by dsimp [t] at ht; omega)
    rw [hz, creationCoeff_partition, if_pos ht, map_zero, LinearMap.zero_apply]
  · let k : ℕ := t.toNat
    have hk : (k : ℤ) = t := Int.toNat_of_nonneg (le_of_not_gt ht)
    let box := Finset.Iic ((W J hNil H hHG).jointCutoff (E J α m v.val))
    let f : (Index D →₀ ℕ) → M := fun d =>
      (W J hNil H hHG).creation d ((W J hNil H hHG).coefficient d (E J α m v.val))
    have hselect (d : Index D →₀ ℕ) (hd : d ∉ weightedLevel k) : f d = 0 := by
      have hweight : occupationWeight d ≠ k := by simpa using hd
      have hmode : m + occupationWeight d ≠ -weightPairing α b - 1 := by
        dsimp [t] at hk
        omega
      dsimp only [f]
      rw [coefficient_E_ground_raw J hNil H hHG hGH,
        Z_selection J hNil H hHG hGH α b _ v hv hmode]
      simp
    have hbox (d : Index D →₀ ℕ) (hd : d ∉ box) : f d = 0 := by
      dsimp only [f]
      rw [coefficient_outside_box J hNil H hHG _ d hd, Submodule.coe_zero, map_zero]
    have hsum : (∑ d ∈ box, f d) = ∑ d ∈ weightedLevel k, f d := by
      calc
        _ = ∑ d ∈ box ∪ weightedLevel k, f d :=
          Finset.sum_subset Finset.subset_union_left (by intro d hd hn; exact hbox d hn)
        _ = _ := (Finset.sum_subset Finset.subset_union_right
          (by intro d hd hn; exact hselect d hn)).symm
    calc
      E J α m v.val = ∑ d ∈ box, f d := by
        calc
          _ = ∑ d ∈ Finset.Iic ((W J hNil H hHG).jointCutoff (E J α m v.val)),
              (WeylData.factorial d : ℂ)⁻¹ •
                (W J hNil H hHG).creation d
                  ((W J hNil H hHG).vacuumProjection
                    ((W J hNil H hHG).derivative d (E J α m v.val))) :=
            ((W J hNil H hHG).taylor_reconstruction (E J α m v.val)).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro d hd
            dsimp only [f, WeylData.coefficient, LinearMap.smul_apply,
              LinearMap.comp_apply]
            rw [Submodule.coe_smul, map_smul]
            rfl
      _ = ∑ d ∈ weightedLevel k,
          taylorScalar α d • (W J hNil H hHG).creation d
            (S J hNil H hHG hGH α b v : M) := by
        rw [hsum]
        apply Finset.sum_congr rfl
        intro d hd
        have hw := (mem_weightedLevel k d).mp hd
        have hi : m + occupationWeight d = -weightPairing α b - 1 := by
          dsimp [t] at hk
          omega
        dsimp only [f]
        rw [coefficient_E_ground_raw J hNil H hHG hGH, hi, map_smul]
        rfl
      _ = _ := by
        rw [creationCoeff_partition, if_neg ht]
        simp only [creationPartition, map_sum, partitionTerm, map_smul,
          LinearMap.sum_apply, LinearMap.smul_apply, polynomialOperator_monomial,
          one_smul]
        rfl

/-- A linear finite coefficient convolution. Using lsum makes the addition
and subtraction laws independent of incidental polynomial supports. -/
def translatedModes (α : Charge D) (m : ℤ) :
    Polynomial (Oscillator D) →ₗ[ℂ] Module.End ℂ M :=
  Polynomial.lsum (fun j =>
    (LinearMap.mulRight ℂ (E J α (m-j))).comp (polynomialOperator J hNil H hHG))

theorem translatedModes_expansion (α : Charge D) (m : ℤ)
    (Q : Polynomial (Oscillator D)) (v : M) :
    translatedModes J hNil H hHG α m Q v =
      ∑ j ∈ Q.support, polynomialOperator J hNil H hHG (Q.coeff j)
        (E J α (m-j) v) := by
  simp only [translatedModes, Polynomial.lsum_apply, Polynomial.sum,
    LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.sum_apply,
    Module.End.mul_apply]

private theorem translatedModes_monomial (α : Charge D) (m : ℤ)
    (j : ℕ) (P : Oscillator D) :
    translatedModes J hNil H hHG α m (Polynomial.monomial j P) =
      polynomialOperator J hNil H hHG P * E J α (m-j) := by
  simp [translatedModes, Polynomial.lsum, Polynomial.sum_monomial_index]

private theorem translatedModes_C_mul (α : Charge D) (m : ℤ)
    (P : Oscillator D) (Q : Polynomial (Oscillator D)) :
    translatedModes J hNil H hHG α m (Polynomial.C P * Q) =
      polynomialOperator J hNil H hHG P * translatedModes J hNil H hHG α m Q := by
  induction Q using Polynomial.induction_on' with
  | add Q R hq hr => simp only [mul_add, map_add, hq, hr]
  | monomial j Q =>
    rw [Polynomial.C_mul_monomial, translatedModes_monomial,
      translatedModes_monomial, polynomialOperator_mul, mul_assoc]

private theorem translatedModes_mul_X_pow (α : Charge D) (m : ℤ)
    (Q : Polynomial (Oscillator D)) (k : ℕ) :
    translatedModes J hNil H hHG α m (Q * Polynomial.X ^ k) =
      translatedModes J hNil H hHG α (m-k) Q := by
  induction Q using Polynomial.induction_on' with
  | add Q R hq hr => simp only [add_mul, map_add, hq, hr]
  | monomial j P =>
    rw [Polynomial.monomial_mul_X_pow, translatedModes_monomial,
      translatedModes_monomial]
    congr 2
    push_cast
    ring

/-- Actual creator induction, on all M before restriction to ground.
Every coefficient of translatedPolynomial is consumed at the mode m-j. -/
theorem E_polynomial (α : Charge D) (P : Oscillator D) (m : ℤ) :
    E J α m * polynomialOperator J hNil H hHG P =
      translatedModes J hNil H hHG α m (translatedPolynomial D α P) := by
  classical
  induction P using MvPolynomial.induction_on generalizing m with
  | C c =>
    have hc : (MvPolynomial.C c : Oscillator D) = c • 1 := MvPolynomial.C_eq_smul_one
    simp [hc, translatedPolynomial, translatedModes_monomial,
      ← Polynomial.monomial_zero_left, polynomialOperator_one, mul_smul_comm]
  | add P Q hp hq => simp only [translatedPolynomial, map_add, mul_add, hp, hq]
  | mul_X P x hp =>
    have hc : (bilinear D α (unitCharge D x.1) : ℂ) =
        (bilinear D (unitCharge D x.1) α : ℂ) := by
      rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D α (unitCharge D x.1)]
    have he (m : ℤ) : E J α m * creation J x.1 x.2 =
        creation J x.1 x.2 * E J α m -
          (bilinear D (unitCharge D x.1) α : ℂ) • E J α (m-(x.2+1)) := by
      exact LinearMap.ext (E_creation J α m x)
    have hτ : translatedPolynomial D α (MvPolynomial.X x * P) =
        Polynomial.C (MvPolynomial.X x) * translatedPolynomial D α P -
          Polynomial.C ((bilinear D α (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) *
            (translatedPolynomial D α P * Polynomial.X ^ (x.2+1)) := by
      simp only [translatedPolynomial, map_mul, MvPolynomial.eval₂Hom_X', translationVariable]
      ring
    have hX : polynomialOperator J hNil H hHG (MvPolynomial.X x) =
        creation J x.1 x.2 := by
      simpa only [mul_one, polynomialOperator_one] using
        polynomialOperator_X_mul J hNil H hHG x 1
    rw [mul_comm P (MvPolynomial.X x), polynomialOperator_X_mul,
      ← mul_assoc, he, sub_mul, smul_mul_assoc, mul_assoc, hp, hp]
    change _ = translatedModes J hNil H hHG α m
      (translatedPolynomial D α (MvPolynomial.X x * P))
    rw [hτ, map_sub, translatedModes_C_mul, translatedModes_C_mul,
      translatedModes_mul_X_pow, hX, map_smul, polynomialOperator_one, hc,
      smul_mul_assoc, one_mul]
    simp only [Nat.cast_add, Nat.cast_one]

/-- Arbitrary polynomial on a true ground vector. The creation cutoff
increases by j precisely because the field mode is m-j. -/
theorem E_polynomial_ground (α b : Charge D) (m : ℤ) (P : Oscillator D)
    (v : Omega J) (hv : v ∈ jointWeight J b) :
    E J α m (polynomialOperator J hNil H hHG P v.val) =
      ∑ j ∈ (translatedPolynomial D α P).support,
        polynomialOperator J hNil H hHG
          ((translatedPolynomial D α P).coeff j *
            creationCoeff D α (-m - 1 - weightPairing α b + j))
          (S J hNil H hHG hGH α b v : M) := by
  rw [← Module.End.mul_apply, E_polynomial, translatedModes_expansion]
  apply Finset.sum_congr rfl
  intro j hj
  have ht : -(m - (j : ℤ)) - 1 - weightPairing α b =
      -m - 1 - weightPairing α b + j := by omega
  rw [E_ground J hNil H hHG hGH α b (m-j) v hv, ht,
    polynomialOperator_mul, Module.End.mul_apply]

end D5.S3.VertexAlgebra.Modules.ActualGroundFieldReconstruction
