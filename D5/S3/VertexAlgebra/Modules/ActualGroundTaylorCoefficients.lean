/-
SOURCE_ONLY_UNCOMPILED.

Actual normalized-current derivatives of E_alpha, factorial Taylor
coefficients, and their opposite-charge scalar. No binomial identity or
spectral resolution is assumed. The remaining weighted-partition sum is
named explicitly by `oppositeTaylorScalar` below, not replaced by a desired
binomial coefficient in a premise. ActualGroundPartitionScalar proves its
finite level sum; ActualGroundSpectralResolution performs the regrouping.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundFiniteReconstruction
import Mathlib.RingTheory.Binomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Modules.ActualGroundTaylorCoefficients

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

include hHG in
theorem inverse_row_pairing (α : Charge D) (i : Fin D.rank) :
    (∑ j, H i j * (bilinear D (unitCharge D j) α : ℂ)) = (α i : ℂ) := by
  classical
  have hrow (k : Fin D.rank) :
      (∑ j, H i j * (D.G j k : ℂ)) = if i = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, gramComplex, Matrix.map_apply, Matrix.one_apply] using
      congrArg (fun A : Matrix (Fin D.rank) (Fin D.rank) ℂ => A i k) hHG
  have hb (j : Fin D.rank) : (bilinear D (unitCharge D j) α : ℂ) =
      ∑ k, (D.G j k : ℂ) * (α k : ℂ) := by
    simp [bilinear, unitCharge]
  simp_rw [hb, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hrow]
  simp

def normalizedCharge (α : Charge D) (x : Index D) : ℂ :=
  (x.2 + 1 : ℂ)⁻¹ * (α x.1 : ℂ)

include hHG in
/-- HG contracts the exact original-current charged commutator. -/
theorem normalized_D_E_commutator (α : Charge D) (x : Index D) (t : ℤ) :
    annihilation J H x.1 x.2 * E J α t - E J α t * annihilation J H x.1 x.2 =
      normalizedCharge α x • E J α (t + (x.2 + 1)) := by
  classical
  rw [annihilation, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    rowMode, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, current_E_commutator,
    smul_smul]
  rw [← Finset.sum_smul, inverse_row_pairing H hHG α x.1, smul_smul]
  have hi : (x.2 : ℤ) + 1 + t = t + (x.2 + 1) := by omega
  rw [hi]
  rfl

include hHG in
theorem normalized_D_E_ground (α : Charge D) (x : Index D) (t : ℤ) (v : Omega J) :
    annihilation J H x.1 x.2 (E J α t v.val) =
      normalizedCharge α x • E J α (t + (x.2 + 1)) v.val := by
  have hv : annihilation J H x.1 x.2 v.val = 0 := by
    simp [annihilation, rowMode, (mem_Omega J v.val).mp v.property]
  have h := LinearMap.congr_fun (normalized_D_E_commutator J H hHG α x t) v.val
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    hv, map_zero, sub_zero] using h

def derivativeScalar (α : Charge D) (d : Index D →₀ ℕ) : ℂ :=
  d.prod (fun x n => normalizedCharge α x ^ n)

@[simp] theorem derivativeScalar_zero (α : Charge D) :
    derivativeScalar α (0 : Index D →₀ ℕ) = 1 := by simp [derivativeScalar]

theorem derivativeScalar_add_single (α : Charge D) (d : Index D →₀ ℕ) (x : Index D) :
    derivativeScalar α (d + Finsupp.single x 1) =
      normalizedCharge α x * derivativeScalar α d := by
  rw [derivativeScalar, Finsupp.prod_add_index' (by intro i; simp)
    (by intro i a b; exact pow_add _ _ _)]
  simp [derivativeScalar, Finsupp.prod_single_index, mul_comm]

/-- Exact positive-current derivative formula on ground inputs. The
frequency shifts are proved from the actual commutator, not assumed. -/
theorem derivative_E_ground (α : Charge D) (d : Index D →₀ ℕ) :
    ∀ (t : ℤ) (v : Omega J),
      (W J hNil H hHG).derivative d (E J α t v.val) =
        derivativeScalar α d • E J α (t + occupationWeight d) v.val := by
  classical
  induction d using Finsupp.induction with
  | zero => intro t v; simp
  | single_add x n d hx hn ih =>
    have hall : ∀ k : ℕ, ∀ (t : ℤ) (v : Omega J),
        (W J hNil H hHG).derivative (d + Finsupp.single x k) (E J α t v.val) =
          derivativeScalar α (d + Finsupp.single x k) •
            E J α (t + occupationWeight (d + Finsupp.single x k)) v.val := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        intro t v
        have he : d + Finsupp.single x (k + 1) =
            (d + Finsupp.single x k) + Finsupp.single x 1 := by
          rw [Finsupp.single_add]
          abel
        have hop : (W J hNil H hHG).derivative
            ((d + Finsupp.single x k) + Finsupp.single x 1) =
              (W J hNil H hHG).D x *
                (W J hNil H hHG).derivative (d + Finsupp.single x k) :=
          WeylData.monomialOperator_add_single _ _ _ _
        rw [he, hop, Module.End.mul_apply, ihk, map_smul]
        change derivativeScalar α (d + Finsupp.single x k) •
          annihilation J H x.1 x.2
            (E J α (t + occupationWeight (d + Finsupp.single x k)) v.val) = _
        rw [normalized_D_E_ground J H hHG, smul_smul, derivativeScalar_add_single,
          occupationWeight_add_single]
        rw [mul_comm (derivativeScalar α (d + Finsupp.single x k))]
        congr 2
        push_cast
        ring
    simpa only [add_comm (Finsupp.single x n) d] using hall n

/-- Every actual Taylor coefficient is a scalar multiple of an actual Z
mode, with the factorial and frequency normalizations visible. -/
theorem coefficient_E_ground (α : Charge D) (d : Index D →₀ ℕ) (t : ℤ) (v : Omega J) :
    vacuumToOmega J hNil H hHG hGH
      ((W J hNil H hHG).coefficient d (E J α t v.val)) =
        ((WeylData.factorial d : ℂ)⁻¹ * derivativeScalar α d) •
          Z J hNil H hHG hGH α (t + occupationWeight d) v := by
  apply Subtype.ext
  simp only [vacuumToOmega_coe, WeylData.coefficient, LinearMap.smul_apply,
    LinearMap.comp_apply, Submodule.coe_smul, WeylData.vacuumProject_coe,
    derivative_E_ground, map_smul, smul_smul, Z_coe, Pi]

/-- Exact scalar produced by opposite-charge creation commutation and
the actual normalized Taylor coefficient. It is not defined as a binomial. -/
def oppositeTaylorScalar (α : Charge D) (d : Index D →₀ ℕ) : ℂ :=
  (WeylData.factorial d : ℂ)⁻¹ * derivativeScalar α d * occupationScalar (-α) d

/-- The finite reconstruction's summands are actual opposite Z pairs,
with all scalar factors explicit. The remaining task is scalar regrouping. -/
theorem groundTerm_opposite_pair (α : Charge D) (p : ℤ) (q j : ℕ)
    (d : Index D →₀ ℕ) (v : Omega J) :
    groundTerm J hNil H hHG hGH α p q j d v =
      oppositeTaylorScalar α d •
        Z J hNil H hHG hGH (-α) (p + q - 1 - j - occupationWeight d)
          (Z J hNil H hHG hGH α (-p - 1 + j + occupationWeight d) v) := by
  change occupationScalar (-α) d •
    Z J hNil H hHG hGH (-α) (p + q - 1 - j - occupationWeight d)
      (vacuumToOmega J hNil H hHG hGH
        ((W J hNil H hHG).coefficient d (E J α (-p - 1 + j) v.val))) = _
  rw [coefficient_E_ground, map_smul, smul_smul]
  congr 1
  dsimp only [oppositeTaylorScalar]
  ring

/-- Conversion to the requested Q operators requires no spectral premise.
This is a finite weighted expansion, NOT yet the coefficient-one resolution. -/
theorem groundTerm_Q (α : Charge D) (p : ℤ) (q j : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (d : Index D →₀ ℕ) (v : Omega J) :
    groundTerm J hNil H hHG hGH α p q j d v =
      (oppositeTaylorScalar α d * epsilon D (-α) α) •
        Q J hNil H hHG hGH α (p - j - occupationWeight d) v := by
  rw [groundTerm_opposite_pair]
  simp only [Q, LinearMap.smul_apply, Module.End.mul_apply, smul_smul]
  have hs : p + (q : ℤ) - 1 - j - occupationWeight d =
      bilinear D α α + (p - j - occupationWeight d) - 1 := by omega
  have ht : -p - 1 + (j : ℤ) + occupationWeight d =
      -(p - j - occupationWeight d) - 1 := by omega
  rw [hs, ht, mul_assoc, mul_inv_cancel₀ (original_epsilon_nonzero (-α) α), mul_one]

/-- An actual finite Q expansion with explicit weights. This conclusion is
strictly before, and does not assume, the coefficient-one Q resolution. -/
theorem finite_weighted_Q_reconstruction (α : Charge D) (q : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (hqpos : 0 < q) (p : ℤ) (v : Omega J)
    (hcut : ∀ n : ℤ, p ≤ n → E J (-α) n v.val = 0) :
    v = ∑ j ∈ Finset.range q,
      (((-1 : ℂ)^j) * StateFieldResidueReconstruction.integerBinomial ((q : ℤ) - 1) j) •
        ∑ d ∈ innerBox J hNil H hHG α p j v,
          oppositeTaylorScalar α d • Q J hNil H hHG hGH α (p - j - occupationWeight d) v := by
  have hrec := finite_ground_reconstruction J hNil H hHG hGH α q hq hqpos p v hcut
  have hc := original_epsilon_nonzero (-α) α
  calc
    v = (epsilon D (-α) α)⁻¹ • (epsilon D (-α) α • v) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := by
      rw [hrec, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [groundTerm_Q J hNil H hHG hGH α p q j hq d v]
      simp only [smul_smul]
      congr 1
      field_simp [hc]
      <;> ring

/-- A finite universal box contains every occupation of weight at most K.
It contains no oscillator frequency greater than K. -/
def weightBox (K : ℕ) : Index D →₀ ℕ :=
  Finsupp.onFinset (Finset.univ ×ˢ Finset.range K)
    (fun x => if x.2 < K then K else 0)
    (by
      intro x hx
      by_contra hn
      apply hx
      have hl : ¬ x.2 < K := by simpa using hn
      simp [hl])

theorem le_weightBox (K : ℕ) (d : Index D →₀ ℕ) (hd : occupationWeight d ≤ K) :
    d ≤ weightBox K := by
  intro x
  by_cases hx : d x = 0
  · simp [hx]
  · have hfreq := Finsupp.le_weight_of_ne_zero'
      (w := fun y : Index D => y.2 + 1) hx
    have hcoord := Finsupp.le_weight (fun y : Index D => y.2 + 1)
      (s := x) (by omega) d
    have hl : x.2 < K := by change x.2 + 1 ≤ occupationWeight d at hfreq; omega
    simpa only [weightBox, Finsupp.onFinset_apply, if_pos hl] using le_trans hcoord hd

def weightedSublevel (K : ℕ) : Finset (Index D →₀ ℕ) :=
  (Finset.Iic (weightBox K)).filter (fun d => occupationWeight d ≤ K)

def weightedLevel (K : ℕ) : Finset (Index D →₀ ℕ) :=
  (weightedSublevel K).filter (fun d => occupationWeight d = K)

@[simp] theorem mem_weightedSublevel (K : ℕ) (d : Index D →₀ ℕ) :
    d ∈ weightedSublevel K ↔ occupationWeight d ≤ K := by
  simp only [weightedSublevel, Finset.mem_filter, Finset.mem_Iic]
  exact ⟨And.right, fun h => ⟨le_weightBox K d h, h⟩⟩

@[simp] theorem mem_weightedLevel (K : ℕ) (d : Index D →₀ ℕ) :
    d ∈ weightedLevel K ↔ occupationWeight d = K := by
  simp only [weightedLevel, Finset.mem_filter, mem_weightedSublevel]
  exact ⟨And.right, fun h => ⟨h.le, h⟩⟩

/-- The actual finite scalar sum. Its partition recurrence is proved in
ActualGroundPartitionScalar, rather than supplied as a premise. -/
def weightedScalarSum (α : Charge D) (k : ℕ) : ℂ :=
  ∑ d ∈ weightedLevel k, oppositeTaylorScalar α d

theorem derivative_vanish_of_weight_cutoff (α : Charge D) (d : Index D →₀ ℕ)
    (t R : ℤ) (v : Omega J) (hR : ∀ n : ℤ, R ≤ n → E J α n v.val = 0)
    (hd : R ≤ t + occupationWeight d) :
    (W J hNil H hHG).derivative d (E J α t v.val) = 0 := by
  rw [derivative_E_ground, hR _ hd, smul_zero]

/- The next two lemmas prove the finite q-1 difference calculation outright.
Their connection to weightedScalarSum is supplied by
ActualGroundPartitionScalar.weightedScalarSum_eq_rising. -/

def risingCoefficient (q k : ℕ) : ℂ :=
  (-1 : ℂ)^k * StateFieldResidueReconstruction.integerBinomial (-(q : ℤ)) k

theorem risingCoefficient_eq_choose (q k : ℕ) (hq : 0 < q) :
    risingCoefficient q k = ((q + k - 1).choose k : ℂ) := by
  have hb : StateFieldResidueReconstruction.integerBinomial (-(q : ℤ)) k =
      (-1 : ℂ)^k * ((q + k - 1).choose k : ℂ) := by
    unfold StateFieldResidueReconstruction.integerBinomial
    rw [Ring.choose_neg,
      show (q : ℤ) + k - 1 = ((q + k - 1 : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
      Int.cast_negOnePow_natCast, Int.cast_natCast]
  have hs : (-1 : ℂ)^k * (-1 : ℂ)^k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [risingCoefficient, hb, ← mul_assoc, hs, one_mul]

/-- Finite Chu--Vandermonde proof of all q-1 backward differences = 1.
The sum is finite at every natural l, with no generating-series limit. -/
theorem finite_difference_one (q l : ℕ) :
    (∑ j ∈ Finset.range (l + 1),
      ((-1 : ℂ)^j * StateFieldResidueReconstruction.integerBinomial ((q : ℤ) - 1) j) *
        risingCoefficient q (l - j)) = 1 := by
  have hv := Ring.add_choose_eq (r := (q : ℤ) - 1) (s := -(q : ℤ)) l
    (Commute.all _ _)
  rw [show (q : ℤ) - 1 + -(q : ℤ) = -1 by omega,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hvc := congrArg (Int.cast : ℤ → ℂ) hv
  have hsum :
      (∑ j ∈ Finset.range (l + 1),
        StateFieldResidueReconstruction.integerBinomial ((q : ℤ) - 1) j *
          StateFieldResidueReconstruction.integerBinomial (-(q : ℤ)) (l - j)) =
        StateFieldResidueReconstruction.integerBinomial (-1) l := by
    simpa only [StateFieldResidueReconstruction.integerBinomial,
      Int.cast_sum, Int.cast_mul] using hvc.symm
  calc
    _ = (-1 : ℂ)^l *
        ∑ j ∈ Finset.range (l + 1),
          StateFieldResidueReconstruction.integerBinomial ((q : ℤ) - 1) j *
            StateFieldResidueReconstruction.integerBinomial (-(q : ℤ)) (l - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjl : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have he : (-1 : ℂ)^j * (-1 : ℂ)^(l - j) = (-1 : ℂ)^l := by
        rw [← pow_add, Nat.add_sub_of_le hjl]
      dsimp only [risingCoefficient]
      calc
        _ = ((-1 : ℂ)^j * (-1 : ℂ)^(l-j)) *
          (StateFieldResidueReconstruction.integerBinomial ((q : ℤ)-1) j *
            StateFieldResidueReconstruction.integerBinomial (-(q : ℤ)) (l-j)) := by ring
        _ = _ := by rw [he]
    _ = 1 := by
      rw [hsum]
      exact LatticeActualStateFieldCalculus.minus_one_binomial l

end D5.S3.VertexAlgebra.Modules.ActualGroundTaylorCoefficients
