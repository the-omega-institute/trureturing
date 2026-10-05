/- GID: D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeGeneratingFieldLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual lattice creation coefficients have graded binomial contraction. -/

/-
   The arbitrary-rank charge-changing fields use the prescribed exponential
   creation coefficients and polynomial translations of Bakalov--Kac, section
   4.1. Translation of each actual creation coefficient gives its binomial
   contraction. The two common-kernel product equations and uniform locality
   remain unproved.
-/
import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic


set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- The integral symmetric form used by the lattice fields. -/
structure LatticeData where
  rank : ℕ
  G : Matrix (Fin rank) (Fin rank) ℤ
  symmetric : ∀ i j, G i j = G j i
  even_diagonal : ∀ i, Even (G i i)

abbrev Charge (D : LatticeData) := Fin D.rank → ℤ

abbrev Index (D : LatticeData) := Fin D.rank × ℕ

abbrev Oscillator (D : LatticeData) := MvPolynomial (Index D) ℂ

abbrev Carrier (D : LatticeData) := Charge D →₀ Oscillator D

def unitCharge (D : LatticeData) (i : Fin D.rank) : Charge D :=
  fun j => if j = i then 1 else 0

/-- The integral bilinear form, with no positivity assumption. -/
def bilinear (D : LatticeData) (α β : Charge D) : ℤ :=
  ∑ i, ∑ j, α i * D.G i j * β j

def halfDiagonal (D : LatticeData) (i : Fin D.rank) : ℤ :=
  D.G i i / 2

def lowerCocycleExponent (D : LatticeData) (α β : Charge D) : ℤ :=
  (Finset.sum Finset.univ (fun i =>
    Finset.sum (Finset.univ.filter (fun j : Fin D.rank => j < i))
      (fun j => D.G i j * α i * β j))) +
    Finset.sum Finset.univ (fun i => halfDiagonal D i * α i * β i)

/-- Integer parity sign, avoiding Laurent-series integer powers. -/
def paritySign (n : ℤ) : ℂ := if Even n then 1 else -1

def epsilon (D : LatticeData) (α β : Charge D) : ℂ :=
  paritySign (lowerCocycleExponent D α β)

def creationSeries (D : LatticeData) (α : Charge D) : PowerSeries (Oscillator D) :=
  PowerSeries.mk (fun q =>
    if _ : q = 0 then 0 else
      ((q : ℂ)⁻¹) •
        ∑ i : Fin D.rank, (α i : ℂ) • (X (i, q - 1) : Oscillator D))

def creationExponential (D : LatticeData) (α : Charge D) : PowerSeries (Oscillator D) :=
  (PowerSeries.exp (Oscillator D)).subst (creationSeries D α)

def creationCoeff (D : LatticeData) (α : Charge D) (t : ℤ) : Oscillator D :=
  if _ : t < 0 then 0
  else PowerSeries.coeff t.toNat (creationExponential D α)

def translationVariable (D : LatticeData) (α : Charge D)
    (i : Fin D.rank) (n : ℕ) : Polynomial (Oscillator D) :=
  Polynomial.C (X (i, n) : Oscillator D) -
    Polynomial.C (((bilinear D α (unitCharge D i) : ℂ) • (1 : Oscillator D))) *
      Polynomial.X ^ (n + 1)

def translatedPolynomial (D : LatticeData) (α : Charge D) (p : Oscillator D) :
    Polynomial (Oscillator D) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : Oscillator D →+* Polynomial (Oscillator D)).comp (algebraMap ℂ _))
    (fun i : Index D => translationVariable D α i.1 i.2) p

def rawSingle (D : LatticeData) (α : Charge D) (k : ℤ)
    (δ : Charge D) (p : Oscillator D) : Carrier D :=
  epsilon D α δ • Finsupp.single (α + δ)
    (Finset.sum (translatedPolynomial D α p).support (fun d =>
      (translatedPolynomial D α p).coeff d •
        creationCoeff D α (k - bilinear D α δ + d)))

def rawPolynomialMap (D : LatticeData) (α : Charge D) (k : ℤ)
    (δ : Charge D) : Oscillator D →ₗ[ℂ] Carrier D :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun e => rawSingle D α k δ (monomial e 1))

/-- The actual raw coefficient on arbitrary finite-charge states. -/
def rawCoeff (D : LatticeData) (α : Charge D) (k : ℤ) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun δ : Charge D => rawPolynomialMap D α k δ)

abbrev PairPolynomial (D : LatticeData) := MvPolynomial (Fin 2) (Oscillator D)

def translatedPairPolynomial (D : LatticeData) (α β : Charge D)
    (p : Oscillator D) : PairPolynomial D :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : Oscillator D →+* PairPolynomial D).comp (algebraMap ℂ _))
    (fun i : Index D =>
      MvPolynomial.C (X i : Oscillator D) -
        MvPolynomial.C (((bilinear D α (unitCharge D i.1) : ℂ) • (1 : Oscillator D))) *
          MvPolynomial.X 0 ^ (i.2 + 1) -
        MvPolynomial.C (((bilinear D β (unitCharge D i.1) : ℂ) • (1 : Oscillator D))) *
          MvPolynomial.X 1 ^ (i.2 + 1)) p

def commonKernelSingle (D : LatticeData) (α β : Charge D)
    (u v : ℤ) (δ : Charge D) (p : Oscillator D) : Carrier D :=
  epsilon D (α + β) δ • Finsupp.single (α + β + δ)
    (Finset.sum (translatedPairPolynomial D α β p).support (fun e =>
      (translatedPairPolynomial D α β p).coeff e *
        creationCoeff D α (u - bilinear D α δ + e 0) *
        creationCoeff D β (v - bilinear D β δ + e 1)))

def commonKernelPolynomialMap (D : LatticeData) (α β : Charge D)
    (u v : ℤ) (δ : Charge D) : Oscillator D →ₗ[ℂ] Carrier D :=
  (MvPolynomial.basisMonomials (Index D) ℂ).constr ℂ
    (fun e => commonKernelSingle D α β u v δ (monomial e 1))

/-- The same two-variable kernel is used by both ordered products. -/
def commonKernel (D : LatticeData) (α β : Charge D) (u v : ℤ) :
    Carrier D →ₗ[ℂ] Carrier D :=
  Finsupp.lsum ℂ (fun δ : Charge D => commonKernelPolynomialMap D α β u v δ)

def localityExponent (D : LatticeData) (α β : Charge D) : ℕ :=
  (-bilinear D α β).toNat

/-- The prescribed raw coefficient family, with a statewise finite lower bound. -/
def actualField (D : LatticeData) (α : Charge D) : VertexOperator ℂ (Carrier D) :=
  VertexOperator.of_coeff (rawCoeff D α) (by
    classical
    have hsum {ι : Type} (s : Finset ι) (q : ι → ℤ → Carrier D)
        (hq : ∀ i ∈ s, ∃ m : ℤ, ∀ k < m, q i k = 0) :
        ∃ m : ℤ, ∀ k < m, (∑ i ∈ s, q i k) = 0 := by
      induction s using Finset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | @insert i s hi ih =>
        obtain ⟨m, hm⟩ := hq i (Finset.mem_insert_self i s)
        obtain ⟨n, hn⟩ := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
        refine ⟨min m n, ?_⟩
        intro k hk
        rw [Finset.sum_insert hi, hm k (lt_of_lt_of_le hk (min_le_left _ _)),
          hn k (lt_of_lt_of_le hk (min_le_right _ _)), add_zero]
    have hsingle (δ : Charge D) (p : Oscillator D) :
        ∃ m : ℤ, ∀ k < m, rawSingle D α k δ p = 0 := by
      let q := translatedPolynomial D α p
      refine ⟨bilinear D α δ - q.support.sup id, ?_⟩
      intro k hk
      have hz : ∑ d ∈ q.support, q.coeff d • creationCoeff D α (k - bilinear D α δ + d) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        have hd' : d ≤ q.support.sup id := Finset.le_sup (f := id) hd
        rw [creationCoeff, dif_pos (by omega), smul_zero]
      simp only [rawSingle, ← show q = translatedPolynomial D α p from rfl, hz,
        Finsupp.single_zero, smul_zero]
    have hpoly (δ : Charge D) (p : Oscillator D) :
        ∃ m : ℤ, ∀ k < m, rawPolynomialMap D α k δ p = 0 := by
      let repr := (MvPolynomial.basisMonomials (Index D) ℂ).repr p
      have hs := hsum repr.support
        (fun e k => repr e • rawSingle D α k δ (monomial e 1)) (by
          intro e he
          obtain ⟨m, hm⟩ := hsingle δ (monomial e 1)
          exact ⟨m, fun k hk => by rw [hm k hk, smul_zero]⟩)
      simpa only [rawPolynomialMap, Module.Basis.constr_apply, Finsupp.sum, repr] using hs
    intro v
    obtain ⟨m, hm⟩ := hsum v.support
      (fun δ k => rawPolynomialMap D α k δ (v δ)) (fun δ hδ => hpoly δ (v δ))
    refine ⟨m, ?_⟩
    intro k hk
    by_contra hle
    have hz : rawCoeff D α k v = 0 := by
      simpa only [rawCoeff, Finsupp.lsum_apply, Finsupp.sum] using hm k (by omega)
    exact hk hz)

def oscillatorWeight (D : LatticeData) (i : Index D) : ℕ := i.2 + 1

/-
proof_shape: actual_creation_coefficient_transport: content
admission_basis: escape-witness
escape_witness: The actual exponential coefficients are graded by oscillator
weight, and their translated recurrence forces the binomial contraction for
every integer creation index and every polynomial coefficient. The arbitrary
polynomial and finite-charge extensions agree with the prescribed formulas.
Classical source: Bakalov--Kac, arXiv math/0402315v1, section 4.1,
(4.12) and the annihilation--creation contraction used in (4.14).
-/
attribute [-instance] PowerSeries.algebraPolynomial in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The coefficient proof uses two strong inductions and a polynomial-valued recurrence.
theorem actual_creation_coefficient_transport (D : LatticeData) (α β : Charge D) :
    (∀ t : ℤ, MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
      (creationCoeff D β t) t.toNat) ∧
    (∀ (t : ℤ) (j : ℕ),
      (translatedPolynomial D α (creationCoeff D β t)).coeff j =
        (PowerSeries.coeff j (PowerSeries.rescale (-1 : ℂ)
          (PowerSeries.binomialSeries (R := ℤ) ℂ (bilinear D α β)))) •
            creationCoeff D β (t - j)) ∧
    (∀ (k : ℤ) (δ : Charge D) (p : Oscillator D),
      rawCoeff D α k (Finsupp.single δ p) = rawSingle D α k δ p) ∧
    (∀ (u v : ℤ) (δ : Charge D) (p : Oscillator D),
      commonKernel D α β u v (Finsupp.single δ p) = commonKernelSingle D α β u v δ p) := by
  classical
  have hweightNat : ∀ n : ℕ, MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
      (PowerSeries.coeff n (creationExponential D β)) n := by
    classical
    let A := creationSeries D β
    let C := creationExponential D β
    have hA : PowerSeries.constantCoeff A = 0 := by
      simp [A, creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hd : PowerSeries.derivative (Oscillator D) C =
        C * PowerSeries.derivative (Oscillator D) A := by
      dsimp [C, creationExponential]
      rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
        PowerSeries.derivative_exp]
    have hAn (n : ℕ) : PowerSeries.coeff n (PowerSeries.derivative (Oscillator D) A) =
        ∑ i : Fin D.rank, (β i : ℂ) • (X (i,n) : Oscillator D) := by
      rw [PowerSeries.coeff_derivative]
      simp only [A, creationSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceDIte,
        Nat.add_sub_cancel]
      rw [mul_comm, show (n + 1 : Oscillator D) = algebraMap ℂ (Oscillator D) (n + 1 : ℂ) by simp,
        ← Algebra.smul_def, smul_smul]
      rw [Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n),
        one_smul]
    have hc : PowerSeries.coeff 0 C = 1 := by
      dsimp [C, creationExponential]
      rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
        finsum_eq_single _ 0]
      · simp
      · intro j hj
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
        simp [hj]
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        rw [show PowerSeries.coeff 0 (creationExponential D β) = 1 from hc]
        exact MvPolynomial.isWeightedHomogeneous_one ℂ _
      | succ n =>
        have hrec := congrArg (PowerSeries.coeff n) hd
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hrec
        have hsum : MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
            (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
              PowerSeries.coeff ab.1 C *
                PowerSeries.coeff ab.2 (PowerSeries.derivative (Oscillator D) A)) (n+1) := by
          apply MvPolynomial.IsWeightedHomogeneous.sum
          intro ab hab
          have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
          have hfirst := ih ab.1 (by omega)
          have hsecond : MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
              (PowerSeries.coeff ab.2 (PowerSeries.derivative (Oscillator D) A)) (ab.2+1) := by
            rw [hAn]
            apply MvPolynomial.IsWeightedHomogeneous.sum
            intro i hi
            exact
              (MvPolynomial.weightedHomogeneousSubmodule ℂ (oscillatorWeight D) (ab.2+1)).smul_mem
              _ (MvPolynomial.isWeightedHomogeneous_X ℂ (oscillatorWeight D) (i,ab.2))
          simpa only [← Nat.add_assoc, hab'] using hfirst.mul hsecond
        rw [← hrec] at hsum
        intro e he
        apply hsum
        rw [show (n + 1 : Oscillator D) = MvPolynomial.C (n + 1 : ℂ) by simp,
          mul_comm, MvPolynomial.coeff_C_mul]
        exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) he
  classical
  let U : Polynomial (Oscillator D) := Polynomial.X
  let b := bilinear D α β
  let T : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) := MvPolynomial.eval₂AlgHom ℂ
    (fun i : Index D => translationVariable D α i.1 i.2)
  let a := (creationSeries D β).map T.toRingHom
  let a₀ := (creationSeries D β).map (Polynomial.C : Oscillator D →+* Polynomial (Oscillator D))
  let f := (creationExponential D β).map T.toRingHom
  let f₀ := (creationExponential D β).map
    (Polynomial.C : Oscillator D →+* Polynomial (Oscillator D))
  let H := PowerSeries.rescale (-U)
    (PowerSeries.binomialSeries (R := ℤ) (Polynomial (Oscillator D)) b)
  let E : PowerSeries (Polynomial (Oscillator D)) := 1 - PowerSeries.C U * PowerSeries.X
  have hS : PowerSeries.constantCoeff (creationSeries D β) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hMapD (h : Oscillator D →+* Polynomial (Oscillator D)) (s : PowerSeries (Oscillator D)) :
      PowerSeries.derivative (Polynomial (Oscillator D)) (s.map h) =
        (PowerSeries.derivative (Oscillator D) s).map h := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.coeff_derivative, map_mul]
    simp only [map_add, map_natCast, map_one]
  have hAn (n : ℕ) :
      PowerSeries.coeff n (PowerSeries.derivative (Oscillator D) (creationSeries D β)) =
        ∑ i : Fin D.rank, (β i : ℂ) • (X (i,n) : Oscillator D) := by
    rw [PowerSeries.coeff_derivative]
    simp only [creationSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceDIte,
      Nat.add_sub_cancel]
    rw [mul_comm, show (n + 1 : Oscillator D) = algebraMap ℂ (Oscillator D) (n + 1 : ℂ) by simp,
      ← Algebra.smul_def, smul_smul]
    rw [Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n),
      one_smul]
  have hB : (∑ i : Fin D.rank, (β i : ℂ) * (bilinear D α (unitCharge D i) : ℂ)) = (b : ℂ) := by
    have hi : (∑ i : Fin D.rank, β i * bilinear D α (unitCharge D i)) = b := by
      simp only [bilinear, unitCharge, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    exact_mod_cast hi
  have hCsmul (z : ℂ) (p : Oscillator D) :
      Polynomial.C (z • p) = z • (Polynomial.C p : Polynomial (Oscillator D)) :=
    map_smul (Polynomial.CAlgHom : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D)) z p
  have hDiff (n : ℕ) :
      PowerSeries.coeff n (PowerSeries.derivative (Polynomial (Oscillator D)) a -
        PowerSeries.derivative (Polynomial (Oscillator D)) a₀) =
        -((b : ℂ) • (1 : Oscillator D) |> Polynomial.C) * U^(n+1) := by
    rw [map_sub]
    dsimp only [a, a₀]
    rw [hMapD, hMapD, PowerSeries.coeff_map, PowerSeries.coeff_map, hAn]
    change T (∑ i : Fin D.rank, (β i : ℂ) • (X (i,n) : Oscillator D)) -
      Polynomial.C (∑ i : Fin D.rank, (β i : ℂ) • (X (i,n) : Oscillator D)) = _
    rw [map_sum, map_sum]
    simp only [map_smul, T, MvPolynomial.eval₂AlgHom_X, translationVariable, smul_sub,
      hCsmul, smul_mul_assoc, smul_smul, Finset.sum_sub_distrib]
    rw [sub_sub_cancel_left, ← Finset.sum_smul, hB]
    simp only [map_one, smul_mul_assoc, neg_mul, U]
  have hDiffSeries :
      PowerSeries.derivative (Polynomial (Oscillator D)) a -
        PowerSeries.derivative (Polynomial (Oscillator D)) a₀ =
      PowerSeries.mk (fun n : ℕ => -Polynomial.C ((b : ℂ) • (1 : Oscillator D)) * U^(n+1)) := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_mk]
    exact hDiff n
  have hDiffE : (PowerSeries.derivative (Polynomial (Oscillator D)) a -
    PowerSeries.derivative (Polynomial (Oscillator D)) a₀) * E =
      -PowerSeries.C (Polynomial.C ((b : ℂ) • (1 : Oscillator D)) * U) := by
    rw [hDiffSeries]
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simp only [E, mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_zero_mul_X, sub_zero, PowerSeries.coeff_mk,
        map_neg, PowerSeries.coeff_zero_C]
      ring
    | succ n =>
      simp only [E, mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
        PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_C,
        Nat.succ_ne_zero, if_false]
      simp only [pow_succ]
      ring
  have hChoose (n : ℕ) : (n + 1 : ℤ) * Ring.choose b (n+1) =
      (b - n) * Ring.choose b n := by
    apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
    have h := Ring.descPochhammer_eq_factorial_smul_choose b (n+1)
    rw [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
      pow_one, pow_zero, nsmul_one,
      Ring.descPochhammer_eq_factorial_smul_choose, Nat.factorial_succ] at h
    simp only [nsmul_eq_mul] at h ⊢
    push_cast at h
    nlinarith [h]
  have hHcoef (n : ℕ) : PowerSeries.coeff n H =
      (-U)^n * ((Ring.choose b n : ℤ) : Polynomial (Oscillator D)) := by
    dsimp only [H]
    rw [PowerSeries.coeff_rescale]
    rw [PowerSeries.binomialSeries_coeff (R := ℤ)]
    rw [zsmul_eq_mul, mul_one]
  have hb : Polynomial.C ((b : ℂ) • (1 : Oscillator D)) = (b : Polynomial (Oscillator D)) := by
    simp [Algebra.smul_def]
  have hHE : PowerSeries.derivative (Polynomial (Oscillator D)) H * E =
      -PowerSeries.C (Polynomial.C ((b : ℂ) • (1 : Oscillator D)) * U) * H := by
    rw [hb]
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      dsimp only [E]
      rw [mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_zero_mul_X, sub_zero,
        PowerSeries.coeff_derivative, neg_mul, map_neg, PowerSeries.coeff_C_mul,
        hHcoef, hHcoef]
      simp
      ring
    | succ n =>
      dsimp only [E]
      rw [mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
        PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
        neg_mul, map_neg, PowerSeries.coeff_C_mul]
      simp only [hHcoef]
      have hr : (n + 2 : Polynomial (Oscillator D)) *
          ((Ring.choose b (n+2) : ℤ) : Polynomial (Oscillator D)) =
          ((b : Polynomial (Oscillator D)) - (n+1 : Polynomial (Oscillator D))) *
            ((Ring.choose b (n+1) : ℤ) : Polynomial (Oscillator D)) := by
        have hc := congrArg (Int.castRingHom (Polynomial (Oscillator D))) (hChoose (n+1))
        simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast,
          Int.cast_one, Int.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
          one_add_one_eq_two] using hc
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      linear_combination (-U)^(n+1) * (-U) * hr
  have hu : IsUnit E := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [E])
  have hDH : PowerSeries.derivative (Polynomial (Oscillator D)) H =
      H * (PowerSeries.derivative (Polynomial (Oscillator D)) a -
        PowerSeries.derivative (Polynomial (Oscillator D)) a₀) := by
    apply hu.mul_right_cancel
    rw [hHE, mul_assoc, hDiffE]
    ring
  have hSourceD : PowerSeries.derivative (Oscillator D) (creationExponential D β) =
      creationExponential D β * PowerSeries.derivative (Oscillator D) (creationSeries D β) := by
    rw [creationExponential, PowerSeries.derivative_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hS), PowerSeries.derivative_exp]
  have hDa :
      PowerSeries.derivative (Polynomial (Oscillator D)) f =
        f * PowerSeries.derivative (Polynomial (Oscillator D)) a := by
    dsimp only [f, a]
    rw [hMapD, hSourceD, map_mul, hMapD]
  have hDa₀ :
      PowerSeries.derivative (Polynomial (Oscillator D)) f₀ =
        f₀ * PowerSeries.derivative (Polynomial (Oscillator D)) a₀ := by
    dsimp only [f₀, a₀]
    rw [hMapD, hSourceD, map_mul, hMapD]
  have hDG :
      PowerSeries.derivative (Polynomial (Oscillator D)) (f₀ * H) =
        (f₀ * H) * PowerSeries.derivative (Polynomial (Oscillator D)) a := by
    have h := (PowerSeries.derivative (Polynomial (Oscillator D))).leibniz f₀ H
    change PowerSeries.derivative (Polynomial (Oscillator D)) (f₀ * H) =
      f₀ * PowerSeries.derivative (Polynomial (Oscillator D)) H +
        H * PowerSeries.derivative (Polynomial (Oscillator D)) f₀ at h
    rw [h, hDa₀, hDH]
    ring
  have hC : PowerSeries.coeff 0 f = PowerSeries.coeff 0 (f₀ * H) := by
    have hc : PowerSeries.coeff 0 (creationExponential D β) = 1 := by
      rw [creationExponential, PowerSeries.coeff_subst'
        (PowerSeries.HasSubst.of_constantCoeff_zero' hS), finsum_eq_single _ 0]
      · simp
      · intro j hj
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hS]
        simp [hj]
    rw [show f = (creationExponential D β).map T.toRingHom from rfl,
      PowerSeries.coeff_map, hc, map_one]
    change 1 = PowerSeries.coeff 0
      ((creationExponential D β).map
        (Polynomial.C : Oscillator D →+* Polynomial (Oscillator D)) * H)
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero]
    simp only [Finset.sum_singleton, PowerSeries.coeff_map, hc, map_one, one_mul,
      hHcoef, pow_zero, one_mul, Ring.choose_zero_right]
    norm_num
  have heq : ∀ n : ℕ, PowerSeries.coeff n f = PowerSeries.coeff n (f₀ * H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact hC
      | succ n =>
        have h := congrArg (PowerSeries.coeff n) hDa
        have h' := congrArg (PowerSeries.coeff n) hDG
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
        rw [PowerSeries.coeff_derivative] at h'
        conv at h' => rhs; rw [PowerSeries.coeff_mul]
        have hs : (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ab.1 f *
              PowerSeries.coeff ab.2 (PowerSeries.derivative (Polynomial (Oscillator D)) a)) =
            ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ab.1 (f₀ *
              H) *
                PowerSeries.coeff ab.2 (PowerSeries.derivative (Polynomial (Oscillator D)) a) := by
          apply Finset.sum_congr rfl
          intro ab hab
          rw [ih ab.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hab; omega)]
        have hmul : PowerSeries.coeff (n+1) f * (n+1) =
            PowerSeries.coeff (n+1) (f₀ * H) * (n+1) := by rw [h, hs]; exact h'.symm
        rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul] at hmul
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hmul
  have hpolynomial (n : ℕ) :
      translatedPolynomial D α (PowerSeries.coeff n (creationExponential D β)) =
        ∑ j ∈ Finset.range (n+1),
          Polynomial.C ((PowerSeries.coeff j (PowerSeries.rescale (-1 : ℂ)
            (PowerSeries.binomialSeries (R := ℤ) ℂ b))) •
              PowerSeries.coeff (n-j) (creationExponential D β)) * U^j := by
    have hf := heq n
    dsimp only [f, f₀] at hf
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mul] at hf
    change translatedPolynomial D α (PowerSeries.coeff n (creationExponential D β)) = _ at hf
    calc
      _ = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
          Polynomial.C (PowerSeries.coeff ab.1 (creationExponential D β)) *
            PowerSeries.coeff ab.2 H := by
        simpa only [PowerSeries.coeff_map] using hf
      _ = ∑ j ∈ Finset.range (n+1),
          Polynomial.C (PowerSeries.coeff (n-j) (creationExponential D β)) *
            PowerSeries.coeff j H := by
        rw [← Finset.Nat.sum_antidiagonal_swap,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hHcoef, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff (R := ℤ)]
        simp only [zsmul_eq_mul, mul_one]
        rw [hCsmul]
        simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_intCast]
        rw [neg_pow]
        ring
  have hcoefficientNat (n j : ℕ) :
      (translatedPolynomial D α (PowerSeries.coeff n (creationExponential D β))).coeff j =
        if j ≤ n then (PowerSeries.coeff j (PowerSeries.rescale (-1 : ℂ)
          (PowerSeries.binomialSeries (R := ℤ) ℂ b))) •
            PowerSeries.coeff (n-j) (creationExponential D β) else 0 := by
    rw [hpolynomial]
    simp [Polynomial.finsetSum_coeff, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, U]
  have hExtensions :
      (∀ (k : ℤ) (δ : Charge D) (p : Oscillator D),
        rawCoeff D α k (Finsupp.single δ p) = rawSingle D α k δ p) ∧
      (∀ (u v : ℤ) (δ : Charge D) (p : Oscillator D),
        commonKernel D α β u v (Finsupp.single δ p) = commonKernelSingle D α β u v δ p) := by
    classical
    constructor
    · intro k δ p
      let T : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
        MvPolynomial.eval₂AlgHom ℂ (fun i : Index D => translationVariable D α i.1 i.2)
      let A : Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
        (Finsupp.lsum (Oscillator D) (fun d : ℕ =>
          LinearMap.mulRight (Oscillator D) (creationCoeff D α (k - bilinear D α δ + d)))).comp
          ((AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap.comp
            (Polynomial.toFinsuppIsoLinear (Oscillator D)).toLinearMap)
      let L : Oscillator D →ₗ[ℂ] Carrier D :=
        (epsilon D α δ • (Finsupp.lsingle (α+δ) : Oscillator D →ₗ[ℂ] Carrier D)).comp
          ((A.restrictScalars ℂ).comp T.toLinearMap)
      have hL (q : Oscillator D) : L q = rawSingle D α k δ q := by
        rfl
      have hmaps : rawPolynomialMap D α k δ = L := by
        apply (MvPolynomial.basisMonomials (Index D) ℂ).ext
        intro e
        rw [rawPolynomialMap, Module.Basis.constr_basis]
        exact (hL (monomial e 1)).symm
      rw [rawCoeff, Finsupp.lsum_single, hmaps, hL]
    · intro u v δ p
      let T : Oscillator D →ₐ[ℂ] PairPolynomial D := MvPolynomial.eval₂AlgHom ℂ
        (fun i : Index D =>
          MvPolynomial.C (X i : Oscillator D) -
            MvPolynomial.C ((bilinear D α (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
              MvPolynomial.X 0 ^ (i.2+1) -
            MvPolynomial.C ((bilinear D β (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
              MvPolynomial.X 1 ^ (i.2+1))
      let A : PairPolynomial D →ₗ[Oscillator D] Oscillator D :=
        (Finsupp.lsum (Oscillator D) (fun e : Fin 2 →₀ ℕ =>
          LinearMap.mulRight (Oscillator D)
            (creationCoeff D α (u - bilinear D α δ + e 0) *
              creationCoeff D β (v - bilinear D β δ + e 1)))).comp
            (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap
      let L : Oscillator D →ₗ[ℂ] Carrier D :=
        (epsilon D (α+β) δ •
          (Finsupp.lsingle (α+β+δ) : Oscillator D →ₗ[ℂ] Carrier D)).comp
          ((A.restrictScalars ℂ).comp T.toLinearMap)
      have hL (q : Oscillator D) : L q = commonKernelSingle D α β u v δ q := by
        simp only [L, A, LinearMap.comp_apply, LinearMap.smul_apply,
          LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply,
          Finsupp.lsingle_apply, Finsupp.lsum_apply, Finsupp.sum,
          LinearMap.mulRight_apply]
        apply congrArg (fun q : Oscillator D => epsilon D (α+β) δ • Finsupp.single (α+β+δ) q)
        apply Finset.sum_congr rfl
        intro e he
        change MvPolynomial.coeff e (translatedPairPolynomial D α β q) *
          (creationCoeff D α (u - bilinear D α δ + e 0) *
            creationCoeff D β (v - bilinear D β δ + e 1)) = _
        ring
      have hmaps : commonKernelPolynomialMap D α β u v δ = L := by
        apply (MvPolynomial.basisMonomials (Index D) ℂ).ext
        intro e
        rw [commonKernelPolynomialMap, Module.Basis.constr_basis]
        exact (hL (monomial e 1)).symm
      rw [commonKernel, Finsupp.lsum_single, hmaps, hL]
  refine ⟨?_, ?_, hExtensions⟩
  · intro t
    by_cases ht : t < 0
    · rw [creationCoeff, dif_pos ht]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
    · rw [creationCoeff, dif_neg ht]
      exact hweightNat t.toNat
  · intro t j
    by_cases ht : t < 0
    · have htj : t - j < 0 := by omega
      simp only [creationCoeff, dif_pos ht, dif_pos htj, translatedPolynomial,
        map_zero, Polynomial.coeff_zero, smul_zero]
    · rw [creationCoeff, dif_neg ht, hcoefficientNat]
      by_cases hj : (j : ℤ) ≤ t
      · rw [if_pos (by omega), creationCoeff, dif_neg (by omega)]
        have hidx : (t - j).toNat = t.toNat - j := by omega
        rw [hidx]
      · rw [if_neg (by omega), creationCoeff, dif_pos (by omega), smul_zero]

end

end D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
