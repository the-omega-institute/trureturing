/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full finite bilinear Gaussian coefficient sewing with native normalization. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
import D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Classical bilinear Gaussian/Fock coefficient calculus. External blocks
are arbitrary. Only the shared blocks enter the analytic estimates. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Ring

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
open MvPolynomial
open FactorialFockQuadraticEstimate
open FactorialFockMetric (weight)
open FiniteSqueezedVacuum

universe u v w
variable {H : Type u} [Fintype H] [DecidableEq H]

/-- Coefficients of a finite polynomial times the actual native Gaussian.
Every monomial acts by the original creation shift, without factorial rescaling. -/
def polynomialGaussian (A : Matrix H H ℂ) :
    MvPolynomial H ℂ →ₗ[ℂ] ((H →₀ ℕ) → ℂ) :=
  (Finsupp.lsum ℂ (fun α =>
    LinearMap.toSpanSingleton ℂ _ (created α (gaussianCoefficient A)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
private theorem polynomialGaussian_monomial (A : Matrix H H ℂ)
    (α : H →₀ ℕ) (c : ℂ) :
    polynomialGaussian A (monomial α c) = c • created α (gaussianCoefficient A) := by
  simp [polynomialGaussian, monomial, AddMonoidAlgebra.lsingle,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
private theorem polynomialGaussian_one (A : Matrix H H ℂ) :
    polynomialGaussian A 1 = gaussianCoefficient A := by
  rw [one_def, polynomialGaussian_monomial, one_smul, created_zero]
private theorem polynomialGaussian_X_mul (A : Matrix H H ℂ)
    (i : H) (p : MvPolynomial H ℂ) :
    polynomialGaussian A (X i * p) = created (Finsupp.single i 1) (polynomialGaussian A p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul_monomial, one_mul, polynomialGaussian_monomial,
      polynomialGaussian_monomial, ← created_add]
    funext d
    by_cases h : Finsupp.single i 1 ≤ d <;> simp [created, h]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, map_add]
    funext d
    by_cases h : Finsupp.single i 1 ≤ d <;> simp [created, h]
private theorem polynomialGaussian_square_summable (A : Matrix H H ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (p : MvPolynomial H ℂ) :
    Summable (fun n : H →₀ ℕ => (weight n : ℝ) * ‖polynomialGaussian A p n‖ ^ 2) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    convert (created_square_summable A hsym hA α).mul_left (‖c‖ ^ 2) using 1
    funext n
    simp only [polynomialGaussian_monomial, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  | add p q hp hq =>
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ ((hp.add hq).mul_left 2)
    intro n
    simp only [map_add, Pi.add_apply]
    have hn := norm_add_le (polynomialGaussian A p n) (polynomialGaussian A q n)
    have hsq : ‖polynomialGaussian A p n + polynomialGaussian A q n‖ ^ 2 ≤
        2 * (‖polynomialGaussian A p n‖ ^ 2 + ‖polynomialGaussian A q n‖ ^ 2) := by
      nlinarith [sq_nonneg (‖polynomialGaussian A p n‖ - ‖polynomialGaussian A q n‖),
        norm_nonneg (polynomialGaussian A p n + polynomialGaussian A q n)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (weight n))]

/-- Actual external row of a native Gaussian block matrix. -/
def row {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (d : X →₀ ℕ) (n : H →₀ ℕ) : ℂ :=
  gaussianCoefficient K (d.sumElim n)
private theorem row_zero {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) :
    row K 0 = gaussianCoefficient (fun i j => K (.inr i) (.inr j)) := by
  funext n
  have h := InfiniteGaussianFock.gaussianCoefficient_enlarge K Sum.inr Sum.inr_injective n
  simpa [row, Finsupp.sumElim_eq_add] using h
private theorem row_step {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hsym : ∀ i j, K i j = K j i) (d : X →₀ ℕ) (i : X) (n : H →₀ ℕ) :
    (d i + 1 : ℂ) * row K (d + Finsupp.single i 1) n =
      (∑ j, K (.inl i) (.inl j) *
        (if d j = 0 then 0 else row K (d - Finsupp.single j 1) n)) +
      ∑ j, K (.inl i) (.inr j) * created (Finsupp.single j 1) (row K d) n := by
  have hadd : d.sumElim n + Finsupp.single (.inl i) 1 =
      (d + Finsupp.single i 1).sumElim n := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
  have hleft (j : X) : d.sumElim n - Finsupp.single (.inl j) 1 =
      (d - Finsupp.single j 1).sumElim n := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  have hright (j : H) : d.sumElim n - Finsupp.single (.inr j) 1 =
      d.sumElim (n - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  have h := congrFun (gaussian_annihilate K hsym (.inl i)) (d.sumElim n)
  simpa only [annihilate, Finsupp.sumElim_inl, hadd, Fintype.sum_sum_type,
    created_single, Finsupp.sumElim_inr, hleft, hright, row] using h

/-- Every fixed external row is a finite polynomial times its shared native
Gaussian, for arbitrary symmetric full matrices. No full-block contraction
or mixed-block bound is imposed, and the external coefficient is ordinary. -/
theorem row_polynomial {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hsym : ∀ i j, K i j = K j i) (d : X →₀ ℕ) :
    ∃ p : MvPolynomial H ℂ,
      polynomialGaussian (fun i j => K (.inr i) (.inr j)) p = row K d := by
  classical
  let A : Matrix H H ℂ := fun i j => K (.inr i) (.inr j)
  have go : ∀ m (e : X →₀ ℕ), e.degree = m →
      ∃ p : MvPolynomial H ℂ, polynomialGaussian A p = row K e := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e he
      by_cases hz : e = 0
      · subst e
        exact ⟨1, (polynomialGaussian_one A).trans (row_zero K).symm⟩
      obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
        by_contra h
        apply hz
        ext i
        simpa using not_exists.mp h i
      let r := e - Finsupp.single i 1
      have hre : r + Finsupp.single i 1 = e := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree < m := by
        have h := congrArg Finsupp.degree hre
        simp only [map_add, Finsupp.degree_single] at h
        omega
      obtain ⟨p, hp⟩ := ih r.degree hrd r rfl
      have hj (j : X) : (r - Finsupp.single j 1).degree < m :=
        (Finsupp.degree_mono tsub_le_self).trans_lt hrd
      choose q hq using fun j : X => ih _ (hj j) (r - Finsupp.single j 1) rfl
      let q' : X → MvPolynomial H ℂ := fun j => if r j = 0 then 0 else q j
      refine ⟨(r i + 1 : ℂ)⁻¹ • ((∑ j, K (.inl i) (.inl j) • q' j) +
        ∑ j, K (.inl i) (.inr j) • (MvPolynomial.X j * p)), ?_⟩
      have hn : (r i + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r i)
      rw [map_smul, map_add, map_sum, map_sum]
      simp_rw [map_smul, polynomialGaussian_X_mul, hp]
      funext n
      simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
      have hq' (j : X) : polynomialGaussian A (q' j) n =
          if r j = 0 then 0 else row K (r - Finsupp.single j 1) n := by
        by_cases h : r j = 0 <;> simp [q', h, hq]
      simp_rw [hq']
      rw [← row_step K hsym r i n, hre]
      exact inv_mul_cancel_left₀ hn _
  exact go d.degree d rfl

/-- Genuine absolute summability of the all-occupation factorial contraction
of two finite polynomial insertions, using only strict shared contractions. -/
private theorem polynomial_pair_norm_summable (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (p q : MvPolynomial H ℂ) :
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      polynomialGaussian A p n * polynomialGaussian B q n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    _ ((polynomialGaussian_square_summable A hAsym hA p).add
      (polynomialGaussian_square_summable B hBsym hB q))
  intro n
  simp only [norm_mul, Complex.norm_natCast]
  have hsq := sq_nonneg (‖polynomialGaussian A p n‖ - ‖polynomialGaussian B q n‖)
  have hw : 0 ≤ (weight n : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hw hsq]

/-- Absolute convergence for actual arbitrary external Gaussian rows. -/
theorem row_pair_norm_summable {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      gaussianCoefficient K (d.sumElim n) * gaussianCoefficient L (e.sumElim n)‖) := by
  obtain ⟨p, hp⟩ := row_polynomial K hK d
  obtain ⟨q, hq⟩ := row_polynomial L hL e
  simpa only [hp, hq, row] using polynomial_pair_norm_summable _ _
    (fun i j => hK (.inr i) (.inr j)) (fun i j => hL (.inr i) (.inr j)) hA hB p q
private theorem annihilate_created_monomial (i : H) (α : H →₀ ℕ)
    (f : (H →₀ ℕ) → ℂ) :
    annihilate i (created α f) = fun n =>
      (α i : ℂ) * created (α - Finsupp.single i 1) f n +
        created α (annihilate i f) n := by
  funext n
  have hshift (hα : α ≤ n) : n + Finsupp.single i 1 - α =
      n - α + Finsupp.single i 1 := by
    ext j
    have hj := hα j
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simp [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji]
  by_cases hz : α i = 0
  · have hiff : α ≤ n + Finsupp.single i 1 ↔ α ≤ n := by
      constructor
      · intro h j
        by_cases hji : j = i
        · subst j
          simp [hz]
        · simpa [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji] using h j
      · intro h
        exact h.trans le_self_add
    by_cases h : α ≤ n
    · simp only [annihilate, created, h, hiff.mpr h, ite_true, hz,
        Nat.cast_zero, zero_mul, zero_add, Finsupp.tsub_apply, tsub_zero, hshift h]
    · simp [annihilate, created, h, hiff, hz]
  · have hα : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
      Finsupp.sub_add_single_one_cancel hz
    by_cases h : α ≤ n
    · have hplus : α ≤ n + Finsupp.single i 1 := h.trans le_self_add
      have hminus : α - Finsupp.single i 1 ≤ n := tsub_le_self.trans h
      have harg : n - (α - Finsupp.single i 1) = n - α + Finsupp.single i 1 := by
        ext j
        have hj := h j
        by_cases hji : j = i
        · subst j
          simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
          omega
        · simp [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji]
      simp only [annihilate, created, h, hplus, hminus, ite_true, harg,
        hshift h, Finsupp.tsub_apply]
      have hn : ((n i - α i : ℕ) : ℂ) + (α i : ℂ) = (n i : ℂ) := by
        exact_mod_cast Nat.sub_add_cancel (h i)
      linear_combination -f (n - α + Finsupp.single i 1) * hn
    · by_cases hplus : α ≤ n + Finsupp.single i 1
      · have hminus : α - Finsupp.single i 1 ≤ n := by
          intro j
          have hj := hplus j
          by_cases hji : j = i
          · subst j
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same] at *
            omega
          · simpa [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji]
              using hj
        have heq : α i = n i + 1 := by
          have hu := hplus i
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hu
          by_contra hh
          apply h
          intro j
          by_cases hji : j = i
          · subst j
            omega
          · simpa [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji] using hplus j
        have harg : n - (α - Finsupp.single i 1) = n + Finsupp.single i 1 - α := by
          ext j
          by_cases hji : j = i
          · subst j
            simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
            omega
          · simp [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji]
        simp [annihilate, created, h, hplus, hminus, harg, heq]
      · have hminus : ¬ α - Finsupp.single i 1 ≤ n := by
          intro hh
          apply hplus
          rw [← hα]
          exact add_le_add hh le_rfl
        simp [annihilate, created, h, hplus, hminus]
private theorem pairing_add_right (f g k : (H →₀ ℕ) → ℂ)
    (hg : Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * g n))
    (hk : Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * k n)) :
    pairing f (fun n => g n + k n) = pairing f g + pairing f k := by
  unfold pairing
  simp only [mul_add]
  exact hg.tsum_add hk
/-- The actual two-sided creation moment, defined by the original bilinear
factorial pairing and the original creation shifts. -/
def bilinearMoment (A B : Matrix H H ℂ) (α β : H →₀ ℕ) : ℂ :=
  pairing (created α (gaussianCoefficient A)) (created β (gaussianCoefficient B))
/-- True creation/annihilation recurrence with both insertion monomials.
The coordinate multiplicity is β_i, with zero-coordinate boundary terms
included. Every infinite finite-sum exchange uses native summability. -/
private theorem bilinearMoment_creation_step (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (α β : H →₀ ℕ) (i : H) :
    bilinearMoment A B (α + Finsupp.single i 1) β =
      (β i : ℂ) * bilinearMoment A B α (β - Finsupp.single i 1) +
        ∑ j, B i j * bilinearMoment A B α (β + Finsupp.single j 1) := by
  let f := created α (gaussianCoefficient A)
  let g := created (β - Finsupp.single i 1) (gaussianCoefficient B)
  let t : H → (H →₀ ℕ) → ℂ := fun j n =>
    B i j * created (β + Finsupp.single j 1) (gaussianCoefficient B) n
  have hg : Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * ((β i : ℂ) * g n)) := by
    convert (created_pair_summable A B hAsym hBsym hA hB α
      (β - Finsupp.single i 1)).mul_left (β i : ℂ) using 1
    funext n
    dsimp [f, g]
    ring
  have ht (j : H) : Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * t j n) := by
    convert (created_pair_summable A B hAsym hBsym hA hB α
      (β + Finsupp.single j 1)).mul_left (B i j) using 1
    funext n
    dsimp [f, t]
    ring
  have hts : Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * ∑ j, t j n) := by
    simpa only [Finset.mul_sum] using summable_sum (s := Finset.univ) (fun j _ => ht j)
  unfold bilinearMoment
  rw [add_comm α, ← created_add, pairing_creation_annihilation,
    annihilate_created_monomial, gaussian_annihilate B hBsym]
  simp_rw [created_sum, created_const, created_add]
  change pairing f (fun n => (β i : ℂ) * g n + ∑ j, t j n) = _
  rw [pairing_add_right _ _ _ hg hts, pairing_const_right,
    pairing_sum_right _ _ ht]
  simp only [t, pairing_const_right]
  rfl
private theorem bilinearMoment_swap (A B : Matrix H H ℂ) (α β : H →₀ ℕ) :
    bilinearMoment A B α β = bilinearMoment B A β α :=
  pairing_comm _ _
open scoped Matrix.Norms.L2Operator
/-- The ordered resolvent equation for the actual two-sided factorial
moments. This solves the creation/annihilation system without dividing by
the vacuum scalar, and without assuming that A and B commute. -/
theorem bilinearMoment_resolvent_step (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (α β : H →₀ ℕ) :
    (fun i => bilinearMoment A B (α + Finsupp.single i 1) β) =
      Matrix.mulVec (1 - B * A)⁻¹ʳ
        (Matrix.mulVec B (fun i => (α i : ℂ) *
          bilinearMoment A B (α - Finsupp.single i 1) β) +
          fun i => (β i : ℂ) * bilinearMoment A B α (β - Finsupp.single i 1)) := by
  let U : H → ℂ := fun i => bilinearMoment A B (α + Finsupp.single i 1) β
  let V : H → ℂ := fun i => bilinearMoment A B α (β + Finsupp.single i 1)
  let u : H → ℂ := fun i => (β i : ℂ) * bilinearMoment A B α (β - Finsupp.single i 1)
  let v : H → ℂ := fun i => (α i : ℂ) * bilinearMoment A B (α - Finsupp.single i 1) β
  have hU : U = B.mulVec V + u := by
    funext i
    simpa only [U, V, u, Matrix.mulVec, dotProduct, Pi.add_apply, add_comm] using
      bilinearMoment_creation_step A B hAsym hBsym hA hB α β i
  have hV : V = A.mulVec U + v := by
    funext i
    have h := bilinearMoment_creation_step B A hBsym hAsym hB hA β α i
    simp_rw [← bilinearMoment_swap A B] at h
    simpa only [U, V, v, Matrix.mulVec, dotProduct, Pi.add_apply, add_comm] using h
  have hrec : U = (B * A).mulVec U + (B.mulVec v + u) := by
    rw [hV, Matrix.mulVec_add, Matrix.mulVec_mulVec] at hU
    simpa only [add_assoc] using hU
  have heq : (1 - B * A).mulVec U = B.mulVec v + u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hrec)
  have hBA : ‖B * A‖ < 1 := (norm_mul_le B A).trans_lt
    ((mul_le_of_le_one_left (norm_nonneg A) hB.le).trans_lt hA)
  have hu := isUnit_one_sub_of_norm_lt_one hBA
  change U = Matrix.mulVec ((1 - B * A)⁻¹ʳ) (B.mulVec v + u)
  calc
    U = Matrix.mulVec ((1 - B * A)⁻¹ʳ) ((1 - B * A).mulVec U) := by
      rw [Matrix.mulVec_mulVec, Ring.inverse_mul_cancel _ hu, Matrix.one_mulVec]
    _ = _ := by rw [heq]
private theorem resolvent_unit (A B : Matrix H H ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) : IsUnit (1 - B * A) := by
  apply isUnit_one_sub_of_norm_lt_one
  exact (norm_mul_le B A).trans_lt
    ((mul_le_of_le_one_left (norm_nonneg A) hB.le).trans_lt hA)
private theorem resolvent_push (A B : Matrix H H ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    (1 - B * A)⁻¹ʳ * B = B * (1 - A * B)⁻¹ʳ := by
  have hleft := resolvent_unit A B hA hB
  have hright := resolvent_unit B A hB hA
  have hp : (1 - B * A) * B = B * (1 - A * B) := by noncomm_ring
  calc
    (1 - B * A)⁻¹ʳ * B =
        (1 - B * A)⁻¹ʳ * (B * ((1 - A * B) * (1 - A * B)⁻¹ʳ)) := by
      rw [Ring.mul_inverse_cancel _ hright, mul_one]
    _ = (1 - B * A)⁻¹ʳ * (((1 - B * A) * B) * (1 - A * B)⁻¹ʳ) := by
      rw [← mul_assoc B, ← hp]
    _ = B * (1 - A * B)⁻¹ʳ := by
      rw [← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ hleft, one_mul]
private theorem resolvent_transpose (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i) :
    ((1 - B * A)⁻¹ʳ).transpose = (1 - A * B)⁻¹ʳ := by
  have hAt : A.transpose = A := by ext i j; exact hAsym j i
  have hBt : B.transpose = B := by ext i j; exact hBsym j i
  simp only [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hAt, hBt]
/-- The ordered joint insertion covariance. The lower cross block is the
transpose of the upper cross block for symmetric A and B. -/
def covariance (A B : Matrix H H ℂ) : Matrix (H ⊕ H) (H ⊕ H) ℂ :=
  Matrix.fromBlocks ((1 - B * A)⁻¹ʳ * B) ((1 - B * A)⁻¹ʳ)
    ((1 - A * B)⁻¹ʳ) ((1 - A * B)⁻¹ʳ * A)
private theorem covariance_symm (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    (covariance A B).IsSymm := by
  have hAt : A.transpose = A := by ext i j; exact hAsym j i
  have hBt : B.transpose = B := by ext i j; exact hBsym j i
  unfold covariance Matrix.IsSymm
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    hAt, hBt, resolvent_transpose A B hAsym hBsym,
    resolvent_transpose B A hBsym hAsym,
    ← resolvent_push A B hA hB, ← resolvent_push B A hB hA]
/-- The complete ordered Wick recurrence for the actual insertion moments,
with symmetric joint covariance and both coordinate families. This is a
recurrence for the actual infinite pairing, not an assumed Wick evaluation. -/
theorem bilinearMoment_wick_recursion (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    (∀ i j, covariance A B i j = covariance A B j i) ∧
    (∀ (α β : H →₀ ℕ) (i : H),
      bilinearMoment A B (α + Finsupp.single i 1) β =
        (∑ j, covariance A B (.inl i) (.inl j) * (α j : ℂ) *
          bilinearMoment A B (α - Finsupp.single j 1) β) +
        ∑ j, covariance A B (.inl i) (.inr j) * (β j : ℂ) *
          bilinearMoment A B α (β - Finsupp.single j 1)) ∧
    (∀ (α β : H →₀ ℕ) (i : H),
      bilinearMoment A B α (β + Finsupp.single i 1) =
        (∑ j, covariance A B (.inr i) (.inl j) * (α j : ℂ) *
          bilinearMoment A B (α - Finsupp.single j 1) β) +
        ∑ j, covariance A B (.inr i) (.inr j) * (β j : ℂ) *
          bilinearMoment A B α (β - Finsupp.single j 1)) := by
  refine ⟨(fun i j => (covariance_symm A B hAsym hBsym hA hB).apply j i), ?_, ?_⟩
  · intro α β i
    have h := congrFun (bilinearMoment_resolvent_step A B hAsym hBsym hA hB α β) i
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec] at h
    simpa only [covariance, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.mulVec, dotProduct, Pi.add_apply, mul_assoc] using h
  · intro α β i
    have h := congrFun (bilinearMoment_resolvent_step B A hBsym hAsym hB hA β α) i
    simp_rw [← bilinearMoment_swap A B] at h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec] at h
    simpa only [covariance, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.mulVec, dotProduct, Pi.add_apply, mul_assoc, add_comm] using h
private theorem polynomialGaussian_expansion (A : Matrix H H ℂ)
    (p : MvPolynomial H ℂ) :
    polynomialGaussian A p = fun n =>
      ∑ α ∈ p.support, p.coeff α * created α (gaussianCoefficient A) n := by
  calc
    polynomialGaussian A p =
        polynomialGaussian A (∑ α ∈ p.support, monomial α (p.coeff α)) :=
      congrArg (polynomialGaussian A) p.as_sum
    _ = _ := by
      simp only [map_sum, polynomialGaussian_monomial]
      funext n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
private theorem pairing_finset_right {T : Type*} (s : Finset T)
    (f : (H →₀ ℕ) → ℂ) (g : T → (H →₀ ℕ) → ℂ)
    (hs : ∀ i ∈ s, Summable (fun n : H →₀ ℕ => (weight n : ℂ) * f n * g i n)) :
    pairing f (fun n => ∑ i ∈ s, g i n) = ∑ i ∈ s, pairing f (g i) := by
  unfold pairing
  simp only [Finset.mul_sum]
  exact Summable.tsum_finsetSum hs
private theorem polynomial_pair_moments (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (p q : MvPolynomial H ℂ) :
    pairing (polynomialGaussian A p) (polynomialGaussian B q) =
      ∑ α ∈ p.support, ∑ β ∈ q.support,
        p.coeff α * q.coeff β * bilinearMoment A B α β := by
  have hp (α : H →₀ ℕ) : Summable (fun n : H →₀ ℕ =>
      (weight n : ℂ) * polynomialGaussian B q n *
        (p.coeff α * created α (gaussianCoefficient A) n)) := by
    simpa only [polynomialGaussian_monomial, Pi.smul_apply, smul_eq_mul] using
      (polynomial_pair_norm_summable B A hBsym hAsym hB hA q
        (monomial α (p.coeff α))).of_norm
  have hq (α β : H →₀ ℕ) : Summable (fun n : H →₀ ℕ =>
      (weight n : ℂ) * created α (gaussianCoefficient A) n *
        (q.coeff β * created β (gaussianCoefficient B) n)) := by
    convert (created_pair_summable A B hAsym hBsym hA hB α β).mul_left
      (q.coeff β) using 1
    funext n
    ring
  rw [pairing_comm, polynomialGaussian_expansion A p,
    pairing_finset_right _ _ _ (fun α _ => hp α)]
  apply Finset.sum_congr rfl
  intro α hα
  rw [pairing_const_right, pairing_comm, polynomialGaussian_expansion B q,
    pairing_finset_right _ _ _ (fun β _ => hq α β)]
  simp only [pairing_const_right, Finset.mul_sum, bilinearMoment]
  apply Finset.sum_congr rfl
  intro β hβ
  ring
/-- The actual absolutely convergent external-row contraction is a finite
sum of the true two-sided creation moments. Both polynomial witnesses are
constructed from the original Gaussian coefficients; neither the vacuum
normalization nor an effective-kernel identity is assumed. All coefficients
are ordinary external coefficients and the shared weight is ∏ i, n_i!. -/
theorem row_pair_moments {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    ∃ p q : MvPolynomial H ℂ,
      polynomialGaussian (fun i j => K (.inr i) (.inr j)) p = row K d ∧
      polynomialGaussian (fun i j => L (.inr i) (.inr j)) q = row L e ∧
      Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
        gaussianCoefficient K (d.sumElim n) * gaussianCoefficient L (e.sumElim n)‖) ∧
      (∑' n : H →₀ ℕ, (weight n : ℂ) * gaussianCoefficient K (d.sumElim n) *
        gaussianCoefficient L (e.sumElim n)) =
        ∑ α ∈ p.support, ∑ β ∈ q.support, p.coeff α * q.coeff β *
          bilinearMoment (fun i j => K (.inr i) (.inr j))
            (fun i j => L (.inr i) (.inr j)) α β := by
  obtain ⟨p, hp⟩ := row_polynomial K hK d
  obtain ⟨q, hq⟩ := row_polynomial L hL e
  refine ⟨p, q, hp, hq, row_pair_norm_summable K L hK hL hA hB d e, ?_⟩
  simpa only [hp, hq, pairing, row] using polynomial_pair_moments _ _
    (fun i j => hK (.inr i) (.inr j)) (fun i j => hL (.inr i) (.inr j)) hA hB p q
private theorem sumElim_add_left {X : Type*} {Y : Type*} [DecidableEq X] [DecidableEq Y]
    (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : X) :
    (d + Finsupp.single i 1).sumElim e = d.sumElim e + Finsupp.single (.inl i) 1 := by
  ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem sumElim_add_right {X : Type*} {Y : Type*} [DecidableEq X] [DecidableEq Y]
    (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : Y) :
    d.sumElim (e + Finsupp.single i 1) = d.sumElim e + Finsupp.single (.inr i) 1 := by
  ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem sumElim_sub_left {X : Type*} {Y : Type*} [DecidableEq X] [DecidableEq Y]
    (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : X) :
    (d - Finsupp.single i 1).sumElim e = d.sumElim e - Finsupp.single (.inl i) 1 := by
  ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply, Finsupp.single_apply]
private theorem sumElim_sub_right {X : Type*} {Y : Type*} [DecidableEq X] [DecidableEq Y]
    (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : Y) :
    d.sumElim (e - Finsupp.single i 1) = d.sumElim e - Finsupp.single (.inr i) 1 := by
  ext (j | j) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply, Finsupp.single_apply]
/-- Identification of the actual factorial pairing with native Gaussian
moments. The normalization is the native trace-log exponential. No inverse
or nonvanishing premise for that scalar is used. -/
theorem bilinearMoment_native (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (α β : H →₀ ℕ) :
    bilinearMoment A B α β =
      Complex.exp ((1 / 2 : ℂ) *
        ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) *
      NativeGaussianMoment.nativeMoment (covariance A B) (α.sumElim β) := by
  obtain ⟨hC, hleft, hright⟩ := bilinearMoment_wick_recursion A B hAsym hBsym hA hB
  let Z := Complex.exp ((1 / 2 : ℂ) *
    ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ))
  have hzero : bilinearMoment A B 0 0 = Z := by
    simpa only [bilinearMoment, created_zero, pairing] using
      (vacuum_trace_log A B hAsym hBsym hA hB).2.2
  have go : ∀ m (a b : H →₀ ℕ), a.degree + b.degree = m →
      bilinearMoment A B a b =
        Z * NativeGaussianMoment.nativeMoment (covariance A B) (a.sumElim b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b hab
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · subst b
          simpa [NativeGaussianMoment.nativeMoment, weight, gaussianCoefficient_zero] using hzero
        obtain ⟨i, hi⟩ := NativeGaussianMoment.occupation_nonzero b hb
        let r := b - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = b := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree < m := by
          have := NativeGaussianMoment.sub_single_degree b i hi
          simp only [map_zero, zero_add] at hab
          dsimp [r]; omega
        rw [← hr, hright, sumElim_add_right,
          NativeGaussianMoment.nativeMoment_step _ hC, Fintype.sum_sum_type,
          mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          simp
        · apply Finset.sum_congr rfl
          intro j hj
          have hjd : (r - Finsupp.single j 1).degree < m :=
            (Finsupp.degree_mono (show r - Finsupp.single j 1 ≤ r from tsub_le_self)).trans_lt hd
          rw [ih (r - Finsupp.single j 1).degree hjd 0
            (r - Finsupp.single j 1) (by simp), sumElim_sub_right]
          simp only [Finsupp.sumElim_inr]
          ring
      · obtain ⟨i, hi⟩ := NativeGaussianMoment.occupation_nonzero a ha
        let r := a - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = a := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree + b.degree < m := by
          have := NativeGaussianMoment.sub_single_degree a i hi
          dsimp [r]; omega
        rw [← hr, hleft, sumElim_add_left,
          NativeGaussianMoment.nativeMoment_step _ hC, Fintype.sum_sum_type,
          mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          have hjd : (r - Finsupp.single j 1).degree + b.degree < m :=
            (Nat.add_le_add_right (Finsupp.degree_mono tsub_le_self) _).trans_lt hd
          rw [ih _ hjd _ _ rfl, sumElim_sub_left]
          simp only [Finsupp.sumElim_inl]
          ring
        · apply Finset.sum_congr rfl
          intro j hj
          have hjd : r.degree + (b - Finsupp.single j 1).degree < m :=
            (Nat.add_le_add_left (Finsupp.degree_mono tsub_le_self) _).trans_lt hd
          rw [ih _ hjd _ _ rfl, sumElim_sub_right]
          simp only [Finsupp.sumElim_inr]
          ring
  exact go _ α β rfl
section ExternalRecurrence
variable {X : Type v} {Y : Type w}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
private def rowLower (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (d : X →₀ ℕ) (i : X) :
    (H →₀ ℕ) → ℂ := if d i = 0 then 0 else row K (d - Finsupp.single i 1)
private def rowPair (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ) (d : X →₀ ℕ) (e : Y →₀ ℕ) : ℂ :=
  pairing (row K d) (row L e)
private theorem rowPair_swap (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ) (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    rowPair K L d e = rowPair L K e d := pairing_comm _ _
private theorem pairing_rowLower (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ) (d : X →₀ ℕ) (e : Y →₀ ℕ) (j : X) :
    pairing (row L e) (rowLower K d j) =
      if d j = 0 then 0 else rowPair K L (d - Finsupp.single j 1) e := by
  by_cases h : d j = 0
  · simp [rowLower, h, pairing]
  · simp only [rowLower, h, ite_false, rowPair, pairing_comm (row L e)]
private theorem row_annihilate (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (d : X →₀ ℕ) (i : H) :
    annihilate i (row K d) = fun n =>
      (∑ j, K (.inr i) (.inl j) * rowLower K d j n) +
        ∑ j, K (.inr i) (.inr j) * created (Finsupp.single j 1) (row K d) n := by
  funext n
  have h := congrFun (gaussian_annihilate K hK (.inr i)) (d.sumElim n)
  simpa only [annihilate, row, Finsupp.sumElim_inr, ← sumElim_add_right,
    Fintype.sum_sum_type, created_single, Finsupp.sumElim_inl,
    ← sumElim_sub_left, ← sumElim_sub_right, rowLower, ite_apply, row, Pi.zero_apply,
    apply_ite] using h
variable (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
  (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
  (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
  (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
include hK hL hA hB
private theorem row_pair_created_summable (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : H) :
    Summable (fun n : H →₀ ℕ => (weight n : ℂ) * row K d n *
      created (Finsupp.single i 1) (row L e) n) := by
  obtain ⟨p, hp⟩ := row_polynomial K hK d
  obtain ⟨q, hq⟩ := row_polynomial L hL e
  have hs := polynomial_pair_norm_summable
    (fun i j : H => K (.inr i) (.inr j)) (fun i j : H => L (.inr i) (.inr j))
    (fun i j => hK (.inr i) (.inr j)) (fun i j => hL (.inr i) (.inr j))
    hA hB p (MvPolynomial.X i * q)
  rw [polynomialGaussian_X_mul, hp, hq] at hs
  exact hs.of_norm
private theorem pairing_row_combination (d : X →₀ ℕ) (e : Y →₀ ℕ)
    (a : X → ℂ) (b : H → ℂ) :
    pairing (row L e) (fun n =>
      (∑ j, a j * rowLower K d j n) +
        ∑ j, b j * created (Finsupp.single j 1) (row K d) n) =
      (∑ j, a j * pairing (row L e) (rowLower K d j)) +
        ∑ j, b j * pairing (row L e) (created (Finsupp.single j 1) (row K d)) := by
  have hs (j : X) : Summable (fun n : H →₀ ℕ =>
      (weight n : ℂ) * row L e n * (a j * rowLower K d j n)) := by
    by_cases h : d j = 0
    · simp [rowLower, h]
    · convert ((row_pair_norm_summable L K hL hK hB hA e
        (d - Finsupp.single j 1)).of_norm.mul_left (a j)) using 1
      funext n
      simp only [rowLower, h, ite_false, row]
      ring
  have ht (j : H) : Summable (fun n : H →₀ ℕ =>
      (weight n : ℂ) * row L e n *
        (b j * created (Finsupp.single j 1) (row K d) n)) := by
    convert (row_pair_created_summable L K hL hK hB hA e d j).mul_left (b j) using 1
    funext n
    ring
  have hss := summable_sum (s := Finset.univ) (fun j _ => hs j)
  have hts := summable_sum (s := Finset.univ) (fun j _ => ht j)
  simp only [← Finset.mul_sum] at hss hts
  rw [pairing_add_right _ _ _ hss hts,
    pairing_finset_right _ _ _ (fun j _ => hs j),
    pairing_finset_right _ _ _ (fun j _ => ht j)]
  simp only [pairing_const_right]
private theorem rowPair_external_step (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : X) :
    (d i + 1 : ℂ) * rowPair K L (d + Finsupp.single i 1) e =
      (∑ j, K (.inl i) (.inl j) *
        (if d j = 0 then 0 else rowPair K L (d - Finsupp.single j 1) e)) +
      ∑ j, K (.inl i) (.inr j) *
        pairing (created (Finsupp.single j 1) (row K d)) (row L e) := by
  calc
    _ = pairing (row L e) (fun n => (d i + 1 : ℂ) *
        row K (d + Finsupp.single i 1) n) := by
      rw [pairing_const_right, pairing_comm]
      rfl
    _ = _ := by
      simp_rw [row_step K hK d i]
      have hh := pairing_row_combination K L hK hL hA hB d e
        (fun j => K (.inl i) (.inl j)) (fun j => K (.inl i) (.inr j))
      simp_rw [pairing_rowLower] at hh
      simpa only [rowLower, ite_apply, apply_ite, Pi.zero_apply,
        pairing_comm (row L e)] using hh
private theorem rowPair_internal_step (d : X →₀ ℕ) (e : Y →₀ ℕ) (i : H) :
    pairing (created (Finsupp.single i 1) (row K d)) (row L e) =
      (∑ j, L (.inr i) (.inl j) *
        (if e j = 0 then 0 else rowPair K L d (e - Finsupp.single j 1))) +
      ∑ j, L (.inr i) (.inr j) *
        pairing (row K d) (created (Finsupp.single j 1) (row L e)) := by
  rw [pairing_creation_annihilation, row_annihilate L hL]
  have hh := pairing_row_combination L K hL hK hB hA e d
    (fun j => L (.inr i) (.inl j)) (fun j => L (.inr i) (.inr j))
  simpa only [pairing_rowLower, ← rowPair_swap K L] using hh
private theorem rowPair_resolved_step (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    let A : Matrix H H ℂ := fun i j => K (.inr i) (.inr j)
    let B : Matrix H H ℂ := fun i j => L (.inr i) (.inr j)
    let P : Matrix X X ℂ := fun i j => K (.inl i) (.inl j)
    let R : Matrix X H ℂ := fun i j => K (.inl i) (.inr j)
    let Rt : Matrix H X ℂ := fun i j => K (.inr i) (.inl j)
    let S : Matrix H Y ℂ := fun i j => L (.inr i) (.inl j)
    let N : Matrix H H ℂ := (1 - B * A)⁻¹ʳ
    (fun i => (d i + 1 : ℂ) * rowPair K L (d + Finsupp.single i 1) e) =
      (P + (((R * N : Matrix X H ℂ) * B : Matrix X H ℂ) * Rt : Matrix X X ℂ)).mulVec
        (fun j => if d j = 0 then 0 else rowPair K L (d - Finsupp.single j 1) e) +
      ((R * N : Matrix X H ℂ) * S : Matrix X Y ℂ).mulVec
        (fun j => if e j = 0 then 0 else rowPair K L d (e - Finsupp.single j 1)) := by
  let A : Matrix H H ℂ := fun i j => K (.inr i) (.inr j)
  let B : Matrix H H ℂ := fun i j => L (.inr i) (.inr j)
  let P : Matrix X X ℂ := fun i j => K (.inl i) (.inl j)
  let R : Matrix X H ℂ := fun i j => K (.inl i) (.inr j)
  let Rt : Matrix H X ℂ := fun i j => K (.inr i) (.inl j)
  let S : Matrix H Y ℂ := fun i j => L (.inr i) (.inl j)
  let l : X → ℂ := fun j => if d j = 0 then 0 else rowPair K L (d - Finsupp.single j 1) e
  let r : Y → ℂ := fun j => if e j = 0 then 0 else rowPair K L d (e - Finsupp.single j 1)
  let U : H → ℂ := fun i => pairing (created (Finsupp.single i 1) (row K d)) (row L e)
  let V : H → ℂ := fun i => pairing (row K d) (created (Finsupp.single i 1) (row L e))
  have hU : U = B.mulVec V + S.mulVec r := by
    funext i
    simpa only [U, V, B, S, r, Matrix.mulVec, dotProduct, Pi.add_apply, add_comm] using
      rowPair_internal_step K L hK hL hA hB d e i
  have hV : V = A.mulVec U + Rt.mulVec l := by
    funext i
    have hh := rowPair_internal_step L K hL hK hB hA e d i
    simp_rw [← rowPair_swap K L] at hh
    simpa only [U, V, A, Rt, l, Matrix.mulVec, dotProduct, Pi.add_apply,
      pairing_comm, add_comm] using hh
  have heq : (1 - B * A).mulVec U = B.mulVec (Rt.mulVec l) + S.mulVec r := by
    rw [hV, Matrix.mulVec_add, Matrix.mulVec_mulVec] at hU
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_assoc, add_comm, add_left_comm] using hU)
  have hu : U = Matrix.mulVec ((1 - B * A)⁻¹ʳ)
      (B.mulVec (Rt.mulVec l) + S.mulVec r) := by
    have hunit := resolvent_unit A B hA hB
    rw [← heq, Matrix.mulVec_mulVec, Ring.inverse_mul_cancel _ hunit, Matrix.one_mulVec]
  have hstep : (fun i => (d i + 1 : ℂ) * rowPair K L (d + Finsupp.single i 1) e) =
      P.mulVec l + R.mulVec U := by
    funext i
    exact rowPair_external_step K L hK hL hA hB d e i
  change _ = (P + R * (1 - B * A)⁻¹ʳ * B * Rt).mulVec l +
    (R * (1 - B * A)⁻¹ʳ * S).mulVec r
  rw [hstep, hu]
  simp only [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, add_assoc]
end ExternalRecurrence
/-- The effective complex bilinear Gaussian kernel, with ordered inverses.
The lower cross block is written explicitly in its ordered form. -/
def effectiveKernel {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Matrix H H ℂ) (R : Matrix X H ℂ) (S : Matrix H Y ℂ) :
    Matrix (X ⊕ Y) (X ⊕ Y) ℂ :=
  Matrix.fromBlocks
    (P + R * (1 - B * A)⁻¹ʳ * B * R.transpose)
    (R * (1 - B * A)⁻¹ʳ * S)
    (S.transpose * (1 - A * B)⁻¹ʳ * R.transpose)
    (Q + S.transpose * (1 - A * B)⁻¹ʳ * A * S)
private theorem effectiveKernel_symm {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Matrix H H ℂ) (R : Matrix X H ℂ) (S : Matrix H Y ℂ)
    (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1) :
    (effectiveKernel P Q A B R S).IsSymm := by
  have hPt : P.transpose = P := by ext i j; exact hP j i
  have hQt : Q.transpose = Q := by ext i j; exact hQ j i
  have hAt : A.transpose = A := by ext i j; exact hAsym j i
  have hBt : B.transpose = B := by ext i j; exact hBsym j i
  have hNB : ((1 - B * A)⁻¹ʳ * B).transpose = (1 - B * A)⁻¹ʳ * B := by
    rw [Matrix.transpose_mul, hBt, resolvent_transpose A B hAsym hBsym,
      ← resolvent_push A B hA hB]
  have hVA : ((1 - A * B)⁻¹ʳ * A).transpose = (1 - A * B)⁻¹ʳ * A := by
    rw [Matrix.transpose_mul, hAt, resolvent_transpose B A hBsym hAsym,
      ← resolvent_push B A hB hA]
  unfold effectiveKernel Matrix.IsSymm
  rw [Matrix.fromBlocks_transpose]
  congr 1
  · conv_lhs => rw [Matrix.mul_assoc R _ B]
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPt, hNB]
    simp only [Matrix.mul_assoc]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      resolvent_transpose B A hBsym hAsym, Matrix.mul_assoc]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      resolvent_transpose A B hAsym hBsym, Matrix.mul_assoc]
  · conv_lhs => rw [Matrix.mul_assoc S.transpose _ A]
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hQt, hVA]
    simp only [Matrix.mul_assoc]
/-- Full finite complex Gaussian coefficient sewing. Only the shared blocks
are strict contractions; the external and mixed blocks are arbitrary. The
external coefficients are ordinary, and all finite types may be empty. -/
theorem finite_sewing {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Matrix H H ℂ) (R : Matrix X H ℂ) (S : Matrix H Y ℂ)
    (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      gaussianCoefficient (Matrix.fromBlocks P R R.transpose A) (d.sumElim n) *
      gaussianCoefficient (Matrix.fromBlocks B S S.transpose Q) (n.sumElim e)‖) ∧
    (∑' n : H →₀ ℕ, (weight n : ℂ) *
      gaussianCoefficient (Matrix.fromBlocks P R R.transpose A) (d.sumElim n) *
      gaussianCoefficient (Matrix.fromBlocks B S S.transpose Q) (n.sumElim e)) =
      Complex.exp ((1 / 2 : ℂ) *
        ∑' k : ℕ, Matrix.trace ((A * B) ^ (k + 1)) / (k + 1 : ℂ)) *
      gaussianCoefficient (effectiveKernel P Q A B R S) (d.sumElim e) := by
  let K := Matrix.fromBlocks P R R.transpose A
  let L := Matrix.fromBlocks Q S.transpose S B
  let K₂ := Matrix.fromBlocks B S S.transpose Q
  let E := effectiveKernel P Q A B R S
  let Z := Complex.exp ((1 / 2 : ℂ) *
    ∑' k : ℕ, Matrix.trace ((A * B) ^ (k + 1)) / (k + 1 : ℂ))
  have hK : ∀ i j, K i j = K j i := by
    rintro (i | i) (j | j)
    · exact hP i j
    · rfl
    · rfl
    · exact hAsym i j
  have hL : ∀ i j, L i j = L j i := by
    rintro (i | i) (j | j)
    · exact hQ i j
    · rfl
    · rfl
    · exact hBsym i j
  have hE : ∀ i j, E i j = E j i :=
    fun i j => (effectiveKernel_symm P Q A B R S hP hQ hAsym hBsym hA hB).apply j i
  have hswap (a : Y →₀ ℕ) (n : H →₀ ℕ) :
      gaussianCoefficient K₂ (n.sumElim a) = row L a n := by
    have hh := InfiniteGaussianFock.gaussianCoefficient_enlarge K₂ Sum.swap
      (fun _ _ h => by simpa only [Sum.swap_swap] using congrArg Sum.swap h) (a.sumElim n)
    rw [Finsupp.mapDomain_swap_sumElim] at hh
    have hmat : (fun i j => K₂ (Sum.swap i) (Sum.swap j)) = L := by
      ext (i | i) (j | j) <;> rfl
    rw [hmat] at hh
    exact hh
  have h00 : rowPair K L 0 0 = Z := by
    have hh := bilinearMoment_native A B hAsym hBsym hA hB 0 0
    rw [rowPair, row_zero, row_zero]
    simpa [bilinearMoment, created_zero, NativeGaussianMoment.nativeMoment, weight,
      gaussianCoefficient_zero, K, L, Z] using hh
  have hleft (a : X →₀ ℕ) (b : Y →₀ ℕ) (i : X) :
      (a i + 1 : ℂ) * rowPair K L (a + Finsupp.single i 1) b =
        (∑ j, E (.inl i) (.inl j) *
          (if a j = 0 then 0 else rowPair K L (a - Finsupp.single j 1) b)) +
        ∑ j, E (.inl i) (.inr j) *
          (if b j = 0 then 0 else rowPair K L a (b - Finsupp.single j 1)) := by
    have hh := congrFun (rowPair_resolved_step K L hK hL hA hB a b) i
    simpa only [K, L, E, effectiveKernel, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.mulVec, dotProduct, Pi.add_apply] using hh
  have hright (a : X →₀ ℕ) (b : Y →₀ ℕ) (i : Y) :
      (b i + 1 : ℂ) * rowPair K L a (b + Finsupp.single i 1) =
        (∑ j, E (.inr i) (.inl j) *
          (if a j = 0 then 0 else rowPair K L (a - Finsupp.single j 1) b)) +
        ∑ j, E (.inr i) (.inr j) *
          (if b j = 0 then 0 else rowPair K L a (b - Finsupp.single j 1)) := by
    have hh := congrFun (rowPair_resolved_step L K hL hK hB hA b a) i
    simp_rw [← rowPair_swap K L] at hh
    simpa only [K, L, E, effectiveKernel, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.mulVec, dotProduct, Pi.add_apply, add_comm] using hh
  let g (a : X →₀ ℕ) (b : Y →₀ ℕ) := gaussianCoefficient E (a.sumElim b)
  have gleft (a : X →₀ ℕ) (b : Y →₀ ℕ) (i : X) :
      (a i + 1 : ℂ) * g (a + Finsupp.single i 1) b =
        (∑ j, E (.inl i) (.inl j) *
          (if a j = 0 then 0 else g (a - Finsupp.single j 1) b)) +
        ∑ j, E (.inl i) (.inr j) *
          (if b j = 0 then 0 else g a (b - Finsupp.single j 1)) := by
    simpa only [g, row, created_single] using row_step E hE a i b
  have gright (a : X →₀ ℕ) (b : Y →₀ ℕ) (i : Y) :
      (b i + 1 : ℂ) * g a (b + Finsupp.single i 1) =
        (∑ j, E (.inr i) (.inl j) *
          (if a j = 0 then 0 else g (a - Finsupp.single j 1) b)) +
        ∑ j, E (.inr i) (.inr j) *
          (if b j = 0 then 0 else g a (b - Finsupp.single j 1)) := by
    simpa only [g, annihilate, row, rowLower, ite_apply, apply_ite, Pi.zero_apply, created_single] using
      congrFun (row_annihilate E hE a i) b
  have go : ∀ m (a : X →₀ ℕ) (b : Y →₀ ℕ), a.degree + b.degree = m →
      rowPair K L a b = Z * g a b := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b hab
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · subst b
          simpa [g, gaussianCoefficient_zero] using h00
        obtain ⟨i, hi⟩ := NativeGaussianMoment.occupation_nonzero b hb
        let r := b - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = b := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree < m := by
          have := NativeGaussianMoment.sub_single_degree b i hi
          simp only [map_zero, zero_add] at hab
          dsimp [r]; omega
        have hn : (r i + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r i)
        rw [← hr]
        apply mul_left_cancel₀ hn
        rw [hright, mul_left_comm (r i + 1 : ℂ) Z, gright,
          mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          simp
        · apply Finset.sum_congr rfl
          intro j hj
          by_cases hz : r j = 0
          · simp [hz]
          · simp only [hz, ite_false]
            have hjd : (r - Finsupp.single j 1).degree < m :=
              (Finsupp.degree_mono
                (show r - Finsupp.single j 1 ≤ r from tsub_le_self)).trans_lt hd
            rw [ih (r - Finsupp.single j 1).degree hjd 0
              (r - Finsupp.single j 1) (by simp)]
            ring
      · obtain ⟨i, hi⟩ := NativeGaussianMoment.occupation_nonzero a ha
        let r := a - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = a := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree + b.degree < m := by
          have := NativeGaussianMoment.sub_single_degree a i hi
          dsimp [r]; omega
        have hn : (r i + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r i)
        rw [← hr]
        apply mul_left_cancel₀ hn
        rw [hleft, mul_left_comm (r i + 1 : ℂ) Z, gleft,
          mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          by_cases hz : r j = 0
          · simp [hz]
          · simp only [hz, ite_false]
            have hjd : (r - Finsupp.single j 1).degree + b.degree < m :=
              (Nat.add_le_add_right (Finsupp.degree_mono tsub_le_self) _).trans_lt hd
            rw [ih _ hjd _ _ rfl]
            ring
        · apply Finset.sum_congr rfl
          intro j hj
          by_cases hz : b j = 0
          · simp [hz]
          · simp only [hz, ite_false]
            have hjd : r.degree + (b - Finsupp.single j 1).degree < m :=
              (Nat.add_le_add_left (Finsupp.degree_mono tsub_le_self) _).trans_lt hd
            rw [ih _ hjd _ _ rfl]
            ring
  constructor
  · change Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      row K d n * gaussianCoefficient K₂ (n.sumElim e)‖)
    simp_rw [hswap]
    obtain ⟨p, q, hp, hq, hs, heq⟩ := row_pair_moments K L hK hL hA hB d e
    exact hs
  · change (∑' n : H →₀ ℕ, (weight n : ℂ) *
      row K d n * gaussianCoefficient K₂ (n.sumElim e)) = Z * g d e
    simp_rw [hswap]
    exact go _ d e rfl
#print axioms finite_sewing
end D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
