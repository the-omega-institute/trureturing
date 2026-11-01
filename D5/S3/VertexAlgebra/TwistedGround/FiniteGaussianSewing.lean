/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial rows of the actual block Gaussian coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import Mathlib.LinearAlgebra.Finsupp.LSum

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
    ext (j | j) <;> simp [Finsupp.sumElim_apply]
  have hleft (j : X) : d.sumElim n - Finsupp.single (.inl j) 1 =
      (d - Finsupp.single j 1).sumElim n := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply]
  have hright (j : H) : d.sumElim n - Finsupp.single (.inr j) 1 =
      d.sumElim (n - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply]
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
        simp only [Finsupp.degree_add, Finsupp.degree_single] at h
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
  · have hsub : α - Finsupp.single i 1 = α := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [Finsupp.tsub_apply, hz]
      · simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hji]
    have hiff : α ≤ n + Finsupp.single i 1 ↔ α ≤ n := by
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
          exact add_le_add_right hh _
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


private theorem polynomialGaussian_expansion (A : Matrix H H ℂ)
    (p : MvPolynomial H ℂ) :
    polynomialGaussian A p = fun n =>
      ∑ α ∈ p.support, p.coeff α * created α (gaussianCoefficient A) n := by
  calc
    polynomialGaussian A p =
        polynomialGaussian A (∑ α ∈ p.support, monomial α (p.coeff α)) :=
      congrArg (polynomialGaussian A) p.as_sum
    _ = _ := by
      simp only [map_sum, polynomialGaussian_monomial, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]

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

end D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
