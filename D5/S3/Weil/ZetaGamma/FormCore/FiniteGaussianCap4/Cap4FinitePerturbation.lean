/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4FinitePerturbation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The original finite certificate absorbs all symmetric entry perturbations. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FiniteCertificate
import D5.S3.PrimeGaps.GreedyResidues

/-! Real matrix perturbation consumer of the original kappa = 3/4 LDL certificate.
The entry enclosure is an explicit premise of this reusable lemma. Its actual
integral-matrix supplier is separate; no entry bound or physical cap is asserted
here without that supplier. The zero vector is included throughout. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Cap4FinitePerturbation
open scoped BigOperators Matrix
open Cap4FiniteCertificate

def rho : ℝ := (rhoQ : ℝ)
def eta : ℝ := 1 / 1000000
def delta : ℝ := 1 / 1000000000

/-- The original finite comparison energy, before subtracting the identity margin. -/
def energy (A : Matrix I I ℝ) (u : I → ℝ) : ℝ :=
  rho * (∑ i, weights i * u i) ^ 2 -
    (∑ i, ∑ j, u i * u j * A i j) +
    (1 / 10 : ℝ) * (∑ i, ∑ j, u i * u j * recurrence i j) -
    (23 / 20 : ℝ) * ∑ i, weights i * u i ^ 2

private theorem centerQ_symm (i j : I) : centerQ i j = centerQ j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem center_symm (i j : I) : center i j = center j i :=
  congrArg (Rat.castHom ℝ) (centerQ_symm i j)

private theorem dot_mulVec_sum (M : Matrix I I ℝ) (u : I → ℝ) :
    u ⬝ᵥ (M *ᵥ u) = ∑ i, ∑ j, u i * u j * M i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem certificate_energy (u : I → ℝ) :
    (∑ i, ∑ j, u i * u j * finite16C i j) =
      energy center u - eta * ∑ i, u i ^ 2 := by
  have hterm (i j : I) :
      u i * u j * finite16C i j =
        rho * (weights i * u i) * (weights j * u j) -
        u i * u j * center i j +
        (1 / 10 : ℝ) * (u i * u j * recurrence i j) -
        (if i = j then (23 / 20 : ℝ) * weights i * u i ^ 2 else 0) -
        (if i = j then eta * u i ^ 2 else 0) := by
    rw [finite16C_entry]
    by_cases h : i = j
    · subst j
      simp [rho, rhoQ, eta]
      ring
    · simp [h, rho, rhoQ]
      ring
  have hrank :
      (∑ i, ∑ j, rho * (weights i * u i) * (weights j * u j)) =
        rho * (∑ i, weights i * u i) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum, mul_assoc]
  calc
    (∑ i, ∑ j, u i * u j * finite16C i j) =
        (∑ i, ∑ j, rho * (weights i * u i) * (weights j * u j)) -
        (∑ i, ∑ j, u i * u j * center i j) +
        (∑ i, ∑ j, (1 / 10 : ℝ) * (u i * u j * recurrence i j)) -
        (∑ i, (23 / 20 : ℝ) * weights i * u i ^ 2) -
        (∑ i, eta * u i ^ 2) := by
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp
    _ = energy center u - eta * ∑ i, u i ^ 2 := by
      rw [hrank]
      simp only [energy, Finset.mul_sum, mul_assoc]

/-- Entrywise error controls the actual quadratic form by 16 delta. -/
theorem quadratic_error (A : Matrix I I ℝ) (hA : A.IsSymm)
    (hentry : ∀ i j, |A i j - center i j| ≤ delta) (u : I → ℝ) :
    |∑ i, ∑ j, u i * u j * (A i j - center i j)| ≤
      (16 * delta) * ∑ i, u i ^ 2 := by
  have hsym (i j : I) :
      |A i j - center i j| = |A j i - center j i| := by
    rw [hA.apply j i, center_symm i j]
  have hrow (i : I) : (∑ j, |A i j - center i j|) ≤ 16 * delta := by
    calc
      (∑ j, |A i j - center i j|) ≤ ∑ _j : I, delta :=
        Finset.sum_le_sum (fun j _ => hentry i j)
      _ = 16 * delta := by simp [I, nsmul_eq_mul]
  calc
    |∑ i, ∑ j, u i * u j * (A i j - center i j)| ≤
        ∑ i, u i ^ 2 * ∑ j, |A i j - center i j| :=
      LongGapsBetweenPrimes.abs_quadratic_form_le_rows u
        (fun i j => A i j - center i j) hsym
    _ ≤ ∑ i, u i ^ 2 * (16 * delta) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
    _ = (16 * delta) * ∑ i, u i ^ 2 := by
      rw [← Finset.sum_mul, mul_comm]

/-- The fixed certificate supplies the full comparison margin for every vector,
including zero, whenever the actual symmetric matrix has the stated entry box. -/
theorem perturbed_energy_lower (A : Matrix I I ℝ) (hA : A.IsSymm)
    (hentry : ∀ i j, |A i j - center i j| ≤ delta) (u : I → ℝ) :
    (eta - 16 * delta) * (∑ i, u i ^ 2) ≤ energy A u := by
  have hpos : 0 ≤ u ⬝ᵥ (finite16C *ᵥ u) := by
    simpa only [star_trivial] using
      finite16C_posDef.posSemidef.dotProduct_mulVec_nonneg u
  rw [dot_mulVec_sum, certificate_energy] at hpos
  have herror := (le_abs_self _).trans (quadratic_error A hA hentry u)
  have henergy : energy A u = energy center u -
      (∑ i, ∑ j, u i * u j * (A i j - center i j)) := by
    simp only [energy, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [henergy]
  simpa only [sub_mul, mul_assoc] using sub_le_sub (sub_nonneg.mp hpos) herror

/-- This is the original eta minus the original all-entry operator error. -/
theorem exact_margin : eta - 16 * delta = (123 / 125000000 : ℝ) := by
  norm_num [eta, delta]

theorem perturbed_energy_nonneg (A : Matrix I I ℝ) (hA : A.IsSymm)
    (hentry : ∀ i j, |A i j - center i j| ≤ delta) (u : I → ℝ) :
    0 ≤ energy A u := by
  have hm : 0 ≤ eta - 16 * delta := by rw [exact_margin]; norm_num
  exact (mul_nonneg hm (Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))).trans
    (perturbed_energy_lower A hA hentry u)

end Cap4FinitePerturbation
