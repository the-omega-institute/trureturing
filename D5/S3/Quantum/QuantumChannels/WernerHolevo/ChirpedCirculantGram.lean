/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier unitarity and Hilbert–Schmidt Gram factorization of chirped circulants. -/

import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-! The Fourier diagonalization and Hilbert–Schmidt Gram identity for chirped circulants. -/

open scoped ComplexConjugate
open Matrix D5.S3.Quantum.Dynamics

namespace ChirpedCirculantGram

noncomputable section

variable {n : ℕ} [NeZero n]

private abbrev phase (x : ZMod n) : ℂ := ZMod.stdAddChar x

private theorem phase_add (x y : ZMod n) : phase (x + y) = phase x * phase y :=
  AddChar.map_add_eq_mul ZMod.stdAddChar x y

private theorem phase_star (x : ZMod n) : star (phase x) = phase (-x) := by
  simp only [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, Complex.star_def]

private theorem phase_sum (a : ZMod n) :
    ∑ x : ZMod n, phase (a * x) = if a = 0 then (n : ℂ) else 0 := by
  by_cases ha : a = 0 <;>
    simpa [ha, mul_comm a, ZMod.card] using
      AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar n)

private abbrev fourier : Matrix (ZMod n) (ZMod n) ℂ :=
  PolygonalFourierCouplings.transform n

private theorem fourier_unitary : fourier (n := n) ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  exact PolygonalFourierCouplings.transform_unitary n

private theorem diagonal_unitary (f : ZMod n → ℂ) (hf : ∀ x, ‖f x‖ = 1) :
    Matrix.diagonal f ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
  rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro x
  apply Unitary.mem_iff_self_mul_star.mpr
  simp only [Complex.star_def, Complex.mul_conj', hf x, one_pow, Complex.ofReal_one]

/-- The circulant kernel of a unit-modulus even spectrum. -/
def kernel (μ : ZMod n → ℂ) (z : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ∑ l, phase (l * z) * μ l

private theorem kernel_even (μ : ZMod n → ℂ) (hμ : ∀ l, μ (-l) = μ l) (z : ZMod n) :
    kernel μ (-z) = kernel μ z := by
  unfold kernel
  congr 1
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun l => by simp [hμ, mul_neg, neg_mul])

private theorem circulant_unitary (μ : ZMod n → ℂ) (hμ : ∀ l, ‖μ l‖ = 1) :
    (fun x y => kernel μ (y - x) : Matrix (ZMod n) (ZMod n) ℂ) ∈
      Matrix.unitaryGroup (ZMod n) ℂ := by
  -- Mathlib's circulant uses the row index minus the column index.
  change (Matrix.circulant (kernel μ))ᵀ ∈ Matrix.unitaryGroup (ZMod n) ℂ
  apply Matrix.transpose_mem_unitaryGroup_iff.mpr
  have hkernel : kernel μ = (ZMod.dft (N := n) (E := ℂ)).symm μ := by
    funext z
    simp only [kernel, ZMod.invDFT_apply, smul_eq_mul]
  have hspectrum : PolygonalFourierCouplings.spectralValue n (kernel μ) = μ := by
    unfold PolygonalFourierCouplings.spectralValue
    rw [hkernel, LinearEquiv.apply_symm_apply]
  have hspec : fourier * Matrix.circulant (kernel μ) = diagonal μ * fourier := by
    simpa only [hspectrum] using
      PolygonalFourierCouplings.circulant_spectral n (kernel μ)
  have hleft : fourierᴴ * fourier = (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (fourier_unitary (n := n))
  have hform : Matrix.circulant (kernel μ) = fourierᴴ * diagonal μ * fourier := by
    calc
      _ = (fourierᴴ * fourier) * Matrix.circulant (kernel μ) := by
        rw [hleft, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hspec, ← Matrix.mul_assoc]
  have hstar : fourierᴴ ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (fourier_unitary (n := n))
  rw [hform]
  exact (Matrix.unitaryGroup (ZMod n) ℂ).mul_mem
    ((Matrix.unitaryGroup (ZMod n) ℂ).mul_mem hstar (diagonal_unitary μ hμ))
    (fourier_unitary (n := n))

/-- A chirped circulant and its one-variable seed. -/
def chirped (c v : ZMod n) (μ : ZMod n → ℂ) : Matrix (ZMod n) (ZMod n) ℂ :=
  fun x y => phase (v * (x + y) + c * (x^2 + y^2)) * kernel μ (y - x)

def seed (h c : ZMod n) (μ : ZMod n → ℂ) (z : ZMod n) : ℂ :=
  phase (c * h * z^2) * kernel μ z

/-- The seed of a unit-modulus spectrum has squared Euclidean norm one. -/
theorem seed_norm_sq (h c : ZMod n) (μ : ZMod n → ℂ) (hμ : ∀ l, ‖μ l‖ = 1) :
    ∑ d : ZMod n, ‖seed h c μ d‖ ^ 2 = 1 := by
  let C : Matrix (ZMod n) (ZMod n) ℂ := Matrix.of fun x y => kernel μ (y - x)
  have hC : C ∈ Matrix.unitaryGroup (ZMod n) ℂ := circulant_unitary μ hμ
  have hunitary := Matrix.mem_unitaryGroup_iff.mp hC
  rw [Matrix.star_eq_conjTranspose] at hunitary
  have hrow : (∑ d : ZMod n, kernel μ d * star (kernel μ d)) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, C, Matrix.of_apply,
      sub_zero, Matrix.one_apply_eq] using
      congrArg (fun A : Matrix (ZMod n) (ZMod n) ℂ => A 0 0) hunitary
  have hkernel : (∑ d : ZMod n, ‖kernel μ d‖ ^ 2) = 1 := by
    simpa only [Complex.re_sum, Complex.star_def, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] using
      congrArg Complex.re hrow
  simpa only [seed, norm_mul, AddChar.norm_apply, one_mul] using hkernel

theorem chirped_transpose (c v : ZMod n) (μ : ZMod n → ℂ) (hμ : ∀ l, μ (-l) = μ l) :
    (chirped c v μ)ᵀ = chirped c v μ := by
  ext x y
  change phase (v * (y + x) + c * (y^2 + x^2)) * kernel μ (x - y) =
    phase (v * (x + y) + c * (x^2 + y^2)) * kernel μ (y - x)
  rw [add_comm y x, add_comm (y ^ 2), ← neg_sub, kernel_even μ hμ]

theorem chirped_unitary (c v : ZMod n) (μ : ZMod n → ℂ) (hμ : ∀ l, ‖μ l‖ = 1) :
    chirped c v μ ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
  let z (x : ZMod n) := phase (v * x + c * x^2)
  let C : Matrix (ZMod n) (ZMod n) ℂ := Matrix.of fun x y => kernel μ (y - x)
  have hz : diagonal z ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
    exact diagonal_unitary z (fun _ => AddChar.norm_apply _ _)
  have hC : C ∈ Matrix.unitaryGroup (ZMod n) ℂ := circulant_unitary μ hμ
  have hEq : chirped c v μ = diagonal z * C * diagonal z := by
    apply Matrix.ext
    intro x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have he : v * (x + y) + c * (x^2 + y^2) =
        (v * x + c * x^2) + (v * y + c * y^2) := by ring
    rw [chirped, he, phase_add]
    change z x * z y * C x y = z x * C x y * z y
    exact mul_right_comm _ _ _
  rw [hEq]
  exact (Matrix.unitaryGroup (ZMod n) ℂ).mul_mem
    ((Matrix.unitaryGroup (ZMod n) ℂ).mul_mem hz hC) hz

private def sumDifference (h : ZMod n) (hh : 2 * h = 1) :
    (ZMod n × ZMod n) ≃ (ZMod n × ZMod n) where
  toFun xy := (xy.1 + xy.2, xy.2 - xy.1)
  invFun sd := (h * (sd.1 - sd.2), h * (sd.1 + sd.2))
  left_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext <;> dsimp
    · linear_combination x * hh
    · linear_combination y * hh
  right_inv := by
    rintro ⟨s, d⟩
    apply Prod.ext <;> dsimp
    · linear_combination s * hh
    · linear_combination d * hh

private theorem chirped_split (h : ZMod n) (hh : 2 * h = 1)
    (c v : ZMod n) (μ : ZMod n → ℂ) (x y : ZMod n) :
    chirped c v μ x y =
      phase (v * (x + y) + c * h * (x + y)^2) * seed h c μ (y - x) := by
  have hsq : c * (x^2 + y^2) =
      c * h * (x + y)^2 + c * h * (y - x)^2 := by
    linear_combination -c * (x^2 + y^2) * hh
  rw [chirped, seed, hsq, ← add_assoc, phase_add, mul_assoc]

/-- The actual Hilbert–Schmidt pairing separates into the seed pairing and a
quadratic character sum in the sum coordinate. -/
theorem chirped_gram (h : ZMod n) (hh : 2 * h = 1)
    (c c' v w : ZMod n) (μ ν : ZMod n → ℂ) :
    ∑ xy : ZMod n × ZMod n, star (chirped c v μ xy.1 xy.2) * chirped c' w ν xy.1 xy.2 =
      (∑ d : ZMod n, star (seed h c μ d) * seed h c' ν d) *
        ∑ s : ZMod n, phase ((w-v)*s + (c'-c)*h*s^2) := by
  let term (sd : ZMod n × ZMod n) :=
    (star (seed h c μ sd.2) * seed h c' ν sd.2) *
      phase ((w-v)*sd.1 + (c'-c)*h*sd.1^2)
  calc
    _ = ∑ sd : ZMod n × ZMod n, term sd := by
      apply Fintype.sum_equiv (sumDifference h hh)
      rintro ⟨x, y⟩
      simp only [chirped_split h hh, star_mul, phase_star]
      dsimp [sumDifference, term]
      have he : (w - v) * (x + y) + (c' - c) * h * (x + y)^2 =
          -(v * (x + y) + c * h * (x + y)^2) +
            (w * (x + y) + c' * h * (x + y)^2) := by ring
      rw [he, phase_add (-(v * (x + y) + c * h * (x + y)^2))
        (w * (x + y) + c' * h * (x + y)^2)]
      ac_rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, term, ← Finset.sum_mul, ← Finset.mul_sum]

/-- The modulations of one seed have Hilbert–Schmidt Gram matrix `n • 1`. -/
theorem chirped_gram_same_seed (h : ZMod n) (hh : 2 * h = 1)
    (c v w : ZMod n) (μ : ZMod n → ℂ) (hμ : ∀ l, ‖μ l‖ = 1) :
    ∑ xy : ZMod n × ZMod n, star (chirped c v μ xy.1 xy.2) * chirped c w μ xy.1 xy.2 =
      if v = w then (n : ℂ) else 0 := by
  have hseed : (∑ d : ZMod n, star (seed h c μ d) * seed h c μ d) = 1 := by
    simpa only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg Complex.ofReal (seed_norm_sq h c μ hμ)
  rw [chirped_gram h hh c c v w μ μ, hseed, one_mul]
  simp only [sub_self, zero_mul, add_zero, phase_sum]
  by_cases hvw : v = w
  · subst w
    simp
  · have hwv : w ≠ v := fun hEq => hvw hEq.symm
    rw [if_neg (sub_ne_zero.mpr hwv), if_neg hvw]

#print axioms chirped_unitary
#print axioms chirped_transpose
#print axioms chirped_gram
#print axioms seed_norm_sq
#print axioms chirped_gram_same_seed

end

end ChirpedCirculantGram
