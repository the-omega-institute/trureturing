/- GID: D5/S3/Quantum/Reduction/CanonicalPositiveRefinement
   generality: I
   mirror-B: D5/B/S3/Quantum/Reduction/CanonicalPositiveRefinement
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Original positive finite records of canonical filters have normalized block scalars and positive amplifications. -/

import D5.S3.Quantum.Reduction.SingularPositiveRefinement
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open D5.S3.Quantum.Reduction.PositiveRefinementRigidity
open D5.S3.Quantum.Reduction.SingularPositiveRefinement
namespace D5.S3.Quantum.Reduction.CanonicalPositiveRefinement
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
variable {d : B → Type*} [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]

/-- Every actual fine record has one nonnegative coefficient on each original
block, normalized on every nonzero effect block. No positivity stronger than
ordinary positivity of the actual records is a premise. -/
theorem canonical_refinement_coefficients
    (E : ∀ b, Matrix (d b) (d b) ℂ) (hE : ∀ b, (E b).PosSemidef)
    (S : A → ((b : B) → Matrix (d b) (d b) ℂ) →ₗ[ℂ]
      ((b : B) → Matrix (d b) (d b) ℂ))
    (hpos : ∀ a X, (∀ b, (X b).PosSemidef) → ∀ b, (S a X b).PosSemidef)
    (hsum : ∀ X b, ∑ a, S a X b = CFC.sqrt (E b) * X b * CFC.sqrt (E b)) :
    ∃ c : A → B → ℝ, (∀ a b, 0 ≤ c a b ∧ c a b ≤ 1) ∧
      (∀ b, E b ≠ 0 → ∑ a, c a b = 1) ∧
      (∀ a X b, S a X b = (c a b : ℂ) •
        (CFC.sqrt (E b) * X b * CFC.sqrt (E b))) := by
  classical
  have hR (b : B) : (CFC.sqrt (E b))ᴴ = CFC.sqrt (E b) :=
    (CFC.sqrt_nonneg (E b)).posSemidef.isHermitian
  have hs : ∀ X b, ∑ a, S a X b = CFC.sqrt (E b) * X b * (CFC.sqrt (E b))ᴴ := by
    simpa only [hR] using hsum
  obtain ⟨hlocal, -, -⟩ := canonical_refinement_structure (fun b => CFC.sqrt (E b)) S hpos hs
  let K (a : A) (b : B) : Matrix (d b) (d b) ℂ →ₗ[ℂ] Matrix (d b) (d b) ℂ :=
    (LinearMap.proj b).comp ((S a).comp (LinearMap.single ℂ _ b))
  have hsingle (b : B) (X : Matrix (d b) (d b) ℂ) (hX : X.PosSemidef) :
      ∀ z, ((Pi.single b X : (z : B) → Matrix (d z) (d z) ℂ) z).PosSemidef := by
    intro z
    by_cases hz : b = z
    · subst z; simpa using hX
    · simpa [Pi.single_eq_of_ne (Ne.symm hz)] using
        (PosSemidef.zero : (0 : Matrix (d z) (d z) ℂ).PosSemidef)
  have hex (a : A) (b : B) : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ X,
      K a b X = (c : ℂ) • (CFC.sqrt (E b) * X * CFC.sqrt (E b)) := by
    apply filter_dominated_scalar (E b) (hE b) (K a b)
    · intro X hX
      exact hpos a _ (hsingle b X hX) b
    · intro X hX
      have hh := Finset.single_le_sum
        (fun a' (_ : a' ∈ Finset.univ) => (hpos a' _ (hsingle b X hX) b).nonneg)
        (Finset.mem_univ a)
      rw [hsum] at hh
      simpa only [K, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
        Pi.single_eq_same] using hh
  choose c hc hc' heq using hex
  have hformula (a : A) (X : (b : B) → Matrix (d b) (d b) ℂ) (b : B) :
      S a X b = (c a b : ℂ) • (CFC.sqrt (E b) * X b * CFC.sqrt (E b)) := by
    rw [hlocal a X b]
    exact heq a b (X b)
  refine ⟨c, fun a b => ⟨hc a b, hc' a b⟩, ?_, hformula⟩
  intro b hb
  have hh := hsum (fun b => (1 : Matrix (d b) (d b) ℂ)) b
  simp only [hformula, mul_one, CFC.sqrt_mul_sqrt_self (E b) (hE b).nonneg] at hh
  have hh' : ((∑ a, c a b : ℝ) : ℂ) • E b = (1 : ℂ) • E b := by
    simpa only [Complex.ofReal_sum, Finset.sum_smul, one_smul] using hh
  exact Complex.ofReal_injective (smul_left_injective ℂ hb hh')


/-- Each original record remains positive after adjoining every finite matrix
ancilla to every original block. This is complete positivity of the actual
direct-sum maps, expressed on their literal matrix-entry amplifications. -/
theorem canonical_refinement_completely_positive
    (E : ∀ b, Matrix (d b) (d b) ℂ) (hE : ∀ b, (E b).PosSemidef)
    (S : A → ((b : B) → Matrix (d b) (d b) ℂ) →ₗ[ℂ]
      ((b : B) → Matrix (d b) (d b) ℂ))
    (hpos : ∀ a X, (∀ b, (X b).PosSemidef) → ∀ b, (S a X b).PosSemidef)
    (hsum : ∀ X b, ∑ a, S a X b = CFC.sqrt (E b) * X b * CFC.sqrt (E b)) :
    ∀ a (k : ℕ) (Z : ∀ b, Matrix (d b × Fin k) (d b × Fin k) ℂ),
      (∀ b, (Z b).PosSemidef) → ∀ b,
      (show Matrix (d b × Fin k) (d b × Fin k) ℂ from
        fun i j => S a (fun z => fun r s => Z z (r, i.2) (s, j.2)) b i.1 j.1).PosSemidef := by
  classical
  obtain ⟨c, hc, -, hf⟩ := canonical_refinement_coefficients E hE S hpos hsum
  intro a k Z hZ b
  let R := CFC.sqrt (E b)
  let W : Matrix (d b × Fin k) (d b × Fin k) ℂ := R ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)
  have hR : Rᴴ = R := (CFC.sqrt_nonneg (E b)).posSemidef.isHermitian
  have heq : (fun (i : d b × Fin k) (j : d b × Fin k) =>
      S a (fun z => fun r s => Z z (r, i.2) (s, j.2)) b i.1 j.1) =
      (c a b : ℂ) • (W * Z b * Wᴴ) := by
    ext i j
    rw [hf]
    simp only [Matrix.smul_apply, smul_eq_mul]
    congr 1
    change (R * (show Matrix (d b) (d b) ℂ from fun r s => Z b (r, i.2) (s, j.2)) * R) i.1 j.1 = _
    calc
      _ = (R * (show Matrix (d b) (d b) ℂ from fun r s => Z b (r, i.2) (s, j.2)) * Rᴴ) i.1 j.1 := by rw [hR]
      _ = _ := by simp [W, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc,
      mul_ite, ite_mul, apply_ite]
  rw [heq]
  exact ((hZ b).mul_mul_conjTranspose_same W).smul
    (by simpa [Complex.le_def] using (hc a b).1 : (0 : ℂ) ≤ (c a b : ℂ))

#print axioms canonical_refinement_completely_positive

#print axioms canonical_refinement_coefficients
end D5.S3.Quantum.Reduction.CanonicalPositiveRefinement
