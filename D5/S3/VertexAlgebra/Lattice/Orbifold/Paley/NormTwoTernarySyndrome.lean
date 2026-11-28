/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/NormTwoTernarySyndrome
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/NormTwoTernarySyndrome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: A norm-two lattice row forces a collision of short ternary syndromes. -/

import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
For an integral Gram matrix `G` and frame rows `U` in the catalogue basis,
the pairing matrix is `F = G * Uᵀ`. A norm-two vector gives a nonzero word of
Hamming weight at most six in the kernel of `F` modulo three. For P48p the
frame identities and the injectivity of the syndrome on words of weight at
most three are hypotheses to be verified on the concrete matrices.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NormTwoTernarySyndrome

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The syndrome of a ternary word under the integral column pairing matrix. -/
def ternarySyndrome (F : Matrix ι κ ℤ) (u : κ → ZMod 3) : ι → ZMod 3 :=
  (F.map (Int.castRingHom (ZMod 3))) *ᵥ u

/-- A norm-two row gives a short nonzero ternary kernel word whenever the
norm-twelve pairing identity holds and more than 24 columns share one parity. -/
theorem exists_short_ternary_kernel_word_of_norm_two
    (G : Matrix ι ι ℤ) (F : Matrix ι κ ℤ)
    (hFrame : F * Fᵀ = (12 : ℤ) • G)
    (hParity : ∀ i j k, (F i j : ZMod 2) = (F i k : ZMod 2))
    (hColumns : 24 < Fintype.card κ) (x : ι → ℤ)
    (hx : (x ᵥ* G) ⬝ᵥ x = 2) :
    ∃ u : κ → ZMod 3, u ≠ 0 ∧ hammingNorm u ≤ 6 ∧ ternarySyndrome F u = 0 := by
  let y := x ᵥ* F
  have hPair : y ᵥ* Fᵀ = (12 : ℤ) • (x ᵥ* G) := by
    change (x ᵥ* F) ᵥ* Fᵀ = _
    rw [Matrix.vecMul_vecMul, hFrame, Matrix.vecMul_smul]
  have hyNorm : (∑ j, y j ^ 2) = 24 := by
    calc
      _ = y ⬝ᵥ y := by simp only [dotProduct, pow_two]
      _ = y ⬝ᵥ (Fᵀ *ᵥ x) := by rw [Matrix.mulVec_transpose]
      _ = (y ᵥ* Fᵀ) ⬝ᵥ x := Matrix.dotProduct_mulVec y Fᵀ x
      _ = 24 := by rw [hPair, smul_dotProduct, hx, smul_eq_mul] <;> norm_num
  have hParityY (j k : κ) : (y j : ZMod 2) = (y k : ZMod 2) := by
    simp only [y, Matrix.vecMul_apply_eq_sum, Int.cast_sum, Int.cast_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [hParity i j k])
  obtain ⟨j₀⟩ : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  have hEven : (y j₀ : ZMod 2) = 0 := by
    by_contra hOdd
    have hLower : (Fintype.card κ : ℤ) ≤ ∑ j, y j ^ 2 := by
      calc
        _ = ∑ j : κ, (1 : ℤ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have hne : y j ≠ 0 := by
            intro hj
            apply hOdd
            rw [← hParityY j j₀, hj, Int.cast_zero]
          have hPos := sq_pos_of_ne_zero hne
          omega
    rw [hyNorm] at hLower
    exact (not_le_of_gt hColumns) (by exact_mod_cast hLower)
  have hDiv (j : κ) : ∃ a : ℤ, y j = 2 * a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (y j) 2).mp ((hParityY j j₀).trans hEven)
  choose w hw using hDiv
  have hyEven : y = (2 : ℤ) • w := by
    funext j
    simpa only [Pi.smul_apply, smul_eq_mul] using hw j
  have hwNorm : (∑ j, w j ^ 2) = 6 := by
    have hScale : (∑ j, y j ^ 2) = 4 * ∑ j, w j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [hw j] <;> ring)
    omega
  let u : κ → ZMod 3 := fun j => (w j : ZMod 3)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hu
    have hDvd : (9 : ℤ) ∣ ∑ j, w j ^ 2 := by
      apply Finset.dvd_sum
      intro j _
      have hj : (w j : ZMod 3) = 0 := congrFun hu j
      obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (w j) 3).mp hj
      change w j = 3 * a at ha
      refine ⟨a ^ 2, ?_⟩
      rw [ha] <;> ring
    rw [hwNorm] at hDvd
    exact (by decide : ¬ (9 : ℤ) ∣ 6) hDvd
  · have hWeight : (hammingNorm u : ℤ) ≤ ∑ j, w j ^ 2 := by
      let support := Finset.univ.filter (fun j => u j ≠ 0)
      calc
        _ = ∑ j ∈ support, (1 : ℤ) := by simp [hammingNorm, support]
        _ ≤ ∑ j ∈ support, w j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hu : u j ≠ 0 := (Finset.mem_filter.mp hj).2
          have hne : w j ≠ 0 := fun hz => hu (by simp [u, hz])
          have hPos := sq_pos_of_ne_zero hne
          omega
        _ ≤ ∑ j, w j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => sq_nonneg (w j))
    rw [hwNorm] at hWeight
    exact_mod_cast hWeight
  · have hTwoPair : (2 : ℤ) • (F *ᵥ w) = (12 : ℤ) • (x ᵥ* G) := by
      calc
        _ = F *ᵥ y := by rw [hyEven, Matrix.mulVec_smul]
        _ = y ᵥ* Fᵀ := (Matrix.vecMul_transpose F y).symm
        _ = _ := hPair
    have hwPair (i : ι) : (F *ᵥ w) i = 6 * (x ᵥ* G) i := by
      have hi : 2 * (F *ᵥ w) i = 12 * (x ᵥ* G) i := by
        simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hTwoPair i
      omega
    funext i
    calc
      ternarySyndrome F u i = ((F *ᵥ w) i : ZMod 3) :=
        ((Int.castRingHom (ZMod 3)).map_mulVec F w i).symm
      _ = 0 := by
        rw [hwPair i, Int.cast_mul, show ((6 : ℤ) : ZMod 3) = 0 by decide, zero_mul]

/-- The absence of nonzero ternary kernel words of weight at most six
excludes norm-two rows for the integral Gram matrix. -/
theorem norm_ne_two_of_no_short_ternary_kernel
    (G : Matrix ι ι ℤ) (F : Matrix ι κ ℤ)
    (hFrame : F * Fᵀ = (12 : ℤ) • G)
    (hParity : ∀ i j k, (F i j : ZMod 2) = (F i k : ZMod 2))
    (hColumns : 24 < Fintype.card κ)
    (hKernel : ∀ u : κ → ZMod 3, hammingNorm u ≤ 6 → ternarySyndrome F u = 0 → u = 0)
    (x : ι → ℤ) : (x ᵥ* G) ⬝ᵥ x ≠ 2 := by
  intro hx
  obtain ⟨u, hu, hWeight, hSyndrome⟩ :=
    exists_short_ternary_kernel_word_of_norm_two G F hFrame hParity hColumns x hx
  exact hu (hKernel u hWeight hSyndrome)

private theorem eq_zero_of_short_syndrome_injective (F : Matrix ι κ ℤ)
    (hInjective : Set.InjOn (ternarySyndrome F) {u | hammingNorm u ≤ 3})
    (u : κ → ZMod 3) (hWeight : hammingNorm u ≤ 6) (hSyndrome : ternarySyndrome F u = 0) :
    u = 0 := by
  classical
  let support := Finset.univ.filter (fun j => u j ≠ 0)
  have hCard : support.card ≤ 6 := hWeight
  obtain ⟨s, hs, hSize⟩ := Finset.exists_subset_card_eq (min_le_right 3 support.card)
  let a : κ → ZMod 3 := fun j => if j ∈ s then u j else 0
  let b : κ → ZMod 3 := fun j => if j ∈ s then 0 else -u j
  have ha : hammingNorm a ≤ 3 := by
    calc
      _ ≤ s.card := by
        unfold hammingNorm
        apply Finset.card_le_card
        intro j hj
        by_contra hOutside
        exact (Finset.mem_filter.mp hj).2 (by simp [a, hOutside])
      _ ≤ 3 := hSize.trans_le (min_le_left _ _)
  have hb : hammingNorm b ≤ 3 := by
    calc
      _ ≤ (support \ s).card := by
        unfold hammingNorm
        apply Finset.card_le_card
        intro j hj
        have hne : b j ≠ 0 := (Finset.mem_filter.mp hj).2
        have hOutside : j ∉ s := fun hj' => hne (by simp [b, hj'])
        have hu : u j ≠ 0 := fun hz => hne (by simp [b, hOutside, hz])
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hu⟩, hOutside⟩
      _ ≤ 3 := by
        rw [Finset.card_sdiff_of_subset hs, hSize]
        by_cases h : support.card ≤ 3
        · simp [min_eq_right h]
        · rw [min_eq_left (by omega : 3 ≤ support.card)]
          omega
  have hab : a - b = u := by
    funext j
    by_cases hj : j ∈ s <;> simp [a, b, hj]
  have hEqual : ternarySyndrome F a = ternarySyndrome F b := by
    apply sub_eq_zero.mp
    calc
      _ = ternarySyndrome F (a - b) := (Matrix.mulVec_sub _ _ _).symm
      _ = 0 := by rw [hab, hSyndrome]
  rw [← hab, hInjective ha hb hEqual, sub_self]

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)

/-- Injectivity on ternary words of weight at most three supplies the
norm-two exclusion for the lattice bilinear form. -/
theorem bilinear_ne_two_of_short_syndrome_injective
    (D : LatticeData) (F : Matrix (Fin D.rank) κ ℤ)
    (hFrame : F * Fᵀ = (12 : ℤ) • D.G)
    (hParity : ∀ i j k, (F i j : ZMod 2) = (F i k : ZMod 2))
    (hColumns : 24 < Fintype.card κ)
    (hInjective : Set.InjOn (ternarySyndrome F) {u | hammingNorm u ≤ 3})
    (x : Charge D) : bilinear D x x ≠ 2 := by
  have hNorm : (x ᵥ* D.G) ⬝ᵥ x = bilinear D x x := by
    rw [← Matrix.dotProduct_mulVec]
    simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum, mul_assoc, bilinear]
  rw [← hNorm]
  exact norm_ne_two_of_no_short_ternary_kernel D.G F hFrame hParity hColumns
    (eq_zero_of_short_syndrome_injective F hInjective) x

#print axioms exists_short_ternary_kernel_word_of_norm_two
#print axioms norm_ne_two_of_no_short_ternary_kernel
#print axioms bilinear_ne_two_of_short_syndrome_injective

end D5.S3.VertexAlgebra.Lattice.Orbifold.NormTwoTernarySyndrome
