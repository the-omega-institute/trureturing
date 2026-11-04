/- GID: D5/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeSugawaraNullFrame
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Finite inverse-Gram Sugawara change of basis in an arbitrary null frame. -/

import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
import Mathlib.Tactic

/-! The original quadratic Sugawara form in an arbitrary null/transverse basis.
Every coefficient is the finite H-weighted change of basis of original standard
basis currents. Both inverse-Gram equations and actual normal-ordering branches
are retained. No transverse metric is silently replaced, and no shell is imported.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeSugawaraNullFrame

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame
open D5.S3.VertexAlgebra.LatticeBRSTModeFiltration
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeQuartetContraction
open D5.S3.Quantum.Fermionic.BcGhostFock

abbrev E (D : LatticeData) := LatticeLightConeCoordinates.E D
abbrev Label (t : ℕ) := LatticeLightConeCoordinates.NullFrame.Label t

open private completeBasis_plus completeBasis_minus completeBasis_transverse repr_plus repr_minus repr_transverse from D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

/-- The original normal-ordering branch written with the actual linear current
`a`; no new operator is introduced. -/
def originalNormal (u v : E D) (k l : ℤ) : Module.End ℂ (Carrier D) :=
  if k < 0 then a u k * a v l else a v l * a u k

/-- The same branch after expanding in the supplied complete null/transverse
basis. -/
def frameNormal (c d : Label t) (k l : ℤ) : Module.End ℂ (Carrier D) :=
  originalNormal (F.completeBasis B c) (F.completeBasis B d) k l

/-- Coefficients obtained by the literal finite change of basis of the two
original current factors. -/
def frameCoeff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (c d : Label t) : ℂ :=
  ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j * (F.completeBasis B).repr (standardBasis D i) c *
      (F.completeBasis B).repr (standardBasis D j) d

theorem a_standardBasis (i : Fin D.rank) (n : ℤ) :
    a (standardBasis D i) n = neutralMode D i n := by
  classical
  simp [a, standardBasis, Pi.basisFun, Pi.single_apply]

theorem a_basis_expand {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (E D)) (u : E D) (n : ℤ) :
    a u n = ∑ c : ι, b.repr u c • a (b c) n := by
  classical
  let A : E D →ₗ[ℂ] Module.End ℂ (Carrier D) :=
    { toFun := fun x => a x n
      map_add' := by
        intro x y
        exact a_add_vectors x y n
      map_smul' := by
        intro z x
        exact a_smul_vector z x n }
  calc
    a u n = A u := rfl
    _ = A (∑ c : ι, b.repr u c • b c) := by rw [b.sum_repr u]
    _ = ∑ c : ι, b.repr u c • A (b c) := by
      simp only [map_sum, map_smul]
    _ = ∑ c : ι, b.repr u c • a (b c) n := rfl

theorem originalNormal_eq_normalSummand (i j : Fin D.rank) (k l : ℤ) :
    originalNormal (standardBasis D i) (standardBasis D j) k l =
      normalSummand D i j k l := by
  simp only [originalNormal, normalSummand, a_standardBasis]

theorem originalNormal_basis_expand {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (E D)) (u v : E D) (k l : ℤ) :
    originalNormal u v k l =
      ∑ c : ι, ∑ d : ι,
        (b.repr u c * b.repr v d) •
          originalNormal (b c) (b d) k l := by
  classical
  by_cases hk : k < 0
  · simp only [originalNormal, if_pos hk]
    rw [a_basis_expand b u k, a_basis_expand b v l]
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    ring
  · simp only [originalNormal, if_neg hk]
    rw [a_basis_expand b v l, a_basis_expand b u k]
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Finset.smul_sum, smul_smul]

private theorem sum_four_reorder {α β γ δ M : Type*} [AddCommMonoid M]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
  classical
  calc
    _ = ∑ a : α, ∑ c : γ, ∑ b : β, ∑ d : δ, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c : γ, ∑ a : α, ∑ b : β, ∑ d : δ, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c : γ, ∑ a : α, ∑ d : δ, ∑ b : β, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

theorem weighted_normal_frame (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (k l : ℤ) :
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j • normalSummand D i j k l) =
      ∑ c : Label t, ∑ d : Label t,
        frameCoeff F B H c d • frameNormal F B c d k l := by
  classical
  have hnormal (i j : Fin D.rank) :
      normalSummand D i j k l =
        ∑ c : Label t, ∑ d : Label t,
          ((F.completeBasis B).repr (standardBasis D i) c *
            (F.completeBasis B).repr (standardBasis D j) d) •
            frameNormal F B c d k l := by
    rw [← originalNormal_eq_normalSummand]
    exact originalNormal_basis_expand (F.completeBasis B)
      (standardBasis D i) (standardBasis D j) k l
  calc
    (∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j • normalSummand D i j k l) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j • (∑ c : Label t, ∑ d : Label t,
          ((F.completeBasis B).repr (standardBasis D i) c *
            (F.completeBasis B).repr (standardBasis D j) d) •
            frameNormal F B c d k l) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hnormal i j]
    _ = ∑ c : Label t, ∑ d : Label t,
        frameCoeff F B H c d • frameNormal F B c d k l := by
      simp only [frameCoeff, frameNormal, Finset.smul_sum, smul_smul]
      rw [sum_four_reorder]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.sum_smul, smul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring

@[simp] theorem frameCoeff_plus_plus
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    :
    frameCoeff F B H (plus t) (plus t) =
      inverseGramPair H F.eMinus F.eMinus := by
  simp [frameCoeff, inverseGramPair, repr_plus, g_symm]

@[simp] theorem frameCoeff_minus_minus
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    frameCoeff F B H (minus t) (minus t) =
      inverseGramPair H F.ePlus F.ePlus := by
  simp [frameCoeff, inverseGramPair, repr_minus, g_symm]

@[simp] theorem frameCoeff_plus_minus
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    frameCoeff F B H (plus t) (minus t) =
      inverseGramPair H F.eMinus F.ePlus := by
  simp [frameCoeff, inverseGramPair, repr_plus, repr_minus, g_symm]

@[simp] theorem frameCoeff_minus_plus
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    frameCoeff F B H (minus t) (plus t) =
      inverseGramPair H F.ePlus F.eMinus := by
  simp [frameCoeff, inverseGramPair, repr_plus, repr_minus, g_symm]

theorem inverseGram_symmetric
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) : H = H.transpose := by
  have hHt : H.transpose * gramComplex D = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M j i) hGH
    simpa [Matrix.mul_apply, Matrix.transpose_apply, gramComplex, Matrix.one_apply,
      D.symmetric, mul_comm, eq_comm] using h
  calc
    H = 1 * H := by simp
    _ = (H.transpose * gramComplex D) * H := by rw [hHt]
    _ = H.transpose * (gramComplex D * H) := by rw [Matrix.mul_assoc]
    _ = H.transpose := by rw [hGH]; simp

private theorem frameCoeff_plus_transverse_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (j : Fin t) :
    frameCoeff F B H (plus t) (transverse t j) = 0 := by
  classical
  have hsymm := inverseGram_symmetric (D := D) H hHG hGH
  have hcol (i : Fin D.rank) :
      ∑ q : Fin D.rank, H q i * g D F.eMinus (standardBasis D q) =
        F.eMinus i := by
    rw [show (∑ q, H q i * g D F.eMinus (standardBasis D q)) =
      ∑ q, H i q * g D F.eMinus (standardBasis D q) by
        apply Finset.sum_congr rfl
        intro q hq
        have hqi : H q i = H i q := congrArg (fun M => M q i) hsymm
        rw [hqi]]
    exact inverse_covector H hHG F.eMinus i
  have hzero : F.projK F.eMinus = 0 := by
    apply Subtype.ext
    change (F.projK F.eMinus : E D) = 0
    rw [coe_projK]
    simp [F.minus_null, F.plus_minus]
  unfold frameCoeff
  simp only [repr_plus, repr_transverse]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol]
  have hrepr :
      (∑ i : Fin D.rank, F.eMinus i • F.projK (standardBasis D i)) = 0 := by
    calc
      _ = F.projK (∑ i : Fin D.rank, F.eMinus i • standardBasis D i) := by
        simp only [map_sum, map_smul]
      _ = F.projK F.eMinus := by
        congr 1
        exact (standardBasis D).sum_repr F.eMinus
      _ = 0 := hzero
  have hc := congrArg (B.coord j) hrepr
  simpa only [map_sum, map_smul, map_zero, smul_eq_mul, Module.Basis.coord_apply] using hc

private theorem frameCoeff_minus_transverse_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (j : Fin t) :
    frameCoeff F B H (minus t) (transverse t j) = 0 := by
  classical
  have hsymm := inverseGram_symmetric (D := D) H hHG hGH
  have hcol (i : Fin D.rank) :
      ∑ q : Fin D.rank, H q i * g D F.ePlus (standardBasis D q) =
        F.ePlus i := by
    rw [show (∑ q, H q i * g D F.ePlus (standardBasis D q)) =
      ∑ q, H i q * g D F.ePlus (standardBasis D q) by
        apply Finset.sum_congr rfl
        intro q hq
        have hqi : H q i = H i q := congrArg (fun M => M q i) hsymm
        rw [hqi]]
    exact inverse_covector H hHG F.ePlus i
  have hzero : F.projK F.ePlus = 0 := by
    apply Subtype.ext
    change (F.projK F.ePlus : E D) = 0
    rw [coe_projK]
    simp [F.plus_null, F.plus_minus]
  unfold frameCoeff
  simp only [repr_minus, repr_transverse]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol]
  have hrepr :
      (∑ i : Fin D.rank, F.ePlus i • F.projK (standardBasis D i)) = 0 := by
    calc
      _ = F.projK (∑ i : Fin D.rank, F.ePlus i • standardBasis D i) := by
        simp only [map_sum, map_smul]
      _ = F.projK F.ePlus := by
        congr 1
        exact (standardBasis D).sum_repr F.ePlus
      _ = 0 := hzero
  have hc := congrArg (B.coord j) hrepr
  simpa only [map_sum, map_smul, map_zero, smul_eq_mul, Module.Basis.coord_apply] using hc

private theorem frameCoeff_swap
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hs : H = H.transpose)
    (c d : Label t) : frameCoeff F B H c d = frameCoeff F B H d c := by
  classical
  unfold frameCoeff
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : H j i = H i j := congrArg (fun M => M j i) hs
  rw [hij]
  ring

private theorem frameCoeff_transverse_plus_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (j : Fin t) :
    frameCoeff F B H (transverse t j) (plus t) = 0 := by
  rw [frameCoeff_swap F B H (inverseGram_symmetric H hHG hGH)]
  exact frameCoeff_plus_transverse_zero F B H hHG hGH j

private theorem frameCoeff_transverse_minus_zero
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (j : Fin t) :
    frameCoeff F B H (transverse t j) (minus t) = 0 := by
  rw [frameCoeff_swap F B H (inverseGram_symmetric H hHG hGH)]
  exact frameCoeff_minus_transverse_zero F B H hHG hGH j

theorem weighted_frame_sector
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) (k l : ℤ) :
    (∑ c : Label t, ∑ d : Label t,
        frameCoeff F B H c d • frameNormal F B c d k l) =
      frameNormal F B (plus t) (minus t) k l +
      frameNormal F B (minus t) (plus t) k l +
      ∑ r : Fin t, ∑ s : Fin t,
        frameCoeff F B H (transverse t r) (transverse t s) •
          frameNormal F B (transverse t r) (transverse t s) k l := by
  classical
  have hlong := inverseGram_longitudinal_coefficients F H hHG
  have hpp : frameCoeff F B H (.inl default) (.inl default) = 0 :=
    (frameCoeff_plus_plus F B H).trans hlong.2.1
  have hmm : frameCoeff F B H (.inr (.inl default)) (.inr (.inl default)) = 0 :=
    (frameCoeff_minus_minus F B H).trans hlong.1
  have hpm : frameCoeff F B H (.inl default) (.inr (.inl default)) = 1 :=
    (frameCoeff_plus_minus F B H).trans hlong.2.2.2
  have hmp : frameCoeff F B H (.inr (.inl default)) (.inl default) = 1 :=
    (frameCoeff_minus_plus F B H).trans hlong.2.2.1
  have hpt (j : Fin t) : frameCoeff F B H (.inl default) (.inr (.inr j)) = 0 :=
    frameCoeff_plus_transverse_zero F B H hHG hGH j
  have hmt (j : Fin t) : frameCoeff F B H (.inr (.inl default)) (.inr (.inr j)) = 0 :=
    frameCoeff_minus_transverse_zero F B H hHG hGH j
  have htp (j : Fin t) : frameCoeff F B H (.inr (.inr j)) (.inl default) = 0 :=
    frameCoeff_transverse_plus_zero F B H hHG hGH j
  have htm (j : Fin t) : frameCoeff F B H (.inr (.inr j)) (.inr (.inl default)) = 0 :=
    frameCoeff_transverse_minus_zero F B H hHG hGH j
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, hpp, hmm, hpm, hmp,
    hpt, hmt, htp, htm, zero_smul, one_smul, zero_add, add_zero,
    Finset.sum_const_zero]
  simp only [plus, minus, transverse, add_assoc]

end D5.S3.VertexAlgebra.LatticeSugawaraNullFrame
