/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairBinaryPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RepeatedPairBinaryPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All four binary characteristic polynomial rows of the full four-dimensional operator. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairModularTables
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: repeated-pair-modular, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. These polynomial identities
are for the entire four-dimensional repeated-pair operator. Only the
even/even row passes splitting; no row passing this necessary test is
asserted to have integral graph spectrum. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairBinaryPolynomial
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

/-- Characteristic determinant of the full operator over every field. -/
theorem characteristic {R : Type*} [Field R] (a b c : R) :
    (tensorK a b c).charpoly =
      (tensorK (C a) (C b) (C c)-(X : R[X]) • 1).det := by
  have hm : (tensorK a b c).charmatrix =
      -(tensorK (C a) (C b) (C c)-(X : R[X]) • 1) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Matrix.charmatrix,tensorK,E,F,kroneckerMap_apply]
  rw [Matrix.charpoly,hm,Matrix.det_neg]
  norm_num

/-- Every binary tail residue pair and its entire characteristic polynomial. -/
theorem binary_rows (b c : ZMod 2) :
    (tensorK (1 : ZMod 2) b c).charpoly =
      if b=0 then
        (if c=0 then X^3*(X+1) else X^2*(X^2+X+1))
      else
        (if c=0 then X^2*(X^2+X+1) else (X+1)^2*(X^2+X+1)) := by
  rw [characteristic,det_tensorK_sub_scalar]
  have h24 : (24 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (24 : ZMod 2) = 0 by decide +kernel)
  have h44 : (44 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (44 : ZMod 2) = 0 by decide +kernel)
  have h30 : (30 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (30 : ZMod 2) = 0 by decide +kernel)
  have h9 : (9 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (9 : ZMod 2) = 1 by decide +kernel)
  have h72 : (72 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (72 : ZMod 2) = 0 by decide +kernel)
  have h110 : (110 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (110 : ZMod 2) = 0 by decide +kernel)
  have h59 : (59 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (59 : ZMod 2) = 1 by decide +kernel)
  have h13 : (13 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (13 : ZMod 2) = 1 by decide +kernel)
  have h243 : (243 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (243 : ZMod 2) = 1 by decide +kernel)
  have h291 : (291 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (291 : ZMod 2) = 1 by decide +kernel)
  have h118 : (118 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (118 : ZMod 2) = 0 by decide +kernel)
  have h19 : (19 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (19 : ZMod 2) = 1 by decide +kernel)
  have h3 : (3 : (ZMod 2)[X]) = 1 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_1] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (3 : ZMod 2) = 1 by decide +kernel)
  have h4 : (4 : (ZMod 2)[X]) = 0 := by
    simpa only [Polynomial.C_ofNat, Polynomial.C_0] using
      congrArg (Polynomial.C : ZMod 2 → (ZMod 2)[X])
        (show (4 : ZMod 2) = 0 by decide +kernel)
  have h : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide +kernel
  rcases h b with rfl | rfl <;> rcases h c with rfl | rfl <;>
    norm_num [← Polynomial.C_ofNat] <;> ring_nf <;>
    simp only [h24, h44, h30, h9, h72, h110, h59, h13, h243, h291, h118, h19, h3, h4, CharTwo.sub_eq_add,
      mul_zero, mul_one, zero_add, add_zero]

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairBinaryPolynomial
