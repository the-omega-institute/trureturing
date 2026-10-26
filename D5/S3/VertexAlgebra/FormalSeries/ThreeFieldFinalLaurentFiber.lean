/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite signed fibers for the three inverse-binomial factors. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
/-! proof_shape: content
admission_basis: escape-witness
escape_witness: signed exponent balance proves finite support of the inverse coefficient fiber.
The binomial factors retain the Mathlib suppliers and their attribution. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.ThreeFieldFinalLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
abbrev LaurentIndex := (ℕ × ℕ) × (ℕ × ℕ)

/-- Native input selected by the Laurent monomial, in SIGNED arithmetic. -/
def laurentInput (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3)
    (i : LaurentIndex) : Exponent 3 :=
  ![e 0 + k - i.1.1 - i.2.1,
    e 1 + 2 * k + i.1.1 - i.1.2 + i.2.1 - i.2.2,
    e 2 + a 0 + a 1 + a 2 + i.1.2 + i.2.2]

/-- Structural relevance. Vanishing binomial scalars or zero states can shrink
support further. This predicate imposes no zero rule on individual raw e_i. -/
def LaurentAdmissible (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3)
    (i : LaurentIndex) : Prop :=
  i.2.1 ≤ i.1.2 ∧ ∀ c : Fin 3, 0 ≤ laurentInput k a e i c

/-- Exact exponent equations and derived finite bounds for the proposed
x<<y<<z expansion of the SAME full R. There is no auxiliary N in any bound. -/
theorem laurent_bounds (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3)
    (i : LaurentIndex) (hi : LaurentAdmissible k a e i) :
    0 ≤ e 0 + k ∧ 0 ≤ e 0 + e 1 + 3 * k ∧
    (i.1.1 : ℤ) + i.2.1 ≤ e 0 + k ∧
    (i.1.2 : ℤ) + i.2.2 ≤ e 0 + e 1 + 3 * k ∧
    laurentInput k a e i 0 + laurentInput k a e i 1 =
      e 0 + e 1 + 3 * k - i.1.2 - i.2.2 ∧
    laurentInput k a e i 1 ≤ e 0 + e 1 + 3 * k ∧
    laurentInput k a e i 2 ≤
      e 2 + a 0 + a 1 + a 2 + (e 0 + e 1 + 3 * k) := by
  have hq := hi.1
  have h0 := hi.2 0
  have h1 := hi.2 1
  have h2 := hi.2 2
  simp only [laurentInput, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
  omega

/-- A proved containing box filtered by the EXACT relevance equations.
This is not an assumed rectangular support condition on the raw channel. -/
def laurentFiber (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : Finset LaurentIndex := by
  classical
  exact (((Finset.range ((e 0 + k).toNat + 1)).product
      (Finset.range ((e 0 + e 1 + 3 * k).toNat + 1))).product
    ((Finset.range ((e 0 + k).toNat + 1)).product
      (Finset.range ((e 0 + e 1 + 3 * k).toNat + 1)))).filter
        (LaurentAdmissible k a e)

/-- Every and only structurally relevant inverse index is in this finite set. -/
theorem mem_laurentFiber_iff (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3)
    (i : LaurentIndex) : i ∈ laurentFiber k a e ↔ LaurentAdmissible k a e i := by
  classical
  unfold laurentFiber
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    rcases laurent_bounds k a e i hi with ⟨hE, hF, hjh, hql, hsum, hm, hz⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩⟩, hi⟩ <;> omega

/-- The exact scalar from (1+x/y)^(-k), (1+(x+y)/z)^(-a0),
and (1+y/z)^(-a1), including the finite splitting h<=q. No extra signs. -/
def laurentWeight (k : ℕ) (a : Fin 3 → ℕ) (i : LaurentIndex) : ℂ :=
  integerBinomial (-(k : ℤ)) i.1.1 *
    integerBinomial (-(a 0 : ℤ)) i.1.2 *
      (i.1.2.choose i.2.1 : ℂ) * integerBinomial (-(a 1 : ℤ)) i.2.2

/-- This is the explicit inverse-factor coefficient expression. Its R-action
law and its identification with the left-nested canonical channel are separate
obligations; neither is a definitional consequence of this expression. -/
def laurentTerm {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ)
    (e : Exponent 3) (i : LaurentIndex) : R :=
  if i.2.1 ≤ i.1.2 then
    laurentWeight k a i • signedExtend P (laurentInput k a e i)
  else 0

/-- No support hypothesis is imposed on P. In particular P can be infinite. -/
private theorem laurentTerm_support {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ)
    (e : Exponent 3) :
    Function.support (laurentTerm P k a e) ⊆ (laurentFiber k a e : Set LaurentIndex) := by
  classical
  intro i hi
  apply (mem_laurentFiber_iff k a e i).2
  by_cases hq : i.2.1 ≤ i.1.2
  · refine ⟨hq, ?_⟩
    by_contra hn
    apply hi
    simp only [laurentTerm, if_pos hq, signedExtend, if_neg hn, smul_zero]
  · exact False.elim (hi (by simp [laurentTerm, hq]))

/-- Explicit x<<y<<z inverse-factor coefficient, before any K identification. -/
def laurentCoefficient {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : R :=
  ∑ᶠ i : LaurentIndex, laurentTerm P k a e i

/-- The full inverse-factor coefficient is a literal finite sum on this fiber. -/
theorem laurentCoefficient_eq_sum {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    laurentCoefficient P k a e =
      ∑ i ∈ laurentFiber k a e,
        laurentWeight k a i • signedExtend P (laurentInput k a e i) := by
  classical
  rw [laurentCoefficient, finsum_eq_sum_of_support_subset _ (laurentTerm_support P k a e)]
  apply Finset.sum_congr rfl
  intro i hi
  exact if_pos ((mem_laurentFiber_iff k a e i).1 hi).1

/-- Actual necessary cone bounds. A negative individual e_i need not vanish. -/
theorem laurentCoefficient_zero {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3)
    (outside : e 0 + k < 0 ∨ e 0 + e 1 + 3 * k < 0 ∨
      e 2 + a 0 + a 1 + a 2 + (e 0 + e 1 + 3 * k) < 0) :
    laurentCoefficient P k a e = 0 := by
  rw [laurentCoefficient_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have ha := (mem_laurentFiber_iff k a e i).1 hi
  rcases laurent_bounds k a e i ha with ⟨hE, hF, hjh, hql, hsum, hm, hz⟩
  have h2 := ha.2 2
  rcases outside with h | h | h <;> omega

end
end D5.S3.VertexAlgebra.ThreeFieldFinalLaurentFiber
