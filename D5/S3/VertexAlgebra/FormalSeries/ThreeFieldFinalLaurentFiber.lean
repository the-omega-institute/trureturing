/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite signed fibers for the three inverse-binomial factors. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedMiddleCollision
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
/-! proof_shape: content
admission_basis: escape-witness
escape_witness: signed exponent balance proves finite support of the inverse coefficient fiber.
The binomial factors retain the Mathlib suppliers and their attribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldFinalLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
open SupportedMiddleCollision SupportedChannelSeries
noncomputable section

private def swap12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

private theorem swap12_index (x y z : ℕ) :
    (index3 x z y).embDomain swap12.toEmbedding = index3 x y z := by
  simp [index3, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, swap12, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc]

private theorem swap12_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℤ) :
    signedExtend (MvPowerSeries.rename swap12 P) ![x, y, z] =
      signedExtend P ![x, z, y] := by
  classical
  have nn : (∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i) ↔
      (∀ i : Fin 3, 0 ≤ (![x, z, y] : Fin 3 → ℤ) i) := by
    constructor <;> intro h i <;> fin_cases i
    · exact h 0
    · exact h 2
    · exact h 1
    · exact h 0
    · exact h 2
    · exact h 1
  by_cases h : ∀ i : Fin 3, 0 ≤ (![x, y, z] : Fin 3 → ℤ) i
  · rw [signedExtend, if_pos h, signedExtend, if_pos (nn.mp h)]
    have idx (s b t : ℤ) : signedIndex (![s, b, t] : Fin 3 → ℤ) =
        index3 s.toNat b.toNat t.toNat := by
      ext i
      fin_cases i <;> simp [signedIndex, index3]
    rw [idx, idx, ← swap12_index x.toNat y.toNat z.toNat]
    exact MvPowerSeries.coeff_embDomain_rename swap12.toEmbedding P _
  · simp only [signedExtend, if_neg h, if_neg (fun h' => h (nn.mpr h'))]

/-- The final native shear s=x+y. The spectator z stays fixed. -/
def finalArguments (R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 1, MvPowerSeries.X 1, MvPowerSeries.X 2]

/-- Coordinates of the SAME original P after all three native shears. -/
def triangularArguments (R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2,
    MvPowerSeries.X 1 + MvPowerSeries.X 2, MvPowerSeries.X 2]

private theorem final_hasSubst (R : Type*) [CommRing R] :
    MvPowerSeries.HasSubst (finalArguments R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [finalArguments]

/-- This legal substitution acts on a generally infinite native series. -/
def finalCollision {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) : MvPowerSeries (Fin 3) R :=
  MvPowerSeries.subst (finalArguments R) P

private theorem final_as_swapped_outer {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) :
    finalCollision P = MvPowerSeries.rename swap12
      (MvPowerSeries.subst (outerArguments R) (MvPowerSeries.rename swap12 P)) := by
  let r : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X ∘ swap12
  have hr : MvPowerSeries.HasSubst r := MvPowerSeries.HasSubst.X_comp _
  have ho : MvPowerSeries.HasSubst (outerArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [outerArguments]
  have hc : MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.subst (outerArguments R) (r i)) := by
    simpa only [MvPowerSeries.substAlgHom_apply] using hr.comp ho
  rw [finalCollision, MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst]
  change _ = MvPowerSeries.subst r (MvPowerSeries.subst (outerArguments R)
    (MvPowerSeries.subst r P))
  rw [MvPowerSeries.subst_comp_subst_apply hr ho,
    MvPowerSeries.subst_comp_subst_apply hc hr]
  congr 1
  funext i
  simp only [r, Function.comp_apply, MvPowerSeries.subst_X ho]
  fin_cases i
  · change MvPowerSeries.X 0 + MvPowerSeries.X 1 =
      MvPowerSeries.subst r (MvPowerSeries.X 0 + MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_add hr, MvPowerSeries.subst_X hr, MvPowerSeries.subst_X hr]
    simp [r, swap12, Equiv.swap_apply_def]
  · change MvPowerSeries.X 1 = MvPowerSeries.subst r (MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap12]
  · change MvPowerSeries.X 2 = MvPowerSeries.subst r (MvPowerSeries.X 1)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap12]

/-- Reassociation of legal substitutions keeps the original P unchanged. -/
theorem final_middle_substitution {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) :
    finalCollision (MvPowerSeries.subst (middleArguments R) P) =
      MvPowerSeries.subst (triangularArguments R) P := by
  have hm : MvPowerSeries.HasSubst (middleArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [middleArguments]
  rw [finalCollision, MvPowerSeries.subst_comp_subst_apply hm (final_hasSubst R)]
  congr 1
  funext i
  fin_cases i
  · change MvPowerSeries.subst (finalArguments R) (MvPowerSeries.X 0 + MvPowerSeries.X 2) = _
    rw [MvPowerSeries.subst_add (final_hasSubst R), MvPowerSeries.subst_X (final_hasSubst R),
      MvPowerSeries.subst_X (final_hasSubst R)]
    rfl
  · change MvPowerSeries.subst (finalArguments R) (MvPowerSeries.X 1 + MvPowerSeries.X 2) = _
    rw [MvPowerSeries.subst_add (final_hasSubst R), MvPowerSeries.subst_X (final_hasSubst R),
      MvPowerSeries.subst_X (final_hasSubst R)]
    rfl
  · change MvPowerSeries.subst (finalArguments R) (MvPowerSeries.X 2) = _
    rw [MvPowerSeries.subst_X (final_hasSubst R)]
    rfl

private theorem signed_nat {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℕ) :
    signedExtend P ![(x : ℤ), (y : ℤ), (z : ℤ)] =
      MvPowerSeries.coeff (index3 x y z) P := by
  have hn : ∀ i : Fin 3, 0 ≤ (![(x : ℤ), (y : ℤ), (z : ℤ)] : Fin 3 → ℤ) i := by
    intro i
    fin_cases i <;> simp
  rw [signedExtend, if_pos hn]
  congr 1
  ext i
  fin_cases i <;> simp [signedIndex, index3]

/-- Exact scalar and index formula. Only 0<=b<=y occurs in the native shear. -/
theorem finalCollision_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (x y z : ℕ) :
    MvPowerSeries.coeff (index3 x y z) (finalCollision P) =
      ∑ d ∈ Finset.range (y + 1), ((x + d).choose x : ℂ) •
        MvPowerSeries.coeff (index3 (x + d) (y - d) z) P := by
  classical
  rw [← signed_nat, final_as_swapped_outer, swap12_signed, outerCollision_signed]
  rw [extend, if_pos (by constructor <;> positivity),
    Int.toNat_natCast, Int.toNat_natCast, collision_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg (fun v : R => ((x + d).choose x : ℂ) • v)
  have hs := middleNativeSlice_extend (MvPowerSeries.rename swap12 P)
    (z : ℤ) ((x + d : ℕ) : ℤ) ((y - d : ℕ) : ℤ)
  rw [extend, if_pos (by constructor <;> positivity),
    Int.toNat_natCast, Int.toNat_natCast, swap12_signed, signed_nat] at hs
  exact hs


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
