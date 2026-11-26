import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdelicAbs
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.RationalPoints
import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.GeneralisedIndex
import OmegaMath.NumberTheory.GRH.Lib.Weil.DualPair.Kronecker
import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.InertResidue
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Haar modulus of ideles and adelic matrices is the adelic absolute value. -/

open LinearMap RingHom Subgroup Units Algebra Matrix MeasureTheory NumberField Valued WithZero
  MeasureTheory.Measure FinitePlace Valuation.IsRankOneDiscrete Valuation.IsUniformizer

variable {E n : Type*} [Field E] [NumberField E] [Fintype n] {w : FinPlace E} (a : GL n (𝔸 E))

lemma v_uniformizer_inv_mul_le_one_iff {y} : v ((uniformizer w).1⁻¹ * y) ≤ 1 ↔
  v y < 1 := by simp [← lt_mul_exp_iff_le]

lemma norm_locField_eq_q_zpow {x : LocField w} : x ≠ 0 → ‖x‖ = w.q ^ (v x).log := by
  simp_all [FinitePlace.norm_def, WithZeroMulInt.toNNReal, toAdd_unzero_eq_log]

lemma eq_norm_inv_of_uniformizer (χ : (LocField w)ˣ →* ℝ) (h : ∀ {x}, v x.1 = exp (-1) → χ x = w.q)
  {x} : χ x = ‖x.1‖⁻¹ := by simpa [norm_locField_eq_q_zpow, h (v_uniformizer w), field] using @h (x
  * uniformizer w ^ (v x.1).log * uniformizer w) (by simp [WithZero.exp_neg, -inv_exp])

lemma isValuationPair_Ohat : IsValuationPair (Ô E) := fun a b ↦ ⟨⟨_, idem_mem_Ô {w | v (a w) ≤
  v (b w)}⟩, by aesop (add simp [exists_eq_mul_iff_v_le, idem_apply, le_of_lt])⟩

instance [IsCMField E] : IsStarStable (Ô E) := ⟨star_mem_Ô⟩

/-- The module |x| of a finite idele x: the adelic absolute value of the idele with finite part
x and component 1 at infinity. -/
noncomputable def finIdeleAbs := (@ideleAbs E).comp finIdeleIncl

/-- The product formula, finite part: for x in E^×, the product of the normalised absolute
values |x|_w over the finite places is |N_{E/ℚ}(x)|⁻¹. -/
@[simp] lemma finIdeleAbs_principalIdele x : finIdeleAbs (principalIdele (x : Eˣ)) =
  |Algebra.norm ℚ x.1|⁻¹ := by simpa [finIdeleAbs, ideleAbs,
  ← (finprod_comp_equiv equivHeightOneSpectrum.symm)] using! prod_eq_inv_abs_norm x.ne_zero

@[simp] lemma finIdeleAbs_locIdele x : finIdeleAbs (locIdele w x) = ‖x.1‖ := by
    simp_all [finIdeleAbs, ideleAbs, finprod_eq_single _ w]

/-- For a finite idele a of a number field E, the inverse of the factor by which a scales
additive Haar measure on the finite adeles equals |a|⁻¹, where |a| = `finIdeleAbs` a is the
adelic absolute value. -/
lemma genIndex_eq_inv_finIdeleAbs (a : (𝔸f E)ˣ) : genIndex a.1 = (finIdeleAbs a)⁻¹ :=
  mem_of_locIdele_mem (H := (genIndex.1.comp (coeHom
  _)).eqLocus (invMonoidHom.comp _)) (isClosed_of_isOpen _ (isOpen_mono (fun _ _ ↦ .symm (by
  simp_all [Nat.card_unique, genIndex_eq_card isOpen_Ô isCompact_Ô, mem_Ô, finIdeleAbs,
  ideleAbs_eq_prod_of_v_eq_one])) (isOpen_idelesUnitOff ∅))) fun w ↦
  .trans (eq_norm_inv_of_uniformizer ((genIndex.1.comp _).comp _) (fun _ ↦ by
  erw [← card_ResField,
    ← Nat.card_congr (quotientKerEquivOfSurjective (funext (reduceAt_algebraMap w) ▸
    algebraMap_ResField_surjective w).of_comp).1, genIndex_eq_card isOpen_Ô isCompact_Ô (mem_Ô.2 _)]
  congr with
  all_goals simp_all +decide [Ideal.mem_span_singleton, Subtype.ext_iff, dvd_def, ← and_forall_ne w,
    exists_eq_mul_iff_v_le, mem_Ô.1, ← lt_mul_exp_iff_le, ← WithZero.exp_add])) (by simp)

lemma genIndex_eq_inv_norm (a : (LocField w)ˣ) : genIndex a.1 = ‖a.1‖⁻¹ :=
  eq_norm_inv_of_uniformizer (genIndex.1.comp (coeHom _))
  (by erw [genIndex_eq_card (isOpen_valuationSubring _) (isCompact_LocInt _), ← is_generator,
  card_ResField] <;> simp_all +decide [iff, generator_eq_exp_neg_one_of_mem_range ⟨_, ·⟩])

lemma map_mulVec_haar_finAdele μ [IsAddHaarMeasure μ] (a : GL n (𝔸f E)) :
    μ.map (a.1 *ᵥ ·) = ENNReal.ofReal (finIdeleAbs a.det)⁻¹ • μ :=
    (distribHaarChar_GL_eq_det isOpen_Ô isCompact_Ô isValuationPair_Ohat a).trans
  (genIndex_eq_inv_finIdeleAbs a.det) ▸ map_smul_eq_inv_distribHaarChar_smul a

/-- For a in GL_n of the adeles of E, the map x ↦ ax pushes the Haar measure on adelic n-vectors
forward to |det a|⁻¹ times itself, with the adelic absolute value. -/
lemma volume_map_mulVec_adele : volume.map (a.1 *ᵥ ·) = ENNReal.ofReal (ideleAbs a.det)⁻¹ •
  volume := map_haar_eq_smul_of_semiconj _ (.mk ⟨.arrowProdEquivProdArrow .., by tauto⟩)
  (congrFun (by ext : 3; exacts [Prod.fst_sum, Prod.snd_sum])) ((MeasurePreserving.prod
  ⟨(LinearMap.continuous_of_finiteDimensional _).measurable,
  map_linearMap_addHaar_eq_smul_addHaar addHaar ((a.map (.fst
  ..)).toLin.toLinearEquiv.restrictScalars _).isUnit_det'.ne_zero⟩ ⟨by fun_prop,
  map_mulVec_haar_finAdele
  volume (a.map (.snd ..))⟩).2.trans (by erw [det_restrictScalars, det_toLin', ← map_det,
  a.map_det, det_pi (mul ℝ ℂ ∘ _), funext (norm_complex_apply ∘' _)]; simp [ideleAbs, finIdeleAbs,
  ← Complex.sq_norm, prod_smul_left, prod_smul_right, mul_smul, finprod_nonneg, Finset.prod_pow]))
  ((LinearMap.continuous_of_finiteDimensional _).measurable.prodMap (by fun_prop))

@[simp] lemma det_star [IsCMField E] : (star a).det = star a.det := Units.ext (det_conjTranspose _)

/-- For a in GL_n(𝔸) and b in GL_1(𝔸), the map x ↦ axb on n×1 adelic matrices pushes the
standard measure forward to |det(b)^n det a|⁻¹ times itself, with |·| the module of an
idele. -/
lemma volume_map_mul_mul_adele (b : GL Unit (𝔸 E)) : volume.map (α := Matrix n Unit (𝔸 E))
  (a.1 * · * b.1) = ENNReal.ofReal (ideleAbs (b.det ^ Fintype.card n * a.det))⁻¹ • volume :=
  map_haar_eq_smul_of_semiconj _ (.mk ⟨.mk _ (· <| Prod.swap ⟨·, ·⟩), vec_add⟩) (.symm <|
  kronecker_mulVec_vec _ · _) ((volume_map_mulVec_adele (kroneckerGL ..)).trans
  (by simp [ideleAbs]; erw [det_kronecker']; simp))
