import GRH.Lib.ClassField.HeckeL.EulerProduct
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Modulus of an idele: multiplicativity, continuity, product formula, invariance under
conjugation. -/

open MonoidHom NumberField FinitePlace

variable {E} [Field E] [NumberField E] {x : (𝔸 E)ˣ}

/-- The module of an idele: the homomorphism x ↦ |x| (the adelic absolute value if E is totally
complex) from the idele group of E to the multiplicative monoid ℝ. -/
noncomputable def ideleAbs : (𝔸 E)ˣ →* ℝ :=
  ⟨⟨fun x ↦ (∏ w, ‖x.1.1 w‖ ^ 2) * ∏ᶠ w, ‖x.1.2 w‖, by simp⟩,
  fun x y ↦ have h (z : (𝔸 E)ˣ) t := (finite_idele_val_ne_one (z.map (snd ..))).subset (t := t)
  by simp +contextual [sq, norm_def, not_imp_not, field, finprod_mul_distrib (h x _ _) (h y _ _)]⟩

@[simp] lemma ideleAbs_nonneg_and_ne_zero : 0 ≤ ideleAbs x ∧ ideleAbs x ≠ 0 :=
    ⟨mul_nonneg (by positivity) (finprod_nonneg (by simp)), (toHomUnits _ x).ne_zero⟩

@[simp] lemma ideleAbs_pos : 0 < ideleAbs x := by simp [lt_of_le_of_ne']

lemma ideleAbs_eq_prod_of_v_eq_one : (∀ w, Valued.v (x.1.2 w) = 1) → ideleAbs x =
  ∏ w, ‖x.1.1 w‖ ^ 2 := by simp_all [ideleAbs, norm_def]

@[fun_prop] lemma continuous_ideleAbs : Continuous (@ideleAbs E _ _) :=
  continuous_of_continuousAt_one _ (.congr (by fun_prop)
  (.mono (((continuous_snd.units_map (snd ..)).1 _ (isOpen_idelesUnitOff ∅)).mem_nhds
  (by simp)) fun _ _ ↦ (ideleAbs_eq_prod_of_v_eq_one (by aesop)).symm))

/-- The product formula: for a totally complex number field E and x in E^×, the principal idele of x
has module `ideleAbs` equal to 1. -/
lemma ideleAbs_toAdele [IsTotallyComplex E] [PlaceEmbedding E] (x : Eˣ) : @ideleAbs E _ _
  (x.map (toAdele (E := E))) = 1 := by simpa [← finprod_comp_equiv equivHeightOneSpectrum.symm,
  ideleAbs, ← InfinitePlace.apply] using! prod_abs_eq_one x.ne_zero

@[simp] lemma ideleAbs_star [IsCMField E] : ideleAbs (star x) = ideleAbs x :=
    congr($(by simp) * $(finprod_eq_of_bijective _ star_involutive.bijective (by simp [norm_def])))

lemma ideleAbs_eq_one_of_mem_unitary [IsCMField E] (h : x.1 ∈ unitary _) : ideleAbs x = 1 := by
  simpa using congr(√(ideleAbs $((Units.unitary_eq.ge h).1)))
