import GRH.Lib.ClassField.Global.CMNorms
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Algebraic Hecke characters (type A₀) and the extension of the quadratic character
of a CM field. The result is stated here for tamely ramified characters of the norm-one torus of a
CM field. The extension of the quadratic character is everywhere unramified of weight one, which
holds for the fields used here and not in general. Source: A. Weil, On a certain type of characters
of the idèle-class group of an algebraic number-field, Tokyo–Nikko symposium 1955 (1956); exposition
A. Raghuram, Notes on the arithmetic of Hecke L-functions, arXiv:2207.03399, §4.

This file: Existence of an unramified splitting Hecke character of a CM field. -/

open NumberField Units Finset Complex ComplexOrder Embeddings Circle Function Submonoid

/-- Let the CM field E be stably unramified (`StablyUnram`), and let every root of unity of E be
δ/δ̄ for some unit δ with ∏_w Φ_w(δ) = 1. Then E has a splitting character (`SplittingChar`).

Known result: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field. -/
lemma nonempty_splittingChar {E : Type} [Field E] [CMType E] [StablyUnram E] (hE : ∀ y, IsOfFinOrder
  y → ∃ δ : (𝓞 E)ˣ, ∏ w, Φ w (δ : E) = 1 ∧ y * star (δ : E) = δ) : Nonempty (SplittingChar E) := by
  have (x : (𝔸 E)ˣ) v := left_ne_zero_of_mul_eq_one congr($(x.3).1 v)
  let S : (𝔸 E)ˣ →ₜ* Circle := ⟨.mk' (fun x ↦ ⟨∏ w, x.1.1 w / ‖x.1.1 w‖, by simp_all [unitSphere,
    prod_eq_zero_iff]⟩) (by aesop (add simp mul_div_mul_comm)), by fun_prop (disch := aesop)⟩
  obtain ⟨χ, k, H⟩ := exists_monoidHom_extend (C := Circle) (d :=
    Surjective.divisibleBy _ exp_surjective exp_zsmul) ((idelesUnitOff ∅).comap
    (map (.snd ..))).subtype (S.domRestrict _) ((Units.map toAdele.1).coprod
    (.id _ * starMulAut.toMonoidHom)).range fun ⟨_, g⟩ e ↦ ext (show univ.prod _ = _ by
    obtain ⟨⟨⟨y, b⟩, rfl⟩, h⟩ := e, mem_idelesUnitOff.1 g
    obtain ⟨δ, _, e⟩ := hE (star y / y) (isOfFinOrder_iff_pow_eq_one.2 (bex_def.1
      (pow_eq_one_of_norm_eq_one E ℂ (algebraMap_mem_Ô.1 (mem_Ô.2 fun w ↦ by
      have := v_star_apply _ w ▸ h (star w) id; simp_all; grind [div_self_le_one])) (by simp))))
    let a := y * δ.map (algebraMap ..).1; have : star a.1 = a := by simp_all [a, field]
    obtain ⟨x, _⟩ := exists_norm_eq_Ô (u := (toAdele a.1 * (b * star b)).2) (by simp [*, mul_comm])
      fun w ↦ by simpa [a, w.valuation_eq_one_iff_notMem.2, w.1.notMem_of_isUnit] using h w
    have := norm_of_nonneg'
      (exists_eq_principalIdele_mul_norm.2.1 a (b.map (.snd ..) / x.map (Ô _).subtype.1) ‹_› (by
      rwa [star_div, div_mul_div_comm, mul_div, div_eq_one, Units.ext_iff, eq_comm, mul_comm])).le
    simp_all [prod_eq_zero_iff, a, mul_conj'])
  exact ⟨⟨⟨_,
    continuous_of_continuousAt_one χ (((isOpen_idelesUnitOff ∅).preimage (continuous_snd.units_map
    _)).continuousOn_iff.1 (S.2.continuousOn.congr (H ⟨·, ·⟩)) (by simp))⟩, fun x ⟨y, h⟩ ↦ k
    ⟨⟨.mk0 y (by grind [ne_zero]), 1⟩, by aesop⟩⟩, (congr($(H ⟨·, coe_idelesUnitOff_empty.ge ·⟩))),
    (eq_inv_of_mul_eq_one_right <| by simpa using! k ⟨⟨1, ·⟩, rfl⟩)⟩
