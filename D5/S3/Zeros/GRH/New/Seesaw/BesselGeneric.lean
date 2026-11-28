/- GID: D5/S3/Zeros/GRH/New/Seesaw/BesselGeneric
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/BesselGeneric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.BesselGeneric. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/BesselGeneric.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.FillingData
import D5.S3.Zeros.GRH.New.Seesaw.GoodDatumExists
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Names for column coordinates and projection to rows on the data. Transformation law,
support and normal form of the Bessel seed of the Poincaré series. -/
seal Finset.univ Finset.sum Finset.prod

variable {P} (D : Data P) {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} {ε l kw V Y η}
  [Frame 𝔰 ε] (h : S.Fits V l kw Y η)

/-- The filling data of D fit the space Y₀ with its lattice, in the sense of `Filling.Fits`. -/
lemma Data.filling_fits : D.filling.Fits _ D.paramW D.κ (D.gradingY 0) (scalarFin _
  (D.latticeScale 0))⁻¹ := ⟨(D.exists_besselSystem · |>.choose_spec), rfl, D.isCuspKernel_paramW.1,
  ((D.exists_spaceY 0).choose_spec.2 D.nat_le_of_hasLogBound).2.imp fun _ ⟨b, e⟩ ↦ ⟨(b ⟨·, ·⟩),
  Unitary.toUnits (D.latticeScale 0),
  Units.ext (e ▸ congrArg (· * _) (show gradedLatticeBasis D.shape.besselIndexEquiv _ _ _ = _ by
  rw [Units.val_mul, Units.val_smul, val_toBesselH_apply_coe, ← map_inv]
  simp [← Matrix.ext_iff, Shape.besselIndexEquiv, filling, gradedLatticeBasis, besselLatticeBasis,
    Matrix.diagonal_apply, Units.smul_def, scalarFin, ← Unitary.star_eq_inv]
  and_intros <;> grind [Unitary.mem_iff]))⟩, (commute_scalarFin · |>.inv_left)⟩

/-- The isomorphism that translates a column on X₀ by the central element `Data.latticeScale` 0,
then takes its values at the class representatives in the coordinates of
`Filling.Fits.columnCoords`. -/
noncomputable def Data.columnCoords :=
  .ofBijective _ (D.centralRep.apply_bijective (D.latticeScale 0)) ≪≫ₗ D.filling_fits.columnCoords

/-- For s in 𝖦, the linear map y ↦ |𝖦|·e₀(sy) from the forms `Data.principalForms` on Y₀ to the
image of the good idempotent e₀. -/
noncomputable abbrev Data.goodProjTranslate s := (Nat.card D.G : ℂ) •
    ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict ∘ₗ D.principalRep _ s

attribute [local simp] Filling.Fits.adelicEquiv_ratEquiv Filling.Fits.finiteEquiv_inclX mul_assoc
  conjWeylRep

/-- The Poincaré series of φ over a subgroup Δ is left Δ-invariant: it takes the same value at
γg and at g for every γ in Δ. -/
lemma Filling.Fits.poincare_rat_mul φ {Δ} γ (o : γ ∈ Δ) g : h.poincare φ Δ (γ * g) =
  h.poincare φ Δ g := congr(∑ _, _ * $(.trans (by simp) ((Equiv.mulRight ⟨γ, o⟩).tsum_eq _)))

/-- If 𝖶_φ, the Poincaré series over the rational points of the Bessel subgroup of Y, is nonzero
at g, some finite adelic element of that subgroup moves g_f into the principal level
`Filling.stdPrincipalLevel`. -/
lemma Filling.Fits.exists_besselFin_mul_mem_of_ne_zero φ {g} (hg : h.poincare φ Y.ratBessel g ≠ 0) :
  ∃ r ∈ Y.besselFin, r * g.2 ∈ S.stdPrincipalLevel := by
  by_contra!; have (γ : Y.ratBessel) a :=
    this _ (Y.snd_mem_besselFin (mul_mem (Y.inclX_mem_besselGroup (a⁻¹ * η)) γ.2.2))
  simp_all [poincare, cutBessel, h.mem_stdPrincipalLevel_iff, -Subtype.forall]

variable [WeilData E]

/-- For a column ψ of level Kc, n unipotent, a in U(X₀)(𝔸) and x_f in `Filling.stdPrincipalLevel`,
the Poincaré series of ψ over `Grading.ratBessel` at nax is χ(n)·A(a_∞⁻¹ψ(a_f η))·W(x_∞) (dot
product), with χ(n) = `stdAddChar`(−σ(n)/(gϖ)), σ = `simpleRootSum`, A =
`Filling.Fits.weylBesselEquiv`. -/
lemma Filling.Fits.poincare_bessel_normal_form ψ [S.IsAdmissible] {n} (hn :
  n ∈ Y.unipotent) a {x} (hx : x.2 ∈ S.stdPrincipalLevel) :
  h.poincare (h.columnCoords ψ) Y.ratBessel (n * (Y.inclX a * x)) = stdAddChar E
  (toAdele (-(S.g * S.ϖ : E)⁻¹) * simpleRootSum (h.adelicEquiv n)) * h.weylBesselEquiv.1
  (conjWeylRep _ 0 a.1⁻¹ (ψ.1.1 (a.2 * η))) ⬝ᵥ S.besselFn (h.realHomeo x.1) := by
  have A {g} o : S.adelicToFin (h.adelicEquiv g) ∈ besselU :=
    toLatBasis_mem_besselU.2 ((h.mem_unipotent_iff.1.1 o).map_mem_unitriangularOn _)
  obtain ⟨⟨d : S.Classes, γ, k, e⟩, u, hu, l⟩ := exists_eq_map_mul_rep_mul stdEmbFin S.columnLevel
    (·.out_eq) (a.2 * η), exists_besselU_approx (A hn) (S.inclHFin (a.2 * η))
  have U u (o : u ∈ besselU) :=
    h.mem_unipotent_iff.1.2 ((h.adelicEquiv_ratEquiv u).substr (o.map_mem_unitriangularOn _))
  have Q g (k : (S.h d)⁻¹ * (S.inclHFin η * h.finiteEquiv g.2) ∈ S.principalLevel) :
      h.poincare (h.columnCoords ψ) Y.ratBessel g =
    h.weylBesselEquiv.1 (ψ.1.1 d.out) ⬝ᵥ S.besselFn (h.realHomeo g.1) := by
    have key γ w {c i} (o : h.cutBessel (c, i) (γ * g) ≠ 0) : c = d ∧ ∃ u : S.classUnip c,
      Subtype.mk _
      (Subgroup.mem_inf.2 ⟨(h.ratEquiv u).2, Y.unipotent_le_besselGroup (U u u.2.1)⟩) = ⟨γ, w⟩ := by
      obtain ⟨σ, e⟩ := h.ratEquiv.surjective ⟨γ, w.1⟩; obtain rfl := congr($e.1)
      simp [cutBessel_ratEquiv_mul] at o; exact .imp_right (⟨⟨_, ·⟩,
        rfl⟩) (eq_and_mem_classUnip_of_besselS (toAdele.injective <| by
        simpa using! h.mem_unipotent_iff.2.1 w.2 · · ·)
        (by simpa [termPosition] using mul_mem o.1 (inv_mem k)))
    rw [poincare, Fintype.sum_prod_type,
      Fintype.sum_eq_single d (by simp +contextual [Not.imp_symm (key _ _)]), dotProduct]; congr! 2
    rw [← Function.Injective.tsum_eq (by simp [Function.Injective]) (key _ ·.2 · |>.2),
      tsum_cutBessel_classUnip (d, _), ite_eq_left k]
  obtain ⟨r, _⟩ := U _ (inv_mem hu), levelSpace_smoothFormRep_apply ψ.2 γ d.out k
  rw [← poincare_rat_mul (o := Subgroup.mem_inf.2 ⟨(h.ratEquiv _).2, Y.unipotent_le_besselGroup r⟩),
    ← mul_assoc, ← poincare_rat_mul (o := Y.inclX_mem_ratBessel ⟨γ⁻¹, rfl⟩), Q]
  simp only [realHomeo_mul, adelicToInf_inclX, h.weylBesselEquiv.2, besselFn_adelicToInf_mul
    (h.mem_unipotent_iff.1.1 (mul_mem r hn)), dotProduct_smul, ← coe_map_conj_inv_eq_transpose]
  rw [unipotentChar_eq_of_mem_principalLevel (one_mem _) (A (mul_mem r hn)) (a.2 * η)
    (by simpa using! inv_mem l), map_mul h.adelicEquiv, simpleRootSum_mul] <;> simp_all [mul_add,
    AddChar.map_add_eq_mul, Space.weightRep, weylRep, ←
    map_mul, -map_neg, -map_inv, (stdSpace ..).ratEmbed.map_inv, h.mem_unipotent_iff]
  simpa [↓finiteEquiv_eq_adelicToFin, adelicToFin_adelicEquiv_inclX, eq_mul_inv_of_mul_eq e] using!
    mul_mem (IsAdmissible.columnLevel_eq.le k.2).out (mul_mem
    (inv_mem l) (h.mem_stdPrincipalLevel_iff.1 hx))

/-- Under `Filling.IsAdmissible`, if jc = −(gϖ)⁻¹ (j = `WeilData.j`, c the scale of the grading),
the
Poincaré series over the rational Bessel subgroup of an algebraic form ψ of level Kc
satisfies the hypotheses `Grading.IsGeneric` of the unfolding step on Y. -/
lemma Filling.Fits.isGeneric_poincare ψ [S.IsAdmissible] (hjc : WeilData.j * Y.c = -(S.g * S.ϖ :
  E)⁻¹) : Y.IsGeneric (h.poincare (h.columnCoords ψ) Y.ratBessel) := by
  choose F L C using fun g ↦ (by_contra fun H ↦ H ⟨0, fun u y k ↦ .trans (by_contra fun e ↦ H
    ((h.exists_besselFin_mul_mem_of_ne_zero _ e).elim fun r ⟨hr, l⟩ ↦
    (Y.exists_unipotent_mul_inclX (inv_mem (mul_mem hr (Y.unipotent_le_besselGroup u.2)))).elim
    fun m ⟨_, a, d⟩ ↦ ⟨_, fun n x i ↦ by
    nth_rw 1 [← inv_mul_cancel_left _ x, d, mul_assoc, ← mul_assoc, poincare_bessel_normal_form,
      map_mul h.adelicEquiv, simpleRootSum_mul, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul,
      mul_assoc] <;> simp [*, mul_mem, ← h.mem_unipotent_iff.1]
    simpa using mul_mem l (mul_mem (inv_mem k) i), by fun_prop⟩)) (by simp), by fun_prop⟩ :
    ∃ F, (∀ (n : Y.unipotent) x,
    (g⁻¹ * x).2 ∈ S.stdPrincipalLevel → h.poincare (h.columnCoords ψ) _ (n * x) =
    stdAddChar E (_ * simpleRootSum (h.adelicEquiv n)) * F x) ∧ Continuous F)
  have K g x := by simpa [simpleRootSum_eq_zero_of_mem_besselH] using L g 1 x
  use continuous_of_cover_nhds (⟨·, S.stdPrincipalLevel.2.preimage_of_continuous.mem_nhds
    (by simp)⟩) (C · |>.continuousOn.congr (K _)), h.poincare_rat_mul _, fun g n hn _ ↦ ?_
  erw [L g ⟨n, hn⟩, K g, (?_ : Y.shift = toAdele Y.c.1 • besselCharMatrix _), smul_mul_assoc,
    Matrix.trace_smul, trace_besselCharMatrix_mul (h.adelicEquiv n), simpleRootSum_inv,
    ← stdAddChar_half (E := E), ← hjc] <;>
    simp [h.mem_unipotent_iff.1.1 hn, Y.c.2, div_eq_inv_mul, mul_add]
  rcases 𝔰 with ⟨_ | _⟩ <;> simp [Grading.shift, besselCharMatrix, ← Matrix.ext_iff, h.index_eq,
    Shape.besselIndexEquiv, splitGram, middleGram, besselFrame,
    Fin.forall_fin_succ', ← Fin.castSucc_succ]; clear * -; grind (splits := 20) [map_natCast]
