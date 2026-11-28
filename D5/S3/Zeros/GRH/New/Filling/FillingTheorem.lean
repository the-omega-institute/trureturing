/- GID: D5/S3/Zeros/GRH/New/Filling/FillingTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/FillingTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.FillingTheorem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FillingTheorem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.Moments
import D5.S3.Zeros.GRH.New.Seesaw.UnfoldingStages
import D5.S3.Zeros.GRH.New.Filling.RowDimension
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Translates of the columns fill the rows. For every subspace F of the rows, some level translate of the projected Poincaré series keeps, modulo F, ramified columns of dimension at least nearly ½(1 − dim F/dim rows) times that of all columns, so rows exist and few translates span almost all rows, which gives the basis for the Gram determinant. Spanning by Poincaré series and the link between least second moment and tight frames are known. Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen, 1932; Benedetto–Fickus, Finite normalized tight frames, 2003; Muić, Compactly supported Poincaré series and existence of cusp forms, 2010. -/

open Filling Module Submodule

variable {P} (D : Data P) (c : ℂˣ)

/-- The Poincaré series 𝒫 as a linear map from columns on X₀ to forms of parameter ς and level g
on Y₀, chosen to realise `Filling.Fits.poincare`. -/
noncomputable def Data.poincare : D.Column →ₗ[ℂ] D.principalForms (D.spaceY 0) :=
  D.filling_fits.poincareMap.1 ∘ₗ D.columnCoords

/-- Filling theorem: for c ≠ 0 and each space F of rows, with φ = dim F / dim(rows), some s in the
finite level group 𝖦 = `Data.G` (e₀ = `Data.e₀` projects to rows) has dim
(|𝖦|e₀s𝒫cE)⁻¹F ≤ ((1 + φ)/2 + b⁻²) dim Col. Here 𝒫 is the Poincaré series and E = `Data.ramifyingOp`
univ maps columns onto ramified columns.

Translates of the columns fill the rows. -/
lemma Data.ramifiedColumns_fill_rows :
  IsSpread (D.goodProjTranslate · ∘ₗ D.poincare ∘ₗ (c.1 • D.ramifyingOp .univ)) (D.b ^ 2)⁻¹ := by
  have := D.hasLogLower_of_le (le_sub_iff_add_le.2 D.le_of_hasLogBound : D.b ^ 9 ≤ D.N - 1)
  have h := Fits.exists_translate_finrank_comap_le (ρ :=
    .comp (D.principalRep _) (.mk' _ (by tauto))) (fun _ _ _ ↦ Space.inner_formRep ..) (fun _ ↦
    (D.filling_fits.petersson_poincare · · (@reduceFamily_liftResidue ..))) (fun _ ↦
    isCentralProj_sum_tupleIdem) (fun i ↦ (bad_share_le (M := P.Mω D.s) (q := D.g i) _ (9 * D.logB)
    (card_resField_eq_levelPrime _ i) rfl (card_chosenPlaces _ i) D.nat_lt_of_hasLogBound
    D.nat_lt_of_hasLogBound D.le_of_hasLogBound le_rfl D.le_of_hasLogBound).trans
    (filling.eq_1 D ▸ D.le_of_hasLogBound)) (measureReal_pos_of_isLevel (K := D.chosenLevel))
  erw [(?_ : Representation.asAlgebraHom _ _ = (principalRep ..).asAlgebraHom D.e₀), Shape.r,
    card_rowIndex, ← Nat.card_congr (.piCurry _)] at h
  simp_rw [IsSpread, ← D.columnCoords.finrank_eq, ← (D.columnCoords.ofSubmodule' _).finrank_eq] at h
  refine fun F ↦ (h D.finrank_rows_le_mass F).imp' Sigma.uncurry fun _ h ↦
    .trans (mod_cast finrank_mono fun _ ↦ by simpa using!
    id) (((D.ramifyingOp_finrank_comap_and_short .univ _).1.trans (add_le_add h le_rfl)).trans ?_)
  simp [← add_mul, add_assoc, card_piPlaces, filling]; gcongr; use D.le_of_hasLogBound
  open Fint in simp_rw [asAlgebraHom_eq_sum, reindex_equiv (Equiv.piCurry _)]
  simp [e₀, goodTupleFamilies, tupleIdem, Finset.prod_univ_sum, Fintype.prod_sigma]; rfl

/-- For admissible data D, the space of rows has nonzero finite dimension over ℂ.

Translates of the columns fill the rows. -/
lemma Data.finrank_rows_ne_zero : finrank ℂ D.rows ≠ 0 := fun e ↦ (D.ramifiedColumns_fill_rows 1
  ⊤).rec fun _ ↦ by erw [finrank_top, e]; norm_num [finrank_pos_iff.2 D.columnCoords.nontrivial,
  ← lt_tsub_iff_left]; use D.lt_of_hasLogBound
