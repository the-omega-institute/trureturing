/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/NormalGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ThetaNormality.NormalGeneration. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ThetaNormality/NormalGeneration.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.ReducedClosure
import D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction.ThetaOrthogonality
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Normal generation of sections on abelian varieties, kept under good reduction (known
result; see Lib.Shimura.ThetaNormality.RiemannRelation).

This file: Every point is centre of a rank-one valuation at a dense complex point. Finite products
of proper schemes over a base are proper. Sup-norm balls of theta functions: powers of balls are
balls, rank of reduction. -/

open Ideal IsLocalRing AlgebraicGeometry CategoryTheory CommRingCat IsIntegrallyClosed Module
  MvPolynomial NNReal Set Valuation ValuativeRel Scheme AlgebraicGeometry.Spec
  IsLocalization.AtPrime

set_option synthInstance.maxHeartbeats 200000 in
/-- Let S be a locally Noetherian scheme, with finitely many complex points η_i of dense image.
Every point s of S is the image of the closed point under some Spec V → S extending an η_i, V the
ring of a real-valued valuation on ℂ. -/
lemma exists_arc {S ι} [IsLocallyNoetherian S] [Finite ι] η (hη :
  @IsDenseFamily ι S η) s : ∃ᵉ (i) (v : Valuation ℂ NNReal) (a),
  specMap v.valuationSubring.subtype ≫ a = η i ∧ a (closedPoint _) = s := by
  obtain ⟨i, h⟩ := by simpa [← iUnion_singleton_eq_range, ← specializes_iff_mem_closure] using hη s
  let O := S.presheaf.stalk s
  obtain ⟨⟨W, hW, hl⟩, r, hr⟩ := exists_factor_valuationRing (S.presheaf.stalkSpecializes h ≫
    stalkClosedPointTo _).hom, (maximalIdeal O).fg_of_isNoetherianRing
  let := (RingHom.codRestrict _ W hW).toAlgebra
  choose x k hk using ((Std.Total.mk fun a b ↦ ValuationRing.dvd_total b a).directed
    (this.2 ·.1)).finite_le (inclusion (hr ▸ subset_span))
  let A := (aeval (R := O) k).range
  obtain ⟨⟨⟨p, ⟨_, h₁⟩, h₂⟩⟩, t, ht⟩ := nonempty_minimalPrimes (span_singleton_ne_top
    (x := algebraMap O A x) (x.2 ∘ hl.1 _ ∘ .map A.val)), exists_isTranscendenceBasis A ℂ
  have P {σ} : (p.map (@C A σ _)).IsPrime := p.mk_ker ▸ ker_map (Ideal.Quotient.mk p) ▸ .comap _
  let e : _ ≃+* (Algebra.adjoin ..).toSubring := ht.1.aevalEquiv.toRingEquiv
  obtain ⟨U, hU, hl⟩ := (LocalSubring.ofPrime _ ((p.map C).map e)).exists_le_valuationSubring
  let f : _ →+* U := Subring.inclusion ((LocalSubring.le_ofPrime ..).trans hU)
  have H : (maximalIdeal U).comap f = (p.map C).map e :=
    congr(under _ $(maximalIdeal_comap (Subring.inclusion hU))).trans LiesOver.over.symm
  have ⟨q, h₄@⟨⟨_, h₃⟩, _⟩, _⟩ := exists_minimalPrimes_le (H ▸ map_comap_le)
  simp [map_le_iff_le_comap] at h₃
  let V := U.ofPrime q
  let := ofValuation V.valuation
  let := (algebraMap _ V).comp f
  refine have ⟨g, k⟩ := (@isRankLeOne_iff_mulArchimedean ℂ).2 ⟨valuation_surjective.forall₂.2 ?_⟩
    ⟨i, .map ⟨g, k.monotone⟩ (valuation ℂ), ((isEquiv_iff_valuationSubring ..).1
    (isEquiv_map_self_of_strictMono ⟨g, k.monotone⟩ k.injective · · |>.trans
      (valuation ℂ).vle_iff_le.symm)).trans
    V.valuationSubring_valuation ▸ ⟨specMap (this.comp (e.toRingHom.comp (algebraMap O _))) ≫
    fromSpecStalk .., map_comp_assoc .. ▸ congr(Spec.map (ofHom $(RingHom.ext ((aeval_C ..).trans <|
    W.coe_mk _ <| hW ·))) ≫ _).trans (by simp [Spec_stalkClosedPointTo_fromSpecStalk _]), (congrArg
    _ (top_unique (α := PrimeSpectrum _) (hr.ge.trans (span_le.2 fun y hy ↦ (under_maximalIdeal _
    q).ge (h₃ (h₁ (mem_span_singleton.2 ⟨⟨_, _, aeval_X ..⟩, Subtype.ext (hk ⟨y, hy⟩)⟩))))))).trans
    fromSpecStalk_closedPoint⟩⟩
  simp_intro z y h [← one_vlt_iff]
  exact Exists₂.imp (by have := h.ne_zero; simp [V.smul_def, field]) ((radical_eq_sInf
    ((Algebra.linearMap ..).range.comap (.smulRight .id z))).ge (mem_sInf.2 fun J ⟨j, hJ⟩ ↦
    hJ.radical_le_iff.2
    ((e.surjective.exists.1 (ht.isAlgebraic.1 z).exists_integral_multiple).elim fun w ⟨h0, d⟩ ↦ by
    obtain ⟨n, u, hu, w, rfl⟩ := w.exists_fin_rename
    simpa [↓map_le_iff_le_comap, LE.le] using! ((((J.comap this).comap e).comap (rename
      u)).eq_of_le_of_height_le (fun a m ↦ mem_map_C_iff.2 (coeff_rename_mapDomain u hu a · ▸
      mem_map_C_iff.1 (by simpa using H.le (le_maximalIdeal (hJ.under U).1 m)) _))
      ((height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ ⟨⟨P, map_mono h₁⟩, fun _ ⟨_, k⟩ h ↦
      map_le_of_le_comap (h₂ ⟨.comap _, le_comap_of_map_le k⟩ ((comap_mono h).trans_eq
      p.comap_map_eq_self_of_faithfullyFlat))⟩).trans (by simpa [Order.one_le_iff_ne_zero,
      Submodule.eq_bot_iff] using ⟨w, j (isIntegral_iff.1 (d.map_of_comp_eq this 1 rfl)), by
      simp_all⟩))).ge) ((radical_map_of_mem_minimalPrimes V q _ h₄).ge ((map_eq_maximalIdeal ..).ge
    (V.mem_nonunits_iff_exists_mem_maximalIdeal.1 (inv_lt_one_of_one_lt₀ (not_le.1 h))).2))))

/-- A finite product of proper schemes over S is proper over S. -/
instance isProper_pi {S J} [Finite J] {A : J → Over S} [h : ∀ l, IsProper (A l).hom] :
    IsProper (∏ᶜ A).hom := let P : MorphismProperty _ := @IsProper
  have := MorphismProperty.HasOfPostcompProperty.of_le P _ @IsProper.toIsSeparated
  (P.over_iso_iff (Limits.PreservesProduct.iso (MorphismProperty.Over.forget P ⊤ S) (⟨_, h ·⟩))).1
    (MorphismProperty.Comma.prop _)

attribute [-simp] Subtype.forall

variable {ι V : Type} [FinComplexSpace V] {L : Submodule ℤ V} {B : LatticeForm L} {χ g u} {f :
  V → ℂ} {v : Valuation ℂ ℝ≥0} {r a : ℕ} {M : Submodule v.valuationSubring
  (V → ℂ)} (R) {A} [CommRing R] [CommRing A] [Algebra R A] (x : ι → A) (m) (G : HasGoodReduction B χ
  v r) (hf : f ∈ B.thetaSpace χ) (f0 : f ≠ 0) {L₀ ζ} (le : L ≤ L₀) [IsFullRankLattice L₀] (Z :
  IsAppellHumbert (L := L₀) B ζ) (Hf : f ∈ B.thetaSpace (L := L₀) ζ) (Hg : g ∈ B.thetaSpace (L :=
  L₀) ζ) (s : ∀ u ∈ B.dualLattice (L := L₀), B.thetaShift u f ∈ M) (dv : ∀ u, r • u ∈ L → u ∈ L₀)

/-- The m-th power of the R-span of the x_i in A, that is, the values at x of the forms of
degree m over R. -/
abbrev formSpan := Submodule.span R (range x) ^ m

lemma map_homogeneousSubmodule_eq_formSpan : (homogeneousSubmodule ι R m).map (aeval x).toLinearMap
  = _root_.formSpan R x m := by simp [Submodule.map_pow, ← homogeneousSubmodule_one_pow R m,
  Submodule.map_span, homogeneousSubmodule_one_eq_span_X, ← range_comp']

/-- p is a primitive integral scaling of w: p_j = w_j/s for one complex s and all j, and some
coordinate p_c is a unit of the valuation ring. -/
def IsIntegralCoords (w : V → ℂ) (p : V → v.valuationSubring) := ∃ s, (∀ j, p j = w j / s) ∧ ∃ c,
  v (p c) = 1

lemma thetaNorm_smul c : B.thetaNorm v (c • f) =
  v c * B.thetaNorm v f := by simp [↓NNReal.mul_iSup, LatticeForm.sizeAt, iSup, range]

@[simp] lemma thetaNorm_zero : B.thetaNorm v 0 = 0 := by simp [range, LatticeForm.sizeAt]

lemma thetaNorm_pow : (a • B).thetaNorm v (f ^ a) =
  B.thetaNorm v f ^ a := by simp [iSup, range, sizeAt_pow, ↓iSup_pow]

lemma dualLattice_nsmul_le {L₀} (hr : r ≠ 0) (h : ∀ u, r • u ∈ L → u ∈ L₀) : (r • B).dualLattice
  (L := L₀) ≤ B.dualLattice := fun _ k l i ↦ by simpa [*, ← smul_assoc] using k ((r⁻¹ : ℝ) • l)

variable [IsFullRankLattice L]

lemma IsAmpleType.thetaNorm_thetaShift (G : IsAmpleType B χ) (hu : u ∈ B.dualLattice) :
  B.thetaNorm v (B.thetaShift u f) = B.thetaNorm v f := have := G.2
  .trans (iSup_congr (G.sizeAt_thetaShift ⟨_,
    G.exists_nsmul_mem_of_mem_dualLattice.imp (by tauto)⟩)) (Equiv.addRight _).iSup_comp

/-- The ball of radius ‖f‖: the module, over the valuation ring of v, of theta functions in
`RealComplexForm.thetaSpace` whose size `LatticeForm.sizeAt` is at most ‖f‖ at every torsion
point. -/
noncomputable def HasGoodReduction.normBall (_ : HasGoodReduction B χ v r) f :=
  (B.thetaSpace χ).restrictScalars v.valuationSubring ⊓ ⨅ x : torsionPoints L,
  Submodule.comap ((.proj 0 ∘ₗ B.thetaShift x).restrictScalars _) (v.leSubmodule (B.thetaNorm v f))

@[local simp, local grind =] lemma HasGoodReduction.mem_normBall : f ∈ G.normBall g ↔
  f ∈ B.thetaSpace χ ∧ B.thetaNorm v f ≤ B.thetaNorm v
  g := by simpa +contextual [normBall, ciSup_le_iff (bddAbove_of_mem_sizes ⟨G.1, _⟩)] using by tauto

@[local grind .] lemma HasGoodReduction.thetaShift_mem_normBall : u ∈ B.dualLattice → f ∈ G.normBall
  g → B.thetaShift u f ∈ G.normBall g := by grind [G.thetaNorm_thetaShift, G.thetaShift_mem_of_dual]

include G in
omit [IsFullRankLattice L] in
lemma HasGoodReduction.pow j : HasGoodReduction (r ^ j • B) (χ ^ r ^ j) v r := { G.nsmul (by grind
  [HasGoodReduction]), G with dual_torsion := G.dual_torsion.imp' (· * r ^ j) (by simp_all [G.3,
  mul_smul, mem_dualLattice_nsmul]) }

include G hf f0 le Z Hf Hg s in
/-- Assume good reduction; let f ≠ 0 and g be theta functions for (L, χ) and for (L₀, ζ), L ⊂
L₀, and let M contain the translates of f by the dual of L₀. Then g = cx with x in M and ‖g‖
= v(c)‖f‖. -/
lemma HasGoodReduction.exists_smul_thetaNorm_eq : ∃ c, ∃ x ∈ M, g = c • x ∧ B.thetaNorm v g =
  v c * B.thetaNorm v f := have := G.isPosRiemann
  by if g = 0 then exact ⟨0, by aesop⟩ else
       obtain ⟨⟨N⟩, γ, _, H⟩ := Z.exists_nsmul_mem_of_mem_dualLattice,
         G.dual_torsion.elim fun _ ⟨n, _⟩ ↦ by
         simpa [*] using Z.exists_proportional_orbit_lattice ![⟨g, Hg⟩] ![⟨f, Hf⟩] 0 0 1
           ((valuationSubring.integers v).isUnit_of_one' n) (by solve_by_elim (maxDepth := 12))
       have k y := H (G.normBall y) fun _ _ _ ↦ G.thetaShift_mem_normBall (by tauto)
       specialize H (⨅ b ∈ B.dualLattice (L := L₀), M.comap ((B.thetaShift b).restrictScalars _))
       simp_all [Z.thetaShift_thetaShift]
       exact ⟨γ⁻¹, _, H (fun u k x h b l ↦ M.smul_mem ⟨_,
         (Z.valuation_exp_riemannForm ⟨_, N, by tauto⟩ ⟨_, N, by tauto⟩).le⟩ (by bound)) 0
         (by simp), by simp_all [((k _).2 _).antisymm ((k _).1 _).2, (k f).1, thetaNorm_smul]⟩

include hf le Z Hf Hg s in
/-- Assume good reduction; let f and g be theta functions for (L, χ) and for (L₀, ζ), L ⊂ L₀,
with ‖g‖ ≤ ‖f‖. Every module M over the valuation ring that contains the translates of f by
the dual of L₀ contains g. -/
lemma HasGoodReduction.mem_of_mem_normBall (k : g ∈ G.normBall f) : g ∈ M :=
  by_cases (by grind [!G.thetaNorm_pos, thetaNorm_zero, zero_mem]) (G.exists_smul_thetaNorm_eq
  hf · le Z Hf Hg s |>.rec fun _ ⟨_, H, E, _⟩ ↦ E ▸ M.smul_mem ⟨_, by simp_all [G.thetaNorm_pos]⟩ H)

include hf Z Hf dv in
/-- Assume good reduction, and let f be a theta function for (L, χ) and also for a lattice L₀
containing r⁻¹L. Then the r-th power of the ball of radius ‖f‖ is the ball of radius ‖f^r‖
in degree rB. -/
lemma HasGoodReduction.normBall_pow (R : HasGoodReduction (r • B) (χ ^ r) v r) : G.normBall f ^ r =
  R.normBall (f ^ r) := by
  obtain ⟨Y, p, P, a, rfl⟩ := Z.nsmul r, thetaSpace.pow hf, thetaSpace.pow Hf,
    le_iff_exists_add'.1 G.one_lt.le
  exact le_antisymm (by delta normBall; exact a.rec (by simp) fun _ h ↦ (mul_left_mono h).trans (by
    simpa [↓thetaNorm_pow, pow_add, add_smul, ↓Submodule.mul_le] using fun _ i k _ j l ↦
      ⟨thetaSpace.mul i j, fun i ↦ (v.map_mul ..).trans_le (mul_le_mul' (k i) (l i))⟩)) fun x h ↦
    R.mem_of_mem_normBall (p _) le_rfl R.isAppellHumbert (p _) h.1 (fun b k ↦ by
    apply R.mem_of_mem_normBall (succ_nsmul B _ ▸ thetaSpace.mul (p a)
      (G.thetaShift_mem_of_dual (mem_dualLattice_nsmul.1 k) hf)) (by solve_by_elim [nsmul_mem])
      (Y.shift b) ((thetaSpace.mul (P a) (Z.thetaShift_mem Hf _)).imp_right (by
      simp; grind)) <;> grind [Y.thetaShift_mem, Submodule.mul_mem_mul, Submodule.pow_mem_pow,
      thetaShift_mul, (dualLattice_nsmul_le _ dv ·), thetaShift_pow, succ_nsmul,
      mem_dualLattice_nsmul, HasGoodReduction, sizeAt_mul, G.thetaNorm_thetaShift,
      G.thetaShift_mem_of_dual, G.hasMultiplicativeNorm ⟨G.nsmul _, _⟩ ⟨G.1, _⟩]) h

include hf Z Hf dv in
/-- Integral normal generation: under good reduction, if f is a theta function for (L, χ) and
also for a lattice containing r⁻¹L, the r^j-th power of the ball of radius ‖f‖ is the ball
of radius ‖f^(r^j)‖ in degree r^j B.

Known result: Normal generation of sections on abelian varieties, kept under good reduction. -/
lemma HasGoodReduction.normBall_pow_pow j : G.normBall f ^ r ^ j =
  (G.pow j).normBall (f ^ r ^ j) := by induction j <;> simp_all [pow_add, pow_mul, mul_nsmul,
  thetaSpace.pow, ← (G.pow _).normBall_pow _ (Z.nsmul _)]

lemma HasGoodReduction.exists_eq_smul_normBall (hf : f ∈ B.thetaSpace χ) (f0 : f ≠ 0) (hg : g ∈
  thetaSpace χ B) : ∃ c, ∃ y ∈ G.normBall f, g = c • y ∧ B.thetaNorm v g = v c * B.thetaNorm v f :=
  G.exists_smul_thetaNorm_eq hf f0 le_rfl G.isAppellHumbert hf hg (by grind)

open Submodule

variable {W : Type} [AddCommGroup W] [Module v.valuationSubring W] {x : W →ₗ[_] _}
  (h : x.range = G.normBall f)

include hf f0 h

/-- Assume `HasGoodReduction`, f a non-zero theta function, φ onto k killing exactly the non-units.
If x maps a finite module onto the ball of radius ‖f‖, and the φ-semilinear y kills w
exactly when ‖x w‖ < ‖f‖, the image of y spans dimension dim Theta(L, B, χ).

Known result: Normal generation of sections on abelian varieties, kept under good reduction. -/
lemma HasGoodReduction.finrank_reduction_eq {k Q} [Field k] [AddCommGroup Q] [Module k Q]
  [Module.Finite v.valuationSubring W] {φ : v.valuationSubring →+* k} (hφ : (⇑φ).Surjective) {y :
  W →ₛₗ[φ] Q} (H : ∀ w, y w = 0 ↔ B.thetaNorm v (x w) < B.thetaNorm v f) :
  finrank k (Submodule.span k (range y)) = finrank ℂ (B.thetaSpace χ) := by
  have := @free_of_flat_of_isLocalRing _ _ _ _ x.range.module _ _
    (Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (isTorsionFree_iff_torsion_eq_bot.1 inferInstance))
  obtain ⟨_, _, _, b⟩ := ker_eq_maximalIdeal φ hφ ▸ @v.mem_maximalIdeal_iff, RingHomSurjective.mk
    hφ, IsLocalization.flat ℂ (nonZeroDivisors v.valuationSubring), finBasis v.valuationSubring
    x.range
  erw [y.range.span_eq, ← x.ker.range_liftQ y (by simp_all [LE.le, G.thetaNorm_pos]),
    ← Submodule.map_top, ← (b.map x.quotKerEquivRange.symm).span_eq, Submodule.map_span,
    ← range_comp, finrank_span_eq_card (Fintype.linearIndependent_iff.2
    ((hφ.comp_left.comp b.equivFun.surjective).forall.2 ?_)), ← span_eq_of_le (thetaSpace ..)
    (h.trans_le inf_le_left) fun _ ↦ by grind [exists_eq_smul_normBall, smul_mem,
    SetLike.mem_coe, mem_span_of_mem]] <;> simp [← map_smulₛₗ, ← map_smul, ← map_sum]
  intro ⟨_, w, rfl⟩
  choose a z _ _ _ using G.exists_eq_smul_normBall hf f0 (h.le ⟨w, rfl⟩).1
  erw [x.quotKerEquivRange_symm_apply_image, H]
  simp_all [G.thetaNorm_pos, le_of_lt,
    (show b.repr ⟨a • z, _⟩ = _ from b.repr.map_smul ⟨a, ·⟩ ⟨z, _⟩)]

/-- Assume `HasGoodReduction`. Let (x_j) enumerate the ball of a theta function f ≠ 0, (a_b) meet
every class of L^∨/L, and p_b primitively scale (x_j(a_b))_j. Then ‖x_j‖ < ‖f‖ iff p_{b,j}
is a non-unit for all b. -/
lemma HasGoodReduction.thetaNorm_lt_iff_coords {I} {a : I → V} (ha : ∀ u : B.dualLattice, ∃ b,
  a b - u ∈ L) {p : I → W → v.valuationSubring} (hp : ∀ b, IsIntegralCoords (x · (a b)) (p b)) j :
  B.thetaNorm v (x j) < B.thetaNorm v f ↔ ∀ b, v (p b j) < 1 := by
  choose s E c hc using hp
  obtain ⟨hx, b, k⟩ := (h.le ⟨·, rfl⟩), ha 0
  have h b : ∀ y ∈ G.normBall f, v (y (a b) / s b) ≤ 1 := h ▸ forall_mem_range.2 (E b · ▸ (p ..).2)
  exact ⟨(G.exists_eq_smul_normBall hf f0 (hx j).1).rec (by simp_all [← mul_div,
    mul_lt_one_of_lt_of_le, G.thetaNorm_pos]), Function.mtr fun e H ↦
    (G.mem_of_mem_normBall (M := Submodule.comap (.proj _ ∘ₗ .mulRight _ fun _ ↦ (s b)⁻¹)
    (v.ltSubmodule 1)) (hx j).1 le_rfl G.isAppellHumbert (hx j).1 (hx _).1 (fun u m ↦
    (ha ⟨_, add_mem (G.le_dualLattice k) m⟩).rec fun d n ↦
    (mul_lt_one_of_lt_of_le (H d) (h b _ (G.thetaShift_mem_normBall m (hx (c d))))).trans_eq' (by
    have := (hx · |>.1.2 _ n (a b + u))
    simp_all [thetaShift, division_def]
    grind)) (by grind)).ne (E .. ▸ hc _)⟩
