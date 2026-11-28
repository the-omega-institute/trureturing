/- GID: D5/S3/Zeros/GRH/New/Rows/LiftVolumeHeight
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/LiftVolumeHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.LiftVolumeHeight. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/LiftVolumeHeight.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.HeckeValueHeight
import D5.S3.Zeros.GRH.New.Rows.ComparisonForms
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! The rows repay the cost of the idle directions. The volume of the chain of lifts on the D rows
is a controlled factor times the volumes of m single lifts, and at the chosen twists each
untwisted-to-twisted ratio of these has height at most D times (a small error minus the cost of k
directions), which gives the lower bound that cancels this cost. Bounding the norm of a lift
by an integral form and a congruence denominator is known for one eigenform. Related work:
Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; X. Zhang, Special L-values
and Selmer groups of Siegel modular forms of genus 2, 2018; Hida, Congruences of cusp forms and
special values of their zeta functions, 1981.

This file: Height bound for untwisted over twisted volume of one lift on good forms. -/

open Module ComplexConjugate Finset Function PolyRep IsAlgClosed LinearMap Matrix NumberField
  AuxPair Real Space LevelPlaces.LevelForm

variable {T U V} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [Module.Finite ℂ T]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [Module.Finite ℂ U] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [Module.Finite ℂ V] {gl : T →ₗ[ℂ] V} {u : U →ₗ[ℂ] V} {A} {γ : ℂ} (k : ℂ)

namespace Data

/-- The endomorphism z ↦ k·pr_L(gl(gl* z)) of the subspace L of V, where gl* is the adjoint of
gl and pr_L the orthogonal projection to L. -/
noncomputable def compressedGramOp (L : Submodule ℂ V) (gl : T →ₗ[ℂ] V) :
    End ℂ L := k • (L.orthogonalProjectionOnto.toLinearMap ∘ₗ gl) ∘ₗ gl.adjoint.domRestrict L

/-- If u* ∘ gl = γA for linear maps of finite-dimensional complex inner product spaces, then gl*
∘ u = γ̄A*. -/
lemma adjoint_comp_eq_conj_smul (h : u.adjoint ∘ₗ gl = γ • A) :
  gl.adjoint ∘ₗ u = conj γ • A.adjoint := by simpa [map_smulₛₗ] using congr(adjoint $h)

/-- `normDet(u)² · det(compressedGramOp k (range u) gl) = k^(dim range u) · normDet(gl* ∘ u)²`. -/
lemma det_compressedGramOp : u.normDet ^ 2 * (compressedGramOp k u.range gl).det = k ^ finrank ℂ
  u.range * (gl.adjoint ∘ₗ u).normDet ^ 2 := by rw [compressedGramOp, (eq_adjoint_iff (_ ∘ₗ gl)
  (gl.adjoint.domRestrict _)).2, normDet_comp] <;> simp [adjoint_inner_right, ← normDet_sq, field]

variable {P} {D : Data P} {j : D.LiftIndex} {ϑ : D.Twist} {gl : Tables j →ₗ[ℂ]
  (D.auxPair ϑ j).FormV} {L : Submodule ℂ _} {β} (sep : ∀ z : L, gl.adjoint z = 0 → z = 0)
  (tst : ∀ (z : SubmoduleElem L), (D.auxPair ϑ.toTameChar j).IsTested D.e₀ Lᗮ (gl ((adjoint gl) z)))

include sep tst in
/-- Let gl* be injective on L, gl gl*L tested (`AuxPair.IsTested`), gl ζ integral at φ: ℂ → ℂ_ℓ
whenever ζ̄ is integral at φ∘conj, and `DenominatorLe` hold at ι. Then |ι det(𝗁·pr_L gl
gl* on L)| ≤ exp(dim L·rβ), 𝗁 = `smallHookNumber`. -/
lemma norm_det_compressedGramOp_padic_le (ι : PrimePadicIso) (int : ∀ ζ (φ : PadicPlace ι.1),
  (∀ a, weylGauge (ι := ⟨φ.ιₚ.comp conj⟩) _ 0
  a.2.out (star (ζ a)) ≤ 1) → gl ζ ∈ integralForms φ) (h : DenominatorLe ι.2 _ D.e₀ L β) :
  ‖ι.2 (compressedGramOp (smallHookNumber j) L gl).det‖ ≤ exp (finrank ℂ L * (D.r * β)) := by
  choose δ hγ _ using fun c : D.SmallClasses ↦ exists_mul_mem_integralAbove ι.1 c.out 1
  let f (a : _ × _) : Tables j := .toLp 2 fun b ↦ (star (weightRep _ 0 _ (δ b.2)⁻¹
    (star (((ite (b = a.1) (of fun i k ↦ fockPairing ℤ (nablaBasis ℤ _ _ i)
    (nablaBasis ℤ _ (untwistedAuxPair j).colsMinus k)) 0).map (↑)).col a.2))) :)
  have Y a ζ : inner ℂ (f a) ζ = smallHookNumber j * conj (weightRep _ 0 _ (δ a.1.2) (star (ζ a.1))
    a.2) := by erw [PiLp.inner_apply, Fintype.sum_eq_single a.1, show inner .. = gramForm _ _ from
    dotProduct_comm .., ← conj_gramForm, ← star_star (R := _ → ℂ) (ζ _), ← gramForm_map_weightRep
    (e := 0) conj (δ a.1.2)] <;> simp +contextual [f, comp_def, gramForm_apply, ← mulVec_single_one,
    -mulVec_single, ← map_mul_intCast, weylGram_mul_fockPairing, ← diagonal_intCast]
  choose c z e hz using exists_auerbach (finBasis ..) (fun a ↦ innerₛₗ ℂ (f a) ∘ₗ
    gl.adjoint.domRestrict _) (fun v h ↦ sep v (PiLp.ext fun c ↦ star_injective (R := _ → ℂ)
    ((Representation.apply_bijective ..).1 (by ext; simpa [Y] using h (c, _)))))
    (complexToCp ι.2) fun _ ↦ continuous_bot
  convert card_rowIndex D ▸ h _ rfl (gl ∘ f ∘ c) _ ?_ fun a ↦
    ⟨?_, tst ((smallHookNumber j : ℂ) • z a)⟩
  any_goals intros; apply int; intro; rw [← weylGauge_embFin, @weylGauge_le_one_iff (hk := hγ _)]
  simp [← det_toMatrix z, toMatrix_apply, ← z.coord_apply, e, compressedGramOp, adjoint_inner_right,
    det_apply]
  · simp [f, IsUltrametricDist.norm_intCast_le_one]
  simpa [Y] using fun i ↦ hz (_, i) a

include sep tst in
/-- Let gl* be injective on L and gl gl*L tested (`AuxPair.IsTested`). If L is the range of the lift
and gl has the size bound S at all σ, every conjugate of the determinant of `compressedGramOp` on L
has absolute value at most exp(dim L · β). -/
lemma norm_det_compressedGramOp_arch_le (e : L = (D.goodLift ϑ j).range) (S : ∀ ζ σ,
  smallHookNumber j * (gl ζ).normSqAt σ ≤ exp β * ∑ a, weylNormSq (σ ∘ ζ a)) (σ : ℂ ≃+* ℂ) : ‖σ
  (compressedGramOp (smallHookNumber j) L gl).det‖ ≤ exp (finrank ℂ L * β) := by
  erw [← place_apply σ.toRingHom, End.det_eq_prod_roots_charpoly_of_splits (splits _), exp_nat_mul,
    map_multiset_prod, ← charpoly_natDegree, ← card_roots_eq_natDegree]
  refine Multiset.prod_map_le_pow_card (by simp) fun α h ↦ ((End.hasEigenvalue_iff_isRoot_charpoly
    ..).2 (Polynomial.mem_roots'.1 h).2).exists_hasEigenvector.elim fun z h ↦ ?_
  obtain ⟨w, hw, t⟩ := (frequently_isSplit_notMem_places (D.auxPair ϑ j)).exists
  let ζ := gl.adjoint z
  have := congr(‖σ (inner ℂ (gl (.toLp 2 (star ∘ σ.symm ∘ star ∘ σ ∘ ζ ·)))
    ($h.apply_eq_smul).1)‖).ge
  simp [compressedGramOp, ← adjoint_inner_right gl _ z, ← le_div_iff₀'] at this S
  grw [show σ (inner ..) = ∑ i, weylNormSq (σ <| ζ i ·) by simp [ζ, inner, coe_weylNormSq,
    dotProduct, mulVec, mul_comm (conj _)], norm_map_inner_le, normSqAt_starProjection_le _ hw t
    D.isCentralProj_e₀ (e ▸ D.range_goodLift_le fun _ _ a _ k m ↦ ⟨D.range_tupleIdem_le k m,
    heckePolyOnForms_testValue_eq_zero _ _ (D.lifts_auxLift _ a.2)⟩) (tst z), S, S] at this
  simpa [ζ, comp_def, abs_of_pos, field, ↓Complex.norm_real, le_of_lt, (sum_pos' (by simp)
    ((not_forall.1 (h.2 ∘ sep z ∘ PiLp.ext)).imp (⟨mem_univ ·,
    weylGram_posDef.re_dotProduct_pos <| by simpa [funext_iff, SmallFormValues] using! ·⟩)) : 0 <
    ∑ i, weylNormSq (σ <| ζ i ·)), exp_pos] using this

/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily` and 1 ≤ j ≤ m, the volume ratios
λ_j(1)/λ_j(θ(ι)^j) (`Data.liftVolume`) have height (`HeightLe`) at most d·k·(B₀·log b − 𝖴), with d
the dimension of `Data.rows` and 𝖴 = `Data.dirCost` (size of a jet less its forced divisibility), B₀
= fa(log b)³/(mk) = `Data.B₀`.

The rows repay the cost of the idle directions. -/
lemma heightLe_liftVolume_ratio {θ} (O : D.IsFitFamily θ) (j : D.LiftIndex) :
  HeightLe (D.rowDim * (D.k * (D.logB * D.B₀ - D.dirCost))) fun ι ↦
  D.liftVolume 1 j / D.liftVolume (θ ι) j := (O.denominator_le j).elim fun β ⟨g, g'⟩ ↦ by
  rw [D.finrank_rows_eq_finrank_goodForms j, liftVolume, show TameChar.pow _ j =
    .one by rw [TameChar.pow]; congr <;> apply one_pow]
  obtain ⟨γ, A, gl, H, ad, sur, tst, int, S⟩ := exists_comparison_forms j
  have d ϑ := finrank_range_of_inj (f := D.goodLift ϑ j) (by simp [auxLift_injective])
  replace tst ϑ y :=
    (A.adjoint.map_smul ..).trans congr($(adjoint_comp_eq_conj_smul (ad ϑ)) y).symm ▸ tst ϑ _
  let u (ϑ : D.Twist) := (compressedGramOp (smallHookNumber j) (D.goodLift ϑ j).range (gl ϑ)).det
  have V ϑ : _ * u ϑ = _ := adjoint_comp_eq_conj_smul (ad ϑ) ▸ d ϑ ▸ det_compressedGramOp _
  have T ϑ := right_ne_zero_of_mul ((V ϑ).trans_ne (by simp [H,
    normDet_eq_zero_iff_ker_ne_bot, ← orthogonal_range, range_eq_top.2 sur]))
  have sep ϑ z (h : (gl ϑ).adjoint z.1 = 0) :=
    ker_eq_bot'.1 (equivOfDetNeZero _ (T ϑ)).ker z (by simp [compressedGramOp, h])
  refine O.heightLe_of_eq_zpow_mul (.mul (y := fun ι ↦ u ((θ ι).powTwist j) / u 1) ⟨_, _,
    (_ : ℕ) * (D.r * β), T 1, d _ ▸ norm_det_compressedGramOp_arch_le (sep 1)
    (fun | ⟨_, y, rfl⟩ => tst 1 y) rfl S, fun ι ↦ ?_, .of_forall
    fun _ ↦ by simp [← mul_sum]; grw [g]; simp⟩ ((heightLe_inv_heckeValueProd_div O j).pow _))
    (by rw [← mul_add, ← mul_add]; gcongr; simpa [mul_sub, add_sub] using D.le_of_hasLogBound) fun ι
    n ↦ ⟨0, by
    have := div_ne_zero_iff.1 n; simp [← (H _).2, field, div_pow, V 1, *]
    erw [V ((θ ι).powTwist j)]; simp; ring⟩
  exact mul_div_cancel₀ _ (T 1) ▸ d _ ▸ norm_det_compressedGramOp_padic_le (sep _)
    (fun | ⟨_, y, rfl⟩ => tst _ y) ι (int _ · _ · (O.1 ι)) (g' ι).1
