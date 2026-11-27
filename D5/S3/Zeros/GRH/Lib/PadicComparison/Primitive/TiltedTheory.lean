/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/TiltedTheory
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Primitive/TiltedTheory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Primitive.TiltedTheory. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Primitive/TiltedTheory.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Descent.AlmostAcyclic
import D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate.HodgeTatePairs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: Comparison map from F_p to the tilt; tilted coefficients form a theory with supports. -/

noncomputable section

open CategoryTheory TensorProduct PrimeSpectrum Functor CommRingCat Ideal PadicTest MonoidalCategory
  Quotient RingHom IsLocalization Away NeZero Perfection LocallyConstant Submodule CommAlgCat ZMod

section

variable {p} [ThePrime p]

/-- The natural map of 𝔽_p-algebras LC(S[1/p]) ≅ LC(S) → S^♭ for p-adic tests S, LC the locally
constant 𝔽_p-valued functions on the spectrum; x goes to the constant sequence of its image
in S/p. -/
def locConstToTilt : genericTest ⋙ testIncl ⋙ locConstAlg ⟶ tilt ⋙ restrictAlg _ _ := by
  choose φ h using fun c : PadicTest ↦
    @exists_ringHom_of_locallyConstant _ (ModP c.ProdRing p) _ _ (algebra ..)
  refine Iso.inv (NatIso.ofComponents (F := ringFunctor ⋙ locConstAlg) (fun c ↦
    isoMk (.ofBijective (locConstAlg.map (ofHom
    (algebraMap c.ProdRing _))).1 ⟨(coe_injective <| ((denseRange_comap_iff_ker_le_nilRadical _).2
    (bot_le.trans' c.eq_zero_of_algebraMap_genericRing)).equalizer ·.continuous ·.continuous <|
    coe_inj.2 ·), locConst_comap_surjective _ (c.isTest.isComparableRing_of_associated
    exists_associated_localization)⟩)) fun f ↦ .symm (locConstAlg.map_commSq ⟨hom_ext
    (ext (mapGeneric_algebraMap f))⟩).w) ≫ ⟨fun c ↦ ConcreteCategory.ofHom (.mk' (.codRestrict
    (.pi fun _ ↦ (φ c).comp (locConstAlg.map (ofHom (mk _))).1.1) (subring ..) fun _ _ ↦
    (map_pow ..).symm.trans congr(φ c $(by ext; apply pow_card))) (map_smul _)), fun c _ f ↦ ?_⟩
  ext; exact ext fun _ ↦ toPiLocalization_injective _ (funext fun _ ↦ .trans
    (by erw [h, eq_comm, ← RingHom.comp_apply, ext_zmod (.comp ..)]; symm; apply h)
    (Localization.localRingHom_to_map _ _ (quotientMap _ f.1 (by simp)) (comap_asIdeal ..) _))

/-- The functor from test rings to O^♭-algebras sending S to O^♭ ⊗ LC(S), the tensor product
over 𝔽_p, LC(S) the locally constant functions Spec S → 𝔽_p. -/
abbrev oFlatLocConst := (testIncl ⋙ locConstAlg) ⋙ algBaseChange OFlat

/-- The natural map of O^♭-algebras from O^♭ ⊗ LC(Spec R[1/p], F_p) to the tilt R^♭, for p-adic
tests with ring R, LC denoting locally constant functions. -/
def primitiveMap : genericTest ⋙ oFlatLocConst ⟶ tilt := (baseChangeTranspose ..).2 locConstToTilt

end

variable {p} (Ω) [CommRing.{0} Ω] [InvertsPrime Ω p] [Algebra Ω ℂ_[p]] (M)

/-- The theory (ℓ = p) on p-adic tests along R ↦ R[1/p] with coefficient R^♭ ⊗ M over O^♭, assuming
the coefficient satisfies `IsAcyclicOnPerfect` (acyclicity on every perfect O^♭-algebra). -/
def tiltTheory (ac : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) :
  Theory (genericTestOver Ω) := let J c I := nearZeros c I (tilt.map · |>.1 |> ker)
  have B c I := surjective_and_dies_of_quotient_sieve tilt (R := killingMaps (ringOf
    (genericTestOver Ω)) I) (ofHom (mkₐ _ (J c I))) (fun f h ↦ ⟨ofHom (liftₐ _ _ fun _ ⟨_, k, l⟩ ↦ l
    _ f ⟨1, .symm (by simpa using! le_comap_of_map_le h.le k)⟩), rfl, fun _ e ↦ hom_ext (algHom_ext
    _ congr($e.1))⟩) (fun f g h ↦ (map_eq_bot_iff_le_ker _).2 ((map_under (.powers ↑p) c.GenericRing
    I).ge.trans (map_le_of_le_comap fun r b ↦ (mapGeneric_algebraMap ..).trans (OrderBot.bot_le
    (ker _) (eq_of_forall_pow_dvd_sub _ fun n ↦ (c.isTest.2 r (p ^ n)).elim fun e ⟨i, k, l⟩ ↦
    (mem_jacobson_bot.1 (HenselianRing.jac (mk_ker.le congr($(congr($h ⟨fun _ ↦ e, by simp [(i.map
    _).pow_eq out]⟩).symm.trans ((ker g.1).ker_le_comap _ (mk_ker.ge ⟨_, I.mem_of_dvd (by
    simpa [-map_natCast, algebraMap_pow_isUnit] using! map_dvd (algebraMap _ c.GenericRing) k) b,
    fun d f u ↦ ext fun _ ↦ congr(⟦$(d.eq_zero_of_algebraMap_genericRing _ (u.mul_right_eq_zero.1
    (by simp [mapGeneric_algebraMap, sub_mul, ← map_mul, i.eq])))⟧)⟩))).1 0))) (-1)).dvd_mul_left.1
    (by simpa [neg_add_eq_sub] using map_dvd f.1 l)))))) (@ac _ (@perfectRing_of_pow_surjective _ _
    _ _ p_eq_zero_of_algebra_oFlat ((isRadical_iff_quotient_reduced _).1 fun _ ⟨n, h⟩ ↦ by
    peel 5 h; exact (isReduced_of_perfectRing (isPerfectTorsionFree_tilt _).1).1 _ ⟨n, by simpa⟩)
    (Quot.ind (c.isPerfectTorsionFree_tilt.1.1.2.forall.2 (⟨⟦·⟧, rfl⟩)))))
  ⟨⟨tilt ⋙ moduleCoeff (tensorCoeff M), fun c x ↦ congr(⟨$(by simp [p_eq_zero_of_algebra_oFlat,
    ← Nat.cast_smul_eq_nsmul OFlat])⟩), let _ : EmbeddedInQpBar p ℚ := {}
    hasZariskiDescent_genericOver (𝟭 _) ⟨exists_isIdemQuotient, (bijective_prod_tilt · · ·
    |>.map_prod (moduleCoeff (tensorRight _) ⋙ forget _))⟩⟩,
    (B · · |>.1 (ULift.map_surjective.2 (LinearMap.rTensor_surjective _ exists_rep))),
    fun c I x h n _ l ↦ (mem_span.1 ((range_map_eq_span_tmul ..).le ((rTensor_mkQ M ((J c
    I).restrictScalars OFlat)).le congr($((B ..).2 x h).1))) (c.nearZeros I ((tilt ⋙ tensorCoeff
    M).map · |>.1.ker)) (by rintro _ ⟨y, m, rfl⟩; peel 5 y.2; simpa using! congr($this ⊗ₜ m))).elim
    fun a h ↦ ⟨_, (n.sub_mem_iff_left (l h.1)).1.mt n.one_notMem, (congr(⟨$(h.2 · · ·)⟩))⟩⟩
