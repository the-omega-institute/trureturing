/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SeedRepresentation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/SeedRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.SeedRepresentation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/SeedRepresentation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Division.MultiplicityFreeSum
import D5.S3.Zeros.GRH.Lib.Shimura.Transfer.PELDataExistence
import D5.S3.Zeros.GRH.Lib.Cohomology.PointClass.GaloisRep
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.ModelExistence
import D5.S3.Zeros.GRH.Lib.GaloisRep.HodgeTateCocharacter.HodgeTateCocharacter
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Galois representation from geometry for odd-rank forms of cuspidal type and free
weights. -/

open IsLocalization Subgroup

attribute [local grind =] mem_star_place star_natCast star_star below_star

attribute [local simp] Function.uncurry mul_assoc starRingEnd_apply

/-- Let E ⊃ ℚ(√−d) be stably unramified, f of odd rank with polynomials P off S, of cuspidal type
at w₀ ∈ S above ℓ, with free jumps at v ∉ S ∪ S̄ over w₀'s split prime u; let w' lie over a split
prime, u if w' ∣ ℓ. Some continuous r has characteristic polynomial ιP_w at most Frobenii,
and `SphericalClause` at w' if w', w̄' ∉ S. -/
lemma exists_rep_of_cuspidal_type {ℓ E a d} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E]
  [EmbeddedNumberField E] [HasQuadSubfield d E] [StablyUnram E] (ha : Odd a) {κ f} (hf :
  f ∈ (stdSpace E (Fin a)).forms κ) {S P} (hP : IsSphericalOff S f P) {w₀ v}
  (hS : w₀ ∈ S) (hu : IsSplitPrimeToDisc (w₀.below _)) {χ} (hty : IsCuspidalType
  (localCongruence _ _ 0) χ) (hχ : ∀ j, rightRegular ℂ _ _ (atSplit hu.star_ne j.1) f =
  χ j • f) (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below _)
  {ε : Ω →+* PadicAlgCl ℓ} (hσ : placeOfEmb (ε.comp (algebraMap ..)) = v) {e : Fin a → ℤ}
  (he : FreeInts e) (he' : ∀ i, e i ∈ jumps κ a (.comp ιℓ.symm (ε.comp (algebraMap ..)))) w' (hw' :
  IsSplitPrimeToDisc (w'.below (QuadField d)) ∧ (↑ℓ ∈ w'.1 → w'.below (QuadField d) = w₀.below _)) :
  ∃ r : GalRep ℓ E (Fin a), Continuous r ∧ (∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = (P
  y.w).map ιℓ) ∧ (w' ∉ S ∧ star w' ∉ S → SphericalClause r Eq (jumps κ a) w' ((P w').map ιℓ)) := by
  have _ := NeZero.of_pos ha.pos
  have {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  let F := pure v ⊔ Filter.principal {w | w' = w ∧ w' ∉ S ∧ star w' ∉ S}
  refine
    (exists_rep_span_diagonal ((mostFrobenii E).map (·.w) ⊔ F) (jumps κ a) (P · |>.map ιℓ) fun τ₀ ↦
    let s₀ := (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap ..))).comp (algebraMap (QuadField d) E)
    ?_).elim fun b ⟨r, hr, hd, h₁, gv, gc⟩ ↦ ?_
  obtain ⟨⟨ξ, μ, n, A₀, hμ, hξ, hz, hl⟩, Ψ, ⟨hv₀, hΨ⟩, N, h, model⟩ :=
    exists_occursInWeight ha (algebraMap ..) s₀ κ, exists_pel a _ {w₀, w'}
  have ev w := (eventually_notMem_star_notMem d S).and ((tendsto_place_comap_cofinite (algebraMap
    ..)).eventually (eventually_notMem_star_notMem N ((insert w S).image (.below (QuadField d)))))
  obtain ⟨w₁, g₁, ⟨⟨k₁, k₂, -⟩, hw⟩, nt⟩ := ((frequently_prime_q.mono fun _ ↦
    isSplit_of_q_prime).and_eventually ((ev w').and (eventually_isNeat (n := Fin a)))).exists
  let B :=
    insert w₁ {w ∈ S ∪ S.image star | star (w.below (QuadField d)) ∉ [w₀.below _, w'.below _]}
  have cv : ∀ w ∈ insert w₁ S, w ∈ B ∨ star w ∈ B := by clear * - hu hw' this hv hσ; grind
    [IsSplitPrimeToDisc.star_ne_and_prime_norm, natCast_mem_placeOfEmb]
  choose 𝔑 h𝔑 hB hlev using exists_levelGU_conj_le (⟨rightStab f,
    hf.1⟩ ⊓ (.comap _ (Gf.continuous_atPlace w₀) ⟨localCongruence _ _ 0, isOpen_localCongruence⟩ ⊓
    .comap _ (Gf.continuous_atPlace w₁) ⟨_, isOpen_proIwahori⟩) : OpenSubgroup _).2 (fun k h ↦
    ⟨congrFun (hP.2.1 k (h.imp_right (by simp))), by simp [Gf.mem_trivialOn.1 h.2, *]⟩) cv N
  obtain ⟨gv, k₃⟩ : F.Eventually (IsSafe 𝔑) ∧ 𝔑 ∉ (star w₀).1 ∧ 𝔑 ∈ w₁.1 ∧ 𝔑 ∉ (star w₁).1 := by
    simp [F, IsSafe, hB, B]; clear * - hu hv hw' hS h hw g₁ this
    grind -ring -linarith
  have gS w : IsSafe 𝔑 w → 𝔑 ∈ w₀.1 ∧ w ∉ S ∧ star w ∉ S := by clear * - cv hB hS k₃; grind [IsSafe]
  choose t ht ht' using fun w : SafePlace 𝔑 ↦ ((gS _ w.2).2.elim (hP.2.2 _ w.1.2)).2
  have η := nt 𝔑 (by simp [·] at k₃) k₃.2.1
  obtain ⟨⟨D, rfl, rfl, T, V⟩, _, -⟩ := model 𝔑 η.1 h𝔑, trace_definiteForms ξ η 1 1
  have O (u : Gf E D.Index) : IsSignedFrameFor (invTransposeGL u.1) .. :=
    isSignedFrameFor_one (entryConj u)
  let Q (p : _ × Gf ..) : _ ⧸ levelGU D.Index D.𝔑 := ⟦toFinGL p.1 * invTransposeGL p.2.1⟧
  let φ := Q.extend (fun (y, u) ↦ ξ y (f u)) 0
  have hφ o : φ (Q o) = _ := Function.FactorsThrough.extend_apply (fun ⟨z, t⟩ ⟨y, u⟩ e ↦ by
    obtain ⟨⟨y, rfl⟩, e⟩ := mul_left_surjective z y, QuotientGroup.eq.1 e
    have := hf.2 (entryConj ⟨y, ((O u).conj_eq_smul (O t)
      (by simpa [-IsScalarFrame] using levelGU.isScalarFrame_inv_one e)).trans (by simp)⟩) u
    rw [← mul_inv_cancel_left t (_ * u), (hlev _ ?_).1] at this; simp [*]
    simp; erw [stdSpace_embFin]; simpa using! e) ..
  choose L H using fun w hw x ↦ @by_cases (∃ z k p, Q p = ⟦toFinGL z * (x * conjAtSplit w k)⟧)
    (∃ L : _ →ₗ[ℂ] _, ∀ y g, φ ⟦toFinGL y * (x * conjAtSplit w g)⟧ =
    ξ y (L (rightRegular ℂ _ _ (atSplit w.2 g) f))) (fun ⟨z, k, p, e⟩ ↦ by
    rw [QuotientGroup.eq] at e; have := conjAtSplit_dualComponent (w := w) hw e
    generalize dualComponent (n := D.Index) w _ = c at this
    exact ⟨ξ _ ∘ₗ .proj _, fun y g ↦ (congrArg φ (QuotientGroup.eq.2 (by simpa using!
      (inv_mul_eq_of_eq_mul (this.2 (k⁻¹ * g)) ▸ mul_mem (inv_mem this.1) e :)))).symm.trans ((hφ
      (y * (z⁻¹ * _), _ * atSplit w.2 (c * k⁻¹) * _)).trans congr($(map_mul ξ ..) _))⟩)
    (⟨0, by simp [φ, by simpa using ·]⟩)
  let s := @centralScalar E _ _ _ D.Index
  have hc x g : g * s x = s x * g := commute_scalar_GL ..
  have mem : cyclicSpan ((rightRegular ..).comp s) (φ ⟦·⟧) ≤ definiteForms D.𝔑 ξ :=
    Submodule.span_le.2 fun _ ⟨x, e⟩ ↦ e ▸ ⟨⟨fun y z ↦ H ⟨_, hu.star_ne⟩ k₃.1 |>
    fun G ↦ by simpa [← (by simpa using G · 1 1)] using G _ y 1,
      fun z ↦ (dite_eq_right fun ⟨p, e⟩ ↦ · (by
    simpa [s, ratConj] using IsSignedFrame.mul ⟨_, O p.2⟩ p.1 (mul_mem (QuotientGroup.eq.1 e).1
      (inv_mem (centralScalar_mem_GU x).1))))⟩, by simp [funext_iff, hc, ← mul_assoc]⟩
  choose ω ψ hψ' hψ cen using @exists_eigencharacter ℂ _ _ _ _ _ _ (.of_fg (.of_le .of_finite mem))
    _ _ _ apply_mem_cyclicSpan
    (hP.1 <| by ext1; simpa using (hφ (1, _)).symm.trans congr($(· self_mem_cyclicSpan) _))
  obtain ⟨hF, c, h₃⟩ := mem hψ', Finsupp.mem_span_range_iff_exists_finsupp.1 hψ'
  have hω' x h : x ∈ ω.toHomUnits.ker := Units.ext ((smul_left_inj hψ).1 (cen x ▸ hF.2 ⟨_, h⟩ :))
  let L w h := c.sum fun x r ↦ r • LinearMap.pi (L w h <| s x * ·)
  have hL w h g : rightRegular ℂ _ _ (conjAtSplit w g) ψ =
    L w h ((rightRegular ℂ ..).comp (atSplit w.2) g f) := by
    simp [funext_iff, ← h₃, L, Finsupp.sum, ← mul_assoc, hc, (by simpa using H _ h · 1 ·)]
  replace h₃ := (by simpa using hL · · 1 |>.symm)
  obtain ⟨hs, hω⟩ : IsTestVector _ (rightRegular ..) ψ ⟨_, hu.star_ne⟩ ⟨_, g₁⟩ χ ∧ (ω.toHomUnits,
    .ofAdd A₀) ∈ algHeckeChars _ := by refine ⟨⟨⟨hS.ne_of_notMem k₁, k₃⟩, ⟨fun g h ↦ by simpa using
    (hlev _ h).2.1, fun _ ↦ (·.1)⟩, hty, fun _ h ↦ by simpa using (hlev _ h).2.2, hψ, ?_, ?_⟩,
    isOpen_mono (hω' · ⟨(centralScalar_mem_GU _).1,
    mem_comap.1 ·⟩) ((isOpen_congruenceGL_span η.1).preimage (.of_coeHom_comp <| .matrix_diagonal <|
    by simp; fun_prop)), fun x ↦ (smul_left_inj hψ).1 (cen _ ▸ funext fun y ↦ congr(ψ $((hc
    ..).trans ?_)).trans ((hF.1.1 _ y).trans (congr($(hz x) _).trans ?_)))⟩ <;> simp +contextual [s,
    h₃, k₃, ↓hL, Units.ext_iff, ↓hχ, ↓by simpa [mem_sphericalAt_iff g₁] using (hP.2.2 _ g₁ k₁ k₂).1]
  let M := ⨅ w, ⨅ _ : IsSafe D.𝔑 w, w.1.primeCompl
  have hM w : Disjoint M.carrier w.1 ↔ IsSafe D.𝔑 w := by
    have ⟨y, _, e, _⟩ := exists_levelGU_conj_le (n := Unit) isOpen_univ le_top (S := {w}) (fun _ ↦
      .inl) 1
    clear * - e; simp_all [M, Set.disjoint_left, Ideal.one_notMem]; grind
  have z : M ≤ _ := iInf₂_le_of_le v gv.1 v.1.primeCompl_le_nonZeroDivisors
  choose ρ hρ H₁ using (exists_model (nonempty_universalFamily z fun m k ↦ V _ ((hM ⟨_, .comap _,
    (bot_lt_under_prime M (Localization.subalgebra E M z) z m (m.bot_lt_of_maximal
    (Ring.not_isField_of_ne_of_ne (Ideal.map_ne_bot_of_ne_bot v.3)
    ((map_algebraMap_ne_top_iff_disjoint ..).2 ((hM v).2 gv.1)))).ne').ne'⟩).1 ((disjoint_under_iff
    ..).2 k.1.1))).some η T V _).some.exists_galois_rep η M iInf₂_le (fun w ↦
    t w * ((ω (unifNorm w.1))⁻¹ ^ ·))
    (.filter (fun _ ↦ τ₀.comp (algebraMap ..) = s₀) ((jumps κ _ τ₀).map (· + ↑μ))) fun u hu ↦ by
    obtain ⟨⟨u, o, rfl⟩, e⟩ := by simpa using hu
    refine (hl _ e u o).imp_right (· hv₀ hΨ η hs hF fun w j ↦ ?_)
    erw [asAlgebraHom_tau (w, j) hF.2, ← h₃ _ (w.2.2.2 _ (below_star ..)),
      ← map_heckeFun _ (isBiInvariant_basicDoubleCoset
      j).1 fun g ↦ by erw [h₃, hL], ht', map_smul, h₃, map_smul, cen]; simp [smul_smul]
  refine (exists_twist_algHeckeChar (.baseChange ⟨_, hω⟩) μ hρ).imp fun _ ⟨c, H₂⟩ ↦ ⟨c,
    .mono ⟨eventually_mostFrobenii (ev w₁) fun y ⟨a, k⟩ ↦ ?_, gv⟩ fun w g A hA ↦ ?_⟩
  -- modulo a prime of degree one prime to `d`, `QuadField.c₀ d` is an integer multiple of `d`
  have g : IsSplitPrimeToDisc (y.w.below (QuadField d)) := (mem_zmultiples_of_prime_card (hp :=
    ⟨y.prime_q⟩) rfl (Ideal.Quotient.eq_zero_iff_mem.1.mt a.2.2)).elim fun a e ↦ ⟨a * d, by
    simpa using Ideal.Quotient.eq.1 e.symm, 1 - 2 * a * QuadField.sqrtNegDInt d, 2 * a *
    QuadField.sqrtNegDInt d + 1, by clear * -; simp; grind [QuadField.sqrtNegDInt_sq d]⟩
  simp [IsSafe, hB]; clear * - g k this; grind -ring -linarith
  have K s (e : inducedPrime s = w) : s.comp (algebraMap ..) = s₀ :=
    (NumberField.InfinitePlace.mk_eq_iff.1 (by subsingleton)).resolve_right fun h ↦
    g.2.2 _ (by ext; simpa [← hv.2.2, ← e, ← hσ, s₀,
    map_star_CM, -starRingEnd_apply] using (congr(‖ιℓ ($h _)‖ < 1)).symm) (gS w g).1
  refine ht ⟨⟨w, g.1.star_ne⟩, g⟩ ▸ Fintype.card_fin _ ▸ (H₂ w ?_ (fun x r ↦
    hω' _ (mem_levelGU_of_local (centralScalar_mem_GU _).1
    (by simpa [s, mem_intGL, ← map_inv, ite_mem, Matrix.diagonal, star_eq_adeleMap] using!
    (coe_idelesUnitOff_empty.le (locIdele_mem_idelesUnitOff
    r)).imp adeleNorm_mem_Ohat adeleNorm_mem_Ohat) fun v h ↦
    ⟨1, by simpa using! evalAt_centralScalar_of_ne (g.2.2 v · h) x⟩)) (H₁ ⟨⟨w, _⟩,
    g⟩) hA).imp_right (.imp_left (·.congr hA ?_)) <;> simp +contextual [*, AlgHeckeChar.baseChange,
    apply_ite, RingHom.algebraMap_toAlgebra]
  clear * -; grind
  obtain ⟨⟨j, hj⟩, z, q, -⟩ := exists_inducesPlace E Gal(Ω/E) (ι := ε) rfl,
    gv (hσ ▸ isPlaceOver_placeOfEmb ε)
  let := PadicPlaceEmbedding.mk (toOverGp := ⟨_, ⟨hj.2.1.2⟩⟩) _ hj
  choose T k hT hk _ using
    z.2.isPotCrys.exists_isHodgeTateFrame (Pi.basisFun ..) (IsScalarTower.toAlgHom ..)
  obtain ⟨rfl, u⟩ := by simpa using (rank_eq_and_charpoly_eq r hr hd (.mp h₁ <|
    eventually_mostFrobenii (eventually_notMem_star_notMem ℓ S)
    fun y ⟨o, p, l⟩ g ↦ ⟨((g y.isPlaceOver).2.2 _ y.isFrob).1
    (y.isPlaceOver.valuation_natCast_eq_one_iff.2 l), ((hP.2.2 _ (isSplit_of_q_prime
    y.prime_q) o p).isMonicOfDegree hP.1).rec (⟨by simp [·], ·.map _⟩)⟩) T⁻¹ k he (fun n ↦ by simpa
    [List.count_eq_zero] using (hk _ ▸ q (g := 1) (by tauto) _ (by simpa using! he' n) :)) fun F h ↦
    by convert aeval_cocharacter_eq_zero (k ·.1) T⁻¹.1.uncurry F (nhds_one_le_map_nearOne _ (hT.mp
      (nearOne_eq_nhds_one hj.2.1 ▸ .mono (continuousAt_subtype_val h) fun g h f ↦ .trans (by
      congr!; erw [← inv_mul_apply_of_isHodgeTateFrame f]; simp [Matrix.mul_apply]) h)))
       simp)
  use r, hr, u, fun p A h ↦ (gc ⟨rfl, p⟩ h).rec fun u ↦ (⟨u, ·.imp_left fun k o γ τ t x ↦ ?_⟩)
  choose K c d using u.2.isPotCrys.exists_hasJumps γ
  rw [d, Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (κ.nodup_jumps ..)).2
    (by simpa [d _, OccursIn] using! k t ·)) (by simp [c, jumps])]
