/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Global/CMNorms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Global/CMNorms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Global.CMNorms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Global/CMNorms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.UpsilonValues
import D5.S3.Zeros.GRH.Lib.Adelic.Reduction.FirstMinimum
import D5.S3.Zeros.GRH.Lib.ClassField.Global.NormTheorems
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence, norms
(known result; see Lib.ClassField.Global.AlbertBrauerHasseNoether).

This file: Class field theory of a CM extension: real ideles modulo norms, signs, splitting
character. -/


open NumberField InfinitePlace Classical Complex ComplexOrder Finset QZChar IsCMField IsTotallyReal
  SplittingChar Units Algebra FinPlace Function
section

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

@[local simp] lemma finAdeleIncl_adeleNorm_eq_mul_star : ∀ y, finAdeleIncl (maximalRealSubfield L) L
  (adeleNorm _ _ y) = y * star y := denseRange_algebraMap_finAdele.eq
  (by simp [norm_maximalRealSubfield_eq_mul_star, Subfield.algebraMap_ofSubfield])

end

attribute [local simp] finAdeleIncl_adeleNorm_eq_mul_star

variable {L : Type} [Field L] [CMType L]

lemma bijective_cmType_restrict : (Φ · |>.comp (maximalRealSubfield L).subtype).Bijective :=
  .of_comp_left (by simpa only [comp_def, ← comap_mk, mk_Φ] using! (equivInfinitePlace L).bijective)
  (LeftInverse.injective (embedding_mk_eq_of_isReal <| complexEmbedding_isReal ·))

/-- L CM. A conjugation-invariant finite idele t is x z z̄, x ∈ L^×, with any signs of product 1
if t = 1. For real a ∈ L^×, a z z̄ = 1 forces ∏Φ_w(a) > 0. A splitting character is −1 on
the uniformiser at every w = w̄. -/
lemma exists_eq_principalIdele_mul_norm : (∀ {t}, star t.1 = ↑t → ∀ s : InfinitePlace L → ℤˣ, ∏ w,
  s w = 1 → ∃ x z, (t = 1 → ∀ φ, 0 < s (mk φ) * φ x.1) ∧ t = principalIdele x * (z * star z)) ∧
  (∀ a z, star a.1 = ↑a → principalIdele (a : Lˣ) * (z * star z) = 1 → 0 < ∏ w, Φ w a.1) ∧
  ∀ [SplittingChar L] (w : FinPlace L), star w = w → υ.atUnif w = -1 := by
  let K := maximalRealSubfield L
  algebraize [Ω.fieldEmb L]
  obtain ⟨χ, _⟩ := exists_char_of_isCyclic (K := K) (isQuadraticExtension L).isCyclic
  have v {P} := by simpa [pair_complexConj_eq_univ] using (forall_mem_insert 1 {complexConj L} P).2
  let f := (abelianLift χ).comp (artinMap _)
  let J := Units.map (finAdeleIncl K L).1
  have N {x z} : J (principalIdele x * z.map (adeleNorm ..)) = principalIdele (x.map K.subtype) *
      (z * star z) := by aesop
  have S b : f (principalIdele b) = 1 ↔ 0 < ∏ w, Φ w b.1.1 :=
    ((RingHom.equivRatAlgHom ..).bijective.comp bijective_cmType_restrict).prod_comp
    (· b.1) ▸ by simp [char_artinMap_principalIdele_eq_one_iff fun c h e ↦
    h.false_of_isTotallyComplex (c := (⟨c, e⟩ : ker χ)), f, lt_def, ← norm_eq_prod_embeddings]
  have A b {s : InfinitePlace L → ℤˣ} (hs : univ.prod s = 1) : ∃ x y, (b = 1 → ∀ φ,
      0 < s (mk φ) * φ x.1) ∧ b = principalIdele x * .map (adeleNorm K L) y := by
    let r := ite (f b = 1) s (Pi.mulSingle ofNonempty (-1))
    have ⟨y, hy⟩ := denseRange_Φ.exists_mem_open (isOpen_set_pi Set.finite_univ fun w _ ↦
      isOpen_lt continuous_zero (continuous_re.const_mul (r w))) ⟨(r ·), by simp⟩
    have ha φ : 0 < r (mk φ) * φ (trace K L y) := by cases Φ_eq_or φ <;> simpa [K,
      trace_maximalReal_eq_add_star, ← (RingHom.congr_fun ‹_› y), lt_def, field] using hy _
    lift trace K L y to Kˣ using .mk0 _ (by simp [·] at ha) with a
    have ⟨x, z, c⟩ :=
      (char_artinMap_eq_one_iff χ (b / principalIdele a)).1 ((f.ker.mul_mem_iff_of_index_two
      ((isQuadraticExtension L).2 ▸ index_ker_char_artinMap ..)).2 ∘ by unfold r; split <;> simp <;>
      norm_cast <;> simp_all [asymm] <| univ.prod_pos fun w _ ↦ ha (Φ w))
    use a * x, z, fun m φ ↦ by simpa [r, m, field] using mul_pos (ha φ) (zero_lt_real.2 (c.1
      (complexEmbedding_isReal (φ.domRestrict K)).embedding)), by simp [mul_assoc, ← c.2]
  have I := (J.ker_eq_bot (map_injective (adeleMap_injective _))).le
  refine ⟨@fun t c s p ↦ (mem_range_finAdeleIncl_iff.2 (v (adeleMap_id _) c)).elim fun b e ↦
    (ext e : J ((e ▸ t.isUnit :).of_map (algebraMap ..)).unit = t) ▸ (A _ p).elim fun x ⟨y, p⟩ ↦
    ⟨_, _, p.1 ∘ @I _, p.2 ▸ N⟩, fun a z c e ↦
    (S (mk0 ⟨_, mem_maximalRealSubfield_iff_star_eq.2 c⟩ (by simp [Subtype.ext_iff]))).1 (by
    simpa [f] using congrArg f (I (N.trans (by exact ext congr(↑$e))))), fun w c ↦
    by_contra fun k ↦ ((FinPlace.isPlaceOver_placeOver _).split_completely
    (((FinPlace.isPlaceOver_placeOver _).artinAt_trivial_iff_decompGroup_le χ).1 fun x ↦
    (A (locIdele _ x) prod_const_one).elim fun a ⟨y, d⟩ ↦ ?_) w rfl).2 _ (complexConj_ne_one L) c⟩
  rcases upsilon_atUnif_mul_star w,
    (upsilon_eq_atUnif_zpow w (x := (a.map K.subtype).map toAdele.1 * (finIdeleIncl y * star
    (finIdeleIncl y))) fun u e ↦ by erw [← congr($(N).1 u), ← d.2, adeleMap_apply _ rfl,
    locIdele_of_ne (exists_gal_comap_eq ·.symm |>.elim (v e.symm (by bound)))]; simp).symm
  simp_all [f, upsilon_toAdele, υ_star, field, prod_pos, prod_ne_zero_iff, ← artinMap_locIdele]
