/- GID: D5/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.GaloisRep.LabelUniqueness. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/GaloisRep/LabelUniqueness.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.LabelCompatibility
import D5.S3.Zeros.GRH.New.Selmer.LevelPlacesChosen
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Good forms on different unitary groups have equal traces (see
New.Trace.GoodFormTransfer).

This file: Given an injective lift to forms on a definite group, a Hecke eigensystem has at most one
primitive label at a chosen place over g. -/

open Matrix Polynomial Finset minpoly
variable {P n} (D : Data P) {s : D.RowIndex → ℤˣ} (V : Space D.E _ s) [Fintype n]

lemma Data.isEigenform_of_hasHeckePolyAt {M} {f : Gf _ n → M → ℂ} (h0 : f ≠ 0) {Q} (h : ∀ w
    (h : D.IsSplitOffLevel w), HasHeckePolyAt f w h.1 (Q w)) : IsEigenform f Q :=
  ⟨h0, (eventually_notMem_star_notMem 1 (image D.chosen ⊤)).mono
  fun w _ q ↦ ⟨_, h w ⟨isSplit_of_q_prime q, by simp_all⟩⟩⟩

/-- Let L inject level g forms on V into definite algebraic forms, make the p-part spherical with
fixed eigenvalues at split places off g, and intertwine the parabolic action at x up to ψ∘det and
distinct χ_l∘det, of orders dividing Mω. Then `Data.occurringLabels` V p x has at most one element.

This is one step toward showing that good forms on different unitary groups have equal traces. -/
lemma Data.occurringLabels_subsingleton {v : _ ↪ n} {S J χ' κ ν} {L : _ →ₗ[ℂ] LevelPlaces.LevelForm
  S J χ' κ ν} [Nonempty n] (hL : (⇑L).Injective) {p} {F : _ → _} (hF : ∀ y ∈ D.eigenPart V p, ∀ w
  (h : D.IsSplitOffLevel w), IsSphericalWith (rightRegular ..) h.1 (F w) (L y).toSmoothForm.1) x {m
  b} χ ψ (hk : ∀ y, HasParahoricType (s := m) (L y).toSmoothForm.1 (D.isConjApart_chosen.2 x x) v b
  ψ χ fun g ↦ (L (D.principalRep V (Pi.mulSingle x g) y)).1.1) (hχ : χ.Injective) (hψ : ψ ^ P.Mω D.s
  = 1) (hM : ∀ l, χ l ^ P.Mω D.s = 1) : (D.occurringLabels V p x).Subsingleton := fun _ J _ J' ↦ by
  choose! t e using fun w (h : _ ≠ w) ↦ exists_heckeSplit_eq_smul (hw := h) (π :=
    rightRegular ℂ (Gf _ n) (WeylIndex n κ → ℂ)) (F w)
  let T := faithfulChar (ResField (D.chosen x))
  obtain ⟨_ : ThePrime 2, _ : PadicIso 2, s, G⟩ := {},
    ⟨(exists_ringEquiv_extend mk_complex_eq_mk_padicAlgCl (Rat.castHom _) (algebraMap ..)).choose⟩,
    (exists_isTameExponent T (D.chosen x).isPlaceOver_placeOver _).1
  have k {c} (J : c ∈ D.occurringLabels V p x) := J.2.elim fun y a ↦
    have z := J.1.scaleRoots _ (charName_pow_eq_one hψ) (D.dvd_card_resField_sub_one x).2.1
    have H := (hk y).hasProductLabel ((AlgForm ..).subtype.domRestrict _ ∘ₗ L) (fun _ _ h ↦
      hL congr(⟨⟨$h, _⟩, _⟩)) a.2 hχ fun _ ↦
      z.2.1.not_isRoot_of_natDegree_ne_one (z.1.2.2.1 ▸ D.nat_lt_of_hasLogBound.ne')
    have E := D.isEigenform_of_hasHeckePolyAt (H.2.2.2.2 <| by simp [·]) (hF y a.1 · · |> fun b ↦
      ⟨b.1, _, rfl, e _ _ _ b⟩)
    (⟨z, (sphericalCompat_std x.2 (L y).toSmoothForm.2 E).1, fun {r} h ↦
      (Attached.isLabelledAt (r := r) (L y).toSmoothForm.2 E h H G.1).2.2 G⟩ : _ ∧ _ ∧ _)
  obtain ⟨⟨i, ⟨r, h⟩, B⟩, ⟨i', -, B'⟩, l⟩ := k J, k J', G.1.valuation_natCast_eq_one_iff.2
    (Nat.not_dvd_of_pos_of_lt two_pos D.nat_lt_of_hasLogBound ∘ (FinPlace.natCast_mem_iff_dvd _
    x.2.2.2).1)
  have e j := by simpa using congr(ιℓ (T (algebraMap _ _ (charName T $(hM j)).1)))
  refine (scaleRootsEquiv (charName T ψ)).injective (by_contra fun hN ↦
    i.isPrimitiveRoot_prod_roots.1.pow_ne_one_of_pos_of_lt NeZero.out (D.dvd_card_resField_sub_one
    x).2.2.le_pred (IsFaithfulMulChar.injective (ιℓ.injective ?_)))
  simpa [← det_eq_prod_roots_charpoly, Multiset.nsmul_singleton, roots_multiset_prod, roots_mul, e,
    Polynomial.map_prod, map_multiset_prod, Multiset.map_bind, prod_eq_zero_iff, roots_prod, aroots,
    X_ne_C, List.prod_ofFn, i.2.1.ne_zero, ← prod_pow, ← pow_mul, pow_mul', mul_pow, T, (B h).2 l]
    using (MonoidHom.mker (powMonoidHom (P.Mω D.s))).multiset_prod_mem _ fun _ ↦ by
    clear * - hN i i' e
    simp_all [eval_multiset_prod, prod_eq_zero_iff, ← eq_iff_aeval_eq_zero, IsPrimitiveLabel,
      IsLabel, scaleRootsEquiv]
    grind [IsFaithfulMulChar] ∘ imp_and.2 ⟨isRoot_of_isRoot_charpoly ((B h).1.1 l),
    isRoot_of_isRoot_charpoly ((B' h).1.1 l)⟩ ∘ isRoot_of_mem_roots
