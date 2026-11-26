/- GID: D5/S3/Zeros/GRH/New/Selmer/TwistForRows
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/TwistForRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.TwistForRows. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/TwistForRows.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.RowBalanced
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! One anticyclotomic twist makes all Selmer groups short. For finitely many irreducible blocks of Galois representations of lifts, one finite-order anticyclotomic twist ramified at new primes makes, for each of its first m powers, all Selmer groups modulo a given power of ℓ short and the ratios of twisted to untwisted Hecke values barely divisible by ℓ, which limits congruences. Twists of ℓ-power order at new primes that kill a Selmer group or keep L-values barely divisible are known. Related work: Mazur–Rubin, Diophantine stability, 2018; Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Hida, Non-vanishing modulo p of Hecke L-values, 2004. -/

open Matrix Filter Real Module Finsupp Finset CoeffRing Subalgebra RingHom
attribute [-simp] map_smul AlgHom.toRingHom_eq_coe

/-- For finitely many rows R_i and M, some m-fold twist has, for its first m powers ϑ, ψ the avatar
of ϑ⁻¹: Q auxiliary, ψ anticyclotomic, Σ v(ψ(γ) − 1) ≤ cr_ℓ over tame generators γ at Q,
Selmer length of ψR_i mod ℓ^M ≤ (10f·rank + 1)cr_ℓ, v(ιρ_p(ϑ^{±1})) ≤ 9cr_ℓ for ramified p.
Here cr_ℓ = `crudeUnit` and ρ_p = `Data.Pair.ratio` p.

One anticyclotomic twist makes all Selmer groups short. -/
lemma exists_mFoldTwist_selmerLengthLe {P} (D : Data P) ℓ [ThePrime ℓ] (ι : PadicIso ℓ) {I : Type}
    [Finite I] {r : I → Type} [∀ i, Fintype (r i)] {R : ∀ i, _ →* GL (r i)
    _} (h : ∀ i, ∃ t J, IsRow D t J (R i)) M : ∃ τ : D.MFoldTwist, ∀ n, let ϑ := τ.powTwist n
  IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D) ∧
    (∀ i, ∃ γ y, SelmerLengthLe ϑ.invAvatar (R i) ϑ.Q M γ y) ∧
    ∀ (p : D.Pair) s, p.IsRamified → ‖ιℓ (p.ratio ϑ s)⁻¹‖ ≤ exp (9 * crudeUnit ℓ D * log ℓ) := by
  choose w _ hw hℓ hi using exists_chosen_notMem_placesDividing D ℓ
  choose μ V f₁ f₃ f using fun k : Subtype _ × _ ↦ exists_isFamily hw hℓ.2 _ k.2 k.1.2
  choose O u γ β hu hβ hρ using
    (eventually_all.2 (h · |>.choose_spec.choose_spec.eventually_isBalanced hw hℓ M)).exists
  choose Q ψ a j c using exists_anticyclotomic_twist (by simp; grind) ⟨w, by grind, _,
    w.isPlaceOver_placeOver, w.isPlaceOver_placeOver.tameGenerator.2⟩
    hρ f₁ (by finiteness) hβ (fun _ _ ↦ by grw [f₃, hi, ← ellVal_le_crudeUnit D ℓ _ ⟨.refl,
    D.nat_le_of_hasLogBound⟩, pow_one]) (η := crudeUnit ℓ D) (by simp [crudeUnit]) D.m
  obtain ⟨τ, rfl, rfl⟩ :=
    (j 1 ⟨.refl, D.nat_le_of_hasLogBound⟩).elim (exists_tameChar_invAvatar_eq · <| pow_one ψ ▸ ·.1)
  simp_rw [show ∀ n, τ.invAvatar ^ n = (τ.pow n).invAvatar by simp [MonoidHom.ext_iff,
    Data.TameChar.pow, invAvatar_eq_of_artinMap_eq (artinMap_surjective ..).choose_spec]] at *
  have N n hn w c (e : τ.ψ w ^ n = 1) : False := have ⟨σ, hw, H⟩ := (j n hn).2.2
    (hw ⟨w, c⟩).2.2.elim fun B ⟨b,
      k⟩ ↦ have ⟨x, hx, j⟩ := b.exists_localArtin_eq (inv_mem b.tameGenerator.2) 0
      by simpa [ellVal, ← k, invAvatar_eq_of_artinMap_eq (b.artinAt_eq_of_localArtin_eq j ▸
        artinMap_locIdele ..), (τ.pow n).4.charUnramifiedAt e ((τ.pow n).5 _
        (τ.6 w c)) x hx] using (single_le_sum (by simp) (mem_univ ⟨w, c⟩)).trans H
  use ⟨⟨τ, by simpa using N 1 ⟨.refl, D.nat_le_of_hasLogBound⟩⟩, N⟩,
    fun ⟨n, hn⟩ ↦ have s@⟨s₁, s₂, _⟩ := j n hn
    ⟨s, fun i ↦ have ⟨⟨v, o, z⟩, y, e', _, hs⟩ := (hρ i).4
      ⟨γ i, ⟨_, norm_le_one y⟩, (c n hn i).mono ?_⟩, fun p s hp ↦ le_exp_of_log_le (by
      simpa using! neg_le_neg (le_log_of_rpow_le (by simp [NeZero.pos]) (ellVal_le_iff.1
        (f (⟨p, hp⟩, s) ⟨τ.pow n, N n hn⟩ s₁ (9 * _) ((a n hn _).trans_eq (by simp; ring))))))⟩
  rintro O' ⟨hO, ψ', k, s₇⟩; let e := (inclusion hO).1
  refine ⟨e.mapMatrix.1.comp (u i), _, e y, rfl, hu i, k, by simp [twistRep, map_smul', e', by
      simpa [← k] using s₂.eq_one_of_mem_inertiaAbove _ ⟨v, by clear * - s₁ o; simp at *; grind,
        z⟩], by simpa using hs.map e, cycChar_eq_one_of_mem_inertiaAbove ⟨v, o.2, z⟩,
    s₇.trans' (normLength_mono (length_mono ?_))⟩
  rintro x ⟨⟨h⟩⟩; use mem_obeying.2 ?_
  let := e.toAlgebra; have := (inclusion.faithfulSMul hO).to_isTorsionFree
  have := Finite.right ℤ_[ℓ] O.1 O'.1
  rintro _ (H | ⟨_, ⟨_, ⟨v, rfl⟩, f, hf, rfl⟩ | rfl, rfl⟩)
  exacts [mem_obeying.1 h _ (.inl (by simpa [unionWithConj] using! H)), mem_obeying.1 h _ (.inr ⟨_,
    ⟨v, rfl⟩, mapRel _ f, fun z a ↦ funext fun i ↦ (forall_dual_apply_eq_zero_iff O _).1 fun l ↦ by
    simpa [← smul_toAlgebra, mapRel, linearCombination, ↓sum_mapRange_index, sum] using congrFun
      (hf _ (crysCocycles.map a ((l.restrictScalars _).compLeft _) fun g ↦ by simp [funext_iff,
      twistRep, mulVec, dotProduct, ← smul_toAlgebra, by simpa [← k] using
      (s₂.eq_one_of_mem_decompGroup v.2 v.1.isPlaceOver_placeOver g.2)])) i,
    mapDomain_mapRange _ _ _ _ (map_add _)⟩), by simpa [mapRel]]
