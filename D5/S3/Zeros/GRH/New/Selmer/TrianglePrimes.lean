/- GID: D5/S3/Zeros/GRH/New/Selmer/TrianglePrimes
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/TrianglePrimes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.TrianglePrimes. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/TrianglePrimes.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.ReciprocityLaw
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.BaseLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Triangular Taylor–Wiles primes controlling the even classes. A count over the real subfield
gives reciprocity laws for even classes in Tate twists, and Taylor–Wiles primes, equally many at
every ℓ-power level, are chosen so that each new Frobenius kills the earlier laws but not the new
one, which lets the even classes be removed without any bound for them. Tame ramification governed
by Frobenius in the Kummer field of units and the inductive choice of primes at every level are
known. Related work: Gras–Munnier, Extensions cycliques T-totalement ramifiées, 1998;
Hajir–Maire–Ramakrishna, Tame Z/pZ-extensions with prescribed ramification, 2022; Taylor–Wiles,
Ring-theoretic properties of certain Hecke algebras, 1995; Darmon–Diamond–Taylor, Fermat's Last
Theorem (2.19), 1995; Dotto–Thorne, Residually reducible representations of rank 2, 2026.

This file: Taylor-Wiles primes in triangular form controlling the even classes. -/

open Function Finset Fintype Filter PadicInt WellFoundedLT Classical

/-- Let E ⊂ ℚ(ζ_N) have ≥ 4 infinite places, N + t < y, cyc(γ)^a − 1 ∣ ℓ^h for 0 < a < t, ℓ ≤ y² or
h = 0, and W contain, for all ν and g, most Frobenii near δ^(ℓ^ν)·g for some δ with cyc(δ) = 1. Then
some finite ordered J with types ty carries, for each ν ≥ 1, Taylor–Wiles places of norm ≡ 1 mod
ℓ^ν, with Frobenii in W, satisfying `IsPrimeTriangle` for γ⁻¹, yh, y²²h.

Triangular Taylor–Wiles primes controlling the even classes. -/
lemma exists_isPrimeTriangle {ℓ E} [ThePrime ℓ] [Field E] [UnramCMField E] t {N y h γ} [NeZero N]
  (hE : ∀ x, algebraMap E Ω x ∈ cycloField N) (hN : N + t < y) (hh : ∀ a ∈ Set.Ioo 0 t,
  (cycChar Ω ℓ γ ^ a).1 - 1 ∣ ℓ ^ h) (hy : ℓ ≤ y ^ 2 ∨ h = 0) (hf : 4 ≤ numInfPlaces E) {W} (hW :
  ∀ ν g, ∃ δ, cycChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g)) : ∃ J,
  ∃ (_ : Fintype J) (_ : LinearOrder J), ∃ ty, ∀ ν > 0, ∃ Q : TaylorWilesPlaces E J (ℓ ^
  ν), IsPrimeTriangle ν Q.w (Q.frobData · |>.isPlaceOver.tameGenerator) (Q.frobData · |>.frob) γ⁻¹ t
  ty (y * h) (y ^ 22 * h) ∧ ∀ j, Q.frobData j ∈ W := by
  choose p hq R using exists_detecting_points_cocycles hE ℓ
  let g i := (γ⁻¹ * i)⁻¹ * (i * γ⁻¹)
  have hD (a : Fin t) : (ℓ ^ h) ^ 3 * ∏ k ∈ {a}ᶜ, ((cycChar Ω ℓ γ ^ a.1).1 -
      (cycChar Ω ℓ γ ^ k.1).1) ∣ ℓ ^ (y * h) := by
    grw [prod_dvd_prod_of_dvd _ (fun _ ↦ ℓ.cast ^ h) fun k n ↦ ?_, pow_mul']
    simp [card_compl, ← pow_add]; grind [pow_dvd_pow, NeZero, Fin]
    wlog H : k < a generalizing a k; grind [mem_compl, neg_dvd, _=_ neg_sub]
    erw [← pow_sub_mul_pow _ H.le, ← sub_one_mul, Units.mul_right_dvd]; grind
  have h2 a k := dvd_trans (by nth_grw 1 [← hh _ ⟨k, a.2⟩, pow_succ', ← map_pow,
    ← four_dvd_cycChar_sub_one]) (hD a)
  obtain ⟨⟨⟩⟩ := exists_wellFoundedLT p, (mostFrobeniiAt E 1).nonempty_of_neBot
  let J := {e : Fin t // 0 < e.1} ×ₗ p
  use J, inferInstance, inferInstance, ⟨_, Prod.Lex.monotone_fst⟩, fun ν hν ↦ ?_
  let κ := cycCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)
  let m := (κ γ).1.valMinAbs
  -- the values of all relations at a point that fixes `μ_{ℓ^ν}`
  let H := (AddSubgroup.ofSub {v : _ → ℤ | ∃ y, κ y = 1 ∧ ∀ {d Φ T z}, IsLaw ν d Φ T z → z y = v (d,
    z)} ⟨(·.2 1 |>.cast), 1, by simp⟩ fun _ ⟨a, _, p⟩ _ ⟨b, _, q⟩ ↦ ⟨a / b, by simp [*], fun h ↦ by
    simp [← p h, ← q h, by simpa [κ, *] using h.map_conj_mul 1 (a / b) b]⟩).toIntSubmodule
  let I (j : J) := {i : Set.Iio j | i.1.1.1 = j.1.1}
  -- recursive choice of a prime `x` with a relation `z` and its exceptional set `T`
  have F j := (fix_eq (fun (j : J) f ↦ epsilon fun (x, T, z) ↦ IsSplitPlace ν x ∧ IsLaw ν j.1
    (.range fun i : I j ↦ (f _ i.1.2).1.frob) T z ∧ 2 * z x.frob ∣ ↑(ℓ ^ (y * h)) ∧
    (∀ O, ∀ c ∈ evenClasses O ∅ ν j.1, (c + c) (g j.2) = c x.frob) ∧
    (∀ i h, primeBelowPlus (f i h).1.w ≠ primeBelowPlus x.w ∧ primeBelowPlus
    x.w ∉ (f i h).2.1 ∧ (f i h).2.2 x.frob = 0) ∧ primeBelowPlus x.w ∉ T ∧ x ∈ W) j).symm
  generalize fix (α := J) _ = f at F
  replace F := fix fun j p ↦ F j ▸ epsilon_spec (by
    choose h₁ hz _ _ h₃ _ using (SetCoe.forall' (s := .Iio j)).1 p
    -- the next relation `r`, and a point `u` where the earlier ones vanish and it does not
    let B := Module.finBasis ℤ (H.map (.funLeft _ _ fun i : I j ↦ (↑j.1, (f i).2.2)))
    choose v hv hb using (B · |>.2); choose y hy k using id hv
    choose _ T₀ r hk w U hw using exists_isLaw j.1 hν hf (I := I j) (.trans
      (Submodule.finrank_le _) (by simp)) (h₁ ·) (.of_lt_imp_ne (by simp +contextual [h₃])) y
    have n : (·.2 w |>.cast) ∈ H := ⟨w, by simpa⟩
    choose c A using B.mem_submodule_iff'.1 ⟨_, n, rfl⟩
    obtain ⟨u, hu, L⟩ := prod_induction (s := {j.1.1}ᶜ) (fun a (d, _) ↦ (m ^ d - m ^ a.1) * m) (∀ v ∈
      H, · * v ∈ H) (by simp +contextual [mul_assoc]) (by simp) (fun a _ _ k@⟨b, B, q⟩ ↦ (zsmul_mem
      k (-m ^ (a.1 + 1))).rec fun a ⟨A, p⟩ ↦
      ⟨_, by simp [*], fun k ↦ (k.map_conj_mul γ b a B A).trans
      (by simp [p k, q k, m]; ring)⟩) _ (sub_mem (H.sum_smul_mem (t := univ) c fun j _ ↦ hv j) n)
    have h₄ (i : Set.Iio j) : (f i).2.2 u = 0 := by by_cases i.1.1.1 = j.1.1 <;> simp [L (hz i),
      prod_eq_zero (i := i.1.1.1), I, (by simpa [← hb] using congrFun A ⟨i, ·⟩), *]
    choose δ hδ V using hW _ _
    -- additive functions at the element that the next Frobenius approximates
    have Y (f : _ → ZMod (ℓ ^ ν)) n (hf : ∀ a b, κ a = 1 → κ b = 1 → f (a * b) = f a + f b) :
        f (δ ^ n * (g j.2 * conjGal (g j.2) * (u / conjGal u))) =
        n • f δ + (f (g j.2) + f (conjGal (g j.2)) + (f u - f (conjGal u))) := by
      clear * - hf hδ hu
      have := hf (u / conjGal u) (conjGal u)
      induction n <;> simp_all [pow_succ, add_smul, κ, cycCharMod_prime_pow_eq, g, mul_comm]
    have R {e Φ T z} (h : IsLaw ν e Φ T z) :=
      (Y z (ℓ ^ ν) (by simpa using h.map_conj_mul 1)).trans (by simp [CharP.cast_eq_zero, *,
      κ, ↓h.odd, g, mul_comm, mul_two] : _ = 2 * z u) ▸ h.isLocallyConstant.eventually_eq _
    refine (nonempty_of_mem (inter_mem V (inter_mem_inf (eventually_mostFrobenii
      ((eventually_notMem_star_notMem ℓ ∅).and (tendsto_place_comap_cofinite (algebraMap _ E)
      (Set.toFinite (T₀ ∪ ⋃ i, insert (primeBelowPlus (f i).1.w) (f
      i).2.1)).compl_mem_cofinite :)) fun _ ↦ id) ⟨_, (R r).and ((eventually_all.2 (R <| hz ·)).and
      (((selmerZ1.finite_unramified_cocycles (.of (charRep ..) (((Continuous.of_isOpen_ker κ
      Fact.out).pow _).inv.fst'.smul continuous_snd)) (placesDividing E
      ℓ).toFinite).eventually_all.2 fun x h ↦ (continuous_discrete_rng.1 h.1.1 _).mem_nhds rfl).and
      (isOpen_ker_cycCharMod.1.mem_nhds (by simp [cycCharMod_prime_pow_eq, g, mul_comm, *])))),
      .rfl⟩))).elim fun x hx ↦
      have a := hx.1
      have z := hx.2.1.1
      have n := hx.2.1.2
      have b := hx.2.2.1
      have c := hx.2.2.2.1
      have d := hx.2.2.2.2.1
      have o := hx.2.2.2.2.2
      ⟨(x, _, _),
      ⟨z.2.2, o⟩, r, by simpa [L r, ← k _ r, cycCharMod_prime_pow_eq, ← mul_assoc, map_ofNat, sq,
      m, *, κ, ((Units.isUnit _).map _).pow] using map_dvd (toZModPow ν) ((mul_dvd_mul_right
      ⟨_, rfl⟩ _).trans (h2 _ j.1.2)), fun O k hk ↦ sub_eq_zero.1 (eq_zero_of_mem_evenClasses hk
      fun u m ↦ (fun d ↦ ?_) (d _ ⟨m, ?_⟩)), by simp [h₄] at n c; simpa [Ne.symm, *]⟩
    erw [map_sub, d, Y (u <| k ·)]
    all_goals simp +contextual [hk.2.1, mem_selmerModule_iff.1 hk.1, ↓m.2, κ, charRep,
      CharP.cast_eq_zero])
  choose a d k l c e s using F
  have inj : Injective (primeBelowPlus ∘ _) := .of_lt_imp_ne (swap (c · · · |>.1))
  have hw : IsNewPlaces ν _ (f · |>.1.isPlaceOver.tameGenerator) _ := (and_assoc.1 ⟨a ·, _, _, rfl⟩)
  refine ⟨⟨(f · |>.1), ⟨inj.of_comp, by grind [isSplit_of_q_prime, primeBelowPlus_star,
    FrobeniusDatum.prime_q]⟩, (f · |>.1.isFrob.mem_ker_cycCharMod_iff
    (by simp [(FrobeniusDatum.isPlaceOver _).valuation_natCast_eq_one_iff, (a _).1]) |>.1
    (inv_mem (a _).2) |>.symm.dvd')⟩, ⟨hw, ⟨p, hy.elim (by
    simp [J]; grw [card_subtype_le, hq y (by omega) ·, Fintype.card_fin]
    nlinarith [(y ^ 21 * h).zero_le]) (by simp [·]), by tauto⟩, dvd_of_mul_left_dvd ∘' hD, fun O j z
    hz H ↦ (d j).reciprocity (J := Set.Ici j) _ inj.injOn.injective (⟨a ·, by clear * - c e; grind⟩)
    ⊥ (c · _ ·.bot_lt |>.2.2) O z ⟨IsNewPlaces.mem_selmerModule_of_tame_eq_zero (J := Set.Iio j)
    (hw ·) hz.1 (by simp +contextual [idOrConjInv, cocycle_apply_inv (mem_selmerModule_iff.1
    hz.1).1, hz.2.1, *, -smul_eq_zero]),
    hz.2⟩ (fun _ ⟨i, e⟩ ↦ e ▸ (H _ i.1.2).2 i.2) _ (k j), fun O e ↦
    ⟨by simpa [cycInv, map_ofNat] using map_dvd (algebraMap _ O) (
    .trans ⟨_, rfl⟩ (h2 _ e.2)), fun z k K ↦ ?_⟩⟩, s⟩
  choose m u _ c
    using by simpa [mem_selmerModule_iff, tateTwist, -Pi.add_apply] using add_mem k.1 k.1
  refine congrFun (sub_eq_zero.1 (R (e := e) _ (mem_selmerModule_iff.2 ⟨?_, ?_, ?_,
    (funext ?_).subst ((c.comp_continuous (continuous_const_mul γ⁻¹)).sub
    (c.comp_continuous (continuous_mul_const γ⁻¹)))⟩) fun _ h ↦
    sub_eq_zero.2 (sah m _ _ (l (e, ⟨_, h⟩) O z k ▸ K _ rfl)))) <;> simp +contextual [m, tateTwist,
    cycInv, u, cycChar_eq_one_of_mem_inertiaAbove, obeying, -Pi.add_apply] <;> intros <;> module
