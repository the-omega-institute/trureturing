/- GID: D5/S3/Zeros/GRH/New/Selmer/ReciprocityLaw
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/ReciprocityLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.ReciprocityLaw. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/ReciprocityLaw.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cyclotomic.OddSha.OddShaBound
import D5.S3.Zeros.GRH.New.Selmer.TiltingLemma
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Triangular Taylor–Wiles primes controlling the even classes (see
New.Selmer.TrianglePrimes).

This file: A value of an even class vanishes if all its cyclic images vanish. Odd Kummer-type maps
with reciprocity law against even classes, primitive, with prescribed zeros. -/

/-- Let c lie in `evenClasses` for the twist −e modulo ℓ^r. If b is killed by every additive
map u to ℤ/ℓ^r for which u∘c is a continuous cocycle for cyc^{−e}, then b = 0. -/
lemma eq_zero_of_mem_evenClasses {ℓ} [ThePrime ℓ] {E} [Field E] [UnramCMField E] {O S r e b c} (k :
  c ∈ evenClasses (E := E) O S r e) (h : ∀ u : _ →+ ZMod (ℓ ^ r),
  (u <| c ·) ∈ Z1 (charRep _ (cycCharMod Ω (ℓ ^ r) ^ e)⁻¹) → u b = 0) : b = 0 :=
  QZ.eq_zero_of_forall_hom_eq_zero ((QZ.bijective_ofZMod_comp (funext <| nsmul_quot_eq_zero ∘' ·)
  ).2.forall.2 fun u ↦ by simp [h u ⟨(k.1.2.comp _).continuous, by simp [tateTwist, cycInv, charRep,
  CharP.cast_eq_zero, ↓← map_pow, ← map_inv, mem_selmerModule_iff.1 k.1, map_cycChar_smul u r]⟩])

open Classical Finset Function NumberField selmerZ1 Subgroup IsCMField
variable {ℓ} [ThePrime ℓ] {E : Type} [Field E] [UnramCMField E] (r : ℕ) (w : FinPlace E)

/-- A triple (w, A, σ): w a place of prime norm not above ℓ, A a place of Ω over w, σ a
geometric Frobenius at A fixing μ_{ℓ^r}. -/
def IsSplitPlace (x : FrobeniusDatum E) := ↑ℓ ∉ x.w.1 ∧ cycCharMod Ω (ℓ ^ r) x.frob = 1

/-- The prime of the maximal real subfield E⁺ below w. -/
noncomputable abbrev primeBelowPlus := w.below (maximalRealSubfield E)

/-- A locally constant z with values in ℤ/ℓ^r, on the kernel of cyc mod ℓ^r an odd homomorphism
of twist e + 1, with a reciprocity law off the finite set T bounding the ramification of
even cocycles of twist −e that vanish on Φ. -/
structure IsLaw e (Φ : Set _) (T : Finset _) (z : Gal(Ω/E) → ZMod (ℓ ^ r)) where
  isLocallyConstant : IsLocallyConstant z
  map_conj_mul g a b : cycCharMod Ω (ℓ ^ r) a = 1 → cycCharMod Ω (ℓ ^ r) b = 1 →
    z (g * a * g⁻¹ * b) = cycCharMod Ω (ℓ ^ r) g ^ (e + 1) * z a + z b
  odd b : cycCharMod Ω (ℓ ^ r) b = 1 → z (conjGal b) = -z b
  reciprocity {J : Type} [Fintype J] (x : J → _) : Injective (primeBelowPlus <| x · |>.w) → (∀ j,
    IsSplitPlace r (x j) ∧ primeBelowPlus (x j).w ∉ T) → ∀ j, (∀ i ≠ j, z (x i).frob = 0) → ∀ O,
    ∀ c ∈ evenClasses O (.range (x · |>.w)) r e,
    (∀ g ∈ Φ, c g = 0) → ∀ n : ℕ, 2 * z (x j).frob ∣ n → n • c (x j).isPlaceOver.tameGenerator = 0

lemma primeBelowPlus_star : primeBelowPlus (star w) = primeBelowPlus w := by
  ext x; exact congr($(Subtype.ext (mem_maximalRealSubfield_iff_star_eq.1 x.1.2)) ∈ w.1)

/-- Let E be stably unramified with ≥ 4 infinite places, r ≥ 1. Given Frobenii x_i fixing μ_{ℓ^r},
at degree-one places off ℓ over distinct primes of E⁺, and at most as many y_i, some function z with
`IsLaw` kills all y_i and takes a unit value on an element fixing μ_{ℓ^r}. -/
lemma exists_isLaw {r} e (hr : 0 < r) (hf : 4 ≤ Fintype.card (InfinitePlace E)) {I k}
  [Fintype I] (hI : k ≤ Fintype.card I) {x : I → FrobeniusDatum E} (hx : ∀ i, IsSplitPlace r (x i))
    (i : Injective (primeBelowPlus <| x · |>.w)) (y : Fin k → _) : ∃ z T, IsLaw r e (.range
  (x · |>.frob)) T z ∧ (∀ i, z (y i) = 0) ∧ ∃ g, IsUnit (z g) ∧ cycCharMod Ω (ℓ ^ r) g = 1 := by
  let K := maximalRealSubfield E
  let res : Gal(Ω/E) →* _ := AlgEquiv.restrictScalarsHom (maximalRealSubfield E)
  let c₀ : Gal(Ω/maximalRealSubfield E) := {cmConj with commutes' x :=
    (mem_maximalRealSubfield_iff_star_eq.1 x.2 ▸ cmConj_algebraMap x.1 :)}
  obtain ⟨⟨⟨⟨ce, ij⟩, _⟩, -, ix⟩, cs : IsComplexConj c₀, -, op⟩ := (@is_quadratic E _ _ _).2 ▸
    isClosedEmbedding_galois_restrict res, isComplexConj_cmConj,
    isOpenEmbedding_galois_restrict res (by tauto)
  have N c (h : IsComplexConj c) :
    c ∉ res.range | ⟨s, e⟩ => (e ▸ h).false_of_isTotallyComplex (c := s)
  choose p o using fun σ ↦ show ite (σ ∈ res.range) σ (σ * c₀) ∈ res.range by
    split <;> simp [mul_mem_iff_of_index_two, *]
  obtain ⟨cp, _, p1⟩ := ce.continuous_iff.2 ((continuous_congr o).2 (continuous_id.if
    (op.frontier_eq ▸ by simp) (by fun_prop))), normal_of_index_eq_two ix,
    (ij <| (o _).trans <| ite_eq_left ⟨·, rfl⟩)
  have μ g h : p (g * h) = p g * p h ∨ p (g * h) = p g * conjGal (p h) := by
    simp only [← ij.eq_iff, map_mul, mul_mem_iff_of_index_two, *,
      show res (conjGal (p h)) = c₀ * res _ * c₀ from rfl]; grind [cs.mul_self]
  have u W g : g ∈ inertiaAbove W → p g ∈ inertiaAbove (primeBelowPlus ⁻¹' W) := fun ⟨v, a, A, hA,
    h⟩ ↦ by
    obtain ⟨⟨w, hw, rfl⟩, e⟩ := hA.exists_above (L := E), o g; split at e; exact ⟨w, a, A, hw,
      (e ▸ h :)⟩
    cases StablyUnram.exists_isUnit_sub_star.elim fun y u ↦ w.1.notMem_of_isUnit u ((hw _).1 (by
      simpa [← (by simpa [res, c₀] using congr($e (algebraMap E Ω y)) :)] using
        h.2 _ (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (star y)⟩)))
  let κ := MonoidHom.mk' (cycChar Ω ℓ ∘ p) (by cases μ · · <;> simp [*])
  have hu g h : κ g = 1 :=
    cycChar_eq_one_of_mem_inertiaAbove (by simpa using! u (placesDividing _ ℓ)ᶜ g h)
  let ρ := (Units.map (PadicInt.toZModPow r).1).comp κ
  let V := OpenNormalSubgroup.mk ⟨res.range ⊓ (cycCharMod Ω (ℓ ^ r)).ker,
    op.inter isOpen_ker_cycCharMod.1⟩
  have U s (h : cycCharMod Ω (ℓ ^ r) s = 1) : res s⁻¹ ∈ V := ⟨⟨_, rfl⟩, by simpa⟩
  have v : V ≤ ρ.ker | _, ⟨⟨s, rfl⟩, h⟩ => by simpa [ρ, κ, *, cycCharMod_prime_pow_eq] using! h
  have D (x : FrobeniusDatum E) : IsFrob x.valRing (primeBelowPlus x.w).q (res x.frob⁻¹) :=
    ((x.prime_q.pow_eq_iff.1 ((primeBelowPlus x.w).1.absNorm_pow_inertiaDeg _)).1 ▸ x.isFrob :)
  obtain ⟨⟨S, hS⟩, hm, l, w⟩ := (placesDividing _ ℓ ∪ .range (primeBelowPlus <| x
    · |>.w)).toFinite.exists_finset, dvd_pow_self ℓ hr.ne', @NeZero.one_le ℓ _, isOpen_mono v V.1.2
  choose P hP η Φ using fun u : FinPlace _ ↦ show ∃ A, IsPlaceOver A u ∧ (u ∈ S → u ∉ placesDividing
    _ ℓ → ∃ i, IsFrob A u.q (res (x i).frob⁻¹)) from if h : ∃ i, primeBelowPlus (x i).w =
    u then h.rec fun i e ↦ e ▸ ⟨_, (x i).isPlaceOver.isPlaceOver_below, by tauto⟩ else ⟨_,
    u.isPlaceOver_placeOver, by simp +contextual [*]⟩
  let M := DiscreteModule.of (charRep (ZMod (ℓ ^ r)) (ρ ^ e)⁻¹)
    (((Continuous.of_isOpen_ker _ w).pow e).inv.fst'.smul continuous_snd)
  generalize m : M = A
  have t {g} (h : ρ g = 1) : A.ρ g = 1 := m ▸ by ext; simp [M, charRep, h]
  have t' {g} (h : κ g = 1) := @t g (by simp [ρ, h])
  have L (B := A) (r : ∀ {g}, A.ρ g = 1 → B.ρ g = 1) u (h : u ∈ S) : (d0 (B.restrictTo (decompGroup
    _ (P u))).ρ).range ≤ .pi {g | ↑ℓ ∈ u.1 → κ g = 1} ⊥ := fun _ ⟨m, J⟩ ↦ J ▸ fun g a ↦
    sub_eq_zero.2 congr($(r (if b : _ then t' (a b) else t ((hP _).decompGroup_le (Φ u h b) w
    (by simp [ρ, hu · ⟨u, b, _, hP u, ·⟩]) (v (U _ (hx _).2)) g.2))) m)
  have hu' g (h : g ∈ inertiaAbove Sᶜ) := t' (hu g (h.imp (by simp +contextual [hS])))
  have C c (h : IsComplexConj c) := t' (by simp [IsComplexConj.cycChar_eq_neg_one, *] :
    cycChar Ω ℓ (res (p c)) = 1)
  have c := exists_split_primes_relations hu' hP _ (L A id) @C A V (congr($(t <|
    @v · ·) ·)) (fun _ ↦ (·.2)) (N _ · ·.1)
  extract_lets Y at c
  choose q ι _ Q _ s γ π T hT hST hπ _ d H using c
  let Z := (smulAddHom _ (Y (.range s.v)) ℓ).ker
  -- the count of the `ℓ`-torsion cocycles; for it the module `A = M` is kept abstract
  have B : .card Z * ℓ ^ (k + 1) ≤ ℓ ^ Fintype.card ι := by
    let W := A.submodule (ℓ • LinearMap.id).ker fun g a h ↦ by simpa using congr(A.ρ g $h)
    obtain ⟨_, hM⟩ : Finite W ∧ .card W = ℓ := by subst m; use inferInstance,
      (IsAddCyclic.card_nsmulAddMonoidHom_ker ..).trans (by simp [M, Nat.gcd_eq_right hm])
    have r {g} (h : A.ρ g = 1) : W.ρ g = 1 := by ext; simp [W, h]
    let ψ := ((DistribMulAction.toAddAut _ W).comp W.ρ.asGroupHom).prod (cycCharMod Ω ℓ)
    have u : V ≤ ψ.ker
      | _, h => Prod.ext (by ext; exact congr($(r (t (v h))) _)) (cycCharMod_eq_one_of_dvd hm h.2)
    let O := OpenNormalSubgroup.mk ⟨_, isOpen_mono u V.1.2⟩
    have G {D : Subgroup _} [IsClosed (SetLike.coe D)] := exists_procyclic_generator (κ.domRestrict
      D) ((continuous_cycChar ℓ).comp cp |>.comp continuous_subtype_val)
      (four_dvd_cycChar_sub_one <| p ·)
    obtain ⟨γ, hγ⟩ := @G _ O.isClosed
    choose v n _ B R φ Q X _ using fun g : O × _ ↦ chebotarev (V.1.2.preimage (continuous_const_mul
      g.1.1)) ⟨g.1⁻¹, by simp⟩ (((finite_natCast_mem q).union (Set.finite_range s.v)).insert g.2)
    let t := (cond · (γ, ofNonempty) (dite _ (⟨c₀, ·⟩) fun _ ↦ 1, v (γ, ofNonempty)))
    simp [-Prod.forall] at n
    let s' : SplitPlaces ℓ q _ O _ := ⟨fun _ h ↦ congr($h.2), hm.trans s.dvd_level, _, s.4.sumElim
      (Bool.injective_iff.2 (n (t _)).1) (by simp [n]), by simp [s.level_notMem, n],
      Sum.rec s.valRing (B ∘ t),
      Sum.rec s.isPlaceOver (R ∘' t), Sum.rec s.φ (φ ∘ t), Sum.rec (s.isFrob · |>.imp id (u ·))
      fun _ ↦ ⟨X _, (mul_mem_cancel_left (by simp)).1 (u (Q _))⟩, by congr!, (s.inertiaGroup_le
      · · |>.trans u), fun F _ h ↦ s.principal_sup_idelesUnitOff F (@h · · <| inclusion u ·)⟩
    have c : W.FiniteKilledFixedInj ℓ O 1 0 := ⟨‹_›, by simp [← hM], fun _ h ↦ (congr($h.1 ·)),
      fun _ _ ↦ by simp⟩
    have B := (card_mul_pow_le (r <| hu' · ·) hP _ (L W r) (r <| C _ ·) s'
      (s'.card_trivialised_of_isHigmanProjective c (c.isHigmanProjective_of_coprime (.of_dvd_right
      (index_ker ψ ▸ card_subgroup_dvd_card _) (by simp [← sq, l, ← Nat.card_congr
      (MulAutMultiplicative W).1, Nat.totient_prime Fact.out, (hM ▸ (isCyclic_of_prime_card (α :=
      Multiplicative W) hM).card_mulAut :)]))) fun y m f ↦ by
      let F := MulAction.stabilizer Gal(Ω/K) y.toMul
      have H : V ≤ F := d y (hm.choose_spec ▸ mul_nsmul y .. ▸ nsmul_mem (m.imp id (· <|
        inclusion u ·)) _) (f <| .inl ·)
      have e j := (mul_mem_cancel_right (f (.inr j))).1 (H (Q _))
      simpa using! hγ (F.subgroupOf _) (fun g (a : cycChar Ω ℓ (p g) = 1) ↦ by
        have b := o g ▸ U (p g)⁻¹ (by simp [a, cycCharMod_prime_pow_eq])
        split at b; exacts [H b, (F.mul_mem_cancel_right (by
          simpa [t, (mul_mem_cancel_left g.2).1 (u b)] using e false)).1 (H b)]) (isOpen_mono H
        V.1.2).preimage_val (e true)).1 hT).trans' (mul_le_mul_left (@Nat.card_le_card_of_injective
      Z _ ((finite_unramified_cocycles W).subset fun _ ↦ (·.1)) (fun x ↦ ⟨fun g ↦ ⟨_,
      congr($(x.2).1 g)⟩, x.1.2.imp (.imp (.imp (·.subtype_mk _) (Subtype.ext <| · · ·)) fun b ↦
      (Subtype.ext <| b · <| ·.imp (by simp +contextual [s']))) (.imp (Subtype.ext <| · · · · ·)
      (Subtype.ext <| · · ·))⟩) (by simp [Injective, funext_iff])) _)
    grw [S.prod_le_prod' (g := fun v ↦ ite (↑ℓ ∉ v.1) 1 (.card W)) fun v _ ↦ ?_, hM,
      card_infinitePlace_eq_card_infinitePlace, ← hf, ← S.card_filter_add_card_filter_not (↑ℓ ∉
      ·.1), ← hI.trans (card_le_card_of_injOn _ ?_ i.injOn)] at B
    simpa [prod_ite, pow_add, pow_succ, ← mul_assoc, add_right_comm _ _ 4, NeZero.pos] using B
    simp [hS, (hx _).1]
    split; simp [Pi.bot_def, *, inf_eq_left.2]
    exact G.elim fun γ hγ ↦ Nat.card_le_card_of_injective _ (.of_ker
      ((LinearMap.proj γ).domRestrict _) fun ⟨_, x⟩ ↦ Subtype.ext ∘ funext ∘
      hγ (cocycleKer (W.restrictTo _).ρ x.2.2) (x.1 · ∘ const _) (x.2.1.1 {0} (by simp)))
  subst m
  choose n a n2 j β using exists_primitive_relation (.mk' (·.1 ∘ γ) (by bound)) (π ∘ res ∘ y⁻¹) hr B
    ((finite_unramified_cocycles M).subset inf_le_left)
  obtain ⟨α, ad, law⟩ := H (.mulRight <| n ·) (a ⟨·, ·⟩)
  exact ⟨(n <| π <| res ·⁻¹), T, ⟨(hπ.comp n).comp_continuous (by fun_prop), fun g a b h h' ↦ by
    simpa [M, charRep, ρ, ↓map_inv, κ, *, cycCharMod_prime_pow_eq, pow_succ', add_comm] using!
      ad (res g) _ (U b h') _ (U a h) 1, fun b h ↦ by
    simpa [by simpa using (ad 1 1 · 1 · 1), *, cs.cycCharMod_eq_neg_one, ← map_inv
      conjGal, -map_inv, inv_eq_iff_mul_eq_one.2 cs.mul_self] using! (ad c₀ 1 V.one_mem _ (U b
      h) 1), fun w i h j z O c Z φ _ ⟨y, b⟩ ↦ eq_zero_of_mem_evenClasses Z fun f ⟨l, fs⟩ ↦ by
    obtain ⟨⟨⟨h1, h2, -⟩, h3, h4⟩, F⟩ := Z.imp mem_selmerModule_iff.1 id,
      (w · |>.isPlaceOver.isPlaceOver_below (K := K))
    choose δ hδ using exists_isTameGeneratorFor Gal(Ω/K) (ℓ ^ r) ∘' F
    let X : Z1 M.ρ := ⟨_, l.comp cp, (by cases μ · · <;>
      simp [M, charRep, ρ, κ, *, -h1, cycCharMod_prime_pow_eq])⟩
    have x4 g a : (X + X).1 g = 0 := h2 _ ((u (placesDividing _ ℓ ∪ .range (primeBelowPlus <|
      w · |>.w))ᶜ g a).imp fun _ ↦ .imp (mt (by
      clear * -; simp [placesDividing]; grind only [primeBelowPlus_star])) id) |> (by simp [X, ·])
    choose m hm using (hδ j).exists_apply_eq_nsmul (F j) (by simp [(w j).w.2.pow_mem_iff_mem, *,
               (h j).1.1]) (τ := res _) (w j).isPlaceOver.tameGenerator.2 X.1 (X.2.1.1 · ⟨⟩)
      (by simp [X.2.2, t' <| hu · ⟨_, by simp [placesDividing, (h j).1.1], _, F j, ·⟩])
    have := (law _ _ _ δ i (⟨(h _).2, F _, hδ ·, D _, U _ (h _).1.2⟩) _ ⟨⟨(X + X).2, (x4 · <|
      ·.imp (by simp +contextual [hS]))⟩, fun u a ⟨g, d⟩ b ↦ if c : _ then by
      simpa [X, t' (b c), h4 (p (g * g)) ⟨_, (hP u).valuation_natCast_lt_one_iff.2 c,
        ((o _).trans (ite_eq_left (mul_self_mem_of_index_two ix g)) ▸ mul_mem d d :),
          κ.ker.mul_mem (b c)
        (b c)⟩] using (X.2.2 g g).symm else DiscreteModule.Z1.eq_zero_on_decompGroup _ (hP u) (Φ u a
      c) (x4 · ⟨u, (·.elim c fun ⟨j, e⟩ ↦ (h j).2 (e ▸ hST a :)), _, hP u, ·⟩) (by simp [X, *,
      cocycle_apply_inv h1, -map_inv]) g d, fun g h ↦ by
      simpa [C g h, h.mul_self ▸ X.2.2 g g] using X.2.2 1 1⟩).symm.trans
      (Fintype.sum_eq_single j (by simp [z · ·, -map_inv]))
    simp [X, p1] at this hm; simp [↓map_nsmul, b, hm]
    linear_combination -m * y * this⟩, n2, (s.isFrob j).2.elim fun ⟨g, e⟩ a ↦
    ⟨g⁻¹, by simpa [e, β] using congr(IsUnit ($(α j) 1)), by simpa [← e] using! a⟩⟩
