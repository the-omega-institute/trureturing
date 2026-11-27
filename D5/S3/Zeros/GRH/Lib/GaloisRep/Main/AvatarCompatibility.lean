/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AvatarCompatibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/AvatarCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.AvatarCompatibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/AvatarCompatibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.TameExponent
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.SeedRepresentation
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.AttachedDeterminant
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Galois representations attached to forms on definite unitary groups. For the
standard definite form and a CM field with enough roots of unity, Hecke polynomials are l-adically
close to characteristic polynomials at most Frobenius elements and kill Frobenius at spherical split
places. The proof uses l-adic limits, one quadratic descent and theta lifts for even rank, with no
eigenvariety or patching. Source: Chenevier, Harris, Construction of automorphic Galois
representations II, Camb. J. Math. 1 (2013), Thm 3.2.3; with Labesse, Changement de base CM et
séries discrètes (2011), Cor. 5.3, and Barnet-Lamb, Gee, Geraghty, Taylor, Potential automorphy and
change of weight (2014), Thm 2.1.1.

Known result: ℓ-adic avatar of an algebraic Hecke character and its local behaviour. Existence is
given over totally complex fields. For the CM fields used here, the behaviour at places above ℓ is
read from the rank-one case of the Galois representations built in this file
(`sphericalCompat_of_odd`) rather than from Lubin–Tate theory. Source: J.-P. Serre, Abelian ℓ-adic
representations and elliptic curves, 1968, II–III (locally algebraic = Hodge–Tate, Tate's theorem);
B. Conrad, Lifting global representations with local properties, App. B (crystalline case).

This file: Galois representations for all eigenforms of odd rank, by l-adic limits of seeds. Descent
of the Galois representation along quadratic steps, replacing the patching lemma. Local-global
compatibility of l-adic avatars of algebraic Hecke characters at all finite places. -/

open Matrix Polynomial Filter Finset Metric Nat Gf NumberField Ideal Subgroup Module.End

attribute [local simp] offPartComap

/-- The statement `SphericalCompat` on Galois representations attached to eigenforms holds at u
in odd rank a, for stably unramified CM fields E ⊃ ℚ(√−D), D ≡ 3 mod 4, if u and all places
above ℓ lie over split primes of ℚ(√−D) (`IsSplitPrimeToDisc`). -/
lemma sphericalCompat_of_split {ℓ E a D} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E]
  [EmbeddedNumberField E] [StablyUnram E] (ha : Odd a) [HasQuadSubfield D E] {u} (sp : ∀ v,
  ↑ℓ ∈ v.1 ∨ v = u → IsSplitPrimeToDisc (v.below (QuadField D))) :
  SphericalCompat E (Fin a) a u := fun P κ f hf he ↦ by
  have ⟨z, l, _⟩ : ∃ z, ↑ℓ ∈ z.1 ∧ (↑ℓ ∈ u.1 → u = z) := by grind [FinPlace.exists_natCast_mem E ℓ]
  have A a := ((sp z (.inl l)).exists_place_above_ne a u).imp fun x h ↦ (exists_comap_intQpBar_eq
    (p := ℓ) (x.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.2
    (by simpa [l] using congr(↑ℓ ∈ $(h.1).1)))).imp fun e H ↦ (H ▸ isPlaceOver_placeOfEmb e).unique
    x.isPlaceOver_placeOver |> fun k ↦ (fun {θ} (o : InducesPlacePair x θ) ↦ (⟨h, k, o, by
    grind [star_star, InducesPlacePair]⟩ : ∃ _ _ _, IsSplitPrimeToDisc (x.below (QuadField D)) ∧
    ¬InducesPlacePair u θ)) (inducesPlacePair_mk _ (.comp ιℓ.symm
    (e.comp (algebraMap ..))) (by aesop))
  obtain ⟨_, v, _, B, -, o', l, n'⟩ := NeZero.of_pos ha.pos, A u
  obtain ⟨⟨x, θ, C, hθ, o, n₂, n⟩, ⟨ϑ, ty, c⟩, g, i, F⟩ := A v, exists_isCuspidalType v a,
    by simpa [funext_iff] using he.1
  let V := offPartComap n₂.star_ne ⟨_, hf.1⟩
  have ⟨S, h, h₂⟩ := exists_inf_trivialOn_le V.2
  let K := .comap _ (continuous_atPlace v) ⟨localCongruence _ v 0,
    isOpen_localCongruence⟩ ⊓ offPartComap l.star_ne V ⊓ ⟨_, isOpen_Kf⟩
  let χ : K.1 →* _ := ϑ.comp (.mk' (⟨_, ·.2.1.1⟩) (by simp [Subtype.ext_iff]))
  obtain ⟨⟨s, t, N, H, y, m⟩, O, L, _, _⟩ := isApproximatingMonoid_of_mem_closure (S :=
    {F | ∃ r Q μ M g w q k J, _}) (fun h ↦ F (by simpa [padicModel, ← map_mul, ← Pi.zero_def] using
    congr((weylRep _ κ.2 (padicComponents g) *ᵥ ($h ⟨g, ·⟩)) i))) (padicModel_mem_uniformClosure _
    ⟨by aesop, K.2⟩ (.mono (isOpen_localCongruence.preimage_of_continuous.mem_nhds (by simp))
    fun _ ↦ c _) {v | ¬_} ⟨_, hf⟩ (fun d h ↦ by simpa [V, χ, o.atPlace_eq_one, o'.atPlace_eq_one, *]
    using d.2.1.2) fun μ _ g j q M N ↦ Submodule.mapsTo_span (f := (padicModel ..).domRestrict _)
    (fun g i ↦ forall_eq'.1 fun F w ↦ i.2.rec fun P e ↦ (exists_rep_of_cuspidal_type ha g.2
    e (S.mem_insert_self v) l ty (fun j ↦ congr($(i.1 ⟨_, by simpa [K] using! j.2.1⟩).1).trans (by
    simp [χ])) ((h x (inf_le_of_right_le (by simp [V, LE.le, ← range_atSplit n₂.star_ne]))).rec (by
    clear * - B C; grind)) hθ (fun d h _ a _ b e ↦ q _ n d h a b (by simp [Finsupp.weight_eq_sum,
    Finsupp.degree_eq_sum, mul_sub, mul_add, ← sum_mul, ← cast_sum] at *; grind only))
    (List.mem_map_of_mem <| mem_range.2 ·.2) u (by simp +contextual [*])).rec (⟨·, P, μ, M, g, w, e,
    N, j, ·⟩)) (have := (stdSpace ..).finite_formTranslation_levelSpace μ K.2 χ
    (fun _ o ⟨k, a, b⟩ ↦ by simp at b; simp [χ, *, o ⟨k, by simpa [b] using h₂ ⟨a, mem_trivialOn.2
      b.2⟩, a⟩]) |> fun J ↦ le_span_isSphericalOff (levelSpace _ _ χ) J (fun _ _ a b _ _ h ↦
      heckeSplit_mem_levelSpace _ _ (levelSpace_le_sphericalAt a b (J h)) inf_le_right h) g)),
    eventually_mostFrobenii (.and (eventually_notMem_star_notMem ℓ
    (insert v S)) he.2) fun y ↦ And.imp_right (· y.prime_q), exists_padic_field_of_form_values hf
  choose r Q μ M g w q k J hr hU hw using (y · |>.2)
  choose b hb c T using exists_padicModel_hecke_contraction κ
  choose! d m using fun x h X j o o' (l : _ → x = u) e ↦ CanLift.prf (β := N) _ (m (_, _)
    ((T x h j).imp fun _ ↦ .imp_right fun T ↦ ⟨T 1 X e (by simp [← map_mul]), fun i ↦ w i ▸ T _ _
    ((q i).2.2 _ _ o o') fun _ ↦ k i _ fun _ h ↦ padicComponents_atSplit _ _ _ (l · ▸ h)⟩))
  exact (exists_trace_limit H (mostFrobeniiAt E · |>.map fun y ↦ d y.w (P y.w) (a - 1))
    L.toSubmodule.complete_of_finiteDimensional (fun _ ↦ mem_inf_of_left (O.mono fun _ ⟨_, _, e⟩ ↦
    by simp [*]; have ⟨c, _, _, t⟩ := e
       simp (maxDischargeDepth := 3) [*, eq_div_of_mul_eq F congr($(t _) _ _).symm, mul_mem,
         heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).1 c), div_mem,
         _root_.sum_mem, -Int.cast_mul])) hr fun g i ↦ tendsto_map' ((tendsto_mostFrobeniiAt (r
    i · |>.1.trace)).congr' (mem_inf_of_left ((hU i).mp (O.mono (by simp +contextual [*,
    trace_eq_neg_charpoly_coeff])))))).rec fun R ⟨hR, hN, hT⟩ ↦ ⟨hR, hN, .id, fun η k ↦
    ((Iic a).eventually_all.2 fun i _ ↦ tendstoUniformly_iff.1 ((H.tendstoUniformly_eval (.C
    ((-1) ^ (a - i) / (a - i)!) * newtonPoly (a - i) 1) (⟨_, hT <| FrobeniusDatum.frob · ^ ·⟩)).add
    (H.2.comp fun z ↦ d z.w (P z.w) i)) η k).exists.rec fun ε h ↦ .mono (.and (.all (hU ⟨ε,
    ·⟩)) O) fun z ⟨p, o, n, e⟩ ↦ forall_eq.2 fun i ↦ (le_or_gt i a).rec (fun l ↦ by
    simpa [l, o, c, m, n, e, ← by simpa using (ext_iff.1 <| p ·), sub_eq_add_neg, eval_newtonPoly,
      trace_pow_eq_sum_roots, charpoly_monic, coeff_eq_esymm_roots_of_splits, IsAlgClosed.splits,
      ← mul_assoc] using (h i (by simpa) z).le) (fun _ ↦ by
    simp [*, k.le, coeff_eq_zero_of_natDegree_lt,
    (e.isMonicOfDegree he.1).1])⟩ |> fun e ↦ ⟨⟨R, e⟩, fun _ c k A hA ↦ And.elim (fun e M ↦ by
    choose g j p using (hw ⟨·, ·⟩ M hA)
    replace j η i := (j η i).congr (J' :=
      jumps κ a) hA fun _ _ ↦ by simp [*, jumps, inducesPlacePair_mk]
    exact (local_clauses_of_trace_limit c.1 c.2.1 _ _ _ _ (⟨r ⟨·, ·⟩⟩) (hr ⟨·, ·⟩) g j (.inr j) (by
    simpa [e] using! H.2.comp (⟨_, hT ·⟩)) fun _ _ _ _ h ↦ cast_inj.1 ∘ tendsto_nhds_unique
    (by simpa [← h, sum_mul] using (H.2.tendsto_at 1).mul_const _)).imp_right (.imp_right
    fun Y k Q hQ s hs ↦ Y .refl (⟨by simp [(hQ.isMonicOfDegree he.1).1, (((q _).2.2 _ k M.1
      M.2).isMonicOfDegree (q _).1).1], p · · s hs⟩) fun j ↦ by simpa [mul_assoc, *] using
      (H.tendstoUniformly_eval ((b u k j)⁻¹ • .X 0 * .X 1) (![d u Q j, ⟨_, hT ·⟩])))) ⟨c.trace_eq e,
    (h u fun g b ↦ by simpa [V, mem_supportedOn.1 b.2 x, C, funext_iff] using k ⟨g,
    b⟩).elim (by clear * - B; aesop)⟩⟩

/-- Odd rank, by descent along one quadratic step (no patching). The representation
of step `0` is conjugate to that of each later step where both are defined; it is extended by `1`
on the elements `K` that all later steps kill, and inertia groups lie in `K`.

Known result: Galois representations attached to forms on definite unitary groups. -/
lemma sphericalCompat_of_odd {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E]
  [CMType E]
  [StablyUnram E] {a} (ha : Odd a) w : SphericalCompat E (Fin a) a w := fun P κ f hf he ↦ by
  choose S _ hS using exists_inf_trivialOn_le hf.1
  let n T := ℓ * (T + w.q + S.sup FinPlace.q).factorial
  choose χ _ _ hμ G H L using fun {T} ↦ exists_quadratic_step E (n T) NeZero.out
  have hp {T} {v : FinPlace E} (h := by omega) : ↑(n T) ∈ v.1 :=
    mem_of_dvd _ ((Nat.dvd_factorial v.one_lt_q.le h).mul_left ℓ).natCast (absNorm_mem _)
  choose F _ Z hs _ using fun {T} ↦
    exists_isWeakBaseChange_of_matching (hμ := @hμ T) ⟨_, hf⟩ isLocalMatching_empty ![] 0 _ rfl (by
    simp) nofun fun _ a _ ↦ trace_restrict_ne_zero one_ne_zero (he.1 congr($(·.le ⟨by simp, a⟩)))
    fun _ _ ↦ eigenspace_le_maxGenEigenspace (by simp [heckeFun, @Fintype.card_unique _ (.mk' _)])
  choose _ e hu _ hr using fun {T x A} a m ↦ (IsPlaceOver.exists_above a).imp fun u e ↦
    And.intro e.2 ((sphericalCompat_of_split ha
    (H · <| ·.elim (mem_of_dvd _ (by simp [n])) (by simpa [·, ← e.2] using m)) (@F
    T).2 Z).symm.imp_left fun H {r} c ↦ (@H r c · A e.1) ∘ (hs.2 x nofun u e.2).1 fun v e ↦
    ⟨hμ.exists_gal_ne_one.imp (notMem_inertia_of_comap_ne ∘ (a.split_completely (L a m).1 v e).2 ·),
    fun y c ↦ by simp [localNorm, ideleAt, ((e ▸ a).artinAt_units_trivial_iff_unramified _).2 fun _
    h ↦ ((L a m).2.1 h).2, v_adeleNorm_eq_one, locIdele_mem_idelesUnitOff c]⟩)
  choose ho hR ρ hρ hs' using
    (@hs · |>.exists_attached_descent (hr w.isPlaceOver_placeOver hp) Z he)
  obtain ⟨⟨m, G⟩, ⟨C, d, o, -⟩, z⟩ := @G 0, hρ 0, (mt <| @hp 0 · ∘ _root_.le_add_left ∘ S.le_sup)
  let K := (⨅ T, (ρ (T + m)).ker.map (Subgroup.subtype _)).normalCore
  choose Q c using fun T ↦ (d.comp (inclusion inf_le_left)).exists_conj_of_trace_eq _ (.id ..)
    ((hρ (T + m)).2.1.comp (inclusion inf_le_right)).hasSemiprimeSpan fun _ ↦
    (hρ 0).trace_eq (hρ _) _ rfl
  have k {T} g h (a : h ∈ K) p : ρ 0 ⟨g.1 * h, p⟩ = Q T * ρ (T + m) g * (Q T)⁻¹ := by
    obtain ⟨y, e, rfl⟩ := Subgroup.mem_iInf.1 (normalCore_le _ a) T
    rw [← mul_one (ρ _ g), ← e, ← map_mul]
    exact eq_mul_inv_of_mul_eq (Units.ext (c _ ⟨_, p, (_ * y).2⟩))
  choose y Y s using G K fun s ⟨x, ⟨p, _⟩, A, a, i⟩ c ↦ Subgroup.mem_iInf.2 fun T ↦ ⟨⟨_,
    (L (a.smul c) hp).2.1 (i.conj c)⟩, hs' .. ▸ (hu (a.smul c) hp (hr ..) (levelSpace_le_sphericalAt
    (z _ p) (z _ (by simpa)) (by simpa [LE.le, funext_iff] using hS))).1.1
    ((a.smul c).valuation_natCast_eq_one_iff.2 (p ∘ mem_of_dvd _ (by simp [n]))) _ (i.conj c), rfl⟩
  have u {x z} (p : (z.1 : _ ⧸ K) = x.1 := by simp [Y]) : ρ 0 x = ρ 0 z :=
    (ρ 0).eq_iff.2 ((@k 0 1 _ (QuotientGroup.eq.1 p) _).trans (by simp))
  exact ⟨⟨.mk' (ρ 0 ⟨_, s ·⟩) fun _ _ ↦ .trans u (map_mul ..), continuous_of_continuousAt_one _
    fun _ h ↦ o.nhds_le 1 ((C.congr fun _ ↦ u).tendsto 1 h), fun x m t ↦ d x (Submodule.span_mono
    (by simp) m) (t · ▸ congr((x * $u).trace)), .id, fun η e V O n ↦
    (chebotarev O n he.2).elim fun y ⟨_, p, _, a, _, v, f, _⟩ ↦ ((hρ (y.q + m)).2.2.2 η e _ (O.inter
    (ho (y.q + m))) ⟨_, v, (L a hp).2.2 (isSplit_of_q_prime p) f.1⟩).imp fun O ⟨a, b⟩ ↦ ⟨fun _ h ↦
    (a h).1, by peel b; simpa [k ⟨_, (a ‹_›).2⟩, Y] using this _ rfl⟩⟩, fun _ R f A a ↦
    match hR 0 R A, L a hp with | ⟨i, j, y⟩, ⟨U, g, D⟩ => (hu a hp (hr ..) f).imp (isGoodAt_iff.2 <|
    isGoodAt_iff.1 · |>.imp i fun x s h ↦ (y ⟨s, g h⟩).2 _ (x _ h)) (.imp (j _) fun x hw P d s h ↦
    (y ⟨s, inv_mem (D hw h.1)⟩).2 _
    (x _ P ((hs.2 w nofun _ (e ..)).2 ⟨by simp [(a.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦
    (D hw h).2], a.split_completely U⟩ _ _ d).2 _ ((a.split_completely U _ (e ..)).1 ▸ h)))⟩

/-- For a stably unramified CM field E, the ℓ-adic avatar μ of an algebraic character θ of type
n satisfies the local clauses `AvatarCompatAt` (finite type, jumps, killing polynomials in
degrees 0 and 1) at every place A above every finite place w.

Known result: ℓ-adic avatar of an algebraic Hecke character and its local behaviour. -/
lemma avatarCompatAt_of_stablyUnram {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E]
  [EmbeddedNumberField E] {w : FinPlace E}
  [NumberField.IsCMField E] [StablyUnram E] θ : AvatarCompatAt w θ := fun A hA ↦ by
  wlog hw : w.IsSplit generalizing E
  · choose χ _ _ _ _ S H using exists_quadratic_step E _ w.one_lt_q.ne_bot
    let j : Gal(Ω/QZChar.stepField χ) →* _ := AlgEquiv.restrictScalarsHom E
    obtain ⟨a, c, u, hu, rfl⟩ := (H hA w.1.absNorm_mem).1,
      isOpenEmbedding_galois_restrict j (by tauto), hA.exists_above (L := QZChar.stepField χ)
    have k := (hA.split_completely a u rfl).1
    refine have T :=
        local_clauses_of_retract 1 _ (by simp) (by tauto) c Filter.univ_mem ?_ (one_mul 1)
      (this θ.baseChange hu (S u (k ▸ u.1.absNorm_mem)).star_ne).imp T.1 (.imp (T.2.1 (by simp))
        fun c s m l t ↦ (c (.ofRingEquiv (·.2 ⟨_, a (inv_mem t.1)⟩)) m l (by rwa [k])).elim fun y witness ↦ by
          obtain ⟨o, e, p⟩ := witness
          exact ⟨_, by simp [v_localNorm (f := 1), *], (hu.localArtin_adeleNorm j).1 e,
      by simpa [← adeleNorm_locIdele] using! T.2.2 _ ⟨⟩ p⟩)
    simp; refine (dense_of_mostFrobenii (eventually_mostFrobenii
      (eventually_notMem_star_notMem ℓ {u}) fun y l ↦ (y.isPlaceOver.exists_localArtin_eq
      y.isFrob 1).elim fun z e ↦ ?_)).induction (fun _ ↦ id) (by apply isClosed_eq <;> fun_prop)
    erw [AlgHeckeChar.avatar_localArtin _ y.isPlaceOver (.inl l.2.2) e.2, θ.1.1.comp_apply,
      adeleNorm_locIdele, θ.avatar_localArtin y.isPlaceOver.isPlaceOver_below _
      ((y.isPlaceOver.localArtin_adeleNorm j).1 e.2)]; simp [l]
  have : CMType E := {}
  obtain ⟨v, o⟩ := (((Northcott.finite_le (h := FinPlace.q) (2 ^ Module.finrank ℚ E)).insert w).insert
    (star w)).exists_notMem
  let k s := ite (inducedPrime s = w) (θ.1.2.toAdd s) (-θ.1.2.toAdd (star s))
  have e : levelSpace ((stdSpace E (Fin 1)).formTranslation (0, k ∘ Φ)) _ ≃ₗ[ℂ] _ :=
    freeLevelEquiv _ _ _ (classAut_eq_bot (w := ![v]) (by simp [·.ext_iff]) (by aesop) le_rfl)
  obtain ⟨f, ⟨-, P, hP⟩, -⟩ := have := e.symm.finiteDimensional; not_forall₂.1
    (Submodule.nontrivial_iff_ne_bot.1 e.nontrivial <| eq_bot_mono (levelSpace_anti
      (.trans (by simp) inf_trivialOn_le_levelOf) |> (le_span_isSphericalOff (S := {v}) _ · (by
    intros; apply_rules [heckeSplit_mem_levelSpace, levelSpace_le_sphericalAt, levelOf_le_Kf]))) <|
      Submodule.span_eq_bot.2 ·)
  have he : IsEigenform _ P := ⟨hP.1,
    (eventually_notMem_star_notMem 1 {v}).mono (by grind [IsSphericalOff, isSplit_of_q_prime])⟩
  obtain ⟨hP, ⟨r, hr⟩, hS⟩ := hP.2.2 w hw (by aesop) (by aesop),
    sphericalCompat_of_odd odd_one w f.2 he
  obtain ⟨⟨t, e⟩, ⟨a₁, b₁, c₁⟩, θ₁, h₁, H, D⟩ := by simpa [Polynomial.isMonicOfDegree_one_iff] using
    (hP.isMonicOfDegree he.1), (hS hr hP.1 A hA).imp_left isGoodAt_iff.1,
    hr.exists_det_eq_avatar f.2 he
  refine (local_clauses_twist A (by simp [← Matrix.ext_iff, by simpa using D])).elim fun T U ↦
    (avatarCompatAt_of_type_eq_zero (θ / θ₁) (fun σ h ↦ ?_) hA).imp (T a₁.1) (.imp (by
    convert U.2.1 b₁ ·; simp [jumps, Multiset.range, *]; lia) fun c ↦ ?_)
  simp [h₁]; grind [Φ_eq_or σ, congr(inducedPrime $(NumberField.IsCMField.isConj_complexConj E
    _)).trans (placeOfEmb_comp_star (ιℓ.toRingHom.comp _))]
  peel c with s m hm hs x v _ k
  refine U.2.2 (.of_dvd ?_ (Polynomial.dvd_iff_isRoot (a :=
    ιℓ (θ₁.1.1 (locIdele w x))).2 (by simp))) k
  interval_cases m
  simpa [(H w hw x).1 v (hP.1 ⟨_, by simp [mem_intGL, mem_LocInt, v]⟩)] using a₁.2 _ (inv_mem hs)
  simpa [(H ..).2 v hP, e] using c₁ _ _ hP _ (pow_one w.q ▸ hs)
