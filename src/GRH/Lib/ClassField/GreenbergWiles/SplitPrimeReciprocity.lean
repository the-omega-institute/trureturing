import GRH.Lib.ClassField.GreenbergWiles.EquivariantUnits
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Power residue symbols of S-units give exactly the relations on tame ramification of
cocycles. -/


variable {G K R} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction
  G Ω] [IsProGalois G K Ω] [CommRing R] {m N} [NeZero m] [NeZero N] {ι U} {A : ClosurePlace} {v :
  FinPlace K} {V : DiscreteModule R G} [Module (ZMod m) V] {I : Set G} (s : SplitPlaces m N I U ι)
open NumberField DiscreteModule trivialisedCocycles DiscreteUnits NeZero Subgroup QuotientGroup
  InfinitePlace QZChar QZ ZModModule Fint

omit [IsProGalois G K Ω] in
lemma eq_one_or_isComplexConj [J : IsProGalois G K Ω] {g} {u : InfinitePlace Ω} (h :
  MulSemiringAction.toAlgAut G ℚ Ω g • u = u) : g = 1 ∨ IsComplexConj g := ((mem_stabilizer_mk_iff
  ..).1 (u.mk_embedding ▸ h)).imp (J.faithful.1 ∘ by simp [AlgEquiv.ext_iff]) (⟨_, ·.eq⟩)

/-- Let A lie over v ∤ m, γ satisfy `IsTameGeneratorFor`, V be killed by m, and f : G → V be locally
constant and additive on inertia. For τ in inertia, f(τ) is a multiple of f(γ). -/
lemma IsTameGeneratorFor.exists_apply_eq_nsmul (h : IsPlaceOver A v) (hm : ↑m ∉ v.1) {γ τ} (hγ :
  IsTameGeneratorFor m A γ) (hτ : τ ∈ inertiaGroup G A) {V} [AddCommGroup V] [Module (ZMod m) V]
  (f : G → V) (l : IsLocallyConstant f) (a : ∀ g ∈ inertiaGroup G A, ∀ k ∈ inertiaGroup G A, f (g *
  k) = f g + f k) : ∃ c : ℕ, f τ = c • f γ := hγ.rec fun i ⟨π, y, u, hy, e⟩ ↦ (((h.decompGroup_spec
  G).1.tame_inertia ((h.decompGroup_spec G).2.2 u) (h.valuation_natCast_eq_one_iff.2 hm)
  congr($hy.1) (.mk' _ (a _ ·.2 _ ·.2)) (l _).preimage_val.preimage_val (char_nsmul_eq_zero m <|
  f ·) (P := Multiplicative V)).2 ⟨⟨_, i.1⟩, i⟩).1 (by simpa [← e,
  ← IsPrimitiveRoot.coe_units_iff] using! isPrimitiveRoot_rootPowHom_one Ω m) ⟨⟨τ, hτ.1⟩, hτ⟩

omit [NeZero N] in
lemma SplitPlaces.apply_inertia_eq_zero (h : IsPlaceOver A v) {i γ τ} (k : s.v i = v) (hγ :
  IsTameGeneratorFor m (s.valRing i) γ) (z : Z1
  V.ρ) (t : V.TrivialOn U.1.1) (e : z.1 γ = 0) (hτ : τ ∈ inertiaGroup G A) : z.1 τ = 0 := by
  obtain ⟨⟨g, k⟩, d⟩ := h.exists_smul G (k ▸ s.isPlaceOver i),
    (t · <| s.inertiaGroup_le (s.level_notMem i) (s.isPlaceOver i) ·)
  have j := k ▸ hτ.conj g
  cases hγ.exists_apply_eq_nsmul (s.isPlaceOver i) (s.level_notMem i ∘ Ideal.mem_of_dvd _
    s.dvd_level.natCast) j _ (z.2.1.1 · (by simp)) (by grind [z.2.2])
  simpa [← mul_assoc, *] using cocycle_conj_eq_smul (a := V.ρ) z.2.2 (d _ j (z.1 g⁻¹⁻¹))

/-- Let U fix V, mV = 0, γ_i satisfy `IsTameGeneratorFor`, and ζ^(b(y)_i) = φ_i r/r for N-units y =
r^m. Trivialised cocycles z obey ∑ b(gy)_i g⁻¹z(γ_i) = 0 and vanish on U if all z(γ_i) = 0. For
totally complex fixed field, ∑ b(gy)_i f(i,g) = 0 for all y makes (∑_g f(i,g) ga)_i some
(z(γ_i))_i. -/
lemma SplitPlaces.power_residue_reciprocity (γ : ι → G) (hγ : ∀ i, IsTameGeneratorFor m (s.valRing
  i) (γ i)) [Fintype ι] (t : V.TrivialOn U.1.1) : ∃ b : _ →+ ι → _, (∀ y r, m • r = ↑y → ∀ i,
  (rootPowHom Ω m).1 (b y i) = unitsRep (s.φ i) r - r) ∧ (∀ P ∈ V.trivialisedCocycles (PlaceAboveS
  N) I, ((∀ i, P.2 (γ i) = 0) → ∀ g ∈ U, P.2 g = 0) ∧ ∀ y, ∑ θ : _ × _, b (fixedSUnitsRep N U θ.2 y)
  θ.1 • V.ρ θ.2.out⁻¹ (P.2 (γ θ.1)) = 0) ∧ (IsTotallyComplex (fixedFieldOf U.1.1) → ∀ f : _ → _,
  (∀ y, ∑ θ, b (fixedSUnitsRep N U θ.2 y) θ.1 * f θ = 0) → ∀ a, ∃ P ∈ V.trivialisedCocycles
  (PlaceAboveS N) I, ∀ i, P.2 (γ i) = ∑ δ, V.ρ δ.out (f (i, δ) • a)) := by
  let Q := U.1.1
  let S := s.liftToSubgroup _ ⟨⊤, normal_top⟩ le_rfl le_top (fun g _ ↦ s.cyc_eq_one _ g.2) _ out_eq'
  obtain ⟨⟨κ, C, Ξ⟩, c, j, A', d, hd, R⟩ := exists_kummer_chars (S.cyc_eq_one · ⟨⟩),
    (S.cyc_eq_one · ⟨⟩), (rootPowHom Ω m).2.1, @FinPlace.isPlaceOver_placeOver (fixedFieldOf Q),
    (s.decompGroup_le (s.isPlaceOver _) <| hγ · |>.1.1), s.principal_sup_idelesUnitOff _ le_rfl,
    (exists_nsmul (Ω := Ω) · (ne m) |>.choose_spec)
  have Z x q h := (map_eq_zero_iff _ j).1 (C x _ (R _) q ▸ sub_eq_zero.2 h)
  have J {B v} (h : IsPlaceOver (K := fixedFieldOf Q) B v) b x a {q} i :=
    Z x q (ext (inertia_fixes_root_of_unit i (h.valuation_natCast_eq_one_iff.2
    (b ∘ v.1.mem_of_dvd s.dvd_level.natCast)) congr($(R _).1) a congr($(x.2 _).1)))
  have n θ x : (κ (ofBase Q Ω (.ofMul x))).1 ⟨_, U.2.1 _ (d θ.1) θ.2.out⁻¹⟩ =
    cycCharMod Ω m θ.2.out⁻¹ * ↑(-((S.v θ).valuation (fixedFieldOf Q) x.1).log) := by
    have O : IsPlaceOver (S.valRing θ) _ := (s.isPlaceOver _).smul _
    obtain ⟨n, a, π, y, hπ, hy, l⟩ :=
      (O.ramification_in_tower Q (S.isPlaceOver θ)).1 (s.decompGroup_le O), hγ θ.1
    exact .trans (sub_eq_zero.1 (κ.map_sub .. ▸ J (S.isPlaceOver θ) (S.level_notMem _) _
      (O.ordRat_eq_zero_iff.1 (by simp [*, Q, O.ordRat_ofBase, (s.isPlaceOver
      _).isUniformiser_iff.1, n.2 ▸ (S.isPlaceOver θ).ordRat_ofBase x])) (a.conj _))) ((fun c : ℤ ↦
      j ((C ⟨_, ((c • ofBase G Ω (.ofMul π)).2 ·)⟩ (c • unitsRep θ.2.out⁻¹ y) (by simp [(ofBase G Ω
      _).2 _, smul_comm m, ← map_nsmul, *]) _).trans (.trans (by simp [← zsmul_one, ← l,
      smul_sub, -zsmul_eq_mul] : unitsRep (_ : G) _ - _ = _) (map_cycCharMod_mul ..).symm))) _)
  let b := AddMonoidHom.mk' (fun x i ↦ (κ ((fixedSUnits N U).inclusion inf_le_right x)).1 ⟨_,
    (s.isFrob i).2⟩) (by clear * -; aesop)
  have L x h θ := j ((C x _ (R _) (S.φ θ)).trans
    (by erw [map_cycCharMod_mul _ θ.2.out⁻¹ (b (fixedSUnitsRep N U θ.2.out ⟨_, h, x.2⟩) θ.1),
    C _ _ (R _ ▸ (map_nsmul (unitsRep _) ..).symm)]; ext; simp [S, liftToSubgroup, mul_smul]))
  refine ⟨b, by tauto, fun P p ↦ (snd_mem_Z1 p).elim fun y z ↦ ?_, fun _ f hf a ↦ by
    choose ξ v e using
      (S.isPlaceOver · |>.exists_localArtin_eq ((inv_inv _).substr (S.isFrob _).1) 1)
    obtain ⟨_, ⟨x, rfl⟩, _, ⟨hx, H⟩, E⟩ := mem_sup.1 (Ξ (finite_natCast_mem _) hd (·.1.mem_of_dvd
      s.dvd_level.natCast) (∏ θ, locIdele _ (ξ θ) ^ (cycCharMod Ω m θ.2.out * f θ).val)
      (by simp [(S.isPlaceOver _).artinAt_eq_of_localArtin_eq (e _), ofBase_mem_sUnits,
      ← toAdd_eq_zero, ← map_nsmul, ← map_sum, mul_comm (f _), mul_assoc, *]))
    cases eq_div_of_mul_eq'' E
    let X := ofBase Q Ω (.ofMul x)
    simp [idelesUnitOff, Units.ext_iff, ideleAt, field] at H
    exact ⟨_, corestrict_mem _ s.mem_and_conj_mem (trivialisedCocycles.exists_mem_of_orbit_reps
      (PlaceAboveS.bijective_orbits Q N A') ((κ X).2.imp (continuous_bot (f := (· • a))).comp fun h
      p q ↦ t _ p.2 _ ▸ by simp [h, add_smul]) (Set.ext S.mem_inertia_iff ▸ fun g ⟨u, b, k, B, h,
      i⟩ ↦ by simp [J h b X (h.valuationVia_eq_one_iff.2 (H u b ▸ by simp [Ne.symm (k ⟨_, ·⟩)])),
      i]) 0 (Sum.rec (fun u g e ↦ by simp [Z X g (ext ((A' u).smul_root_eq_of_local_pow (by
      simpa [u.2.ne_of_notMem, S.level_notMem] using mem_iInf.1 hx u) congr($(R X).1) g
      (by repeat injections) (c g)))]) fun u g e ↦ by simp [(eq_one_or_isComplexConj
      (by injections)).resolve_right (·.false_of_isTotallyComplex),
      Z])).choose_spec.1, fun i ↦ congr(∑ δ, V.ρ _ ($(.trans (by exact δ.ind' (by simp [(eq_one_iff
      _).2, d, X])) ((n (i, δ) x).trans (by rw [← H _ (S.level_notMem _),
      Finset.prod_eq_single (i, δ)] <;> simp +contextual [v, S.v_injective.ne, eq_comm]))) • a))⟩⟩
  have T y (g : Q) (e : g.1 • y = y) := by simpa [*] using p.2.1 g y
  have hc c (h : IsComplexConj c) := T (.inr _) c (congrArg _ ((mem_stabilizer_mk_iff ..).2 (.inr
    (RingHom.ext h.choose_spec).symm)))
  have hD u k := (T (.inl ⟨_, (A' u).valuation_natCast_lt_one_iff.2 k⟩) · congr(.inl ⟨$(·), _⟩))
  refine ⟨fun h ↦ (eq_zero_of_unramified_off _ hd ⟨_, by fun_prop, by simp [*]⟩ hc hD (fun u _ q e ↦
    by_cases (s.apply_inertia_eq_zero (A' u).isPlaceOver_below ·.choose_spec (hγ _) ⟨_, y,
    z⟩ t (h _) e) (p.2.2 _ <| (s.mem_inertia_iff _).2 ⟨_, by simpa, ·, _, (A' u).isPlaceOver_below,
    e⟩)) ⟨·, ·⟩), fun ⟨x, i, f⟩ ↦ eq_zero_of_forall_hom_eq_zero ((bijective_ofZMod_comp
    (char_nsmul_eq_zero m)).2.forall.2 fun u ↦ (hilbert90_unitsRep ⟨fun g : Q ↦ (rootPowHom ..).1 (u
    (P.2 g)), by fun_prop, by simp [← map_cycCharMod_mul, *]⟩).elim fun r e ↦ ?_)⟩
  obtain ⟨a, hr⟩ := ((ofBase_bijective Q).2 ⟨m • r, by simp [← add_eq_of_eq_sub (e _),
        ← map_nsmul]⟩).imp fun _ ↦ (congr($(·).1).symm)
  have E {g : Q} (k : P.2 g = 0) := by simpa [k] using (e g).symm
  have J {B v} k h := (@J B v k h ⟨_,
    f⟩ (i _ (k.valuation_natCast_eq_one_iff.2 h)) · · ▸ map_zero (ofZMod m))
  refine .trans (by simp [← map_zsmul, *, ZMod.map_smul, show u (V.ρ _ _) =
    _ from cocycle_conj_eq_smul (a :=
    V.ρ) z _ ▸ n _ a ▸ j (C _ r hr _ ▸ e _)]; ac_rfl) (sum_ord_smul_frob_eq_zero (?_ :
    m • ofZModCocycle m _ = 0) (artin_reciprocity ⟨_, IsProGalois.isOpen_stabilizer _⟩ (congr($(E <|
    hc · ·).1)) (resH2_cyclicClass_eq_zero hr (⟨ext ·.2, ?_⟩))) S.v_injective (⟨S.isPlaceOver ·,
    (S.isFrob _).1, J (S.isPlaceOver _) (S.level_notMem _)⟩) fun u k ↦ (em _).imp (fun l ↦ (A'
    _).abelianLift_artinAt_eq_one_iff.2 (resH2_cyclicClass_eq_zero hr (⟨E <|
    hD u l _ ·.2, ?_⟩))) fun l ↦ ⟨⟨r, hr ▸ by simp, (E <| p.2.2 · <| (S.mem_inertia_iff _).2 ⟨_, l,
    k, _, A' u, ·⟩)⟩, J (A' u) l⟩) <;> simp [funext_iff, ← map_nsmul]
