import GRH.Lib.ClassField.GreenbergWiles.SplitPrimeReciprocity
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Count of trivialised cocycles for a projective module (Euler characteristic type
formula). -/

open NumberField Classical Nat NeZero Fintype AddSubgroup Finset Submodule AddMonoidHom Fint
attribute [local simp] funext_iff

/-- Let V be finite, l-torsion, U-fixed, with Higman's property, z − n injective on V, and let U
fix zr/rⁿ whenever r^l is an N-unit and all φ_i fix r. Trivialised cocycles number at most
(#V)^{#ι+1}, exactly so if K is totally complex and z = n on μ_l. -/
lemma SplitPlaces.card_trivialised_of_isHigmanProjective {G K R ι} [Group G] [TopologicalSpace G]
  [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] {l N :
  ℕ} [Fact l.Prime] [NeZero N] {V : DiscreteModule R G} {I U} (s : SplitPlaces l N I U ι) [Fintype
  ι] {z n} (x : V.FiniteKilledFixedInj l U z n) (h : V.IsHigmanProjective U.1.1) (m : ∀ r, l • r ∈
  fixedSUnits N U → (∀ i, unitsRep (s.φ i) r = r) → unitsRep z r - n • r ∈ (unitsModule U.1.1).H0) :
  V.HasFewCocycles (PlaceAboveS N) I (card ι + 1) ∧ ((cycCharMod Ω l z).1 = n → IsTotallyComplex K →
  Nat.card (V.trivialisedCocycles (PlaceAboveS N) I) = .card V ^ (card ι + 1)) := by
  obtain ⟨⟨_, Λ, u, v, w⟩, ⟨_, hV, t, i⟩, ⟨τ, hτ⟩, ⟨γ, hγ⟩⟩ := dirichlet_fixedSUnits G N U, x, h,
    skolem.1 (exists_isTameGeneratorFor G l <| s.isPlaceOver ·), AddCommGroup.zmodModule x.2.1
  let W := QuotientGroup.lift _ (actionRep ℤ _ V.ρ) (LinearMap.ext ∘ t ·)
  obtain ⟨⟨β₀, B, R, T⟩, o⟩ := s.power_residue_reciprocity γ hγ t, show ∀ g, ⇑(V.ρ g) = W g by tauto
  simp [o, -Subtype.forall, injective_iff_map_eq_zero] at hτ R T i
  let d := (d0 V.ρ).toAddMonoidHom
  let β := mk' (fun y (i, g) ↦ β₀ (fixedSUnitsRep N U g y) i) (by simp)
  let j : (ι → V) × d.ker →+ ((fixedSUnitsRep N U).prod (.trivial _ _ ℤ)).IntertwiningMap W :=
    mk' (fun (a, v)
    ↦ ⟨.coprod (∑ θ, .smulRight (.proj θ ∘ₗ β.toIntLinearMap) (W θ.2⁻¹ (a θ.1))) (.smulRight .id v),
    fun g ↦ by ext <;> simp [β, ZMod.map_smul]; exacts [(sum_equiv (.prodCongr 1 (.mulRight g)) _ _
    (by simp)), g.ind' (sub_eq_zero.1 congr($(v.2) ·) |>.symm)]⟩) fun _ _ ↦ by ext <;> simp
  let r : V.trivialisedCocycles (PlaceAboveS N) I →+ j.ker := mk' (fun P ↦
    ⟨(P.1.2 ∘ γ, 0), by ext <;> simp [j, β, (R _ _ P.2).2]⟩) (by simp [Subtype.ext_iff])
  let f (P : r.ker) := @Quotient.lift _ _ (MulAction.orbitRel U.1.1 _) P.1.1.1 fun _ x ⟨g, e⟩ ↦ by
    simpa [← e, t, (R _ _ P.1.2).1 (congr($(P.2).1.1 ·))] using! (P.1.2.2.1 g x).symm
  have H P (g : G) y : W g (f P y) = f P ((g : _ ⧸ U.1.1) • y) + P.1.1.2 g := y.ind' (P.1.2.2.1 g)
  let p : r.ker →+ d.range := mk' (fun P ↦ ⟨P.1.1.2, ∑ x, W x (τ (W x⁻¹ (f P (x • ⟦ofNonempty⟧)))),
    funext fun g ↦ sub_eq_of_eq_add' ((map_sum ..).trans (hτ (P.1.1.2 g) ▸ (sum_equiv (.mulLeft ↑g)
    _ _ (by simp [o, ← map_add, ← H, mul_smul])).trans sum_add_distrib))⟩) (by tauto)
  have hj x : x ∈ j.range := by
    obtain ⟨v, hv⟩ := LinearMap.exists_extend (p := β.range.toZModSubmodule l) ((liftOfSurjective _
      β.rangeRestrict_surjective ⟨.comp x (inl _ ℤ), fun ⟨y, a⟩ k ↦ i _ (by
      obtain ⟨w, rfl⟩ := y.exists_nsmul (ne l)
      erw [← x.isIntertwining, ← map_nsmul, ← sub_eq_zero, ← map_sub,
        ← show l • inl (fixedSUnits N U) _ ⟨_, mem_sUnits_of_nsmul_mem ?e,
        m _ a fun i ↦ by simpa [β, B _ w] using congr((rootPowHom Ω l).1 ($k.1
        (i, 1)))⟩ = _ - _ from Prod.ext (Subtype.ext ?e) rfl, map_nsmul, hV]
      rw [smul_sub, ← map_nsmul, smul_comm]; rfl)⟩).toZModLinearMap l)
    use ⟨fun i ↦ ∑ g, W g (τ (v (Pi.single (i, g) 1))), x (0, 1), by
      simp [d, o, ← x.isIntertwining]⟩
    ext <;> simp [j]
    rw [← hτ (x _)]
    simp [↓← x.isIntertwining, congrArg v (pi_eq_sum_univ' (β _)), ZMod.map_smul, ← sum_product',
      smul_sum, ← (show (v ∘ β) · = _ by simpa using! congr($hv (β.rangeRestrict _)))]
    apply sum_nbij' (fun ((i, d), g) ↦ (d⁻¹ * g, i, g)) fun (h, i, g) ↦ ((i, g / h), g) <;> simp [β]
  have := ofSurjective j hj
  rw [DiscreteModule.HasFewCocycles, pow_succ, ← card_eq_fintype_card, ← Nat.card_fun,
    ← d.ker.card_mul_index, ← mul_assoc, ← Nat.card_prod, ← j.ker.card_mul_index, mul_rotate,
    ← r.ker.card_mul_index, ← p.ker.card_mul_index,
    ← (card_hom_lattice_eq_card_equivariant l hτ u v w).trans (@card_congr _ p.ker ⟨fun F ↦ ⟨⟨⟨⟨(F.1
    ⟦·⟧), 0⟩, by fun_prop, by simp [o, ← F.2]; tauto⟩, rfl⟩, rfl⟩, fun P ↦ ⟨f P, (·.ind'
    (by simp [H, Subtype.mk.inj P.2]))⟩, fun _ ↦ by ext ⟨⟩; rfl, by rintro ⟨⟨⟨⟨⟩⟩⟩, ⟨⟩⟩; rfl⟩)]
  simp_rw [index_ker, j.range_eq_top.2 hj, p.range_eq_top.2 fun ⟨_, m, rfl⟩ ↦ ⟨⟨⟨⟨fun _ ↦ m, _⟩,
    (V.coboundary m).2.1, by simp +contextual [t _ (s.mem_and_conj_mem ..).1]⟩, by ext <;> simp [r,
    t, s.decompGroup_le (s.isPlaceOver _) (hγ _).1.1]⟩, rfl⟩, card_top]
  use ⟨mul_pos (mul_pos (@card_pos _ ⟨0, by simp⟩ _) card_pos) card_pos,
    by grw [r.range.card_le_card_addGroup, Finite.card_subtype_le]⟩, fun c _ ↦ ?_
  erw [r.range_eq_top.2, card_top, card_congr (.subtypeUnivEquiv fun x y h ↦ i _ ?_)]
  obtain ⟨k, _, e⟩ := (torsion_int.le h).exists_nsmul_eq_zero
  have := of_pos ‹_›
  erw [← x.isIntertwining, ← cast_smul_eq_nsmul (ZMod l), ← c, cycCharMod_eq_of_dvd ⟨k, rfl⟩
    zmod_eq_natCast_val, cast_smul_eq_nsmul, ← map_nsmul]
  apply congrArg; ext; exact cycCharMod_spec z (by simpa [pow_mul'] using congr($e.1.1.toMul.1 ^ l))
  simp [by simpa [ne] using congr($e.2)]
  intro ⟨⟨a, v⟩, e⟩
  obtain ⟨⟨⟩, c⟩ := by simpa [j] using congr($e (0, 1)), Module.finBasis (ZMod l) V
  choose P Q hP m using fun k ↦ T (isTotallyComplex_of_algebra K _) _ (fun y ↦ by
    simpa [j, ZMod.map_smul] using! congr(c.repr (τ ($e (y, 0))) k)) (c k)
  exact ⟨∑ j, ⟨_, hP j⟩, by simp [r, Prod.snd_sum, m, sum_comm, ← map_sum, hτ]⟩
