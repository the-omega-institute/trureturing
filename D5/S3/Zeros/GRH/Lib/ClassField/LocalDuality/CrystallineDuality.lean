/- GID: D5/S3/Zeros/GRH/Lib/ClassField/LocalDuality/CrystallineDuality
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/LocalDuality/CrystallineDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.LocalDuality.CrystallineDuality. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/LocalDuality/CrystallineDuality.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.BlochKato.BlochKato
import D5.S3.Zeros.GRH.Lib.CM.FormalGroup.FormalHeight
import D5.S3.Zeros.GRH.Lib.Weil.Construction.FockThetaFunctions
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. Only the inequality is proved, not perfectness or the Euler characteristic formula. It is
proved outright when Galois acts through a p-group (Kummer theory, dévissage), and otherwise it
descends by a Sylow argument from a largest orthogonal pair, supplied by crystalline cocycles of a
twist. Source: J.-P. Serre, Galois Cohomology (1997), II §5.2 Thm 2 and §5.7; J. S. Milne,
Arithmetic Duality Theorems (2nd ed. 2006), I 2.3, 2.8.

This file: Dual crystalline lattices have complementary cocycle counts; index form of the local
duality inequality. -/

open Lift Module LE Submodule Function crysCocycles NeZero AddSubgroup Multiset Topology Nat Algebra
  LinearMap IsDiscreteValuationRing PadicInt MulAction Equiv DFunLike IsLocalGalois
variable {ℓ} [ThePrime ℓ] {R Γ : Type} [CommRing R] [PadicIntegerRing R ℓ] [Group Γ]
  [TopologicalSpace Γ] {L L' : GalLattice R Γ} [𝒥 : OverGp Γ ℓ] (hj :
  IsOpenEmbedding 𝒥.toGp) (h : IsPotCrys L.ρ) (h' : IsPotCrys L'.ρ) (b :
  L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L) (hb : ∀ g x y, b (L'.ρ g x) (L.ρ g y) = χ g • b x y)

omit [TopologicalSpace Γ] [OverGp Γ ℓ] in
/-- Let R be a discrete valuation ring, finite and free over ℤ_ℓ, and L a lattice over R. For
some ℤ_ℓ-linear form f on R, the map φ ↦ f ∘ φ is a bijection from Hom_R(L, R) onto
Hom_{ℤ_ℓ}(L, ℤ_ℓ). -/
lemma exists_perfect_pairing : ∃ f : Dual _ R, Bijective ((restrictScalarsₗ ℤ_[ℓ] R L R
    ℤ_[ℓ]).compr₂ f) := let D := Dual ℤ_[ℓ] R
  let := compHom (R := Rᵈᵐᵃ) D (algebraMap R Rᵐᵒᵖ)
  have e o y x : (o • y : D) x = y (o * x) := rfl
  have : IsScalarTower ℤ_[ℓ] R D := ⟨by aesop⟩
  have := Finite.right ℤ_[ℓ] R D
  have : IsTorsionFree R D := ⟨fun o ho ↦ (Algebra.IsAlgebraic.exists_smul_eq_mul ℤ_[ℓ] 1
    ho.ne_zero).elim fun c ⟨k, n, e⟩ ↦ .of_mul (a := c) fun _ ↦ by simp [mul_comm, ← e, n]⟩
  have t : D ≃ₗ[R] R := .ofFinrankEq _ _ (by
    simpa [finrank_linearMap, finrank_pos.ne', D] using finrank_mul_finrank ℤ_[ℓ] R D)
  by refine ⟨applyₗ (1 : R) ∘ₗ ↑t.symm.1, Equiv.bijective ⟨_, (t.1 ∘ₗ ⟨⟨fun x ↦ · ∘ₗ smulRight id
    x, ?_⟩, ?_⟩), ?_, ?_⟩⟩ <;> intro <;> simp [e, smul_smul, mul_comm, D, -smul_eq_mul, ←
    t.eq_symm_apply, ext_iff]

include h h' hb

omit [TopologicalSpace Γ] in
/-- Let L, L' be potentially crystalline lattices in perfect equivariant duality with values in
ℤ_ℓ(1), Γ open of index n in G_ℓ. The orders of the images mod ℓ^m of Z_f(L') and Z_f(L) have
product ℓ^{m d (n+2)}, d the ℤ_ℓ-rank of L.

Known result: Bloch–Kato finite local condition: rank formula and size of its annihilator. -/
lemma IsPotCrys.index_mul_index_dual m : (pPowMultiples (crysCocycles L.ρ) m).index * (pPowMultiples
  (crysCocycles L'.ρ) m).index = ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) := by
  have ⟨J, _, hJ⟩ := h.exists_hasJumps (ρ := overZp _) (ofId ..)
  obtain ⟨⟨⟩, ⟨⟩⟩ := finrank_eq h hJ, finrank_eq h' fun u ↦ by simpa [← (J.count_map_eq_count' (-· -
    1) fun _ ↦ by lia)] using (jump_eq_of_pairing (ρ := overZp _) h b 1 (by simpa)).trans (hJ _)
  simp_all [← pow_add, ← pow_mul, b.finrank_eq, finrank_linearMap]
  grind [countP_map, countP_eq_card_filter, card_eq_countP_add_countP]

include hj

/-- Local duality: L, L' potentially crystalline, perfectly paired by b into ℤ_ℓ(1), Γ → G_ℓ an open
embedding, A the image of Z_f(L) in V = L/ℓ^m. If A and S consist of continuous cocycles whose cup
products with H bound in ℚ̄_ℓ^×, then [S : S∩A] divides [Z_f(L') : H∩Z_f(L')]. -/
lemma IsPotCrys.relIndex_dvd_of_orthogonal [IsTopologicalGroup Γ]
    {m} {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q :
  L →+ V} (l : IsLinearMap ℤ_[ℓ] q) (e₀ : ∀ g x, q (L.ρ g x) = V.ρ g (q x)) (o : Surjective q) (k :
  q.ker = pPowMultiples L m) {H S : AddSubgroup (Γ → _)} (hZ : ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).carrier ∪ S ⊆ Z1 V.ρ) (hH : ∀ s ∈ ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).carrier ∪ S, ∃ a, q ∘ a = s ∧ ∀ c ∈ H, (fun x ↦ zmodPowToUnits m (.mk'' (b
  (L'.ρ x.1 (c x.2)) (a x.1)))) ∈ B2 (unitsRep.comp toGp)) : ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).relIndex S ∣ H.relIndex (crysCocycles L'.ρ).toAddSubgroup := by
  let := MulSemiringAction.compHom (PadicAlgCl ℓ) 𝒥.toGp; have C := h.index_mul_index_dual h' b hb
  let u := (zmodPowToUnits m).comp (mkQ _).toAddMonoidHom
  obtain ⟨c, _⟩ := by simpa [k] using (index_comap_of_surjective ⊥ o).symm,
    isLocalGalois_localFieldOf hj
  obtain ⟨⟨Q, w⟩, ⟨r, I⟩ : ∃ r : L' →+ V.cartierDual, ∀ x y, r x (q y) = u (b x y)⟩ :=
    exists_openNormalSubgroup_apply_eq V.continuous, ⟨(q.liftOfSurjective o ⟨(toAddMonoidHom'.comp
    b.flip.toAddMonoidHom).compr₂ u, by simp [k, le, u, ext_iff]⟩).flip, by simp⟩
  have k' : r.ker = pPowMultiples _ m := by ext; simpa [u, ext_iff, o.forall, I, zmodPowToUnits,
    (rootPowHom ..).2,
    map_eq_zero_iff, ← RingHom.mem_ker, ker_toZModPow, mem_span_singleton, mul_comm (_ ^ m),
    (reindex_equiv b.symm).2.1, ← b.injective.eq_iff] using ⟨(⟨_,
    codRestrictOfInjective_comp_apply _ (mulRight ..) (mul_left_injective₀ out) ·⟩), by tauto⟩
  have ⟨U, _, P, p⟩ := DiscreteModule.exists_open_sylow ℓ Q
  have hU := hj.comp U.2.isOpenEmbedding_subtypeVal
  let J := OverGp.mk (toGp.comp U.subtype) ⟨hU.2⟩
  have ⟨a, ha⟩ := exists_jump_bound (ρ := overZp (L'.ρ.comp U.subtype)) (γ := ofId ..)
  let N := (a + 1 : ℤ) * Nat.card (Perm V)
  let M := {L with ρ := smulMonoidHom.comp ((χ ^ N).prod L.ρ)}
  let M' := {L' with ρ := smulMonoidHom.comp ((χ ^ (-N)).prod L'.ρ)}
  have ⟨t, t'⟩ : IsPotCrys M.ρ ∧
    IsPotCrys M'.ρ := by constructor <;> apply IsAdmissible.tate_twist <;> tauto
  have B g x y : b (M'.ρ g x) (M.ρ g y) = χ g • b x y := by simp [M, M', hb, Units.smul_def]
  have e g x : q (M.ρ g x) = V.ρ g (q x) := e₀ .. ▸ (l.2 ..).trans congr($(show
    toPermHom ℤ_[ℓ]ˣ V _ = 1 by simp [N, zpow_mul, -toPermHom_apply]) _)
  have D {σ τ : Representation R Γ _} (e : ∀ g x, q (σ g x) = V.ρ g (q x)) (B : ∀ g x
      y, b (τ g x) (σ g y) = χ g • b x y) g x : r (τ g x) = DiscreteModule.ρ _ g (r x) := by
    simp [ext_iff, (o.comp (σ.apply_bijective g).2).forall, I, ← e, B, Units.smul_def, u,
      map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, -smul_eq_mul]; tauto
  have := (mul_dvd_mul_right ((card_dvd_of_le (sup_le_iff.2 (forall₂_or_left.1 fun s z ↦ (hH s
    z).rec fun a ⟨F, G⟩ ↦ ⟨⟨_, hZ z⟩, by
    rintro _ ⟨c, v, e⟩
    exact e ▸ neg_eq_zero.1 ((cupProduct_flip ..).symm.trans ((ker_mkQ _).ge (by
    simpa [← F, ← by simpa [ext_iff] using D e₀ hb, I] using! G c v))), rfl⟩))).trans (card_map_dvd
    _ (Z1 _).toAddSubgroup.subtype)) _).trans (V.local_duality_card_dvd (holdsCorestrictions hj t'
    (D e B) k' (r.range_eq_top.1 (eq_top_of_card_eq _ (by erw [← index_ker, k', index_pPowMultiples,
    b.finrank_eq, finrank_linearMap_self, card_congr (β := _ →* _ˣ)
    AddMonoidHom.toMultiplicativeLeft, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, c]))) hU)
    (t.holdsCorestrictions hj e k o hU) (c ▸ (P.pow_left _).pow_left _) ?_ ?_ ((H.addSubgroupOf
    (crysCocycles _).toAddSubgroup).map (h'.reducedCocycle hj (D e₀ hb) k')))
  · rw [← relIndex_ker, ker_reducedCocycle, ← index_ker, ker_reducedCocycle, ← index_ker,
      ker_reducedCocycle, t.index_mul_index_dual t' b B, ←
      relIndex_bot_left, ← relIndex_mul_relIndex _ _ _ bot_le le_sup_left, relIndex_sup_left,
      relIndex_bot_left, mul_right_comm, ← relIndex_ker] at this
    grw [← mul_dvd_mul_iff_left (left_ne_zero_of_mul (ne_zero_of_dvd_ne_zero out ‹_›)), this, ← C,
      mul_assoc, ← ker_reducedCocycle hj h e₀ k, AddMonoidHom.ker_codRestrict,
      index_dvd_of_le inf_le_left, ← relIndex_mul_index inf_le_right, inf_relIndex_right] <;> rfl
  · rintro _ ⟨⟨w, hw⟩, rfl⟩ _ ⟨c, rfl⟩
    choose l n y o using
      (t'.comp _).exists_coboundary_eq_smul (fun u o ↦ by nlinarith [ha _ ((jump_twist_cyclotomicGp
      N (by simp [M', J, toGp, ← Units.smul_def])).trans_ne o), @card_pos (Perm V) _ _]) c.2
    choose i v z using associated_pow_irreducible n irreducible_p
    choose E X using show ∃ E : _ →+ _, ∀ a, E (l * a) = u a by
      simpa using! QZ.exists_extend (l • .id _) u (by simp [le, n])
    have Z y : ℓ ^ (i + m) • E y = 0 := by simp [← E.map_nsmul, pow_add, ← z, mul_assoc, X, u]
    refine (ker_mkQ _).ge ⟨_, continuous_comp hU (t.comp _) (E.comp (b y)) (by tauto) hw,
      fun g v ↦ ?_⟩
    refine .trans ?_ congr($(map_cyclotomicGp_smul _ Z (b y (w v)) (toGp g.1)) - _ + _)
    simpa [apply_mul hw, sub_add, ← I, *] using! congr(E (b ($o.symm g) (M.ρ g _)))
  refine (card_mul_card_le_of_orthogonal (J := isLocalGalois_localFieldOf (j :=
    J.toGp) hU) (Q.subgroupOf U) (by simp [of_finite ⟨_, J.2.1⟩,
    isUniformiser_ell.card_quot isLocalGalois_padic 1, residueCard_padic]; rfl) ⟨‹_›, by
    rw [pow_mul, ← c]; simp, (by simpa using! w ·), fun _ ↦ by simp⟩ (p _ ·.2) · · · |>.trans_eq ?_)
  erw [← index_ker, ker_reducedCocycle, ← index_ker, ker_reducedCocycle, mul_comm,
    index_mul_index_dual (L := ⟨_, _⟩) (L' := ⟨_, _⟩) (t.comp U.subtype) (t'.comp _) _ (B ·), c]
