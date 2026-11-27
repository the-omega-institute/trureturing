/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/BlochKato
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/BlochKato
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.BlochKato.BlochKato. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/BlochKato/BlochKato.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.PairingDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: The rank formula for the Bloch–Kato finite local condition and the size of its
annihilator. The result is stated on cocycles of a lattice in a potentially crystalline
representation, and the rank is counted from the fundamental exact sequence. Of the duality, only
the count of orders modulo p^m is proved. Source: S. Bloch, K. Kato, L-functions and Tamagawa
numbers of motives, Grothendieck Festschrift I (1990), Prop. 3.8, Cor. 3.8.4; J. Bellaïche, An
introduction to the conjecture of Bloch and Kato, Clay Summer School notes (2009), Prop. 2.8, Thm
2.1.

This file: Bloch–Kato rank formula for crystalline cocycles; positive weights and cyclotomic twists
as consequences. -/


attribute [-simp] map_eq_zero map_smul
open Function Module IsScalarTower Submodule Multiset Bcris crysCocycles Algebra IsFractionRing
  LinearMap QuotientAddGroup NeZero algebraMap PadicInt Classical Matrix
variable {p} [ThePrime p] {Γ R T T' : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R]
  [AddCommGroup T] [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup T']
  [𝒥 : OverGp Γ p] {ρ : Representation R Γ T} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T]

/-- Rank–nullity for preimages: for a linear map e of modules over a domain and a submodule N of T',
rk e⁻¹(N) = rk(N ⊓ range e) + rk ker e. -/
lemma rank_comap_eq_add [IsDomain R] [Module R T'] {e : T →ₗ[R] T'} {N} :
  Module.rank R (N.comap e) = Module.rank R ↥(N ⊓ e.range) + Module.rank R e.ker := by
  erw [← (e.domRestrict _).rank_range_add_rank_ker, range_domRestrict, map_comap_eq, inf_comm,
    (comapSubtypeEquivOfLe e.ker_le_comap).rank_eq]

attribute [local simp] funext_iff smul_sub coordAction comp_def mulVec.eq_unfold dotProduct ne
attribute [local simp ←] IsScalarTower.algebraMap_apply

/-- Bloch–Kato rank formula: if T is finite free over Z_p and potentially crystalline with
multiset of jumps J over Z_p, then Z_f(T) is finitely generated over Z_p of rank rk T + [G_p
: j(Γ)]·#{negative jumps in J}, counted with multiplicity.

Known result: Bloch–Kato finite local condition: rank formula. -/
lemma crysCocycles.finrank_eq (h : IsPotCrys ρ) {J} (hJ : HasJumps (overZp ρ) (ofId ..) J) :
  Module.Finite ℤ_[p] (crysCocycles ρ) ∧ finrank ℤ_[p] (crysCocycles ρ) =
  finrank ℤ_[p] T + 𝒥.toGp.range.index * J.countP (· < 0) := (fun H ↦ ⟨(free_finite_of_rank_le
  (maximalIdeal_eq_span_p.trans span_insert_zero.symm) (isHausdorff_of_injective_pi _ (crysCocycles
  (overZp ρ)).subtype) (by simp) _ H.le).2, finrank_eq_of_rank_eq H⟩) (let ε := finBasis ℤ_[p] T
  (h.exists_hodge_basis ε).elim fun k ⟨N, hk, A, h₀, _⟩ ↦ by
  simp at A
  let D := d0 (coordAction (B := Bcris) ρ ε)
  let u := N.1 ∘ₗ (toAlgHom _ Bcris _).toLinearMap.compLeft _
  let w := ((toAlgHom _ _ BdR).comp ((localFieldOf Γ).val.restrictScalars ℤ_[p])).toLinearMap
  have h₁ y (S : _ → _) (h : ∀ g i, u (D y g) i ∈ S i) := skolem.1 fun i ↦
    BdR.exists_sub_mem_of_smul_sub_mem Γ _ (by simpa [D, u, LinearMap.compLeft,
    ← smul_algebraMap_eq_algebraMap_smul, A, ← Pi.sub_def] using h · i)
  have F y : frobEnd ∘ y - y ∈ D.ker ↔ (frobEnd ∘ D y ·) = D y := by simp [D]; simp [frobEnd]
  have H := rank_quotient_add_rank (((((Algebra.linearMap ..).compLeft _ ∘ₗ ε.equivFun.1).compLeft
    Γ).range.comap D).comap ((D.ker.prod ((N.1 ∘ₗ (toAlgHom _ BdRPlus _).toLinearMap.compLeft
    _).range.mkQ ∘ₗ w.compLeft _).range).comap (.prod (actionRep _ _ (.id FrobGal)
    ⟨.ofAdd 1, 1⟩ - 1) (mkQ _ ∘ₗ u))).subtype)
  rw [rank_eq_zero_iff.2 ?_, zero_add, (comapSubtypeEquivOfLe (by use fun y ⟨c, E⟩ ↦ ⟨(F y).2 (by
    simp [← E, frobEnd]), (h₁ y _ fun g ↦ (h₀ _).1 ⟨(ε.1 (c g) ·), by simp [← E, u]⟩).imp fun _ ↦
    .symm ∘ eq_iff_sub_mem.2 ∘ (h₀ _).2⟩)).rank_eq, ← D.ker.range_subtype, ← range_prodMap,
    rank_comap_eq_add,
    rank_comap_eq_add, show ker (.prod ..) = ((toAlgHom _ ℚ_[p] _).toLinearMap.compLeft _).range by
    ext; simp [u, range_comp, range_compLeft, ← forall_and]; peel 1 using ⟨fun ⟨h, x, e⟩ ↦
    exists_padic_eq_of_frobEnd_fixed h e.symm, fun ⟨c, e⟩ ↦ e ▸ ⟨by simp, c, by simp⟩⟩,
    ← map_comap_eq, inf_of_le_left (by rintro _ ⟨c, rfl⟩; simpa [u, Submodule.Quotient.eq, skolem,
    range_comp, forall_and] using! fun x ↦ fundamental_sequence_surjective _ _),
    ← (quotKerEquivRange _).rank_eq, show ker _ = (id.prodMap (funLeft _ _ ((↑) : {i // k i < 0} →
    _))).ker by ext; simpa [w, qpBar_mem_hodgeFil_iff] using!
    (fun _ ↦ h₀ (w ∘ _)), (quotKerEquivOfSurjective _ (by simp [surjective_id, coe_prodMap,
    funLeft_surjective_of_injective])).rank_eq, rank_map_eq fun _ ↦ by simp [ε.ext_elem_iff],
    rank_range_of_injective _ fun _ ↦ by simp, rank_eq_of_surjective (M := _ × _) fst_surjective, ←
    show (crysCocycles ρ).restrictScalars _ =
    .comap _ _ by ext; simp [crysCocycles, D, -coordAction, reindex_equiv (ε.baseChange
    _).equivFun, ↓← equivFun_tensorAction, (ε.baseChange _).ext_elem_iff, eq_comm,
    smul_def'], ker_fst, rank_range_of_injective _ inr_injective, add_rotate] at H
  erw [Cardinal.eq_of_add_eq_add_right H (by grw [← rank_map_eq (f := u) fun _ ↦ by simp [u],
    (rank_mono (by rintro _ ⟨y, e, rfl⟩; simpa [@eq_comm _ (N _ _)] using! h₁ y ⊥ (e ▸ by
    simp))).trans (rank_range_le (w.compLeft _)), ← rank_right_eq _ ℚ_[p], rank_lt_aleph0])]
  cases ext' (hJ · ▸ hk _); simp [↓countP_map, ← rank_right_eq _ ℚ_[p], finrank_fixedFieldOf,
    ← finrank_eq_rank, Fintype.card_subtype]; ring!
  rintro ⟨y, hz, a, hy⟩
  refine (eq_iff_sub_mem.1 hy.symm).elim fun x hx ↦ (pow_unbounded_of_one_lt (∑ i, ‖thetaBdR (x i)‖
    + ‖thetaBdR ∘ x‖) (p.one_lt_cast.2 Fact.out)).elim fun s h ↦ ⟨p ^ s, out, (ker_mkQ _).ge ?_⟩
  simp [range_compLeft]; intro g i
  have E := congrFun (N.injective (by simpa [D, u, w, A, ← smul_algebraMap_eq_algebraMap_smul,
    LinearMap.compLeft, mem_localFieldOf.1, ← Pi.sub_def] using (congr(toGp g • $hx - $hx).symm) :
    u (D y g) = N ((↑) ∘ d0 (coordAction ρ ε) x g))) i
  have ⟨c, hc⟩ := exists_padic_eq_of_frobEnd_fixed congr($((F y).1 hz) g i) E
  rw [← hc, ← coe_smul]; use ⟨p ^ s * c, ?_⟩, algebraMap_apply ..
  have E := congr(‖thetaBdR $((coe_inj.1 (.trans (by simp [← hc]) E) : ↑c = _))‖)
  have := pos p; simp [field] at E ⊢
  grw [← h, E, norm_sub_le, norm_sum_le, ← norm_le_pi_norm _ i]
  gcongr <;> simp [mul_le_of_le_one_left, algebraMap_apply _ ℚ_[p] ℂ_[p], norm_le_one])

/-- If j: Γ → G_p is a homomorphism with open image and the R[Γ]-module T is finite free over
Z_p and potentially crystalline, then the R-module Z_f(T) of crystalline cocycles is
finitely generated. -/
lemma crysCocycles.fg (h : IsPotCrys ρ) : Module.Finite R (crysCocycles ρ) :=
  (finrank_eq h (IsPotCrys.exists_hasJumps ‹_› _).choose_spec.2).1.of_restrictScalars_finite ..

/-- Let j have open image and T be finite free over Z_p, potentially crystalline, with all
Hodge–Tate jumps over Z_p positive. Then for every crystalline cocycle c there are t ≠ 0 in Z_p and
x in T with t·c(g) = ρ(g)x − x for all g. -/
lemma IsPotCrys.exists_coboundary_eq_smul (h : IsPotCrys ρ) (H : ∀ u, jump (overZp ρ) (ofId ..)
  u ≠ 0 → 0 < u) {c} (hc : c ∈ crysCocycles ρ) : ∃ t ≠ (0 : ℤ_[p]), ∃ x, (ρ · x - x) = t • c := by
  change IsPotCrys (overZp ρ) at h
  cases h.exists_hasJumps _
  let d := codRestrict _ (d0 (overZp ρ)) coboundary_mem
  obtain ⟨⟨⟩, _⟩ := finrank_eq h (by tauto), finrank_range_of_inj (.of_ker d fun x e ↦ by_contra
    fun n ↦ (H 0 (exists_jump_of_jointly_injective (fun _ ↦ h) (ρ := 1) (fun () ↦
    toSpanSingleton _ _ x) (by simp_all [d, d0, Subtype.ext_iff]) (by aesop)
    (by simp [hasJumps_of_cyclotomicGp_zpow 0 ..])).choose_spec).false)
  simpa [← Quotient.mk_smul, Subtype.ext_iff] using! finrank_eq_zero_iff (R := ℤ_[p]).1 (by
    simp_all [finrank_quotient, HasJumps, countP_eq_zero, le_of_lt]) (d.range.mkQ ⟨c, hc⟩)

attribute [local simp] Algebra.smul_def eq_sub_iff_add_eq

/-- Let Γ act on T, finite free over Z_p, through χ^(−a) with a ≥ 0. A crystalline cocycle c
vanishes at every s with ρ(s) = 1, provided j(s) lies in inertia when a = 0. -/
lemma crysCocycles.apply_eq_zero_of_cyclotomicGp {a : ℕ} (h : ∀ g x, ρ g x =
  (χ g ^ (-a : ℤ)).1 • x) {c}
  (hc : c ∈ crysCocycles ρ) {s} (e : ρ s = 1) (hs : a = 0 → IsWeilPair (toGp s) 0) : c s = 0 := by
  cases a
  -- a coordinate of `c` is `g y - y`; then `φ y - y` is invariant, so `y ∈ A_inf[1/p]`
  apply eval_apply_injective ℤ_[p]; ext l
  obtain ⟨y, e⟩ := by simpa [reindex_equiv (TensorProduct.rid ..).symm, tensorAction, crysCocycles,
    ← (TensorProduct.rid ..).apply_eq_iff_eq] using map hc (σ := .trivial ℤ_[p] ..) l (by simp [h])
  obtain ⟨⟨_, n, w, _⟩, ⟨a⟩, z, _⟩ := exists_witt_ratio (a :=
    frobEnd y - y) (ne 1) (nhds_one_le_map_nearOne Γ (by simp [← e]; simp [frobEnd])),
    BdR.exists_sub_mem_of_smul_sub_mem Γ 1 (x := y) fun g ↦ ⟨l (c g), by simp [← e]⟩
  have ⟨x, hx⟩ := Ainf.exists_frobEnd_sub_xi_pow_mul_eq 0 w
  have ⟨r, hr⟩ := @exists_padic_eq_of_frobEnd_fixed p _ (p ^ n * y - x) (by simp; grind) (p ^ n *
    (z + a) - x) (by aesop)
  simpa [-map_mul] using (congrArg _ ((algebraMap.coe_inj ..).1 (injective_BPlus_Bcris (by
    simpa [← e, mul_add, sub_sub_sub_comm] using! congr(toGp s • $hr - $hr).symm)) :
    ↑(p ^ n * l _) + x = _)).trans (toWittResidue_smul_of_isFrob (hs rfl) x)
  have ⟨t, n, x, E⟩ := IsPotCrys.exists_coboundary_eq_smul (isAdmissible_of_cyclotomicGp_zpow _ h)
    (by simp [mem_replicate, hasJumps_of_cyclotomicGp_zpow (ρ := overZp ρ) _ h _]) hc
  simpa [*] using congr(-$E s)
