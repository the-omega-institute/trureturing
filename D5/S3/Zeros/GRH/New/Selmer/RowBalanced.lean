/- GID: D5/S3/Zeros/GRH/New/Selmer/RowBalanced
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/RowBalanced
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.RowBalanced. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RowBalanced.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.ValueFamilies
import D5.S3.Zeros.GRH.New.Lift.ExponentTheorems
import D5.S3.Zeros.GRH.New.Selmer.CrystallineRank
import D5.S3.Zeros.GRH.New.Selmer.TwistTheorem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

This file: Roots of unity give a tame class; lattices in columns read above ℓ. Local duality bounds
Ribet cocycles' distance from crystalline by the dual lattice's defect. Rows are balanced: local
conditions and mirror scalar within explicit bound. -/

open Lift Polynomial Multiset minpoly Pi Filter Function
variable {P} {D : Data P} {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {n} [Fintype n]

/-- Let M consist of at most N elements of ℚ̄_ℓ, each killed by y^(ℓ^a − 1) − 1 for some 1 ≤ a ≤
r. A class of polynomials over O containing all those vanishing on M is tame
(`Lift.IsTameType`) for r and degree Nr. -/
lemma isTameType_of_roots {N r K M} (b : card M ≤ N) (k : ∀ y ∈ M, ∃ a ∈ Set.Icc 1 r,
  y ^ (ℓ ^ a - 1) = 1) (h : ∀ Q : O[X], (∀ y ∈ M, Q.aeval (y : PadicAlgCl ℓ) = 0) → K Q) :
  Lift.IsTameType ℓ r (N * r) K :=
  have H y c : (minpoly _ y).Monic ∧ (minpoly ℤ_[ℓ] y).natDegree ≤ r := by
    choose f hf hx using k y c
    obtain ⟨a, rfl : wittToQpBar _ = _⟩ := exists_flatFq_root (f := f.toPNat hf.1) _ _ fun _ ↦ hx
    grw [algHom_eq _ wittToQpBar_injective, natDegree_le,
      KummerChart.JumpLattice.finrank_wittFq]; use monic (.of_finite ..), hf.2
  ⟨h _ (k · · |>.elim fun a h ↦ by rw [(Finset.dvd_lcm (mem_Icc.2 h.1)).choose_spec]; simp [pow_mul,
    h]), _, monic_multiset_prod_of_monic _ _ (H · · |>.1), by grw [natDegree_multiset_prod_le,
    sum_le_card_nsmul, ← b] <;> aesop, h _ (by aesop (add simp map_multiset_prod))⟩

variable [PadicIso ℓ] {τ} {u : AbsGal D →* Matrix n n O}

lemma IsColumn.eq_one_of_mem_inertiaAbove {t S R} (h : IsColumn (n := n) D t τ S R) :
  ∀ g ∈ inertiaAbove (placesDividing _ ℓ ∪ placesAboveG D ∪ S)ᶜ, R g = 1 := by grind [IsColumn,
  IsGoodAt, IsPlaceOver.valuation_natCast_eq_one_iff, placesDividing, inertiaAbove]

/-- Let u be a lattice in a column R ∈ 𝓡, and w ∣ ℓ. At w, u has jumps τ and is potentially
crystalline, crystalline unless w ∣ g; if w ∣ g, inertial s is killed by each Q vanishing,
for every R' ∈ 𝓡, at the roots of some polynomial killing s on R'. -/
lemma inClass_of_isLatticeIn {R t S} w {𝓡 : _ → Prop} (h : IsColumn D t τ S R) (m : 𝓡 R) :
  let v := matrixLattice (u.comp (decompGroup _ (placeOver w.1)).subtype)
  let J g := τ (complexEmbOf ((localChart ℓ _ w).e.comp (algebraMap ..)) g)
  IsLatticeIn R u → (∀ g, HasJumps v.ρ (coeffEmb O g) (J g)) ∧ InClass (⨅ _ : ↑w ∈ placesAboveG
    D, ⊥) (fun s Q ↦ w.1 ∈ placesAboveG D ∧ ∀ R, 𝓡 R → ∃ P, PolyKillsAt R (placeOver w.1) s.1 P ∧
    ∀ y, P.IsRoot y → Q.aeval y = 0) (toFinset ∘ J ∘ surjInv coeffEmb_surjective) v := by
  let ⟨⟨_, c⟩, d, z⟩ := h.local_conditions _ (by simp) w.1.isPlaceOver_placeOver
  intro v J ⟨P, hP⟩
  let L := P.toLin.toLinearEquiv
  let F := L.1.restrictScalars _ ∘ₗ O.1.val.toLinearMap.compLeft n
  have hf g x : F (v.ρ g x) = decompRep R _ g (F x) := congr(L $(funext
    (O.1.val.1.map_mulVec _ x))).trans (hP g ▸ by simp [L, F, mul_assoc]; rfl)
  suffices _ from ⟨this,
    .of_jointly_injective le_sup_left (by by_cases ↑w ∈ placesAboveG D <;> simp [*, (z _).2]) _
    (fun _ ↦ .of_forall hf) ?I, by simp [← count_ne_zero, ← this .., surjInv_eq], fun s Q k hs ↦
    (k.2 R m).rec fun _ ⟨a, _⟩ ↦ .of_jointly_injective hs _ (by tauto) ?I le_top (fun _ ↦ ⟨c,
    map_eq_zero_of_roots (eval₂RingHom' _ _ (commute_coefEnd_linearFrob c hs))
    ((((mapClusterPt_one_atTop_pow _).frequently (mem_comap'.1 c.eventually_linearFrob_eq_one)).mono
    (by simpa [← linearFrob_pow c hs ·] using · (map_pow ..) (hs.pow _))).forall_exists_of_atTop 1)
    (a.2 hs).2 (by simpa [eval_map])⟩) rfl fun () _ _ ↦ L.map_smul ..⟩
  any_goals intro g _; rw [coeffEmb, ← jump_baseChange ⟨F.1, fun _ _ ↦ L.map_smul
    ..⟩ (basisFun ..) ((basisFun ..).map L) (fun _ ↦ congr(L $(by ext; simp [apply_ite])))
    (.of_forall hf), ← @d _ _ g]
  all_goals simp [F, v, J, funext_iff]; tauto

open DistribSMul LinearMap NeZero Submodule crysCocycles Ideal.Quotient Matrix.Module

/-- Let j be an open embedding and the lattices u_x∘η, L = ρ∘η lie in `Lift.InClass` F K U. The
cocycles `obeyingCocycles` mod ℓ^m, modulo those obeying along η the relations of Z_f(L), are
no longer than Z_f(L^∨(1)) modulo `Lift.cupOrthogonal` of this class. -/
lemma relLength_obeyingCocycles_le {ℓ} [ThePrime ℓ] {X n R Γ G d : Type} [Fintype X] [Fintype n]
  [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group G] [Fintype d] [𝒥 : OverGp Γ ℓ] (hj : Topology.IsOpenEmbedding 𝒥.toGp) {η : Γ →* _} {u :
  X → G →* Matrix n n R} {ρ : G →* Matrix d d R} {F K U} (hZ : ∀ x, InClass F K U (matrixLattice ((u
  x).comp η))) m : let L := matrixLattice (ρ.comp η); InClass F K U L → relLength (obeyingCocycles u
    ρ (ℓ ^ m)) ((obeying (relationsOn (crysCocycles L.ρ)) _).comap (.funLeft R _ η)) ≤
    relLength (crysCocycles L.tateDual.ρ) (cupOrthogonal (InClass F K U) _) := by
  intro L H
  let τ := (mkQ (R ∙ (ℓ : R) ^ m)).compLeft d
  obtain ⟨⟨f, b⟩, o : Function.Surjective τ, ⟨⟩⟩ := exists_perfect_pairing (L := L),
    mk_surjective.comp_left, PSigma.mk _ (discreteTopology_bot (QuotSpan (ℓ ^ m : R)))
  have hτ : τ.toAddMonoidHom.ker = pPowMultiples L m := by ext; simp [τ, L, Algebra.smul_def,
              funext_iff, eq_zero_iff_mem, mem_span_singleton, Classical.skolem, mul_comm]
  have e g x : τ (L.ρ g x) = ρ (η g) • τ x := by ext; apply map_sum (mkQ _)
  have C y := _root_.funext (nsmul_quot_eq_zero dvd_rfl <| τ y ·)
  grw [relLength_comap, relLength_mono le_rfl (Submodule.map_le_iff_le_comap (f := τ.compLeft Γ).2
    (comp_mem_obeying ·))]
  refine (length_le_of_card_dvd_or_le ℓ ∘ .inl : (toAddSubgroup _).relIndex (toAddSubgroup _) ∣
    (toAddSubgroup _).relIndex (toAddSubgroup _) → relLength .. ≤
    relLength ..) (H.isPotCrys.relIndex_dvd_of_orthogonal hj H.dual.isPotCrys
    (.ofBijective _ b) (by simp) ⟨by simp, by simp⟩ e o hτ (V := .of (actionRep _ _ (ρ.comp η))
    (by simpa [o.forall, e, continuous_prod_of_discrete_right] using fun x ↦ (continuous_comp hj
    H.isPotCrys τ C (coboundary_mem x)).add_const (τ x))) |> (forall₂_and.1 fun s hs ↦ ?_).elim)
  choose y hY t q a ha E using show ∃ y, InClass F K U y ∧ ∃ t : y →ₗ[R] _, (∀ g x, t (y.ρ g x) =
    ρ (η g) • t x) ∧ s ∈ (crysCocycles y.ρ).map (t.compLeft Γ) from hs.elim (by tauto) fun witness ↦ by
    obtain ⟨w, hw, s⟩ := witness
    choose k Y i hx using obeyingCocycles.exists_graph_subrepresentation _ _ hw
    have := i.moduleIsTorsionFree (R := R) _ (by simp)
    use ⟨_, Y.toRepresentation.comp η⟩, .of_jointly_injective (hZ <| Prod.fst ·) (fun a ↦ ⟨⟨(·.1.1
      a.1 · a.2), by tauto⟩, by tauto⟩) (by tauto) fun _ h ↦ i (by ext; apply congrFun (h (_, _))),
      domRestrict (snd ..) _, by tauto, (⟨_, hx · 0⟩) ∘ η, of_smul (a := (ℓ ^ m) ^ k) out
      ((_root_.funext fun _ ↦ i (by ext; simp [mul_sub, Subrepresentation.toRepresentation,
      ← algebraMap_smul R])).subst (coboundary_mem ⟨_, hx 1 1⟩)), s
  -- the form given by a lift `p` of the map to `L / ℓ^m`, and its coboundary divided by `ℓ^m`
  choose p P using Module.projective_lifting_property τ t o; subst P E
  simp at q
  let ψ p : (y.tensor L.tateDual).tateDual := TensorProduct.lift (dualMap p).flip
  have E g : (?_ : ℤ_[ℓ]) • ψ ?_ = GalLattice.ρ _ g (ψ p) - ψ p := by
    ext x l; simpa [ψ] using congr(l $((y.ρ.linHom L.ρ g p - p).codRestrictOfInjective_comp_apply
      (toLinearMap ..) (smul_right_injective _ out) (fun _ ↦ hτ.le (by simp [e, ← q])) x))
  exact ⟨⟨continuous_comp hj hY.isPotCrys (τ ∘ₗ p).toAddMonoidHom (C <| p ·) ha, by simp [*,
    apply_mul ha]⟩, _, rfl, fun _ ↦ (· y ⟨m, ψ p, f,
    ⟨_, of_smul out (_root_.funext E ▸ coboundary_mem _)⟩, mod_cast E⟩ hY a ha)⟩

open Finset Fintype IsLocalRing Matrix
variable {P : _} {D : Data P} {ℓ : _} [ThePrime ℓ] [PadicIso ℓ] {n : Type} [Fintype n]

/-- For a row R of rank n, a chosen place w off ℓ and all large O, some lattice u is balanced
(`IsBalanced`) for Z_f above ℓ, and β plus v(det(u(σ) − 1)) for σ = σ_w, σ_w^{−c}
(σ_w a tame generator at w) has
normalised length ≤ 10fn·cr_ℓ. -/
lemma IsRow.eventually_isBalanced {t J R w} (r : IsRow D t J R) (hG : D.IsChosen w) (hℓ :
  w ∈ placesAboveG D \ placesDividing _ ℓ) M (h := (Finset.finite_toSet _).subset
  (placesDividing_union_subset_badPlaces D ℓ)) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ u :
  _ →* Matrix n n O, ∃ γ β, IsLatticeIn R u ∧ O.normLength (β + ∑ b, IsDiscreteValuationRing.addVal
  _ (u (idOrConjInv b w.isPlaceOver_placeOver.tameGenerator) - 1).det)
  ≤ 10 * D.f * Fintype.card n * crudeUnit ℓ D ∧ IsBalanced ℓ h.toFinset u (crysRels u) γ β M := by
  filter_upwards [r.span_and_scalar, eventually_exists_isLatticeIn r.continuous] with O hs ⟨u, hu⟩
  obtain ⟨⟨hs, g, l, α, c, hg⟩, ⟨Φ, I, f, d⟩, ⟨i⟩, S, ⟨⟨a, b⟩⟩, h2, g₀, o, y, q, hy⟩ := hs u hu,
    hu.exists_algHom, card_pos_iff.1 r.2.1.1, Set.union_sdiff_left ▸ h.sdiff, r.2,
    sum_mono r.card_neg_le, r.5
  cases by simpa [q] using congr($(hu.choose_spec g₀) i i)
  replace q : u _ = u _ .. • 1 := I (by simpa [f])
  have Y j h := (O.isUnit_iff_norm_eq_one (_ ^ j - 1)).2 (by simpa using hy 0 j h)
  choose! γ m Z F G H using (r.inertia_above_g · · (FinPlace.isPlaceOver_placeOver _))
  simp_rw [← f, ← map_one Φ, ← map_sub, d, ← S.mem_toFinset] at *
  choose L K using (inClass_of_isLatticeIn · r.1 r hu)
  have C {g y} (e : u g = y • 1) : IsUnit y ∧ u (conjGal g)⁻¹ = (cycInv ℓ _ O g⁻¹ ^ (t - 1) * y) •
    1 := ⟨by simpa [e, Nat.ne_of_gt a] using isUnits_det_units (u.toHomUnits g), (by exact fun _ _ ↦
    ext_iff_trace_mul_left.2 ∘ DFunLike.ext_iff.1 : (traceLinearMap .. ∘ₗ mulRight O ·).Injective)
    (ext_on_range hs fun k ↦ by ext; simp [cycInv,
    e, by simpa [↓← hu.trace_eq] using
    And.intro (r.trace_conj (conjGal k * g⁻¹)) (r.trace_conj (conjGal k))]; ring)⟩
  refine ⟨u, _, _, hu, ?_, (isOpen_discrete · |>.preimage ((hu.continuous r.continuous).matrix_map
    continuous_quot_mk)), fun _ ↦ hu.eq_one ∘ r.eq_one_of_mem_inertiaAbove _ ∘ by simp, hs,
    ⟨by simpa, _, ⟨by simp [C q, cycInv, cycChar_eq_one_of_mem_inertiaAbove (o.imp fun _ ↦
    .imp_left (·.2))], q⟩, by simpa [sq, mul_self_sub_one] using Y 2⟩, orderOf_le_card.trans_lt' (by
    simpa using (Y _ ⟨((C q).1.map (residue O)).isOfFinOrder.orderOf_pos, ·⟩ |>.map (residue O))),
    fun x b ↦ Quotient.induction_on_pi b fun b ↦ by simpa [obeying_crysRels, entrywise] using! (fun
    v _ ↦ comp_mem_obeying (Z := ZfAt _ u) _ (crysCocycles.coboundary_mem b)), _, _, _,
    ⟨hg, (C hg).2⟩, fun x hx ↦ by
    grw [iInf_le _ ⟨_, FinPlace.isPlaceOver_placeOver _⟩,
      (by simp [← Finset.coe_inj] : h.toFinset = (placesDividing _
      ℓ).toFinset ∪ S.toFinset), sum_union (by simp [Finset.disjoint_right]), ← sum_set_coe]
    refine .trans (add_le_add_three (sum_le_sum fun v _ ↦ .trans (length_mono (by
     rintro _ ⟨_, h, ⟨⟩⟩; simp [mem_selmerModule_iff, obeying_crysRels] at h; tauto))
      (length_obeying_relationsOn_le (crysCocycles.fg (K _).isPotCrys) i)) (sum_le_sum fun v
      c ↦ have p := v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 (S.mem_toFinset.1 c).2
      length_localCocycles_le (nsmul_quot_eq_zero hx) v.isPlaceOver_placeOver (hu.eq_one ∘ G v c ·)
        (((r.local_conditions v (·.1) v.isPlaceOver_placeOver).1.1
        p).mono fun _ ↦ (hu.eq_one ∘ ·)) (γ v) (by simp [*])) le_rfl) ?_
    simp_rw [← sum_mul, finrank_crysCocycles_eq_add_neg_jumps (localChart ..).inducesPlace.2
      (K _).isPotCrys (L _), ← Nat.cast_sum, sum_add_distrib]
    simp [NumberField.Embeddings.card, finrank_eq_two_mul_card_infinitePlace, ← two_mul, mul_assoc,
      star_involutive.bijective.sum_comp (J · |>.countP (· < 0))] at h2
    grw [sum_complexEmbOf_le, h2, length_ker_le_addVal_det, ← add_assoc, add_assoc]
    gcongr; simp [Finset.disjoint_right]; ring; rfl⟩
  simp [-univ_bool, ← Z w hℓ hG]
  grw [H w hℓ, sum_le_sum (by exact (H · · true)), sum_const, card_le_of_subset_placesAboveG,
    ellVal_le_ellVal, ellVal_le_crudeUnit D ℓ l ⟨mul_pos a (t - 1).succ_pos,
    mul_le_mul' b (D.t_odd.rec (by omega))⟩] <;> simp [← add_mul, cycInv, c, ← mul_assoc, pow_succ',
    ← one_sub_mul, pow_mul, norm_sub_rev, (O.isUnit_iff_norm_eq_one _).1 (C hg).1]
  gcongr; norm_cast; nlinarith [D.f.pos_of_neZero]
