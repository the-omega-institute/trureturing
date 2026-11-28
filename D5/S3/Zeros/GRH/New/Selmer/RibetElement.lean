/- GID: D5/S3/Zeros/GRH/New/Selmer/RibetElement
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/RibetElement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.RibetElement. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RibetElement.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.LabelledColumns
import D5.S3.Zeros.GRH.New.Selmer.OnePlaceDefect
import D5.S3.Zeros.GRH.New.Selmer.RowBalanced
import D5.S3.Zeros.GRH.New.Selmer.TateTwistSteps
import D5.S3.Zeros.GRH.Lib.Cyclotomic.OddSha.OddShaBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Ribet's method with congruent blocks and tied auxiliary primes. In any rank the method gives a
Hecke element, polynomial in the tie parameters, that kills a determinant vanishing on lifts modulo
the ties, and on lifts it has no term below the product of all parameters, whose coefficient has
valuation bounded without the even classes. Fitting-ideal forms of Ribet's method are known for
distinct blocks in any rank and for congruent characters in rank 2. Related work:
Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's method for GL2, 2023;
Bellaïche–Chenevier, Families of Galois representations and Selmer groups, 2009; Urban, Selmer
groups and the Eisenstein–Klingen ideal, 2001.

Crystalline losses above ℓ are affordable. The torsion cocycles that Ribet's method produces in the
blocks of a lift's Galois representation need not reduce from crystalline ones, but local duality
and a case analysis on ℓ bound their total distance from the crystalline condition, over all blocks
and places above ℓ, by an explicit, affordable loss. It is known that torsion crystalline classes
can miss reductions of crystalline ones by a bounded defect that vanishes for small weights. Related
work: Sweeting, Bloch–Kato conjecture for four-dimensional symplectic representations, 2025;
Chang–Diamond, Extensions of rank one (φ,Γ)-modules, 2011; T. Liu, Torsion p-adic Galois
representations and a conjecture of Fontaine, 2007.

This file: Ribet's Hecke element for columns with ties; valuation at the lift within budget. -/

open Module CoeffRing ENNReal Filter Finset Fintype Function Lift Matrix NeZero NumberField
  Polynomial Matrix.Module

attribute [-instance] NormedAlgebra.toAlgebra Subalgebra.isScalarTower_left

attribute [-simp] IsUnit.dvd length_eq_zero

/-- The budget at ℓ per unit of rank: h₂²⁷(cr_ℓ + v_ℓ(X)) + 4f·loss_ℓ, with X the integer of
`exists_length_shaOdd_le` for E and t. -/
noncomputable def rowBudget {P} (D : Data P) ℓ := D.h₂ ^ 27 * (crudeUnit ℓ D + padicValNat ℓ
  (exists_length_shaOdd_le _ D.t _ D.algebraMap_mem_cycloField).choose) + 4 * D.f * loss D ℓ

variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {K Y n r : Type} [Fintype n] [Fintype r]
  {t ν : ℕ} {w} {τ φ : K → AbsGal D} {u : Y → GalRep ℓ D.E n} {O : CoeffRing ℓ}

lemma obeyingCocycles.mem_selmerModule [Fintype Y] {u : Y → AbsGal D →* Matrix n n O} (hc : ∀ x,
  Continuous (u x)) {S} (hS : ∀ g ∈ inertiaAbove Sᶜ, ∀ x, u x g = 1) {ρ : _ →* Matrix r r O} {b c L}
  (h : c ∈ obeyingCocycles u ρ b) [NeZero b] (l : c ∈ obeying L _) : c ∈ selmerModule ρ S L _ := by
  choose k _ p H using exists_graph_subrepresentation u _ h
  refine mem_selmerModule_iff.2 ⟨mem_obeying_cocycleRels.1 h.1, fun g k ↦ congr($(@p ⟨_, H g 0⟩ 0
    (by ext; simp [*])).1.2), l, (IsLocallyConstant.iff_exists_open _).2 fun g ↦ ⟨_, (continuous_pi
    (hc · |>.matrix_map (Ideal.span {b ^ k}).continuous_mkQ)).1 {_} (by simp), rfl, fun h K ↦ ?_⟩⟩
  choose w hw using (Ideal.mk_span_eq_iff_dvd_sub.1 congr($K · · ·))
  exact congr($(@p ⟨_, H h 0⟩ ⟨_, H g (of ∘ w)⟩ (by ext; simp [← hw])).1.2)

/-- Let τ_j, φ_j satisfy `IsNewPlaces` at level ℓ^ν and the u_x be conjugate self-dual
(`IsConjSelfDual`). If `IsTraceIdeal` holds for u, ℓ^ν, τ, φ, it still holds after
adding τ_j^{−c}, φ_j^{−c}, with the same variable for both copies of j. -/
lemma isTraceIdeal_withConjInv (hw : IsNewPlaces ν w τ φ) {S 𝒥 e} (hu : ∀ x, IsConjSelfDual t (u x))
  (h : IsTraceIdeal (S := S) (L := PadicAlgCl ℓ) 𝒥 (u · · |>.1) (ℓ ^ ν : ↑O) τ φ id e) :
  IsTraceIdeal 𝒥 (u · · |>.1) (ℓ ^ ν) (withConjInv τ) (withConjInv φ) (·.1) e :=
  h.imp_right (.imp_right fun k g ↦ (k g).imp_right fun a (j, b) ↦ b.rec (by
  have H h i x : (u x (withConjInv h (j, false) ^ i * g)).1.trace = cycInv ℓ _ O (withConjInv h (j,
    false) ^ i * g) ^ (t - 1) • (u x (h j ^ i * (conjGal g)⁻¹)).1.trace := by
    simpa [idOrConjInv, cycInv, trace_mul_comm _⁻¹, O.1.smul_def] using
      (hu x).trace_conj ((h j)⁻¹ ^ i * conjGal g)
  choose d hd using (hw.cycInv_withConjInv O (j, false)).2
  convert 𝒥.smul_of_tower_mem (cycInv ℓ _ O g ^ (t - 1))
    (sub_mem ((k (conjGal g)⁻¹).2 j) (𝒥.smul_mem ⟨_, h.1 j⟩ (sum_mem fun i _ ↦ 𝒥.smul_of_tower_mem
    (d ((t - 1) * i) * ((X - 1) * e j).coeff i) (k (φ j ^ i * (conjGal g)⁻¹)).1)))
  simp [*, Subalgebra.smul_def, ↓aeval_eq_sum_range, sum_mul, sub_mul, mul_sum, mul_sub,
    eq_add_of_sub_eq' (hd _), sub_sub, add_mul, mul_add, MvPolynomial.smul_eq_C_mul,
    by simpa [hw.cycInv_withConjInv, mul_pow, ← pow_mul'] using And.intro H (H τ <| Bool.toNat ·)]
  ac_rfl) (a j))

variable [Fintype Y] [PadicIso ℓ] {V : AuxPair D.E r n} {c ϑ} (hc : IsApt V c ϑ)

/-- Fix a row of rank r and finitely many `IsLabelledColumn` representations with common jumps,
level and apt labels times (X − 1)^t. For O large, lattices u_x in them, one being
T ⊕ O ⊕ … ⊕ O(1 − t), T a lattice in the row above ℓ: the losses of the blocks, at any moduli,
total ≤ 4rf·loss.

Crystalline losses above ℓ are affordable. -/
lemma sum_blockLoss_le (hc : IsApt V c ϑ) {τ τ' S R} {R' : Y → _} (hT : IsRow D t τ R)
    (hC : ∀ x, IsLabelledColumn V t τ' (twistedLabel V c · * (X - 1) ^ t) S (R' x)) (ϵ :
  Sigma (@RowBlockIndex r t) ≃ n) π : ∀ᶠ O : CoeffRing ℓ in atTop, ∀ T {T₀} (u : Y → _ →* Matrix n n
  O) (M : Option (Fin t) → ℕ), (∀ g, u π g = reindex ϵ ϵ (blockDiagonal' (blockRep T · g))) →
  (∀ x, IsLatticeIn (R' x) (u x)) → IsLatticeIn R T₀ → (∀ v : placesDividing D.E ℓ,
  T.comp (decompGroup _ (placeOver v.1)).subtype = T₀.comp (Subgroup.subtype _)) →
  ∑ i, O.normLength (blockLoss (blockRep T i) u (M i)) ≤ 4 * card r * D.f * loss D ℓ := by
  have he v := (localChart ℓ D.E v).inducesPlace.2
  filter_upwards [Eventually.all (block_defect_le_at_place hT.2 <| he ·)] with O h T _ u M hπ Z Y H
  simp_rw [blockLoss, obeying_crysRels]
  let L H i := matrixLattice ((blockRep (t := t) T i).comp (Subgroup.subtype H))
  let f := .funCongrLeft O O ϵ ≪≫ₗ .piCurry _ fun _ _ ↦ _
  have hf H i g x : f (u π g.1 *ᵥ x) i = (L H i).ρ g (f x i) := by simp +zetaDelta [funext_iff,
    hπ, mulVec_apply_eq_sum, reindex_equiv ϵ, Fintype.sum_sigma, blockDiagonal'_apply', Sigma.curry]
  have hu v x := inClass_of_isLatticeIn v (hC x).1 (hC x) (Z x)
  have S v i :=
    InClass.of_jointly_injective (fun _ ↦ (hu v π).2) (fun () ↦ f.symm ∘ₗ .single _ (L _ ·) i)
    (by simp [f.symm_apply_eq, funext_iff, hf, (Pi.apply_single fun i ↦ (L _ i).ρ ·)]) (by simp)
  grw (transparency := default) [relLength_iInf_le, (map_sum ..).le,
    relLength_obeyingCocycles_le (he _).1
    (hu _ · |>.2) _ (S ..), fun v i ↦ h v ((em (v.1 ∈ placesAboveG D)).imp (·.imp fun k b ↦ by
    cases (v.1.charP_quotient b).eq _ (v.1.charP_quotient v.2)
    use rfl, fun s w ↦ ((exists_inertia_eigenvalues n hc b v.1.isPlaceOver_placeOver
      _).choose_spec.2 _ ((localChart ..).isWeilPair_zero_iff.1 w)).elim fun μ H ↦
      isTameType_of_roots (by grw [H.1, hc.rank_le.1, hT.t_le]) (H.2.1 · · |>.2.2) fun _ _ ↦
      ⟨⟨k, b⟩, fun _ N ↦ ⟨_, (H.2.2 N).1, by simpa [eval_multiset_prod]⟩⟩) (by simp [·,
    funext_iff])) (fun g a this ↦ exists_jump_of_jointly_injective (S v · |>.isPotCrys) (.proj · ∘ₗ
    f.1) (hf _) (by simp [← funext_iff, ← Pi.zero_def]) (surjInv_eq coeffEmb_surjective g ▸
    ((hu v π).1 ..).trans_ne (by simpa))) (Option.rec (H v ▸ inClass_of_isLatticeIn v hT.1 hT Y).1
    fun c _ _ ↦ by rw [hasJumps_of_cyclotomicGp_zpow _ (tateTwist_smul _), finrank_pi]; simp!)
    (finrank_pi _) i (S ..)]
  simp! [L, (he _).index_eq_card_range, ← sum_mul]; simp_rw [Finset.card_eq_sum_ones]; norm_cast
  grw [sum_complexEmbOf_le, hT.t_le.trans (le_mul_of_one_le_left' hT.rank_mem.1)]
  have := D.t_odd.pos.ne'
  simp [Embeddings.card, finrank_eq_two_mul_card_infinitePlace, field]; linarith

/-- Ribet's method. Let u_x be `IsLabelledColumn`, of trace ψ·row + Σ_{e<t} cyc^{−e} with
`SelmerLengthLe` on 𝓧, with places `IsPrimeTriangle`, and S, 𝒥 as in `IsTraceIdeal`, e_j(1) = 1.
Then x ↦ det Σ_g ω_g(u_x(g) − 1), ω from `ribetNormaliser`, satisfies `IsRibetElement` at π with
coefficient d, v(`chosenGroupOrder`³·d) ≤ |r|·`rowBudget`.

Ribet's method with congruent blocks and tied auxiliary primes. -/
lemma ribet_columns (hc : IsApt V c ϑ) {J' ψ Q} (hq : IsAuxTwist (badPlaces D ℓ) Q ψ (crudeUnit ℓ
  D)) [Fintype K] [LinearOrder K] {ty a h} (hh : h ≤ padicValNat ℓ D.chosenGroupOrder) (tri :
  IsPrimeTriangle ν w τ φ a V.rankDiff ty (D.h₂ * h) (D.h₂ ^ 22 * h)) (S : Subalgebra (intQpBar ℓ)
  (Y → MvPolynomial K (PadicAlgCl ℓ))) (hu : ∀ x, IsLabelledColumn V V.rankDiff J'
  (twistedLabel V c · * (X - 1) ^ V.rankDiff) (.conjClosure Q ∪ (Set.range w).conjClosure) (u x) ∧
  ∀ g ∈ inertiaAbove (.conjClosure Q), ((u x g).1 - ψ g • 1) * ((u x g).1 - 1) = 0) {𝓧 : Set Y}
  {J R γ y : 𝓧 → _} {m₀} (hm : ⌊D.r * rowBudget D ℓ⌋₊ < m₀) (hR : ∀ x, IsRow (n := r) D V.rankDiff
  (J x) (R x) ∧ SelmerLengthLe ψ (R x) Q m₀ (γ x) (y x)) (hl' : ∀ (x : 𝓧) g, (u x g).1.trace = ψ g *
  (R x g).1.trace + ∑ e ∈ range V.rankDiff, cycInv ℓ _ _ g ^ e) {𝒥 e} (h𝒥 : IsTraceIdeal (S := S) 𝒥
  (u · · |>.1) (ℓ ^ ν) τ φ id e) (he' : ∀ j, (e j).eval 1 = 1) π θ : ∃ d, IsRibetElement 𝒥 (fun x ↦
  ((ribetNormaliser (γ π) a (y π) (ℓ ^ (m₀ + D.h₂ * h)) θ).linearCombination (intQpBar ℓ) fun g ↦
  (u x g).1 - 1).det) π d ∧ @ellVal ℓ _ (D.chosenGroupOrder ^ 3 * d) ≤ card r * rowBudget D ℓ := by
  obtain ⟨⟨-, hψ, σ, hq⟩, ⟨hJ⟩, ⟨s, hs, hr⟩, ⟨od, -, odd⟩, o, hG, ϵ⟩ := hq, hR π, tri.detect,
    (exists_length_shaOdd_le _ D.t _ D.algebraMap_mem_cycloField).choose_spec, of_pos hc.odd.2.pos,
    ((finite_toSet _).subset (placesDividing_union_subset_badPlaces D ℓ)).sdiff (t := placesDividing
    _ ℓ), (equivOfCardEq (by simp! [V.rank_lt.le]) : Sigma (@RowBlockIndex r V.rankDiff) ≃ n)
  let z := σ ⊕ᵥ fun v : hG.toFinset ↦ v.1.isPlaceOver_placeOver.tameGenerator
  have N : IsNewPlaces 0 (_ ⊕ᵥ _) z 1 :=
    Sum.rec hq.1 (⟨hG.mem_toFinset.1 ·.2 |>.2, map_one _, _, _, rfl⟩)
  have M k {S} h : withConjInv z k ∈ inertiaAbove S := (N k.1).2.2.elim fun _ ⟨a, e⟩ ↦
    idOrConjInv_mem_inertiaAbove a (e ▸ a.tameGenerator.2) h _
  choose O' l hL ζ η hR' R₀ ψ' y' ey hl hψ' e₀ hy c₀ hS using
    ((sum_blockLoss_le hc hJ (hu · |>.1) ϵ π).and (.and (.all (eventually_exists_isLatticeIn <|
    hu · |>.1.continuous)) ((eventually_primitiveRoot (Monoid.exponent
    (ZMod D.cycloConductor)ˣ)).and (.and (.all (e · |>.finite_range_coeff.eventually_all.2 fun a _ ↦
    eventually_mem a.2)) (.all (hR · |>.elim (·.span_and_scalar.and ·))))))).exists
  choose η hε using fun j ↦ (mem_lifts ((e j).map (intQpBar ℓ).subtype)).1 ((mem_map_rangeS
    (algebraMap O' _)).2 (⟨⟨_, η j _ ⟨·, rfl⟩⟩, by simp⟩))
  let T x := twistRep (.id _) (ψ' x) (R₀ x)
  have p1 {g} (h : ψ g = 1) : T π g = R₀ π g := by ext; simp [*, T, twistRep]
  have sp x := Basis.units_smul_span_eq_top (w := (ψ' x).toHomUnits) (hR' x _ (hl x)).1
  let Φ R [CommRing R] := (reindexAlgEquiv R R ϵ).toAlgHom.comp blockDiagonalAlgHom
  have B x (e : Fin V.rankDiff) g : Eq (blockRep (T x) (some e) g) fun _ _ ↦
    cycInv ℓ _ O' g ^ e.1 := funext₂ fun _ _ ↦ ite_eq_left rfl
  choose u' hL hB using fun x ↦ show ∃ v, IsLatticeIn (u x) v ∧ ∀ h g, v g = Φ _
    (blockRep (T ⟨x, h⟩) · g) from if h : x ∈ 𝓧 then ⟨(Φ _).1.1.comp (.pi _), .imp (fun Z c g ↦ by
    simp [c, mul_assoc, Φ, ← submatrix_map, blockDiagonal'_map]; rfl)
    ((hu x).1.nondeg.exists_conj_of_trace_eq
    (.pi (O'.1.val.mapMatrix.1.1.comp <| blockRep (T ⟨x, h⟩) ·)) (Φ _) (fun y _ H ↦ by
    ext (_ | e) a b
    simpa [mul_apply, single_apply, ite_and] using congrFun₂ (LinearMap.congr_fun
     (LinearMap.ext_on_range (g := 0) (f := .mulLeftRight _ (y _, y _) ∘ₗ (Algebra.linearMap O'
     _).mapMatrix) (sp _) (congr($(H ·) _))) (.single b a 1)) a b
    with_unfolding_all simpa using! (sum_singleton _ a).symm.trans congr($(H 1) _ a a)) fun g ↦ by
    simp [↓hl' ⟨x, h⟩, ↓← (hl _).trace_eq, ← hψ' ⟨x, h⟩, Φ, trace, sum_range, mul_sum, reindex_equiv
      ϵ, Fintype.sum_sigma, B, cycInv]; simp!; rfl), fun _ _ ↦ rfl⟩ else (hL x).imp (by tauto)
  choose F I f d tr using (hL · |>.exists_algHom)
  have hC x := (hL x).continuous (hu x).1.continuous
  have U g h x := (hL x).eq_one ((hu x).1.eq_one_of_mem_inertiaAbove g h)
  refine (ribet_first_order (S := ⟨_, (S.2 ⟨·, norm_le_one _⟩)⟩) u' 𝒥 (.trans ⟨(⟨none, ·⟩) ⊕ᵥ (⟨some
    ·, ()⟩), (·.rec (·.rec .inl fun e _ ↦ .inr e)), by rintro ⟨⟩ <;> rfl, by rintro ⟨⟨⟩⟩ <;> rfl⟩ ϵ)
    π T (by simp) (fun x g ↦ (reindex ..).symm_apply_eq.1 (by ext1 ⟨⟩ ⟨⟩ <;>
    simp [hB, Φ, blockDiagonal', B] <;> rfl)) (sp π) e₀ hy (by simp [cycInv, c₀]) out (by
    simpa [IsTraceIdeal, ↓(hL _).charpoly_eq_map, ← f, aeval_algHom_apply (F _), ← map_mul, sub_mul,
      tr, O'.1.smul_def] using isTraceIdeal_withConjInv tri.isNewPlaces (e := η) (hu · |>.1.1.1) (by
      simpa [IsTraceIdeal, hε, ← aeval_map_algebraMap (PadicAlgCl ℓ)] using! h𝒥)) (fun e k ↦ by
    simpa [by simpa [eval_map, he'] using (congr(Polynomial.eval 1 $(hε ·)))]
      using ((tri.isNewPlaces.cycInv_withConjInv ..).2 e).trans (sub_dvd_eval_sub _ 1 (η _))) _
    (by simpa [cycInv] using
    (map_dvd (algebraMap _ O') <| tri.prod_dvd ·)) ⟨(ty ·), ty.2⟩ out (.trans (by
    simp [ribetNormaliser, Finsupp.linearCombination_apply ℕ, Finsupp.sum, f, pow_add, ey,
      O'.1.smul_def]
    rfl) <| d · _) (le_self_add.trans_lt (O'.normLength_mono.reflect_lt ((le_add_self.trans
    ?H).trans_lt (by grw [hJ.rank_mem.2]; simpa using mod_cast Nat.lt_of_floor_lt hm))))
    ((relLength_add_length_inf _ (obeying
    (crysRels (T π)) _)).ge.trans (add_le_add (relLength_mono (fun _ ↦ (·.1.1)) le_rfl)
    (length_mono (T := _ ⊓ _) fun c k ↦ ⟨tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero
    (obeyingCocycles.mem_selmerModule hC U k.1.1.1 k.2) (k.1.1.2 _ ⟨·, rfl⟩) (Set.union_assoc ..).ge
    fun g ⟨v, hv, H⟩ _ ↦ (p1 (hψ.eq_one_of_mem_inertiaAbove g ⟨v, mt .inr hv, H⟩)).trans ((hl
    π).eq_one (hJ.eq_one_of_mem_inertiaAbove g ⟨v, mt (.imp_right nofun) hv, H⟩)), k.1.2⟩))) (o :=
    fun k ↦ ite k.1.isLeft (C (ψ' π (withConjInv z k)) - X) (∑ i ∈ range D.chosenGroupOrder,
    X ^ i)) (by simp [N.cycInv_withConjInv]) (by
    rintro ⟨j | j, b⟩ x <;> apply I x
    simpa [f, ← hψ' π, Algebra.smul_def, ← neg_mul] using! congr(-$((hu x).2 _ (M _ (by simp))))
    have ⟨v, ⟨⟨i, b⟩, l⟩, A, a, s⟩ := @M (.inr j,
      b) (placesAboveG D \ placesDividing _ ℓ) (by simpa using j.2)
    have ⟨μ, _, Z, P⟩ := (exists_inertia_eigenvalues n hc b a V.rankDiff).choose_spec.2 _ s
    convert ((hu x).1.local_conditions v (·.2 (.inr ⟨i, b⟩)) a).1.aeval_eq_zero_of_roots
      (a.valuation_natCast_eq_one_iff.2 l) s (P (hu x).1).1
      (X ^ D.chosenGroupOrder - 1) _ <;> simp [f, geom_sum_mul, eval_multiset_prod]
    exact (Z · · |>.2.2.elim fun d ⟨a, h⟩ ↦ (g_pow_sub_one_dvd_chosenGroupOrder D
      (a.imp_right D.nat_le_of_hasLogBound.trans')).choose_spec
      ▸ by rw [pow_mul, h, one_pow])) (s := s ∪ image (withConjInv τ) univ) fun e Z H ↦ (fun N ↦
    ⟨hasTriangleCost_tateTwist tri N (H · · |>.2.2) (add_le_add (relLength_mono (H · · |>.1) le_rfl)
    (odd ℓ _ ⟨ζ, inferInstance⟩ e (e.2.trans_le hJ.t_le) ν)), fun c k b ↦ hr _ e c
    (tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero (N c k) (by simp [b])) (by simp +contextual
    [b])⟩) fun c k ↦ N.mem_selmerModule_of_tame_eq_zero (obeyingCocycles.mem_selmerModule hC U (H c
    k).1 (by simp [obeying])) (H c k).2.1).elim fun d k ↦ ⟨d, k.1, .trans (by
    grw [ellVal_mul_le, (normLength_addVal d).ge, k.2, card_union_le, card_image_le]) ?H⟩
  rw [← @Nat.cast_le ℝ≥0∞] at hs
  simp [rowBudget, mul_add (_ ^ 27), ellVal_natCast, ne, od, two_mul, mul_two, add_mul, hψ',
    sum_prod_type,
    hψ.apply_idOrConjInv, z, -AddValuation.map_pow, -ENat.natCast_sub, -natCast_sub] at hs hq ⊢
  grw [hS, hJ.rank_mem.2, mul_add (card r : ℝ≥0∞),
    ← le_mul_of_one_le_left' (mod_cast hJ.rank_mem.1),
    hq.2, card_le_of_subset_placesAboveG D (by simp), le_self_add.trans hs, le_add_self.trans hs,
    hh, hJ.t_le, (by simp [crudeUnit] : (padicValNat ℓ _ : ℝ≥0∞) ≤ crudeUnit ℓ D)]
  exact (add_le_add (by gcongr <;> exact_mod_cast D.nat_le_of_hasLogBound) ((l _ u' (·.elim m₀
    fun _ ↦ ν) (hB _ _) hL (hl π) fun v ↦ MonoidHom.ext (p1 <| hψ.eq_one_of_mem_decompGroup v.2
    v.1.isPlaceOver_placeOver ·.2)).trans_eq (by ring)) : ((4 + D.t *
    (2 + 10 * D.f + 6 * D.h₂ ^ 22) + D.h₂ ^ 22 + D.h₂) * _ + D.t * _ + _ : ℝ≥0∞) ≤
    _).trans_eq' (by simp only [sum_option, Data.t]; push_cast; ring1!)
