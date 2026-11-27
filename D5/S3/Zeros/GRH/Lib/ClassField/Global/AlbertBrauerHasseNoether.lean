/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Global/AlbertBrauerHasseNoether
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Global/AlbertBrauerHasseNoether
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Global.AlbertBrauerHasseNoether. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Global/AlbertBrauerHasseNoether.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.NormAbsValue
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeL.HeckeContinuation
import D5.S3.Zeros.GRH.Lib.ClassField.Local.ArtinMapAtPlace
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Global class field theory, covering Albert–Brauer–Hasse–Noether, reciprocity,
existence and norms. Only finite ideles are used, real places are handled by total positivity, and
existence is proved only for totally complex fields. Reciprocity starts from cyclotomic characters
of prime conductor, and the auxiliary character is chosen by B. H. Neumann's covering lemma. Source:
J. S. Milne, Class Field Theory (v4.03, 2020), VI 4.9, VII 4–9, VIII 4; Tate, Global class field
theory, in Cassels–Fröhlich 1967, ch. VII; H. Hasse, Die Struktur der R. Brauerschen
Algebrenklassengruppe, Math. Ann. 107 (1933) (reciprocity from the sum formula).

Analytic second inequality for norm index; primes of degree one in every coset. Global Artin map as
product of local symbols: continuity, norm compatibility, splitting of places.
Albert–Brauer–Hasse–Noether: locally trivial Brauer classes vanish; Artin symbol kills norms. -/

open NumberField InfinitePlace AddChar QZChar DFunLike DiscreteModule Finset Fint Function IsGalois
  Module MulSemiringAction NeZero QuotientGroup SUnit Subgroup IsDedekindDomain.HeightOneSpectrum

instance {K L} [Field K] [Field L] [Algebra K L] (w : FinPlace L) : w.1.LiesOver (w.below K).1 :=
  ⟨rfl⟩

variable {K L} [Field K] [Field L] [NumberField K] [NumberField L] {W : Subgroup (𝔸f K)ˣ}

/-- The formula efg = n: for L/K a Galois extension of number fields and w a prime of L, the
number of primes of L over the same prime of K, times e(w)f(w), equals [L:K]. -/
lemma FinPlace.ncard_above_mul_ef_eq_finrank [Algebra K L] (w : FinPlace L) [IsGalois K L] :
  {u : FinPlace L | u.below K = w.below
  K}.ncard * (w.1.ramificationIdx (𝓞 K) * w.1.inertiaDeg (𝓞 K)) = finrank K L := by
  rw [← card_aut_eq_finrank, ← (w.below K).1.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (𝓞 L), Ideal.ramificationIdxIn_eq_ramificationIdx _ w Gal(L/K), Ideal.inertiaDegIn_eq_inertiaDeg
    _ w Gal(L/K), ← Set.ncard_congr' (.trans (.subtypeEquivRight _) (equivPrimesOver _ (ne_bot _)))]
  simp [← Ideal.liesOver_iff_dvd_map (isPrime _).1, Ideal.liesOver_iff,
    IsDedekindDomain.HeightOneSpectrum.ext_iff]; tauto

/-- Let ψ and finitely many c_i be homomorphisms from a monoid to ℂ, with ψ(x) = 1 whenever no
c_i(x) is −1. Then ψ times the product of some subset of the c_i is trivial. -/
lemma exists_mul_prod_eq_one {G ι} [Monoid G] [Fintype ι] (ψ : G →* ℂ) c
    (h : ∀ x, (∀ i, c i x ≠ -1) → ψ x = 1) : ∃ T : Finset ι, ψ * T.prod c = 1 := by
  by_contra!; absurd ext_iff.1 (linearIndependent_monoidHom _ _ (by
    simp [funext_iff, ← mul_sum, ← powerset_univ, ← prod_one_add]; grind [prod_eq_zero_iff]) : ∑ T,
    .single (Finset.prod T c) 1 = ∑ T, .single (ψ * Finset.prod T c) 1) 1
  simp [Finsupp.single_apply, *]; use ∅; simp

/-- Let W be an open subgroup of the finite ideles containing the totally positive elements of
K, f a complex character of the quotient. The f(ϖ_v) have density 1 − m (f trivial) or −m
(otherwise), for some m ≥ 0. -/
lemma exists_hasPrimeDensity_ray_char (h : W.IsOpen) (h' : ∀ x, IsTotallyPositive x.1 →
  principalIdele (x : Kˣ) ∈ W) (f : AddChar (Additive (_ ⧸ W)) ℂ) : ∃ m : ℕ,
  HasPrimeDensity (fun v ↦ f (.ofMul ⟦locIdele v (uniformizer v)⟧)) (ite (f = 0) 1 0 - m) := by
  split; use 0; simp_all [hasPrimeDensity_const]
  let ψ := f.toMonoidHom.comp (mk' W)
  have l := le_comap_mk' W f.toMonoidHom.ker
  cases exists_mul_prod_eq_one (ψ.comp principalIdele) (fun w ↦
    ⟨⟨fun x ↦ Φ w x.1 / ‖Φ w x‖, by simp⟩, by simp [field]⟩) fun x H ↦ l (h' x fun φ ↦ not_le.1
    (H (.mk (Complex.ofRealHom.comp φ)) <| by simp [Φ, abs_of_nonpos ·, IsSelfAdjoint, ext_iff]))
  exact (IsHeckeOfType.exists_hasPrimeDensity (n := piecewise ‹_› 1 0)
    ⟨ψ.ker_toHomUnits.substr (isOpen_mono l h), by simp_all [piecewise, ext_iff]⟩ Set.finite_empty
    (‹¬_› <| by ext ⟨⟩; congrm $(·) _)).2.imp (by simp [heckeCoeff]; tauto)

/-- Second inequality: for L/K Galois, an open subgroup W of the finite ideles containing
totally positive elements and norms from L has finite index at most [L:K], and every coset
contains ϖ_v for infinitely many v of prime norm. -/
lemma second_inequality L [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (h : W.IsOpen)
    (h' : ∀ x, IsTotallyPositive x.1 → principalIdele (x : Kˣ) ∈ W) (h₁ : ∀ y,
  .map (adeleNorm K L) y ∈ W) : FiniteIndex W ∧ W.index ≤ finrank K L ∧ ∀ a, ∃ᶠ v in .cofinite,
  v.q.Prime ∧ locIdele v (uniformizer v) / a ∈ W := by
  choose _ m hm using
    And.intro (finiteIndex_idele_subgroup_of_isOpen W h h') (exists_hasPrimeDensity_ray_char h h')
  have := (hasPrimeDensity_card_degree_one L W.index).re_le_re (.sum (finrank K L) hm)
    ((eventually_unramified (mk' W)
    (by simpa)).mono fun v h _ ↦ (Set.ofPred _).eq_empty_or_nonempty.elim
    (· ▸ by simp [← mul_sum, sum_apply_eq_ite, apply_ite, mul_nonneg]) (by
    rintro ⟨w, ⟨⟩, q⟩
    specialize h (uniformizer _ / localNorm K w (uniformizer w))
    simp_all [v_localNorm (f := 1), ← adeleNorm_locIdele, index, (eq_one_iff _).2]
    grw [(Finite.card_range_le _).trans' (Set.ncard_le_ncard fun _ ↦
      (w.exists_gal_comap_eq ·.1.symm)), card_aut_eq_finrank]))
  have := (Nat.cast_pos.2 Nat.card_pos).trans_le this
  use ‹_›, ?_, fun c H ↦ ((HasPrimeDensity.sum (· (.ofMul c⁻¹)) hm).re_le_re
    (hasPrimeDensity_const 0) (H.mono ?_)).not_gt ?_ <;> simp_all [← Nat.cast_sum, ← mul_sum,
    finrank_pos, ← map_add_eq_mul, sum_apply_eq_ite, neg_add_eq_sub, eq_iff_div_mem]

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K] {A :
  ClosurePlace} {v : FinPlace K} (χ : QZChar Γ) {L : Type*} [Field L] [EmbeddedNumberField L]
  [Algebra K L] (h : IsPlaceOver A v) [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω] (U :
  Subgroup Γ) [IsGalois K L] [IsScalarTower K L Ω] [Fact U.IsOpen] [IsProGalois U L Ω]

include h

lemma IsPlaceOver.ncard_above_mul_relIndex : {u : FinPlace L | u.below K =
  v}.ncard * U.relIndex (decompGroup Γ A) = finrank K L := h.exists_above.elim fun u H ↦
  .trans (by grind [h.ramification_in_tower U H.1]) u.ncard_above_mul_ef_eq_finrank

variable {U}

/-- Let L ⊂ Ω be finite Galois over K, and let U = Gal(Ω/L) contain the decomposition group of a
place A over v. Then every prime u of L above v has the norm of v and is fixed by no σ ≠ 1
in Gal(L/K). -/
lemma IsPlaceOver.split_completely (H : decompGroup Γ A ≤ U) (u : FinPlace L) (k :
  FinPlace.below K u = v) : u.q = v.q ∧ ∀ σ ≠ (1 : Gal(L/K)), u.comap σ ≠
  u := have e := (U.relIndex_eq_one.2 H ▸ mul_one _).symm.trans (h.ncard_above_mul_relIndex U)
  have := k ▸ u.ncard_above_mul_ef_eq_finrank; ⟨by simp_all [← (u.below K).1.absNorm_pow_inertiaDeg,
    finrank_pos.ne'], fun σ ↦ ((Set.rangeFactorization_surjective.bijective_of_nat_card_le
    ((e ▸ card_aut_eq_finrank ..).trans_le (Set.ncard_le_ncard fun _ ↦
    FinPlace.exists_gal_comap_eq ∘ by grind))).1 <| Subtype.ext ·).mt⟩

/-- For A lying over v and a character χ of Γ, the image of K_v^× under χ∘Art_v equals the image
under χ of the decomposition group of A. -/
lemma IsPlaceOver.range_abelianLift_artinAt : ((abelianLift χ).comp (artinAt Γ v)).range =
  (decompGroup Γ A).map (toHom χ) :=
  le_antisymm (fun _ ⟨_, e⟩ ↦ e ▸ ⟨_, by simp, congr(abelianLift χ $((h.artinAt_eq_of_localArtin_eq
  (Quot.out_eq _).symm).symm))⟩) (Set.forall_mem_image.2 (h.denseRange_localArtin.exists_mem_open
  ((continuous_abelianLift _).1 {_} ⟨⟩) ⟨⟦⟨·, ·⟩⟧, rfl⟩ |>.imp (h.abelianLift_artinAt χ · ▸ ·)))

lemma IsPlaceOver.artinAt_trivial_iff_decompGroup_le : (∀ x, abelianLift χ (artinAt Γ v x) = 1) ↔
  decompGroup Γ A ≤ ker χ := by
  simp [← Subgroup.map_eq_bot_iff, ← h.range_abelianLift_artinAt, SetLike.ext'_iff]

lemma IsPlaceOver.artinAt_units_trivial_iff_unramified :
  (∀ x, Valued.v x.1 = 1 → abelianLift χ (artinAt Γ v x) = 1) ↔ inertiaGroup Γ A ≤ ker
  χ := ⟨fun H g a ↦ (h.exists_localArtin_eq (inv_mem a) 0).elim fun x ⟨b, e⟩ ↦
  (h.artinAt_eq_of_localArtin_eq e ▸ H x b :), fun H _ a ↦ (h.exists_inertia_eq_localArtin a).elim
  fun _ e ↦ (h.artinAt_eq_of_localArtin_eq e.2).substr (by tauto)⟩

/-- Let A lie over v, χ be trivial on the inertia group of A and φ an arithmetic Frobenius at A.
Then χ(Art_v x) = −ord_v(x)·χ(φ) for x ∈ K^×. -/
lemma IsPlaceOver.abelianLift_artinAt_of_unramified (c : inertiaGroup Γ A ≤ ker χ) {φ} (hφ :
  IsFrob A v.q φ) x : abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) =
  .ofAdd (-(-(v.valuation K x).log • χ.1 φ)) := (h.exists_localArtin_eq (inv_inv φ ▸ hφ) 1).elim
  fun z F ↦ by simpa [h.artinAt_eq_of_localArtin_eq F.2, mul_inv_eq_one] using
  ((h.artinAt_units_trivial_iff_unramified χ).2 c (_ * z ^ (_ : ℤ))
    (by simp_all [ideleAt, WithZero.exp_neg, -WithZero.inv_exp]))

omit h

open _root_.Set in
lemma QZChar.eventually_artinAt_eq_one : ∀ᶠ a in nhds 1, a ∈ idelesUnitOff ∅ ∧ ∀ v,
  abelianLift χ (artinAt Γ v (ideleAt v a)) = 1 := .mono (((isOpen_idelesUnitOff _).inter
  (Finite.isOpen_biInter (finite_ramified (isOpen_ker χ)) fun v _ ↦ (continuous_iff_isOpen_ker.1
  (continuous_hom_locField_units _) χ).preimage_of_continuous)).mem_nhds (by simp)) fun a ⟨h, H⟩ ↦
  ⟨h, fun v ↦ by_cases (fun n ↦ (v.isPlaceOver_placeOver.artinAt_units_trivial_iff_unramified χ).2
  (n _ v.isPlaceOver_placeOver) _ (mem_idelesUnitOff.1 h _ id)) (mem_iInter₂.1 H _)⟩

/-- For every character χ of Γ and finite idele a, χ(Art a) is the finitely supported product
over the finite places v of χ(Art_v a_v). -/
@[local simp] lemma abelianLift_artinMap_eq_finprod : ∀ χ a, abelianLift χ (artinMap Γ a) = ∏ᶠ v,
  abelianLift χ (artinAt Γ v (ideleAt
  v a)) := have s χ a := (finite_ramified (isOpen_ker χ)).mp (.mono (finite_idele_val_ne_one a)
    fun v e n ↦ ((FinPlace.isPlaceOver_placeOver v).artinAt_units_trivial_iff_unramified χ).2
    (n _ (FinPlace.isPlaceOver_placeOver v)) (ideleAt v a) e)
  Classical.epsilon_spec (exists_hom_abelianLift_eq (.mk' (fun a ↦ .mk' _ fun χ ξ ↦
    .symm ((finprod_mul_distrib _ (s ξ a.toMul)).symm.trans (finprod_congr
    (by rcases artinAt _ · _; rfl)))) (by aesop (add simp (finprod_mul_distrib (s ..) (s ..))))))

/-- The global Artin map from the finite ideles of K to the abelianisation of Γ is continuous. -/
@[fun_prop] lemma continuous_artinMap : Continuous (artinMap Γ) := continuous_iff_isOpen_ker.2
  fun χ ↦ isOpen_of_mem_nhds _ ((nhds 1).3 (eventually_artinAt_eq_one χ) (by aesop_cat))

/-- The global Artin map sends the idele with the single component x at v to the local Artin
symbol Art_v x. -/
@[simp] lemma artinMap_locIdele v x : artinMap Γ (locIdele v x) = artinAt Γ v x :=
  abelianization_ext (by simp_all [finprod_eq_single _ v])

omit [MulSemiringAction Γ Ω] G

/-- Norm compatibility: let j: Ω → Ω extend K → L, and g ∈ Gal(Ω/K), g' ∈ Gal(Ω/L) satisfy jg =
g'j. If Art_L y is the class of g', then Art_K of the norm of y is the class of g. -/
lemma artinMap_adeleNorm {L} [Field L] [EmbeddedNumberField L] [Algebra K L] [MulSemiringAction Γ Ω]
  [G : IsProGalois Γ K Ω] {Γ'} [Group Γ'] [TopologicalSpace Γ'] [MulSemiringAction Γ' Ω]
  [IsProGalois Γ' L Ω] {y} {g : Γ} {g' : Γ'} (hy : artinMap Γ' y = g') (j : Ω →+* Ω := 1) (hj : ∀ x,
  j (algebraMap K Ω x) = algebraMap L Ω (algebraMap K L x) := by simp) (h : ∀ z, j (g • z) =
  g' • j z := by tauto) : artinMap Γ (y.map (adeleNorm K L)) = g := (exists_galois_restrict ..).elim
  fun φ hφ ↦ G.faithful.1 (j.injective <| h _ ▸ hφ _ ·) ▸ abelianization_ext fun χ ↦ .trans
  (mem_of_locIdele_mem (H := ((abelianLift χ).comp (.comp ..)).eqLocus ((abelianLift (QZChar.comap φ
  _)).comp _)) (by apply isClosed_eq <;> simp <;> fun_prop) (FinPlace.isPlaceOver_placeOver · |>
  fun h ↦ congr(id $(by simpa [adeleNorm_locIdele, h.artinAt_eq_of_localArtin_eq (Quotient.out_eq
  _).symm] using! (congrArg _ (IsPlaceOver.artinAt_eq_of_localArtin_eq (by simp [hj ·,
  val_comap_lt_one, ← h _]) ((h.localArtin_adeleNorm _ j hφ hj).1 (by simp)))))))) (congrArg _ hy)

@[local simp] lemma map_adeleNorm_principalIdele {K L : Type} [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra K L] x : (principalIdele x).map (adeleNorm K L) =
  principalIdele (x.map (Algebra.norm K)) := by aesop

lemma adeleNorm_mem_closure {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] {y v} : adeleNorm K L y v ∈ _root_.closure (.range (algebraMap K _ <| Algebra.norm K
    (S := L) ·)) := map_mem_closure ((continuous_evalAt v).comp (by fun_prop))
  (denseRange_algebraMap_finAdele y) (by aesop)

variable {Γ K L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra K L] [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω] {χ : QZChar Γ} [IsProGalois (ker χ) L Ω]

/-- Let the continuous character χ : Γ → ℚ/ℤ cut out the finite extension L of K. If u ∈ K_v^×
is a limit in K_v of norms from L to K, then χ vanishes on the local Artin symbol Art_v(u). -/
lemma abelianLift_artinAt_of_mem_closure {v : FinPlace K} {u} (h : u.1 ∈ _root_.closure
    (.range (algebraMap K _ <| Algebra.norm K (S := L) ·)) := by exact adeleNorm_mem_closure) :
  abelianLift χ (artinAt Γ v u) = 1 := Units.isOpenMap_val.preimage_closure_subset_closure_preimage
  h _ ⟨⟨((continuous_abelianLift χ).comp (continuous_hom_locField_units _)).1 {1}ᶜ ⟨⟩⟩, fun w ⟨z,
  e⟩ ↦ (Units.ext e : ideleAt v (principalIdele (.map (Algebra.norm K) (.mk0 z (by simpa [·] using
  e.symm)))) = w) ▸ v.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff.2
  (congrArg _ ((cyclicClass_eq_zero_iff_norm _).2 ⟨_, rfl⟩))⟩

@[simp] lemma abelianLift_artinMap_adeleNorm y :
  abelianLift χ (artinMap Γ (.map (adeleNorm K L) y)) = 1 := abelianLift_artinMap_eq_finprod χ _
  ▸ finprod_eq_one_of_forall_eq_one fun _ ↦ abelianLift_artinAt_of_mem_closure

/-- Let L be the field cut out by the character χ, w a finite place of L above v. Every x in
K_v^× with χ(Art_v x) trivial is the local norm of an element of L_w^×. -/
lemma exists_localNorm_of_abelianLift_artinAt {w : FinPlace L} {x} (hx : abelianLift χ (artinAt Γ _
  x) = 1) : ∃ y, localNorm K w y = x := w.isPlaceOver_placeOver.localArtin_adeleNorm (ker χ).subtype
  (hj := IsScalarTower.algebraMap_apply K L Ω).2 (by aesop)
  (w.isPlaceOver_placeOver.isPlaceOver_below.abelianLift_artinAt χ x ▸ hx)

/-- Let f : E → G be a homomorphism to a commutative group, J, N subgroups of G with f(E)·J = G,
and U = f⁻¹J. Then [G : f(E)(N ∩ J)] · [U : U ∩ f⁻¹N] = [J : J ∩ N]. -/
lemma relIndex_mul_index_sup {E G} [Group E] [CommGroup G] {f : E →* G} {J N U} (h :
  f.range ⊔ J = ⊤) (e : ∀ {x}, f x ∈ J ↔ x ∈ U) : (N.comap f).relIndex U * (f.range ⊔ N ⊓ J).index =
  N.relIndex J := by simpa [sup_inf_assoc_of_le, h, ← J.relIndex_sup_left (_ ⊔ _),
  sup_assoc, sup_comm f.range, ← relIndex_comap, ← map_comap_eq, (J.comap f).ext @e, N.comap_inf,
  inf_relIndex_right, inf_sup_self] using (N ⊓ J).relIndex_inf_mul_relIndex (N ⊓ J ⊔ f.range) J

/-- Albert–Brauer–Hasse–Noether: a class in Br(K) = H²(Γ, Ω^×), K a number field, is zero if it
dies on every decomposition group at a finite place and on some open subgroup containing all
complex conjugations.

Known result: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence,
norms. -/
lemma albert_brauer_hasse_noether α (h : ∀ {A : ClosurePlace} {v : FinPlace K}, IsPlaceOver A v →
  (unitsModule Γ).resH2 (decompGroup Γ A) α = 0)
  (U : OpenSubgroup Γ) (c : ∀ c, IsComplexConj c → c ∈ U) (e : resH2 _ U α = 0) : α = 0 := by
  wlog H : U.Normal ∧ Fact U.index.Prime
  · exact mem_of_prime_step ⊥ (W := ⟨_, have := U.finiteIndex_of_finite_quotient
      isOpen_of_isClosed_of_finiteIndex _ (normalCore_isClosed _ U.isClosed)⟩) (α.ind' (fun _ ↦
    (pairMapH2 (.mk (inclusion U.normalCore_le)) .id).congr_arg) e) fun U V _ _ i p _ z ↦
    (⟨_, z, this _ (z ▸ by simpa using! resH2_swap <| congrArg _ <| h ·.isPlaceOver_below) V (fun _
      ⟨j, _⟩ ↦ i fun b ↦ c _ ⟨j.comp (toRingHom _ _ b⁻¹), by simp [mul_smul]; bound⟩) · ⟨‹_›, ⟨p⟩⟩⟩)
  obtain ⟨_, l⟩ := finrank_fixedFieldOf U.1 ▸ H
  obtain ⟨⟨⟩, χ, rfl⟩ := U,
    exists_ker_eq_of_isCyclic U (isCyclic_of_prime_card (finrank_fixedFieldOf _).symm)
  set L := fixedFieldOf (ker χ)
  obtain ⟨⟨x, ⟨⟩⟩, d, g₂⟩ := ((cyclicClass_spec χ).1 _).1 e, @exists_idele_classGroup_hom L ..
  obtain ⟨S, F, g, _, G⟩ := exists_sup_idelesUnitOff_eq_top (((Set.finite_iUnion fun c ↦
    finite_idele_val_ne_one (.map (adeleNorm K L) (invFun d c))).union (finite_ramified ‹_›)).union
    (finite_idele_val_ne_one (principalIdele x)))
  have m v := by simpa using (@g v).mt
  have T := by simpa using tendsto_place_comap_cofinite (algebraMap K L) F.compl_mem_cofinite
  have vK {w : FinPlace L} (h : w.below K ∉ S) := by
    simpa [(w.isPlaceOver_placeOver.isPlaceOver_below.ramification_in_tower _
      w.isPlaceOver_placeOver).2.1 ((m _ h).1.2 _ w.isPlaceOver_placeOver.isPlaceOver_below),
      (w.comap _).3,
    Ideal.ramificationIdx'_eq_ramificationIdx] using (w.below K).valuation_liesOver L (K := K) w
  let t := MonoidHom.pi fun v : S ↦
    ((abelianLift χ).comp (artinAt Γ v.1)).rangeRestrict.comp (ideleAt _)
  have N y : t (.map (adeleNorm K L) y) = 1 := by ext; use abelianLift_artinAt_of_mem_closure
  obtain ⟨⟨S, rfl⟩, ⟨_, eT⟩, ⟨_, eS⟩, C⟩ := F.exists_finset_coe, dirichlet_unit_theorem T,
    dirichlet_unit_theorem F, second_inequality L ((principalIdele.range ⊔ t.ker ⊓ idelesUnitOff
    S).isOpen_of_mem_nhds ((eventually_artinAt_eq_one χ).mono fun _ h ↦ mem_sup_right
    ⟨by ext; apply h.2, by simp_all⟩)) (fun _ _ ↦ mem_sup_left ⟨_, rfl⟩) fun y ↦ by
    refine mem_comap.1 ((comap_map_eq_self (g₂ ▸ sup_le ?_ ?_)).le ⟨_, ?_, apply_invFun_apply⟩) <;>
      simp +contextual [*, LE.le, mem_sup_left, mem_sup_right, v_adeleNorm_eq_one]
  have key := by simpa [cokerKerIndex_eq_pow_finrank, ne] using
    (tate_index_formula_norm _ rfl ((FinPlace.comap (algebraMap K L) ⁻¹' S).unit
    L) ((SetLike.coe S).unit K) (by ext; simp +contextual [Set.unit, vK, (FinPlace.comap_surjective
    (algebraMap K L)).forall]) (fun g y hy w h ↦ by
    erw [← v_algebraMap_eq_valuation, ← locMap_algebraMap g.toRingHom rfl,
      v_locMap_eq_of_surjective _ _ g.surjective, v_algebraMap_eq_valuation, hy]
    rwa [← g.toAlgHom.comp_algebraMap] at h) fun z hz ↦ (exists_idele_eq_uniformizer_zpow _
    ((finite_idele_val_ne_one (principalIdele (z.map (Algebra.norm K)))).subset fun v ↦
    mt (congr($(·).log / Nat.card Gal(L/K)).trans (by simp)))).elim fun a ha ↦
    (exists_valuation_eq_of_mem_sup (G ▸ mem_top a)).imp fun x hx w h ↦ by simp [← vK h,
    hx _ h, vK h, ha, Algebra.norm_eq_prod_automorphisms, (by simpa [div_eq_iff] using hz · w h)])
  norm_cast at *
  have E := le_of_mul_le_mul_right (((pow_left_inj l.1.pred_pos.ne').1 (mul_right_cancel₀ out (by
    erw [mul_pow, mul_mul_mul_comm, key, pow_right_comm, pow_sub_one_mul l.1.ne_zero, ← pow_succ,
    eS, ← pow_succ, eT, relIndex_ker, Nat.card_congr (.subtypeUnivEquiv fun a ↦
      pi_mem_of_mulSingle_mem a fun v ↦ (a v).2.imp' (locIdele _) (by
      simp +contextual [← and_forall_ne v.1, t, Pi.mulSingle, eq_update_iff]; bound)), Nat.card_pi,
      (⟨comap_surjective.forall.2 fun ⟨_, _, rfl⟩ ↦ isUnramified_iff.2 ((isReal_or_isComplex
      _).imp_left fun r ↦ (exists_smul_emb_eq Γ _ (star _) (isReal_mk_iff.1 r).symm).elim fun g h ↦
      ⟨_, isReal_comp_algebraMap (c := (⟨g, c _ ⟨_, h⟩⟩ : ker χ)) h,
    rfl⟩)⟩ : IsUnramifiedAtInfinitePlaces K L).card_infinitePlace, pow_add, pow_add, pow_mul', ←
    mul_assoc, ← Nat.card_coe_set_eq, card_preimage_eq_sum_card_image_eq fun _ _ ↦ T.subset (by
    aesop_cat), ← sum_attach, ← prod_pow, ← prod_pow_eq_pow_sum, univ_eq_attach, ← prod_mul_distrib,
    prod_eq_pow_card fun v _ ↦ ?_, card_attach]
    rw [v.1.isPlaceOver_placeOver.range_abelianLift_artinAt, ← relIndex_ker,
      ← v.1.isPlaceOver_placeOver.ncard_above_mul_relIndex (ker χ)] at *
    cases Nat.prime_mul_iff.1 l.1 <;> simp [*, L, Nat.Prime.pos, ← Set.coe_ofPred _]))).trans_le
    (relIndex_mul_index_sup G principalIdele_mem_idelesUnitOff ▸ mul_le_mul_right C.2.1 _)) l.1.pos
  exact (cyclicClass_eq_zero_iff_norm _).2 ((not_and_not_right.1 (E.not_gt <|
    @index_strictAnti _ _ _ _ · ⟨(by simp [relIndex, ·, l.1.one_lt, ne'] at key)⟩)
    (comap_mono (by simp [LE.le, ← map_adeleNorm_principalIdele, N])) (x := ⟨x, (m · · |>.2)⟩) (by
    ext v; apply v.1.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff.2
      (h v.1.isPlaceOver_placeOver))).elim (⟨·, ·.2⟩))
