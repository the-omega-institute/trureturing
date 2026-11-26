/- GID: D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerRelations
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.GreenbergWiles.SelmerRelations. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/GreenbergWiles/SelmerRelations.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles.GreenbergWilesBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Selmer conditions against trivialisations; many relations at split primes:
Greenberg–Wiles lower bound. -/

namespace selmerZ1

open NumberField Function Finset Classical QuotientGroup InfinitePlace DiscreteModule Fintype
  Submodule Filter Set Pi NeZero
variable {K R} [Field K] [EmbeddedNumberField K] [CommRing R] {M : DiscreteModule R Gal(Ω/K)} {S :
  Finset (FinPlace K)} {A : FinPlace K → ClosurePlace} (hu : ∀ g ∈ inertiaAbove Sᶜ, M.ρ g = 1) (hA :
  ∀ v, IsPlaceOver (A v) v) (L : ∀ _, Submodule R (_ → M)) (hL : ∀ v ∈ S,
  (d0 (M.restrictTo _).ρ).range ≤ L v) (hcM : ∀ {c}, IsComplexConj c → M.ρ c = 1) {m : ℕ} [NeZero m]
include hu hA hL hcM

/-- Let M be finite, unramified outside S (primes dividing N), fixed by complex conjugations, with
at most (#M)^k trivialised cocycles, and B¹ ⊂ L_v on S. Then `selmerZ1`, ramification allowed at the
primes of s, has #selmerZ1·(#M)^(#S+#∞) ≤ (#M)^k·∏_{v∈S} #(L_v ∩ Z¹), ∞ the infinite places of K. -/
theorem card_mul_pow_le [Finite M] {k U N I ι} [NeZero N] (s : SplitPlaces m N I U ι) (hk :
  M.HasFewCocycles (PlaceAboveS N) I k)
  (hT : ∀ v ∈ S, ↑N ∈ v.1) : .card (selmerZ1 M S A L (range s.v)) * .card M ^ (#S + card
  (InfinitePlace K)) ≤ Nat.card M ^ k * ∏ v ∈ S, .card ↥(L v ⊓ Z1 (M.restrictTo _).ρ) := by
  let J := (L · ⊓ Z1 (M.restrictTo _).ρ)
  let T := {v : FinPlace K | ↑N ∈ v.1}
  obtain ⟨_ : Finite T, ⟨⟩⟩ := finite_natCast_mem N, Nat.card_pos_iff.1 hk.1
  let F : selmerZ1 M S A L (range s.v) × (T ⊕ InfinitePlace K → M) →+ (∀ v : S, J v) × (↥(T \ S) →
    M) := .mk' (fun (y, m) ↦ (fun ⟨v, h⟩ ↦ ⟨_, sub_mem ⟨y.2.2.1 v h, .imp (·.comp (by fun_prop)) (by
    tauto) y.2.1.1⟩ ⟨hL v h ⟨m (.inl ⟨v, hT v h⟩), rfl⟩, (coboundary _ _).2⟩⟩, fun v ↦ (y - d0 M.ρ
    (m (.inl ⟨v, v.2.1⟩))) ((hA v).exists_isFrob _).choose)) (by intros; ext <;> simp <;> abel)
  choose f hf e using fun a : F.ker ↦ a.1.1.2.elim fun ⟨b, u⟩ C ↦
    trivialisedCocycles.exists_mem_of_orbit_reps (PlaceAboveS.bijective_orbits _ N hA) b (u · ∘
    .imp (by grind -zetaDelta -abstractProof) ∘ (s.mem_inertia_iff _).1) a.1.2 (by
    rintro ⟨v, n⟩ g e <;> injections
    · exact sub_eq_zero.1 (byCases (congr($(a.2).1 ⟨v, ·⟩ |>.1 ⟨g, ‹_›⟩)) fun h ↦
        Z1.eq_zero_on_decompGroup (⟨_, b⟩ - M.coboundary _) (hA v) (choose_spec _)
        (fun g i ↦ by simpa [hu g ⟨v, by tauto⟩] using u g ⟨v,
        (·.elim h fun ⟨j, e⟩ ↦ s.level_notMem j (e ▸ n)), _, hA v, i⟩)
          (congr($(a.2).2 ⟨v, n, h⟩) :) g ‹_›)
    cases eq_one_or_isComplexConj ‹_›; simpa [*] using b.2 1 1; simp [*, by simpa using C.2])
  have {v} : Finite (J v) :=
    .inter_of_right (((hA v).decompGroup_spec _).1.finite_Z1_local (M.restrictTo _)) _
  simpa [Nat.card_fun, Nat.card_pi, ← ncard_sdiff_add_ncard_of_subset (t := T) hT, pow_add,
    ← S.prod_attach, add_rotate (ncard _), ← mul_assoc] using! F.ker.card_mul_index.ge.trans
    (mul_le_mul' (hk.2.trans' (Nat.card_le_card_of_injective (⟨_, hf ·⟩) fun _ _ _ ↦ by
    ext <;> grind -zetaDelta -abstractProof)) ((AddSubgroup.index_ker F).trans_le F.range.card_le_card_addGroup))

/-- Relations at split primes. For U fixing M and μ_m, without complex conjugations, there are
split primes, Frobenii φ_i and elements γ_i such that each family (n_i) with ∑ n_i(x(γ_i)) =
0 on Selmer cocycles x extends to an equivariant homomorphism on U giving such relations at
other split primes. A bound on trivialised cocycles bounds their number below.

Known result: Greenberg–Wiles formula, as a lower bound for the dual side. -/
lemma exists_split_primes_relations N [AddCommGroup N] [Module (ZMod m) M] U (hU :
  M.TrivialOn U.1.1) (hUm : ∀ g ∈ U, cycCharMod Ω m g = 1) (hc : ∀ {c}, IsComplexConj c →
  c ∉ U) : let Y := selmerZ1 M S A L; ∃ q ι I, ∃ (_ : NeZero q) (_ : Fintype ι) (s :
    SplitPlaces m q I U ι) (γ : ι → _), ∃ π T, (∀ v ∈ S, ↑q ∈ v.1) ∧ S ⊆ T ∧ IsLocallyConstant π ∧
    (∀ [Finite M], M.HasFewCocycles (PlaceAboveS q) I (card ι + 1) → .card (Y ∅) * .card M ^ (#S
    + card (InfinitePlace K)) ≤ .card {n : ι → M →+ QZ | ∀ x ∈ Y (.range s.v), ∑ i, n i (x (γ i)) =
    0} * .card M * ∏ v ∈ S, Nat.card ↥(L v ⊓ Z1 (M.restrictTo _).ρ)) ∧ s.FrobeniiDetectRoots ∧ ∀ n :
    ι → M →+ N, (∀ x ∈ Y (.range s.v), ∑ i, n i (x (γ i)) = 0) → (∀ i, n (π (s.φ i)) = n i) ∧
    (∀ g, ∀ a ∈ U, ∀ b ∈ U, ∀ x, n (π (a * (g * b * g⁻¹))) x = n (π a) x + n (π b)
    ((cycCharMod Ω m g).1 • M.ρ g⁻¹ x)) ∧ ∀ {J : Type} [Fintype J] (v C φ δ : J → _), Injective v →
    (∀ j, v j ∉ T ∧ IsPlaceOver (C j) (v j) ∧ IsTameGeneratorFor m (C j) (δ j) ∧
    IsFrob (C j) (v j).q (φ j) ∧ φ j ∈ U) → ∀ x ∈ Y (.range v), ∑ j, n (π (φ j)) (x (δ j)) = 0 := by
  intro Z
  have o : Monotone Z := fun _ _ _ _ ↦ by simp [Z, selmerZ1, inertiaAbove]; grind
  have h {F} [Field F] [NumberField F] {T} (t : Set.Finite T) := t.eventually_all.2 fun
    (v : FinPlace F) _ ↦ .mono (mem_atTop _) fun _ h ↦ v.1.mem_of_dvd
    (Nat.dvd_factorial v.one_lt_q.le h).natCast v.1.absNorm_mem
  obtain ⟨r, hT, hr, i, d⟩ := ((h S.finite_toSet).and (.and (mem_atTop m) (.and (h (finite_ramified
    U.1.2)) ((@finite_range _ _ (fixedFieldOf U.1.1).lift (.of_equiv _
    IsGalois.intermediateFieldEquivSubgroup.1.symm)).eventually_all.2 fun F _ ↦ .all fun
    _ : NumberField F ↦ (exists_sup_idelesUnitOff_eq_top finite_empty).elim fun _ ⟨e, _, _, f⟩ ↦ (h
    e).mono fun _ k ↦ eq_top_mono (sup_le_sup_left (idelesUnitOff_mono (K := F) k) _) f)))).exists
  have n := mk r.factorial_ne_zero
  -- the m-th roots of the U-fixed r!-units form a finitely generated group
  obtain ⟨T, j⟩ := fg_of_fg_map_of_fg_inf_ker (m • .id) (.of_le (Module.Finite.iff_fg.1
    (dirichlet_fixedSUnits _ r.factorial U).1) (map_comap_le ..)) (.of_le
    (fg_range (rootPowHom Ω m).1.toIntLinearMap) fun _ h ↦ by exact ((rootPowHom ..).2.2 _).2 h.2)
  obtain ⟨⟨O, h⟩, F⟩ := exists_openNormalSubgroup_apply_eq (Y := T) ((unitsModule
    Gal(Ω/K)).continuous.comp (f := Prod.map id (↑)) (by fun_prop)), @finite_natCast_mem K _ _ _ n
  let ι := _ ⧸ O.1.1
  have hN {g k} (e : (⟦g⟧ : ι) = ⟦k⟧) y (m : m • y ∈ fixedSUnits _ U) : unitsRep k y =
    unitsRep g y := LinearMap.eqOn_span (by simpa using!
    (congr(unitsRep g $(h _ (QuotientGroup.eq.1 e) ·)))) (j.ge m)
  obtain ⟨_, ⟨e, _⟩, u, H⟩ := ofFinite ι, exists_injective_nat ι, seq_of_forall_finite_exists
    fun t f ↦ skolem.1 fun c ↦ chebotarev (U.1.2.inter (isOpen_discrete {(@invFun U ι _ (↑)
    c : ι)})) ⟨_, by simp, rfl⟩ (F.union (f.seq finite_univ))
  choose a _ P hP φ b hφ _ using fun c ↦ by simpa using H (e c) c
  let s : SplitPlaces .. := ⟨hUm, Nat.dvd_factorial one_le hr, _, by grind [Injective], by grind, P,
    hP, φ, (⟨hφ ·, (b _).1⟩), by congr!, by grind, fun F i ↦ (d F ⟨_, F.lift_restrict ·⟩ i)⟩
  have hκ g h : (s.φ ⟦g⟧ : ι) = g := (b _).2.trans (@apply_invFun_apply U ι (↑) ⟨g, h⟩)
  obtain ⟨_, γ, hγ⟩ := by simpa using hκ 1, skolem.1 (exists_isTameGeneratorFor Gal(Ω/K) m <| hP ·)
  have z {P x} (h : x ∈ Z P) i n : _ = _ := h.1.2 _ ⟨_, (·.elim (s.level_notMem i ∘ hT _) n), _,
    hP i, (hγ i).1⟩
  refine ⟨_, ι, _, n, ‹_›, s, γ, (↑), S ∪ F.toFinset ∪ univ.image s.v, hT, by simp,
    isOpen_discrete, fun k ↦ ?_, by grind, fun ν hν ↦ ?_⟩
  have := by simpa [pairingAnnihilator, Nat.card_pi] using (card_pairingAnnihilator_mul_card (∑ i,
    (evalAddMonoidHom _ i).flip.comp (evalAddMonoidHom _ (γ i))) (.refl _) (Z (range
    s.v)).toAddSubgroup).ge.trans' (mul_le_mul_right (Nat.card_mono ((finite_unramified_cocycles
    M).subset fun _ ↦ (·.2.1)) fun x h ↦ .intro (by simp [z h]) (o bot_le h)) _)
  grw [← mul_le_mul_iff_right₀, ← mul_assoc, this, mul_assoc,
    card_mul_pow_le hu hA L hL @hcM s k hT, pow_succ]
  ac_nf
  simp
  have fam {J I} [Fintype J] (s : SplitPlaces m r.factorial I U J) (γ : J → _) hγ i j k g (E :
    (s.φ i : ι) = ↑(s.φ j * (g * s.φ k * g⁻¹))) a : ∃ z ∈ Z (range s.v), ∀ n, z (γ n) = ite (n =
    i) a 0 - ite (n = j) a 0 - ite (n = k) ((cycCharMod Ω m g).1 • M.ρ g⁻¹ a) 0 :=
    (s.power_residue_reciprocity γ hγ hU).rec fun b ⟨h, t⟩ ↦ by
    obtain ⟨⟨P, hP, _⟩, _, _⟩ := t.2 ⟨fun _ ↦ not_isReal_iff_isComplex.1 (exists_isComplexConj
      U.1.1 · |>.rec (flip hc ·.2))⟩ (Pi.single (i, 1) 1 - Pi.single (j, 1) 1 - Pi.single (k,
      mk g⁻¹) ↑(cycCharMod Ω m (s.φ j * g))) (fun y ↦ (y.1.exists_nsmul (ne m)).rec fun x q ↦
      (rootPowHom Ω m).2.1 (by simp [q, sub_mul, mul_comm (b _ _), map_cycCharMod_mul, h _ x,
      ← hN E, -map_mul, unitsRep.map_mul, h (fixedSUnitsRep _ U g⁻¹ y) _
      (q ▸ map_nsmul (unitsRep _) ..).symm])) a, skolem.1 (mk_out_eq_mul U.1.1)
    have c x g (e : g • x = x) := sub_eq_of_eq_add' (e ▸ hP.2.1 ..)
    have f B h g e := c (.inl ⟨B, h⟩) g congr(.inl ⟨$e, _⟩)
    use P.2, ⟨⟨trivialisedCocycles.snd_mem_Z1 hP, fun g ⟨v, n, B, k⟩ ↦ byCases (hP.2.2 g) fun _ ↦ f
      B (by grind [s.mem_inertia_iff, k.1.valuation_natCast_lt_one_iff]) g k.2.1 ▸ by simp [hu g ⟨v,
      n ∘ .inl, _, k⟩]⟩, fun v h ↦ hL v h ⟨_, funext (f _ ((hA v).valuation_natCast_lt_one_iff.2
      (hT v h)) _ ·.2)⟩, fun g h ↦ c (.inr _) g (congrArg _
      ((mem_stabilizer_mk_iff ..).2 (.inr (RingHom.ext h.choose_spec).symm))) ▸ by simp [hcM h]⟩
    simp [*, apply_ite (M.ρ _), ite_and, -mk_inv, ← mk_one, ZMod.map_smul, s.isFrob, sub_smul]
  have T i j k g E a := (fam s _ hγ i j k g E a).elim fun _ h ↦ by simpa [h, apply_ite (ν _), ι,
    sub_eq_iff_eq_add'] using (hν _ h.1)
  have := by simpa [*] using T 1 1 1 1
  refine ⟨fun i ↦ by ext; simp [*, T i (s.φ i) 1 1, s.isFrob], fun g a ha b hb ↦ T _ _ _ g (by simp
        [↓hκ, mul_mem ha (U.2.1 _ hb _), *]), fun v C φ δ hv H x hx ↦ ?_⟩
  choose _ n m c d f using by simpa [and_assoc] using H
  let s' : SplitPlaces .. := ⟨hUm, s.2, _, s.4.sumElim hv (swap m), Sum.rec s.level_notMem n,
    Sum.rec P C, Sum.rec hP
    c, Sum.rec _ φ, Sum.rec s.isFrob f, by congr!, s.inertiaGroup_le, s.principal_sup_idelesUnitOff⟩
  choose u hw _ _ using fun j ↦ by simpa using (fam s' (Sum.rec γ δ)
    (Sum.rec hγ d) (.inr j) (.inl (φ j)) (.inl 1) 1 (by simp [s', *]) (x (δ j)))
  simpa [*, apply_ite (ν _), @sum_comm _ _ ι, ι, z hx, Ne.symm (m _ _)] using hν _ ((sub_mem (o (by
    simp [s']) hx) (sum_mem fun _ _ ↦ hw _)).imp_left fun ⟨y, z⟩ ↦ ⟨y, fun τ ⟨w, h, B, b, c⟩ ↦ if o
    : w ∈ range v then o.rec (s'.apply_inertia_eq_zero b (i := .inr ·) · (d _) ⟨_,
    y⟩ hU (by simp [*]) c) else z τ ⟨w, h ∘ by simp [s', o], B, b, c⟩⟩)
