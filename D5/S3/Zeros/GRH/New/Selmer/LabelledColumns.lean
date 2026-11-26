/- GID: D5/S3/Zeros/GRH/New/Selmer/LabelledColumns
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/LabelledColumns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.LabelledColumns. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/LabelledColumns.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.LabelCompatibility
import D5.S3.Zeros.GRH.New.Selmer.ValueFamilies
import D5.S3.Zeros.GRH.New.Selmer.HeckeStableSubspaces
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations of theta lifts: irreducible block plus string (see
New.Selmer.RowsExist).

This file: Labelled representations are rows via tame inertia; quadratic inertia relation at twist
primes. -/
seal Finset.univ Finset.sum Finset.prod

open Matrix Polynomial Fintype Fact IsAlgClosed Fint NumberField

open Multiset hiding card

section

variable {ℓ} [hp : ThePrime ℓ] {P} {D : Data P} {r n} [Fintype r] [Fintype n]

attribute [local simp] Algebra.smul_def Units.ext_iff NeZero.pos eval_multiset_prod
  Data.TameChar.invAvatar

/-- Let x be a root of unity in ℚ̄_ℓ. If (x^a)^{ℓ^u} ≠ (x^b)^{ℓ^u} for all u, then x^a − x^b is
a unit. -/
lemma norm_pow_sub_pow_eq_one {x : PadicAlgCl ℓ} (h : IsOfFinOrder x) a b (H : ∀ u,
  (x ^ a) ^ ℓ ^ u ≠ (x ^ b) ^ ℓ ^ u) : ‖x ^ a - x ^ b‖ = 1 := by
  choose u k c e using WfDvdMonoid.max_power_factor h.orderOf_pos.ne' hp.out
  let z : intQpBar ℓ := ⟨x, h.norm_eq_one.le⟩
  refine (z ^ a - z ^ b).2.antisymm ((not_lt.1 ((valuation_natCast_eq_one c).not_lt ∘
    valuation_intQpBar_lt_one_iff.2)).trans ((norm_natCast_le_norm_sub_of_pow_eq_one ?_ ?_
    (H u)).trans ((Valuation.integer.integers _).le_of_dvd
    (sub_dvd_pow_sub_pow (z ^ a) (z ^ b) _)))) <;> rw [← pow_mul, ← e, pow_right_comm] <;> simp

variable [PadicIso ℓ] {O : AuxPair D.E r n} {ϑ c} (m) [Fintype m]

/-- For apt c and A above g_l, some γ (the tame generator at chosen places) works: each inertial
s has r + t numbers y, with y^(g_l^{r!} − 1) = 1, y^(g_l^d − 1) = 1 for some 1 ≤ d ≤ D.r, y
≠ 1 if t = 0 and s = γ, such that ∏(X − y) kills s, and s^{−c} at the conjugate place, on
all `IsLabelledColumn` R with labels times (X − 1)^t. -/
lemma exists_inertia_eigenvalues (hc : IsApt O c ϑ) {l} {v : FinPlace _} (hv : ↑(D.g l) ∈ v.1) {A :
  ClosurePlace} (hA : IsPlaceOver A v) t : ∃ γ, (D.IsChosen v → γ = hA.tameGenerator) ∧
  ∀ s ∈ inertiaGroup _ A, ∃ μ, Multiset.card μ = card r + t ∧ (∀ y ∈ μ, (t = 0 → s = ↑γ → y ≠ 1) ∧
  y ^ (D.g l ^ (card r).factorial - 1) = 1 ∧ ∃ d ∈ Set.Icc 1 D.r, y ^ (D.g l ^ d - 1) = 1) ∧
  ∀ {R k J S}, IsLabelledColumn (m := m) O k J (twistedLabel O c · * (X - 1) ^ t) S R → let P :=
    (μ.map (X - C ·)).prod; PolyKillsAt R A s P ∧ PolyKillsAt R (conjPlace A) (conjGal s⁻¹) P := by
  wlog h : D.IsChosen v generalizing v A
  exact (this (by simpa) hA.conjPlace_star ((D.isChosen_star_iff hv).2 h)).elim fun γ w ↦
    ⟨⟨_, conjPlace_conjPlace ▸ γ⁻¹.2.conjPlace_conjGal⟩, h.elim, fun s u ↦
    (w.2 _ (inv_mem u).conjPlace_conjGal).imp (by simp +contextual; grind)⟩
  obtain ⟨i, rfl⟩ : ∃ i, O.chosenPlace i = v := hc.1 ▸ D.range_chosen.ge h
  have l : IsLabel _ (twistedLabel ..) := (hc.isLabel i).scaleRoots _
  refine ⟨_, by tauto, fun s u ↦ ((exists_isTameExponent _ hA _).2 s u).elim fun y ⟨H, F⟩ ↦ ⟨_, by
    simp [l.2, card_aroots_eq_natDegree, l.1.natDegree_mul', ← C_1, -map_one, X_ne_C],
    forall_mem_map_iff.2 fun x hx ↦ ?_, fun N ↦ (fun k ↦
    ⟨k, ((conjPlace_conjPlace ▸ local_clauses_of_conjPlace N.1.1) (N.local_conditions _ (by grind
    [placesAboveG]) hA).1).2.2 s u _ k⟩) ((congrArg prod (map_map ..)).substr (N.labelled H))⟩⟩
  obtain ⟨-, p | ⟨rfl, z⟩⟩ := by simpa using hx
  refine ⟨fun _ e u ↦ hc.isLabel_twistedLabel i (by simp_all [aeval_def, (pow_eq_one_iff_of_coprime
    (F e)).1 ⟨IsFaithfulMulChar.injective (by cases y <;> simp_all [ιℓ.map_eq_one_iff,
    MulChar.pow_apply', ← map_pow]), (l.root_pow_eq_one p).1⟩]), (l.root_pow_eq_one p).imp ?_
    (.imp fun d ↦ .imp (by grind [IsApt]) ?_)⟩ <;> simp_all [D.q_eq_g hv, ← map_pow]
  simpa [z] using ⟨1, .refl, D.nat_le_of_hasLogBound⟩

/-- For apt labels c, a labelled column R of rank r with the twisted labels of c, empty
extra level, and jumps satisfying `IsRowType` is a row (`IsRow`) for k and
these jumps. -/
lemma IsLabelledColumn.isRow (hc : IsApt O c ϑ) {R k J} (h :
  IsLabelledColumn (m := r) O k J (twistedLabel O c) ∅ R)
  (hJ : IsRowType D (card r) k J) : IsRow D k J R := (D.g_injective.exists_ne ℓ).elim fun l hl ↦ by
  choose i L g using hc.exists_primitive l
  obtain ⟨⟨_, n, p, d⟩, ⟨A, B, -⟩, ⟨G, v, S⟩, hA, hℓ, j, ⟨J, hj⟩, b⟩ := (by grind [Parameters,
    Nat.prime_two, Nat.prime_five] : ∃ p ≠ ℓ, p.Prime ∧ p ∣ P.N₀ * P.d),
    (D.range_chosen.ge (isChosen_chosenPlace hc.1 i).1).choose_spec ▸ D.dvd_card_resField_sub_one _,
    isChosen_chosenPlace hc.1 i, (O.chosenPlace i).isPlaceOver_placeOver,
    hl ∘ (FinPlace.charP_quotient _ L).eq _ ∘ FinPlace.charP_quotient _, hc.tame_part_eq
  obtain ⟨⟨e, y, E, Y⟩ : ∃ e y, (∀ ξ, (twistedLabel O c i).aeval ξ = 0 → ξ ^ e =
    y ∧ ξ ^ (O.chosenPlace i).q ^ card r = ξ ∧ ∀ u, (Set.Iio (card r)).InjOn fun a ↦
    (ξ ^ (O.chosenPlace i).q ^ a) ^ ℓ ^ u) ∧ ∀ x, y ^ x = 1 → _ ∣ j * x, F, hv, ⟨s, H⟩, φ, hφ⟩ :=
    g.elim (fun ⟨R, h⟩ ↦ have z@⟨L, I, y, h⟩ := h.scaleRoots _ (charName_pow_eq_one
      (by simp [b ▸ D.omega_zpow_mul_pow_eq_one j v])) B
    z.isPrimitiveRoot_prod_roots.2.imp fun _ N ↦ ⟨_, fun x o ↦ ⟨N x (mem_aroots.2 ⟨I.ne_zero,
      o⟩), by rw [← card_ResField, root_pow_card_pow_eq_self_iff I o, L.2.2.1], fun a _ _ _ _ _ ↦ by
    apply frobenius_conj_pow_injOn a A (R.trans D.r_pow.choose_spec ▸ h.2) hp.out <;> grind
      [card_ResField, pow_right_comm, exists_pow_card_pow_eq_of_root I o]⟩,
      (z.isPrimitiveRoot_prod_roots.1.2 · · |> B.trans |> dvd_of_mul_left_dvd |>.mul_left _)⟩)
    (fun _ ↦ ⟨1, by simp [MulEquiv.map_eq_one_iff, *, twistedLabel, ← card_ResField, ← map_pow,
    ← C_1, -map_one, FiniteField.pow_card, pow_mul, ← D.orderOf_ω G, orderOf_dvd_iff_pow_eq_one,
    ← Units.val_pow_eq_pow_val]⟩), (h.local_conditions _ nofun hA).1,
    hA.valuation_natCast_eq_one_iff.2 hℓ,
    (exists_isTameExponent _ hA _).1.imp fun _ t ↦ h.labelled t, hA.exists_isFrob (AbsGal D)
  obtain ⟨ζ, z⟩ := IsAlgClosed.exists_root (R s).1.charpoly (by simp; grind)
  obtain ⟨ξ, ⟨-, hξ⟩, rfl⟩ := by simpa using isRoot_of_isRoot_charpoly (H.1 hv) z
  have o := ((hc.isLabel i).scaleRoots _).root_pow_eq_one hξ
  simp_rw [Set.InjOn, ← IsFaithfulMulChar.injective.eq_iff, ← ιℓ.injective.eq_iff, map_pow,
    map_one] at *
  obtain ⟨o, T⟩ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, by simp, o.1⟩,
    F.aeval_eq_zero_of_roots hv s.2 H
  refine ⟨h.1, hJ, ?r, (?r _ ⟨S, hℓ⟩ hA).elim fun _ ⟨M, _, v, w, _⟩ ↦ (CoeffRing.eventually_mem
    o.norm_eq_one.le).mono fun _ h _ a ↦ (a.span_eq_top_of_tame_pair (ζ := ⟨_, h⟩) ((hA.tame_inertia
    R (F.1 hv) v (by simpa using w) s).2 _ _ hφ).symm (fun _ p _ q n ↦ norm_pow_sub_pow_eq_one o _ _
    (n ∘ (E ξ hξ).2.2 · p q)) z (by simpa +contextual [E] using (T (X ^ (O.chosenPlace i).q ^ card
    r - X) :))).imp_right (.rec (⟨_, l, ·, by simp [hφ.cycChar_eq ℓ hv, D.q_eq_g L], ·⟩)), _, ⟨_,
    ⟨S, hℓ⟩, _, hA, (s ^ e).2⟩, _, by simpa +contextual [E] using (T (X ^ e - C (ιℓ (faithfulChar _
    y))) :), fun a t U ↦ by simpa [pow_mul, *] using norm_pow_sub_pow_eq_one o (e * _ * t) 0
                              fun c f ↦ (Nat.le_of_dvd (mul_pos J U.1) ((Nat.coprime_pow_primes _
    (a + c) p out n).dvd_mul_right.1 (by grw [d, mul_assoc, ← Y _ (by simpa [pow_mul, pow_add,
    pow_right_comm, *] using f), Parameters.Mω, ← le_self_add]))).not_gt (by
    grw [hj, U.2, hc.rank_le.1, ← p.two_le]; use D.nat_lt_of_hasLogBound)⟩
  rintro w ⟨⟨i, b⟩, v⟩ A a
  choose s t _ _ d H using exists_inertia_eigenvalues r hc b a 0; simp at d H
  refine ⟨s, _, t, ?_, fun t c ↦ by simpa +contextual [d t c] using
    ((h.local_conditions _ nofun a).1.aeval_eq_zero_of_roots (a.valuation_natCast_eq_one_iff.2 v) c
    (H t c h).1 (X ^ (D.g i ^ (card r).factorial - 1) - 1) :), fun b ↦ ?_⟩
  simp [↓a.valuation_natCast_eq_one_iff, ← algebraMap_ResField_eq_zero, ← D.q_eq_g b,
    ← card_ResField]
  grw [(by simpa using (det_aeval_neg_eq_prod_roots (R (idOrConjInv b s)).1 (-X - 1) :) :),
    apply_prod_le_sum_map _ _ (by simp [ellVal]) (@ellVal_mul_le _ _),
    sum_map_le_sum_map ellVal (fun _ ↦ crudeUnit ℓ D) (forall_mem_map_iff.2 fun x u ↦ ?_)]
  simp [card_roots_eq_natDegree]
  choose b _ j u e using
    d s s.2 x (by simpa using ((isRoot_of_isRoot_charpoly · (isRoot_of_mem_roots u))
    (b.rec (·.2.1 (by simpa [a.conjPlace_star.valuation_natCast_eq_one_iff]))
    (·.1.1 (a.valuation_natCast_eq_one_iff.2 v)) (H s s.2 h))))
  grw [← ellVal_le_crudeUnit D ℓ i (u.imp_right D.nat_le_of_hasLogBound.trans'), ellVal_le_ellVal]
  simpa using norm_natCast_le_norm_sub_of_pow_eq_one e (one_pow _) (b rfl)

/-- For apt data with Q auxiliary, let R be attached to an eigenform of parahoric type (1,
ψ_w⁻¹) at each w in Q. Then u = Rχ₁⁻¹ satisfies (u − a)(u − 1) = 0 on inertia above Q ∪ Q̄,
a the avatar of ϑ⁻¹. -/
lemma normalisedRep_quadratic_on_inertia [Nonempty n] (hc : IsApt O c ϑ) (hQ :
  IsAuxiliary (badPlaces D ℓ) ϑ.Q) {f : (stdSpace _ n).forms (O.κ, O.detExp)} {H R} (he :
  IsEigenform f.1 H) (h : Attached H R) (p : ∀ i, HasParahoricType f.1 (O.apart.2 _ (.inr i))
  (ρ := Empty) .ofIsEmpty (if · ∈ Set.range O.incl then 2 else 1) 1 ![1, (O.ψ _)⁻¹] fun _ ↦ f) :
  ∀ g ∈ inertiaAbove (.conjClosure ϑ.Q),
  ((normalisedRep O R g).1 - ϑ.invAvatar g • 1) * ((normalisedRep O R g).1 - 1) = 0 := by
  rintro s ⟨w, hv, A, hA, hs⟩
  have : ↑ℓ ∉ w.1 := by grind [placesDividing]
  suffices IsFiniteTypeAt R A ∧ PolyKillsAt R A s ((X - C (ϑ.invAvatar s)) * (X - 1)) by
    simp_all [Units.smul_def, chiOneInv_spec hA _ 0 (inv_mem hs), PolyKillsAt,
      hA.valuation_natCast_eq_one_iff]
  wlog hw : w ∈ ϑ.Q generalizing w A s
  refine (this (conjGal s⁻¹) _ ?_ _ hA.conjPlace_star ?_ ?_ ?_).elim fun a q ↦
    cast ?_ ((local_clauses_of_conjPlace (isConjSelfDual_of_attached he h) a).imp_right
    (·.2 _ ?_ _ q)) <;> simp_all [eq_inv_of_mul_eq_one_left (avatar_conjGal_mul _ 0 0 s)]
  obtain ⟨⟨i, rfl⟩ : ∃ i, O.twistPlace i = w, y, G, -⟩ := hc.1 ▸ ⟨⟨_, hw⟩, rfl⟩,
    (exists_isTameExponent (faithfulChar (ResField w)) hA _).2 s hs
  have := isLabelledAt_avatar ϑ.hasWeight.inv 0 0 (by simp_all [ϑ.1.5, ϑ.1.6]) (by grind) G
  refine (h.isLabelledAt f.2 he (HasParahoricType.hasProductLabel (χ := ![1, _⁻¹]) (σ := 1)
    (c := 1) 1 (by tauto) ?_ (by simpa [congrFun hc.tame_part_eq.choose_spec.2 _,
    D.omega_eq_one_of_not_isChosen (D.levelNorm_mem_and_notMem_of_mem_Q _ ‹_›).2.1] using! p i)
    ?_ ?_) hA).elim fun F b ↦ ⟨F, (F.aeval_eq_zero_of_roots · hs (b.2 G).1 _ ?_),
    absurd ?_ (‹PadicPlaceEmbedding ..›.inducesPlace.1.1 ▸
    valuation_comap_intQpBar_lt_one _).ne⟩ <;> open Calc in simp_all [or_imp,
    hA.valuation_natCast_eq_one_iff, PolyKillsAt, he.1, algebraMap_eq_diagonal, funext_iff,
    labelIdem, IsLabel, asAlgebraHom_eq_sum, Hall.evalGL, ϑ.psi_ne_one]

end

variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {P} {D : Data P} {r n m : Type} [Fintype r] [Fintype n]
  [Fintype m] {O : AuxPair D.E r n} {ϑ} {c : ∀ _, _} {R : GalRep ℓ D.E m} {k S} {A : ClosurePlace}

attribute [local simp] Units.smul_def Units.ext_iff cycInv

/-- Twisting a labelled column by the avatar of an algebraic character whose tame part ψ is trivial
off the chosen places gives a labelled column: the jumps shift by the weight, and the roots of each
label are scaled by the label of ψ. -/
lemma IsLabelledColumn.twist_avatar {J a e ψ b} (h : IsLabelledColumn O k J c S R) (hμ :
  AutChar.HasWeight a e ψ) (k' j : ℤ) (hb : (b - 1 : ℕ) + (2 * j - k') = (k - 1 :)) {d} (hc :
  IsApt O d ϑ) (hH : ∀ v, ¬D.IsChosen v → ψ v = 1) : IsLabelledColumn O b (fun σ ↦ (J σ).map
  (· + -(hμ.toAlgebraic k' j).1.2.toAdd σ)) (fun i ↦ (c i).scaleRoots (charName (faithfulChar
  (ResField (O.chosenPlace i))) (ψ _)).1) S (twistByChar (hμ.toAlgebraic k' j).avatar R) := by
  choose x u z w using fun {A μ} ↦ local_clauses_twist A (r' := twistByChar μ R) (by tauto)
  use ⟨⟨.of_coeHom_comp (.smul (by fun_prop) (.comp (by fun_prop) h.continuous)),
    h.nondeg.twist _, by simp [eq_sub_of_add_eq' hb, h.trace_conj, zpow_sub₀, field,
     eq_mul_inv_of_mul_eq (avatar_conjGal_mul ..)]⟩, fun v hv A a ↦ (h.local_conditions v hv a).imp
    (x · (avatarCompatAt_of_stablyUnram _ a).1) (.imp (z · (avatarCompatAt_of_stablyUnram _ a).2.1)
    fun f n ↦ u (f n) ((avatarCompatAt_of_stablyUnram _).sphericalClause_of_unramified (by simp_all
    [hμ.charUnramifiedAt_toAlgebraic, placesAboveG, D.isChosen_iff.not]) a).1)⟩, fun i A s y hy ↦
    w ((h.labelled hy).of_dvd ?_) (by simpa using isLabelledAt_avatar hμ _ _ (hH _
    (isChosen_chosenPlace hc.1 i).1.not_star) (O.isConjApart_chosenPlace.2 i i) hy)
  by_cases c i = 0 <;> simp_all [aroots, map_scaleRoots, roots_scaleRoots, multiset_prod_comp,
    Multiset.prod_dvd_prod_of_dvd, dvd_iff_isRoot]

/-- The representation attached to an eigenform of rank m, spherical at the places off S or above ℓg
that are neither chosen nor conjugate to a chosen place, and with label c_i (`HasProductLabel`) at
each chosen place, is a labelled column with labels c_i·(X − 1)^{m−r}. -/
lemma isLabelledColumn_of_hasProductLabel {d} (hc : IsApt O d ϑ) {κ f s H} (hf :
  f ∈ (stdSpace _ m).forms κ) (he : IsEigenform f H) (hR : Attached H R) (hK : ∀ v ∉ S \
  (placesDividing _ ℓ ∪ placesAboveG D), v ∉ (Set.range O.chosenPlace).conjClosure → f ∈ sphericalAt
  (rightRegular ℂ ..) v) {t : Fin s → ℕ} (h : ∀ i, HasProductLabel f (O.isConjApart_chosenPlace.2 i
  i) (faithfulChar (ResField (O.chosenPlace i))) (card r) (c i) 1 t) [Nonempty m] :
  IsLabelledColumn O (card m) (jumps κ (card m))
  (c · * (X - 1) ^ (card m - card r)) S R := have L i := (hR.isLabelledAt (A := ·) hf he (h i))
  ⟨⟨isConjSelfDual_of_attached he hR, fun v k A hA ↦ by grind [(sphericalCompat_std v hf he).2 hR,
    local_clauses_of_conjPlace (isConjSelfDual_of_attached he hR), !isChosen_chosenPlace hc.1,
    hA.conjPlace_star, isGoodAt_iff]⟩, fun i A _ _ H ↦ by simpa [Finset.prod_pow_eq_pow_sum, ← (h
    i).2.2.1] using ((L i A H.1).2.2 H).1⟩
