/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Characters/UnramifiedPeriods
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Characters.UnramifiedPeriods. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Characters/UnramifiedPeriods.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Pseudocharacter.FibreSum
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.GoodCriterion
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Characters with finite image on inertia are potentially crystalline of weight 0 (known
result; see Lib.PadicHodge.Characters.LocalCharacters).

Set-up used by: Characters with finite image on inertia are potentially crystalline of weight 0.

This file: Algebra lemma: killing polynomials in all positive degrees give one in degree zero.
Finite type, weights, killing polynomials pass to retracts and along open embeddings. Twisting by a
character keeps goodness, shifts weights, rescales killing polynomials. Potentially unramified
characters are potentially crystalline, with jumps and Frobenius; Lang for GL_1. -/
seal Finset.univ Finset.sum Finset.prod

open Polynomial Finset Ideal Quotient PiTensorProduct Matrix Topology Multiset

/-- Let S, T in a ring A commute with the image of a field K, and α_i, a_i ∈ K with a_i ≠ 0. If
∏(T − a_i) = 0 and ∏(ST^k − α_i a_i^k) = 0 for all k ≥ 1, then ∏(S − α_i) = 0. -/
lemma eval₂_eq_zero_of_pos_pow {K A n} [Field K] [Ring A] {g : K →+* A} {α a : Fin n → K}
    (S T : Subring.centralizer (.range g)) (u : (∏ i, (X - C (a i))).eval₂ g T = 0) (o : ∀ i,
    a i ≠ 0) (h : ∀ k > 0, (∏ i, (X - C (α i * a i ^ k))).eval₂ g (S.1 * T ^ k) = 0) :
    (∏ i, (X - C (α i))).eval₂ g S = 0 := by
  let Z := Subring.centralizer (.range g)
  let := (g.codRestrict Z ?_).toAlgebra' ?_
  norm_cast at *
  simp_all [↓← show ∀ P (x : Z), aeval x P = eval₂ g x P from (hom_eval₂ · _ Z.subtype)]
  set q := ∏ i, (X - C (a i))
  obtain ⟨y, _⟩ := (((isUnit_of_dvd_unit (map_dvd (mk (span {q})) q.X_dvd_sub_C) (by simp [q, o,
    IsUnit.map, Finset.prod_eq_zero_iff, coeff_zero_prod, -map_prod])).map (Pi.constRingHom (Fin n)
    _)).map (tprodMonoidHom K)).mem_nonZeroDivisors, (monic_prod_X_sub_C a univ).finite_quotient
  let ⟨p, m, z⟩ := (IsAlgebraic.of_finite K _).exists_nonzero_coeff_and_aeval_eq_zero y
  simp_rw [aeval_eq_sum_range, ← map_pow] at z
  apply_fun lift (.mkPiAlgebraFin ..) ∘ₗ PiTensorProduct.map fun i ↦ .coprod .id (Algebra.linearMap
    K Z) ∘ₗ .mulLeft K (S, -α i) ∘ₗ AlgHom.toLinearMap ⟨lift _ (aeval (T, a i)).1 (by simp [*, q,
    mem_span_singleton', aeval_prod_apply, eval_prod, Finset.prod_eq_zero (mem_univ i)]),
    aeval_C _⟩ at z
  simp_all [sum_range_succ', ← List.prod_ofFn, map_list_prod, Function.comp_def, sub_eq_add_neg]
  all_goals simp_all [Z, Subring.mem_centralizer_iff, ← map_mul, mul_comm, Subtype.ext_iff]

/-- Suppose r'(g)P = P r(φg) for g in a neighbourhood S of 1, P'P = 1, and the open embedding φ
is conjugation by c ∈ Aut Ω. Then finite type, killing polynomials on S, and (if PP' = 1)
jumps pass from r' at c⁻¹A to r at A. -/
lemma local_clauses_of_retract {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E E' m m'} [Fintype m] [Fintype m']
  {P : Matrix m' m (PadicAlgCl ℓ)} {P' : Matrix m m' (PadicAlgCl ℓ)} [Field E] [Algebra E Ω]
  [Field E'] [EmbeddedNumberField E'] {r : GalRep ℓ E m} {r' : _ →* GL m' _} {A} (c :
  Ω ≃+* Ω) i (hi : ∀ x, c (algebraMap E' Ω (i x)) = algebraMap E Ω x) {φ : _ →* Gal(Ω/E)} (hφ :
  ∀ g x, φ g (c x) = c (g x)) (he : IsOpenEmbedding φ) {S} (hS : S ∈ 𝓝 1) (h : ∀ g ∈ S,
  (r' g).1 * P = P * (r (φ g)).1) (q : P' * P = 1) : let A' := A.comap c; (IsFiniteTypeAt r' A' →
    IsFiniteTypeAt r A) ∧ (P * P' = 1 → ∀ {R J}, JumpsRelAt r' A' R (J <| ·.comp i) →
    JumpsRelAt r A R J) ∧ ∀ s ∈ S, ∀ {Q}, PolyKillsAt r' A' s Q → PolyKillsAt r A (φ s) Q := by
  have hD {g} : φ g ∈ decompGroup _ A ↔ g ∈ decompGroup _ (A.comap c : ClosurePlace) := by
    simpa [↓mem_decompGroup_iff, ← hφ] using (reindex_equiv c).1
  simp [IsFiniteTypeAt, PolyKillsAt, isEquiv_comap.eq_one_iff_eq_one]
  have M := by simpa [ext_iff_mulVec, ← mulVec_mulVec] using (h · · |>.symm)
  have I x (h : Unit → P.toLin'.restrictScalars ℤ_[ℓ] x = 0) := by
    simpa [q] using congr(P' *ᵥ $(h ()))
  use fun G H ↦ ⟨fun v ↦ map_one φ ▸ he.map_nhds_eq _ ▸ (G v).mp (.mono hS fun g b a d ↦ by
    simpa [← P'.mul_assoc, q, a (d.imp hD.1 (by simp_all [← hφ, val_comap_lt_one]))] using
    congr(P' * $(h g b)).symm), @fun a ↦ ?_⟩, fun p R J H a γ τ t ↦ ?_, fun s hs Q G H ↦
    ⟨fun v ↦ by simpa [*, ← P'.mul_assoc] using congr(P' * $(aeval_semiconj (h s hs).symm Q)),
    @fun a b k d ↦ ?_⟩ <;> (
    obtain @⟨a, e, ⟨⟨⟩, k⟩, u⟩ := a
    have l : InducesPlace E' _ (e.comp c) (a.toGp.comp (φ.restrict fun _ ↦ hD.2)) :=
      (exists_inducesPlace _ _ (by rfl)).rec fun J l ↦ (J.ext fun g ↦ eq_of_smul_eq_smul
      ((denseRange_emb_padicAlgCl (e.comp c)).eq (by simpa [k, ← hφ] using! l.1.2 g))).subst l
    let J := OverGp.mk _ ⟨l.2.1.2⟩
    obtain ⟨H, n, o⟩ := @H ⟨_, l⟩, map_nearOne _ u.1.1.2 J.2,
      (nearOne_eq_nhds_one l.2.1 ▸ continuousAt_subtype_val.eventually_mem hS).mono (M ·)
    try simp [IsPotCrys, IsKilledBy, linearFrob, Dpcris, ← n, ← isAdmissible_comp_iff _ J.2])
  exact .of_jointly_injective le_rfl (by tauto) _ (by tauto) I
  convert H t
  aesop
  exacts [by rw! [jump, hodgeTateMaps, ← n]; exact (jump_baseChange (φ := 1) (ρ :=
    decompRep (r.comp φ) _) _ _ _
    (symm ∘' (Pi.basisFun ..).map_apply (toLin'OfInv q p)) o).symm, IsKilledBy.of_jointly_injective
    ‹_› _ (by tauto) I le_rfl (fun _ ↦ @H (hD.1 b) _ d) Q.map_id (by simp)]

/-- For r' = μ ⊗ r at A: finite type and unramified (crystalline above ℓ) pass from r and μ to
r', and the jump of μ shifts the jumps. If X − c kills s on μ and Q(cX) on r, then Q kills s
on r'. -/
lemma local_clauses_twist {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E m} [Field E] [Algebra E Ω] [Fintype m]
  {r r' : GalRep ℓ E m} A {μ} (h : ∀ g, (r' g).1 = (μ g).1 • (r g).1) : let ν :=
    ((GeneralLinearGroup.scalar (Fin 1)).comp μ); (IsFiniteTypeAt r A → IsFiniteTypeAt ν A →
    IsFiniteTypeAt r' A) ∧ (IsGoodAt r A → IsGoodAt ν A → IsGoodAt r' A) ∧ (∀ {R J} {u : _ → ℤ},
    JumpsRelAt r A R J → HasJumpsAt ν A ({u ·}) → JumpsRelAt r' A R fun τ ↦ (J τ).map (· + u τ)) ∧
    ∀ {s Q c}, PolyKillsAt r A s (Q.comp (C c * X)) → PolyKillsAt ν A s (X - C c) →
    PolyKillsAt r' A s Q := let B := (Algebra.lsmul ..).toLinearMap ∘ₗ .proj 0
  have K := by simp [h, B, mul_comm]
  have H {j F} := (IsAdmissible.of_bilinear (𝒥 := j) (F := F) B K · · (⟨1 ⊗ₜ ·, by simp [B]⟩))
  ⟨fun ⟨a, c⟩ ⟨b, e⟩ ↦ ⟨fun l ↦ (a l).mp ((b l).mp (by simp_all [GeneralLinearGroup.ext_iff])), H e
  c⟩, fun ⟨_, c⟩ ⟨_, e⟩ ↦ ⟨by simp_all [GeneralLinearGroup.ext_iff], H e c⟩, fun a b i γ τ t v ↦ by
    obtain ⟨f, ⟨x, hx⟩, h, -⟩ := by simpa [jump, finrank_eq_one_iff', DFunLike.ext_iff] using
      (@b i _ _ t _ ▸ count_singleton_self _ :)
    rw [← sub_add_cancel v, count_map_eq_count' _ _ (add_left_injective _), jump_twist_of_period _
      hx ((h x).mp _)] <;> aesop, fun ⟨a, a'⟩ ⟨b, b'⟩ ↦ ⟨by simp_all [funext_iff, algebraMap,
    aeval_comp, Algebra.smul_def], fun w ↦ match a' w, b' w with | ⟨a, p⟩, ⟨f, q⟩ => ⟨H f a, by
    have := congr($(linearFrob_baseChangePairing a w f _ K (H f a)) (1 ⊗ₜ 1)).symm
    convert (hom_eval₂ _ C (eval₂RingHom' _ _ (commute_coefEnd_linearFrob a w)) _).symm.trans p <;>
      clear * - B q this <;> simp_all [DFunLike.ext_iff, B, Lift.baseChangePairing]; tauto⟩⟩⟩

open Filter Function Algebra TensorProduct Module Multiplicative IsScalarTower Subgroup LinearMap
  IsAdicComplete PadicComplex
variable {p} [ThePrime p] {Γ T} [Group Γ] [TopologicalSpace Γ] [CommRing T] [Algebra ℤ_[p] T]
  [𝒥 : OverGp Γ p] {ν : Γ →* (PadicAlgCl p)ˣ}

attribute [local instance] SMulCommClass.symm

attribute [local simp] smul_tmul' Finset.smul_sum pow_mul frobEnd smul_sub

attribute [local simp ←] tmul_sub mul_assoc

noncomputable instance : MulSemiringAction FrobGal (Ainf ⊗[ℤ_[p]] T) :=
  ⟨by simp [TensorProduct.one_def],
  fun m ↦ (Algebra.TensorProduct.map (MulSemiringAction.toAlgHom ℤ_[p] _ m) (.id _ T)).map_mul⟩

/-- Let O be a finite free commutative Z_p-algebra, a ∈ O with 1 − a nilpotent mod p. Some unit
y of A_inf⊗O has φ^n g·y ∈ O·y for all n ≥ 0, g ∈ G_p, and φ^k s·y = y, s·y = a^k y for Weil
pairs (s, k). -/
lemma exists_unramified_period [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (a : T) (h : ∃ e : ℕ,
  ↑p ∣ (1 - a) ^ e) : ∃ y : Ainf ⊗[ℤ_[p]] T, IsUnit y ∧ (∀ m : FrobGal, ∃ o, m • y = 1 ⊗ₜ o * y) ∧
  ∀ s k, IsWeilPair s k → (ofAdd k, s) • y = y ∧ s • y = 1 ⊗ₜ a ^ k * y := let φ := (ofAdd 1, 1)
  let d := DistribSMul.toLinearMap _ Ainf φ - .id
  let α := (1 : Ainf) ⊗ₜ a
  have ⟨⟨e, b, hb⟩, c⟩ := And.intro h (isAdicComplete_of_free (span {(p : Ainf)}))
  -- `α φ - 1` is onto, because `φ - 1` is onto and `1 - α` is nilpotent modulo `p`
  have ⟨y, hy, B⟩ : ∃ y, IsUnit y ∧ α * φ • y = y := (mem_range_of_approx (α •
    frobEnd.toAddMonoidHom - .id _) (map_natCast_smul _ Ainf Ainf p) (·) (fun v ↦
    (e.rec ⟨0, by simp⟩ fun k ⟨n, w, e⟩ ↦ (d.rTensor_surjective T
    (by simpa using! ·.exists_frobEnd_sub_xi_pow_mul_eq 0) w).rec fun x h ↦ ⟨n + (1 - α) ^
    k * x, φ • x, by simp [α, e, ← h, d]; ring!⟩ : ∃ n w, v = α * φ • n - n + (1 - α) ^ e * w).imp
    fun n ↦ .imp' (1 ⊗ₜ b * ·) (by simp [α, TensorProduct.one_def, hb, ← nsmul_eq_mul, φ,
    ← smul_mul_assoc])) 1).rec fun x k ↦ ⟨_, mem_jacobson_bot (x := 1 - α).1 (isRadical_jacobson _
    ⟨e, ((map_algebraMap_iff ..).2 c).le_jacobson_bot _ (by simp [α, TensorProduct.one_def, hb,
    mem_span_singleton, dvd_def, ← nsmul_eq_mul, -smul_tmul'])⟩) x, by simp_all [α]; grind⟩
  have G k m : α ^ k * (φ ^ k * m) • y = m • y := k.rec (by simp) fun k e ↦ by
    simpa [α, φ, smul_smul, pow_succ, Prod.mul_def, mul_right_comm] using congr(_ * _ • $B).trans e
  -- the fixed points of `φ` are the elements of `T`
  have E m := hy.dvd (a := m • y).rec fun z h ↦ .imp (by simp_all [mul_comm]) ((reindex_equiv
    (TensorProduct.lid ..).symm).2.1.1 ((Flat.rTensor_exact T (f := Algebra.linearMap ..)
    (g := d) (⟨exists_algebraMap_eq_of_frobenius_eq · ∘ (frobEnd_eq_frobenius _).symm.trans ∘
    sub_eq_zero.1, by aesop⟩) z).1 (by simpa [d, mul_smul, *, hy.mul_right_inj] using! G 1 m)))
  ⟨y, hy, E, fun s k w ↦ (E (ofAdd k,
    s)).rec fun o h ↦ let R := Algebra.TensorProduct.map toWittResidue (.id ℤ_[p] T)
    by simpa [(Flat.tensorProduct_mk_injective _ _ _ (by simpa [R, (hy.map _).mul_eq_right] using!
      (congr(R $h).symm.trans (y.exists_finset.elim (by simp_all [R,
      toWittResidue_smul_of_isFrob w])) : _ = R y)) :
      o = 1), h, φ, α, ← TensorProduct.one_def, ← ofAdd_nsmul] using! (G k (1, s)).symm⟩

/-- Let j be an open embedding, ν: Γ → Q̄_p^× a continuous character trivial on inertia near 1,
acting by scalars on a commutative Q̄_p-algebra T. Then T is potentially crystalline, has
the jumps of the trivial action, and X − ν(s) kills (s, k) for Weil pairs (j(s), k).

Known result: Characters with finite image on inertia are potentially crystalline of weight 0. -/
lemma isPotCrys_of_unramified_char [Algebra (PadicAlgCl p) T] [IsScalarTower ℤ_[p] (PadicAlgCl p) T]
  (hj : IsOpenEmbedding 𝒥.toGp) (c : Continuous ν) (hI : ∀ᶠ g in 𝓝 1, IsWeilPair (toGp g) 0 →
  ν g = 1) {ρ : Γ →* End _ T} (e : ∀ g x, ρ g x = (ν g).1 • x) : IsPotCrys ρ ∧ jump ρ = jump
  (1 : Γ →* End _ T) ∧ ∀ s k, IsWeilPair (toGp s) k → IsKilledBy ρ s k (X - C (ν s).1) := by
  have ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean _ (mem_comap'.1 (nearOne_eq_nhds_one hj ▸
    hI.and (Metric.continuous_iff'.1 (Units.continuous_val.comp c) 1 1 one_pos)))
  have ⟨L, ⟨_, f, n, _⟩, _⟩ := IsLocalGalois.of_finite (U ⊓ ⟨_, 𝒥.2.1⟩)
  obtain ⟨⟨⟨_, u, φ, rfl⟩, hφ⟩, F, -⟩ := L.frobenius_spec
  -- `φ` is a Frobenius of `U`, of degree `f`, and `a ≡ 1` is an `f`-th root of `ν φ`
  have ⟨a, b, h⟩ : ∃ a, a ^ f = (ν φ).1 ∧ ‖1 - a‖ < 1 := by_contra fun _ ↦ (hU u rfl).2.not_ge (by
    simpa [dist_eq_norm', (right_ne_zero_of_mul (n.1 ▸ index_ne_zero_of_finite)).pos] using
   pow_le_norm_aeval (X ^ f - C (ν φ).1 :) (ν 1).1 zero_le_one (by simp_all))
  have ⟨O, hO⟩ := (CoeffRing.eventually_mem h.le).exists
  obtain ⟨y, hy, E, W⟩ := exists_unramified_period (1 - ⟨_, hO⟩ : ↑O) (by simpa [O.dvd_iff_norm_le]
    using (exists_pow_lt_of_lt_one (norm_pos_iff.2 (NeZero.ne (p : ↑O))) h).imp (by bound))
  let Θ γ := productMap ((thetaBPlus.restrictScalars _).comp (toAlgHom _ Ainf _)) (.comp γ O.1.val)
  -- `g⁻¹ • y = ν g * y` on `U`: after `θ` this is a closed condition, true on `φ ^ k` times inertia
  have K : ∀ᶠ g in nearOne Γ, ∃ o, toGp g • y = 1 ⊗ₜ o * y ∧ o.1 = (ν g⁻¹).1 := ⟨_, U.mem_nhds_one,
    fun g _ ↦ (E _).imp fun o h ↦ ⟨h, by simpa [h, Θ, (hy.map _).ne_zero, ← map_inv₀, coe_eq] using
    (hj.isClosed_iff'.1 (isClosed_eq (y.exists_finset.rec (by simp_intro .. [Θ]; fun_prop))
    (by fun_prop) : IsClosed {g | Θ (toAlgHom ..) (toGp g⁻¹ • y) = ν g * Θ (toAlgHom ..) y}) _
    (Set.MapsTo.closure (by rintro _ ⟨⟨k, ⟨_, u, i, rfl⟩, hi⟩, rfl⟩; exact ⟨φ ^ k * i, by simp [↓W
    (toGp (φ ^ k * i))⁻¹ (f * k)
    (by simpa [IsWeilPair, residueCard_padic, ↓n] using! (hφ.pow k).mul_iff.2 hi), Θ,
    b, (hU u _).1 (inv_mem hi), coe_eq]⟩) continuous_subtype_val (F hφ ⟨toGp g⁻¹, by simpa⟩)))⟩⟩
  let Φ := Algebra.TensorProduct.map (toAlgHom ℤ_[p] Ainf Bcris) ((toAlgHom _ _ T).comp O.1.val)
  have P (m : FrobGal) h g x y : tensorAction _ m (ρ g) (1 ⊗ₜ x * Φ y) =
    coefEnd _ _ (ν h).1 (1 ⊗ₜ ρ (h⁻¹ *
    g) x * Φ (m • y)) := y.exists_finset.rec (by simp_intro .. [Φ, tensorAction, e, Finset.mul_sum])
  have D x : 1 ⊗ₜ x * Φ y ∈ Dpcris ρ := K.mono fun g ⟨o, h, k⟩ ↦ by
    erw [P _ 1, h]; simp [Φ, *, algebraMap_eq_smul_one]
  have Z : Surjective (mulRight Bcris _) := (hy.map Φ).unit.mulRight_bijective.2
  have S : IsPotCrys ρ := (Submodule.ker_mkQ _).symm.trans (ker_eq_top.2 ((cancel_right Z).1
    (by ext; simp [Submodule.mem_span_of_mem, D])))
  use S, ?_, fun s k w ↦ ⟨S, (cancel_right Z).1 ?_⟩ <;> ext γ
  simpa using y.exists_finset.elim fun S Y ↦ (exists_gp_eq_algHom γ).elim fun s r ↦
    (jump_twist_of_period (v := 0) (ν ·⁻¹ |>.1) (hy.map (Θ γ)).ne_zero (K.mp ((S.eventually_all.2
    fun i _ ↦ eventually_nearOne_apply_eq Γ (s i.2)).mono fun g l ⟨o, h, k⟩ ↦ by
    simpa +contextual [Θ, *] using congr(Θ γ $h).symm)) (by simp [e])).symm
  simp [linearFrob_apply, P _ s, *]
