import GRH.Lib.GaloisRep.BaseChange.UnitaryRoots
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: An adelic polynomial root of the norm can be corrected to a rational one. Splitting data
for the Weil representation pass to suitably unramified CM extensions. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-simp] Subtype.forall multiplicity_eq_one_of_not_finiteMultiplicity

open NumberField Matrix Polynomial UniqueFactorizationMonoid AdjoinRoot MulAction Function
  Norms.L2Operator Algebra AlgEquiv MulDistribMulAction Ideal ComplexConjugate Ring

/-- For a step E'/E, σ ≠ 1, σ^p = 1, z a root for P = σP = charpoly γ': some rational w and
adelic c make x = w·z·σc invertible at each adelic unitary γ killed by rad P, and a·x(γ)* =
x(γ) implies a·c(γ)* = c(γ). -/
lemma exists_global_root {E E' n} [Field E] [CMType E] [Field E'] [Algebra E E'] [Fintype n]
    {p μ} {σ : Gal(E'/E)} [Fact p.Prime] (ho : σ ^ p = 1) (hσ : σ ≠ 1) [hμ : IsStep (E := E) E' μ]
    {z} {γ' : U (n := n) 1} : let k := algebraMap E' _; let P := γ'.1.1.charpoly; σ • P = P →
    IsNormRoot n (adeleMap σ) p 1 (normKer _ μ) (P.map k) z → ∀ {γ : Gf _ n}, γ.1.1.charpoly =
      P.map k → let T c := z * mapRingHom (adeleMap σ.toRingHom) c; ∃ w c, ∀ x, .map k w * T c = x →
        ∀ γ : Gf _ n, aeval γ.1.1 ((radical P).map k) = 0 → IsUnit (aeval γ.1.1 x) ∧
        IsRootQuotient γ x ≤ IsRootQuotient γ c := by
  intro k P hγ hz γ e T
  obtain ⟨⟨_, v, hv⟩, hI⟩ := @id (IsCoprime P X) (isUnit_aeval_iff_isCoprime.1 (by simp)), fun {q} ↦
    mem_primeFactors.trans (P.mem_normalizedFactors_iff (p := q) (charpoly_monic _).ne_zero)
  have cj {γ : Gf E' n} (h : aeval γ.1.1 (P.map k) = 0) := by
    simpa [← aeval_comp, star, by simpa using left_inv_eq_left_inv γ.2 (by
      simpa [h] using congr(aeval γ.1.1 (map k $hv)))] using star_aeval (R := 𝔸f E') γ.1.1
  let τ := (toPerm σ).subtypePermOfFintype fun q h ↦ hI.2 ((hI.1 h).imp
    (.map (toMulEquiv _ σ)) (.imp (by simp [smul_eq_map]) (hγ ▸ map_dvd (toMulEquiv _ σ) ·)))
  have C S [CommRing S] f := pairwise_primeFactors_isRelPrime (a := P).imp fun _ _ ↦
    (·.isCoprime.map (mapRingHom (S := S) f))
  have crt {S} [CommRing S] f := exists_forall_sub_mem_ideal
    (((C S f).subtype _).mono fun _ _ ↦ (isCoprime_span_singleton_iff ..).2)
  have := e.symm.dvd.trans (charpoly_dvd_charpoly_aeval_comp (T^[p] 1 - X *
    ((T^[p] 1).map conj).comp (v.map k)))
  choose hq hm hP using fun q ↦ (hI.1 (Subtype.prop q)).imp_left Fact.mk
  let θ (q : primeFactors P) := aeval (R := 𝔸f E') (root q.1 : 𝔸f (AdjoinRoot q.1))
  choose _ h₁ sur ker F hβ using fun q ↦ adjoinRoot_cm_presentation (hm q) 1 (fun φ x h ↦ mod_cast
    (spectrum_subset_unitary_of_mem_unitary (U_one_mem_unitaryGroup ((U.map φ) γ'))
      (mem_spectrum_of_isRoot_charpoly ((isRoot_of_mem_roots h).dvd
        ((charpoly_map ..).substr (map_dvd φ (hP q)))))).2) (refl (θ q)) (.refl k)
  choose d hd e₀ using fun q ↦ (hz.2 _ e).1 _ (leftMulMatrix (Module.finBasis ..) (θ q X))
    (by simp [aeval_algHom_apply, *, mk_eq_zero.2])
  simp [← cj (e ▸ aeval_self_charpoly _), aeval_algHom_apply, ← norm_eq_matrix_det, by simpa [←
    (by rw [iterate_mul_apply, map_one, mul_one]; with_unfolding_all rfl : T^[p] 1 =
    twistedNorm (.map (adeleMap σ)) p z)] using (hz.2 γ e).2, mem_span_singleton] at this crt e₀ h₁
  have hu q := lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det _).2 ⟨_, e₀ q⟩)
  have hw q := left_inv_eq_right_inv (by simpa [hP, mk_eq_zero.2] using congr(mk q $hv)) (h₁ q)
  let g {q q'} (h : τ q = q') := mapAlgEquiv σ q q' (.of_eq (smul_eq_map E' σ ▸ congr($h)))
  have hT {q q'} h f : θ q' (T f) = θ q' z * adeleMap (@g q q' h) (θ q f) := by
    simp [θ, g, T, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
  choose y c₁ h₂ h₄ using fun q ↦ show ∃ y c, IsUnit (θ q c) ∧ IsSelfAdjoint
      (star (θ q c) * ((principalIdele y).1 * θ q (T^[period τ q] c))) by
    have i := isReduced_of_injective (RingHom.pi (evalAt (E :=
      AdjoinRoot q.1))) DFunLike.coe_injective
    cases' by simpa [← ker, *, map_X k ▸ F q X] using (map_dvd k (hP q)).trans this with N
    obtain f | rfl := (eq_or_ne (τ q) q).imp_right
      (minimalPeriod_eq_prime (by simp [τ, ← toPermHom_apply, ← map_pow, *] : (τ ^ p) q = _))
    have ⟨hg, hx⟩ : Semiconj (of q.1) σ (g f) ∧ g f (root _) = root _ := by simp [g, Semiconj]
    have := orderOf_eq_prime (coe_toAlgHom_injective (by ext <;> simp [iterate_fixed, ← coe_pow σ,
      ← hg.iterate_right p _, *]) : g f ^ p = 1) fun h ↦ hσ (ext (coe_injective' <| h ▸ hg ·))
    simpa [hT f, period_eq_one_iff.2, *, (sur _).exists, mul_assoc] using
      hμ.exists_selfAdjoint_of_norm hx
      adjoinRoot_eq_top (hu q).unit (.trans congr(μ $(by ext; simp [*])) (hd q))
      (by simpa [*, Semiconj.iterate_right (gb := (_ * adeleMap _ ·)) (hT f) p _] using! N)
    peel exists_star_principalIdele_mul_eq _ N using ⟨1, by simpa⟩
  let r q := @invFun _ _ ⟨q⟩ (periodicOrbit τ) (periodicOrbit τ q)
  choose e j J hr using by simpa [periodicOrbit] using (by simp [r, τ.injective.mem_periodicPts,
    invFun_eq, periodicOrbit_apply_eq] : ∀ q, r (τ q) = r q ∧ q ∈ periodicOrbit τ (r q))
  obtain ⟨⟨c, Y⟩, w, W⟩ := crt k fun q ↦ T^[j q] (c₁ (r q)),
    crt (.id _) fun q ↦ surjInv mk_surjective (y q ^ 0 ^ j q).1
  use w, c, fun x X γ h ↦ (crt k fun q ↦ surjInv (sur q) (θ q x)⁻¹ʳ).elim fun d hd ↦ ?_
  simp [← ker, ← mk_eq_mk, surjInv_eq] at W Y hd
  choose H G using @id (∀ q, IsUnit (θ q x) ∧ IsSelfAdjoint (star (θ q c) * θ q x))
      ((reindex_equiv τ).1.2 fun q ↦ by
    simp_rw [← X, map_mul, hT rfl, Y, ← hT, ← iterate_succ_apply', F, W]
    rw [iterate_injOn_Iio_minimalPeriod (J _) ((j q).succ.mod_lt (J _).pos)
      (by simp [↓iterate_succ', ↓← hr, e]), e, congrArg τ (hr q), ← iterate_succ_apply' τ]
    use .mul (.map _ ⟨_ ^ _, rfl⟩) ((j q).succ.rec (h₂ _) fun _ _ ↦ by simp [*, -hr, iterate_succ',
      -iterate_succ, IsUnit.map]), (Nat.eq_or_lt_of_le (J q)).elim (by
      rw [·, iterate_minimalPeriod]; simpa using! (h₄ _))
      (by simp [Nat.mod_eq_of_lt ·, -iterate_succ]))
  have K (f g : (𝔸f E')[X]) := by
    simpa [Subtype.forall', ← ker] using (aeval_eq_zero_of_dvd_aeval_eq_zero · h) ∘ (map_prod
      (mapRingHom k) ..).dvd.trans ∘ Finset.prod_dvd_of_coprime (C _ k) (z := f - g)
  use .of_mul_eq_one _ (by simpa [*, inverse] using K (x * d) 1), fun a b ↦ by rw [IsRootQuotient,
    cj, K _ (_ * (c * d)), map_mul, ← mul_assoc, ← cj, b, ← map_mul, mul_left_comm, K] <;> simp [*,
    -hr, -Y, K _ 0, ← mul_assoc, mul_inverse_cancel_right, (star_star_mul ..).symm.trans (G _)]

open WithZero Valued IsDedekindDomain HeightOneSpectrum FiniteMultiplicity Finset WeilData RingHom

attribute [local simp] prime of_prime_left differentIdeal_ne_bot im_pos

/-- If E carries Weil data, so does every stably unramified CM extension L with compatible CM
type such that no place v = v̄ of L divides the relative different. -/
lemma nonempty_weilData_of_unramified {E L : Type} [Field E] [CMType E] [Field L] [Algebra E L]
    [h : CMOver E L] [WeilData E] [StablyUnram L]
  (hu : ∀ v : FinPlace L, star v = v → ¬v.1 ∣ differentIdeal (𝓞 E) _) : Nonempty (WeilData L) := by
  obtain ⟨⟨_, -, -, g, -, _, H⟩, ⟨⟩, _⟩ :=
    @exists_reduction_and_idele_generator L _ _ (differentIdeal ℤ _) (by simp),
    exists_wellFoundedLT (FinPlace L), (by simpa [RingHom.ext_iff] using h.2 <| Φ ·)
  let i := algebraMap E L
  let s := principalIdele (.map i.1 (.mk0 j j_ne_zero)) * g
  have ⟨β, _⟩ := exists_idele_eq_uniformizer_zpow (fun u ↦
    (ite (u < star u) 1 0 - (v (s.1 u)).log) / 2) ((finite_idele_val_ne_one s).subset (by aesop))
  refine have : SplittingChar L := ⟨⟨υ.1.comp ⟨_, .units_map (.prodMap (.pi (∏ u with u.comap i = ·,
    Pi.evalMonoidHom _ u)) (adeleNorm ..)) (by simp [MonoidHom.pi]; and_intros <;> fun_prop)⟩,
    fun _ ⟨x, e⟩ ↦ υ.2 _ ⟨norm E x, ?_⟩⟩, fun _ _ ↦ by
    erw [υ_unit] <;> simp_all [prod_fiberwise, adeleNorm_mem_Ohat, Submonoid.mem_units_iff], fun _ ↦
    congr(υ.1 $(by bound)).trans (υ_star _)⟩; ⟨⟨i j, by simp [← map_star_CM], by aesop, β,
    fun u ↦ ?_, by simpa [map_ofNat] using map_isIntegral_int i isIntegral_traceOne,
      exists_eq_principalIdele_mul_norm.2.2⟩⟩
  ext w <;> simp [← e]
  algebraize [Φ w]
  erw [norm_eq_prod_embeddings]
  refine' prod_bij' (fun σ _ ↦ .mk σ) (fun u _ ↦ ⟨Φ u, _⟩) .. <;>
    simp [algebraMap_toAlgebra, i, ← (h.2 _).2] <;> aesop
  let w := FinPlace.below E u
  rcases valuation_star u (i j), self_dual w ▸ log_exp _, (H (star ↑g⁻¹)).1 (forall_ψf_mul_eq_one.1
    (by simp_all [↓ψf_star (_ * _), mem_Ô, forall_ψf_mul_eq_one.2 ∘ (H _).2])),
    self_dual w ▸ exp_ne_zero,
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L) ▸ emultiplicity_mul u.prime
  rw [← exp_log (x := v _), exp_inj] <;> simp_all [s, i, ← w.valuation_liesOver L, mem_Ô,
    ← map_star_CM, v_inv, ← log_le_log, emultiplicity_eq_multiplicity, irreducible,
    emultiplicity_map_eq_ramificationIdx'_mul (v := w.1), ← eq_sub_iff_add_eq, ne_bot,
    w.1.ramificationIdx'_eq_ramificationIdx _ w.ne_bot]
  norm_cast at *
  grind [multiplicity_eq_zero_of_not_dvd, star_star, below_star,
    @congrArg _ _ (star w) w (v <| α.1 ·)]
