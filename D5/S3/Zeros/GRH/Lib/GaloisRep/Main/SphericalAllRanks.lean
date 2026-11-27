/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/SphericalAllRanks
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/SphericalAllRanks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.SphericalAllRanks. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/SphericalAllRanks.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.AvatarCompatibility
import D5.S3.Zeros.GRH.Lib.GaloisRep.EvenRank.ThetaLift
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Galois representations for eigenforms of any rank, compatible at spherical places. -/

open NumberField Matrix Polynomial Filter Fintype Finset AlgHeckeChar AutChar Metric Classical Units

/-- For E with Weil data, every eigenform f on the definite U(n) has an attached ℓ-adic
representation. If K_w fixes f, each attached one is unramified or crystalline at w, with
the jumps of f's weight, and any Hecke polynomial there kills geometric Frobenius.

Known result: Galois representations attached to forms on definite unitary groups. -/
lemma sphericalCompat_std {ℓ E n} [ThePrime ℓ] [PadicIso ℓ] [Field E] [EmbeddedNumberField E]
  [CMType E]
  [Fintype n] [Nonempty n] [WeilData E] w : SphericalCompat E n (card n) w := fun P κ f hf h ↦ by
  let t := card n + 1
  -- two unramified characters of U(1) with different values at every split place (Kronecker)
  let c (i : Fin 2) u : ℤ := -torsionOrder E * ((-κ.2 u).toNat + ite (u = ofNonempty) i.1 0)
  choose μ hμ using (exists_hasWeight_of_prod_eq_one (S := ∅) (e := c ·) (by tauto)
    (by simp_all [c, _root_.zpow_mul, ← map_pow, _root_.pow_torsionOrder_eq_one]))
  have e {i} u : c i u ≤ κ.2 u := by simp [c]; grw [← (torsionOrder_pos E).nat_succ_le]; lia
  let θ i (l : Fin t) := (hμ i).toAlgebraic (card n + t) (t - l)
  have X₀ {l l' w} (_ : w.IsSplit) : heckeCoeff (θ 0 l).1.1 ∅ w ≠ heckeCoeff (θ 1 l').1.1 ∅ w :=
    fun e ↦ by
    choose n _ γ a k using ((hμ 0).mul (hμ 1).inv).exists_pow_eq_prod (divStar (locFullIdele w _))
      (Unitary.coe_mul_star_self 1)
    rcases a w, congrArg (w.valuation E) ((Φ _).injective (by simpa [c, mul_add] using (k.symm.trans
      congr($(div_eq_one.2
      (Circle.ext (by simpa [θ, heckeCoeff, HasWeight.toAlgebraic, HeckeChar.finPart, abs_of_nonneg,
      Real.sqrt_eq_zero'] using! congr($e / ‖$e‖)))).1 ^ n))) : γ.1 ^ _ = 1)
    simp_all [coe_divStar, locFullIdele, ← map_inv, NeZero.ne]
  have N := (eventually_mostFrobenii h.2 fun y ↦ (· y.prime_q)).and (.all fun i ↦
    ((hμ i).toAlgebraic t t).eventually_avatar_frob.and (.all (eventually_avatar_frob <| θ i ·)))
  let R i w := ∏ l, (X - C (heckeCoeff (θ i l).1.1 ∅ w))
  choose! F hF o h' Q q e' using fun {i} ↦ exists_theta_lift_heckePoly (hμ i) e rfl ⟨f,
    hf⟩ h.1 t.le_refl
  choose H σ s using
    (sphericalCompat_of_odd (by grind) w hF ⟨@o ·, by peel h.2 using q this.1 this⟩ |>.symm)
  let ρ i := twistByChar ((hμ i).toAlgebraic t t).avatar (σ i)
  have c i : Attached (P * R i) (ρ i) := (s i).imp (fun _ ↦ .of_coeHom_comp (.smul (by fun_prop) (by
    fun_prop))) (.imp (·.twist _) (.imp_right (· · · |>.mp <| N.mono fun y ⟨⟨_, p⟩, a⟩ ↦ by simp [R,
    θ, ← e' p.1 p, ρ, Units.smul_def, charpoly_smul_coeff, ← (a i).1, ← mul_sub, ((q p.1
    p).isMonicOfDegree o).1, mul_comm (ιℓ _), norm_eq_one_of_continuous, continuous_avatar])))
  have K {g} i := (ρ i g).1.trace_eq_neg_charpoly_coeff ▸ (((c i).tendsto_charpoly_coeff ..).neg.sub
    (tendsto_mostFrobeniiAt fun g ↦ ∑ l, ((θ i l).avatar g).1)).congr' (mem_inf_of_left (N.mono
    fun y a ↦ ((a.1.2.isMonicOfDegree h.1).rec fun d m ↦ by simp [R, a, by
    simpa [↓prod_X_sub_C_nextCoeff, nextCoeff, m.natDegree_mul, d, monic_prod_X_sub_C] using
      m.nextCoeff_mul (q := R i y.w) (monic_prod_X_sub_C ..)] :
    _ = -ιℓ ((P y.w).coeff (card n - 1)))))
  refine ⟨(IsTraceNondeg.exists_cancel_chars (by simp) (c · |>.2.1) (fun _ _ ↦ DFunLike.ne_iff.2
    (dense_of_mostFrobenii (N.mono fun y a e ↦ X₀ a.1.1 (by simpa [a] using congr($e.1)))).nonempty)
    fun _ _ ↦ eq_add_of_sub_eq (tendsto_nhds_unique (K _) (K 0))).imp fun r ⟨nr, hr⟩ ↦
    ⟨nr.continuous_of_trace (.congr (by cases c 0; fun_prop) hr), nr, .id, ((c 0).2.2.2 · · |>.mp <|
    N.mono fun y a b ↦ forall_eq.2 (norm_coeff_le_of_mul_monic (monic_prod_X_sub_C ..) (by
    simpa [sub_mul, charpoly_eq_mul_of_trace_pow_add _ _ _ (by simpa [sub_eq_iff_eq_add] using hr <|
      y.frob ^ ·), a, R, Polynomial.map_prod] using b)))⟩, fun r b x A hA ↦ ?_⟩
  have U i g := (r g).1.trace_eq_neg_charpoly_coeff ▸ tendsto_nhds_unique
    (b.tendsto_charpoly_coeff ..).neg (K i)
  choose T J H using (H · (s _) (h' x) A hA)
  choose x y G using fun {i a l} ↦ (avatarCompatAt_of_stablyUnram _).sphericalClause_of_unramified
    ((hμ i).charUnramifiedAt_toAlgebraic rfl rfl a l) hA
  choose _ u v z using (local_clauses_twist A (r' := ρ ·) fun _ ↦ rfl)
  choose Y Z K using fun i ↦ local_clauses_of_trace_limit (J := jumps κ (card n)) b.1 b.2.1 Eq (pure
    ()) (fun _ ↦ Option.elim' 1 (-1)) (fun _ ↦ (fun j ↦ Option.elim' (jumps κ (card n) + ∑ l, j l)
    j) _) (fun _ ↦ Option.elim' ⟨ρ i⟩ (⟨(GeneralLinearGroup.scalar _).comp <| θ i · |>.avatar⟩))
    (fun _ ↦ (·.rec (c i).1 fun _ ↦ .of_coeHom_comp <| .matrix_diagonal (by
    simp +instances; fun_prop))) (fun _ ↦ (·.rec (u i (T i) x) fun _ ↦ x)) (fun _ ↦ Option.rec (by
    convert! v _ (J i) y
    simp [jumps, HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, sum_ite, e, ← range_val,
      ← sum_multiset_singleton, ← Multiset.coe_mapAddMonoidHom, sum_range, Fin.sum_univ_add]
    apply congrArg₂ _ (by clear * -; grind); split
    exacts [by ring, sum_equiv Fin.revPerm _ _ (by simp +arith)]) fun _ ↦ y) (.inl inferInstance)
    (by simp +instances [tendstoUniformly_iff, U i])
    (by simp +contextual [eq_comm, Multiset.count_sum'])
  use Y 0, Z 0, fun hw P p s hs ↦ ?_
  have K i c := (K i .refl (fun _ o ↦ ⟨.refl, o.rec (z i ((H i _ _ (q p.1 p) s hs).of_dvd (by
    erw [← e' p.1 p, Polynomial.comp, eval₂_map, scaleRoots_eval₂_mul]; simp [Polynomial.map]))
    (G s hs)) fun l ↦ (G s hs).of_dvd (by simp [dvd_iff_isRoot, R, θ, eval_map, eval₂_finsetProd,
       prod_eq_zero (mem_univ l)])⟩) (by simp +instances [tendstoUniformly_iff, U i, mul_sub,
       mul_sum])).of_dvd (Polynomial.map_dvd ιℓ.toRingHom (dvd_mul_right (P * R i w) c))
  have ⟨a, b, e⟩ : IsCoprime (R ..) (R ..) := .prod_left fun _ _ ↦ .prod_right fun _ _ ↦
    pairwise_coprime_X_sub_C (fun _ _ ↦ id) (X₀ hw)
  rw [← mul_one P, ← e, mul_add]
  clear * - K
  grind [PolyKillsAt, IsKilledBy, eval₂_add, Polynomial.map_add, K 0 a, K 1 b]
