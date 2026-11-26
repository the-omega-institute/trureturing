import GRH.Lib.LocalGL.Green.CuspidalAtScalars
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: The Brauer lift is a virtual character, and cuspidal times Steinberg is induced
from a torus. Without Brauer induction, the character induced from the Coxeter torus is divided by
the Steinberg character, taken as a Möbius function on semisimple classes, compatibly with the
Galois action. Only the vanishing half of Crapo's theorem appears. Source: Green 1955, Thm 1; T. A.
Springer, Sém. Bourbaki 441 (1973/74), 1.1-1.7; for Steinberg times torus character, R. Carter,
Finite groups of Lie type (1985), 7.4.5, as cited by Hiss-Zalesski; for the vanishing of the Möbius
number off semisimple modules, P. Hall's lemma, D. Krasula, arXiv 2403.05656, Lemma 23, and H.
Crapo's complementation theorem (1966).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Naming characters of F_Q^× by field elements; multiplicativity and norm compatibility.
Cuspidal character times Steinberg is induced from the Coxeter torus. -/

open IntermediateField Complex ComplexConjugate Finset Hall IsGalois LinearEquiv Module MulChar
  Polynomial Units LinearMap.GeneralLinearGroup

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] (T) [IsFaithfulMulChar K T]
  {Q m} {x y z : K} (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (η : K → ℂ)

include hQ hx

omit [IsFaithfulMulChar K T] in
/-- Let T be a multiplicative character K → ℂ, Q ≥ 2, and x^(Q−1) = 1. Then there is a natural
number e with θ_x = T^e (θ_x taken for Q) and T(x) = exp(2πi/(Q−1))^e. -/
lemma thetaChar_spec : ∃ e, thetaChar T Q x = T ^ e ∧ T x = exp (2 * Real.pi * I / (Q - 1 :)) ^ e :=
  have : NeZero (Q - 1) := ⟨by lia⟩; ⟨_, rfl, @Classical.epsilon_spec _ (_ = _ ^ ·) (by
    grind [(isPrimitiveRoot_exp _ this.1).eq_pow_of_pow_eq_one, congr(T $hx)])⟩

omit [IsFaithfulMulChar K T] in
/-- Let Q ≥ 2, N ≠ 0 with N = (Q − 1)m, and x^{Q−1} = 1. If T(z) = exp(2πi/N)^a, then
θ_x(z^m) = T(x)^a, where θ_x is formed with Q. -/
lemma thetaChar_apply_pow {m a N} (hN : N ≠ 0) (hm : N = (Q - 1) * m)
    (h : T z = exp (2 * Real.pi * I / N) ^ a) : thetaChar T Q x (z ^ m) = (T ^ a) x := by
  obtain ⟨⟨x, rfl⟩, ⟨z, rfl⟩, _, _⟩ := IsUnit.of_pow_eq_one hx (by lia),
    T.apply_ne_zero_iff.1 (h.trans_ne (by simp)), thetaChar_spec T hQ hx
  simp_all [← exp_nsmul, pow_apply_coe]; grind [Nat.cast_eq_zero]

omit [IsFaithfulMulChar K T] in
lemma thetaChar_mul : y ^ (Q - 1) = 1 → z ^ (Q - 1) = 1 → thetaChar T Q (x * y) z =
  thetaChar T Q x z * thetaChar T Q y z := by grind [thetaChar_spec T,
  @thetaChar_apply_pow (m := 1), mul_pow, map_mul (thetaChar T Q z) x y]

omit [IsFaithfulMulChar K T] in
lemma thetaChar_eq_apply_norm_pow {m r a} (h : 2 ≤ m) (e : m = Q ^ r) (o : x ^ a = y) :
  z ^ (m - 1) = 1 → thetaChar T m y z = thetaChar T Q x (z ^ ∑ i ∈ .range r,
  Q ^ i) ^ a := by grind [thetaChar_spec T, thetaChar_apply_pow T, @thetaChar_apply_pow
  (m := 1), map_pow (thetaChar T m z) x a, pow_mul, one_pow, pow_right_comm, geom_sum_mul_of_one_le]

/-- For T injective, the group isomorphism χ ↦ x_χ from the multiplicative characters of k to
k^×, inverse to a ↦ θ_a restricted to k, with θ_a taken for Q = |k|. -/
noncomputable def charName : MulChar k ℂ ≃* kˣ := .symm (.ofBijective (F := _ →* _)
    (.mk' (fun a ↦ ⟨(thetaChar T (.card k) (algebraMap k K a)).comp (algebraMap k K), by simp⟩) (by
    simp [MulChar.ext_iff, thetaChar_mul T Finite.one_lt_card])) (((injective_iff_map_eq_one
  _).2 fun a h ↦ (thetaChar_spec T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one a)).elim
  fun e ⟨p, q⟩ ↦ by rw [← Nat.card_units, ← IsCyclic.exponent_eq_card, ((isPrimitiveRoot_exp _
  NeZero.out).pow_eq_one_iff_dvd e).2 (Monoid.exponent_dvd_of_forall_pow_eq_one _)] at q <;> cases e
  <;> simp_all [pow_apply', ← map_pow, IsFaithfulMulChar.injective, map_eq_one_iff, MulChar.ext_iff,
  ← val_eq_one]).bijective_of_nat_card_le (card_eq_card_units_of_hasEnoughRootsOfUnity ..).le))

omit hQ hx

/-- For T injective, every multiplicative character χ of k is the restriction to k of θ_{x_χ},
formed with Q = |k|: θ_{x_χ}(y) = χ(y) for all y ∈ k. -/
lemma thetaChar_charName χ y : thetaChar T (.card k) (algebraMap k K (charName T χ))
  (algebraMap k K y) = χ y := congr($((charName T).1.3 χ) y)

lemma charName_pow_eq_one {T} [IsFaithfulMulChar K T] {χ M} (h : χ ^ M = 1) :
    (charName T χ).1 ^ M = (1 : k) := mod_cast by simp [← map_pow, h]

open Fint

/-- For a finite extension L of k embedded by φ in K, the inner product on GL_{[L:k]}(k) of C_η with
B·μ is the mean over z ∈ L^× of conj η(φz) times B at multiplication by z.

Known result: The Brauer lift is a virtual character; cuspidal times Steinberg is induced from a
torus. -/
lemma rankInner_greenCuspidal_mulMu {L} [Field L] [Finite L] [Algebra k L] (φ : L →ₐ[k] K) (B :
  Hall k) : rankInner (finrank k L) (greenCuspidal k η) B.mulMu = finMean fun z :
  Lˣ ↦ conj (η (φ z)) * B (simClassOf (LinearMap.mulLeft k z.1)) :=
  let ρ (e : L ≃ₗ[k] L) := (e.conjAlgEquiv k).toAlgHom.comp (Algebra.lmul ..); let := φ.toAlgebra
    have H e z : simClassOf (ρ e z) = simClassOf (LinearMap.mulLeft k z) :=
      simClassOf_eq_of_equiv e⁻¹
    have E g : (greenCuspidal k η).mulMu (simClassOf g) =
        (∑ z, η (φ z) * Nat.card {e // ρ (generalLinearEquiv k L e) z = g}) / Nat.card Lˣ := by
      obtain h | ⟨a, y, rfl⟩ := em' (∃ a y, ρ a y = g); simp_all; by_contra! ⟨h0, h1⟩
      have ⟨P, j, p, e⟩ := (isCuspidal_greenCuspidal η).exists_charpoly_eq_pow h0; let V :=
        AEval' g; let A := AdjoinRoot P
      let : Module A V := IsTorsionBy.module (congr($(minpoly.dvd_iff.1 ((isSemisimple_of_mu_ne_zero
        h1).minpoly_squarefree.isRadical _ _ (e ▸ g.minpoly_dvd_charpoly))) ·))
      rcases Fact.mk p, ‹Finite V›, show IsScalarTower k A V from IsTorsionBySet.isScalarTower _
      have r := finrank_mul_finrank k A
      let := (FiniteField.nonempty_algHom_of_finrank_dvd (L := L) ⟨_, (r V).symm⟩).some.toAlgebra
      let t := ofFinrankEq _ _ (mul_left_cancel₀ (by grind [r L, finrank_pos]) (r L ▸ r V))
      exact h (t.symm.restrictScalars k) _ (.trans
        (.symm (LinearMap.ext (t.eq_symm_apply.2 <| t.map_smul (.root P) ·))) (aeval_X _))
      erw [eq_div_iff (by simp), H, Nat.card_units, mulMu_greenCuspidal_lsmul (adjoin.powerBasis
        (integral k y)), minpoly_gen, ← (splits _ y).map_aroots_algebraMap, Multiset.map_map,
        ← sum_mk _ (nodup_roots (.map (separable ..))), sum_mul]
      apply sum_subset_zero_on_sdiff le_top <;> intro z h; simp [(show ρ · z ≠ ρ a y from
        ne_of_apply_ne (aeval · (minpoly k y)) (by simp_all [aeval_algHom_apply,
        minpoly.ne_zero_of_finite]))]
      obtain ⟨c, rfl⟩ := minpoly.exists_algEquiv_of_root (.of_finite ..) (mem_aroots.1 h).2
      exact congr(_ * $(Nat.card_congr (((Equiv.mulLeft a * .mulRight c).trans (generalLinearEquiv
        ..).1.symm).subtypeEquiv fun e ↦ ((a * e).forall_congr
        (by simp [ρ, Algebra.smul_def, mul_eq_trans])).trans LinearMap.ext_iff.symm)))
    star_injective (by simp [*, rankInner_eq_classInner_simClassOf, classInner, finMean,
      Fintype.sum_eq_add_sum_subtype_ne _ (0 : L),
      mul_left_comm, fun e (z : Lˣ) g ↦ (.symm Units.ext_iff : ρ e z = g.1 ↔ z.map (ρ e) = g),
      Ne.symm, mul_div, reindex_equiv unitsEquivNeZero, Fintype.card_subtype, ← sum_boole,
      ← sum_comm_cycle, ← sum_div, mul_sum, field, mul_comm _ (η _)])

instance : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
