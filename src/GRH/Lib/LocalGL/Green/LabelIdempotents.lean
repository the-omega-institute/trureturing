import GRH.Lib.LocalGL.Shintani.LabelCharacters
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Twisting a Green character by a determinant character scales the label's roots. Label
idempotents are orthogonal projections; they kill twisted sums over hyperplane-fixing elements. -/

open Nat Finite Function Hall Matrix Polynomial

/-- For nonzero a in k, the multiplicative bijection of k[X] to itself scaling the roots of a
polynomial by a, with inverse scaling by a⁻¹. -/
noncomputable def scaleRootsEquiv {k} [Field k] (a : kˣ) : k[X] ≃* k[X] := by
  use! (·.scaleRoots a), (·.scaleRoots a⁻¹) <;>
    simp_intro _ [← scaleRoots_mul, mul_scaleRoots_of_noZeroDivisors]

variable {k K : Type _} {r : ℕ} [Field k] [Finite k] [Field K] {c : k[X]}

omit [Finite k] in
lemma IsLabel.scaleRoots (a : kˣ) (hc : IsLabel r c) :
    IsLabel r (c.scaleRoots a) := by simp_all [IsLabel, Monic]; use (reindex_equiv _).1.2 fun x h ↦
    (hc.2.1 x ((map_dvd_iff (scaleRootsEquiv a)).1 (by simpa))).map _

/-- Let q = |k| ≡ 1 mod 9, r = 3^{e+1}, ξ a primitive (q^r − 1)-th root of unity and l prime.
Then ξ^{l^a} has r distinct conjugates: its q^i-th powers, 0 ≤ i < r, are distinct. -/
lemma frobenius_conj_pow_injOn {ξ : K} {e l} a (h3 : 9 ∣ .card k - 1) (h :
  IsPrimitiveRoot ξ (.card k ^ 3 ^ (e +
  1) - 1)) (hl : Nat.Prime l) : (Set.Iio (3 ^ (e + 1))).InjOn ((ξ ^ l ^ a) ^ .card k ^ ·) := by
  obtain ⟨o, u, s, hy⟩ := @one_lt_card k _ _, h.1, h3.trans (sub_one_dvd_pow_sub_one _ (3 ^ e))
  convert @minimalPeriod_eq_prime_pow _ (· ^ Nat.card k) (ξ ^ l ^ a) 3 e _ ?_ ?_ ▸
    iterate_injOn_Iio_minimalPeriod <;> simp_all [IsPeriodicPt, IsFixedPt, succ_le_iff,
    pow_right_comm ξ (l ^ a), pow_succ, mul_pow, tsub_eq_iff_eq_add_of_le]
  exact ((dvd_prime_pow hl).1 ∘ (h.pow (b := s * (81 * s + 27) + 3) (by simpa)
    (by rw [pow_mul, hy]; lia)).2 _).mt (by rintro ⟨_ | _ | _, _, D⟩ <;>
    grind [one_lt_pow, dvd_prime, prime_three.dvd_of_dvd_pow (.trans (by lia) D.dvd)])

/-- For T injective, a label c (of any degree r, not tied to n) and a multiplicative character χ of
k, Ξ_c(g)·χ(det g) = Ξ_{c'}(g) on GL_n(k), where the roots of c' are x_χ times those of c. -/
lemma labelChar_mul_det [Algebra k K] {n} [Fintype n] {T} [IsFaithfulMulChar K T] (hc :
  IsLabel r c) χ (g : GL n k) :
  (labelChar T c).evalGL g * χ g.1.det = (labelChar T (c.scaleRoots (charName T χ))).evalGL g := by
  erw [← thetaChar_charName T, RingHom.map_det, det_eq_prod_roots_charpoly, charpoly_map,
    ← charpoly_toLin', ← charpoly_simClassOf]
  exact ((hc.induction_irreducible_mul K (by simp_all [simClassOf_eq_of_dim_zero]) fun P _ _ _ _ i o
    h _ ↦ congrFun (Hall.ext fun _ _ ↦ by
    have := i.map (scaleRootsEquiv (charName T χ))
    simp_all [map_mul, scaleRootsEquiv, Monic.def, mul_simClassOf, Finset.sum_mul]; congr with W
    simp [*, greenTau_eq _ _ (scaleRoots_aeval_eq_zero h), greenTau_eq i _ h,
      aroots_mul, ↓mul_left_comm, ← charpoly_endOnSub_mul_endOnQuot _ W,
      (LinearMap.charpoly_monic _).ne_zero, mul_comm, mul_assoc]
    congr!; rw [mul_comm (greenCuspidal ..)]
    exact greenCuspidal_congr _ _ fun z ↦ by by_cases z = 0 <;> simp_all [thetaChar_mul,
      root_pow_card_pow_pred_eq_one i o h, ← Finset.range_val, MulChar.map_zero,
      thetaChar_eq_apply_norm_pow T one_lt_card _ _ rfl (pow_one _), mul_comm,
      Finset.prod_pow_eq_pow_sum, root_pow_card_pow_eq_self_iff (irreducible_X_sub_C _)]) : ∀ x,
    labelChar T (scaleRootsEquiv _ c) x =
    labelChar T c x * thetaChar T _ _ (x.charpoly.aroots K).prod) _).symm

open Finset LinearMap Fint Submodule MonoidAlgebra Representation
variable {n ι : Type _} [Fintype n] [Fintype ι] {k : Type _} [Field k] [Finite k]

attribute [local simp] labelIdem coeff_mul_apply_right Finsupp.sum_fintype finMean_prod
  Units.smul_def evalGL_conj reflectionSum asAlgebraHom_eq_sum LinearMap.ext_ring_iff character skew
  detChar Units.ext_iff

lemma labelIdem_orthogonal : OrthogonalIdempotents (labelIdem (k := k) n) :=
  .iff_mul_eq.2 fun c d ↦ by
  ext x
  have (h : IsLabel _ d) := (h.isIrrChar_labelChar (faithfulChar k)).2.2
    (labelChar (faithfulChar k) c).evalGL evalGL_conj x⁻¹
  simp only [labelIdem]; split_ifs <;> simp_all [Finsupp.sum_fintype, _root_.finMean,
    classInner_evalGL, rankInner_labelChar, eq_comm, mul_mul_mul_comm _ _ (_ / _), ← mul_sum,
    ← (IsLabel.isIrrChar_labelChar _ _).1.apply_inv] <;> grind

/-- For any polynomial c, if the element x_χ naming χ is not a root of c, and l ≠ 0, then e_c kills
the sum of χ(det h)⁻¹ h over the invertible h = 1 + u lᵀ. -/
lemma reflectionSum_mul_labelIdem {c : Polynomial k} {χ} (hχ : ¬c.IsRoot
  (charName (faithfulChar k) χ)) {l} (hl : l ≠ 0) : reflectionSum χ l * labelIdem n c = 0 := by
  rw [IsClassFunction.commute (by aesop)]; simp; intro h
  let N : Submonoid (GL n k) := ⟨⟨{g | ∃ u, g.1 = 1 + vecMulVec u l}, by
    simp_all [mul_add, mul_vecMulVec, add_assoc, ← add_vecMulVec]; lia⟩, by simp⟩
  let := @LeftCancelMonoid.groupOfFinite N {}
  let e := (dotProductEquiv k n l).equivProdOfSurjectiveOfIsCompl (mkQ _) (by simpa [range_eq_top,
    surjective_iff_ne_zero]) (by simp) (by simpa using (ker _).exists_isCompl.choose_spec)
  let E := e ≪≫ₗ .symm (prodEquiv k ≪≫ₗ ringLmapEquivSelf k ..)
  have hd u : (1 + vecMulVec u l).det = (1 + (E u).1).det ∧ simClassOf
    (.id + (vecMulVec u l).toLin') = simClassOf (blockTriangularEnd 1 (1 + (E u).1) (E u).2) :=
    ⟨by simp [E, e, vecMulVec_eq Unit, det_one_add_mul_comm],
    simClassOf_eq_of_equiv e (by simp [E, e, vecMulVec_mulVec, add_comm])⟩
  have := ((h.isIrrChar_labelChar (faithfulChar k)).1.groupAlgElem_eq_zero (V := ℂ)
    N.subtype · (ρ := .comp .smulOneHom ⟨⟨(χ⁻¹ ·.1.det), by simp⟩, by simp⟩) ?_)
  ext; simp_all [sum_ite, ← sum_subtype_eq_sum_filter, ← (h.isIrrChar_labelChar _).1.apply_inv,
    mul_assoc, ← mul_sum]
  convert! Or.inr (this _)
  simpa [classInner, mul_comm (labelChar _ c _), hd, ← χ.star_apply', Hall.evalGL,
    ← blockAverage_simClassOf, ↓rankInner_eq_classInner_simClassOf,
    ↓LinearMap.det_eq_sign_charpoly_coeff, finMean_equiv (.ofBijective (uncurry fun g x ↦ (⟨.mk'' _
    ((hd _).1 ▸ .map _ (by simp)), E.symm (Units.val g - 1, x), rfl⟩ : N)) ⟨by simp_all [Injective,
    ↓← sub_eq_zero (a := vecMulVec _ l), ← sub_vecMulVec], fun ⟨g, u, _⟩ ↦ ⟨(g.det • 1, (E u).2), by
    simp_all [E]⟩⟩) (by tauto)] using
    congrFun (Module.finrank_self k ▸ skew_detChar_labelChar_eq_zero _ h hχ :) _

variable {k : ι → _} [∀ w, Field (k w)] [∀ w, Finite (k w)] (c : ∀ w, Polynomial (k w))

variable (n) in
/-- For a tuple (c_w) of polynomials over the fields k_w, the tensor product of the label
idempotents e_{c_w} in the group algebra of ∏ GL_n(k_w). -/
noncomputable def tupleIdem := piTensorElem (labelIdem n <| c ·)

/-- For every tuple (c_w) of polynomials, the element ⊗_w e_{c_w} is a central idempotent of the
group algebra of ∏_w GL_n(k_w). -/
lemma isCentralProj_tupleIdem : IsCentralProj (tupleIdem n c) :=
  .piTensorElem (⟨labelIdem_orthogonal.1 <| c ·, by aesop⟩)

/-- The elements ⊗_w e_{c_w} of the group algebra of ∏_w GL_n(k_w), indexed by all tuples (c_w)
of polynomials, are idempotents, and those of distinct tuples have product zero. -/
lemma tupleIdem_orthogonal : OrthogonalIdempotents (tupleIdem (k := k) n) :=
  ⟨(isCentralProj_tupleIdem · |>.1),
  fun _ _ e ↦ piTensorElem_mul_eq_zero _ (labelIdem_orthogonal.2 (ne_iff.1 e).choose_spec)⟩

/-- For every finite set s of tuples (c_w) of polynomials over the finite fields k_w, the sum
over s of the idempotents ⨂_w e_{c_w} is a central idempotent of the complex group algebra
of ∏_w GL_n(k_w). -/
lemma isCentralProj_sum_tupleIdem {s} : IsCentralProj (∑ c ∈ s, tupleIdem (k := k) n c) :=
  ⟨tupleIdem_orthogonal.isIdempotentElem_sum, by simp [(isCentralProj_tupleIdem _).2]⟩
