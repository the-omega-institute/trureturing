import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Green.LabelIdempotents
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Shintani descent for GL_n(F_q), with the lift named. This file treats only prime
degree, Green's characters with squarefree labels and characters of the determinant, and it gives no
bijection. One character of the semidirect product with the Galois group restricts to the lift and
is the character at the norm off it. Source: T. Shintani, J. Math. Soc. Japan 28 (1976) 396-414; A.
Silberger and E.-W. Zink, J. Algebra 319 (2008) 4147-4176, Thm 5.1; for tensor induction,
Gluck-Isaacs, Illinois J. Math. 27 (1983).

This file: Occurrence of a parabolically induced character detected on the parabolic (Frobenius
reciprocity). Lifted Green character times Steinberg is induced from the base-changed torus.
Shintani lifting in prime degree of Green's characters with squarefree labels. -/

open Algebra Algebra.TensorProduct IntermediateField _root_.Subalgebra _root_.TensorProduct
  ComplexConjugate Fin FiniteField Finset Fint Function Hall IsGalois Module Polynomial Units
  minpoly

variable {k n V ι} [Field k] [Finite k] [Fintype n] [AddCommGroup V] [Module ℂ V]

/-- Let F_a be characters concentrated in the size of block a, and A_gA_x v = A_{gx}v. Then Σ_g
conj((∏F_a)(g))A_g v = 0 on GL_n(k) iff Σ_p conj(∏F_a(p_a))A_{py}v = 0 for all y, p running
over the parabolic subgroup with diagonal blocks p_a. -/
lemma sum_evalGL_prod_eq_zero_iff [LinearOrder ι] (b : n → ι) [Fintype ι] {F : ι → _} (hF : ∀ a,
  Lift ℕ (F a) (F a)) (A : GL n k → End ℂ V) {v} (h : ∀ g x, A g (A x v) = A (g * x) v) : ∑ᶠ g,
  star ((∏ a, (F a).rankPart (Fintype.card {i // b i = a})).evalGL g) • A g v = 0 ↔ ∀ y, ∑ᶠ p, star
  (∏ a, (F a).evalGL (blockHom b a p)) • A (p * y) v = 0 := by
  let L := Finsupp.lift _ ℂ _ (A · v) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).1
  let ρ := (Representation.leftRegular ..).quotient L.ker
    (A · |> L.ker_le_ker_comp |>.trans_eq (congrArg _ (by aesop) : _ = (L ∘ₗ _).ker))
  have := (isChar_of_mem_virtualChars (prod_mem fun a _ ↦ comp_mem_virtualChars (hF
    a).evalGL_mem_virtualChars (blockHom ..))).groupAlgElem_eq_zero_iff (ρ := ρ.domRestrict _).trans
    (classInner_evalGL_prod b F (mem_univ <| b ·) _ ρ.char_conj ▸ (isChar_of_mem_virtualChars
    (Lift.evalGL_mem_virtualChars (prod_hom_rel .one fun _ _ _ ↦
    .mul (.rankPart_of_descendsTo (hF ..))))).groupAlgElem_eq_zero_iff.symm)
  simp_all +zetaDelta [Submodule.linearMap_qext_iff, MonoidAlgebra.lhom_ext'_iff, Subtype.ext_iff,
    LinearMap.ext_ring_iff, ← L.quotKerEquivRange.map_eq_zero_iff, asAlgebraHom_eq_sum]
  use fun e y ↦ ((MulAut.conj y).sum_comp _).rec (by simpa [h, evalGL_conj] using congr(A y $e)),
    (by simpa using · 1)

variable {k : Type*} {k'} {n : Type*} {K r} [Field k] [Field k'] [Algebra k k'] [Finite k]
  [Finite k'] [Fintype n] [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] (T)
  [IsFaithfulMulChar K T] (σ : Gal(k'/k)) {L} [Field L] [Algebra k L] {P : k[X]} {x : K}

omit [Finite k] in
@[simp] lemma evalGL_detChar χ (g : GL n k) : (detChar χ).evalGL g = χ g.1.det := by
  simp [Hall.evalGL, detChar, Matrix.det_eq_sign_charpoly_coeff]

attribute [local simp ←] prod_pow_eq_pow_sum card_eq_pow_finrank finMean_const_mul
  trace_eq_sum_automorphisms in
attribute [local simp] AlgEquiv.eq_symm_apply exists_fin_succ forall_fin_succ
  coe_frobeniusAlgEquivOfAlgebraic coe_frobeniusAlgHom pow_card_pow rankInner mulMu skew funext_iff
  pow_add pow_mul in
variable (k') in
/-- Let P over k be an irreducible label of degree r = [L:k] with root x in K. Some character of
GL_r(k') ⋊ Gal(k'/k) descends (`DescendsTo`) over k to C_θ·μ, θ = θ_x taken for |k|^r, and over
k' to (−1)^r Ξ_P·μ; here μ is the inverse of 𝟙, products pointwise. -/
lemma exists_isChar_descendsTo_labelChar [Finite L] (hP : Irreducible P) (hL : IsLabel r P) (hx :
  aeval x P = 0) (hn : finrank k L = r) : ∃ Φ : GalSemidirect k k' (Fin r) → ℂ, IsChar Φ ∧
  DescendsTo Φ (greenCuspidal k (thetaChar T (.card k ^ r) x)).mulMu ∧ DescendsTo
  Φ ((-1 : ℂ) ^ r • (labelChar T (P.map (algebraMap k k'))).mulMu) := by
  obtain ⟨rfl, i : IsIntegral k' x, Q, _, X, q⟩ := hL.2.2.1, .tower_top ⟨P, hL.1, hx⟩,
    @natCard_eq_pow_finrank k k', @finite_of_finite k' (k' ⊗[k] L),
    root_pow_card_pow_pred_eq_one hP hL.2.2.2 hx
  have D {S} {z : K} i s h a := (root_pow_card_pow_eq_self_iff (P := S) i s).symm.trans (Q ▸
    Nat.pow_mul _ _ a ▸ root_pow_card_pow_eq_self_iff hP (x := z) h)
  have G := adjoin.finrank i ▸ D (irreducible i) (by simp) hx
  obtain ⟨_, r, hr⟩ := finite_iff_finite.1 (adjoin.finiteDimensional i), (G _).1 dvd_rfl
  set N := k'⟮x⟯
  have ⟨g, a, ⟨c, d⟩, H⟩ := (hL.map k').induction_irreducible_mul K (p := fun n c ↦ c ∣ P.map _ →
    ∃ b, ∃ a : Fin b → ℕ,
    ((∀ z, aeval z c = 0 → ∃ j, ∃ v < finrank k' N, a j < P.natDegree ∧ z ^ .card k' ^ v = x ^ .card
    k ^ a j) ∧ b * finrank k' N = n) ∧ ∀ B, (-1) ^ n * rankInner n (labelChar T c) (mulMu B) =
    finMean fun u : _ → Nˣ ↦ (∏ j, conj (thetaChar T (.card N) (x ^ .card k ^ a j) (u j))) * B
    (simClassOf (LinearMap.mulLeft k' (u · |>.1)))) (by simp [simClassOf_eq_of_dim_zero, finMean,
    univ_eq_empty]) (fun S _ _ z m i o s ih h ↦ ?_) dvd_rfl
  obtain ⟨ψ⟩ := nonempty_algHom_of_finrank_dvd ⟨r, hn ▸ finrank_mul_finrank k k' N ▸ hr⟩
  let F := frobeniusAlgEquivOfAlgebraic k k'; let n (i : _ × Fin r) := a i.1 + P.natDegree * i.2
  let Φ := frobeniusAlgEquivOfAlgebraic k N
  let χ a := AlgHom.liftEquiv k k' L N (.comp ↑(Φ ^ a)⁻¹ ψ)
  have I i t : χ 0 (Algebra.TensorProduct.map (F ^ n i).toAlgHom (.id ..) t) = (Φ ^ n i) (χ (a i.1)
    t) := by induction t <;> simp [*]; simp +zetaDelta [smul_def', mul_pow, ← map_pow, ← hn]
  have b := Surjective.bijective_of_nat_card_le (f := (F ^ n ·))
    ((bijective_frobeniusAlgEquivOfAlgebraic_pow ..).2.forall.2 fun u ↦ (c (x ^ .card k ^ u.1) (by
    simpa [hx] using P.aeval_algHom_apply (frobeniusAlgHom .. ^ u.1) x)).elim fun j ⟨v, l, p, t⟩ ↦
    ⟨(j, ⟨_, Nat.div_lt_of_lt_mul (by nlinarith [u.2])⟩), .trans congr(F ^ $(Nat.mod_eq_of_modEq (by
    simpa only [root_pow_card_pow_eq_iff_modEq hP hx, Q, ← pow_mul, ← pow_add] using
      t) p ▸ Nat.mod_add_div ..))
    (by ext; simp [F])⟩) (by simp [↓card_aut_eq_finrank]; nlinarith [hP.natDegree_pos])
  let e := equivFinsuppOfBasisLeft (N := L) (finBasis k k').traceDual
  let π := AlgHom.pi (χ <| a ·)
  let E := π.toLinearMap.linearEquivOfInjective (fun t u h ↦ e.injective (by
    ext; exact ψ.injective (by simp_all [π, fun t i ↦ (by induction t <;> simp [*, e, add_mul,
      χ, ← sum_smul, -map_mul] : ψ (e t i) = ∑ τ : Gal(k'/k), χ 0 (map τ.toAlgHom
      (.id k L) (t * finBasis k k' i ⊗ₜ 1))), ← b.sum_comp]))) (by simp [*])
  peel 3 exists_torus_induced_descendsTo _ _ _ hn (N.val.comp (χ 0))
  refine this _ fun B ↦ .trans (by simp; ac_rfl) ((H B).trans (finMean_equiv ((mapEquiv ⟨E.toEquiv,
    map_mul π⟩).trans .piUnits) fun t ↦
    .symm congr($(?_) * B $(simClassOf_eq_of_equiv E (map_mul π _)))))
  simp_rw [← b.prod_comp, map_prod, AlgHom.comp_apply, I, Fintype.prod_prod_type]; congr!
  erw [thetaChar_eq_apply_norm_pow T q X Finite.one_lt_card (by rw [← pow_mul, ← hr]; simp) rfl
    (algebraMap_pow_card_pred_eq_one _)]
  simp [n, Φ, prod_range, prod_pow]; rfl
  have R := by simpa [s] using map_dvd (aeval z) h
  obtain ⟨d, ⟨e, w, rfl⟩, b, y, ⟨f, rfl⟩, H⟩ := by simpa [← G, Nat.dvd_right_iff_eq] using D i s R,
    exists_pow_card_pow_eq_of_root hP hx R, ih (.trans (by simp) h)
  use b + 1, cons e y, by simp [-Nat.card_eq_fintype_card]; grind [exists_pow_card_pow_eq_of_root],
    fun B ↦ ?_
  rw [pow_add, map_mul, labelChar_eq_greenTau T i m, rankInner_mul_eq_rankInner_skew
    greenTau_eq_zero_of_dim_ne, d, (funext fun a ↦ .trans ?_ congr((-1) ^
    finrank k' N * $(rankInner_greenCuspidal_mulMu _ N.val (B <| simClassOf <| ·.out.2.prodMap
    a.out.2)) * _) : skew _ _ _ = _), mul_assoc, H, finMean_equiv (consEquiv _) (by tauto)]
  simp [↓finMean_prod, finMean, prod_univ_succ, mul_sum, ↓sum_div, sum_comm (α := _ˣ)]; congr! 2
  simpa [field, ← pow_mul] using .inl (congrArg B ((exists_equiv_simClassOf_out _).rec fun f _ ↦
    (exists_equiv_simClassOf_out _).rec
    fun e _ ↦ simClassOf_eq_of_equiv (f.prodCongr e ≪≫ₗ consLinearEquiv _ fun _ ↦ _)))
  simp [mul_comm (finMean _), greenTau_eq i o s, d]; ac_rfl

omit [IsScalarTower k k' K] in
/-- Galois equivariance of Green's characters: for σ in Gal(k'/k), a label c over k' and g in
GL_n(k'), Ξ_c(σ(g)) = Ξ_{σ(c)}(g). -/
lemma labelChar_gal_map {c : k'[X]} (hc : IsLabel r c) (g : GL n k') : (labelChar T c).evalGL (g.map
  σ) = (labelChar T (c.map σ)).evalGL g := let τ := σ.toRingEquiv; let := τ.toRingHom.toAlgebra
    have A := aroots_map_frobenius_pow (K :=
      K) (algebraMap ..) (exists_forall_apply_eq_pow _ _ _ σ).choose_spec
    have ⟨_, _, a, b⟩ := ((hc.induction_irreducible_mul K (by simp) fun R _ _ x m p z e h ↦ by
    have i := R.mapEquiv_apply τ ▸ p.map _
    simpa only [map_mul, mapEquiv_apply, labelChar_eq_greenTau, m.map, greenTau_eq p z e, *,
      natDegree_map, greenTau_eq i (by simpa) (mem_aroots.1 (A _ ▸ Multiset.mem_map.2 ⟨x, by aesop,
      rfl⟩)).2, rankPart_greenCuspidal_pow p z e] using .mul (.rankPart_mulMu_mul_constOne fun _ ↦
      exists_descendsTo_of_gal_trivial (AlgEquiv.ext <| (reindex_equiv σ).1.2 ·.4)
      ((irreducible_criteria_of_isClassFunction _ evalGL_conj).2.1 (by simp)) (by simp [Hall.evalGL,
      Matrix.charpoly_map, A])) h :
    Lift ℂ (labelChar T (c.mapEquiv τ)) (labelChar T c)).exists_descendsTo n)
    DescendsTo.iff_comp_inl_eq_evalGL.1 b ▸ a 1 (σ.range_eq_univ.trans (by bound)) _ g rfl
      (by aesop)

/-- Let T be injective and χ, χ' multiplicative characters of k, k' with x_{χ'} = x_χ
(`charName`). Then χ∘det and χ'∘det form a lift by true characters, in every rank.

Known result: Shintani descent for GL_n(F_q), with the lift named. -/
lemma lift_detChar {χ χ'} (h : (charName T χ').1 = algebraMap k k' (charName T χ).1) : Lift ℕ
  (detChar χ) (detChar χ') := fun _ ↦ have ⟨_, a, e, f⟩ := exists_norm_char_semidirect _ ((thetaChar
    T (.card k) (algebraMap k K (charName T χ))).comp (.comp (algebraMap k' K) Matrix.detMonoidHom))
  ⟨_, a.mem_virtualChars, fun σ s ↦ by simp +contextual [DescendsOnCoset, f σ s _, RingHom.map_det,
    ← thetaChar_charName T, IsScalarTower.algebraMap_apply k k' K], .iff_comp_inl_eq_evalGL.2 (by
    ext g; simpa [← thetaChar_charName T, ↓← map_pow, AlgEquiv.map_det, norm_eq_prod_automorphisms,
      ← IsScalarTower.algebraMap_apply, ↓← algebraMap_norm_eq_pow_sum, *] using!
      (thetaChar_eq_apply_norm_pow T Finite.one_lt_card
      (algebraMap_pow_card_pred_eq_one (charName T χ)) Finite.one_lt_card
      natCard_eq_pow_finrank (pow_one _) (algebraMap_pow_card_pred_eq_one g.det)).symm)⟩

omit [Finite k] in
/-- For an extension L/k of fields of prime degree, the elements of L fixed by σ ∈ Gal(L/k) are
exactly those of k if and only if σ ≠ 1. -/
lemma fixed_eq_range_iff_ne_one (hp : (finrank k L).Prime) {σ : Gal(L/k)} : HasFixedField k σ ↔ σ ≠
  1 := by simpa [iff_comm, SetLike.ext_iff, DFunLike.ext_iff, Set.ext_iff, lt_top_iff_ne_top] using!
  (Subalgebra.isSimpleOrder_of_finrank_prime k _ hp).lt_top_iff_eq_bot (a := σ.toAlgHom.equalizer 1)

lemma DescendsTo.card_mul_classInner (hp : (finrank k k').Prime) {F G : Hall k} {Φ Ψ : GalSemidirect
  k k' n → ℂ} (v : IsClassFunction Φ) (w : IsClassFunction Ψ) (l : DescendsTo Φ F) (m :
  DescendsTo Ψ G) : let N : ℂ := Nat.card Gal(k'/k); N * _root_.classInner Φ Ψ = _root_.classInner
    (Φ ∘ SemidirectProduct.inl) (Ψ ∘ SemidirectProduct.inl) + (N - 1) * rankInner (.card n)
    F G := have := (univ.erase 1).sum_congr rfl fun σ e ↦
    (fun s ↦ (exists_isRootChoice_GL s).choose_spec.1.classInner_eq_fibre_mean.2 (l _ s) (m σ s)
    (by tauto)) (by grind [fixed_eq_range_iff_ne_one])
  by simp_all [↓classInner_evalGL, _root_.classInner,
    Subgroup.index_ker, ↓SemidirectProduct.rightHom_surjective, Fintype.card_pos, ← mul_sum,
    ← finMean_sum, sub_eq_iff_eq_add', SemidirectProduct.rightHom_eq_right.trans rfl, field]

/-- Shintani lifting: let k'/k be an extension of finite fields of prime degree, T injective and
c a label over k. Then Ξ_c lifts by characters (`Lift` ℕ) to Ξ_c formed over k'.

Known result: Shintani descent for GL_n(F_q), with the lift named. -/
lemma shintani_lift_labelChar (hp : (finrank k k').Prime) T [IsFaithfulMulChar K T] {c} (hc :
  IsLabel r c) : Lift ℕ (labelChar T c) (labelChar T (c.map (algebraMap k k'))) :=
  hc.induction_irreducible_mul K (by simp) fun P _ _ x hm hP h0 hx ↦ by
  simp; apply Lift.mul
  obtain ⟨h1 | h1, _, hL : IsLabel ..⟩ := em' (P.IsRoot 1), NeZero.of_pos hP.natDegree_pos,
    ⟨hm, hP.squarefree, rfl, h0⟩
  obtain ⟨hθ, u, M, ⟨B, b⟩, J, v, j, i⟩ := labelChar_eq_greenTau T hP hm ▸ greenTau_eq hP h0 hx,
    rankInner_labelChar T hL _ hL, hL.map k', exists_lift_brauerLift k k' (thetaChar T ..),
    exists_isChar_descendsTo_labelChar k' T hP hL hx (finrank_extension ..)
  obtain ⟨⟨β, b, d, _⟩, Φ, l, o, _⟩ := b _, hθ ▸ b.rankPart_mulMu_mul_constOne _
  obtain ⟨⟨N, t⟩, _⟩ := v.exists_classInner_eq b, j.card_mul_classInner hp v.isClassFunction
    (isClassFunction_of_mem_virtualChars b) d, rankInner_labelChar_mul_constOne T M (by
    simpa [aeval_def]), rankInner_labelChar_mul_constOne T hL h1
  refine rankPart_labelChar T M ▸ rankPart_labelChar T hL ▸ .rankPart_of_descendsTo ⟨_,
    ((IsLabel.isIrrChar_labelChar T (by simpa)).extend_semidirect (fun σ g
    ↦ by erw [labelChar_gal_map T σ M]; congr with; simp) l
    (by grind [isClassFunction_of_mem_virtualChars l, Nat.card_fin,
    o.card_mul_classInner hp]) (N - 1) ?_).1.mem_virtualChars, by simpa +contextual [DescendsTo,
    DescendsOnCoset, fixed_eq_range_iff_ne_one, *] using o, by simp⟩
  simp_all [-brauerLift, classInner_evalGL, greenCuspidal, comp_def, rankInner.eq_1, mul_assoc,
    mul_left_comm]
  grind [neg_one_pow_eq_or]
  simpa [← labelChar_X_sub_C T, eq_of_irreducible_of_monic hP h1 hm] using
    Lift.rankPart_of_descendsTo (@lift_detChar k k' K _ _ _ _ _ _ _ _ _ T _ 1 1 (by simp) 1)
