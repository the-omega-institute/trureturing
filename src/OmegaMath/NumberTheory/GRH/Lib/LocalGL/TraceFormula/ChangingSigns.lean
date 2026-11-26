import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.BaseChange.BaseChangePlaces
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Global.CMNorms
import OmegaMath.NumberTheory.GRH.Lib.Shimura.IntegralModel.NeatLevel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Comparison of simple trace formulas for unitary groups that differ only at real places
(known result; see Lib.LocalGL.TraceFormula.TraceComparison).

Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number (known
result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Finitely many double cosets of frames of given signature (finite class number). Changing
real signs of elliptic classes by a global element locally a norm. -/

open Finset Polynomial RingHom AdjoinRoot Algebra ComplexOrder Equiv IsAlgClosed Lagrange Matrix
  MulAction NumberField

/-- Let V be an open subgroup of GL_n of the finite adeles of E, and K = `GU` ∩ V.
Only finitely many double cosets GL_n(E) x K contain an x with `IsSignedFrame` x ℓ for some
complex matrix ℓ. -/
lemma finite_isSignedFrame_classes {E n} [Field E] [CMBase E] [Fintype n] {V} (hV : V.IsOpen) :
    (DoubleCoset.mk toFinGL.range (GU E n ⊓ V) '' {x | ∃ ℓ, IsSignedFrame x ℓ}).Finite := by
  have U B h : ∃ a : GL n ℂ, (star a * B * a).1 ∈ unitary _ :=
    ⟨cfcUnits (√|·⁻¹|) B (by grind [Units.zero_notMem_spectrum]), by simpa [star_trivial, cfc_mul,
      cfc_id', ← cfc_star, finite_real_spectrum.continuousOn, h] using ((cfc_unitary_iff
      (fun x ↦ √|x⁻¹| * x * √|x⁻¹|) B.1).2 (by grind [star_trivial, Units.zero_notMem_spectrum]))⟩
  choose! g G using (@_root_.id <| ∃ x, IsFrameFor · x ∧ @QuotientGroup.mk _ _ V x = ·)
  refine (exists_finite_gram (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (isCompact_closedBall_prod_integral.matrix.prod
    (isCompact_closedBall_prod_integral.matrix.image_auto .op)))).elim fun _ ⟨_, hF, hC, H⟩ ↦
    (hF.image2 (⟦g ·.2 ·⟧) (finite_quotient_image_of_isCompact hV (hC.image_auto (·.1)))).subset
    fun _ ⟨x, ⟨_, J, h@⟨ν, _⟩, p⟩,
    e⟩ ↦ e ▸ (((exists_ne v₀).imp fun v ↦ (by simpa [·] using p v)).elim fun v p ↦ ?_)
  obtain ⟨J, rfl⟩ := isUnit_of_mapMatrix _ p.isUnit
  choose a u using by simpa using fun w ↦ U (.map (Φ w) J) h.isHermitian_map
  choose Z d o hy hY using H J (mkAdelicGL (a, x)) (Set.mem_of_eq_of_mem (Units.ext (by
    apply matrix_ext_𝔸 <;> push_cast [Matrix.map_mul] <;> tauto)) (y := mkAdelicGL ((Unitary.toUnits
    ⟨_, u ·⟩), ν.map ((finAdeleIncl ℚ E).domRestrict _).1 • 1)) (by simp [Set.matrix, ← map_inv,
             entry_norm_bound_of_unitary, u, ite_mem, pi_norm_le_iff_of_nonneg, Units.smul_def]))
  obtain rfl := _root_.funext fun i ↦ by_contra (((Z.map _).isUnit.posDef_star_left_conjugate_iff.2
    p).diag_pos.ne' <| by simpa [mul_apply] using congr(Φ v $(o ⟨i, ·⟩ ⟨i, ‹_›⟩)))
  set Y := (star Z * J)⁻¹
  exact (G _ _ ⟨_, (IsFrameFor.conj_iff (toFinGL Y⁻¹ * _) Y).2 (by simpa), rfl⟩).elim fun b e ↦ ⟨_,
    hY, _, ⟨_, ⟨_, hy, rfl⟩, .trans (by simp; tauto) e⟩, (DoubleCoset.eq ..).2 ⟨_, ⟨Y, rfl⟩, _,
    ⟨⟨1, rfl, b.mul_iff.1 (by simpa [IsFrameFor.conj_iff])⟩, QuotientGroup.eq.1 e⟩, by simp⟩⟩

variable {E n Z : Type} [Field E] [Fintype n] {y : GL n E}

/-- For y in GL_n(E) with separable characteristic polynomial P and an embedding t of E into ℂ,
the numbering `numberedRoots` lists the complex roots of t(P), each once. -/
lemma roots_eq_map_numberedRoots (h : y.1.charpoly.Separable) t : (y.1.charpoly.map t).roots =
  (@univ n).1.map (numberedRoots
  t y.1.charpoly) := Classical.epsilon_spec ((Function.Embedding.exists_of_card_eq_finset (s :=
  ⟨_, nodup_roots h.map⟩) (by simp [card_roots_eq_natDegree])).imp fun _ ↦ val_inj.2 ∘ .symm)

attribute [local simp] charpoly_map map_smul' eval_map map_aeval_matrix mul_assoc

lemma isRoot_numberedRoots (h : y.1.charpoly.Separable) t (i : n) : (y.map t).1.charpoly.IsRoot
  (numberedRoots t y.1.charpoly i) := isRoot_of_mem_roots (by simp [roots_eq_map_numberedRoots h])

variable [CMType E]

lemma eval_interpolate_univ_node (r : n ↪ ℂ) f i :
    (interpolate univ r f).eval (r i) = f i := eval_interpolate_at_node _ r.2.injOn (by simp)

/-- y has irreducible characteristic polynomial, ν ≠ 0, yᴴβy = νβ, and under each embedding of
the CM type all complex roots r of that polynomial satisfy r r̄ = ν. -/
def IsEllipticSimilitude (ν : ℚ) (y : GL n E) β := Irreducible y.1.charpoly ∧ ν ≠ 0 ∧ y.1ᴴ * β * y =
  (ν : E) • β ∧ ∀ᵉ (w) (r ∈ (y.1.charpoly.map (Φ w)).roots), r * star r = ν

/-- (x, y) has type ε: y has irreducible characteristic polynomial with complex roots satisfying
r r̄ = ν, and some β over E has yᴴβy = νβ, xᴴβx ∈ F and βp_w(y) positive definite at each
infinite w, p_w interpolating the signs ε_w at the numbered roots. -/
def HasSignType (ε : _ → n → ℤˣ) ν (y : GL n E) (F : Set _) (x : GL n (𝔸f E)) := ∃ β,
  IsEllipticSimilitude ν y β ∧ xᴴ * β.map (↑) * x.1 ∈ F ∧ ∀ w, (β.map (Φ w) *
  (interpolate univ (numberedRoots (Φ w) y.1.charpoly) (ε w ·)).aeval (y.1.map (Φ w))).PosDef

/-- Under `IsEllipticSimilitude`, at w, with roots x_i in any order: kᴴβk = diag d for some k; βq(y)
is positive definite iff all d_i q(x_i) > 0; signs t with d_i t_i > 0 give k' with k'ᴴβk' =
diag t, k'⁻¹yk' = diag x. -/
lemma exists_eigenbasis_diag_form {ν β} (h : IsEllipticSimilitude ν y β) w (σ :
  Perm n) : let x i := numberedRoots (Φ w) y.1.charpoly (σ i)
  let g := y.1.map (Φ w); let B := β.map (Φ w); ∃ (k : GL n ℂ) (d : n → ℂ), k.1ᴴ * B * k
  = diagonal d ∧ (∀ q, (B * aeval g q).PosDef ↔ ∀ i, 0 < d i * q.eval (x i)) ∧ ∀ t : n → ℤˣ, (∀ i,
      0 < d i * t i) → ∃ k : GL n ℂ, k.1ᴴ * B * k = signMatrix t ∧ k⁻¹.1 * g * k = diagonal x := by
  intro x g B
  have ⟨k, (a : _ * diagonalAlgHom ℂ x = g * _)⟩ := isConj_diagonal_of_isRoot_charpoly (x :=
    σ.toEmbedding.trans _) (isRoot_numberedRoots h.1.separable _ <| σ ·)
  refine ⟨k, .imp (fun d b ↦ ⟨b, fun q ↦ ?_, fun t ht ↦ ?_⟩) ⟨_, .symm (IsDiag.diagonal_diag fun i
    j ↦ by grind [map_eq_zero, σ.injective, by simpa [roots_eq_map_numberedRoots h.1.separable]
    using h.2, by simpa [↓gram_mul, B, g, ← map_conjTranspose_mul_mul, h.2, -mul_assoc]
    using congr(($aᴴ * B * $a) i j)])⟩⟩
  erw [← k.isUnit.posDef_star_left_conjugate_iff, ← mul_assoc, mul_assoc, ← aeval_semiconj a,
    aeval_algHom_apply, ← mul_assoc, b]; simp
  choose c hc using (CStarAlgebra.nonneg_iff_eq_star_mul_self.1 <| ht · |>.le)
  use k * diagGL fun i ↦ .mk0 (t i / c i) ?_, gram_mul_of_gram_eq b ?_ <;>
    simp_all [signMatrix, ← mul_assoc g, ← a, ← map_inv] <;> grind

attribute [local grind] IsEllipticSimilitude Multiset.mem_map HasSignType roots_map_conjugate
  star_star

/-- Change of signs. If each η_μ has product 1, some permutation of the GL_n(E)-orbits of
triples has the form (q, y, μ) ↦ (Uq, y, μ), where U ∈ GL_n(𝔸_f) depends on y, μ only,
commutes with the centraliser of y in GL_n(E), and (x, y) has type εη_μ iff (Ux, y) has type
ε. -/
lemma exists_hasSignType_mul_iff (η : Z → InfinitePlace E → n → _) (hη : ∀ μ, ∏ w, ∏ i,
  η μ w i = 1) K : ∃ e : Perm (orbitRel.Quotient (GL n E) (MarkedTriple K Z)), ∀ y μ, ∃ U,
  (∀ ν ε F x, HasSignType (ε * η μ) ν y F x ↔ HasSignType ε ν y F (U * x)) ∧
  (∀ z, Commute y z → Commute (toFinGL z) U) ∧ ∀ q, e ⟦(q, y, μ)⟧ = ⟦(U • q, y, μ)⟧ := by
  have h P μ : ∃ υ : (𝔸f E)[X], ∀ y, y.1.charpoly = P → ∃ U, U.1 = υ.aeval (y.1.map (↑)) ∧
    ∀ ν ε F x, HasSignType (ε * η μ) ν y F x ↔ HasSignType ε ν y F (U * x)
  by_contra H
  obtain ⟨z, rfl, ν, _⟩ := by simpa using (H ⟨1, ·⟩)
  have hP : Fact (Irreducible z.1.charpoly) := ⟨by grind⟩
  obtain ⟨_, -, sj, ker, hev, _⟩ :=
    adjoinRoot_cm_presentation z.1.charpoly_monic ν (by grind [Φ_eq_or ·]) rfl rfl
  let φ w i := lift _ _ (by simpa using isRoot_numberedRoots hP.1.separable (Φ w) i)
  obtain ⟨⟨c, _⟩, ⟨⟨δ⟩, _, a⟩, υ, hs, hυ⟩ := (star (root z.1.charpoly)).mk_surjective,
    @(@exists_eq_principalIdele_mul_norm _ _ ⟨⟩).1 1 (by simp) (∏ (w) (i) with InfinitePlace.mk
    (φ w i) = ·, η μ w i) (by rw [prod_fiberwise, prod_product, hη])
  refine H ((sj ↑υ⁻¹).imp fun g hg y e ↦ ?_)
  obtain ⟨d, ψ, K⟩ := isUnit_aeval_iff_isCoprime.2 (e ▸ hP.1.coprime_iff_not_dvd.2
    (left_ne_zero_of_mul_eq_one a ∘ mk_eq_zero.2)), (liftOfSurjective _ sj).3.surjective ⟨(aeval
    (toFinGL y).1).1, by simp [LE.le, ker, dvd_def, ← e, ← charpoly_map, aeval_self_charpoly]⟩
  simp [liftOfRightInverse, RingHom.ext_iff] at K
  use υ⁻¹.map ψ, by simp [← K, *], fun ν ε F x ↦ .symm (d.unit.mulRight.exists_congr
    fun β ↦ .trans (and_congr_right fun h ↦ congr($(gram_mul_of_gram_eq ?_ rfl) ∈ F).to_iff.and ?_)
    (and_congr_left'
    (by rw [IsEllipticSimilitude, IsEllipticSimilitude, ← d.mul_left_inj]; simp [aeval_semiconj])))
  have a := congr((toFinGL y).1ᴴ * β.map (algebraMap ..) * $(hev (C ν.cast - X * c) ▸ K _))
  simp [mul_sub, ← mul_assoc, @algebraMap_eq_smul_one (𝔸f E), eq_sub_iff_add_eq, h.2, *,
    ← map_conjTranspose_mul_mul, -aeval_map_algebraMap,
    (adjoinRoot_cm_presentation z.1.charpoly_monic ν (by grind [Φ_eq_or ·]) ..).2] at a
  simp [← hg, K, ← star_eq_conjTranspose, star_aeval, ← aeval_comp,
    ← aeval_semiconj (y := star _) a, -aeval_map_algebraMap]
  simpa [← K, *, -hυ] using! congr(_ * ψ $(div_eq_of_eq_mul'' hυ))
  choose _ _ _ K using (exists_eigenbasis_diag_form h · 1)
  simp [*, ← map_mul, -interpolate_apply, eval_interpolate_univ_node]; peel with w i
  erw [← mul_pos_iff_of_pos_right (hs rfl (φ w i)), prod_eq_single (w, i), lift_mk] <;>
    simp [AdjoinRoot.ringHom_ext_iff, φ] <;> grind [InfinitePlace.mk_eq_iff, mk_Φ]
  choose υ U hU h using h
  have hz z y μ : SemiconjBy (toFinGL z) (U _ μ y rfl) (U _ μ (z * y * z⁻¹) rfl) :=
    .units_of_val (by simpa [hU, -mul_assoc] using! aeval_semiconj (by simp) _)
  use Quotient.congr (prodCongrLeft fun (y, μ) ↦ toPerm (U _ μ y rfl)) fun _ _ ↦ exists_congr
    fun _ ↦ (apply_eq_iff_eq _).symm.trans (Eq.congr_left congr(($((hz ..).map (toPermHom ..)) _,
    _)).symm), fun _ _ ↦ ⟨_, h _ _ _ rfl, by grind [Commute, mul_inv_cancel_right], by tauto⟩
