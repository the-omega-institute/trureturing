/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/RiemannRelation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ThetaNormality/RiemannRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ThetaNormality.RiemannRelation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ThetaNormality/RiemannRelation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli.FlatClosure
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli.ThetaTorus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Normal generation of sections on abelian varieties, kept under good reduction.
Only degrees that are powers of one integer r are treated here, over a rank-one valuation ring of
the complex numbers. Powers of the sup-norm ball of theta functions are the balls, reduction keeps
the ranks, and no cohomology or vanishing theorem is used. Source: S. Koizumi, Theta relations and
projective normality of abelian varieties, Amer. J. Math. 98 (1976); T. Sekiguchi, J. Math. Soc.
Japan 29 (1977) for characteristic p; G. Kempf, Multiplication over abelian varieties, Amer. J.
Math. 110 (1988).

Known result: Riemann's theta relations. They are stated here in one variable for the theta
coordinates of a PEL torus, with multipliers in the ring of integers of a CM field in place of the
matrix with entries ±1/2. The proof uses Schur orthogonality for the theta group. Source: C.-L.
Chai, Riemann's theta formula (2014), Theorem 1.2; A. Nagano, On Riemann type relations for theta
functions on bounded symmetric domains of type I, arXiv 2301.09243 (2023), Theorem 1.1; D. Mumford,
On the equations defining abelian varieties I, Invent. Math. 1 (1966) §3; G. Kempf, Linear systems
on abelian varieties, Amer. J. Math. 111 (1989) 65–94.

This file: Riemann's theta relation; largest theta constants; reduction cut out by level points. -/

open Complex Finite LatticeForm Finset Fint Function Module MvPolynomial NNReal NumberField
  PeriodMap Submodule thetaSpace

variable {V E k K : Type} [FinComplexSpace V] {v} [Field E] [CMBase E] {D : PEL E} {g ℓ} (x :
  ThetaTorus D g ℓ V) [Fintype K] (a : K → 𝓞 E) {μ μ' : K → D.T} {w t} (p : K → 𝓞 E × 𝓞 E)

namespace ThetaTorus

attribute [-simp] iInf_neg map_eq_zero map_smul nsmul_eq_mul

noncomputable instance : Module (𝓞 E) D.T := module ⟨_, by
  rintro a ⟨y⟩ h; exact (D.mem_T _).2 fun z k ↦ by simpa [xiForm, ↓star_smul] using
    ((D.mem_T y).1 h (algebraMap E (𝔸f E) (star a) • z) (torsionClass.ker.smul_mem (star a) k))⟩

/-- For pairs p_l = (a_l, b_l) in O_E: ∑ ā_l a_l = r and ∑ ā_l b_l = 0, with r the degree in the
data D. -/
def IsRiemannTuple (D : PEL E) := ∑ l, star (p l).1 * (p l).1 = D.r ∧ ∑ l,
  star (p l).1 * (p l).2 = 0

/-- The family of coefficient pairs, on two copies of the index set, made of (0, second entry of
k_l) on the first copy and of p_l on the second. -/
def doubledCoeffs (k : K → 𝓞 E × _) := Sum.elim (0, k · |>.2) p

/-- For pairs p_k = (a_k, b_k) in O_E, μ_k in T and w in V, the function z ↦ ∏_k θ_{μ_k}(a_k z +
b_k w) on V. -/
noncomputable def thetaProduct (μ : K → _) w z := ∏ k,
  x.thetaCoord (μ k) (x.intAction (p k).1 z + x.intAction (p k).2 w)

attribute [local simp] thetaShift_apply exp_add exp_neg Ideal.Quotient.eq_zero_iff_mem map_eval
  PeriodMap.torsionLift bicharacter thetaCoord_ne_zero periodPoint
  PeriodMap.sub_mem_periodLattice_iff adjoint thetaProduct Valuation.pos_iff canonicalMultiplier
  div_eq_inv_mul mul_pow thetaNorm_pow thetaRanks

/-- Let ∑ ā_k a_k = r, ∑ ā_k b_k = 0, ∑ ā_k μ_k = t, y over T. If U_{a_k u} θ_{μ_k} = χ(a_k u)
e(⟨a_k y, μ_k⟩) θ_{μ'_k} for all k, then U_u P_μ = χ(u)^r e(⟨y, t⟩) P_{μ'} in degree rB, P =
`ThetaTorus.thetaProduct`. -/
lemma thetaShift_thetaProduct {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {u y}
    (k : y ∈ x.latticeOver D.T) (h : ∀ k, x.B.thetaShift (x.intAction (p k).1 u) (x.thetaCoord
  (μ k)) = (x.multiplier (x.intAction (p k).1 u) * x.B.riemannPhase (x.intAction (p k).1 y)
  (x.torsionLift (μ k))) • x.thetaCoord (μ' k)) z : (D.r • x.B).thetaShift u (x.thetaProduct p μ w)
  z = x.multiplier u ^ D.r * x.B.riemannPhase y (x.torsionLift t) * x.thetaProduct p μ' w z := by
  obtain ⟨⟨⟩⟩ := x.dualLattice_periodLattice.ge k (∑ k, x.intAction _ (x.torsionLift _) -
    x.torsionLift t) (by simp [intAction, ← toRealVectors_smul, ← map_sum]; simp [← ht]; rfl),
    (congr(x.B u <| x.intAction $(hp.1) ·)), congr(x.B u (x.intAction $(hp.2)
    w)), congr(x.B.riemannForm (x.intAction (D.rescaledBeta * $(hp.1)) u) u)
  simp [← ofReal_inj, sub_eq_iff_eq_add', map_sub, riemannForm_def,
    mul_sum, ↓mul_left_comm D.rescaledBeta] at *
  simpa [*, ← exp_sum, add_right_comm, mul_add, ← zsmul_eq_mul', ← mul_sum, ← exp_nsmul,
    mul_left_comm D.r.cast,
    nsmul_eq_mul] using congr(∏ k, $(h k) (x.intAction (p k).1 z + x.intAction (p k).2 w))

/-- Riemann's theta relation. For P, P' the products `ThetaTorus.thetaProduct` of pairs p, q
satisfying `ThetaTorus.IsRiemannTuple`, with one w and ∑ āμ = ∑ ā'μ': |T| P'_{μ'}(0) P_μ(z) = ⌊√[T :
T[r]]⌋ ∑_{s∈T} P_{μ−as}(0) P'_{μ'+a's}(z).

Known result: Riemann's theta relations. -/
lemma riemann_relation {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {q} (hq :
  IsRiemannTuple q D) (h : ∑ k, star (q k).1 • μ' k = t) [Fintype D.T] z : Fintype.card D.T *
  x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z = (D.rTorsion.relIndex D.T).sqrt * ∑ s,
  x.thetaProduct p (μ - (·.1 • s) ∘ p) w 0 * x.thetaProduct q (μ' + (·.1 • s) ∘ q) w z := by
  obtain ⟨m, r, _⟩ := x.latticeOver_mono (S := D.rTorsion) D.torsion_mem_lagrangian,
    x.hasGoodReduction_trivial.4.ne_bot, (x.thetaCoord_mem_thetaSpace · |>.1)
  obtain ⟨_, d⟩ := x.discreteTopology_latticeOver_lagrangian.of_subset m,
    ((dualLattice_nsmul_le r fun _ ↦ (x.nsmul_mem_latticeOver r).1).antisymm fun _ h
    _ ↦ by simpa using h _ ∘ (x.nsmul_mem_latticeOver r).2).trans x.dualLattice_periodLattice
  rw [← x.relIndex_latticeOver, ← (((x.isAppellHumbert_of_le m).nsmul _).shift _
    _).sum_shift_mul_shift (hp := x.isPosRiemann.nsmul r) _ (⟨_, d.ge <| x.torsionLift_mem ·⟩)
    (d.le ·.2 |>.elim fun y ⟨h, e⟩ ↦ ⟨.addLeft ⟨_, h⟩, by simp [← e, ← map_add, ← map_sub]; simp⟩)
    ⟨_, ?_⟩ ⟨_, ?_⟩] <;> try exact ⟨by fun_prop [thetaProduct], fun l
    h z ↦ by erw [mul_right_comm, ← x.thetaShift_thetaProduct ‹_› ‹_› (x.latticeOver_mono
    D.lagrangian_le_T (m h)) fun k ↦ thetaShift_of_mem (x.thetaCoord_mem_thetaSpace_lagrangian _) (m
    (by grind [=_ nsmul_mem_latticeOver, PEL.rTorsion, intAction_mem_periodLattice, =_
    map_nsmul]))]; simp [field]⟩
  congr with s; have d := congr($(x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem s)
    (x.torsionLift_mem s) rfl) ^ D.r)
  have L y h p μ := (x.thetaShift_thetaProduct (p := p) (K := K) (w := w) (μ' := μ +
    (·.1 • ⟨frameTorsionClass g y, h⟩) ∘ p) · rfl (x.intAction_rescaledBeta_mem_latticeOver le_rfl
    (by tauto)) (u := x.Q _) fun k ↦ by simpa [intAction, smul_comm (cmEmbedding (p k).1.val),
    add_comm] using (x.thetaShift_thetaCoord (s := (p k).1 • ⟨_, h⟩) (map_smul ..) _))
  erw [← map_neg, ← map_neg, L] <;> simp [*, two_mul, add_mul, field, sub_eq_add_neg] at *
  simp [← smul_neg, sq_eq_one_iff.2 d]; ring!

/-- Under good reduction and v(|T|) = 1, every s in T is u + (s − u) with v(θ_u(0))
v(θ_{s−u}(0)) ≥ v(θ_t(0))² for all t: both theta constants have the largest valuation. -/
lemma exists_peak (G : HasGoodReduction x.B x.multiplier v D.r) (hv : v (Nat.card D.T) = 1) s :
    ∃ u, ∀ w ∈ [u, -u, s - u], ∀ t, v (x.thetaCoord t 0) ≤ v (x.thetaCoord w 0) := by
  obtain ⟨T, ⟨o, ho⟩, ⟨η, H⟩, ⟨r, e⟩, u, hu⟩ :=
    (sizes.of_mem_thetaSpace G.1 <| x.thetaCoord_mem_thetaSpace ·), exists_max (v <|
    x.thetaCoord · 0), x.exists_thetaCoord_sign_smul (-1), Nat.exists_eq_add_of_lt D.three_le_r,
    exists_max fun u ↦ v (x.thetaCoord (s - u) 0) ⊓ _
  obtain ⟨N, le⟩ := G.hasMultiplicativeNorm (φ :=
    _ * _) (by simpa using! mul_shift_mem_sizes (T s) (T (D.r • o - s)) 0)
    ⟨G.nsmul r.succ_ne_zero, pow (x.thetaCoord_mem_thetaSpace 0) _⟩, (size_le_iSup <| T ·)
  simp [-Subtype.forall, sizeAt, field, thetaNorm_thetaCoord,
    G.hasMultiplicativeNorm (T _) (T _)] at le N hv H
  have A := not_lt.1 fun q ↦ q.not_ge ((le_of_mul_le_mul_right (congr(v (x.thetaCoord
    o 0) * $N).ge.trans (mul_iSup_le fun z ↦ ?_)) (by simp [G.thetaNorm_pos])).trans (hu u))
  · use u, List.forall_mem_cons.2 ⟨fun _ ↦ by grw [← neg_zero, H, H, map_mul, ho, map_mul, A,
      inf_le_right], by simp [(ho _).trans, A.trans]⟩
  have := congr(v $(x.riemann_relation (w := 0) (p := const _ (1, 0)) (μ' := const _ o) (μ :=
    Option.elim'
    (D.r • o - s) (Sum.elim ![s, 0] (0 : Fin r → _))) ?S ?_ ?S rfl z)).trans_le ((v.leSubmodule
    _).smul_mem (Nat.cast _) (sum_mem fun t ↦ by simp; grw [ho, ← min_mul_max _ (v _), hu, ho (s -
    t), ho (-t), le])) <;> simp [IsRiemannTuple, ↓sizeAt_pow, sizeAt, *, field, pow_add, q.pos] at *
  linarith

/-- Let the theta torus x satisfy `HasGoodReduction` for v, with residue field k. If the N_l have at
t the reduced theta vectors of the level points as coordinates, then `IsCutOutAt`
holds at t for the reductions of all theta vectors (θ_s(z))_s. -/
lemma isCutOutAt_reduction [Field k] {φ : v.valuationSubring →+* k} (hφ : Surjective φ) (G :
  HasGoodReduction x.B x.multiplier v D.r) {q p : _ → _} (hq : ∀ z, IsIntegralCoords (x.thetaCoord
  · z) (q z)) (hp : ∀ l : D.levelTorsion, IsIntegralCoords (x.thetaCoord · (x.torsionLift l)) (p l))
  {S t} {N : _ → LineBundle S _} (hx : ∀ l, (N l).IsHomogCoords t (φ <| p l ·)) :
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) N t (.range (φ ∘ q ·)) := fun l hl c ↦ by
  obtain ⟨T, R, H, Y, U⟩ := pow (x.thetaCoord_mem_thetaSpace c), G.pow, @eval₂_mul_of_isHomogeneous,
    @isHomogeneous_X_pow, (x.formSpan_eq_normBall G c · ▸ (LinearMap.range_domRestrict ..).trans
    (map_homogeneousSubmodule_eq_formSpan ..))
  choose e _ E using (lt_iff_exists_add.1 <| @Nat.pow_lt_pow_succ _ · G.one_lt)
  have W j := ext fun _ ↦ mem_dualLattice_nsmul.trans
    (x.dualLattice_periodLattice ▸ x.nsmul_mem_latticeOver (pow_ne_zero j G.one_lt.ne_bot))
  have P j {I} {a p : I → _} k (h : ∀ b, IsIntegralCoords (x.thetaCoord · (a b)) (p b)) :=
    (R j).thetaNorm_lt_iff_coords (T _) (by simp) (p :=
    fun l ↦ (·.1.eval (p l))) (U j) k (h · |>.imp' _ fun s ⟨e, t, h⟩ ↦ ⟨fun f ↦ by simpa
    [eval_eq, aeval_def, eval₂_eq, e] using (H f.2 (algebraMap ..) s⁻¹ _), ⟨_, Y t _⟩, by simp [h]⟩)
  have Q j (f : homogeneousSubmodule ..) := P _ (⟨·.1, by simp⟩) hq ⟨_, E j ▸ f.2.mul (Y c _)⟩
  simp [*, G.hasMultiplicativeNorm (.of_mem_thetaSpace (f :=
    aeval _ (Subtype.val _)) (R _).1 ((U _).le ⟨_, rfl⟩).1) ⟨G.nsmul _,
    _⟩, -Subtype.forall, add_smul, ↓thetaNorm_pow, pow_add, G.thetaNorm_pos
    (x.thetaCoord_mem_thetaSpace c) (x.thetaCoord_ne_zero c), LatticeForm.thetaNorm, ne_of_gt,
    or_iff_not_imp_right, ↓← v.mem_maximalIdeal_iff, ← IsLocalRing.ker_eq_maximalIdeal φ hφ] at P Q
  have L d : Surjective fun f : homogeneousSubmodule D.T _ d ↦ (⟨_, f.2.map φ⟩ :
      homogeneousSubmodule ..) | ⟨g, h⟩ => ⟨⟨_, sum_mem fun m a ↦ isHomogeneous_monomial
    (surjInv hφ (g.coeff m)) (h.degree_eq_sum_deg_support a).symm⟩, by simp [surjInv_eq]⟩
  use by simp +contextual, fun j ↦ ?_, fun _ a ↦ Subtype.forall'.2 ((L _).forall.2 fun f ↦ by
   simpa +contextual [Q, hx .., ((hx ..).1.1 (hl _)).ne_zero, H f.2, mul_comm (φ _)] using! P
    _ (W _ ▸ fun ⟨_, y, h, rfl⟩ ↦ ⟨⟨_, D.degree_spec.2 _ a _ h⟩, by simp⟩) hp f)
  erw [← (imageMod ..).span_eq, map_coe, Set.image_eq_range, ← (L _).range_comp, (R
    _).finrank_reduction_eq (T _) (by simp) (U _) hφ (y := ⟨⟨_, by simp⟩, by
    simp [Algebra.smul_def]; tauto⟩) fun f ↦ by simp +contextual [Q, H f.2], ← (finrank
    ..).sqrt_eq', (R _).finrank_sq_eq_relIndex (hp := (R _).isPosRiemann).2.1, W,
    relIndex_latticeOver]; simp

/-- The family of pairs in O_E consisting of (1, 0) twice, (c, 1), (1, −c̄), and (a_l, 0) for
every l. -/
noncomputable def _root_.paddingTuple bicharacter := @Sum.elim Bool _ _ (fun _ ↦ (1, 0))
    (Sum.elim (cond · (bicharacter, 1) (1, -star bicharacter)) (a ·, 0))
