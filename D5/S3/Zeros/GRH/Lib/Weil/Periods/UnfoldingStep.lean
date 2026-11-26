/- GID: D5/S3/Zeros/GRH/Lib/Weil/Periods/UnfoldingStep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Periods/UnfoldingStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Periods.UnfoldingStep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Periods/UnfoldingStep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.TwoEdgesOnePair
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the transfer of Bessel and Fourier–Jacobi periods under a theta lift (one
unfolding step). This file treats unitary pairs and hook orbits with a definite complement, with the
Bessel and Fourier–Jacobi cases together. The period is taken against any continuous automorphic
function with the generic unipotent character, for a rapidly decreasing form, with absolute
convergence. Source: B. Wang Peng Jun, Global theta lifting and automorphic periods associated to
nilpotent orbits, J. Number Theory 271 (2025) 122–149, Prop. 3.2 and Thm. 4.5; for the local case,
R. Gomez, C.-B. Zhu, GAFA 24 (2014) 796–853; for unitary hooks, M. Furusawa, K. Morimoto, Math. Ann.
391 (2025) §3.

This file: Surviving rational orbit by Witt's theorem, its stabiliser, twists killing other terms.
Constant terms along graded isotropic subspaces: substitution rules, Fourier expansion, next generic
function. One unfolding step transferring Bessel or Fourier-Jacobi periods across a theta lift. -/

noncomputable section

section

open Finite Finset MatMul Matrix Space WeilData

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero IsOrderedRing.toIsStrictOrderedRing

attribute [-simp] Matrix.one_apply

attribute [local grind] HasDegreeGe sum_eq_zero Grading.hasDegreeGe_neg_one_stringMap
  Grading.gradeOf_stringReversal Matrix.sub_apply star_zero

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] [Fintype X']
  {s : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s) (Y' : Grading V' N X' (s - 1)) [WeilData E]

/-- β(Tu, T) = β(wu, w) for every unipotent u with u − 1 of degree ≥ 2 and w(u − 1) of degree ≥
1 for target weights D; T = `Grading.stringMap`. -/
abbrev Grading.Survives D w := ∀ u ∈ Y.unipotent,
  HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1) ∧ HasDegreeGe D Y.gradeOf 1
  (w * (V.ratCoordMatrix u - 1)) → V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u)
  (Y.stringMap Y') = V.homBicharacter V' (w * V.ratCoordMatrix u) w

attribute [local simp] HasDegreeGe Fin.val_inj mulVec_neg mul_vecMulVec eichlerMap mul_sub star_form

omit [Fintype X'] in
lemma Grading.eq_of_survives {w D} (H : Y.Survives Y' D w) v k (h : (∀ p,
  Y.gradeOf p < 1 ⊔ (2 + Y.gradeOf k) → v p = 0) ∧ (∀ p, D p ≤ Y.gradeOf k ⊔ -1 → (w *ᵥ v) p = 0) ∧
  ∀ p q, D p + Y.gradeOf q ≤ 0 → w p (Y.stringReversal k) = 0 ∨ v q = 0 := by simp; grind) :
  ((V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y') *ᵥ v) k = ((V.formAdjoint V'
  w * w) *ᵥ v) k := sub_eq_zero.1 (eq_zero_of_forall_stdAddChar_eq_one
  fun t ↦ let x := Pi.single (Y.stringReversal k) (star (↑(j⁻¹ * V.J⁻¹ k (Y.stringReversal k)) *
    t)); (Y.exists_eichlerMap v x (Y.gradeOf k)).elim fun u ⟨hu, e⟩ ↦ by
    have b y : stdAddChar E (toAdele j * star x ⬝ᵥ (yᴴ * V'.J.map toAdele * y) *ᵥ v) =
      V.homBicharacter V' (y * V.ratCoordMatrix u)
      y := by rw [← stdAddChar_half, homBicharacter_eq, eq_comm,
      ← stdAddChar_half]; congr 3; simp [e, formAdjoint, ← dotProduct_mulVec, dotProduct_comm _
      (_ ᵥ* _), ← Matrix.mul_assoc, mul_eq_one_symm V.map_J_inv_mul_map_J, (isHermitian_J
      _).eq, ← trace_conjTranspose, conjTranspose_nonsing_inv, trace_mul_comm _ (map _ _)]; grind
    simpa [↓← b, x, AddChar.map_sub_eq_div, div_eq_one, Circle.ext_iff, ← mul_assoc, ← map_mul,
      formAdjoint, Y.J_inv_eq_gradedGram, ↓map_gradedGram_mul_apply, mulVec_apply_eq_sum, mul_sum,
      mul_comm t (toAdele _)] using
      H u hu (by simp [e, Y.vecMul_J_apply, vecMulVec_apply, x, -single_vecMul]; grind))

omit [WeilData E] [Fintype X] in
/-- Let s = s' + 1, and k a string index of Y' of grade ≥ 0. Some index a of Y one grade higher and
adelic unit t give m·(w e_a) = m_k t whenever w satisfies `Grading.AgreesWithT` and m vanishes in
grades above that of k. -/
lemma Grading.exists_gradeOf_succ_isUnit_stringMap : ∀ k, ite (Y'.indexEquiv.symm k).isRight 0 1 ≤
  Y'.gradeOf k → ∃ a, Y.gradeOf a = Y'.gradeOf k + 1 ∧ IsUnit (Y.stringMap Y' k a) ∧ ∀ {w},
  Y.AgreesWithT Y' w → ∀ m, (∀ l, Y'.gradeOf l ≤ Y'.gradeOf k ∨ m l = 0) → m ⬝ᵥ (w · a) =
  m k * Y.stringMap Y' k a := by simpa [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv,
  stringMap, dotProduct] using fun k _ ↦ ⟨⟨k, by lia⟩, by grind [sum_eq_single k]⟩

omit [WeilData E] in
lemma Grading.agreesWithT_mul_iff {w γ} (hγ : γ ∈ Y.besselGroup) (hw : Y.AgreesWithT Y' w) : ∀ δ,
  Y.AgreesWithT Y' (V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ)) ↔
  δ ∈ Y'.besselGroup := suffices ∀ {δ}, _ from (⟨fun h ↦ Y'.mem_besselGroup_iff_sub_one.2 fun b ↦
    int_weight_induction (-Y'.gradeOf ·) fun k o p _ ↦ (Y.exists_gradeOf_succ_isUnit_stringMap _ k
    p).elim fun a ⟨_, t, e⟩ ↦ by rw [← t.mul_left_eq_zero, ← e (this (one_mem
    _)), ← mul_apply'] <;> simp <;> grind [by simpa using this (one_mem _) b a], @this ·⟩)
  by grind [→ hasDegreeGe_zero_of_mem_besselGroup, → hasDegreeGe_zero_mul_stringMap_mul_sub,
    Matrix.mul_apply, -sum_eq_zero]

lemma Grading.hasDegreeGe_of_survives {w} (hw : Y.AgreesWithT Y' w) (H : Y.Survives Y' Y'.gradeOf
  w) : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (w - Y.stringMap Y') := int_weight_induction Y'.gradeOf
  fun b m a l ↦ sub_eq_zero.2 (by_contra (· ((Y.exists_gradeOf_succ_isUnit_stringMap Y'
  (Y'.stringReversal b) (by grind)).elim fun i ⟨n, t, e⟩ ↦ by rw [← V.formAdjoint_formAdjoint _ w,
  Y'.formAdjoint_apply Y, ← (by simpa (disch := grind [Y.formAdjoint_apply Y']) [mul_apply', e,
  t.mul_left_inj] using Y.eq_of_survives _ H (Pi.single i 1) (Y.stringReversal a) :),
  ← formAdjoint_apply, formAdjoint_formAdjoint])))

/-- Let s' = s − 1. If a rational w satisfies `Grading.Survives` (frequency T, target weights 0),
some rational unitary δ of V' makes δw agree with T in negative degree on basis vectors of positive
grade. -/
lemma Grading.exists_agreesWithT : ∀ w ∈ ratMatrices .., Y.Survives Y' 0 w → ∃ δ ∈ V'.Γ,
  Y.AgreesWithT Y' (V'.ratCoordMatrix δ * w) := by
  rintro _ ⟨_, rfl⟩ H
  have L {x} (H : Y.Survives Y' 0 (map x toAdele)) : HasLeftInv (k := univ.filter (0 < Y.gradeOf ·))
      (x.submatrix id (↑)) := .of_ker_le_bot fun u hu ↦
    funext (int_weight_induction (Y.gradeOf ·.1) (by
    simp [reindex_equiv Y.indexEquiv]
    by_contra! ⟨a, l, _⟩
    have e : x.map (↑) *ᵥ toAdele ∘ Finsupp.indicator _ (u ⟨·, ·⟩) = 0 := by
      simp_all [funext_iff, mulVec_apply_eq_sum, ← map_mul, ← map_sum, sum_dite]
    absurd Y.eq_of_survives _ H _ (Y.indexEquiv (.inr ⟨a + 1, by omega⟩))
      (by rw [e]; simp [reindex_equiv Y.indexEquiv]; grind)
    simp [formAdjoint_stringMap_mul_stringMap, ← mulVec_mulVec, e, shift]
    simp [mulVec_apply_eq_sum, reindex_equiv Y.indexEquiv, -mul_dite, ← map_mul,
      ← map_sum]; grind [Y.3]))
  refine (V'.witt (L H) (L fun _ _ _ ↦ rfl) (ext fun k i ↦ toAdele.injective ?_)).elim fun g e ↦
    ⟨_, ⟨g, rfl⟩, fun b a _ _ ↦ by simpa [mul_apply, ratCoordMatrix, ratEmbed,
    stringMap] using! congr(toAdele ($e b ⟨a, by simpa⟩))⟩
  have G {M} := Y.2 ▸ Y.map_gradedGram_mul_apply toAdele (replicateCol _ M) k ()
  simpa [↓← replicateCol_mulVec, formAdjoint, ← Matrix.mul_assoc,
    mul_eq_one_symm V.map_J_inv_mul_map_J, mul_apply, stringMap, ↓mulVec_mulVec] using
    G.trans (G.trans congr(_ * $(Y.eq_of_survives _ H (Pi.single i 1) _))).symm

end

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal

open Matrix QuotientAddGroup Subtype WeilData Function Space Splitting Circle Set Heisenberg MatMul
  MeasureTheory Subgroup MulAction ProbabilityTheory ENNReal ContinuousLinearMap
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] [Fintype X']
  {s : ℕ} {s' : ℕ} {N : E} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s) (Y' : Grading V' N X' s') (d : ι' → ℤ) [WeilData E]
  (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V'))

omit [WeilData E] in
lemma Space.mul_mem_ratMatrices {γ δ w} : γ ∈ V.Γ → δ ∈ V'.Γ → w ∈ ratMatrices E ι' ι →
  V'.ratCoordMatrix δ * (w * V.ratCoordMatrix γ) ∈ ratMatrices .. := by simp +contextual [Γ,
  ratCoordMatrix, ratEmbed, ratMatrices, U.map, comm, ← Matrix.map_mul]

/-- The rational points of U(V) whose matrix in rational coordinates lowers no d-grade, that is,
has entry (i, j) zero whenever d(i) < d(j). -/
def Space.ratParabolic (V : Space E _ ε') :=
  V.Γ ⊓ (parabolic (-d ·)).comap V.ratCoordMatrix.toHomUnits

namespace Grading

/-- The constant term at w of a datum f on Hom(V,V') along the maps of positive degree, for the
grades of Y and weights d on V'. -/
def constTerm w := quotMean (_root_.ratVectors ..) (homHeisOp w f <| V.homAtPoint V' <| vecToMat <|
  {r | 0 < Y.mapDegree d r}.indicator ·)

/-- The constant term at T, along the maps of positive degree from Y to Y', of the Weil translate
ω(g,h)f, ω = `Space.twistedPairWeil` for α. -/
abbrev constTermAtT g h := Y.constTerm Y'.gradeOf (twistedPairWeil α (g, h) f) (Y.stringMap Y')

/-- The unfolded function P'_x(h): the integral over r in [B] of P(rx) times the constant term
at T of ω(rx, h)f, B the Bessel subgroup of Y. -/
def unfoldStep (P : _ → ℂ) (x : G E ε) h := ∫ r,
  P (r * x) * Y.constTermAtT Y' α f (r * x) h ∂Y.besselMeasure

variable {d} {α} {f} {Y} {P : G E ε → ℂ} {Y' : Grading V' N X' (s - 1)}
  (hd : ∀ b, d (Y'.stringReversal b) = -d b) {γ x : G E ε} {δ : G E ε'}

instance : Countable (_ ⧸ Y.nonnegMaps d) := Quotient.countable

include hd

omit [Fintype X'] in
lemma exists_splitting_constTerm : ∃ m s₀ U D, (D :
  (V.hom V').Splitting (n₀ := Fin m) (s₀ := s₀) U {r // 0 < Y.mapDegree d r}).k = inclMatrix E val ∧
  (V.hom V').J⁻¹ * (D.k * (D.kᴴ * (V.hom V').J)) = diagonal (if Y.mapDegree d · < 0
  then 1 else 0) ∧ ∀ f w, Y.constTerm d f w = U.θ (D.zeroTerm (homHeisOp w f)) := by
  have : ∀ a b, (V.hom V').J a b ≠ 0 → Y.mapDegree d a = -Y.mapDegree d b := by
    simp [hom, Y.J_inv_eq_gradedGram, Y'.2, gradedGram, stringReversal, reindex_equiv Y.indexEquiv,
      reindex_equiv Y'.indexEquiv, mapDegree] at *; grind
  peel (V.hom V').exists_splitting ⟨_, inclMatrix_transpose_mul_self
    (.subtype (0 < Y.mapDegree d ·))⟩ (by simp [entrywise, inclMatrix]; grind) with _ _ _ D H
  use H, by erw [inv_mul_eq_iff_eq_mul_of_invertible, H, Matrix.ext (M := _ᴴ * _),
    ← (eq_inclMatrix_mul_iff _).2] <;> simp [diagonal_apply, inclMatrix, mul_apply] <;> grind
  intros; erw [D.zeroTerm_apply, ← quotMean_comp (_root_.ratVectors ..) (.mk' _ (by tauto)) _ _
    val_injective.surjective_comp_right _] <;> simp_all [constTerm, ↓isContPeriodic_along_k,
    comp_def, ← x_inv_mulVec_matToVec,
    mem_ratVectors, ↓← kAdelic_mulVec _ H, matToVec, vecToMat, -sub_pos, -Int.sub_pos]; fun_prop

lemma constTerm_congr_rat (w w' : ratMatrices E ι' ι) (e : (w : _ ⧸ Y.nonnegMaps d) = w') :
  Y.constTerm d f w = Y.constTerm d f w' := by
  obtain ⟨⟨_, w, rfl⟩, _, z, rfl⟩ := w, w'; delta constTerm; congr! 2
  iterate 2 erw [← θ_ϱ, ϱ_swap, map_smul, theta_eq_rawTheta,
    (isThetaFunctional_rawTheta _).1 _ ⟨matToVec _, vecAtPoint_hom ..⟩, eq_comm]
  simp_all [eq_iff_sub_mem, nonnegMaps, HasDegreeGe, ← map_sub, homBicharacter_eq, trace, mul_apply,
    Y.formAdjoint_apply Y', vecToMat, indicator]

omit [Fintype X'] in
lemma constTerm_eq_homBicharacter_mul w w' (hy : HasDegreeGe d Y.gradeOf 1 (w - w')) :
  Y.constTerm d f w' = V.homBicharacter V' w w' * Y.constTerm d f
  w := by choose _ _ _ _ H _ L using Y.exists_splitting_constTerm hd; rw [L, ← zeroTerm_rho_kAdelic,
  kAdelic_mulVec _ H, x_inv_mulVec_matToVec
  (w - w')] <;> simp_all [HasDegreeGe, matToVec, sub_eq_add_neg, add_left]

lemma hasSum_constTerm : HasSum (fun x : _ ⧸ Y.nonnegMaps d ↦ Y.constTerm d f x.out) (f 0) ∧ ∃ M :
  NNReal, ∀ f : 𝒮 (V.hom V'), ∑' x : _ ⧸ Y.nonnegMaps d, ‖Y.constTerm d f x.out‖ₑ ≤ M * ‖f‖ₑ := by
  choose _ _ U D _ P L using Y.exists_splitting_constTerm hd; let r x :
    _ ⧸ Y.nonnegMaps d := ⟦⟨_, vecToMat x, rfl⟩⟧
  have k x y : _ = (r x = r y) := congr($P *ᵥ x = $P *ᵥ y).trans (by
    simp [nonnegMaps, eq_iff_sub_mem, HasDegreeGe, funext_iff, r, vecToMat, ← map_sub]; grind)
  let e := Equiv.ofBijective (r ∘ D.l.mulVec) ⟨fun a b
    h ↦ by simpa [← Matrix.mul_assoc] using
    congr((D.lᴴ * (V.hom V').J * (V.hom V').J) *ᵥ $((k ..).mpr h)), Quot.ind fun ⟨_, x, rfl⟩ ↦
    ⟨(D.kᴴ * (V.hom V').J) *ᵥ matToVec x, (k _ (matToVec x)).mp (by simp [↓mulVec_mulVec])⟩⟩
  simp_rw [← e.hasSum_iff, ← e.tsum_eq, comp_def, fun f a ↦
    (by erw [constTerm_congr_rat hd _ _ (out_eq' _), L, mixedTerm, ← mulVec_mulVec,
    ← funext (toAdele.map_mulVec _ a), homHeisOp, ← x_inv_mulVec_matToVec]; rfl :
    Y.constTerm d f (e a).out = θ _ (D.mixedTerm _ f))]
  exact ⟨hasSum_theta_mixedTerm f, D.tsum_enorm_mixedTerm_le.imp' _ fun _ h f ↦ by
    grw [U.θ.le_opENorm, ENNReal.tsum_mul_left, h, ← mul_assoc]; rfl⟩

lemma tsum_constTerm_agreesWithT (hS : d ≤ Y'.gradeOf ⊔ 0) : ∑' x : {x : _ ⧸ Y.nonnegMaps d
  | Y.AgreesWithT Y' x.out}, Y.constTerm d f x.1.out = quotMean (ratMatrices ..) fun v ↦ (fun y ↦
  homHeisOp (V'.formAdjoint V y) f 0 / stdAddChar E (toAdele j * (y * Y.stringMap Y').trace))
  (of fun a b ↦ ite (0 ⊔ Y'.gradeOf b < Y.gradeOf a) (v a b) 0) := by
  choose r o using
    (· - (⟨Y.stringMap Y', _, rfl⟩ : ratMatrices ..) |>.2); simp [← ext_iff, Pi.le_def] at o hS
  convert isDualFamily_ratMatrices.tsum_coeff_eq_quotMean (fun x ↦ of fun b a ↦
    j * ite (0 ⊔ Y'.gradeOf b < Y.gradeOf a) (r x.out b
    a) 0) ?_ (Y.hasSum_constTerm hd).1.summable; swap; simp [← ext_iff]; grind [map_eq_zero]
  apply ((Y.hasSum_constTerm hd).1.div_const _).tsum_eq.symm.trans; congr! 2
  rw [constTerm, ϱ_swap]; simp_rw [homBicharacter_eq, Space.smul_apply, quotMean_const_mul,
    ← constTerm.eq_1]
  rw [Y.constTerm_eq_homBicharacter_mul hd 0, sq, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
    ← add_mul, ← map_add, add_halves, formAdjoint_formAdjoint, mul_div_right_comm, ← Circle.coe_div,
    ← AddChar.map_sub_eq_div, ← mul_sub, ← trace_sub, ← Matrix.mul_sub,
    trace_mul_comm] <;> simp [constTerm, trace, mul_apply, apply_ite, Finset.mul_sum, HasDegreeGe,
    Y'.formAdjoint_apply Y, homBicharacter_eq, -Matrix.sub_mul] <;> grind [gradeOf_stringReversal]

omit [Fintype X'] in
/-- Let d be odd under the duality of Y'. The constant term of ω(γg, δh)f at w is that of
ω(g,h)f at δ⁻¹wγ, if γ ∈ B and δ are rational with δ⁻¹ of d-degree ≥ 0, or if γ − 1 raises
grades and δ − 1 raises d. -/
lemma constTerm_mul (o : γ ∈ Y.ratBessel ∧ δ ∈ V'.ratParabolic d ∨ γ ∈ Y.unipotent ∧
  HasDegreeGe d d 1 (V'.ratCoordMatrix δ - 1)) g h w : Y.constTerm d
  (twistedPairWeil α (γ * g, δ * h) f) w = Y.constTerm d (twistedPairWeil α (g, h) f)
  (V'.ratCoordMatrix δ⁻¹ * (w * V.ratCoordMatrix γ)) := by
  choose _ _ _ D H P L using Y.exists_splitting_constTerm hd
  have t f : D.zeroTerm (twistedPairWeil α (γ, δ) f) 0 = D.zeroTerm f 0; obtain ⟨p, q⟩ | ⟨p, q⟩ := o
  · choose c e using mem_ratMatrices.2
      (mem_Gamma_iff_ratCoordMatrix.1 (G.onHom_mem_Gamma _ _ (inv_mem p).1 (inv_mem q).1))
    have k : D.ActsOnFrame _ ((c.toBlock _ _).map toAdele) :=
      e ▸ actsOnFrame_submatrix_ratCoordMatrix D H (by
      have := (inv_mem q).2; simp_all [parabolic, BlockTriangular]; grind [HasDegreeGe,
        Y.hasDegreeGe_zero_of_mem_besselGroup p.2])
    simpa [D.zeroTerm_apply, ← k, pairWeil_of_mem_Gamma _ _ _ _ p.1 q.1] using
      quotMean_comp _ (toLin' _).toAddMonoidHom (D.isContPeriodic_along_k f 0)
      (map_mulVec_mem_ratVectors _) (mulVec_surjective_iff_isUnit.2 k.isUnit)
  have U : HasDegreeGe (Y.mapDegree d) (Y.mapDegree d) 1 ((V.hom V').ratCoordMatrix (.onHom (γ,
    δ)) - 1) := by have := Y.mem_unipotent.1 (inv_mem p); simp_all [HasDegreeGe]; grind
  simp [pairWeil_apply, det_eq_one_of_hasDegreeGe_one q, det_eq_one_of_hasDegreeGe_one
    (Y.mem_unipotent.1 p), det_eq_one_of_hasDegreeGe_one U, zeroTerm_omega_of_inclMatrix _ H
    (g₀ := 1) (fun _ _ _ ↦ sub_self _) (U · · ∘ by simp) (det_ratCoordMatrix _)
    (by simpa using U.mul (d' := 0) (by simpa [HasDegreeGe, ← ext_iff] using congr($P.symm * D.i)))]
  simp [L, ← t (homHeisOp (_ * _) _), pairWeil_homHeisOp, rep_apply_apply, ← Matrix.mul_assoc,
    ← map_mul, w.mul_assoc]

lemma IsGeneric.unipotent_mul_constTerm (hP : Y.IsGeneric P) {u w} (hu : u ∈ Y.unipotent) (h₁ :
  HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1)) (h₂ : HasDegreeGe d Y.gradeOf 1 (w *
  (V.ratCoordMatrix u - 1))) x g h : P (u * x) * Y.constTerm d (twistedPairWeil α (u * g, h) f) w
  = V.homBicharacter V' (Y.stringMap Y' * V.ratCoordMatrix u) (Y.stringMap Y') / V.homBicharacter V'
  (w * V.ratCoordMatrix u) w * (P x * Y.constTerm d (twistedPairWeil α (g, h)
  f) w) := by simp [hP.3, one_mul h ▸ constTerm_mul hd (.inr ⟨hu, by simp [HasDegreeGe]⟩) g h,
  Y.constTerm_eq_homBicharacter_mul hd _ w (by simpa using h₂), homBicharacter_eq,
  formAdjoint_stringMap_mul_stringMap, ← Matrix.mul_assoc, *, field]

omit hd

lemma constTermAtT_rat_mul (γ : Y.ratBessel) (δ : Y'.ratBessel) g h : Y.constTermAtT Y' α f (γ * g)
  (δ * h) = Y.constTermAtT Y' α f g h := (constTerm_mul Y'.gradeOf_stringReversal (.inl ⟨γ.2, δ.2.1,
  (by simpa using hasDegreeGe_zero_of_mem_besselGroup _ δ.2.2 ·)⟩) ..).trans (Y.constTerm_congr_rat
  Y'.gradeOf_stringReversal ⟨_, mul_mem_ratMatrices γ.2.1 δ⁻¹.2.1 ⟨_, rfl⟩⟩ ⟨_, _,
  rfl⟩ (eq_iff_sub_mem.2 (Y.hasDegreeGe_zero_mul_stringMap_mul_sub γ.2.2 δ⁻¹.2.2)))

/-- Let s' = s − 1 and let Y, Y' have the same constant c. If P is continuous, invariant under
rational points of B and follows the character on degree ≥ 2 unipotents (`Grading.IsGeneric` for
Y), then the unfolded function `Grading.unfoldStep` has these properties for Y'.

Known result: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding
step). -/
lemma isGeneric_unfoldStep (hP : Y.IsGeneric P) (hc : Y'.c = Y.c) :
  Y'.IsGeneric (Y.unfoldStep Y' α f P x) := by
  obtain ⟨_, _, _, U, D, _, _, L⟩ := hP.1, Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  use .congr (by fun_prop) fun h ↦ (strongIntegral_apply Y.besselMeasure (fun r ↦
    P (r * x) • θ _ ∘L D.zeroTerm ∘L homHeisOp (Y.stringMap Y') ∘L twistedPairWeil α (r * x, 1))
    (fun f ↦ integrable_of_cocompact Y.isCocompact_ratBessel (by simp; fun_prop) fun
    γ o r ↦ by simp [← L, mul_assoc, hP.2 γ o, ← constTermAtT_rat_mul ⟨_, o⟩ 1 (r * x)])
    (twistedPairWeil α (1, h) f)).trans (by simp [unfoldStep, L, rep_apply_apply]), fun _ o ↦
    (by simp [unfoldStep, ← constTermAtT_rat_mul 1 ⟨_, o⟩ _ ·]), fun _ _ _ hb ↦ ?_
  erw [← integral_const_mul, unfoldStep]; congr! 2
  rw [constTermAtT, constTerm_eq_homBicharacter_mul Y'.gradeOf_stringReversal _ _
    (by simpa using hb.mul Y.hasDegreeGe_neg_one_stringMap), ← one_mul (_ * x), constTerm_mul
    Y'.gradeOf_stringReversal] <;> simp_all [homBicharacter_eq, formAdjoint_stringMap_mul_stringMap,
    ← Matrix.mul_assoc, ← map_mul, trace_mul_comm _ (Y.stringMap Y'), field]

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X] [Fintype X']
  {s : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  {Y : Grading V N X s} (Y' : Grading V' N X' (s - 1)) {P : G E ε → ℂ} [WeilData E]
  (α : (n : Type) → [Fintype n] → AutChar E) (Φ : 𝒮 (V.hom V')) (hP : Y.IsGeneric P) (x : G E ε)
  {y : G E ε' → ℂ} (hy : V'.IsAutomorphic y) (hy' : V'.IsRapid y) (d : ι' → ℤ)

attribute [local simp] compHom_smul_def mul_assoc

instance : MulAction (Y.ratBessel × V'.ratParabolic d) (_ ⧸ Y.nonnegMaps d) := by
  refine' { smul γ := map _ _ (.mk' (⟨_, mul_mem_ratMatrices γ⁻¹.1.2.1 γ.2.2.1 ·.2⟩) _) fun _ h ↦
    (by apply HasDegreeGe.mul (d := 0) (fun _ _ _ ↦
    γ.2.2.2 (by lia)) (h.mul (Y.hasDegreeGe_zero_of_mem_besselGroup γ⁻¹.1.2.2)
    le_rfl) le_rfl), .. } <;> simp [forall_mk, HSMul.hSMul]

include hP hy

/-- Let s′ = s − 1, P generic (`Grading.IsGeneric`), y continuous and invariant under rational
points, d odd under duality, d ≤ max(grade, 0). The terms k_w(h, r) = P(rx)·ct_d(ω(rx, h)Φ)(w)·y(h)
are continuous, rationally equivariant and absolutely summable uniformly in r; ∑_A ∫ k_w dr = ∫ ∑_B
k_w dr if A ⊆ B, with B∖A stable under `Grading.ratBessel` and satisfying the negation of
`Grading.Survives` at d. -/
lemma tsum_integral_eq_of_not_survives (hd : ∀ b, d (Y'.stringReversal b) = -d b) (hS : d ≤
  Y'.gradeOf ⊔ 0) {k} (hk : k = fun (w : _ ⧸ Y.nonnegMaps d) h (r : Y.besselGroup) ↦ P (r * x) *
  Y.constTerm d (twistedPairWeil α (r.1 * x, h) Φ) w.out * y h) : (∀ h (A B : Set _), A ⊆ B
  → (∀ w ∈ B \ A, ¬Y.Survives Y' d w.out ∧ ∀ γ, ((γ, 1) : Y.ratBessel × V'.ratParabolic d) • w ∈ B \
  A) → ∑' w : A, Y.besselMeasure[k w h] = ∫ r, ∑' w : B, k w.1 h r ∂Y.besselMeasure) ∧
  (∀ (γ : Y.ratBessel × V'.ratParabolic d) w, (∀ h r, k (γ • w) (γ.2 * h) (⟨_, γ.1.2.2⟩ * r) =
  k w h r) ∧ (Y.AgreesWithT Y' (γ • w).out ↔ Y.AgreesWithT Y' (V'.ratCoordMatrix γ.2 * (w.out.1 *
  V.ratCoordMatrix γ⁻¹.1)))) ∧ (∀ w, Continuous ↿(k w)) ∧ ∃ a : NNReal, ∀ h (δ : V'.ratParabolic d)
  (S : Set _) r, ∑' w : S, ‖k w.1 h r‖ₑ ≤ ‖y h • pairWeil V V' (α ι) (α ι') (1, δ * h)‖ₑ * a := by
  choose _ K hK γ n i using And.intro hP.1 Y.isCocompact_ratBessel
  obtain ⟨⟨_, b, s⟩, ⟨a, ha⟩, _, _, _, _, _, ⟨⟩⟩ := Y.hasSum_constTerm hd (f := Φ),
    hK.bddAbove_image (f := fun r ↦ ‖P (r.1 * x) • twistedPairWeil α (r.1 * x, 1) Φ‖₊)
    (by with_reducible fun_prop), hy.1, Y.exists_splitting_constTerm hd
  refine (fun e m ↦ (fun hb ↦ ⟨fun h A B hA hZ ↦ ?_, e, m, b * a, hb⟩) fun h δ S r ↦ ?_)
    (fun γ w ↦ have o := (γ • w).out_eq'.trans (congrArg _ w.out_eq'.symm)
    ⟨by simp [hk, hy.2 _ γ.2.2.1, hP.2, constTerm_congr_rat hd _ _ o, constTerm_mul hd, ← map_mul,
      ← (V'.ratCoordMatrix _⁻¹).mul_assoc], forall₄_congr fun b a _ _ ↦ sub_eq_zero.1
      (eq_iff_sub_mem.1 o b a ((hS b).trans_lt (by simp [*]))) ▸ .rfl⟩) (by simp [*]; fun_prop)
  simp [← (e (⟨_, n r⟩, δ) _).1 h]
  apply (tsum_comp_le_tsum_of_injective (MulAction.injective _).injOn.injective (‖k · ..‖ₑ)).trans
  grw [mul_left_comm, ← ha ⟨_, i r, rfl⟩, ← enorm_eq_nnnorm, ← le_opENorm, ← s]
  simp [*, rep_apply_apply, hy.2 _ δ.2.1]; ac_nf
  have l S := IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal Y.besselMeasure ⟨_, hb h 1 S⟩
  have s S := hasSum_integral_of_lintegral (l S)
  let := compHom (_ ⧸ Y.nonnegMaps d) (.inl Y.ratBessel (V'.ratParabolic d))
  let Z := SubMulAction.mk _ fun γ _ h ↦ (hZ _ h).2 γ
  rw [(s B).unique (union_sdiff_cancel hA ▸ (s A).add_disjoint (f := (Y.besselMeasure[k · h]))
    disjoint_sdiff_right (s Z)), (s _).tsum_eq, left_eq_add, ← ((s _).tsum_fiberwise (Quot.mk
    (orbitRel Y.ratBessel _))).tsum_eq]
  convert tsum_zero with ⟨o⟩
  choose u v t c using by simpa only [not_forall] using (hZ _ o.2).1
  exact (integral_tsum_orbit (inclusion_injective _) (by simp) (by fun_prop) (fun γ (w : Z) ↦
    one_mul h ▸ (e (γ, 1) w).1 h :) (right_eq_inf.2 ((map_le_range ..).trans (inclusion_range
    inf_le_right).le)) fun _ ↦ Quotient.eq.trans comm).elim fun f O ↦ (O (.inl (l Z))).2.2.trans
    (integral_quotMeasure_eq_zero_of_twist _ f (by fun_prop) (u :=
    ⟨_, Y.unipotent_le_besselGroup v⟩) (by simp)
    (div_ne_one_of_ne c) (by simp [hk, hP.unipotent_mul_constTerm hd v t.1 t.2, field]))

include hy'

/-- One unfolding step, s = s' + 1: for P as in `Grading.IsGeneric` and y rapid continuous on [G'],
the [B]-period at x of P times the theta integral of y is ∫ P'_x·y over B'(E⁺)∖G'(𝔸), which
converges absolutely.

Known result: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding
step). -/
lemma integral_besselGroup_unfold : let F := Y.unfoldStep Y' α Φ P x * y; Integrable F
    Y'.ratBessel.qms ∧ ∫ r, P (r * x) * ∫ h, θ _ (twistedPairWeil α (val r * x, h) Φ) * y
    h ∂V'.quotMeasure ∂Y.besselMeasure = Y'.ratBessel.qms[F] := by
  choose _ _ R Q using ((pairThetaKer V V' _ _).exists_rat_norm_le_height 1).exists
  obtain ⟨⟨k, hk⟩, L⟩ := exists_eq, tsum_integral_eq_of_not_survives Y' α Φ hP x hy
  obtain ⟨⟨e, ⟨o⟩⟩, K, n, m, _, B⟩ := L _ Y'.gradeOf_stringReversal (by simp) rfl,
    L 0 (by simp) (by simp) hk
  have B h := (B h ⟨_, R h, nofun⟩ · · |>.trans (by grw [← ofReal_norm, norm_smul, Q,
    mul_left_comm, (hy' _).choose_spec]))
  have t γ w h := (n γ w).2.trans (Y.agreesWithT_mul_iff _ γ⁻¹.1.2.2 h _)
  let := compHom (ratMatrices E ι' ι ⧸ Y.nonnegMaps 0) (.inr Y.ratBessel (V'.ratParabolic 0))
  have I := (integral_tsum_block (μ := ℙ) val_injective ((V'.ratParabolic 0).range_subtype.trans
    (inf_of_le_left nofun)) inf_le_left (fun δ ↦ (t _ · ·.out |>.trans (and_iff_right δ.2.1).symm))
    (@mem_ofPred _ · _) (m · |>.stronglyMeasurable.integral_prod_right (ν := Y.besselMeasure)
    |>.measurable) (by simp [← n ⟨1, ·⟩ · |>.1 ·, (mk_eq_one _).2]) (.inl (by
    grw [enorm_integral_le_lintegral_enorm, (lintegral_tsum (by fun_prop)).ge, B]
    simp [mul_lt_top_iff, -withDensity_apply]))).imp_right (·.1)
  have e := (e · {.mk'' ⟨_, _, rfl⟩} _ (by exact fun w e b a _ l ↦ sub_eq_zero.1 (eq_iff_sub_mem.1
    (w.out_eq'.trans e) b a (by omega))) fun w ⟨h, l⟩ ↦ ⟨(l <| out_eq' w ▸ eq_iff_sub_mem.2 ·) ∘
    Y.hasDegreeGe_of_survives _ h.out, fun γ ↦
    ⟨(o ..).2.2 ((Y.agreesWithT_mul_iff _ γ⁻¹.2.2 h _).2 (by simp)), ((MulAction.injective _).ne
    l).trans_eq (eq_iff_sub_mem.2 (Y.hasDegreeGe_zero_mul_stringMap_mul_sub γ⁻¹.2.2 (by simp)))⟩⟩)
  rw [funext (K · _ _ .rfl nofun), funext (K · _ univ le_top ?_), integral_integral_swap] at I
  simp (disch := simp) only [hk, (hasSum_unique _).tsum_eq, tsum_mul_left, tsum_mul_right,
    default_coe_singleton, integral_mul_const,
    Y.constTerm_congr_rat Y'.gradeOf_stringReversal _ _ (out_eq' _), Y.tsum_constTerm_agreesWithT,
    (tsum_univ _).trans (Y.hasSum_constTerm (Y' := Y') _).1.tsum_eq] at *
  simpa only [← e, mul_assoc, integral_const_mul] using! I
  exacts [⟨by fun_prop, .of_bounded_enorm coe_ne_top (.of_forall fun _ ↦
    enorm_tsum_le_tsum_enorm.trans (B ..))⟩, fun w ⟨_, h⟩ ↦ ⟨(Y.exists_agreesWithT _ _ w.out.2
    · |>.elim fun δ ⟨e, i⟩ ↦ h ⟨⟨δ, e, nofun⟩, (n ..).2.2 (by simpa)⟩), (⟨⟨⟩, fun ⟨δ, e⟩ ↦ h ⟨δ, by
    simpa [smul_smul] using t ⟨·⁻¹, 1⟩ _ e⟩⟩)⟩]
