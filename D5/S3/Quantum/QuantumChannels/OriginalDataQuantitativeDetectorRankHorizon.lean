/- GID: D5/S3/Quantum/QuantumChannels/OriginalDataQuantitativeDetectorRankHorizon
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OriginalDataQuantitativeDetectorRankHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original density observations quantitatively control spectral tails of arbitrary complex subunital CP maps. -/

import D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension
import D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
open scoped InnerProductSpace CStarAlgebra ComplexOrder MatrixOrder
open InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 4

namespace D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon
private abbrev H (D : ℕ) := EuclideanSpace ℂ (Fin D)
private abbrev Op (D : ℕ) := H D →L[ℂ] H D
private abbrev Mat (D : ℕ) := CStarMatrix (Fin D) (Fin D) ℂ

private def opEquiv (D : ℕ) : Mat D ≃⋆ₐ[ℂ] Op D :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM

private theorem trace_op (D : ℕ) (X : Mat D) :
    LinearMap.trace ℂ (H D) (opEquiv D X).toLinearMap =
      Matrix.trace (CStarMatrix.ofMatrix.symm X) := by
  change LinearMap.trace ℂ (H D)
    ((CStarMatrix.ofMatrix.symm X).toEuclideanLin) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

private theorem trace_rank (D : ℕ) (X : Mat D) (v : H D) :
    (Matrix.trace (CStarMatrix.ofMatrix.symm
      (X * (opEquiv D).symm (rankOne ℂ v v)))).re =
      (inner ℂ v (opEquiv D X v)).re := by
  rw [← trace_op]
  have heq : opEquiv D (X * (opEquiv D).symm (rankOne ℂ v v)) =
      rankOne ℂ (opEquiv D X v) v := by
    rw [map_mul, StarAlgEquiv.apply_symm_apply]
    exact comp_rankOne v v (opEquiv D X)
  rw [heq, trace_rankOne]

private theorem projection_sum {D m : ℕ} (e : Fin m → H D) (he : Orthonormal ℂ e) :
    (Submodule.span ℂ (Set.range e)).starProjection = ∑ j, rankOne ℂ (e j) (e j) := by
  classical
  let b : OrthonormalBasis (Fin m) ℂ (Submodule.span ℂ (Set.range e)) :=
    (Module.Basis.span he.linearIndependent).toOrthonormalBasis
      (by
        convert! orthonormal_span he using 1
        funext i
        exact Module.Basis.span_apply he.linearIndependent i)
  simpa only [b, Module.Basis.coe_toOrthonormalBasis, Module.Basis.span_apply] using
    b.starProjection_eq_sum_rankOne

private theorem conjugate_rank {D : ℕ} (A : Op D) (v : H D) :
    A * rankOne ℂ v v * star A = rankOne ℂ (A v) (A v) := by
  simp only [ContinuousLinearMap.mul_def]
  rw [comp_rankOne, rankOne_comp]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

private theorem trace_mono {D : ℕ} (σ : Mat D) (hσ : 0 ≤ σ) {X Y : Mat D} (hXY : X ≤ Y) :
    (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * X))).re ≤
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * Y))).re := by
  have hσm := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hσ)
  have hYm := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr hXY))
  have ht := (hσm.trace_mul_nonneg hYm).1
  change 0 ≤ (Matrix.trace
    (CStarMatrix.ofMatrix.symm σ * (CStarMatrix.ofMatrix.symm Y -
      CStarMatrix.ofMatrix.symm X))).re at ht
  change (CStarMatrix.ofMatrix.symm σ * CStarMatrix.ofMatrix.symm X).trace.re ≤
    (CStarMatrix.ofMatrix.symm σ * CStarMatrix.ofMatrix.symm Y).trace.re
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using ht

private theorem sqrt_quadratic {D : ℕ} (σ : Mat D) (hσ : 0 ≤ σ) (v : H D) :
    ‖CFC.sqrt (opEquiv D σ) v‖ ^ 2 = (inner ℂ v (opEquiv D σ v)).re := by
  letI : T2Space (Op D) := inferInstance
  have hpos : 0 ≤ opEquiv D σ := map_nonneg (opEquiv D) hσ
  have hs : star (CFC.sqrt (opEquiv D σ)) = CFC.sqrt (opEquiv D σ) :=
    (show IsSelfAdjoint (CFC.sqrt (opEquiv D σ)) from
      IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (opEquiv D σ))).star_eq
  have hsq : star (CFC.sqrt (opEquiv D σ)) * CFC.sqrt (opEquiv D σ) = opEquiv D σ := by
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self (A := Op D) (opEquiv D σ) hpos
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  change (inner ℂ v ((star (CFC.sqrt (opEquiv D σ)) * CFC.sqrt (opEquiv D σ)) v)).re = _
  rw [hsq]

private theorem kraus_operator_action {D : ℕ}
    (T : CompletelyPositiveMap (Mat D) (Mat D)) :
    ∃ K : Fin (D ^ 2) → Op D, ∀ Y : Op D,
      opEquiv D (T ((opEquiv D).symm Y)) = ∑ a, K a * Y * star (K a) := by
  classical
  let k := D5.S3.Quantum.Foundation.FiniteKrausChannel.krausRepresentation T
  let f : Fin (D ^ 2) ≃ Fin D × Fin D :=
    (Fintype.equivFinOfCardEq (by simp [pow_two])).symm
  refine ⟨fun a => opEquiv D (CStarMatrix.ofMatrix (k.val (f a))), ?_⟩
  intro Y
  have hk := k.property (CStarMatrix.ofMatrix.symm ((opEquiv D).symm Y))
  have hc : T ((opEquiv D).symm Y) =
      ∑ a, CStarMatrix.ofMatrix (k.val a) * (opEquiv D).symm Y *
        star (CStarMatrix.ofMatrix (k.val a)) := by
    apply CStarMatrix.ofMatrixStarAlgEquiv.symm.injective
    simp only [map_sum, map_mul, map_star]
    exact hk
  rw [hc, map_sum]
  simp only [map_mul, map_star, StarAlgEquiv.apply_symm_apply]
  exact (Equiv.sum_comp f _).symm

private theorem kraus_contractions {D : ℕ}
    (T : CompletelyPositiveMap (Mat D) (Mat D)) (hT : T 1 ≤ 1)
    (K : Fin (D ^ 2) → Op D)
    (hK : ∀ Y : Op D, opEquiv D (T ((opEquiv D).symm Y)) =
      ∑ a, K a * Y * star (K a)) :
    ∀ a x, ‖K a x‖ ≤ ‖x‖ := by
  classical
  intro a x
  have ht : ∑ a, K a * star (K a) ≤ (1 : Op D) := by
    have hh := hK 1
    simp only [map_one, mul_one] at hh
    rw [← hh]
    simpa only [map_one] using (show opEquiv D (T 1) ≤ opEquiv D 1 from
      OrderHomClass.mono (opEquiv D) hT)
  have hk : K a * star (K a) ≤ (1 : Op D) :=
    (Finset.single_le_sum (fun i _ => mul_star_self_nonneg (K i))
      (Finset.mem_univ a)).trans ht
  have hn : ‖K a‖ ≤ 1 := by
    have hs := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg (K a))).mpr hk
    rw [CStarRing.norm_self_mul_star] at hs
    nlinarith [norm_nonneg (K a)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg x))

private theorem word_domination {D M r : ℕ}
    (F : Op D →ₗ[ℂ] Op D) (hF : Monotone F)
    (K : Fin M → Op D)
    (hK : ∀ Y : Op D, F Y = ∑ a, K a * Y * star (K a))
    (B : Op D) (t : ℝ) (ht : 0 ≤ t)
    (η : Fin r → H D)
    (hη : ∀ b, t • rankOne ℂ (η b) (η b) ≤ B) :
    ∀ (w : List (Fin M)) (b : Fin r),
      t • rankOne ℂ ((w.reverse.map K).prod (η b))
        ((w.reverse.map K).prod (η b)) ≤ F^[w.length] B := by
  classical
  intro w
  induction w using List.reverseRecOn with
  | nil => simpa using hη
  | @append_singleton w a ih =>
    intro b
    let v := (w.reverse.map K).prod (η b)
    have hp : 0 ≤ t • rankOne ℂ v v :=
      smul_nonneg ht (ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (isPositive_rankOne_self v))
    have hk : K a * (t • rankOne ℂ v v) * star (K a) ≤ F (t • rankOne ℂ v v) := by
      rw [hK]
      exact Finset.single_le_sum (fun j _ => star_right_conjugate_nonneg hp (K j))
        (Finset.mem_univ a)
    have he : K a * (t • rankOne ℂ v v) * star (K a) =
        t • rankOne ℂ (K a v) (K a v) := by
      calc
        _ = t • (K a * rankOne ℂ v v * star (K a)) := by
          apply ContinuousLinearMap.ext
          intro x
          simp only [mul_apply_eq_comp, smul_apply, ContinuousLinearMap.map_smul_of_tower]
        _ = _ := congrArg (fun Z : Op D => t • Z) (conjugate_rank (K a) v)
    have hh := (he ▸ hk).trans (hF (ih b))
    simpa [List.reverse_append, List.map_append, List.prod_append,
      Function.iterate_succ_apply', v] using hh

private theorem corner_bound {D M m : ℕ}
    (F : Op D →ₗ[ℂ] Op D) (K : Fin M → Op D)
    (hK : ∀ Y : Op D, F Y = ∑ a, K a * Y * star (K a))
    (e : Fin m → H D) (he : Orthonormal ℂ e)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hres : ∀ a j, ‖K a (e j) -
      (Submodule.span ℂ (Set.range e)).starProjection (K a (e j))‖ ≤ δ) :
    let P := (Submodule.span ℂ (Set.range e)).starProjection
    ‖(1 - P) * F P * (1 - P)‖ ≤ (M : ℝ) * m * δ ^ 2 := by
  classical
  let P := (Submodule.span ℂ (Set.range e)).starProjection
  let Q : Op D := 1 - P
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hQ : star Q = Q := hP.one_sub.isSelfAdjoint.star_eq
  have heq : Q * F P * Q = ∑ a, ∑ j,
      rankOne ℂ (Q (K a (e j))) (Q (K a (e j))) := by
    rw [hK, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show P = ∑ j, rankOne ℂ (e j) (e j) from projection_sum e he,
      Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [conjugate_rank]
    calc
      Q * rankOne ℂ (K a (e j)) (K a (e j)) * Q =
        Q * rankOne ℂ (K a (e j)) (K a (e j)) * star Q := by rw [hQ]
      _ = _ := conjugate_rank Q (K a (e j))
  change ‖Q * F P * Q‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ a, ‖∑ j, rankOne ℂ (Q (K a (e j))) (Q (K a (e j)))‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ j, ‖rankOne ℂ (Q (K a (e j))) (Q (K a (e j)))‖ := by
      exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ ∑ _a : Fin M, ∑ _j : Fin m, δ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_rankOne, ← pow_two]
      apply pow_le_pow_left₀ (norm_nonneg _) _
      simpa only [Q, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        P] using hres a j
    _ = (M : ℝ) * m * δ ^ 2 := by simp [mul_assoc]

private theorem spectral_seed {D r : ℕ} (hr : 2 ≤ r) (hrD : r ≤ D)
    (B : Op D) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (t : ℝ) (ht : 0 ≤ t)
    (hst : t ≤ (ContinuousLinearMap.nonneg_iff_isPositive.mp hB0).isSymmetric.eigenvalues
      (show Module.finrank ℂ (H D) = D by simp [H])
      ⟨r - 1, by omega⟩) :
    ∃ (q : ℕ), r ≤ q ∧ q ≤ D ∧ ∃ η : Fin q → H D,
      Orthonormal ℂ η ∧
      (∀ b, t • rankOne ℂ (η b) (η b) ≤ B) ∧
      ∀ W : Submodule ℂ (H D), (∀ b, η b ∈ W) →
        B ≤ W.starProjection + t • (1 : Op D) := by
  classical
  let hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hB0
  let hsym := hpos.isSymmetric
  let hn : Module.finrank ℂ (H D) = D := by simp [H]
  let b := hsym.eigenvectorBasis hn
  let lam := hsym.eigenvalues hn
  have hlam0 (i : Fin D) : 0 ≤ lam i := hpos.toLinearMap.nonneg_eigenvalues hn i
  have hlam1 (i : Fin D) : lam i ≤ 1 := by
    have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hB1)).re_inner_nonneg_right (b i)
    have hei : B (b i) = (lam i : ℂ) • b i := hsym.apply_eigenvectorBasis hn i
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hei,
      inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one i, one_pow, Complex.ofReal_one,
      mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hh
    norm_num at hh
    linarith
  have hBsum : B = ∑ i : Fin D, (lam i) • rankOne ℂ (b i) (b i) := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := b.sum_repr' (B x)
    rw [← hx]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rankOne_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have he := hsym.eigenvectorBasis_apply_self_apply hn x i
    simp only [OrthonormalBasis.repr_apply_apply] at he
    change inner ℂ (b i) (B x) = (lam i : ℂ) * inner ℂ (b i) x at he
    rw [he, mul_smul]
    simp only [Complex.coe_smul]
  let S : Finset (Fin D) := Finset.univ.filter fun i => t ≤ lam i
  let q := S.card
  let f : Fin q ≃ S := (Fintype.equivFinOfCardEq (by simp [q])).symm
  let η : Fin q → H D := fun i => b (f i).val
  have hη : Orthonormal ℂ η :=
    b.orthonormal.comp (fun i => (f i).val) (Subtype.val_injective.comp f.injective)
  have hηsum : ∑ i : Fin q, rankOne ℂ (η i) (η i) = ∑ i ∈ S, rankOne ℂ (b i) (b i) := by
    calc
      _ = ∑ i : S, rankOne ℂ (b i.val) (b i.val) := Equiv.sum_comp f _
      _ = _ := Finset.sum_coe_sort S (fun i : Fin D => rankOne ℂ (b i) (b i))
  have hrq : r ≤ q := by
    let g : Fin r → S := fun i => ⟨Fin.castLE hrD i, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply hst.trans
      apply hsym.eigenvalues_antitone hn
      show (i : ℕ) ≤ r - 1
      omega⟩
    have hg : Function.Injective g := by
      intro i j hij
      have hval := congrArg (fun a : S => (a.val : ℕ)) hij
      exact Fin.ext hval
    have hh := Fintype.card_le_of_injective g hg
    simpa [q] using hh
  have hqD : q ≤ D := by simpa [q] using Finset.card_le_univ S
  refine ⟨q, hrq, hqD, η, hη, ?_, ?_⟩
  · intro i
    have hmem := (Finset.mem_filter.mp (f i).property).2
    calc
      t • rankOne ℂ (η i) (η i) ≤ lam (f i).val • rankOne ℂ (η i) (η i) :=
        smul_le_smul_of_nonneg_right hmem
          (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self _))
      _ ≤ B := by
        rw [hBsum]
        exact Finset.single_le_sum (fun j _ => smul_nonneg (hlam0 j)
          (show (0 : Op D) ≤ rankOne ℂ (b j) (b j) from
            ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self (b j))))
          (Finset.mem_univ (f i).val)
  · intro W hW
    let P₀ := (Submodule.span ℂ (Set.range η)).starProjection
    have hle : P₀ ≤ W.starProjection := by
      apply (isStarProjection_starProjection.le_iff_mul_eq_right isStarProjection_starProjection).mpr
      apply ContinuousLinearMap.ext
      intro x
      apply Submodule.starProjection_eq_self_iff.mpr
      apply Submodule.span_le.mpr (Set.forall_mem_range.mpr hW)
      exact Submodule.starProjection_apply_mem _ x
    have hBcut : B ≤ P₀ + t • (1 : Op D) := by
      rw [hBsum, show P₀ = ∑ i : Fin q, rankOne ℂ (η i) (η i) from projection_sum η hη,
        hηsum, show (1 : Op D) = ∑ i, rankOne ℂ (b i) (b i) from b.sum_rankOne_eq_id.symm]
      have hh : ∑ i ∈ S, rankOne ℂ (b i) (b i) =
          ∑ i : Fin D, (if i ∈ S then (1 : ℝ) else 0) • rankOne ℂ (b i) (b i) := by
        simp [Finset.sum_filter]
      rw [hh, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      rw [← add_smul]
      apply smul_le_smul_of_nonneg_right _
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self _))
      by_cases hmem : i ∈ S
      · simp only [hmem, ite_true]
        linarith [hlam1 i]
      · simp only [hmem, ite_false, zero_add]
        have hh : ¬ t ≤ lam i := by simpa [S] using hmem
        exact (lt_of_not_ge hh).le
    exact hBcut.trans (add_le_add hle (le_refl (t • (1 : Op D))))

private theorem expansion_mass {D M r m L : ℕ}
    (A : Fin M → Module.End ℂ (H D)) (η : Fin r → H D)
    (e : Fin m → H D) (G : H D →L[ℂ] H D)
    (c : Fin m → (List (Fin M) × Fin r →₀ ℂ))
    (hshort : ∀ j p, p ∈ (c j).support → p.1.length ≤ L)
    (hexp : ∀ j, e j = (c j).sum fun p z => z • (p.1.reverse.map A).prod (η p.2))
    (C u : ℝ) (hu : 0 ≤ u) (hC : 0 ≤ C)
    (hmass : ∀ j, (c j).sum (fun _ z => ‖z‖) ≤ C)
    (hword : ∀ (w : List (Fin M)) (b : Fin r), w.length ≤ L → ‖G ((w.reverse.map A).prod (η b))‖ ≤ u) :
    ∑ j, ‖G (e j)‖ ^ 2 ≤ (m : ℝ) * (C * u) ^ 2 := by
  classical
  have hj (j : Fin m) : ‖G (e j)‖ ≤ C * u := by
    rw [hexp j, map_finsuppSum]
    simp only [map_smul]
    calc
      _ ≤ (c j).sum (fun p z => ‖z • G ((p.1.reverse.map A).prod (η p.2))‖) :=
        norm_sum_le _ _
      _ ≤ (c j).sum (fun _ z => ‖z‖ * u) := by
        apply Finset.sum_le_sum
        intro p hp
        dsimp only
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hword _ _ (hshort j p hp)) (norm_nonneg _)
      _ = (c j).sum (fun _ z => ‖z‖) * u := by simp [Finsupp.sum, Finset.sum_mul]
      _ ≤ C * u := mul_le_mul_of_nonneg_right (hmass j) hu
  calc
    _ ≤ ∑ _j : Fin m, (C * u) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj'
      exact pow_le_pow_left₀ (norm_nonneg _) (hj j) _
    _ = _ := by simp

private theorem projection_observation {D m : ℕ}
    (σ : Mat D) (hσ : 0 ≤ σ) (e : Fin m → H D) (he : Orthonormal ℂ e) :
    (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * (opEquiv D).symm
      ((Submodule.span ℂ (Set.range e)).starProjection)))).re =
      ∑ j, ‖CFC.sqrt (opEquiv D σ) (e j)‖ ^ 2 := by
  rw [← trace_op, map_mul, StarAlgEquiv.apply_symm_apply, projection_sum e he,
    Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ContinuousLinearMap.mul_def, comp_rankOne, trace_rankOne,
    sqrt_quadratic σ hσ]

end D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon

namespace D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon

theorem detector_rank_horizon
    (D r n : ℕ) (hD : 2 ≤ D) (hr : 2 ≤ r) (hrD : r ≤ D) (hn : 1 ≤ n)
    (T : CompletelyPositiveMap (CStarMatrix (Fin D) (Fin D) ℂ) (CStarMatrix (Fin D) (Fin D) ℂ)) (hT : T 1 ≤ 1)
    (B σ : CStarMatrix (Fin D) (Fin D) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hσ : 0 ≤ σ) (hσtr : Matrix.trace (CStarMatrix.ofMatrix.symm σ) = 1)
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 < p) (hp1 : p ≤ 1)
    (hearly : ∀ k : ℕ, k ≤ D - r →
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[k] B))).re ≤ ε)
    (hlate : p ≤ (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[n] B))).re) :
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hB0)).isHermitian.eigenvalues₀
        ⟨r - 1, by simpa using (show r - 1 < D by omega)⟩ ≤
      (8 * (D : ℝ) / p ^ 2) *
        (8 * (n : ℝ) * (D : ℝ) ^ (5 / 2 : ℝ) / p) ^ (2 * (D - r)) * ε := by
  classical
  let E := opEquiv D
  let Bop := E B
  have hBop0 : 0 ≤ Bop := map_nonneg E hB0
  have hBop1 : Bop ≤ 1 := by simpa using OrderHomClass.mono E hB1
  let hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hBop0
  let hsym := hpos.isSymmetric
  let hd : Module.finrank ℂ (H D) = D := by simp [H]
  let j : Fin D := ⟨r - 1, by omega⟩
  let s := hsym.eigenvalues hd j
  have heig (N : ℕ) (hND : N = D) (hN : Module.finrank ℂ (H D) = N) (i : Fin N) :
      hsym.eigenvalues hN i = hsym.eigenvalues hd (Fin.cast hND i) := by
    subst N
    rfl
  unfold Matrix.IsHermitian.eigenvalues₀
  change hsym.eigenvalues (show Module.finrank ℂ (H D) = Fintype.card (Fin D) from
    finrank_euclideanSpace) ⟨r - 1, by simpa using (show r - 1 < D by omega)⟩ ≤ _
  rw [heig _ (Fintype.card_fin D)]
  change s ≤ _
  have hs0 : 0 ≤ s := hpos.toLinearMap.nonneg_eigenvalues hd j
  have hconst : 0 ≤ (8 * (D : ℝ) / p ^ 2) *
        (8 * (n : ℝ) * (D : ℝ) ^ (5 / 2 : ℝ) / p) ^ (2 * (D - r)) * ε := by positivity
  by_cases hs : 0 < s
  swap
  · exact (le_of_not_gt hs).trans hconst
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hs1 : s ≤ 1 := by
    have hq := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hBop1)).re_inner_nonneg_right
      (hsym.eigenvectorBasis hd j)
    have hei : Bop (hsym.eigenvectorBasis hd j) = (s : ℂ) • hsym.eigenvectorBasis hd j :=
      hsym.apply_eigenvectorBasis hd j
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hei,
      inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      (hsym.eigenvectorBasis hd).orthonormal.norm_eq_one j, one_pow,
      Complex.ofReal_one, mul_one, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hq
    norm_num at hq
    linarith
  let t := p * s / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hts : t ≤ s := by dsimp [t]; nlinarith
  have htp : t ≤ p / 4 := by dsimp [t]; nlinarith
  let dhalf := (D : ℝ) * Real.sqrt D
  have hdhalf : 0 < dhalf := by dsimp [dhalf]; positivity
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt D := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ D by linarith)
  have hhalf1 : 1 ≤ dhalf := by dsimp [dhalf]; nlinarith
  let δ := p / (8 * (n : ℝ) * dhalf)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by
    dsimp [δ]
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  let C := ((D : ℝ) / δ) ^ (D - r)
  have hratio : 1 ≤ (D : ℝ) / δ := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨K, hK⟩ := kraus_operator_action T
  have hA := kraus_contractions T hT K hK
  let F : Op D →ₗ[ℂ] Op D := E.toAlgEquiv.toLinearMap.comp
    (T.toLinearMap.comp E.symm.toAlgEquiv.toLinearMap)
  have hF (Y : Op D) : F Y = E (T (E.symm Y)) := rfl
  have hFK (Y : Op D) : F Y = ∑ a, K a * Y * star (K a) := hK Y
  have hFmono : Monotone F := fun X Y hXY =>
    OrderHomClass.mono E (OrderHomClass.mono T (OrderHomClass.mono E.symm hXY))
  have hiter (k : ℕ) (X : Mat D) : F^[k] (E X) = E (T^[k] X) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hF,
        StarAlgEquiv.symm_apply_apply]
  obtain ⟨q, hrq, hqD, η, hη, hηB, hcut⟩ := spectral_seed hr hrD Bop hBop0 hBop1 t ht.le hts
  let A : Fin (D ^ 2) → Module.End ℂ (H D) := fun a => (K a).toLinearMap
  obtain ⟨m, hqm, hmD, e, he, heη, hres, c, hshort, hexp, hmass⟩ :=
    D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension.quantitative_word_orthonormal_extension
      D q (D ^ 2) (hr.trans hrq) hqD le_rfl δ hδ hδ1 A hA η hη
  let W := Submodule.span ℂ (Set.range e)
  let P := W.starProjection
  let Pm := E.symm P
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hPm : IsStarProjection Pm := hP.map E.symm
  have hηW (b : Fin q) : η b ∈ W := by
    rw [← heη b]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hcutP : Bop ≤ P + t • (1 : Op D) := hcut W hηW
  have hEreal (a : ℝ) (Y : Op D) : E.symm (a • Y) = a • E.symm Y :=
    E.symm.toAlgEquiv.toLinearMap.map_smul_of_tower a Y
  have hTreal (a : ℝ) (Y : Mat D) : T (a • Y) = a • T Y :=
    T.toLinearMap.map_smul_of_tower a Y
  have hXP : B - t • (1 : Mat D) ≤ Pm := by
    apply sub_le_iff_le_add.mpr
    simpa only [map_add, hEreal, map_one, StarAlgEquiv.symm_apply_apply, Bop,
      E, Pm] using OrderHomClass.mono E.symm hcutP
  have hwordEnd (w : List (Fin (D ^ 2))) (x : H D) :
      (w.reverse.map A).prod x = (w.reverse.map K).prod x := by
    have heq (l : List (Fin (D ^ 2))) :
        (l.map A).prod = ((l.map K).prod).toLinearMap := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons, ih]
        rfl
    rw [heq]
    rfl
  let G := CFC.sqrt (E σ)
  let u := Real.sqrt (ε / t)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hword (w : List (Fin (D ^ 2))) (b : Fin q) (hw : w.length ≤ D - r) :
      ‖G ((w.reverse.map A).prod (η b))‖ ≤ u := by
    rw [hwordEnd]
    have hd := word_domination F hFmono K hFK Bop t ht.le η hηB w b
    rw [hiter] at hd
    have hm := OrderHomClass.mono E.symm hd
    simp only [StarAlgEquiv.symm_apply_apply] at hm
    have ho := (trace_mono σ hσ hm).trans (hearly w.length hw)
    have heq : (Matrix.trace (CStarMatrix.ofMatrix.symm
        (σ * E.symm (t • rankOne ℂ ((w.reverse.map K).prod (η b))
          ((w.reverse.map K).prod (η b)))))).re =
        t * ‖G ((w.reverse.map K).prod (η b))‖ ^ 2 := by
      rw [hEreal]
      change (Matrix.trace (CStarMatrix.ofMatrix.symm σ *
        t • CStarMatrix.ofMatrix.symm (E.symm (rankOne ℂ _ _)))).re = _
      rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      change t * (Matrix.trace (CStarMatrix.ofMatrix.symm
        (σ * E.symm (rankOne ℂ ((w.reverse.map K).prod (η b))
          ((w.reverse.map K).prod (η b)))))).re = _
      rw [trace_rank, ← sqrt_quadratic σ hσ]
    rw [heq] at ho
    apply (sq_le_sq₀ (norm_nonneg _) hu).mp
    change _ ≤ Real.sqrt (ε / t) ^ 2
    rw [Real.sq_sqrt (div_nonneg hε ht.le)]
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hcoeff (j : Fin m) : (c j).sum (fun _ z => ‖z‖) ≤ C :=
    (hmass j).trans (pow_le_pow_right₀ hratio (by omega))
  have hmassP : (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * Pm))).re ≤
      (D : ℝ) * C ^ 2 * ε / t := by
    rw [projection_observation σ hσ e he]
    have hm := expansion_mass A η e G c (fun j p hp => (hshort j p hp).trans (by omega))
      hexp C u hu hC hcoeff hword
    calc
      _ ≤ (m : ℝ) * (C * u) ^ 2 := hm
      _ ≤ (D : ℝ) * (C * u) ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hmD) (sq_nonneg _)
      _ = (D : ℝ) * C ^ 2 * ε / t := by
        rw [mul_pow, show u ^ 2 = ε / t from Real.sq_sqrt (div_nonneg hε ht.le)]
        ring
  have hcornerOp : ‖(1 - P) * F P * (1 - P)‖ ≤ (D : ℝ) ^ 3 * δ ^ 2 := by
    have hc := corner_bound F K hFK e he δ hδ.le hres
    exact hc.trans (by
      have hmDr : (m : ℝ) ≤ D := by exact_mod_cast hmD
      push_cast
      nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg (D : ℝ)) (sq_nonneg δ)])
  have hcorner : ‖(1 - Pm) * T Pm * (1 - Pm)‖ ≤ (D : ℝ) ^ 3 * δ ^ 2 := by
    rw [← NonUnitalStarAlgHom.norm_map E E.injective]
    simpa only [map_mul, map_sub, map_one, StarAlgEquiv.apply_symm_apply, Pm,
      ← hF] using hcornerOp
  let α := Real.sqrt ‖(1 - Pm) * T Pm * (1 - Pm)‖
  have hα : α ≤ p / (8 * (n : ℝ)) := by
    have hhalf : dhalf ^ 2 = (D : ℝ) ^ 3 := by
      dsimp [dhalf]
      rw [mul_pow, Real.sq_sqrt hDpos.le]
      ring
    have hprod : dhalf * δ = p / (8 * (n : ℝ)) := by
      dsimp [δ]
      field_simp
    rw [← hprod]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hdhalf.le hδ.le)).mp
    rw [Real.sq_sqrt (norm_nonneg _), mul_pow, hhalf]
    exact hcorner
  have ht1 (k : ℕ) : T^[k] (1 : Mat D) ≤ 1 := by
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (OrderHomClass.mono T ih).trans hT
  have hsub (k : ℕ) : T^[k] (B - t • (1 : Mat D)) =
      T^[k] B - t • T^[k] (1 : Mat D) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, map_sub, hTreal]
  have hord : T^[n] B ≤ T^[n] (B - t • (1 : Mat D)) + t • (1 : Mat D) := by
    calc
      _ = T^[n] (B - t • (1 : Mat D)) + t • T^[n] (1 : Mat D) := by rw [hsub]; abel
      _ ≤ _ := add_le_add le_rfl (smul_le_smul_of_nonneg_left (ht1 n) ht.le)
  have htraceAdd (X : Mat D) :
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * (X + t • (1 : Mat D))))).re =
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * X))).re + t := by
    change (Matrix.trace (CStarMatrix.ofMatrix.symm σ *
      (CStarMatrix.ofMatrix.symm X + t • (1 : Matrix (Fin D) (Fin D) ℂ)))).re = _
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
      Matrix.trace_smul, hσtr]
    simp
    rfl
  have hcoh := (D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon.coherent_compression_trace_transfer
    T hT Pm (B - t • (1 : Mat D)) σ hPm hXP hσ hσtr n).2
  have hprob : p ≤ (D : ℝ) * C ^ 2 * ε / t + 2 * (n : ℝ) * α + t := by
    have hh := (trace_mono σ hσ hord)
    rw [htraceAdd] at hh
    exact hlate.trans (hh.trans (add_le_add
      (hcoh.trans (add_le_add hmassP le_rfl)) le_rfl))
  have hαn : 2 * (n : ℝ) * α ≤ p / 4 := by
    have hh := mul_le_mul_of_nonneg_left hα (show 0 ≤ 2 * (n : ℝ) by positivity)
    have heq : 2 * (n : ℝ) * (p / (8 * (n : ℝ))) = p / 4 := by field_simp; ring
    rwa [heq] at hh
  have hmid : p / 2 ≤ (D : ℝ) * C ^ 2 * ε / t := by linarith
  have hmul := (le_div_iff₀ ht).mp hmid
  have hsbound : s ≤ (8 * (D : ℝ) * C ^ 2 * ε) / p ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    dsimp [t] at hmul
    nlinarith
  have hrpow : (D : ℝ) ^ (5 / 2 : ℝ) = (D : ℝ) ^ 2 * Real.sqrt D := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hDpos]
    simp [Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hbase : (D : ℝ) / δ = 8 * (n : ℝ) * (D : ℝ) ^ (5 / 2 : ℝ) / p := by
    rw [hrpow]
    dsimp [δ, dhalf]
    field_simp
  calc
    s ≤ (8 * (D : ℝ) * C ^ 2 * ε) / p ^ 2 := hsbound
    _ = _ := by
      dsimp [C]
      rw [hbase, ← pow_mul]
      congr 2 <;> ring

end D5.S3.Quantum.QuantumChannels.OriginalDataQuantitativeDetectorRankHorizon
