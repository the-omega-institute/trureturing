/- GID: D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Fermionic Gaussian Renyi strong subadditivity for orders between zero and one. -/

import D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
import D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
import D5.S3.Quantum.Subentropy.DensityKernel

/-! Strong subadditivity from a positive mixture of principal log determinants. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped ComplexOrder
open D5.S3.Quantum.Analysis.FermionicRenyiStieltjes
open D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity (reducedCovariance)

namespace D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity

/-- Real Majorana covariance with Hermitian spectrum in `[-1, 1]`. -/
def physicalCovariance {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Prop :=
  Gᵀ = -G ∧ ∃ h : (Complex.I • G.map Complex.ofReal).IsHermitian,
    ∀ i, |h.eigenvalues i| ≤ 1

/-- The source entropy: half the sum over the complete Majorana spectrum. -/
def fermionicGaussianRenyiEntropy {n : ℕ} {X : Finset (Fin n)} (α : ℝ)
    (G : Matrix {p : Fin n × Fin 2 // p.1 ∈ X}
      {p : Fin n × Fin 2 // p.1 ∈ X} ℝ) : ℝ :=
  if h : (Complex.I • G.map Complex.ofReal).IsHermitian then
    (1 / 2 : ℝ) * ∑ i, fermionicRenyiFunction α (h.eigenvalues i)
  else 0

def claim : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance G → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α < 1 →
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B)) +
            fermionicGaussianRenyiEntropy α (reducedCovariance G (B ∪ C)) ≥
          fermionicGaussianRenyiEntropy α (reducedCovariance G (A ∪ B ∪ C)) +
            fermionicGaussianRenyiEntropy α (reducedCovariance G B)

private def interpolation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (u : ℝ) : Matrix ι ι ℂ :=
  1 + (u : ℂ) • (Complex.I • G.map Complex.ofReal)

private lemma skew_hermitian {ι : Type*}
    (G : Matrix ι ι ℝ) (hG : Gᵀ = -G) :
    (Complex.I • G.map Complex.ofReal).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  apply isSelfAdjoint_smul_of_mem_skewAdjoint
  · simp only [skewAdjoint.mem_iff, Complex.star_def, Complex.conj_I]
  · rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
      ← Matrix.conjTranspose_map Complex.ofReal
        (by intro x; simp only [star_trivial, Complex.star_def, Complex.conj_ofReal]),
      Matrix.conjTranspose_eq_transpose_of_trivial,
      hG, Matrix.map_neg _ Complex.ofReal_neg]

private lemma interpolation_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (h : (Complex.I • G.map Complex.ofReal).IsHermitian) (u : ℝ) :
    interpolation G u = Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((1 + u * h.eigenvalues i : ℝ) : ℂ))) := by
  have hd : Matrix.diagonal (fun i => ((1 + u * h.eigenvalues i : ℝ) : ℂ)) =
      1 + (u : ℂ) • Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext i
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
      RCLike.ofReal_eq_complex_ofReal]
  rw [hd, map_add, map_one, map_smul, ← h.spectral_theorem]
  rfl

private lemma interpolation_nonneg_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (h : (Complex.I • G.map Complex.ofReal).IsHermitian) (u : ℝ) :
    (interpolation G u).PosSemidef ↔ ∀ i, 0 ≤ 1 + u * h.eigenvalues i := by
  rw [interpolation_diagonal G h u, Unitary.conjStarAlgAut_apply,
    Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff,
    Matrix.posSemidef_diagonal_iff]
  simp (config := { congrConsts := false }) only [Complex.zero_le_real]

private lemma interpolation_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (G : Matrix ι ι ℝ) (f : κ → ι)
    (hf : Function.Injective f) (u : ℝ) :
    (interpolation G u).submatrix f f = interpolation (G.submatrix f f) u := by
  change (1 : Matrix ι ι ℂ).submatrix f f +
      (u : ℂ) • (Complex.I • (G.map Complex.ofReal).submatrix f f) = _
  rw [Matrix.submatrix_one f hf]
  rfl

private lemma interpolation_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (h : (Complex.I • G.map Complex.ofReal).IsHermitian)
    (hb : ∀ i, |h.eigenvalues i| ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (interpolation G u).PosDef := by
  have hfull : D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.physicalOn
      (1 : Matrix ι ι ℝ) G := by
    refine ⟨Matrix.isSymm_one, ?_⟩
    rw [Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
    simpa only [interpolation, Complex.ofReal_one, one_smul] using
      (interpolation_nonneg_iff G h 1).mpr (fun i => by
        have hi := (abs_le.mp (hb i)).1
        simpa only [one_mul] using (show 0 ≤ 1 + h.eigenvalues i by linarith))
  simpa only [interpolation, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one] using
    D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.shifted_posDef
      (1 : Matrix ι ι ℝ) G hfull
      (by simpa only [Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one] using
        (Matrix.PosDef.one : (1 : Matrix ι ι ℂ).PosDef)) hu0 hu1

private lemma reduced_physical {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hG : physicalCovariance G)
    (X : Finset (Fin n)) :
    (reducedCovariance G X)ᵀ = -(reducedCovariance G X) ∧
      ∃ h : (Complex.I • (reducedCovariance G X).map Complex.ofReal).IsHermitian,
        ∀ i, |h.eigenvalues i| ≤ 1 := by
  have hs : (reducedCovariance G X)ᵀ = -(reducedCovariance G X) := by
    change (G.submatrix Subtype.val Subtype.val)ᵀ = -(G.submatrix Subtype.val Subtype.val)
    rw [Matrix.transpose_submatrix, hG.1]
    rfl
  refine ⟨hs, skew_hermitian _ hs, ?_⟩
  obtain ⟨h, hb⟩ := hG.2
  have hp (u : ℝ) (hu : u = 1 ∨ u = -1) :
      (interpolation (reducedCovariance G X) u).PosSemidef := by
    have hfull : (interpolation G u).PosSemidef :=
      (interpolation_nonneg_iff G h u).mpr (fun i => by
        have hi := abs_le.mp (hb i)
        rcases hu with rfl | rfl <;> linarith [hi.1, hi.2])
    have hr := hfull.submatrix
      (Subtype.val : {p : Fin n × Fin 2 // p.1 ∈ X} → Fin n × Fin 2)
    rw [interpolation_submatrix G _ Subtype.val_injective] at hr
    exact hr
  intro i
  have hp1 := (interpolation_nonneg_iff _ (skew_hermitian _ hs) 1).mp
    (hp 1 (Or.inl rfl)) i
  have hm1 := (interpolation_nonneg_iff _ (skew_hermitian _ hs) (-1)).mp
    (hp (-1) (Or.inr rfl)) i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma determinant_log_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : Gᵀ = -G)
    (h : (Complex.I • G.map Complex.ofReal).IsHermitian)
    (hb : ∀ i, |h.eigenvalues i| ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (interpolation G u).det.re =
      (1 / 2 : ℝ) * ∑ i, Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2) := by
  have hd (t : ℝ) : (interpolation G t).det =
      ∏ i, ((1 + t * h.eigenvalues i : ℝ) : ℂ) :=
    D5.S3.Quantum.Subentropy.DensityKernel.det_spectral h t
  have ht : (interpolation G u)ᵀ = interpolation G (-u) := by
    change (1 + (u : ℂ) • (Complex.I • G.map Complex.ofReal))ᵀ =
      1 + ((-u : ℝ) : ℂ) • (Complex.I • G.map Complex.ofReal)
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_smul, ← Matrix.transpose_map, hG,
      Matrix.map_neg _ Complex.ofReal_neg, smul_neg, smul_neg,
      Complex.ofReal_neg, neg_smul]
  have hdt : (interpolation G (-u)).det = (interpolation G u).det := by
    rw [← ht, Matrix.det_transpose]
  have hp : (∏ i, ((1 - u ^ 2 * h.eigenvalues i ^ 2 : ℝ) : ℂ)) =
      (interpolation G u).det ^ 2 := by
    calc
      _ = (∏ i, ((1 + u * h.eigenvalues i : ℝ) : ℂ)) *
          (∏ i, ((1 + (-u) * h.eigenvalues i : ℝ) : ℂ)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        push_cast
        ring
      _ = _ := by rw [← hd u, ← hd (-u), hdt, pow_two]
  have hpos := interpolation_posDef G h hb hu0 hu1
  have hdr : ((interpolation G u).det.re : ℂ) = (interpolation G u).det := by
    apply Complex.ext
    · rfl
    · simpa (config := { congrConsts := false }) only
        [Complex.ofReal_im, Complex.zero_im] using hpos.det_pos.2
  rw [← hdr, ← Complex.ofReal_pow, ← Complex.ofReal_prod] at hp
  have hr := Complex.ofReal_injective hp
  have hterms (i : ι) : 0 < 1 - u ^ 2 * h.eigenvalues i ^ 2 := by
    have hsq : (u * h.eigenvalues i) ^ 2 < 1 :=
      (sq_lt_one_iff_abs_lt_one _).mpr (by
        rw [abs_mul, abs_of_nonneg hu0]
        exact lt_of_le_of_lt (mul_le_of_le_one_right hu0 (hb i)) hu1)
    simpa only [mul_pow] using sub_pos.mpr hsq
  have hl := congrArg Real.log hr
  rw [Real.log_prod (fun i _ => (hterms i).ne'), Real.log_pow] at hl
  generalize hx : Real.log (interpolation G u).det.re = x at hl ⊢
  generalize hy : (∑ i, Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2)) = y at hl ⊢
  norm_num (config := { congrConsts := false }) at hl
  linarith only [hl]

private lemma entropy_mixture {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hG : physicalCovariance G)
    (X : Finset (Fin n)) {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    IntegrableOn (fun u : ℝ => fermionicWeight α u *
      Real.log (interpolation (reducedCovariance G X) u).det.re) (Ioo 0 1) ∧
    fermionicGaussianRenyiEntropy α (reducedCovariance G X) =
      (X.card : ℝ) * Real.log 2 + ∫ u in Ioo (0 : ℝ) 1,
        fermionicWeight α u * Real.log (interpolation (reducedCovariance G X) u).det.re := by
  obtain ⟨hskew, h, hb⟩ := reduced_physical G hG X
  have hs (i : {p : Fin n × Fin 2 // p.1 ∈ X}) :=
    stieltjes_representation ha0 ha1 (hb i)
  have heq (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      fermionicWeight α u * Real.log (interpolation (reducedCovariance G X) u).det.re =
        (1 / 2 : ℝ) * ∑ i, fermionicWeight α u *
          Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2) := by
    rw [determinant_log_identity _ hskew h hb hu.1.le hu.2, ← Finset.mul_sum]
    ring
  have hi := (integrable_finsetSum Finset.univ (fun i _ => (hs i).1)).const_mul
    (1 / 2 : ℝ)
  constructor
  · exact IntegrableOn.congr_fun hi (fun u hu => (heq u hu).symm) measurableSet_Ioo
  · have hint : (∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u *
          Real.log (interpolation (reducedCovariance G X) u).det.re) =
        (1 / 2 : ℝ) * ∑ i, ∫ u in Ioo (0 : ℝ) 1,
          fermionicWeight α u * Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2) := by
      rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ => (hs i).1)]
    have hsum : (∑ i, fermionicRenyiFunction α (h.eigenvalues i)) =
        (Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} : ℝ) * Real.log 2 +
          ∑ i, ∫ u in Ioo (0 : ℝ) 1,
            fermionicWeight α u * Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2) := by
      calc
        _ = ∑ i, (Real.log 2 + ∫ u in Ioo (0 : ℝ) 1,
            fermionicWeight α u * Real.log (1 - u ^ 2 * h.eigenvalues i ^ 2)) := by
          exact Finset.sum_congr rfl (fun i _ => (hs i).2)
        _ = _ := by rw [Finset.sum_add_distrib]; simp (config := { congrConsts := false })
    have hcard : Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} = 2 * X.card := by
      exact D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reduced_card X
    rw [fermionicGaussianRenyiEntropy, dite_eq_left h, hsum, hint, hcard]
    push_cast
    ring

private lemma mode_interpolation_det {n : ℕ}
    (G : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (Y : Finset (Fin n × Fin 2)) (X : Finset (Fin n))
    (hYX : ∀ p, p ∈ Y ↔ p.1 ∈ X) (u : ℝ) :
    ((interpolation G u).submatrix
      (Subtype.val : ↥Y → Fin n × Fin 2) Subtype.val).det =
      (interpolation (reducedCovariance G X) u).det := by
  simpa only [interpolation, reducedCovariance,
    Matrix.submatrix_one _ Subtype.val_injective,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one] using
    D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.mode_interpolation_det
      (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) G Y X hYX u

private lemma settlement_main : claim := by
  intro n G hG A B C hAB hAC hBC α ha0 ha1
  let L := fun (X : Finset (Fin n)) (u : ℝ) =>
    Real.log (interpolation (reducedCovariance G X) u).det.re
  have hm (X : Finset (Fin n)) :
      IntegrableOn (fun u => fermionicWeight α u * L X u) (Ioo (0 : ℝ) 1) ∧
      fermionicGaussianRenyiEntropy α (reducedCovariance G X) =
        (X.card : ℝ) * Real.log 2 +
          ∫ u in Ioo (0 : ℝ) 1, fermionicWeight α u * L X u :=
    entropy_mixture G hG X ha0 ha1
  have hk (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
      L (A ∪ B ∪ C) u + L B u ≤ L (A ∪ B) u + L (B ∪ C) u := by
    obtain ⟨h, hb⟩ := hG.2
    have hk := D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.log_koteljanskii
      (interpolation G u) (interpolation_posDef G h hb hu0 hu1)
      (A ×ˢ (Finset.univ : Finset (Fin 2))) (B ×ˢ Finset.univ) (C ×ˢ Finset.univ)
      (Finset.disjoint_product.mpr (Or.inl hAB))
      (Finset.disjoint_product.mpr (Or.inl hAC))
      (Finset.disjoint_product.mpr (Or.inl hBC))
    rw [mode_interpolation_det G _ (A ∪ B ∪ C)
        (fun p => by
          simp (config := { congrConsts := false }) only
            [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ B
        (fun p => by
          simp (config := { congrConsts := false }) only
            [Finset.mem_product, Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ (A ∪ B)
        (fun p => by
          simp (config := { congrConsts := false }) only
            [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) u,
      mode_interpolation_det G _ (B ∪ C)
        (fun p => by
          simp (config := { congrConsts := false }) only
            [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) u] at hk
    exact hk
  have hpoint : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      fermionicWeight α u * L (A ∪ B ∪ C) u + fermionicWeight α u * L B u ≤
        fermionicWeight α u * L (A ∪ B) u + fermionicWeight α u * L (B ∪ C) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa (config := { congrConsts := false }) only [mul_add] using
      mul_le_mul_of_nonneg_left (hk u hu.1.le hu.2) (weight_pos ha0 ha1 hu.1.le hu.2).le
  have hi := integral_mono_ae ((hm (A ∪ B ∪ C)).1.add (hm B).1)
    ((hm (A ∪ B)).1.add (hm (B ∪ C)).1) hpoint
  simp (config := { congrConsts := false }) only [Pi.add_apply] at hi
  rw [integral_add (hm (A ∪ B ∪ C)).1 (hm B).1,
    integral_add (hm (A ∪ B)).1 (hm (B ∪ C)).1] at hi
  have hc : (A ∪ B).card + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
    simpa only [Finset.inter_union_distrib_left, Finset.union_inter_distrib_right,
      Finset.disjoint_iff_inter_eq_empty.mp hAB,
      Finset.disjoint_iff_inter_eq_empty.mp hAC,
      Finset.disjoint_iff_inter_eq_empty.mp hBC,
      Finset.inter_self, Finset.empty_union, Finset.union_empty,
      Finset.union_assoc, Finset.union_left_idem] using
        (Finset.card_union_add_card_inter (A ∪ B) (B ∪ C)).symm
  have hcr : ((A ∪ B).card : ℝ) + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
    exact_mod_cast hc
  have hconst := congrArg (fun t : ℝ => t * Real.log 2) hcr
  rw [(hm (A ∪ B)).2, (hm (B ∪ C)).2, (hm (A ∪ B ∪ C)).2, (hm B).2]
  linarith only [hi, hconst]

theorem result : claim := settlement_main

end D5.S3.Quantum.Fermionic.GaussianRenyiStrongSubadditivity
