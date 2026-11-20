/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldCriticalMatterModeBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldCriticalMatterModeBPZ
   mirror-E: none(waiver:algebraic-original-critical-matter-bpz)
   anchors: []
   utility: none
   digest: Finite BPZ mode transposition for the original Leech orbifold tensor hyperbolic lattice. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTTensorBPZ
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

/-! Reflected coefficients of the native tensor field pair against the native
matter form. The hyperbolic descendant cutoff is computed from the oscillator
polynomials on the finite charge support of the inserted state. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldCriticalMatterModeBPZ

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldMatterTensorField (stateField stateField_tmul support_tmul)
open OriginalOrbifoldMatterBPZ (matterBPZ matterBPZ_tmul orbifoldBPZ hyperbolicBPZ)
open LatticePositiveEnergy (grade)
open LatticeSugawaraCurrents (gramComplex)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open MvPolynomial (weightedTotalDegree)
open StateField.BorcherdsPermutations
  (dividedTranslation lowerTruncated_modesOfStateField modesOfStateField)
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

open private reflect sum_antidiagonal_cutoffs from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTTensorBPZ

local notation "YO" => orbifoldVertexAlgebra.stateField
local notation "YH" => LatticeAllStateField.Y hyperbolicData
local notation "DO" => dividedTranslation (orbifoldMode 1)
local notation "DH" => dividedTranslation (hyperbolicMode 1)
local notation "DM" => dividedTranslation (mode 1)

private theorem hyperbolic_det_unit : IsUnit hyperbolicData.G.det := by
  have hdet : hyperbolicData.G.det = -1 := by
    calc
      hyperbolicData.G.det = OrderedHyperbolicExtension.U.det :=
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.det) hyperbolic_gram
      _ = -1 := by simp [OrderedHyperbolicExtension.U, Matrix.det_fin_two_of]
  rw [hdet]
  exact isUnit_neg_one

private theorem hyperbolic_gram_inv : (gramComplex hyperbolicData)⁻¹ = hyperbolicInverse :=
  Matrix.right_inv_eq_left_inv
    (Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit hyperbolicData hyperbolic_det_unit))
    hyperbolic_inverse_left

/-- The oscillator-weight bound on the finite charge support, plus one. -/
def hyperbolicLoweringCutoff (b : Hyperbolic) : ℕ :=
  b.support.sup (fun α => weightedTotalDegree (sourceWeight hyperbolicData) (b α)) + 1

private theorem hyperbolic_lowering_tail (b : Hyperbolic) (s : ℕ)
    (hs : hyperbolicLoweringCutoff b ≤ s) : DH s b = 0 := by
  have hbound : (hyperbolicMode 1 ^ hyperbolicLoweringCutoff b) b = 0 := by
    have h := SourceMobius.actual_sugawara_one_bound hyperbolicData hyperbolic_det_unit b
    rw [hyperbolic_gram_inv] at h
    exact h
  have hpow : (hyperbolicMode 1 ^ s) b = 0 := by
    rw [show s = (s - hyperbolicLoweringCutoff b) + hyperbolicLoweringCutoff b by omega,
      pow_add, Module.End.mul_apply, hbound, map_zero]
  simp only [dividedTranslation, LinearMap.smul_apply, hpow, smul_zero]

/-- Divided powers of the native matter lowering mode split on pure tensors. -/
theorem divided_matter_L1_tmul (a : Orbifold) (b : Hyperbolic) (d : ℕ) :
    DM d (a ⊗ₜ[ℂ] b) =
      ∑ rs ∈ antidiagonal d, DO rs.1 a ⊗ₜ[ℂ] DH rs.2 b := by
  let ol := Module.End.rTensorAlgHom ℂ Orbifold Hyperbolic
  let hl := Module.End.lTensorAlgHom ℂ Hyperbolic Orbifold
  have hcomm : Commute (ol (orbifoldMode 1)) (hl (hyperbolicMode 1)) := by
    change (orbifoldMode 1).rTensor Hyperbolic * (hyperbolicMode 1).lTensor Orbifold =
      (hyperbolicMode 1).lTensor Orbifold * (orbifoldMode 1).rTensor Hyperbolic
    apply TensorProduct.ext'
    intro u x
    simp only [Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  change (((d.factorial : ℂ)⁻¹) • (ol (orbifoldMode 1) + hl (hyperbolicMode 1)) ^ d)
    (a ⊗ₜ[ℂ] b) = _
  rw [hcomm.add_pow', LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hd : rs.1 + rs.2 = d := mem_antidiagonal.mp hrs
  have hscalar :
      (d.factorial : ℂ)⁻¹ * (d.choose rs.1 : ℂ) =
        (rs.1.factorial : ℂ)⁻¹ * (rs.2.factorial : ℂ)⁻¹ := by
    rw [← hd, Nat.cast_add_choose]
    have hne (q : ℕ) : (q.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    field_simp [hne] <;> ring
  rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.smul_apply, smul_smul, hscalar,
    ← map_pow ol, ← map_pow hl, Module.End.mul_apply]
  simp only [dividedTranslation, LinearMap.smul_apply, TensorProduct.smul_tmul_smul] <;> rfl

private theorem tensorModes_finite (a u : Orbifold) (b x : Hyperbolic) (n : ℤ) :
    Function.HasFiniteSupport (fun j : ℤ =>
      ((YO a)[[j]]) u ⊗ₜ[ℂ] ((YH b)[[n - 1 - j]]) x) := by
  obtain ⟨A, hA⟩ := lowerTruncated_modesOfStateField YO a u
  obtain ⟨B, hB⟩ := lowerTruncated_modesOfStateField YH b x
  exact (Set.finite_Icc _ _).subset (support_tmul a u b x n A B hA hB)

private theorem matterBPZ_mode_tmul (a u v : Orbifold) (b x y : Hyperbolic) (n : ℤ) :
    matterBPZ (((stateField (a ⊗ₜ[ℂ] b))[[n]]) (u ⊗ₜ[ℂ] x)) (v ⊗ₜ[ℂ] y) =
      ∑ᶠ j : ℤ, orbifoldBPZ (((YO a)[[j]]) u) v *
        hyperbolicBPZ (((YH b)[[n - 1 - j]]) x) y := by
  let term : ℤ → Matter := fun j =>
    ((YO a)[[j]]) u ⊗ₜ[ℂ] ((YH b)[[n - 1 - j]]) x
  let form : Matter →ₗ[ℂ] ℂ := matterBPZ.flip (v ⊗ₜ[ℂ] y)
  rw [stateField_tmul]
  change form (∑ᶠ j : ℤ, term j) = _
  rw [map_finsum form (tensorModes_finite a u b x n)]
  exact finsum_congr (fun j => matterBPZ_tmul (((YO a)[[j]]) u) v
    (((YH b)[[n - 1 - j]]) x) y)

private def reflectedTerm (a u v : Orbifold) (b x y : Hyperbolic)
    (h k n : ℤ) (r s : ℕ) (j : ℤ) : ℂ :=
  orbifoldBPZ u (((YO (DO r a))[[2 * h - (r : ℤ) - j - 2]]) v) *
    hyperbolicBPZ x (((YH (DH s b))[[2 * k - (s : ℤ) - (n - 1 - j) - 2]]) y)

private theorem reflected_mode_pair (a u v : Orbifold) (b x y : Hyperbolic)
    (h k n : ℤ) (r s : ℕ) :
    Function.HasFiniteSupport (reflectedTerm a u v b x y h k n r s) ∧
      (∑ᶠ j : ℤ, reflectedTerm a u v b x y h k n r s j) =
        matterBPZ (u ⊗ₜ[ℂ] x)
          (((stateField (DO r a ⊗ₜ[ℂ] DH s b))[[2 * (h + k) - (r : ℤ) - (s : ℤ) - n - 2]])
            (v ⊗ₜ[ℂ] y)) := by
  let N : ℤ := 2 * (h + k) - (r : ℤ) - (s : ℤ) - n - 2
  let e := reflect (2 * h - (r : ℤ) - 2)
  let tensorTerm : ℤ → Matter := fun i =>
    ((YO (DO r a))[[i]]) v ⊗ₜ[ℂ] ((YH (DH s b))[[N - 1 - i]]) y
  let form := matterBPZ (u ⊗ₜ[ℂ] x)
  have hfinite : Function.HasFiniteSupport tensorTerm :=
    tensorModes_finite (DO r a) v (DH s b) y N
  have heq : reflectedTerm a u v b x y h k n r s = fun j => form (tensorTerm (e j)) := by
    funext j
    have hi : e j = 2 * h - (r : ℤ) - j - 2 := by
      dsimp [e, reflect]
      omega
    have hj : N - 1 - e j = 2 * k - (s : ℤ) - (n - 1 - j) - 2 := by
      rw [hi]
      dsimp [N]
      omega
    simp only [reflectedTerm, form, tensorTerm, matterBPZ_tmul]
    rw [hj, hi]
  rw [heq]
  refine ⟨(hfinite.fun_comp (map_zero form)).preimage_embedding e.toEmbedding, ?_⟩
  change (∑ᶠ j : ℤ, form (tensorTerm (e j))) =
    form (((stateField (DO r a ⊗ₜ[ℂ] DH s b))[[N]]) (v ⊗ₜ[ℂ] y))
  rw [stateField_tmul]
  change _ = form (∑ᶠ i : ℤ, tensorTerm i)
  rw [map_finsum form hfinite]
  exact finsum_comp_equiv e (f := fun i => form (tensorTerm i))

/-- At weights `h` and `k`, the finite orbifold adjunction and the all-state
hyperbolic adjunction give the native matter transpose on pure tensors. -/
theorem matterBPZ_mode_adjoint_tmul (a : Orbifold) (b : Hyperbolic) (h k : ℤ) (A : ℕ)
    (ha : ∀ r, A ≤ r → DO r a = 0) (hk : b ∈ grade hyperbolicData k)
    (hOrbifold : ∀ (j : ℤ) (u v : Orbifold),
      orbifoldBPZ (((YO a)[[j]]) u) v =
        (-1 : ℂ) ^ h * ∑ r ∈ Finset.range A,
          orbifoldBPZ u (((YO (DO r a))[[2 * h - (r : ℤ) - j - 2]]) v))
    (n : ℤ) (u v : Orbifold) (x y : Hyperbolic) :
    matterBPZ (((stateField (a ⊗ₜ[ℂ] b))[[n]]) (u ⊗ₜ[ℂ] x)) (v ⊗ₜ[ℂ] y) =
      (-1 : ℂ) ^ (h + k) * ∑ d ∈ Finset.range (A + hyperbolicLoweringCutoff b),
        matterBPZ (u ⊗ₜ[ℂ] x)
          (((stateField (DM d (a ⊗ₜ[ℂ] b)))[[2 * (h + k) - (d : ℤ) - n - 2]])
            (v ⊗ₜ[ℂ] y)) := by
  classical
  let B := hyperbolicLoweringCutoff b
  let P := Finset.range A ×ˢ Finset.range B
  have hHyperbolic (j : ℤ) :
      hyperbolicBPZ (((YH b)[[j]]) x) y =
        (-1 : ℂ) ^ k * ∑ s ∈ Finset.range B,
          hyperbolicBPZ x (((YH (DH s b))[[2 * k - (s : ℤ) - j - 2]]) y) := by
    have ht := SourceBPZ.AllStateTranspose.sourcePairing_allState hyperbolicData
      hyperbolic_det_unit k j b hk x y
    rw [hyperbolic_gram_inv] at ht
    simpa only [B, hyperbolicLoweringCutoff, hyperbolicMode, dividedTranslation,
      LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul] using ht
  let pairAt (m : ℤ) : Matter →ₗ[ℂ] ℂ :=
    (matterBPZ (u ⊗ₜ[ℂ] x)).comp
      ((LinearMap.applyₗ (R := ℂ) (v ⊗ₜ[ℂ] y)).comp (modesOfStateField stateField m))
  let reflectedIndex (d : ℤ) : ℤ := 2 * (h + k) - d - n - 2
  let pairedDescendants (rs : ℕ × ℕ) :=
    pairAt (reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ))) (DO rs.1 a ⊗ₜ[ℂ] DH rs.2 b)
  let term (j : ℤ) (rs : ℕ × ℕ) := reflectedTerm a u v b x y h k n rs.1 rs.2 j
  have hsign : (-1 : ℂ) ^ (h + k) = (-1 : ℂ) ^ h * (-1 : ℂ) ^ k :=
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) h k
  have hrow (j : ℤ) :
      orbifoldBPZ (((YO a)[[j]]) u) v * hyperbolicBPZ (((YH b)[[n - 1 - j]]) x) y =
        (-1 : ℂ) ^ (h + k) * ∑ rs ∈ P, term j rs := by
    rw [hOrbifold j u v, hHyperbolic (n - 1 - j), hsign]
    let orb (r : ℕ) := orbifoldBPZ u (((YO (DO r a))[[2 * h - (r : ℤ) - j - 2]]) v)
    let hyp (s : ℕ) :=
      hyperbolicBPZ x (((YH (DH s b))[[2 * k - (s : ℤ) - (n - 1 - j) - 2]]) y)
    change ((-1 : ℂ) ^ h * ∑ r ∈ Finset.range A, orb r) *
        ((-1 : ℂ) ^ k * ∑ s ∈ Finset.range B, hyp s) =
      ((-1 : ℂ) ^ h * (-1 : ℂ) ^ k) * ∑ rs ∈ P, term j rs
    have hprod : (∑ r ∈ Finset.range A, orb r) * (∑ s ∈ Finset.range B, hyp s) =
        ∑ rs ∈ P, term j rs := by
      change _ = ∑ rs ∈ Finset.range A ×ˢ Finset.range B, term j rs
      rw [Finset.sum_mul, Finset.sum_product]
      simp only [Finset.mul_sum, term, reflectedTerm, orb, hyp]
    rw [← hprod]
    ring
  have hdiag (d : ℕ) :
      pairAt (reflectedIndex d) (DM d (a ⊗ₜ[ℂ] b)) =
        ∑ rs ∈ antidiagonal d, pairedDescendants rs := by
    rw [divided_matter_L1_tmul, map_sum]
    apply Finset.sum_congr rfl
    intro rs hrs
    have hd : (rs.1 : ℤ) + (rs.2 : ℤ) = (d : ℤ) := by
      exact_mod_cast (mem_antidiagonal.mp hrs : rs.1 + rs.2 = d)
    simp only [pairedDescendants, hd]
  have hzero (rs : ℕ × ℕ) (hr : A ≤ rs.1 ∨ B ≤ rs.2) : pairedDescendants rs = 0 := by
    rcases hr with hr | hs
    · simp only [pairedDescendants, ha _ hr, TensorProduct.zero_tmul, map_zero]
    · simp only [pairedDescendants, hyperbolic_lowering_tail b _ hs, TensorProduct.tmul_zero,
        map_zero]
  change _ = (-1 : ℂ) ^ (h + k) * ∑ d ∈ Finset.range (A + B),
    pairAt (reflectedIndex d) (DM d (a ⊗ₜ[ℂ] b))
  rw [matterBPZ_mode_tmul]
  calc
    _ = ∑ᶠ j : ℤ, (-1 : ℂ) ^ (h + k) * ∑ rs ∈ P, term j rs := finsum_congr hrow
    _ = (-1 : ℂ) ^ (h + k) * ∑ rs ∈ P, ∑ᶠ j : ℤ, term j rs := by
      -- The union of the reflected supports over P is finite.
      rw [← finsum_sum_comm P term (fun rs _ =>
        (reflected_mode_pair a u v b x y h k n rs.1 rs.2).1)]
      simpa only [smul_eq_mul] using
        (smul_finsum ((-1 : ℂ) ^ (h + k)) (fun j => ∑ rs ∈ P, term j rs)).symm
    _ = (-1 : ℂ) ^ (h + k) * ∑ rs ∈ P, pairedDescendants rs := by
      congr 1
      apply Finset.sum_congr rfl
      intro rs _
      have hindex : reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ)) =
          2 * (h + k) - (rs.1 : ℤ) - (rs.2 : ℤ) - n - 2 := by
        dsimp [reflectedIndex]
        omega
      change (∑ᶠ j : ℤ, term j rs) = pairAt _ _
      rw [hindex]
      exact (reflected_mode_pair a u v b x y h k n rs.1 rs.2).2
    _ = _ := by
      simp_rw [hdiag]
      rw [sum_antidiagonal_cutoffs A B pairedDescendants hzero]

/-- A pure inserted matter state has the native finite transpose against all
algebraic matter testers. -/
theorem matterBPZ_mode_adjoint (a : Orbifold) (b : Hyperbolic) (h k : ℤ) (A : ℕ)
    (ha : ∀ r, A ≤ r → DO r a = 0) (hk : b ∈ grade hyperbolicData k)
    (hOrbifold : ∀ (j : ℤ) (u v : Orbifold),
      orbifoldBPZ (((YO a)[[j]]) u) v =
        (-1 : ℂ) ^ h * ∑ r ∈ Finset.range A,
          orbifoldBPZ u (((YO (DO r a))[[2 * h - (r : ℤ) - j - 2]]) v))
    (n : ℤ) (u v : Matter) :
    matterBPZ (((stateField (a ⊗ₜ[ℂ] b))[[n]]) u) v =
      (-1 : ℂ) ^ (h + k) * ∑ d ∈ Finset.range (A + hyperbolicLoweringCutoff b),
        matterBPZ u (((stateField (DM d (a ⊗ₜ[ℂ] b)))[[2 * (h + k) - (d : ℤ) - n - 2]]) v) := by
  induction u using TensorProduct.inductionOn generalizing v with
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, mul_add, hu v, hw v]
  | tmul u x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw =>
      simp only [map_add, Finset.sum_add_distrib, mul_add, hv, hw]
    | tmul v y =>
      exact matterBPZ_mode_adjoint_tmul a b h k A ha hk hOrbifold n u v x y

#print axioms divided_matter_L1_tmul
#print axioms reflected_mode_pair
#print axioms matterBPZ_mode_adjoint_tmul
#print axioms matterBPZ_mode_adjoint

end D5.S3.VertexAlgebra.OriginalOrbifoldCriticalMatterModeBPZ
