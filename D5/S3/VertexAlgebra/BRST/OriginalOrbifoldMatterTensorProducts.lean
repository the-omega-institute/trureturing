/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTensorProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTensorProducts
   mirror-E: none(waiver:algebraic-original-matter-products)
   anchors: []
   utility: none
   digest: Native translation covariance and finite ordered tensor matter coefficients. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorField

/-! The two constituent translation laws combine under normal convolution.
An ordered product has finite support on pairs of modes on every pure input. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterTensorProducts

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldMatterTensorField (modeSummand modeSummand_finite stateField
  stateField_ncoeff_apply stateField_tmul support_tmul)
open private cutoff mode_eq_zero_of_cutoff_le modeSummand_tmul from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorField

local notation "T" => OriginalOrbifoldCriticalMatter.mode (-1)
local notation "TO" => orbifoldVertexAlgebra.translation
local notation "TH" => LatticeSugawaraConformal.translation hyperbolicData
local notation "YO" => orbifoldVertexAlgebra.stateField
local notation "YH" => LatticeAllStateField.Y hyperbolicData

private theorem translation_tmul (x : Orbifold) (y : Hyperbolic) :
    T (x ⊗ₜ[ℂ] y) = TO x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] TH y := by
  rw [mode_minus_one_eq_translation]
  rfl

/-- The native matter translation annihilates the tensor vacuum. -/
theorem translation_vacuum : T matterVacuum = 0 := by
  rw [matterVacuum, translation_tmul, orbifoldVertexAlgebra.translation_vacuum,
    LatticeAllStateField.translation_kills_vacuum, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, add_zero]

private theorem summand_covariance (s : Matter) (n k : ℤ) :
    T * modeSummand n k s - modeSummand n k s * T =
      -(k : ℂ) • modeSummand (n - 1) (k - 1) s +
        -((n - 1 - k : ℤ) : ℂ) • modeSummand (n - 1) k s := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    have hO := LinearMap.congr_fun (orbifoldVertexAlgebra.covariance a k) x
    have hH := LinearMap.congr_fun
      (LatticeAllStateField.stateField_covariance hyperbolicData b (n - 1 - k)) y
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hO hH
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, modeSummand_tmul, translation_tmul, map_add]
    rw [sub_eq_iff_eq_add.mp hO, sub_eq_iff_eq_add.mp hH,
      show n - 1 - 1 - (k - 1) = n - 1 - k by omega,
      show n - 1 - k - 1 = n - 1 - 1 - k by omega]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    abel
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul] at *
    rw [show ∀ A B C D : Module.End ℂ Matter,
      (A + B) - (C + D) = (A - C) + (B - D) by intros; abel, hs, ht]
    simp only [smul_add]
    abel

/-- The commutator of the native translation with each actual matter mode is its derivative. -/
theorem stateField_covariance (s : Matter) (n : ℤ) :
    T * ((stateField s)[[n]]) - ((stateField s)[[n]]) * T =
      -(n : ℂ) • ((stateField s)[[n - 1]]) := by
  apply LinearMap.ext
  intro x
  let f : ℤ → Matter := fun k => modeSummand (n - 1) k s x
  have hf : Function.HasFiniteSupport f := modeSummand_finite s x (n - 1)
  let shift : ℤ ≃ ℤ := Equiv.subRight 1
  have hLeft : Function.HasFiniteSupport (fun k : ℤ => -(k : ℂ) • f (k - 1)) :=
    (hf.comp_of_injective shift.injective).smul_right (fun k : ℤ => -(k : ℂ))
  have hRight : Function.HasFiniteSupport (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k) :=
    hf.smul_right (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ))
  have hShift : (∑ᶠ k : ℤ, -(k : ℂ) • f (k - 1)) =
      ∑ᶠ k : ℤ, -((k + 1 : ℤ) : ℂ) • f k := by
    let g : ℤ → Matter := fun k => -((k + 1 : ℤ) : ℂ) • f k
    calc
      _ = ∑ᶠ k : ℤ, g (shift k) := by
        apply finsum_congr
        intro k
        change -(k : ℂ) • f (k - 1) = -((k - 1 + 1 : ℤ) : ℂ) • f (k - 1)
        rw [sub_add_cancel]
      _ = _ := finsum_comp_equiv shift
  change T (((stateField s)[[n]]) x) - ((stateField s)[[n]]) (T x) =
    -(n : ℂ) • ((stateField s)[[n - 1]]) x
  rw [stateField_ncoeff_apply s x n, stateField_ncoeff_apply s (T x) n,
    map_finsum T (modeSummand_finite s x n),
    ← finsum_sub_distrib ((modeSummand_finite s x n).fun_comp (map_zero T))
      (modeSummand_finite s (T x) n)]
  calc
    _ = ∑ᶠ k : ℤ, (-(k : ℂ) • f (k - 1) + -((n - 1 - k : ℤ) : ℂ) • f k) := by
      apply finsum_congr
      intro k
      exact LinearMap.congr_fun (summand_covariance s n k) x
    _ = _ := by
      rw [finsum_add_distrib hLeft hRight, hShift,
        ← finsum_add_distrib
          (f := fun k : ℤ => -((k + 1 : ℤ) : ℂ) • f k)
          (g := fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k)
          (hf.smul_right (fun k : ℤ => -((k + 1 : ℤ) : ℂ))) hRight]
      simp_rw [← add_smul, show ∀ k : ℤ,
        -((k + 1 : ℤ) : ℂ) + -((n - 1 - k : ℤ) : ℂ) = -(n : ℂ) by
          intro k
          push_cast
          ring]
      rw [← smul_finsum' _ hf, stateField_ncoeff_apply]

private theorem convolution_finite (a x : Orbifold) (b y : Hyperbolic) (n : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ =>
      ((YO a)[[k]]) x ⊗ₜ[ℂ] ((YH b)[[n - 1 - k]]) y) :=
  (Set.finite_Icc _ _).subset
    (support_tmul a x b y n (cutoff (YO a) x) (cutoff (YH b) y)
      (mode_eq_zero_of_cutoff_le _ _) (mode_eq_zero_of_cutoff_le _ _))

/-- The ordered product of actual matter modes on pure tensors is a pointwise finite
sum over the outer orbifold index and the inner orbifold index, in that order. -/
theorem ordered_product_tmul (a c x : Orbifold) (b d y : Hyperbolic) (m n : ℤ) :
    ((stateField (a ⊗ₜ[ℂ] b))[[m]])
        (((stateField (c ⊗ₜ[ℂ] d))[[n]]) (x ⊗ₜ[ℂ] y)) =
      ∑ᶠ p : ℤ × ℤ, ((YO a)[[p.1]]) (((YO c)[[p.2]]) x) ⊗ₜ[ℂ]
        ((YH b)[[m - 1 - p.1]]) (((YH d)[[n - 1 - p.2]]) y) := by
  let left (j : ℤ) := ((YO c)[[j]]) x
  let right (j : ℤ) := ((YH d)[[n - 1 - j]]) y
  let inner (j : ℤ) : Matter := left j ⊗ₜ[ℂ] right j
  let term (p : ℤ × ℤ) : Matter :=
    ((YO a)[[p.1]]) (left p.2) ⊗ₜ[ℂ] ((YH b)[[m - 1 - p.1]]) (right p.2)
  have hInner : Function.HasFiniteSupport inner := convolution_finite c x d y n
  have hOuter (j : ℤ) : Function.HasFiniteSupport (fun i => term (i, j)) :=
    convolution_finite a (left j) b (right j) m
  let swap := ((Equiv.sigmaEquivProd ℤ ℤ).trans (Equiv.prodComm ℤ ℤ)).toEmbedding
  let pairs : Finset (ℤ × ℤ) := (hInner.toFinset.sigma fun j => (hOuter j).toFinset).map swap
  have hPairs : Function.support term ⊆ (pairs : Set (ℤ × ℤ)) := by
    rintro ⟨i, j⟩ hij
    have hOuterIndex : i ∈ (hOuter j).toFinset := (hOuter j).mem_toFinset.2 hij
    have hInnerIndex : j ∈ hInner.toFinset := by
      apply hInner.mem_toFinset.2
      intro hj
      apply hij
      rw [show term (i, j) = modeSummand m i (a ⊗ₜ[ℂ] b) (inner j) from
        (modeSummand_tmul a (left j) b (right j) m i).symm, hj, map_zero]
    change (i, j) ∈ pairs
    exact Finset.mem_map.2 ⟨⟨j, i⟩, Finset.mem_sigma.2 ⟨hInnerIndex, hOuterIndex⟩, rfl⟩
  rw [stateField_tmul c x d y n]
  change ((stateField (a ⊗ₜ[ℂ] b))[[m]]) (∑ᶠ j : ℤ, inner j) = ∑ᶠ p, term p
  rw [finsum_eq_sum inner hInner, map_sum, finsum_eq_sum_of_support_subset term hPairs]
  change (∑ j ∈ hInner.toFinset, ((stateField (a ⊗ₜ[ℂ] b))[[m]]) (inner j)) =
    ∑ p ∈ (hInner.toFinset.sigma fun j => (hOuter j).toFinset).map swap, term p
  rw [Finset.sum_map, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change ((stateField (a ⊗ₜ[ℂ] b))[[m]]) (left j ⊗ₜ[ℂ] right j) =
    ∑ i ∈ (hOuter j).toFinset, term (i, j)
  rw [stateField_tmul a (left j) b (right j) m]
  exact finsum_eq_sum (fun i => term (i, j)) (hOuter j)

#print axioms translation_vacuum
#print axioms stateField_covariance
#print axioms ordered_product_tmul

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterTensorProducts
