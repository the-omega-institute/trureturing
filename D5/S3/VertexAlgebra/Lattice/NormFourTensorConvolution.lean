/- GID: D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourTensorConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite integer field convolution and natural translation on the actual literal tensor vertex algebra. -/

import D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Basic

/-!
The complete r=-1 residue iterate gives both natural finite-support families.
The original injective tensorMap reflects their support, and the pinned
Equiv.subRight and Equiv.intEquivNatSumNat reindex them over every integer.
Coefficient preservation pulls the ambient equality back to the actual
NormFourTensorVertexAlgebra.tensorVertexAlgebra. Actual covariance and
state_derivative_modes at -1 give the ambient derivation law; translation
preservation and tensor extensionality give the global tensor translation.

The norm-four construction retains Dong--Mason--Zhu and Shimakura attribution;
the lattice fields retain Bakalov--Kac attribution. The imported residue,
iterate and normal-product kernels retain Scott Carnahan and Matsuo--Nagatomo
attribution, including Carnahan's Apache-2.0 notice and the adapted kernels
from ScottCarnahan/vertexAlg, commit 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean. No literature novelty is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourTensorConvolution

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus LatticeSugawaraConformal
open LatticeActualStateDerivative NormFourVacuumIrreducible
open NormFourTensorEmbedding NormFourTensorCommutantModes
open scoped BigOperators VertexOperator TensorProduct

noncomputable section

-- Complete integer convolution in the ambient image, consumed by the actual field law.
private theorem ambient_tensor_convolution (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v : vacuumDescendants D a s) (b c : NormFourCommutant.space D a s)
    (n : ℤ) :
    let V_S := NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := NormFourCommutant.restrictedVertexAlgebra D a s
    let F := tensorMap D a s
    let f : ℤ → vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s :=
      fun k => (((V_S.stateField u)[[k]]) v) ⊗ₜ[ℂ]
        (((V_C.stateField b)[[n - 1 - k]]) c)
    Function.HasFiniteSupport f ∧
      mu D (F (u ⊗ₜ[ℂ] b)) n (F (v ⊗ₜ[ℂ] c)) = F (∑ᶠ k : ℤ, f k) := by
  classical
  let S := vacuumDescendants D a s
  let C := NormFourCommutant.space D a s
  let V_S := NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
  let V_C := NormFourCommutant.restrictedVertexAlgebra D a s
  let F := tensorMap D a s
  let f : ℤ → S ⊗[ℂ] C := fun k =>
    (((V_S.stateField u)[[k]]) v) ⊗ₜ[ℂ]
      (((V_C.stateField b)[[n - 1 - k]]) c)
  change Function.HasFiniteSupport f ∧
    mu D (F (u ⊗ₜ[ℂ] b)) n (F (v ⊗ₜ[ℂ] c)) = F (∑ᶠ k : ℤ, f k)

  obtain ⟨injectiveF, pureProduct, allS, _vacuumImage⟩ :=
    actual_tensor_embedding D a ha s hs

  -- Both mode identities specialize the already accepted FULL intertwinings.
  have sMode (x y : S) (d : C) (k : ℤ) :
      mu D x.val k (F (y ⊗ₜ[ℂ] d)) =
        F ((((V_S.stateField x)[[k]]) y) ⊗ₜ[ℂ] d) := by
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using
      (allS x k (y ⊗ₜ[ℂ] d)).symm
  have cMode (d e : C) (x : S) (k : ℤ) :
      mu D d.val k (F (x ⊗ₜ[ℂ] e)) =
        F (x ⊗ₜ[ℂ] (((V_C.stateField d)[[k]]) e)) := by
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using
      (actual_commutant_mode_intertwining D a s d k (x ⊗ₜ[ℂ] e)).symm

  let first : ℕ → S ⊗[ℂ] C := fun i =>
    (((V_S.stateField u)[[n + (i : ℤ)]]) v) ⊗ₜ[ℂ]
      (((V_C.stateField b)[[-1 - (i : ℤ)]]) c)
  let second : ℕ → S ⊗[ℂ] C := fun i =>
    (((V_S.stateField u)[[n - 1 - (i : ℤ)]]) v) ⊗ₜ[ℂ]
      (((V_C.stateField b)[[(i : ℤ)]]) c)

  -- This is ALL i, including every term beyond i=0.
  have weight (i : ℕ) :
      (-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ) = 1 :=
    minus_one_binomial i
  have first_image (i : ℕ) :
      ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
        mu D b.val (-1 - (i : ℤ))
          (mu D u.val (n + (i : ℤ)) (F (v ⊗ₜ[ℂ] c))) = F (first i) := by
    rw [weight i, one_smul, sMode u v c (n + (i : ℤ)),
      cMode b c (((V_S.stateField u)[[n + (i : ℤ)]]) v) (-1 - (i : ℤ))]
  have second_image (i : ℕ) :
      ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
        mu D u.val (-1 + n - (i : ℤ))
          (mu D b.val (i : ℤ) (F (v ⊗ₜ[ℂ] c))) = F (second i) := by
    rw [weight i, one_smul, cMode b c v (i : ℤ),
      sMode u v (((V_C.stateField b)[[(i : ℤ)]]) c) (-1 + n - (i : ℤ))]
    dsimp only [second]
    rw [show -1 + n - (i : ℤ) = n - 1 - (i : ℤ) by omega]

  -- Use the actual iterate, with both natural families and their real support.
  have actual := stateField_iterate D b.val u.val (F (v ⊗ₜ[ℂ] c)) (-1) n
  dsimp only at actual
  change
    Function.HasFiniteSupport (fun i : ℕ =>
      ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
        mu D b.val (-1 - (i : ℤ))
          (mu D u.val (n + (i : ℤ)) (F (v ⊗ₜ[ℂ] c)))) ∧
    Function.HasFiniteSupport (fun i : ℕ =>
      ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
        mu D u.val (-1 + n - (i : ℤ))
          (mu D b.val (i : ℤ) (F (v ⊗ₜ[ℂ] c)))) ∧
    mu D (mu D b.val (-1) u.val) n (F (v ⊗ₜ[ℂ] c)) =
      (∑ᶠ i : ℕ,
        ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
          mu D b.val (-1 - (i : ℤ))
            (mu D u.val (n + (i : ℤ)) (F (v ⊗ₜ[ℂ] c)))) -
      ((-1 : ℂ)^(-1 : ℤ)) • (∑ᶠ i : ℕ,
        ((-1 : ℂ)^i * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)) •
          mu D u.val (-1 + n - (i : ℤ))
            (mu D b.val (i : ℤ) (F (v ⊗ₜ[ℂ] c)))) at actual

  have firstImageFinite : Function.HasFiniteSupport (F ∘ first) := by
    simpa only [first_image, Function.comp_def] using actual.1
  have secondImageFinite : Function.HasFiniteSupport (F ∘ second) := by
    simpa only [second_image, Function.comp_def] using actual.2.1
  -- Injectivity, rather than a new uniform truncation/basis bound, pulls back
  -- each complete family's actual finite support. Zero states are retained.
  have firstFinite : Function.HasFiniteSupport first :=
    firstImageFinite.of_comp (map_zero F) injectiveF
  have secondFinite : Function.HasFiniteSupport second :=
    secondImageFinite.of_comp (map_zero F) injectiveF

  have ambient :
      mu D (F (u ⊗ₜ[ℂ] b)) n (F (v ⊗ₜ[ℂ] c)) =
        (∑ᶠ i : ℕ, F (first i)) + (∑ᶠ i : ℕ, F (second i)) := by
    rw [pureProduct u b]
    -- The outer minus and (-1)^(-1) give PLUS on the full second family.
    simpa only [first_image, second_image,
      show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num,
      neg_smul, one_smul, sub_neg_eq_add] using actual.2.2

  -- Translate k to k-n, then use EXACTLY the existing Int/Nat+Nat equiv.
  -- Its inverse sends inl i to n+i and inr i to n-1-i.
  let e : ℤ ≃ ℕ ⊕ ℕ := (Equiv.subRight n).trans Equiv.intEquivNatSumNat
  let split : ℕ ⊕ ℕ → S ⊗[ℂ] C := Sum.elim first second
  have inverse_terms (j : ℕ ⊕ ℕ) : f (e.symm j) = split j := by
    cases j with
    | inl i =>
        change f ((i : ℤ) + n) = first i
        dsimp only [f, first]
        rw [show (i : ℤ) + n = n + (i : ℤ) by omega,
          show n - 1 - (n + (i : ℤ)) = -1 - (i : ℤ) by omega]
    | inr i =>
        change f (Int.negSucc i + n) = second i
        dsimp only [f, second]
        rw [show Int.negSucc i + n = n - 1 - (i : ℤ) by omega,
          show n - 1 - (n - 1 - (i : ℤ)) = (i : ℤ) by omega]

  -- The existing disjoint-sum finset API handles the two finite supports.
  -- No replacement integer equivalence or general reindexing framework.
  let splitSupport : Finset (ℕ ⊕ ℕ) :=
    firstFinite.toFinset.disjSum secondFinite.toFinset
  have split_support : Function.support split ⊆ (splitSupport : Set (ℕ ⊕ ℕ)) := by
    intro j hj
    cases j with
    | inl i =>
        change first i ≠ 0 at hj
        change Sum.inl i ∈ firstFinite.toFinset.disjSum secondFinite.toFinset
        exact Finset.inl_mem_disjSum.mpr (firstFinite.mem_toFinset.mpr hj)
    | inr i =>
        change second i ≠ 0 at hj
        change Sum.inr i ∈ firstFinite.toFinset.disjSum secondFinite.toFinset
        exact Finset.inr_mem_disjSum.mpr (secondFinite.mem_toFinset.mpr hj)
  have splitFinite : Function.HasFiniteSupport split :=
    splitSupport.finite_toSet.subset split_support
  have f_eq : f = split ∘ e := by
    funext k
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using inverse_terms (e k)
  have finite : Function.HasFiniteSupport f := by
    rw [f_eq]
    exact splitFinite.comp_of_injective e.injective

  have split_sum : (∑ᶠ j : ℕ ⊕ ℕ, split j) =
      (∑ᶠ i : ℕ, first i) + (∑ᶠ i : ℕ, second i) := by
    rw [finsum_eq_sum_of_support_subset split split_support]
    change (∑ j ∈ firstFinite.toFinset.disjSum secondFinite.toFinset, split j) = _
    rw [Finset.sum_disjSum]
    change (∑ i ∈ firstFinite.toFinset, first i) +
      (∑ i ∈ secondFinite.toFinset, second i) = _
    exact congrArg₂ (fun x y : S ⊗[ℂ] C => x + y)
      (finsum_eq_sum first firstFinite).symm
      (finsum_eq_sum second secondFinite).symm
  have integer_sum : (∑ᶠ k : ℤ, f k) =
      (∑ᶠ i : ℕ, first i) + (∑ᶠ i : ℕ, second i) := by
    calc
      (∑ᶠ k : ℤ, f k) = ∑ᶠ j : ℕ ⊕ ℕ, f (e.symm j) :=
        (finsum_comp_equiv e.symm).symm
      _ = ∑ᶠ j : ℕ ⊕ ℕ, split j := finsum_congr inverse_terms
      _ = _ := split_sum

  refine ⟨finite, ?_⟩
  rw [integer_sum, map_add, map_finsum F firstFinite, map_finsum F secondFinite]
  exact ambient


-- Only the actual production -1 coefficient is needed. The two existing
-- identities already have exactly the same scalar and shifted mode.
private theorem translation_minus_one_product (D : LatticeData)
    (x y : Carrier D) :
    translation D (mu D x (-1) y) =
      mu D (translation D x) (-1) y + mu D x (-1) (translation D y) := by
  have commutator :
      translation D * ((Y D x)[[-1]]) -
          ((Y D x)[[-1]]) * translation D =
        ((Y D (translation D x))[[-1]]) :=
    (stateField_covariance D x (-1)).trans
      (state_derivative_modes D x (-1)).symm
  have evaluated := congrArg
    (fun A : Module.End ℂ (Carrier D) => A y) commutator
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at evaluated
  simpa only [mu] using (sub_eq_iff_eq_add.mp evaluated)

-- The constructor uses (translation D).restrict; its inclusion is literal.
private theorem vacuum_translation_val (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : vacuumDescendants D a s) :
    ((NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).translation u :
        Carrier D) = translation D u.val := rfl

-- The commutant constructor explicitly gives the subtype this ambient value.
private theorem commutant_translation_val (D : LatticeData) (a : Charge D)
    (s : ℂ) (b : NormFourCommutant.space D a s) :
    ((NormFourCommutant.restrictedVertexAlgebra D a s).translation b :
        Carrier D) = translation D b.val := rfl

-- Ambient derivation law for the actual pure-product embedding.
private theorem actual_pure_tensor_translation (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := NormFourCommutant.space D a s
    let V_S := NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := NormFourCommutant.restrictedVertexAlgebra D a s
    let F := tensorMap D a s
    ∀ (u : S) (b : C),
      (LatticeActualVertexAlgebra.actualVertexAlgebra D).translation
          (F (u ⊗ₜ[ℂ] b)) =
        F ((V_S.translation u) ⊗ₜ[ℂ] b + u ⊗ₜ[ℂ] (V_C.translation b)) := by
  dsimp only
  intro u b
  change translation D (tensorMap D a s (u ⊗ₜ[ℂ] b)) = _
  have pureProduct := (actual_tensor_embedding D a ha s hs).2.1
  -- F places the C state on the left of the -1 product, so its two
  -- translated-factor terms occur in the opposite additive order.
  simpa only [map_add, pureProduct, vacuum_translation_val,
    commutant_translation_val] using
      (translation_minus_one_product D b.val u.val).trans (add_comm _ _)


/-- Finite support and the exact all-integer pure tensor field convolution
on the actual accepted literal tensor vertex algebra. -/
theorem actual_tensor_field_convolution (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v : vacuumDescendants D a s) (b c : NormFourCommutant.space D a s)
    (n : ℤ) :
    let V_S := NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := NormFourCommutant.restrictedVertexAlgebra D a s
    let V_T := NormFourTensorVertexAlgebra.tensorVertexAlgebra D a ha s hs
    let f : ℤ → vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s :=
      fun k => (((V_S.stateField u)[[k]]) v) ⊗ₜ[ℂ]
        (((V_C.stateField b)[[n - 1 - k]]) c)
    Function.HasFiniteSupport f ∧
      (((V_T.stateField (u ⊗ₜ[ℂ] b))[[n]]) (v ⊗ₜ[ℂ] c)) = ∑ᶠ k : ℤ, f k := by
  have embedding :=
    NormFourTensorVertexAlgebra.actual_tensor_vertex_algebra_embedding D a ha s hs
  dsimp only at embedding
  rcases embedding with ⟨injectiveF, _rv, _rc, _rt, _vR, _cR, _tR,
    _naturalVac, _imageVac, coeffF, _translationF⟩
  obtain ⟨finite, ambient⟩ := ambient_tensor_convolution D a ha s hs u v b c n
  refine ⟨finite, injectiveF ?_⟩
  exact (coeffF (u ⊗ₜ[ℂ] b) (v ⊗ₜ[ℂ] c) n).trans ambient

/-- Global natural translation on the actual literal tensor space, together
with its pure-pair formula for every pair, including zero states. -/
theorem actual_tensor_translation_split (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := NormFourCommutant.space D a s
    let V_S := NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs
    let V_C := NormFourCommutant.restrictedVertexAlgebra D a s
    let V_T := NormFourTensorVertexAlgebra.tensorVertexAlgebra D a ha s hs
    V_T.translation = TensorProduct.map V_S.translation (LinearMap.id : C →ₗ[ℂ] C) +
      TensorProduct.map (LinearMap.id : S →ₗ[ℂ] S) V_C.translation ∧
    ∀ (u : S) (b : C), V_T.translation (u ⊗ₜ[ℂ] b) =
      (V_S.translation u) ⊗ₜ[ℂ] b + u ⊗ₜ[ℂ] (V_C.translation b) := by
  dsimp only
  have embedding :=
    NormFourTensorVertexAlgebra.actual_tensor_vertex_algebra_embedding D a ha s hs
  dsimp only at embedding
  rcases embedding with ⟨injectiveF, _rv, _rc, _rt, _vR, _cR, _tR,
    _naturalVac, _imageVac, _coeffF, translationF⟩
  have pure (u : vacuumDescendants D a s) (b : NormFourCommutant.space D a s) :
      (NormFourTensorVertexAlgebra.tensorVertexAlgebra D a ha s hs).translation
        (u ⊗ₜ[ℂ] b) =
      ((NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).translation u) ⊗ₜ[ℂ] b +
        u ⊗ₜ[ℂ] ((NormFourCommutant.restrictedVertexAlgebra D a s).translation b) := by
    apply injectiveF
    exact (translationF (u ⊗ₜ[ℂ] b)).trans
      (actual_pure_tensor_translation D a ha s hs u b)
  refine ⟨?_, pure⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro b
  simpa only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply] using pure u b

end
end D5.S3.VertexAlgebra.Lattice.NormFourTensorConvolution
