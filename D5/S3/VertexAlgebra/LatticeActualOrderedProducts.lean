/- GID: D5/S3/VertexAlgebra/LatticeActualOrderedProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualOrderedProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both actual charged ordered products expand in the bounded common kernel. -/

import D5.S3.VertexAlgebra.LatticeActualProductKernel

/- Ordered products of the actual lattice fields, with their actual cocycle.
   All finite supports and oscillator recurrences are derived on the actual
   carrier. Bakalov--Kac math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualOrderedProducts
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualGeneratorLocality LatticeActualProductKernel MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

def contraction (b : ℤ) (j : ℕ) : ℂ := (-1 : ℂ)^j * (Ring.choose b j : ℤ)

theorem single_sum {ι : Type*} (D : LatticeData) (δ : Charge D)
    (s : Finset ι) (f : ι → Oscillator D) :
    Finsupp.single δ (∑ i ∈ s, f i) = ∑ i ∈ s, Finsupp.single δ (f i) :=
  map_sum (Finsupp.lsingle δ : Oscillator D →ₗ[ℂ] Carrier D) f s

theorem convolution_finsum (D : LatticeData) (α : Charge D) (s : ℤ)
    (q : Polynomial (Oscillator D)) :
    convolution D α s q = ∑ᶠ j : ℕ, q.coeff j * creationCoeff D α (s+j) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (show Function.support
      (fun j => q.coeff j * creationCoeff D α (s+j)) ⊆ q.support from by
    intro j hj
    exact Polynomial.mem_support_iff.mpr (fun h => hj (by simp [h])))]
  rfl

theorem contracted_convolution (D : LatticeData) (α β : Charge D) (s t : ℤ) :
    convolution D α s (translatedPolynomial D α (creationCoeff D β t)) =
      ∑ j ∈ Finset.range (t.toNat+1), contraction (bilinear D α β) j •
        (creationCoeff D α (s+j) * creationCoeff D β (t-j)) := by
  classical
  rw [convolution_finsum]
  simp_rw [actual_contraction_binomial]
  rw [finsum_eq_sum_of_support_subset _ (show Function.support (fun j : ℕ =>
      (((-1 : ℂ)^j * (Ring.choose (bilinear D α β) j : ℤ)) •
        creationCoeff D β (t-j)) * creationCoeff D α (s+j)) ⊆
          Finset.range (t.toNat+1) from by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    exact hj (by simp [creationCoeff, show t-(j : ℤ) < 0 by omega]))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_mul_assoc, contraction]
  rw [mul_comm (creationCoeff D β (t-j))]

theorem raw_ground (D : LatticeData) (α : Charge D) (k : ℤ) (δ : Charge D) :
    rawCoeff D α k (Finsupp.single δ 1) =
      epsilon D α δ • Finsupp.single (α+δ) (creationCoeff D α (k-bilinear D α δ)) := by
  rw [raw_single_convolution]
  have ht : translatedPolynomial D α (1 : Oscillator D) = 1 := by
    simp [translatedPolynomial]
  rw [ht, show (1 : Polynomial (Oscillator D)) = Polynomial.monomial 0 1 by simp,
    convolution_monomial]
  simp

theorem kernel_ground (D : LatticeData) (α β : Charge D) (u v : ℤ)
    (δ : Charge D) :
    commonKernel D α β u v (Finsupp.single δ 1) = epsilon D (α+β) δ •
      Finsupp.single (α+β+δ)
        (creationCoeff D α (u-bilinear D α δ) * creationCoeff D β (v-bilinear D β δ)) := by
  rw [kernel_single_convolution]
  have ht : translatedPairPolynomial D α β (1 : Oscillator D) = 1 := by
    simp [translatedPairPolynomial]
  rw [ht, show (1 : PairPolynomial D) = MvPolynomial.monomial 0 1 by simp,
    pairConvolution_monomial]
  simp

def orderedKernel (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (p : Oscillator D) : Carrier D :=
  epsilon D α β • ∑ᶠ j : ℕ, contraction (bilinear D α β) j •
    commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)

theorem ordered_finite (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (p : Oscillator D) :
    Function.HasFiniteSupport (fun j : ℕ => contraction (bilinear D α β) j •
      commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)) :=
  Function.HasFiniteSupport.smul_right (fun j => contraction (bilinear D α β) j)
    (ordered_kernel_finite D α β k l δ p).1

/-- The actual ordered product on every charged ground state, including α=β. -/
theorem actual_ordered_ground (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) :
    rawCoeff D α k (rawCoeff D β l (Finsupp.single δ 1)) =
      orderedKernel D α β k l δ 1 := by
  classical
  rw [raw_ground, map_smul, raw_single_convolution, smul_smul]
  rw [mul_comm (epsilon D β δ), epsilon_ordered,
    bilinear_add_right, contracted_convolution]
  unfold orderedKernel
  rw [finsum_eq_sum_of_support_subset _ (show Function.support (fun j : ℕ =>
      contraction (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ 1)) ⊆
          Finset.range ((l-bilinear D β δ).toNat+1) from by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    exact hj (by
      change contraction (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ 1) = 0
      rw [kernel_ground]
      simp [creationCoeff, show l-(j : ℤ)-bilinear D β δ < 0 by omega]))]
  simp_rw [kernel_ground]
  simp only [single_sum, ← Finsupp.smul_single, Finset.smul_sum, smul_smul]
  have hcharge : α+(β+δ) = α+β+δ := by abel
  rw [hcharge]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show k-(bilinear D α β+bilinear D α δ)+(j : ℤ) =
      k-bilinear D α β+j-bilinear D α δ by omega,
    show l-bilinear D β δ-(j : ℤ) = l-j-bilinear D β δ by omega]
  simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

theorem raw_creator_operator (D : LatticeData) (α : Charge D) (k : ℤ) (x : Index D) :
    rawCoeff D α k * creator D x = creator D x * rawCoeff D α k -
      (bilinear D α (unitCharge D x.1) : ℂ) • rawCoeff D α (k+(x.2+1 : ℕ)) := by
  apply Finsupp.lhom_ext
  intro δ p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    creator_single]
  exact raw_creator D α k δ x p

theorem raw_product_creator (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (x : Index D) (p : Oscillator D) :
    rawCoeff D α k (rawCoeff D β l (Finsupp.single δ (X x*p))) =
      creator D x (rawCoeff D α k (rawCoeff D β l (Finsupp.single δ p))) -
      (bilinear D α (unitCharge D x.1) : ℂ) •
        rawCoeff D α (k+(x.2+1 : ℕ)) (rawCoeff D β l (Finsupp.single δ p)) -
      (bilinear D β (unitCharge D x.1) : ℂ) •
        rawCoeff D α k (rawCoeff D β (l+(x.2+1 : ℕ)) (Finsupp.single δ p)) := by
  rw [raw_creator, map_sub, map_smul]
  have hc := congrArg (fun f : Module.End ℂ (Carrier D) =>
      f (rawCoeff D β l (Finsupp.single δ p))) (raw_creator_operator D α k x)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hc
  rw [hc]

theorem ordered_add (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (p q : Oscillator D) :
    orderedKernel D α β k l δ (p+q) =
      orderedKernel D α β k l δ p + orderedKernel D α β k l δ q := by
  simp only [orderedKernel, Finsupp.single_add, map_add, smul_add]
  rw [finsum_add_distrib (ordered_finite D α β k l δ p)
    (ordered_finite D α β k l δ q), smul_add]

theorem ordered_smul (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (c : ℂ) (p : Oscillator D) :
    orderedKernel D α β k l δ (c • p) = c • orderedKernel D α β k l δ p := by
  simp only [orderedKernel, ← Finsupp.smul_single, map_smul]
  simp_rw [smul_comm (contraction (bilinear D α β) _ ) c]
  rw [← smul_finsum' c (ordered_finite D α β k l δ p), smul_comm]

theorem ordered_creator (D : LatticeData) (α β : Charge D) (k l : ℤ)
    (δ : Charge D) (x : Index D) (p : Oscillator D) :
    orderedKernel D α β k l δ (X x*p) =
      creator D x (orderedKernel D α β k l δ p) -
      (bilinear D α (unitCharge D x.1) : ℂ) •
        orderedKernel D α β (k+(x.2+1 : ℕ)) l δ p -
      (bilinear D β (unitCharge D x.1) : ℂ) •
        orderedKernel D α β k (l+(x.2+1 : ℕ)) δ p := by
  classical
  let a : ℂ := bilinear D α (unitCharge D x.1)
  let b : ℂ := bilinear D β (unitCharge D x.1)
  let r : ℤ := (x.2+1 : ℕ)
  let F := fun j : ℕ => contraction (bilinear D α β) j •
    commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)
  let G := fun j : ℕ => contraction (bilinear D α β) j •
    commonKernel D α β (k+r-bilinear D α β+j) (l-j) (Finsupp.single δ p)
  let H := fun j : ℕ => contraction (bilinear D α β) j •
    commonKernel D α β (k-bilinear D α β+j) (l+r-j) (Finsupp.single δ p)
  have hF : Function.HasFiniteSupport F := ordered_finite D α β k l δ p
  have hG : Function.HasFiniteSupport G := ordered_finite D α β (k+r) l δ p
  have hH : Function.HasFiniteSupport H := ordered_finite D α β k (l+r) δ p
  have ht (j : ℕ) : contraction (bilinear D α β) j •
      commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ (X x*p)) =
      creator D x (F j) - a • G j - b • H j := by
    rw [kernel_creator, smul_sub, smul_sub, ← map_smul]
    rw [show k-bilinear D α β+(j : ℤ)+r = k+r-bilinear D α β+j by omega,
      show l-(j : ℤ)+r = l+r-j by omega]
    dsimp only [F,G,H,a,b,r]
    simp only [map_smul,smul_smul]
    module
  unfold orderedKernel
  simp_rw [ht]
  have hc := hF.fun_comp (map_zero (creator D x))
  have ha := Function.HasFiniteSupport.smul_right (fun _ => a) hG
  have hb := Function.HasFiniteSupport.smul_right (fun _ => b) hH
  have hs1 : (∑ᶠ j : ℕ, (creator D x (F j) - a • G j)) =
      (∑ᶠ j : ℕ, creator D x (F j)) - ∑ᶠ j : ℕ, a • G j := by
    simpa only [Pi.sub_apply,Pi.smul_apply,Pi.smul_apply'] using finsum_sub_distrib hc ha
  have hs2 : (∑ᶠ j : ℕ, (creator D x (F j) - a • G j - b • H j)) =
      (∑ᶠ j : ℕ, (creator D x (F j) - a • G j)) - ∑ᶠ j : ℕ, b • H j := by
    simpa only [Pi.sub_apply,Pi.smul_apply,Pi.smul_apply'] using finsum_sub_distrib (hc.sub ha) hb
  have hcSum : (∑ᶠ j : ℕ, creator D x (F j)) = creator D x (∑ᶠ j : ℕ, F j) :=
    ((creator D x).toAddMonoidHom.map_finsum hF).symm
  rw [hs2,hs1,hcSum, ← smul_finsum' a hG, ← smul_finsum' b hH]
  change epsilon D α β • (creator D x (∑ᶠ j : ℕ, F j) - a • (∑ᶠ j : ℕ, G j) -
      b • (∑ᶠ j : ℕ, H j)) =
    creator D x (epsilon D α β • (∑ᶠ j : ℕ, F j)) -
      a • epsilon D α β • (∑ᶠ j : ℕ, G j) -
      b • epsilon D α β • (∑ᶠ j : ℕ, H j)
  rw [map_smul]
  module

/-- Both indices and every polynomial are quantified; no product/locality premise. -/
theorem actual_ordered_product (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) (k l : ℤ) :
    rawCoeff D α k (rawCoeff D β l (Finsupp.single δ p)) =
      epsilon D α β • ∑ᶠ j : ℕ, contraction (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p) := by
  change _ = orderedKernel D α β k l δ p
  induction p using MvPolynomial.induction_on generalizing k l with
  | C c =>
    rw [MvPolynomial.C_eq_smul_one,
      ← Finsupp.smul_single, map_smul, map_smul, ordered_smul, actual_ordered_ground]
  | add p q hp hq =>
    rw [Finsupp.single_add, map_add, map_add, ordered_add, hp, hq]
  | mul_X p x hp =>
    rw [mul_comm p, raw_product_creator, ordered_creator, hp, hp, hp]

theorem kernel_swap (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) (u v : ℤ) :
    commonKernel D β α v u (Finsupp.single δ p) =
      commonKernel D α β u v (Finsupp.single δ p) := by
  induction p using MvPolynomial.induction_on generalizing u v with
  | C c =>
    rw [MvPolynomial.C_eq_smul_one,
      ← Finsupp.smul_single, map_smul, map_smul]
    rw [kernel_ground, kernel_ground, add_comm β α,
      mul_comm (creationCoeff D β (v-bilinear D β δ))
        (creationCoeff D α (u-bilinear D α δ))]
  | add p q hp hq =>
    rw [Finsupp.single_add, map_add, map_add, hp, hq]
  | mul_X p x hp =>
    rw [mul_comm p, kernel_creator, kernel_creator]
    simp_rw [hp]
    abel

/-- The second ordered product uses exactly the same actual common kernel. -/
theorem actual_reverse_ordered_product (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) (k l : ℤ) :
    rawCoeff D β l (rawCoeff D α k (Finsupp.single δ p)) =
      epsilon D β α • ∑ᶠ j : ℕ, contraction (bilinear D α β) j •
        commonKernel D α β (k-j) (l-bilinear D α β+j) (Finsupp.single δ p) := by
  rw [actual_ordered_product]
  simp_rw [bilinear_symmetric D β α, kernel_swap D α β δ p]

end
end D5.S3.VertexAlgebra.LatticeActualOrderedProducts

/- Ordered products expressed directly in normalized actual field modes.
The identities are exact corollaries of the proved actual coefficient products;
all finite supports and contractions were derived from the actual definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeActualFieldProducts
open LatticeGeneratingFieldLocality LatticeActualGeneratorLocality LatticeActualOrderedProducts
open scoped VertexOperator
noncomputable section

theorem actual_field_ordered_product (D : LatticeData) (α β δ : Charge D)
    (p : Oscillator D) (m n : ℤ) :
    ((actualField D α)[[m]]) (((actualField D β)[[n]]) (Finsupp.single δ p)) =
      epsilon D α β • ∑ᶠ j : ℕ, contraction (bilinear D α β) j •
        commonKernel D α β (-m-1-bilinear D α β+j) (-n-1-j) (Finsupp.single δ p) := by
  rw [actual_modes,actual_modes]
  exact actual_ordered_product D α β δ p (-m-1) (-n-1)

theorem actual_field_reverse_ordered_product (D : LatticeData) (α β δ : Charge D)
    (p : Oscillator D) (m n : ℤ) :
    ((actualField D β)[[n]]) (((actualField D α)[[m]]) (Finsupp.single δ p)) =
      epsilon D β α • ∑ᶠ j : ℕ, contraction (bilinear D α β) j •
        commonKernel D α β (-m-1-j) (-n-1-bilinear D α β+j) (Finsupp.single δ p) := by
  rw [actual_modes,actual_modes]
  exact actual_reverse_ordered_product D α β δ p (-m-1) (-n-1)

end
end D5.S3.VertexAlgebra.LatticeActualFieldProducts
