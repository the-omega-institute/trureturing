/- GID: D5/S3/Quantum/AURICOmega/TernaryComparisonProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TernaryComparisonProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Products of ternary comparison structures, with multiplied feature ranks. -/

import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Mathlib.Analysis.Matrix.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-! Products of ternary comparison structures.

On `M × N` the transfer acts componentwise and the reading is the product of the two readings.
The Gram forms of the product reading are nonnegative by the Schur product theorem, feature
ranks multiply through the tensor product of feature maps, and chain connectedness passes from
both factors to the product. Noncommutativity and readings arbitrarily close to zero pass from
the first factor to the product whenever the second carrier is nonempty. -/

open scoped InnerProductSpace Matrix

namespace D5.S3.Quantum.AURICOmega.TernaryComparisonProduct

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

variable {M N : Type*}

/-- The quadratic form of a real square matrix, written as a double sum. -/
private theorem dotProduct_mulVec_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) : star c ⬝ᵥ (A *ᵥ c) = ∑ i, ∑ j, c i * c j * A i j := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Every finite Gram matrix of a ternary comparison reading is positive semidefinite. -/
private theorem gram_posSemidef (C : TernaryComparison M) {n : ℕ} (x : Fin n → M) :
    (Matrix.of fun i j : Fin n => C.kappa (x i) (x j)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    exact C.kappa_symm (x j) (x i)
  · rw [dotProduct_mulVec_eq_sum]
    exact C.kappa_gram_nonneg n x c

/-- The reading is at most one: the Gram form of the pair `x, y` with coefficients `1, -1`
equals `2 - 2 * kappa x y`. -/
private theorem kappa_le_one (C : TernaryComparison M) (x y : M) : C.kappa x y ≤ 1 := by
  have h := C.kappa_gram_nonneg 2 ![x, y] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [C.kappa_self, C.kappa_self, C.kappa_symm y x] at h
  linarith

/-- If a product of two numbers in `[0, 1]` equals one, the first factor equals one. -/
private theorem eq_one_of_mul_eq_one {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hab : a * b = 1) : a = 1 :=
  le_antisymm ha1 (hab ▸ mul_le_of_le_one_right ha hb1)

/-- The product structure on `M × N`: componentwise transfer, multiplied readings. -/
def prod (C : TernaryComparison M) (D : TernaryComparison N) : TernaryComparison (M × N) where
  tri p q r := (C.tri p.1 q.1 r.1, D.tri p.2 q.2 r.2)
  kappa p q := C.kappa p.1 q.1 * D.kappa p.2 q.2
  tri_self_left x z := Prod.ext (C.tri_self_left x.1 z.1) (D.tri_self_left x.2 z.2)
  tri_self_right x z := Prod.ext (C.tri_self_right x.1 z.1) (D.tri_self_right x.2 z.2)
  tri_assoc x y z u v :=
    Prod.ext (C.tri_assoc x.1 y.1 z.1 u.1 v.1) (D.tri_assoc x.2 y.2 z.2 u.2 v.2)
  kappa_symm x y := by
    rw [C.kappa_symm, D.kappa_symm]
  kappa_eq_one_iff x y := by
    change C.kappa x.1 y.1 * D.kappa x.2 y.2 = 1 ↔ x = y
    constructor
    · intro h
      have h1 : C.kappa x.1 y.1 = 1 :=
        eq_one_of_mul_eq_one (C.kappa_nonneg _ _) (kappa_le_one C _ _) (kappa_le_one D _ _) h
      have h2 : D.kappa x.2 y.2 = 1 :=
        eq_one_of_mul_eq_one (D.kappa_nonneg _ _) (kappa_le_one D _ _) (kappa_le_one C _ _)
          (by rw [mul_comm]; exact h)
      exact Prod.ext ((C.kappa_eq_one_iff _ _).mp h1) ((D.kappa_eq_one_iff _ _).mp h2)
    · rintro rfl
      rw [C.kappa_self, D.kappa_self, mul_one]
  kappa_nonneg x y := mul_nonneg (C.kappa_nonneg x.1 y.1) (D.kappa_nonneg x.2 y.2)
  kappa_tri_right x y u v := by
    change C.kappa (C.tri x.1 u.1 v.1) (C.tri y.1 u.1 v.1) *
        D.kappa (D.tri x.2 u.2 v.2) (D.tri y.2 u.2 v.2) = C.kappa x.1 y.1 * D.kappa x.2 y.2
    rw [C.kappa_tri_right, D.kappa_tri_right]
  kappa_tri_left u v x y := by
    change C.kappa (C.tri u.1 v.1 x.1) (C.tri u.1 v.1 y.1) *
        D.kappa (D.tri u.2 v.2 x.2) (D.tri u.2 v.2 y.2) = C.kappa x.1 y.1 * D.kappa x.2 y.2
    rw [C.kappa_tri_left, D.kappa_tri_left]
  kappa_gram_nonneg n x c := by
    have h := ((gram_posSemidef C fun i => (x i).1).hadamard
      (gram_posSemidef D fun i => (x i).2)).dotProduct_mulVec_nonneg c
    rw [dotProduct_mulVec_eq_sum] at h
    simpa only [Matrix.hadamard_apply, Matrix.of_apply] using h

variable (C : TernaryComparison M) (D : TernaryComparison N)

/-- The product reading is the product of the two readings. -/
private theorem prod_kappa (p q : M × N) :
    (prod C D).kappa p q = C.kappa p.1 q.1 * D.kappa p.2 q.2 := rfl

/-- If the readings of the factors are Gram kernels of maps into Euclidean `r`- and
`s`-space, the product reading is the Gram kernel of their tensor product, a map into
Euclidean `r * s`-space. -/
theorem prod_hasFeatureRank {r s : ℕ} (hC : C.HasFeatureRank r) (hD : D.HasFeatureRank s) :
    (prod C D).HasFeatureRank (r * s) := by
  obtain ⟨φ, hφ⟩ := hC
  obtain ⟨ψ, hψ⟩ := hD
  refine ⟨fun p => WithLp.toLp 2 fun k : Fin (r * s) =>
    (φ p.1).ofLp (finProdFinEquiv.symm k).1 * (ψ p.2).ofLp (finProdFinEquiv.symm k).2,
    fun p q => ?_⟩
  rw [prod_kappa, hφ, hψ, EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply]
  ring

/-- If both factors are chain connected, so is the product: move first in the left
coordinate, where the right reading `D.kappa w w` equals one, then in the right coordinate. -/
theorem prod_chainConnected (hC : C.ChainConnected) (hD : D.ChainConnected) :
    (prod C D).ChainConnected := by
  intro ε hε u v
  have h1 : Relation.ReflTransGen (fun a b : M × N => 1 - ε < (prod C D).kappa a b)
      (u.1, u.2) (v.1, u.2) :=
    Relation.ReflTransGen.lift (p := fun a b : M × N => 1 - ε < (prod C D).kappa a b)
      (fun a : M => (a, u.2))
      (fun a b hab => by
        change 1 - ε < C.kappa a b * D.kappa u.2 u.2
        rw [D.kappa_self, mul_one]
        exact hab)
      _ _ (hC ε hε u.1 v.1)
  have h2 : Relation.ReflTransGen (fun a b : M × N => 1 - ε < (prod C D).kappa a b)
      (v.1, u.2) (v.1, v.2) :=
    Relation.ReflTransGen.lift (p := fun a b : M × N => 1 - ε < (prod C D).kappa a b)
      (fun b : N => (v.1, b))
      (fun a b hab => by
        change 1 - ε < C.kappa v.1 v.1 * D.kappa a b
        rw [C.kappa_self, one_mul]
        exact hab)
      _ _ (hD ε hε u.2 v.2)
  exact h1.trans h2

/-- If the left factor is noncommutative, so is the product: place the witnesses at a common
point of `N`. -/
theorem prod_noncommutative_left [Nonempty N] (hC : C.Noncommutative) :
    (prod C D).Noncommutative := by
  obtain ⟨x, y, z, h⟩ := hC
  obtain ⟨w⟩ := ‹Nonempty N›
  exact ⟨(x, w), (y, w), (z, w), fun he => h (congrArg Prod.fst he)⟩

/-- If the readings of the left factor come arbitrarily close to zero, so do the product
readings: place the witnesses at a common point `w` of `N`, where `D.kappa w w = 1`. -/
theorem prod_touchesZero_left [Nonempty N] (hC : C.TouchesZero) : (prod C D).TouchesZero := by
  intro ε hε
  obtain ⟨x, y, h⟩ := hC ε hε
  obtain ⟨w⟩ := ‹Nonempty N›
  refine ⟨(x, w), (y, w), ?_⟩
  rw [prod_kappa, D.kappa_self, mul_one]
  exact h

end D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
