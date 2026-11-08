/- GID: D5/S3/Quantum/Algebra/PBWeightedZeroBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBWeightedZeroBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Original positive pair tables and balancing constrain the same weighted response. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-! Zero budgets of the original positive tables constrain an arbitrary total response. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.PBWeightedZeroBudget

open scoped ComplexOrder
open Matrix

variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

/-- The original directed pair table, before skewness has been recovered. -/
def pairTable (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (f : E →ₗ[ℝ] ℝ) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(f (S a a) : ℂ), (f (S a b) : ℂ) - Complex.I * (f (D a b) : ℂ);
     (f (S b a) : ℂ) - Complex.I * (f (D b a) : ℂ), (f (S b b) : ℂ)]

/-- Only the original pair and balancing constraints are retained here.
The product is the inherited real bilinear symmetric Jordan product.
No linearity or regularity of the total response is asserted. -/
structure OriginalTables (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (C : Set E) (evaluation : I → E →ₗ[ℝ] ℝ) : Prop where
  comm : ∀ a b, S a b = S b a
  exact_cone : ∀ x, x ∈ C ↔ ∀ i, 0 ≤ evaluation i x
  separating : ∀ x y, (∀ i, evaluation i x = evaluation i y) → x = y
  p2 : ∀ a b i, (pairTable S D (evaluation i) a b).PosSemidef
  pb : ∀ a b c i,
    let rPlus := b + D a b - S a c
    let rMinus := b - D a b + S a c
    let sPlus := c + S a b + D a c
    let sMinus := c - S a b - D a c
    evaluation i (S rPlus rPlus + S sPlus sPlus + (2 : ℝ) • D rPlus sPlus) =
      evaluation i (S rMinus rMinus + S sMinus sMinus + (2 : ℝ) • D rMinus sMinus)

/-- An independent derived interface; this is not a field of OriginalTables. -/
def RotationInvariant (D : E → E → E) : Prop :=
  ∀ a b θ, D (Real.cos θ • a - Real.sin θ • b)
    (Real.sin θ • a + Real.cos θ • b) = D a b

variable {S : E →ₗ[ℝ] E →ₗ[ℝ] E} {D : E → E → E}
  {C : Set E} {evaluation : I → E →ₗ[ℝ] ℝ}

private theorem skew (H : OriginalTables S D C evaluation) (a b : E) :
    D b a = -D a b := by
  apply H.separating
  intro i
  have h := congrArg Complex.im
    (congrFun (congrFun (H.p2 a b i).isHermitian 0) 1)
  simpa [pairTable, Matrix.conjTranspose_apply] using h

private theorem quadratic_read (H : OriginalTables S D C evaluation)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x) (a b : E) (z : Fin 2 → ℂ) :
    0 ≤ (star z ⬝ᵥ (pairTable S D f a b *ᵥ z)).re := by
  let q : E :=
    ((z 0).re ^ 2 + (z 0).im ^ 2) • S a a +
    ((z 1).re ^ 2 + (z 1).im ^ 2) • S b b +
    (2 * ((z 0).re * (z 1).re + (z 0).im * (z 1).im)) • S a b +
    (2 * ((z 0).re * (z 1).im - (z 0).im * (z 1).re)) • D a b
  have read (g : E →ₗ[ℝ] ℝ) :
      (star z ⬝ᵥ (pairTable S D g a b *ᵥ z)).re = g q := by
    simp [q, pairTable, dotProduct, mulVec, Fin.sum_univ_two,
      H.comm b a, skew H a b, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    ring
  rw [read]
  apply hf
  apply (H.exact_cone q).mpr
  intro i
  rw [← read]
  exact (H.p2 a b i).re_dotProduct_nonneg z

private theorem positive_pair (H : OriginalTables S D C evaluation)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x) (a b : E) :
    (pairTable S D f a b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairTable, Matrix.conjTranspose_apply, H.comm b a, skew H a b,
        sub_eq_add_neg]
  · intro z
    apply Complex.nonneg_iff.mpr
    refine ⟨quadratic_read H f hf a b z, ?_⟩
    simp [pairTable, dotProduct, mulVec, Fin.sum_univ_two,
      H.comm b a, skew H a b, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
    ring

private theorem null_square_read (H : OriginalTables S D C evaluation)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x) (a b : E)
    (hb : f (S b b) = 0) : f (D a b) = 0 := by
  have h := (positive_pair H f hf a b).dotProduct_mulVec_zero_iff.mp
    (show star (![0, 1] : Fin 2 → ℂ) ⬝ᵥ
      (pairTable S D f a b *ᵥ ![0, 1]) = 0 by
        simp [pairTable, dotProduct, mulVec, Fin.sum_univ_two, hb])
  have hz := congrArg Complex.im (congrFun h 0)
  simpa [pairTable, mulVec, Fin.sum_univ_two] using hz

private theorem zero_right (H : OriginalTables S D C evaluation) (a : E) : D a 0 = 0 := by
  apply H.separating
  intro i
  simpa using null_square_read H (evaluation i)
    (fun x hx => (H.exact_cone x).mp hx i) a 0 (by simp)

private theorem element_pb (H : OriginalTables S D C evaluation) (a b c : E) :
    let ν := D a b - S a c
    let ω := S a b + D a c
    D (b + ν) (c + ω) - D (b - ν) (c - ω) =
      (-2 : ℝ) • S b ν - (2 : ℝ) • S c ω := by
  dsimp only
  rw [show b + (D a b - S a c) = b + D a b - S a c by abel,
    show b - (D a b - S a c) = b - D a b + S a c by abel,
    show c + (S a b + D a c) = c + S a b + D a c by abel,
    show c - (S a b + D a c) = c - S a b - D a c by abel]
  apply H.separating
  intro i
  have hp := H.pb a b c i
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, smul_eq_mul] at hp ⊢
  simp only [H.comm (D a b) b, H.comm (S a c) b,
    H.comm (S a b) c, H.comm (D a c) c,
    H.comm (S a c) (D a b), H.comm (D a c) (S a b)] at hp
  linarith

private theorem second_direction (H : OriginalTables S D C evaluation)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x) (a b : E)
    (hg : f (S (S a b) (S a b)) = 0) : f (S b (D a b)) = 0 := by
  have hp := element_pb H a b 0
  simp only [map_zero, LinearMap.zero_apply, zero_right H, sub_zero, add_zero,
    zero_add, zero_sub, smul_zero] at hp
  have hPlus := null_square_read H f hf (b + D a b) (S a b) hg
  have hMinus := null_square_read H f hf (b - D a b) (-S a b) (by simpa using hg)
  have he := congrArg f hp
  simp only [map_sub, map_smul, smul_eq_mul, hPlus, hMinus] at he
  linarith

/-- The two actual swapped PB instances constrain both directions of the
same original response under a positive read with zero product-square budget. -/
theorem zero_budget_directions (H : OriginalTables S D C evaluation)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x) (a b : E)
    (hg : f (S (S a b) (S a b)) = 0) :
    f (S a (D a b)) = 0 ∧ f (S b (D a b)) = 0 := by
  refine ⟨?_, second_direction H f hf a b hg⟩
  have h := second_direction H f hf b a (by simpa [H.comm b a] using hg)
  simpa [skew H a b] using h

/-- A weighted old value is used literally. Only the independent rotation
interface and a null product-square read are needed for its two directions. -/
theorem weighted_rotated_directions (H : OriginalTables S D C evaluation)
    (rotation : RotationInvariant D) (P F : E) (α β θ : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ x ∈ C, 0 ≤ f x)
    (hg : let r := Real.cos θ • (α • P) - Real.sin θ • (β • F)
          let s := Real.sin θ • (α • P) + Real.cos θ • (β • F)
          f (S (S r s) (S r s)) = 0) :
    f (S P (D (α • P) (β • F))) = 0 ∧
      f (S F (D (α • P) (β • F))) = 0 := by
  have h := zero_budget_directions H f hf
    (Real.cos θ • (α • P) - Real.sin θ • (β • F))
    (Real.sin θ • (α • P) + Real.cos θ • (β • F)) hg
  rw [rotation] at h
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
  have ht := Real.cos_sq_add_sin_sq θ
  have hβ : 0 < β := hα.trans_le hαβ
  have ha : α * f (S P (D (α • P) (β • F))) = 0 := by
    have he : (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        (α * f (S P (D (α • P) (β • F)))) = 0 := by
      linear_combination Real.cos θ * h.1 + Real.sin θ * h.2
    simpa only [ht, one_mul] using he
  have hb : β * f (S F (D (α • P) (β • F))) = 0 := by
    have he : (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        (β * f (S F (D (α • P) (β • F)))) = 0 := by
      linear_combination -Real.sin θ * h.1 + Real.cos θ * h.2
    simpa only [ht, one_mul] using he
  exact ⟨(mul_eq_zero.mp ha).resolve_left (ne_of_gt hα),
    (mul_eq_zero.mp hb).resolve_left (ne_of_gt hβ)⟩

section Ambient

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem ambient_eq_zero (x : A)
    (hx : ∀ g : A →L[ℝ] ℝ, (∀ y : A, 0 ≤ y → 0 ≤ g y) → g x = 0) : x = 0 := by
  have positive (y : A)
      (hy : ∀ g : A →L[ℝ] ℝ, (∀ z : A, 0 ≤ z → 0 ≤ g z) → g y = 0) : 0 ≤ y := by
    by_contra hn
    obtain ⟨g, hg, hneg⟩ :=
      (ProperCone.positive ℝ A).hyperplane_separation_point hn
    have hz := hy g (fun z hz => hg z hz)
    linarith
  have hpos := positive x hx
  have hneg := positive (-x) (by
    intro g hg
    simpa only [map_neg, neg_eq_zero] using hx g hg)
  exact le_antisymm (neg_nonneg.mp hneg) hpos

/-- A null original input annihilates the actual response in every ambient
compression. The multiplier need not be an original input. -/
theorem response_compression_of_annihilation (H : OriginalTables S D C evaluation)
    (ι : E →ₗ[ℝ] A) (hC : ∀ x, x ∈ C ↔ 0 ≤ ι x)
    (hsq : ∀ x, ι (S x x) = ι x * ι x) (a b : E) (z : A)
    (ha : ι a * z = 0) : star z * ι (D a b) * z = 0 := by
  let compression := ContinuousLinearMap.mulLeftRight ℝ A (star z) z
  have hc (x : E) : compression (ι x) = star z * ι x * z := rfl
  have hzero : compression (ι (S a a)) = 0 := by
    rw [hc, hsq]
    simp only [mul_assoc, ha, mul_zero]
  apply ambient_eq_zero
  intro g hg
  let f : E →ₗ[ℝ] ℝ := g.toLinearMap.comp (compression.toLinearMap.comp ι)
  have hf (x : E) (hx : x ∈ C) : 0 ≤ f x :=
    hg _ (star_left_conjugate_nonneg ((hC x).mp hx) z)
  have h := null_square_read H f hf b a (by simp only [f, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, hzero, map_zero])
  simpa only [skew H a b, map_neg, neg_eq_zero, f, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, hc] using h

/-- Null compressed product squares constrain both original directions of
the same weighted old value, in an arbitrary unital complex C* ambient algebra. -/
theorem weighted_compressed_directions (H : OriginalTables S D C evaluation)
    (rotation : RotationInvariant D)
    (ι : E →ₗ[ℝ] A) (hC : ∀ x, x ∈ C ↔ 0 ≤ ι x)
    (hsq : ∀ x, ι (S x x) = ι x * ι x)
    (P F : E) (hP : IsStarProjection (ι P))
    (α β θ : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (z : A)
    (hkernel : let r := Real.cos θ • (α • P) - Real.sin θ • (β • F)
               let s := Real.sin θ • (α • P) + Real.cos θ • (β • F)
               ι (S r s) * z = 0) :
    (1 - ι P) * ι (D (α • P) (β • F)) * (1 - ι P) = 0 ∧
      star z * ι (S P (D (α • P) (β • F))) * z = 0 ∧
        star z * ι (S F (D (α • P) (β • F))) * z = 0 := by
  let r := Real.cos θ • (α • P) - Real.sin θ • (β • F)
  let s := Real.sin θ • (α • P) + Real.cos θ • (β • F)
  change ι (S r s) * z = 0 at hkernel
  let compression := ContinuousLinearMap.mulLeftRight ℝ A (star z) z
  have hc (x : E) : compression (ι x) = star z * ι x * z := rfl
  have hzero : compression (ι (S (S r s) (S r s))) = 0 := by
    rw [hc, hsq]
    simp only [mul_assoc, hkernel, mul_zero]
  have reads (g : A →L[ℝ] ℝ) (hg : ∀ y : A, 0 ≤ y → 0 ≤ g y) :
      g (star z * ι (S P (D (α • P) (β • F))) * z) = 0 ∧
        g (star z * ι (S F (D (α • P) (β • F))) * z) = 0 := by
    let f : E →ₗ[ℝ] ℝ := g.toLinearMap.comp (compression.toLinearMap.comp ι)
    have hf (x : E) (hx : x ∈ C) : 0 ≤ f x :=
      hg _ (star_left_conjugate_nonneg ((hC x).mp hx) z)
    have h := weighted_rotated_directions H rotation P F α β θ hα hαβ f hf
      (by change g (compression (ι (S (S r s) (S r s)))) = 0; rw [hzero, map_zero])
    exact h
  have hp2 : ι P * ι P = ι P := hP.isIdempotentElem
  have hsupport := response_compression_of_annihilation H ι hC hsq
    (α • P) (β • F) (1 - ι P) (by
      rw [map_smul, smul_mul_assoc, mul_sub, mul_one, hp2, sub_self, smul_zero])
  refine ⟨?_, ambient_eq_zero _ (fun g hg => (reads g hg).1),
    ambient_eq_zero _ (fun g hg => (reads g hg).2)⟩
  simpa only [star_sub, star_one, hP.isSelfAdjoint.star_eq] using hsupport

omit [PartialOrder A] [StarOrderedRing A] in
private theorem projection_flip_kernel (p f : A) (hp : p * p = p) (hf : f * f = 1)
    (hpf : p * f + f * p = f)
    (c s β : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    let α := 2*β*s*c
    let k := c^2-s^2
    let r := c • (α • p) - s • (β • f)
    let t := s • (α • p) + c • (β • f)
    ((1/2 : ℝ) • (r*t+t*r)) * (p+k • (f*p)) = 0 := by
  dsimp only
  have hfp : f*p = f-p*f := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hpf
  have hpfp : p*(f*p)=0 := by
    rw [hfp, mul_sub, ← mul_assoc, hp, sub_self]
  have hffp : f*(f*p)=p := by rw [← mul_assoc,hf,one_mul]
  have hid : 4*s^2*c^2+(c^2-s^2)^2=1 := by
    nlinarith [congrArg (fun x : ℝ => x^2) hcs]
  have hg : (1/2 : ℝ) •
      ((c • ((2*β*s*c) • p) - s • (β • f)) *
        (s • ((2*β*s*c) • p) + c • (β • f)) +
       (s • ((2*β*s*c) • p) + c • (β • f)) *
        (c • ((2*β*s*c) • p) - s • (β • f))) =
      (β^2*s*c) • ((4*s^2*c^2) • p + (c^2-s^2) • f - 1) := by
    simp only [mul_add,add_mul,mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm,
      smul_smul,hp,hf,hfp]
    module
  rw [hg, show 4*s^2*c^2=1-(c^2-s^2)^2 by linarith [hid], smul_mul_assoc]
  suffices h : ((1-(c^2-s^2)^2) • p + (c^2-s^2) • f - 1) *
      (p+(c^2-s^2) • (f*p)) = 0 by rw [h,smul_zero]
  simp only [sub_mul,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    hp,hpfp,hffp,one_mul,smul_zero]
  module


/-- The original projection-flip geometry supplies the actual kernel at every
positive ordered pair of weights; no extra kernel premise is needed. -/
theorem projection_flip_weighted_compressions (H : OriginalTables S D C evaluation)
    (rotation : RotationInvariant D)
    (ι : E →ₗ[ℝ] A) (hC : ∀ x, x ∈ C ↔ 0 ≤ ι x)
    (hS : ∀ x y, ι (S x y) = (1/2 : ℝ) • (ι x * ι y + ι y * ι x))
    (P F : E) (hP : IsStarProjection (ι P))
    (hF : ι F * ι F = 1) (hPF : ι P * ι F + ι F * ι P = ι F)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    let θ := Real.arcsin (α / β) / 2
    let k := Real.cos θ ^ 2 - Real.sin θ ^ 2
    let z := ι P + k • (ι F * ι P)
    (1 - ι P) * ι (D (α • P) (β • F)) * (1 - ι P) = 0 ∧
      star z * ι (S P (D (α • P) (β • F))) * z = 0 ∧
        star z * ι (S F (D (α • P) (β • F))) * z = 0 := by
  let θ := Real.arcsin (α / β) / 2
  have hβ : 0 < β := hα.trans_le hαβ
  have hangle : Real.sin (2*θ) = α / β := by
    rw [show 2*θ = Real.arcsin (α/β) by dsimp [θ]; ring]
    exact Real.sin_arcsin (by have hd := div_pos hα hβ; linarith) ((div_le_one hβ).mpr hαβ)
  have halpha : α = 2*β*Real.sin θ*Real.cos θ := by
    rw [Real.sin_two_mul] at hangle
    have hh := (div_eq_iff (ne_of_gt hβ)).mp hangle.symm
    nlinarith [hh]
  have hsq (x : E) : ι (S x x) = ι x * ι x := by rw [hS]; module
  apply weighted_compressed_directions H rotation ι hC hsq P F hP α β θ hα hαβ
  change ι (S (Real.cos θ • (α • P) - Real.sin θ • (β • F))
    (Real.sin θ • (α • P) + Real.cos θ • (β • F))) *
      (ι P + (Real.cos θ ^ 2 - Real.sin θ ^ 2) • (ι F * ι P)) = 0
  rw [hS]
  simp only [map_sub,map_add,map_smul]
  rw [halpha]
  exact projection_flip_kernel (ι P) (ι F) hP.isIdempotentElem hF hPF
    (Real.cos θ) (Real.sin θ) β (Real.cos_sq_add_sin_sq θ)

end Ambient

end D5.S3.Quantum.Algebra.PBWeightedZeroBudget
