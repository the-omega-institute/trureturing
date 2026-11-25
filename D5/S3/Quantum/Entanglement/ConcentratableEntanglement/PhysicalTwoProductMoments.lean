/- GID: D5/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ConcentratableEntanglement/PhysicalTwoProductMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Read all positive-order cut moments of an actual coherent two-product amplitude. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Exact spectral moments and a phase-sensitive normalization bound for a coherent sum of two product amplitudes. -/

noncomputable section
namespace D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments

section
open Matrix
open scoped Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The cut amplitude of a coherent sum of two product tensors. The vectors
are arbitrary complex arrays on the left and right cut configurations. -/
private def cutAmplitude (a b : ℂ) (x z : I → ℂ) (y w : J → ℂ) : Matrix I J ℂ :=
  fun i j => (a * x i) * y j + (b * z i) * w j

/-- Unnormalized partial trace over the actual right configurations. -/
private def reduced (C : Matrix I J ℂ) : Matrix I I ℂ :=
  fun i i' => ∑ j, C i j * star (C i' j)

private def pairColumns {I : Type*} (x z : I → ℂ) : Matrix I (Fin 2) ℂ :=
  fun i k => if k = 0 then x i else z i

private def pairRows {J : Type*} (y w : J → ℂ) : Matrix (Fin 2) J ℂ :=
  fun k j => if k = 0 then y j else w j

private def twoGram {I : Type*} [Fintype I] (x z : I → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (pairColumns x z)ᴴ * pairColumns x z

omit [Fintype I] in
private theorem reduced_eq_mul_adj (C : Matrix I J ℂ) : reduced C = C * Cᴴ := by
  ext i i'
  simp [reduced, Matrix.mul_apply]

omit [Fintype I] [Fintype J] in
private theorem literal_factor (a b : ℂ) (x z : I → ℂ) (y w : J → ℂ) :
    cutAmplitude a b x z y w = pairColumns (fun i => a * x i) (fun i => b * z i) * pairRows y w := by
  ext i j
  simp [cutAmplitude, pairColumns, pairRows, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_pow_two_compress {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    trace ((A * B) * (A * B)) = trace ((B * A) * (B * A)) := by
  rw [Matrix.mul_assoc A B (A * B), trace_mul_comm A, ← Matrix.mul_assoc B A B,
      ← Matrix.mul_assoc (B * A) B A]

private theorem trace_det_fin_two (K : Matrix (Fin 2) (Fin 2) ℂ) :
    trace K ^ 2 - trace (K * K) = 2 * K.det := by
  simp only [trace,diag_apply,Matrix.mul_apply,Fin.sum_univ_two,det_fin_two]
  ring

/-- The sum of degree-two principal minors of the actual large reduction is the
product of the two small Gram determinants. No full-rank hypotheses are used. -/
private theorem trace_purity_det_of_two_factors (U : Matrix I (Fin 2) ℂ) (V : Matrix (Fin 2) J ℂ) :
    (trace (reduced (U * V))) ^ 2 - trace (reduced (U * V) * reduced (U * V)) =
      2 * (Uᴴ * U).det * (V * Vᴴ).det := by
  let A : Matrix I (Fin 2) ℂ := U * (V * Vᴴ)
  let B := Uᴴ
  have hactual : reduced (U * V) = A * B := by
    rw [reduced_eq_mul_adj, conjTranspose_mul]
    simp only [A, B, Matrix.mul_assoc]
  rw [hactual, trace_mul_comm A B, trace_pow_two_compress, trace_det_fin_two]
  change 2 * (Uᴴ * (U * (V * Vᴴ))).det = _
  rw [← Matrix.mul_assoc Uᴴ U (V * Vᴴ), det_mul]
  ring

/-- Replacing a right column array by a row array transposes, but does not
change, its Gram determinant. -/
private theorem row_pair_det (y w : J → ℂ) :
    (pairRows y w * (pairRows y w)ᴴ).det = (twoGram y w).det := by
  rw [← Matrix.det_transpose (pairRows y w * (pairRows y w)ᴴ)]
  congr 1
  ext i j
  simp [Matrix.mul_apply, pairRows, pairColumns, twoGram, mul_comm]

/-- The literal physical reduction has the desired Gram factor at every
cut. This identity remains valid when a coefficient or Gram determinant is zero. -/
private theorem literal_trace_purity_det (a b : ℂ) (x z : I → ℂ) (y w : J → ℂ) :
    let ρ := reduced (cutAmplitude a b x z y w)
    trace ρ ^ 2 - trace (ρ * ρ) =
      2 * (twoGram (fun i => a*x i) (fun i => b*z i)).det * (twoGram y w).det := by
  dsimp only
  rw [literal_factor, trace_purity_det_of_two_factors, row_pair_det]
  rfl
end

section
open Matrix
open scoped Matrix

/-- The actual tensor-array inner product, conjugate-linear in the first slot. -/
def overlap {I : Type*} [Fintype I] (x z : I → ℂ) : ℂ :=
  ∑ i, star (x i) * z i

variable {I : Type*} [Fintype I]

private theorem overlap_scale (a b : ℂ) (x z : I → ℂ) :
    overlap (fun i => a * x i) (fun i => b * z i) = (star a * b) * overlap x z := by
  unfold overlap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  ring

private theorem overlap_flip (x z : I → ℂ) : overlap z x = star (overlap x z) := by
  simp [overlap, star_sum, star_mul]

private theorem det_twoGram_expand (x z : I → ℂ) : (twoGram x z).det =
    overlap x x * overlap z z - overlap x z * overlap z x := by
  simp [twoGram, pairColumns, Matrix.det_fin_two, Matrix.mul_apply, overlap]

private theorem det_twoGram_scale (a b : ℂ) (x z : I → ℂ) :
    (twoGram (fun i => a*x i) (fun i => b*z i)).det =
      (star a * a) * (star b * b) * (twoGram x z).det := by
  simp only [det_twoGram_expand, overlap_scale]
  ring

private theorem det_twoGram_unit (x z : I → ℂ) (hx : overlap x x = 1) (hz : overlap z z = 1) :
    (twoGram x z).det = 1 - overlap x z * star (overlap x z) := by
  rw [det_twoGram_expand, hx, hz, one_mul, overlap_flip x z]

/-- Product of all local amplitudes at a basis configuration. Local dimensions
can vary with the site, and the empty tensor is included. -/
private def productArray {ι : Type*} [Fintype ι] {D : ι → Type*}
    (u : ∀ i, D i → ℂ) (x : ∀ i, D i) : ℂ :=
  ∏ i, u i (x i)

private theorem productArray_overlap {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*} [∀ i, Fintype (D i)]
    (x z : ∀ i, D i → ℂ) :
    overlap (productArray x) (productArray z) = ∏ i, overlap (x i) (z i) := by
  classical
  unfold overlap productArray
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [star_prod, Finset.prod_mul_distrib]
end

section
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*} [∀ i, Fintype (D i)]

private abbrev Assign (D : ι → Type*) (S : Finset ι) := ∀ s : S, D s.val
private abbrev Right (S : Finset ι) := (Finset.univ \ S : Finset ι)

private def join (S : Finset ι) (x : Assign D S) (y : Assign D (Right S)) (i : ι) : D i :=
  if h : i ∈ S then x ⟨i,h⟩ else y ⟨i, by simp [Right,h]⟩

omit [∀ i, Fintype (D i)] in
@[simp] private theorem join_left (S : Finset ι) (x : Assign D S) (y : Assign D (Right S))
    (i : S) : join S x y i.val = x i := by simp [join,i.property]

omit [∀ i, Fintype (D i)] in
@[simp] private theorem join_right (S : Finset ι) (x : Assign D S) (y : Assign D (Right S))
    (i : Right S) : join S x y i.val = y i := by
  have hi := (Finset.mem_sdiff.mp i.property).2
  simp [join,hi]

/-- Coherent, unnormalized sum of two literal sitewise product states. -/
private def globalAmplitude (a b : ℂ) (u v : ∀ i, D i → ℂ) (x : ∀ i, D i) : ℂ :=
  a * productArray u x + b * productArray v x

private def physicalCut (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    Matrix (Assign D S) (Assign D (Right S)) ℂ :=
  fun x y => globalAmplitude a b u v (join S x y)

omit [∀ i, Fintype (D i)] in
private theorem productArray_join (u : ∀ i, D i → ℂ) (S : Finset ι)
    (x : Assign D S) (y : Assign D (Right S)) :
    productArray u (join S x y) =
      productArray (fun i : S => u i.val) x * productArray (fun i : Right S => u i.val) y := by
  let f (i : ι) := u i (join S x y i)
  have h := Finset.prod_sdiff (s₁:=S) (s₂:=Finset.univ) (f:=f) (Finset.subset_univ S)
  rw [mul_comm] at h
  rw [Finset.prod_subtype (F := (inferInstance : Fintype ↥S)) S (fun _ => Iff.rfl), Finset.prod_subtype (F := (inferInstance : Fintype ↥(Right S))) (Right S) (fun _ => Iff.rfl)] at h
  simpa [productArray,f] using h.symm

omit [∀ i, Fintype (D i)] in
private theorem physicalCut_eq (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    physicalCut a b u v S =
      cutAmplitude a b
        (productArray (fun i : S => u i.val)) (productArray (fun i : S => v i.val))
        (productArray (fun i : Right S => u i.val)) (productArray (fun i : Right S => v i.val)) := by
  ext x y
  simp only [physicalCut, globalAmplitude, cutAmplitude, productArray_join, mul_assoc]

/-- The product of the local squared overlap magnitudes on a specified side. -/
private def siteOverlapProd (u v : ∀ i, D i → ℂ) (S : Finset ι) : ℝ :=
  ∏ i ∈ S, Complex.normSq (overlap (u i) (v i))

omit [Fintype ι] in
private theorem tensor_Gram_det (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1) (S : Finset ι) :
    (twoGram (productArray (fun i : S => u i.val)) (productArray (fun i : S => v i.val))).det =
      ((1 - siteOverlapProd u v S : ℝ) : ℂ) := by
  rw [det_twoGram_unit]
  · have hnorm (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
    rw [hnorm, productArray_overlap, map_prod]
    unfold siteOverlapProd
    rw [Finset.prod_subtype (F := (inferInstance : Fintype ↥S)) S (fun _ => Iff.rfl)]
    push_cast
    rfl
  · rw [productArray_overlap]; simp [hu]
  · rw [productArray_overlap]; simp [hv]

/-- The actual complex partial trace over the omitted sites obeys the
factorization into squared amplitudes and the two products of local overlaps. -/
private theorem physical_trace_purity_det (a b : ℂ) (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1) (S : Finset ι) :
    let ρ := reduced (physicalCut a b u v S)
    trace ρ ^ 2 - trace (ρ * ρ) =
      (2 * Complex.normSq (a*b) * (1-siteOverlapProd u v S) *
        (1-siteOverlapProd u v (Right S)) : ℝ) := by
  dsimp only
  rw [physicalCut_eq]
  rw [literal_trace_purity_det, det_twoGram_scale, tensor_Gram_det u v hu hv S,
    tensor_Gram_det u v hu hv (Right S)]
  have hn (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj z
  rw [hn,hn,Complex.normSq_mul]
  push_cast
  ring
end

section
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*} [∀ i, Fintype (D i)]

/-- Actual squared mass of the entire unnormalized physical state. -/
def totalMass (a b : ℂ) (u v : ∀ i, D i → ℂ) : ℝ :=
  ∑ x : ∀ i, D i, Complex.normSq (globalAmplitude a b u v x)

private def cutAssignmentEquiv (S : Finset ι) :
    Assign D S × Assign D (Right S) ≃ (∀ i, D i) where
  toFun p := join S p.1 p.2
  invFun x := (fun i => x i.val, fun j => x j.val)
  left_inv p := Prod.ext (funext fun i => join_left S p.1 p.2 i) (funext fun j => join_right S p.1 p.2 j)
  right_inv x := by
    funext i
    by_cases hi : i∈S <;> simp [join,hi]

/-- Exactly the same global mass is obtained by tracing any original cut. -/
private theorem physicalTrace_eq_mass (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    trace (reduced (physicalCut a b u v S)) = (totalMass a b u v : ℂ) := by
  unfold trace reduced totalMass physicalCut
  simp only [Complex.ofReal_sum]
  let f (x : ∀ i, D i) : ℂ := (Complex.normSq (globalAmplitude a b u v x) : ℂ)
  have hr := Equiv.sum_comp (cutAssignmentEquiv (D:=D) S) f
  rw [Fintype.sum_prod_type] at hr
  change (∑ x : Assign D S, ∑ y : Assign D (Right S), _) = (∑ x, f x)
  rw [← hr]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact Complex.mul_conj _

/-- Squared trace normalization is convenient and avoids choosing an amplitude
phase convention: this divides the actual partial trace by the positive mass. -/
private noncomputable def normalizedReduction (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    Matrix (Assign D S) (Assign D S) ℂ :=
  ((totalMass a b u v : ℂ)⁻¹) • reduced (physicalCut a b u v S)

private theorem totalMass_nonneg (a b : ℂ) (u v : ∀ i, D i → ℂ) : 0 ≤ totalMass a b u v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- For a nonzero literal coherent two-product state, the trace is exactly one
and its actual purity deficit is twice the nontrivial Gram determinant. -/
private theorem normalized_trace_purity_det (a b : ℂ) (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1)
    (hN : totalMass a b u v ≠ 0) (S : Finset ι) :
    let ρ := normalizedReduction a b u v S
    trace ρ = 1 ∧
      1 - trace (ρ * ρ) =
      ((2 * Complex.normSq (a*b) * (1-siteOverlapProd u v S) *
        (1-siteOverlapProd u v (Right S))) / (totalMass a b u v)^2 : ℝ) := by
  dsimp only
  let R := reduced (physicalCut a b u v S)
  let N : ℂ := totalMass a b u v
  have hNc : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast hN
  have htr : trace R = N := physicalTrace_eq_mass a b u v S
  have ht : trace (normalizedReduction a b u v S) = 1 := by
    change trace (N⁻¹ • R) = 1
    rw [trace_smul, smul_eq_mul, htr, inv_mul_cancel₀ hNc]
  refine ⟨ht,?_⟩
  have H := physical_trace_purity_det a b u v hu hv S
  change trace R ^ 2 - trace (R * R) = _ at H
  calc
    _ = trace (normalizedReduction a b u v S) ^ 2 -
        trace (normalizedReduction a b u v S * normalizedReduction a b u v S) := by
      rw [ht, one_pow]
    _ = (N⁻¹)^2 * (trace R ^ 2 - trace (R*R)) := by
      change trace (N⁻¹ • R) ^ 2 - trace ((N⁻¹ • R) * (N⁻¹ • R)) = _
      simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_eq_mul]
      ring
    _ = _ := by
      rw [H, inv_pow]
      push_cast
      rw [div_eq_mul_inv, mul_comm]
end

section
open Matrix

private theorem overlap_coherent {I : Type*} [Fintype I] (a b : ℂ) (x z : I → ℂ) :
    overlap (fun i => a*x i+b*z i) (fun i => a*x i+b*z i) =
      (star a*a) * overlap x x + (star b*b) * overlap z z +
        ((star a*b) * overlap x z) + ((star b*a) * overlap z x) := by
  unfold overlap
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_add, star_mul, star_mul]
  ring

/-- Direct finite complex Cauchy–Schwarz for unit arrays, obtained by
subtracting the exact projected component. -/
private theorem unit_overlap_normSq_le_one {I : Type*} [Fintype I] (x z : I → ℂ)
    (hx : overlap x x = 1) (hz : overlap z z = 1) :
    Complex.normSq (overlap x z) ≤ 1 := by
  let h := overlap x z
  let r := fun i => -h*x i + 1*z i
  have hr : overlap r r = 1 - (Complex.normSq h : ℂ) := by
    dsimp only [r]
    rw [overlap_coherent, hx, hz, overlap_flip x z]
    change _ + _ + _ * h + _ * star h = _
    rw [Complex.normSq_eq_conj_mul_self]
    change _ = 1 - star h * h
    simp only [star_neg,star_one]
    ring
  have hpos : 0 ≤ (overlap r r).re := by
    unfold overlap
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    have he : star (r i) * r i = (Complex.normSq (r i) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    rw [he, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  rw [hr, Complex.sub_re,Complex.one_re,Complex.ofReal_re] at hpos
  exact sub_nonneg.mp hpos

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*} [∀ i, Fintype (D i)]

/-- The total normalization retains the coherent cross phase. The trace model
does not replace the true norm by the sum of the two component norms. -/
private theorem totalMass_coherent (a b : ℂ) (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1) :
    totalMass a b u v = Complex.normSq a + Complex.normSq b +
      2 * (((star a)*b) * (∏ i, overlap (u i) (v i))).re := by
  have hn (z : ℂ) : star z * z = (Complex.normSq z : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  let x := productArray u
  let z := productArray v
  let h := (star a*b) * overlap x z
  have cx : overlap x x = 1 := by dsimp [x]; rw [productArray_overlap]; simp [hu]
  have cz : overlap z z = 1 := by dsimp [z]; rw [productArray_overlap]; simp [hv]
  have hh : (star b * a) * overlap z x = star h := by
    rw [overlap_flip x z]
    simp only [h, star_mul, star_star]
    ring
  have hm : (totalMass a b u v : ℂ) =
      overlap (fun i => a*x i+b*z i) (fun i => a*x i+b*z i) := by
    unfold totalMass overlap
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (hn _).symm
  rw [overlap_coherent, cx, cz, hh, hn, hn, mul_one, mul_one] at hm
  have he := congrArg Complex.re hm
  simp only [Complex.ofReal_re, Complex.add_re, Complex.star_def, Complex.conj_re] at he
  change totalMass a b u v = Complex.normSq a + Complex.normSq b + h.re + h.re at he
  have shape : h.re = (((star a)*b) * (∏ i, overlap (u i) (v i))).re := by
    dsimp [h,x,z]
    rw [productArray_overlap]
  rw [shape] at he
  linarith only [he]

/-- Even arbitrarily destructive global phases cannot lower the mass past
the exact two-amplitude bound needed by the virtual midpoint of the cut formula. -/
private theorem totalMass_lower_bound (a b : ℂ) (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1) :
    2 * ‖a‖ * ‖b‖ * (1 - ∏ i, ‖overlap (u i) (v i)‖) ≤ totalMass a b u v := by
  let z := star a * b * (∏ i, overlap (u i) (v i))
  have hz : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hn : ‖z‖ = ‖a‖ * ‖b‖ * ∏ i, ‖overlap (u i) (v i)‖ := by
    simp [z]
  rw [hn] at hz
  rw [totalMass_coherent a b u v hu hv, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  change _ ≤ ‖a‖^2 + ‖b‖^2 + 2*z.re
  nlinarith only [hz, sq_nonneg (‖a‖-‖b‖)]
end

section
open Matrix
open scoped Matrix MatrixOrder ComplexOrder

private theorem small_support_sums {I : Type*} [Fintype I] [DecidableEq I]
    (vals : I → ℝ) (h₀ : ∀ i, 0 ≤ vals i) (h₁ : ∑ i, vals i = 1)
    (hc : Fintype.card {i // vals i ≠ 0} ≤ 2) :
    ∃ σ τ : ℝ, 0 ≤ σ ∧ 0 ≤ τ ∧ σ+τ=1 ∧
      ∀ f : ℝ → ℝ, f 0 = 0 → (∑ i, f (vals i)) = f σ+f τ := by
  classical
  let S := Finset.univ.filter (fun i => vals i ≠ 0)
  have hr (f : ℝ → ℝ) (hf : f 0 = 0) :
      (∑ i, f (vals i)) = ∑ i ∈ S, f (vals i) := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) _).symm
    intro i _ hi
    have hz : vals i = 0 := by simpa [S] using hi
    simp [hz,hf]
  have hs : 0 < S.card := by
    apply Finset.card_pos.mpr
    by_contra! he
    have hh := hr id rfl
    rw [he] at hh
    simp [h₁] at hh
  have ht : S.card ≤ 2 := by
    simpa only [S, Fintype.card_subtype] using hc
  have hcases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with hS|hS
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hS
    refine ⟨vals i, 0, h₀ i, le_rfl, ?_, ?_⟩
    · have q := hr id rfl
      simpa [hi,h₁] using q.symm
    · intro f hf
      rw [hr f hf, hi]
      simp [hf]
  · obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hS
    refine ⟨vals i,vals j,h₀ i,h₀ j,?_,?_⟩
    · have q := hr id rfl
      simpa [he, hij, h₁] using q.symm
    · intro f hf
      rw [hr f hf, he]
      simp [hij]

private theorem trace_cfc_eq_sum {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) (f : ℝ → ℝ) :
    (trace (cfc f ρ)).re = ∑ i, f (h.eigenvalues i) := by
  rw [h.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul]
  simp [Function.comp_def]

/-- All the continuous functional calculus moments of a trace-one PSD matrix
of rank at most two have the same pair of nonnegative spectral coordinates.
Rank one (including a one-dimensional reduction) uses the second value zero. -/
private theorem two_value_cfc {I : Type*} [Fintype I] [DecidableEq I]
    {ρ : Matrix I I ℂ} (hPSD : ρ.PosSemidef) (hrank : ρ.rank ≤ 2) (ht : trace ρ = 1) :
    ∃ σ τ : ℝ, 0 ≤ σ ∧ 0 ≤ τ ∧ σ+τ=1 ∧
      2*σ*τ = 1 - (trace (ρ*ρ)).re ∧
      (∀ f : ℝ → ℝ, f 0 = 0 → (trace (cfc f ρ)).re = f σ+f τ) := by
  let h := hPSD.isHermitian
  let e := h.eigenvalues
  have he : ∀ i, 0 ≤ e i := hPSD.eigenvalues_nonneg
  have hs : ∑ i, e i = 1 := by
    have h₂ := congrArg Complex.re (h.trace_eq_sum_eigenvalues.trans rfl)
    rw [ht, Complex.one_re, Complex.re_sum] at h₂
    simpa [e] using h₂.symm
  have hr : Fintype.card {i // e i ≠ 0} ≤ 2 := h.rank_eq_card_non_zero_eigs ▸ hrank
  obtain ⟨σ,τ,hσ,hτ,hst,hfs⟩ := small_support_sums e he hs hr
  have hm (f : ℝ → ℝ) (hf : f 0 = 0) :
      (trace (cfc f ρ)).re = f σ+f τ := (trace_cfc_eq_sum h f).trans (hfs f hf)
  refine ⟨σ,τ,hσ,hτ,hst,?_ ,hm⟩
  have hp := hm (fun x => x^2) (by simp)
  rw [cfc_pow_id ρ 2 h.isSelfAdjoint, pow_two] at hp
  nlinarith only [hst, sq_nonneg (σ+τ-1), hp, congrArg (fun x : ℝ => x^2) hst]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

omit [∀ i, DecidableEq (D i)] in
private theorem normalized_psd (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    (normalizedReduction a b u v S).PosSemidef := by
  have hn := totalMass_nonneg a b u v
  rw [normalizedReduction, reduced_eq_mul_adj, ← Complex.ofReal_inv]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hn))

omit [∀ i, DecidableEq (D i)] in
private theorem normalized_rank_le_two (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset ι) :
    (normalizedReduction a b u v S).rank ≤ 2 := by
  rw [normalizedReduction, reduced_eq_mul_adj, physicalCut_eq, literal_factor]
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.smul_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- One and the same pair gives the exact physical cut determinant and every
real CFC power moment at positive orders, including rank-one and singleton cuts. -/
private theorem normalized_physical_real_moment (a b : ℂ) (u v : ∀ i, D i → ℂ)
    (hu : ∀ i, overlap (u i) (u i) = 1) (hv : ∀ i, overlap (v i) (v i) = 1)
    (hN : totalMass a b u v ≠ 0) (S : Finset ι) :
    let ρ := normalizedReduction a b u v S
    ∃ σ τ : ℝ, 0 ≤ σ ∧ 0 ≤ τ ∧ σ+τ=1 ∧
      σ*τ = (Complex.normSq (a*b)*(1-siteOverlapProd u v S)*
        (1-siteOverlapProd u v (Right S))) / (totalMass a b u v)^2 ∧
      ∀ K : ℝ, 0 < K → (trace (ρ ^ K)).re = σ^K+τ^K := by
  dsimp only
  have ht := normalized_trace_purity_det a b u v hu hv hN S
  dsimp only at ht
  obtain ⟨σ,τ,hσ,hτ,hst,hdet,hm⟩ :=
    two_value_cfc (normalized_psd a b u v S) (normalized_rank_le_two a b u v S) ht.1
  refine ⟨σ,τ,hσ,hτ,hst,?_,?_⟩
  · have he := congrArg Complex.re ht.2
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at he
    have q := hdet.trans he
    linear_combination q / 2
  · intro K hK
    rw [CFC.rpow_eq_cfc_real (normalized_psd a b u v S).nonneg]
    exact hm _ (Real.zero_rpow (ne_of_gt hK))
end

private def traceMoment (K t : ℝ) := ((1+t)/2)^K+((1-t)/2)^K

private theorem traceMoment_of_product (K eig μ : ℝ) (h : eig+μ=1) :
    traceMoment K (√(1-4*(eig*μ))) = eig^K + μ^K := by
  have eq : 1-4*(eig*μ)=(eig-μ)^2 := by
    have hh := congrArg (fun x : ℝ => x^2) h
    nlinarith
  rw [eq,Real.sqrt_sq_eq_abs]
  by_cases hl : μ ≤ eig
  · rw [abs_of_nonneg (sub_nonneg.mpr hl),traceMoment,
      show (1+(eig-μ))/2=eig by linarith,show (1-(eig-μ))/2=μ by linarith]
  · have hl' : eig ≤ μ := le_of_not_ge hl
    rw [abs_of_nonpos (sub_nonpos.mpr hl'),traceMoment,
      show (1+(-(eig-μ)))/2=μ by linarith,show (1-(-(eig-μ)))/2=eig by linarith,add_comm]

private theorem productSqrt {I : Type*} [Fintype I] (q : I → ℂ) : √(∏ i,Complex.normSq (q i)) = ∏ i, ‖q i‖ := by
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [Finset.prod_pow, Real.sqrt_sq_eq_abs,abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

section
open Matrix
open scoped Classical Matrix MatrixOrder ComplexOrder
universe u v

/-- Real power trace computed by functional calculus on the exact normalized
partial trace of the literal coherent amplitude. -/
def physicalCutMoment (K : ℝ) {I : Type u} [Fintype I] {D : I → Type v}
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] (a b : ℂ) (u v : ∀ i, D i → ℂ) (U : Finset I) : ℝ :=
  (trace ((normalizedReduction a b u v U)^K)).re

/-- The normalization cannot be arbitrarily small relative to the local
overlaps and coefficients. Every actual cut's real power trace is determined
by the two spectral values of a single quadratic with trace one. -/
theorem physical_two_product_moments {K : ℝ} (hK : 0 < K) :
    let observed := @physicalCutMoment.{u,v} K
    ∀ {I : Type u} [Fintype I] {D : I → Type v} [∀ i, Fintype (D i)]
      [∀ i, DecidableEq (D i)] (a b : ℂ) (u v : ∀ i, D i → ℂ),
    (∀ i, overlap (u i) (u i) = 1) →
    (∀ i, overlap (v i) (v i) = 1) →
    totalMass a b u v ≠ 0 →
    let observed := @observed I inferInstance D inferInstance inferInstance a b u v
    let s := fun i => Complex.normSq (overlap (u i) (v i))
    (∀ i, s i ≤ 1) ∧
    2*(‖a‖*‖b‖)*(1-√(∏ i,s i)) ≤ totalMass a b u v ∧
    ∀ U : Finset I,
      let d := (‖a‖*‖b‖/totalMass a b u v)^2 *
        (1-∏ i ∈ U,s i)*(1-∏ i ∈ (Finset.univ \ U),s i)
      let t := √(1-4*d)
      observed U = ((1+t)/2)^K+((1-t)/2)^K := by
  dsimp only
  intro I _ D _ _ a b u v hu hv hn
  refine ⟨fun i => unit_overlap_normSq_le_one (u i) (v i) (hu i) (hv i), ?_, ?_⟩
  · rw [productSqrt (fun i => overlap (u i) (v i))]
    simpa only [mul_assoc] using totalMass_lower_bound a b u v hu hv
  · intro U
    obtain ⟨σ,τ,_,_,hs,hd,hm⟩ := normalized_physical_real_moment a b u v hu hv hn U
    unfold physicalCutMoment
    rw [hm K hK]
    let N := totalMass a b u v
    have e : σ*τ = (‖a‖*‖b‖/N)^2*
      (1-∏ i ∈ U,Complex.normSq (overlap (u i) (v i)))*
      (1-∏ i ∈ (Finset.univ \ U),Complex.normSq (overlap (u i) (v i))) := by
      rw [hd,siteOverlapProd,siteOverlapProd,Complex.normSq_eq_norm_sq,norm_mul]
      unfold Right
      change (‖a‖ * ‖b‖) ^ 2 * _ * _ / N^2 = _
      ring
    change _ = traceMoment K (√(1-4*_))
    rw [← e, traceMoment_of_product K σ τ hs]

end
end D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
