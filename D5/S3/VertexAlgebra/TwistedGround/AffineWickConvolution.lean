/- GID: D5/S3/VertexAlgebra/TwistedGround/AffineWickConvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/AffineWickConvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wick regrouping by the positions assigned to each covariance. -/

import D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick

/-! The finite product rule separates correction edges from native Wick edges. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff

namespace D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution

open NativeAffineExternalCoefficient
open NativeAffineTransport (affineExponent)
open OriginalChargedRowSource (affineMoment affineMoment_coefficient)
open AffineOccurrenceWick (wick affineMoment_eq_wick)
open private coordinateJet_contDiff from
  D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient

variable {X : Type*}

/-- Ordered partitions by position. Each position independently belongs to
exactly one subword, and both subwords retain the original order. -/
def partitions : List X → List (List X × List X)
  | [] => [([], [])]
  | a :: l => ((partitions l).map fun p => (a :: p.1, p.2)) ++
      ((partitions l).map fun p => (p.1, a :: p.2))

variable [Fintype X] [DecidableEq X]

private theorem update_contDiff (x : X → ℂ) (a : X) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fun t => Function.update x a t) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = a
  · subst j
    change ContDiff ℂ (⊤ : ℕ∞ω) (fun t : ℂ => Function.update x a t a)
    rw [show (fun t : ℂ => Function.update x a t a) = id from
      funext fun t => Function.update_self a t x]
    exact contDiff_id
  · simpa only [Function.update_of_ne h] using (contDiff_const :
      ContDiff ℂ (⊤ : ℕ∞ω) (fun _ : ℂ => x j))

private theorem derivative_contDiff {f : (X → ℂ) → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (a : X) :
    ContDiff ℂ (⊤ : ℕ∞ω) (coordinateDerivative a f) :=
  coordinateJet_contDiff f hf [a]

private theorem derivative_add {f g : (X → ℂ) → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (hg : ContDiff ℂ (⊤ : ℕ∞ω) g) (a : X) :
    coordinateDerivative a (fun x => f x + g x) =
      fun x => coordinateDerivative a f x + coordinateDerivative a g x := by
  funext x
  exact deriv_add ((hf.comp (update_contDiff x a)).differentiable (by simp) (x a))
    ((hg.comp (update_contDiff x a)).differentiable (by simp) (x a))

private theorem derivative_mul {f g : (X → ℂ) → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (hg : ContDiff ℂ (⊤ : ℕ∞ω) g) (a : X) :
    coordinateDerivative a (fun x => f x * g x) =
      fun x => coordinateDerivative a f x * g x + f x * coordinateDerivative a g x := by
  funext x
  have hd : DifferentiableAt ℂ (fun t => f (Function.update x a t)) (x a) :=
    (hf.comp (update_contDiff x a)).differentiable (by simp) (x a)
  have he : DifferentiableAt ℂ (fun t => g (Function.update x a t)) (x a) :=
    (hg.comp (update_contDiff x a)).differentiable (by simp) (x a)
  simpa only [coordinateDerivative, Function.comp_apply, Function.update_eq_self] using
    (hd.hasDerivAt.fun_mul he.hasDerivAt).deriv

private theorem jet_add (l : List X) {f g : (X → ℂ) → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (hg : ContDiff ℂ (⊤ : ℕ∞ω) g) (x : X → ℂ) :
    coordinateJet l (fun y => f y + g y) x = coordinateJet l f x + coordinateJet l g x := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    simp only [coordinateJet, derivative_add hf hg]
    exact ih (derivative_contDiff hf a) (derivative_contDiff hg a)

private theorem jet_mul (l : List X) {f g : (X → ℂ) → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (hg : ContDiff ℂ (⊤ : ℕ∞ω) g) (x : X → ℂ) :
    coordinateJet l (fun y => f y * g y) x =
      ((partitions l).map fun p => coordinateJet p.1 f x * coordinateJet p.2 g x).sum := by
  induction l generalizing f g with
  | nil => simp [partitions, coordinateJet]
  | cons a l ih =>
    simp only [coordinateJet, derivative_mul hf hg]
    rw [jet_add l ((derivative_contDiff hf a).mul hg) (hf.mul (derivative_contDiff hg a)),
      ih (derivative_contDiff hf a) hg, ih hf (derivative_contDiff hg a)]
    simp [partitions, coordinateJet, List.map_map, Function.comp_def]

private def gaussian (A : Matrix X X ℂ) (μ : X → ℂ) (v : X → ℂ) : ℂ :=
  Complex.exp (MvPolynomial.eval v (affineExponent A μ))

omit [DecidableEq X] in
private theorem gaussian_contDiff (A : Matrix X X ℂ) (μ : X → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (gaussian A μ) := by
  unfold gaussian
  apply ContDiff.cexp
  simp only [affineExponent, FactorialFockQuadraticEstimate.quadratic,
    map_add, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_sum,
    MvPolynomial.eval_X]
  apply ContDiff.add
  · apply contDiff_const.mul
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    fun_prop
  · apply ContDiff.sum
    intro i _
    fun_prop

private theorem jet_gaussian (A : Matrix X X ℂ) (μ : X → ℂ)
    (hs : ∀ i j, A i j = A j i) (l : List X) :
    coordinateJet l (gaussian A μ) 0 = wick A μ l := by
  have h := native_affine_external_jet A μ hs l (jetOccupation l).degree le_rfl
  have hw : (FactorialFockMetric.weight (jetOccupation l) : ℂ) ≠ 0 := by
    exact_mod_cast (FactorialFockMetric.weight_pos (jetOccupation l)).ne'
  rw [← show affineMoment A μ (jetOccupation l) = wick A μ l by
    simpa only [List.map_id, Matrix.submatrix_id_id, Function.comp_id] using
      affineMoment_eq_wick A μ hs id l,
    affineMoment_coefficient, mul_comm]
  exact (div_eq_iff hw).mp h

omit [DecidableEq X] in
private theorem gaussian_add (A C : Matrix X X ℂ) (μ : X → ℂ) :
    gaussian (A + C) μ = fun v => gaussian C 0 v * gaussian A μ v := by
  funext v
  unfold gaussian
  rw [← Complex.exp_add]
  congr 1
  simp only [affineExponent, FactorialFockQuadraticEstimate.quadratic, map_add,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_sum, MvPolynomial.eval_X,
    Matrix.add_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    add_mul, Finset.sum_add_distrib]
  ring

omit [Fintype X] [DecidableEq X] in
/-- Split every edge into native and correction covariance and regroup by
the positions incident to correction edges. The left word has zero mean, so
it contains only correction pairs. The right word retains every native
singleton and both endpoints of every native pair. -/
theorem wick_add_covariance [Finite X] (A C : Matrix X X ℂ) (μ : X → ℂ)
    (hA : ∀ i j, A i j = A j i) (hC : ∀ i j, C i j = C j i) (l : List X) :
    wick (A + C) μ l =
      ((partitions l).map fun p => wick C 0 p.1 * wick A μ p.2).sum := by
  classical
  letI := Fintype.ofFinite X
  have hs (i j : X) : (A + C) i j = (A + C) j i := by
    simp only [Matrix.add_apply, hA i j, hC i j]
  rw [← jet_gaussian (A + C) μ hs l, gaussian_add,
    jet_mul l (gaussian_contDiff C 0) (gaussian_contDiff A μ)]
  simp only [jet_gaussian C 0 hC, jet_gaussian A μ hA]

end D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution
