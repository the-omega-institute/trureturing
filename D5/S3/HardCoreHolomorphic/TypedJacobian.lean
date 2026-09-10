/- GID: D5/S3/HardCoreHolomorphic/TypedJacobian
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/TypedJacobian
   mirror-E: none(waiver:actual-holomorphic-map-and-derivative)
   anchors: []
   digest: One logarithm defines every pruned transformed recursion and its full differential. -/

import D5.S3.HardCoreHolomorphic.AffineChart

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.TypedJacobian
open scoped BigOperators
open D5.S3.HardCoreHolomorphic.AffineChart

variable {ι : Type*} [DecidableEq ι]

/-- Product over precisely the retained children; an empty product is one. -/
def messageProduct (s : Finset ι) (a b : ι → ℂ) (m : ι → ℂ) : ℂ :=
  ∏ j ∈ s, inverse (a j) (b j) (m j)

/-- The single log argument. It is positive on the real box and has no
vanishing issue at activity zero, where it equals b0-a0. -/
def logArgument (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ) (z : ℂ) (m : ι → ℂ) : ℂ :=
  b0-a0+b0*z*messageProduct s a b m

/-- Actual transformed hard-core map. There is no logarithm of the activity. -/
def rowMap (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ) (z : ℂ) (m : ι → ℂ) : ℂ :=
  -Complex.log (logArgument s a0 b0 a b z m)/b0

/-- Coefficients of the full differential in the child coordinates. -/
def jacobianEntry (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ)
    (z : ℂ) (m : ι → ℂ) (j : ι) : ℂ :=
  -(z*messageProduct s a b m*psi (a j) (b j) (inverse (a j) (b j) (m j))) /
    logArgument s a0 b0 a b z m

/-- Coefficient of activity variation in the same differential. -/
def activityEntry (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ)
    (z : ℂ) (m : ι → ℂ) : ℂ :=
  -messageProduct s a b m/logArgument s a0 b0 a b z m

private theorem prod_hasDerivAt (s : Finset ι) (f : ι → ℂ → ℂ)
    (r : ι → ℂ) (t : ℂ)
    (hf : ∀ j ∈ s, HasDerivAt (f j) (f j t*r j) t) :
    HasDerivAt (fun u => ∏ j ∈ s, f j u)
      ((∏ j ∈ s, f j t)*(∑ j ∈ s, r j)) t := by
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simpa using hasDerivAt_const t (1:ℂ)
  | @insert j s hj ih =>
      intro hf
      have h := (hf j (Finset.mem_insert_self _ _)).mul
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
      convert! h using 1
      · ext u
        simp [Finset.prod_insert, hj]
      · simp [Finset.prod_insert, Finset.sum_insert, hj]
        ring

/-- The derivative along every differentiable complex input curve. Since both
activity and all child tangent values are arbitrary, this identifies the full
Jacobian, including mixed simultaneous input perturbations and all pruning sets. -/
theorem rowMap_hasDerivAt (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ)
    (z : ℂ → ℂ) (m : ι → ℂ → ℂ) (t z' : ℂ) (m' : ι → ℂ)
    (hb : b0 ≠ 0) (hz : HasDerivAt z z' t)
    (hm : ∀ j ∈ s, HasDerivAt (m j) (m' j) t)
    (hd : ∀ j ∈ s, 1+a j*Complex.exp (b j*m j t) ≠ 0)
    (hH : logArgument s a0 b0 a b (z t) (fun j => m j t) ∈ Complex.slitPlane) :
    HasDerivAt (fun u => rowMap s a0 b0 a b (z u) (fun j => m j u))
      (activityEntry s a0 b0 a b (z t) (fun j => m j t)*z' +
        ∑ j ∈ s, jacobianEntry s a0 b0 a b (z t) (fun j => m j t) j*m' j) t := by
  let x : ι → ℂ := fun j => inverse (a j) (b j) (m j t)
  have hi (j) (hj : j ∈ s) :
      HasDerivAt (fun u => inverse (a j) (b j) (m j u))
        (x j*(psi (a j) (b j) (x j)*m' j)) t := by
    convert! (inverse_hasDerivAt (a j) (b j) (m j t) (hd j hj)).comp t (hm j hj) using 1 <;>
      dsimp [x] <;> ring
  have hp := prod_hasDerivAt s (fun j u => inverse (a j) (b j) (m j u))
    (fun j => psi (a j) (b j) (x j)*m' j) t hi
  have hh := ((((hz.const_mul b0).mul hp).const_add (b0-a0)).clog hH).neg.div_const b0
  have hn : logArgument s a0 b0 a b (z t) (fun j => m j t) ≠ 0 :=
    Complex.slitPlane_ne_zero hH
  convert! hh using 1
  dsimp [activityEntry, jacobianEntry, logArgument, messageProduct, x]
  have hs : (∑ j ∈ s,
      -(z t*(∏ k ∈ s, inverse (a k) (b k) (m k t))*
        psi (a j) (b j) (inverse (a j) (b j) (m j t))) /
          (b0-a0+b0*z t*(∏ k ∈ s, inverse (a k) (b k) (m k t)))*m' j) =
      -(z t*(∏ k ∈ s, inverse (a k) (b k) (m k t)) /
        (b0-a0+b0*z t*(∏ k ∈ s, inverse (a k) (b k) (m k t)))) *
        (∑ j ∈ s, psi (a j) (b j) (inverse (a j) (b j) (m j t))*m' j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj; ring
  rw [hs]
  field_simp [hb, hn] <;> ring

/-- Joint holomorphy of the actual finite-dimensional map on its pole-free
principal-log domain; it is not inferred just from a pointwise Jacobian fit. -/
theorem rowMap_differentiableAt [Fintype ι] (s : Finset ι)
    (a0 b0 : ℂ) (a b : ι → ℂ) (p : ℂ × (ι → ℂ))
    (hd : ∀ j ∈ s, 1+a j*Complex.exp (b j*p.2 j) ≠ 0)
    (hH : logArgument s a0 b0 a b p.1 p.2 ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun q : ℂ × (ι → ℂ) => rowMap s a0 b0 a b q.1 q.2) p := by
  have hi (j) (hj : j ∈ s) :
      DifferentiableAt ℂ (fun q : ℂ × (ι → ℂ) => inverse (a j) (b j) (q.2 j)) p := by
    have hproj : DifferentiableAt ℂ (fun q : ℂ × (ι → ℂ) => q.2 j) p := by
      fun_prop
    exact (inverse_hasDerivAt (a j) (b j) (p.2 j) (hd j hj)).differentiableAt.comp p
      hproj
  have hp : DifferentiableAt ℂ
      (fun q : ℂ × (ι → ℂ) => messageProduct s a b q.2) p := by
    unfold messageProduct
    exact (HasFDerivAt.finsetProd (fun j hj => (hi j hj).hasFDerivAt)).differentiableAt
  have hh : DifferentiableAt ℂ
      (fun q : ℂ × (ι → ℂ) => logArgument s a0 b0 a b q.1 q.2) p := by
    dsimp [logArgument]
    fun_prop
  simpa only [rowMap, div_eq_mul_inv, Pi.neg_apply] using (hh.clog hH).neg.mul_const b0⁻¹

/-- Inverse coordinates return the actual vacancy recursion. Both possible
rational poles are stated; the quantitative tube later excludes them uniformly. -/
theorem inverse_rowMap (s : Finset ι) (a0 b0 : ℂ) (a b : ι → ℂ)
    (z : ℂ) (m : ι → ℂ) (hb : b0 ≠ 0)
    (hH : logArgument s a0 b0 a b z m ≠ 0)
    (hD : 1+z*messageProduct s a b m ≠ 0) :
    inverse a0 b0 (rowMap s a0 b0 a b z m) =
      (1+z*messageProduct s a b m)⁻¹ := by
  have he : b0*rowMap s a0 b0 a b z m = -Complex.log (logArgument s a0 b0 a b z m) := by
    dsimp [rowMap]; field_simp [hb]
  rw [inverse, he, Complex.exp_neg, Complex.exp_log hH]
  dsimp [logArgument] at hH ⊢
  have hden : b0-a0+b0*z*messageProduct s a b m+a0 ≠ 0 := by
    convert mul_ne_zero hb hD using 1 <;> ring
  field_simp [hb, hH, hD, hden]
  ring

/-- The Jacobian entry is exactly the previously certified message ratio.
This is a rational identity; no assumed derivative identification is used. -/
theorem jacobian_vacancy_identity (s : Finset ι) (a0 b0 : ℂ)
    (a b : ι → ℂ) (z : ℂ) (m : ι → ℂ) (j : ι)
    (hD : 1+z*messageProduct s a b m ≠ 0)
    (hH : logArgument s a0 b0 a b z m ≠ 0) :
    let y := (1+z*messageProduct s a b m)⁻¹
    jacobianEntry s a0 b0 a b z m j =
      -(1-y)*psi (a j) (b j) (inverse (a j) (b j) (m j))/psi a0 b0 y := by
  dsimp [jacobianEntry, psi, logArgument] at hH ⊢
  field_simp [hD, hH] <;> ring

#print axioms rowMap_hasDerivAt
#print axioms rowMap_differentiableAt
#print axioms inverse_rowMap
#print axioms jacobian_vacancy_identity
end D5.S3.HardCoreHolomorphic.TypedJacobian
