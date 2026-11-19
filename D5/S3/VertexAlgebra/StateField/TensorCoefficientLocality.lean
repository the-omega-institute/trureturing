/- GID: D5/S3/VertexAlgebra/StateField/TensorCoefficientLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateField/TensorCoefficientLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Oriented pointwise truncation gives finite tensor convolution and locality. -/

import D5.S3.VertexAlgebra.BinomialKernelDelta
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
The inner mode has a bound on a fixed input. The outer mode has a bound on
each intermediate state, which may depend on the inner index. The finite
convolution and reindexing adapt the private same-order arguments in
`LatticeMatterGhostStateField` to a reusable coefficient statement.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.StateField.TensorCoefficientLocality

open FieldNormalProductLocality (delta commutator)
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

variable {E : Type*} [AddCommGroup E]
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

/-- The inner (second) mode is bounded uniformly in the first mode. The bound on
the first mode can depend on the second mode. -/
def ForwardBounded (F : ℤ → ℤ → E) : Prop :=
  (∃ J : ℤ, ∀ i j : ℤ, J ≤ j → F i j = 0) ∧
    ∀ j : ℤ, ∃ I : ℤ, ∀ i : ℤ, I ≤ i → F i j = 0

/-- For the reverse product, the first mode acts first on the fixed input. -/
def ReverseBounded (F : ℤ → ℤ → E) : Prop :=
  ForwardBounded (fun i j => F j i)

theorem ForwardBounded.shift {F : ℤ → ℤ → E} (h : ForwardBounded F) (a b : ℤ) :
    ForwardBounded (fun i j => F (i + a) (j + b)) := by
  obtain ⟨⟨J, hJ⟩, hI⟩ := h
  refine ⟨⟨J - b, fun i j hj => hJ (i + a) (j + b) (by omega)⟩, fun j => ?_⟩
  obtain ⟨I, hI⟩ := hI (j + b)
  exact ⟨I - a, fun i hi => hI (i + a) (by omega)⟩

private theorem ForwardBounded.combine {F G : ℤ → ℤ → E} (hF : ForwardBounded F)
    (hG : ForwardBounded G) (op : E → E → E) (hzero : op 0 0 = 0) :
    ForwardBounded (fun i j => op (F i j) (G i j)) := by
  obtain ⟨⟨JF, hJF⟩, hIF⟩ := hF
  obtain ⟨⟨JG, hJG⟩, hIG⟩ := hG
  constructor
  · refine ⟨max JF JG, fun i j hj => ?_⟩
    simp only [hJF i j ((le_max_left JF JG).trans hj),
      hJG i j ((le_max_right JF JG).trans hj), hzero]
  · intro j
    obtain ⟨IF, hIF⟩ := hIF j
    obtain ⟨IG, hIG⟩ := hIG j
    refine ⟨max IF IG, fun i hi => ?_⟩
    simp only [hIF i ((le_max_left IF IG).trans hi), hIG i ((le_max_right IF IG).trans hi), hzero]

theorem ForwardBounded.add {F G : ℤ → ℤ → E} (hF : ForwardBounded F)
    (hG : ForwardBounded G) : ForwardBounded (F + G) :=
  hF.combine hG (· + ·) (zero_add 0)

theorem ForwardBounded.sub {F G : ℤ → ℤ → E} (hF : ForwardBounded F)
    (hG : ForwardBounded G) : ForwardBounded (F - G) :=
  hF.combine hG (· - ·) (sub_zero 0)

private theorem delta_eq_shifts (F : ℤ → ℤ → E) :
    delta F = (fun i j => F (i + 1) (j + 0)) - (fun i j => F (i + 0) (j + 1)) := by
  funext i j
  simp only [delta, Pi.sub_apply, add_zero]

theorem ForwardBounded.delta {F : ℤ → ℤ → E} (h : ForwardBounded F) :
    ForwardBounded (delta F) := by
  rw [delta_eq_shifts]
  exact (h.shift 1 0).sub (h.shift 0 1)

theorem ReverseBounded.shift {F : ℤ → ℤ → E} (h : ReverseBounded F) (a b : ℤ) :
    ReverseBounded (fun i j => F (i + a) (j + b)) :=
  ForwardBounded.shift h b a

theorem ReverseBounded.add {F G : ℤ → ℤ → E} (hF : ReverseBounded F)
    (hG : ReverseBounded G) : ReverseBounded (F + G) :=
  ForwardBounded.add hF hG

theorem ReverseBounded.sub {F G : ℤ → ℤ → E} (hF : ReverseBounded F)
    (hG : ReverseBounded G) : ReverseBounded (F - G) :=
  ForwardBounded.sub hF hG

theorem ReverseBounded.delta {F : ℤ → ℤ → E} (h : ReverseBounded F) :
    ReverseBounded (delta F) := by
  rw [delta_eq_shifts]
  exact (h.shift 1 0).sub (h.shift 0 1)

/-- The summand for normalized tensor modes at the two output indices. -/
def summand (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) (m n : ℤ) (z : ℤ × ℤ) : V ⊗[ℂ] U :=
  F z.1 z.2 ⊗ₜ[ℂ] G (m - 1 - z.1) (n - 1 - z.2)

/-- Finiteness of the summand at every output pair. -/
def PairFinite (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) : Prop :=
  ∀ m n : ℤ, Function.HasFiniteSupport (summand F G m n)

/-- The normalized bivariate coefficient convolution. -/
def convolution (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) (m n : ℤ) : V ⊗[ℂ] U :=
  ∑ᶠ z : ℤ × ℤ, summand F G m n z

theorem pairFinite_forward {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (hF : ForwardBounded F) (hG : ForwardBounded G) : PairFinite F G := by
  classical
  obtain ⟨⟨JF, hJF⟩, hIF⟩ := hF
  obtain ⟨⟨JG, hJG⟩, hIG⟩ := hG
  choose IF hIF using hIF
  choose IG hIG using hIG
  intro m n
  let inner := Finset.Icc (n - JG) (JF - 1)
  let outer (j : ℤ) := Finset.Icc (m - IG (n - 1 - j)) (IF j - 1)
  let indices := inner.biUnion (fun j => (outer j).image (fun i => (i, j)))
  apply indices.finite_toSet.subset
  rintro ⟨i, j⟩ hne
  change summand F G m n (i, j) ≠ 0 at hne
  have hj : j ∈ inner := by
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · by_contra h
      exact hne (by simp only [summand, hJG (m - 1 - i) (n - 1 - j) (by omega),
        TensorProduct.tmul_zero])
    · by_contra h
      exact hne (by simp only [summand, hJF i j (by omega), TensorProduct.zero_tmul])
  have hi : i ∈ outer j := by
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · by_contra h
      exact hne (by simp only [summand, hIG (n - 1 - j) (m - 1 - i) (by omega),
        TensorProduct.tmul_zero])
    · by_contra h
      exact hne (by simp only [summand, hIF j i (by omega), TensorProduct.zero_tmul])
  exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem pairFinite_reverse {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (hF : ReverseBounded F) (hG : ReverseBounded G) : PairFinite F G := by
  intro m n
  have h := (pairFinite_forward hF hG n m).fun_comp_of_injective
    (g := Equiv.prodComm ℤ ℤ) (Equiv.prodComm ℤ ℤ).injective
  change Function.HasFiniteSupport (fun z => summand F G m n z)
  simpa only [Function.comp_apply, summand, Equiv.prodComm_apply, Prod.swap] using h

private def translate (a b : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun z := (z.1 + a, z.2 + b)
  invFun z := (z.1 - a, z.2 - b)
  left_inv z := by ext <;> dsimp <;> omega
  right_inv z := by ext <;> dsimp <;> omega

private theorem summand_shift_left (F : ℤ → ℤ → V) (G : ℤ → ℤ → U)
    (m n a b : ℤ) :
    summand (fun i j => F (i + a) (j + b)) G m n =
      summand F G (m + a) (n + b) ∘ translate a b := by
  funext z
  simp only [summand, Function.comp_apply, translate, Equiv.coe_fn_mk]
  rw [show m + a - 1 - (z.1 + a) = m - 1 - z.1 by omega,
    show n + b - 1 - (z.2 + b) = n - 1 - z.2 by omega]

private theorem summand_shift_right (F : ℤ → ℤ → V) (G : ℤ → ℤ → U)
    (m n a b : ℤ) :
    summand F (fun i j => G (i + a) (j + b)) m n =
      summand F G (m + a) (n + b) := by
  funext z
  simp only [summand]
  rw [show m - 1 - z.1 + a = m + a - 1 - z.1 by omega,
    show n - 1 - z.2 + b = n + b - 1 - z.2 by omega]

private theorem PairFinite.shift_left {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) (a b : ℤ) : PairFinite (fun i j => F (i + a) (j + b)) G := by
  intro m n
  rw [summand_shift_left]
  exact (h (m + a) (n + b)).comp_of_injective (translate a b).injective

private theorem PairFinite.shift_right {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) (a b : ℤ) : PairFinite F (fun i j => G (i + a) (j + b)) := by
  intro m n
  rw [summand_shift_right]
  exact h (m + a) (n + b)

private theorem summand_delta_left (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) (m n : ℤ) :
    summand (delta F) G m n =
      summand (fun i j => F (i + 1) (j + 0)) G m n -
        summand (fun i j => F (i + 0) (j + 1)) G m n := by
  funext z
  simp only [summand, delta, add_zero, Pi.sub_apply, TensorProduct.sub_tmul]

private theorem summand_delta_right (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) (m n : ℤ) :
    summand F (delta G) m n =
      summand F (fun i j => G (i + 1) (j + 0)) m n -
        summand F (fun i j => G (i + 0) (j + 1)) m n := by
  funext z
  simp only [summand, delta, add_zero, Pi.sub_apply, TensorProduct.tmul_sub]

theorem PairFinite.delta_left {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) : PairFinite (delta F) G := by
  intro m n
  rw [summand_delta_left]
  exact (h.shift_left 1 0 m n).sub (h.shift_left 0 1 m n)

theorem PairFinite.delta_right {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) : PairFinite F (delta G) := by
  intro m n
  rw [summand_delta_right]
  exact (h.shift_right 1 0 m n).sub (h.shift_right 0 1 m n)

theorem convolution_delta_left {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) : delta (convolution F G) = convolution (delta F) G := by
  funext m n
  have hs (a b : ℤ) :
      (∑ᶠ z, summand (fun i j => F (i + a) (j + b)) G m n z) =
        convolution F G (m + a) (n + b) := by
    simp only [summand_shift_left, convolution]
    exact finsum_comp_equiv (translate a b)
  symm
  change (∑ᶠ z, summand (delta F) G m n z) =
    convolution F G (m + 1) n - convolution F G m (n + 1)
  simp only [summand_delta_left, Pi.sub_apply]
  rw [finsum_sub_distrib (h.shift_left 1 0 m n) (h.shift_left 0 1 m n)]
  simpa only [add_zero] using congrArg₂ (· - ·) (hs 1 0) (hs 0 1)

theorem convolution_delta_right {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) : delta (convolution F G) = convolution F (delta G) := by
  funext m n
  symm
  change (∑ᶠ z, summand F (delta G) m n z) =
    convolution F G (m + 1) n - convolution F G m (n + 1)
  simp only [summand_delta_right, Pi.sub_apply]
  rw [finsum_sub_distrib (h.shift_right 1 0 m n) (h.shift_right 0 1 m n)]
  have hs (a b : ℤ) := congrArg (fun f : ℤ × ℤ → V ⊗[ℂ] U => ∑ᶠ z, f z)
    (summand_shift_right F G m n a b)
  simpa only [convolution, add_zero] using congrArg₂ (· - ·) (hs 1 0) (hs 0 1)

/-- A total of `p + q` differences can be assigned to the two factors separately. -/
theorem convolution_iterate {F : ℤ → ℤ → V} {G : ℤ → ℤ → U}
    (h : PairFinite F G) (p q : ℕ) :
    delta^[p + q] (convolution F G) = convolution (delta^[p] F) (delta^[q] G) := by
  have left (p : ℕ) :
      PairFinite (delta^[p] F) G ∧ delta^[p] (convolution F G) = convolution (delta^[p] F) G := by
    induction p with
    | zero => exact ⟨h, rfl⟩
    | succ p ih =>
      simp only [Function.iterate_succ_apply', ih.2]
      exact ⟨ih.1.delta_left, convolution_delta_left ih.1⟩
  have right (q : ℕ) : PairFinite (delta^[p] F) (delta^[q] G) ∧
      delta^[q] (convolution (delta^[p] F) G) = convolution (delta^[p] F) (delta^[q] G) := by
    induction q with
    | zero => exact ⟨(left p).1, rfl⟩
    | succ q ih =>
      simp only [Function.iterate_succ_apply', ih.2]
      exact ⟨ih.1.delta_right, convolution_delta_right ih.1⟩
  rw [Nat.add_comm p q, Function.iterate_add_apply, (left p).2, (right q).2]

private theorem delta_iterate_sub (N : ℕ) (F G : ℤ → ℤ → E) :
    delta^[N] (F - G) = delta^[N] F - delta^[N] G := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ_apply', ih]
    funext i j
    simp only [delta, Pi.sub_apply]
    abel

/-- Pairwise finite supports and the two factor localities kill the tensor defect. -/
theorem convolution_locality_of_pairFinite
    {F F' : ℤ → ℤ → V} {G G' : ℤ → ℤ → U}
    (forward : PairFinite F G) (reverse : PairFinite F' G') (p q : ℕ)
    (hF : delta^[p] F = delta^[p] F') (hG : delta^[q] G = delta^[q] G') :
    delta^[p + q] (convolution F G - convolution F' G') = 0 := by
  rw [delta_iterate_sub, convolution_iterate forward, convolution_iterate reverse, hF, hG, sub_self]

/-- Opposite product orders each supply their own support for the tensor defect. -/
theorem convolution_locality {F F' : ℤ → ℤ → V} {G G' : ℤ → ℤ → U}
    (hF : ForwardBounded F) (hG : ForwardBounded G)
    (hF' : ReverseBounded F') (hG' : ReverseBounded G') (p q : ℕ)
    (eF : delta^[p] F = delta^[p] F') (eG : delta^[q] G = delta^[q] G') :
    delta^[p + q] (convolution F G - convolution F' G') = 0 :=
  convolution_locality_of_pairFinite (pairFinite_forward hF hG)
    (pairFinite_reverse hF' hG') p q eF eG

private theorem modes_vanish (A : VertexOperator ℂ V) (x : V) :
    ∃ I : ℤ, ∀ i ≥ I, (A[[i]]) x = 0 := by
  refine ⟨-((HahnModule.of ℂ).symm (A x)).order, fun i hi => ?_⟩
  exact VertexOperator.ncoeff_eq_zero_of_lt_order A i x (by omega)

/-- Ordered forward coefficients of genuine vertex operators have oriented bounds. -/
theorem forwardBounded_modes (A B : VertexOperator ℂ V) (x : V) :
    ForwardBounded (fun i j => (A[[i]]) ((B[[j]]) x)) := by
  obtain ⟨J, hJ⟩ := modes_vanish B x
  exact ⟨⟨J, fun i j hj => by simp only [hJ j hj, map_zero]⟩,
    fun j => modes_vanish A ((B[[j]]) x)⟩

/-- In the reverse coefficients the other mode acts on the fixed input. -/
theorem reverseBounded_modes (A B : VertexOperator ℂ V) (x : V) :
    ReverseBounded (fun i j => (B[[j]]) ((A[[i]]) x)) :=
  forwardBounded_modes B A x

private theorem modes_iterate_eq (A B : VertexOperator ℂ V) (x : V) (N : ℕ)
    (h : delta^[N] (commutator A B) = 0) :
    delta^[N] (fun i j => (A[[i]]) ((B[[j]]) x)) =
      delta^[N] (fun i j => (B[[j]]) ((A[[i]]) x)) := by
  have he := BinomialKernelDelta.delta_evaluation (commutator A B) x N
  rw [h] at he
  have he' : delta^[N] ((fun i j => (A[[i]]) ((B[[j]]) x)) -
      (fun i j => (B[[j]]) ((A[[i]]) x))) = 0 := by
    simpa only [FieldNormalProductLocality.commutator, Pi.sub_def, Module.End.mul_apply,
      LinearMap.sub_apply, Pi.zero_def, LinearMap.zero_apply] using he.symm
  rw [delta_iterate_sub, sub_eq_zero] at he'
  exact he'

/-- Tensor coefficient locality for actual vertex-operator modes on a pure input. -/
theorem convolution_mode_locality (A B : VertexOperator ℂ V) (C D : VertexOperator ℂ U)
    (x : V) (y : U) (p q : ℕ) (hAB : delta^[p] (commutator A B) = 0)
    (hCD : delta^[q] (commutator C D) = 0) :
    delta^[p + q]
      (convolution (fun i j => (A[[i]]) ((B[[j]]) x)) (fun i j => (C[[i]]) ((D[[j]]) y)) -
        convolution (fun i j => (B[[j]]) ((A[[i]]) x)) (fun i j => (D[[j]]) ((C[[i]]) y))) = 0 :=
  convolution_locality (forwardBounded_modes A B x) (forwardBounded_modes C D y)
    (reverseBounded_modes A B x) (reverseBounded_modes C D y) p q
    (modes_iterate_eq A B x p hAB) (modes_iterate_eq C D y q hCD)

private theorem convolution_transpose (F : ℤ → ℤ → V) (G : ℤ → ℤ → U) (m n : ℤ) :
    convolution (fun i j => F j i) (fun i j => G j i) m n = convolution F G n m :=
  finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := summand F G n m)

/-- The ordered-product coefficient formula on pure tensors implies uniform
operator locality for a pair of tensor fields. Each product formula lists
its outer mode first. -/
theorem tensorField_locality_of_ordered_products
    (A B : VertexOperator ℂ V) (C D : VertexOperator ℂ U)
    (P Q : VertexOperator ℂ (V ⊗[ℂ] U)) (p q : ℕ)
    (hAB : delta^[p] (commutator A B) = 0) (hCD : delta^[q] (commutator C D) = 0)
    (hPQ : ∀ (x : V) (y : U) (m n : ℤ),
      (P[[m]]) ((Q[[n]]) (x ⊗ₜ[ℂ] y)) =
        convolution (fun i j => (A[[i]]) ((B[[j]]) x)) (fun i j => (C[[i]]) ((D[[j]]) y)) m n)
    (hQP : ∀ (x : V) (y : U) (n m : ℤ),
      (Q[[n]]) ((P[[m]]) (x ⊗ₜ[ℂ] y)) =
        convolution (fun j i => (B[[j]]) ((A[[i]]) x)) (fun j i => (D[[j]]) ((C[[i]]) y)) n m) :
    delta^[p + q] (commutator P Q) = 0 := by
  funext m n
  apply TensorProduct.ext'
  intro x y
  let F := fun i j => (A[[i]]) ((B[[j]]) x)
  let G := fun i j => (C[[i]]) ((D[[j]]) y)
  let F' := fun i j => (B[[j]]) ((A[[i]]) x)
  let G' := fun i j => (D[[j]]) ((C[[i]]) y)
  have hexpand :
      (fun r s => commutator P Q r s (x ⊗ₜ[ℂ] y)) = convolution F G - convolution F' G' := by
    funext r s
    change (P[[r]]) ((Q[[s]]) (x ⊗ₜ[ℂ] y)) - (Q[[s]]) ((P[[r]]) (x ⊗ₜ[ℂ] y)) =
      convolution F G r s - convolution F' G' r s
    rw [hPQ, hQP]
    exact congrArg (convolution F G r s - ·) (convolution_transpose F' G' s r)
  have heval := BinomialKernelDelta.delta_evaluation (commutator P Q) (x ⊗ₜ[ℂ] y) (p + q)
  rw [hexpand, convolution_mode_locality A B C D x y p q hAB hCD] at heval
  exact congrFun (congrFun heval m) n

#print axioms pairFinite_forward
#print axioms pairFinite_reverse
#print axioms convolution_delta_left
#print axioms convolution_delta_right
#print axioms convolution_iterate
#print axioms convolution_locality
#print axioms convolution_mode_locality
#print axioms tensorField_locality_of_ordered_products

end

end D5.S3.VertexAlgebra.StateField.TensorCoefficientLocality
