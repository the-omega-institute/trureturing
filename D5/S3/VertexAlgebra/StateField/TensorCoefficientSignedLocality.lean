/- GID: D5/S3/VertexAlgebra/StateField/TensorCoefficientSignedLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateField/TensorCoefficientSignedLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary matter locality and signed ghost locality give signed tensor locality. -/

import D5.S3.VertexAlgebra.StateField.TensorCoefficientLocality

/-! The scalar on the reverse ghost modes can be absorbed before applying ordinary
finite-convolution locality. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.StateField.TensorCoefficientSignedLocality

open FieldNormalProductLocality (commutator delta deltaEnd)
open TensorCoefficientLocality
open scoped BigOperators TensorProduct VertexOperator

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

private theorem convolution_signed_locality_of_pairFinite
    {F F' : ℤ → ℤ → V} {G G' : ℤ → ℤ → U}
    (forward : PairFinite F G) (reverse : PairFinite F' G') (s : ℂ) (p q : ℕ)
    (hF : delta^[p] F = delta^[p] F') (hG : delta^[q] G = delta^[q] (s • G')) :
    delta^[p + q] (convolution F G - s • convolution F' G') = 0 := by
  have hsummand (m n : ℤ) : summand F' (s • G') m n =
      fun z => s • summand F' G' m n z := by
    funext z
    simp only [summand, Pi.smul_apply, TensorProduct.tmul_smul]
  have hfinite : PairFinite F' (s • G') := by
    intro m n
    rw [hsummand]
    exact Function.HasFiniteSupport.smul_right (fun _ => s) (reverse m n)
  have hconv : convolution F' (s • G') = s • convolution F' G' := by
    funext m n
    simp only [convolution, hsummand, Pi.smul_apply, smul_finsum' s (reverse m n)]
  rw [← hconv]
  exact convolution_locality_of_pairFinite forward hfinite p q hF hG

private theorem delta_iterate_eq_on_input {F G : ℤ → ℤ → Module.End ℂ V}
    (x : V) (N : ℕ) (h : delta^[N] (F - G) = 0) :
    delta^[N] (fun i j => F i j x) = delta^[N] (fun i j => G i j x) := by
  let Δ : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := deltaEnd
  change Δ^[N] (F - G) = 0 at h
  rw [← Module.End.pow_apply, map_sub, sub_eq_zero, Module.End.pow_apply,
    Module.End.pow_apply] at h
  rw [← BinomialKernelDelta.delta_evaluation, ← BinomialKernelDelta.delta_evaluation]
  exact congrArg (fun T : ℤ → ℤ → Module.End ℂ V => fun i j => T i j x) h

/-- Ordinary locality of the matter modes and signed locality of the ghost modes
give signed locality of tensor modes under the two ordered product formulas.
Each formula lists its outer mode first. -/
theorem tensorField_signed_locality_of_ordered_products
    (A B : VertexOperator ℂ V) (C D : VertexOperator ℂ U)
    (P Q : VertexOperator ℂ (V ⊗[ℂ] U)) (s : ℂ) (p q : ℕ)
    (hAB : delta^[p] (commutator A B) = 0)
    (hCD : delta^[q] (fun i j => (C[[i]]) * (D[[j]]) - s • ((D[[j]]) * (C[[i]]))) = 0)
    (hPQ : ∀ (x : V) (y : U) (m n : ℤ),
      (P[[m]]) ((Q[[n]]) (x ⊗ₜ[ℂ] y)) =
        convolution (fun i j => (A[[i]]) ((B[[j]]) x)) (fun i j => (C[[i]]) ((D[[j]]) y)) m n)
    (hQP : ∀ (x : V) (y : U) (n m : ℤ),
      (Q[[n]]) ((P[[m]]) (x ⊗ₜ[ℂ] y)) =
        convolution (fun j i => (B[[j]]) ((A[[i]]) x)) (fun j i => (D[[j]]) ((C[[i]]) y)) n m) :
    delta^[p + q] (fun m n => (P[[m]]) * (Q[[n]]) - s • ((Q[[n]]) * (P[[m]]))) = 0 := by
  funext m n
  apply TensorProduct.ext'
  intro x y
  let F := fun i j => (A[[i]]) ((B[[j]]) x)
  let G := fun i j => (C[[i]]) ((D[[j]]) y)
  let F' := fun i j => (B[[j]]) ((A[[i]]) x)
  let G' := fun i j => (D[[j]]) ((C[[i]]) y)
  have hF : delta^[p] F = delta^[p] F' :=
    delta_iterate_eq_on_input (F := fun i j => (A[[i]]) * (B[[j]]))
      (G := fun i j => (B[[j]]) * (A[[i]])) x p hAB
  have hG : delta^[q] G = delta^[q] (s • G') :=
    delta_iterate_eq_on_input (F := fun i j => (C[[i]]) * (D[[j]]))
      (G := fun i j => s • ((D[[j]]) * (C[[i]]))) y q hCD
  have hlocal := convolution_signed_locality_of_pairFinite
    (pairFinite_forward (forwardBounded_modes A B x) (forwardBounded_modes C D y))
    (pairFinite_reverse (reverseBounded_modes A B x) (reverseBounded_modes C D y)) s p q hF hG
  have hreverse (i j : ℤ) : (Q[[j]]) ((P[[i]]) (x ⊗ₜ[ℂ] y)) = convolution F' G' i j := by
    rw [hQP]
    exact finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := summand F' G' i j)
  let defect := fun i j => (P[[i]]) * (Q[[j]]) - s • ((Q[[j]]) * (P[[i]]))
  have hexpand : (fun i j => defect i j (x ⊗ₜ[ℂ] y)) =
      convolution F G - s • convolution F' G' := by
    funext i j
    simp only [defect, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      Pi.sub_apply, Pi.smul_apply, hPQ, hreverse, F, G]
  have heval := BinomialKernelDelta.delta_evaluation defect (x ⊗ₜ[ℂ] y) (p + q)
  rw [hexpand, hlocal] at heval
  exact congrFun (congrFun heval m) n

#print axioms tensorField_signed_locality_of_ordered_products

end D5.S3.VertexAlgebra.StateField.TensorCoefficientSignedLocality
