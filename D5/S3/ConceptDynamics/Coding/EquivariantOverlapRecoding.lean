/- GID: D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Overlap recoding transports group coordinates by a constructed boundary cocycle. -/

import D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding

open D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy

universe u v w z h

variable {U : Type u} {V : Type v} {I : Type w} {J : Type z}
  {H : Type h} [Group H]

/-- Move the boundary across the first half-edge. -/
def encode (d : Boundary U V I J) (alpha : U → H)
    (p : LeftPath d × H) : RightPath d × H :=
  (forward d p.1, p.2 * alpha (p.1.val 0).1)

/-- The preceding output supplies the missing half-edge and its inverse group label. -/
def decode (d : Boundary U V I J) (alpha : U → H)
    (p : RightPath d × H) : LeftPath d × H :=
  (backward d p.1, p.2 * (alpha (p.1.val (-1)).2)⁻¹)

@[simp] theorem decode_encode (d : Boundary U V I J) (alpha : U → H)
    (p : LeftPath d × H) : decode d alpha (encode d alpha p) = p := by
  apply Prod.ext
  · exact backward_forward d p.1
  · simp [decode, encode, forward, mul_assoc]

@[simp] theorem encode_decode (d : Boundary U V I J) (alpha : U → H)
    (p : RightPath d × H) : encode d alpha (decode d alpha p) = p := by
  apply Prod.ext
  · exact forward_backward d p.1
  · simp [decode, encode, backward, mul_assoc]

/-- Both inverse laws are proved for the explicit coordinate formulas. -/
def skewEquiv (d : Boundary U V I J) (alpha : U → H) :
    LeftPath d × H ≃ RightPath d × H where
  toFun := encode d alpha
  invFun := decode d alpha
  left_inv := decode_encode d alpha
  right_inv := encode_decode d alpha

/-- One step of the UV-labelled group extension. -/
def leftStep (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : LeftPath d × H) : LeftPath d × H :=
  (leftShift d p.1, p.2 * (alpha (p.1.val 0).1 * beta (p.1.val 0).2))

/-- One step of the VU-labelled group extension. -/
def rightStep (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : RightPath d × H) : RightPath d × H :=
  (rightShift d p.1, p.2 * (beta (p.1.val 0).1 * alpha (p.1.val 0).2))

/-- Multiplication order is preserved even when H is noncommutative. -/
theorem encode_step (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : LeftPath d × H) :
    encode d alpha (leftStep d alpha beta p) =
      rightStep d alpha beta (encode d alpha p) := by
  apply Prod.ext
  · exact forward_shift d p.1
  · simp [encode, leftStep, rightStep, leftShift, forward, mul_assoc]

theorem decode_step (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : RightPath d × H) :
    decode d alpha (rightStep d alpha beta p) =
      leftStep d alpha beta (decode d alpha p) := by
  apply (skewEquiv d alpha).injective
  change encode d alpha (decode d alpha (rightStep d alpha beta p)) =
    encode d alpha (leftStep d alpha beta (decode d alpha p))
  rw [encode_decode, encode_step, encode_decode]

/-- The left group action on an extension. -/
def translate {X : Type*} (g : H) (p : X × H) : X × H := (p.1, g * p.2)

theorem encode_equivariant (d : Boundary U V I J) (alpha : U → H)
    (g : H) (p : LeftPath d × H) :
    encode d alpha (translate g p) = translate g (encode d alpha p) := by
  apply Prod.ext
  · rfl
  · simp [encode, translate, mul_assoc]

theorem decode_equivariant (d : Boundary U V I J) (alpha : U → H)
    (g : H) (p : RightPath d × H) :
    decode d alpha (translate g p) = translate g (decode d alpha p) := by
  apply Prod.ext
  · rfl
  · simp [decode, translate, mul_assoc]

/-- The transfer function is read from a half-edge, rather than assumed to exist. -/
def transfer (d : Boundary U V I J) (alpha : U → H) (x : LeftPath d) : H :=
  alpha (x.val 0).1

theorem transfer_cocycle (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (x : LeftPath d) :
    (alpha (x.val 0).1 * beta (x.val 0).2) * transfer d alpha (leftShift d x) =
      transfer d alpha x *
        (beta ((forward d x).val 0).1 * alpha ((forward d x).val 0).2) := by
  simp [transfer, forward, leftShift, mul_assoc]

section Topology

variable [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace H]
  [IsTopologicalGroup H]

theorem continuous_encode (d : Boundary U V I J) (alpha : U → H)
    (ha : Continuous alpha) : Continuous (encode d alpha) := by
  have hc : Continuous (fun p : LeftPath d × H => alpha (p.1.val 0).1) :=
    ha.comp (((continuous_apply (0 : ℤ)).comp
      (continuous_subtype_val.comp continuous_fst)).fst)
  exact ((continuous_forward d).comp continuous_fst).prodMk (continuous_snd.mul hc)

theorem continuous_decode (d : Boundary U V I J) (alpha : U → H)
    (ha : Continuous alpha) : Continuous (decode d alpha) := by
  have hc : Continuous (fun p : RightPath d × H => alpha (p.1.val (-1)).2) :=
    ha.comp (((continuous_apply (-1 : ℤ)).comp
      (continuous_subtype_val.comp continuous_fst)).snd)
  exact ((continuous_backward d).comp continuous_fst).prodMk (continuous_snd.mul hc.inv)

/-- An explicitly constructed homeomorphism of the two group extensions. -/
def skewHomeomorph (d : Boundary U V I J) (alpha : U → H) (ha : Continuous alpha) :
    LeftPath d × H ≃ₜ RightPath d × H where
  toEquiv := skewEquiv d alpha
  continuous_toFun := continuous_encode d alpha ha
  continuous_invFun := continuous_decode d alpha ha

end Topology

#print axioms decode_encode
#print axioms encode_decode
#print axioms encode_step
#print axioms encode_equivariant
#print axioms transfer_cocycle
#print axioms skewHomeomorph

end D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
