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

/-- Both inverse laws are proved for the explicit coordinate formulas. -/
def skewEquiv (d : Boundary U V I J) (alpha : U → H) :
    LeftPath d × H ≃ RightPath d × H where
  toFun := encode d alpha
  invFun := decode d alpha
  left_inv := by
    intro p
    apply Prod.ext
    · exact (pathEquiv d).left_inv p.1
    · simp [decode, encode, forward, mul_assoc]
  right_inv := by
    intro p
    apply Prod.ext
    · exact (pathEquiv d).right_inv p.1
    · simp [decode, encode, backward, mul_assoc]

/-- One step of the UV-labelled group extension. -/
def leftStep (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : LeftPath d × H) : LeftPath d × H :=
  (leftShift d p.1, p.2 * (alpha (p.1.val 0).1 * beta (p.1.val 0).2))

/-- One step of the VU-labelled group extension. -/
def rightStep (d : Boundary U V I J) (alpha : U → H) (beta : V → H)
    (p : RightPath d × H) : RightPath d × H :=
  (rightShift d p.1, p.2 * (beta (p.1.val 0).1 * alpha (p.1.val 0).2))

/-- The left group action on an extension. -/
def translate {X : Type*} (g : H) (p : X × H) : X × H := (p.1, g * p.2)

section Topology

variable [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- An explicitly constructed homeomorphism of the two group extensions. -/
def skewHomeomorph (d : Boundary U V I J) (alpha : U → H) (ha : Continuous alpha) :
    LeftPath d × H ≃ₜ RightPath d × H where
  toEquiv := skewEquiv d alpha
  continuous_toFun := by
    have hc : Continuous (fun p : LeftPath d × H => alpha (p.1.val 0).1) :=
      ha.comp (((continuous_apply (0 : ℤ)).comp
        (continuous_subtype_val.comp continuous_fst)).fst)
    exact ((pathHomeomorph d).continuous.comp continuous_fst).prodMk
      (continuous_snd.mul hc)
  continuous_invFun := by
    have hc : Continuous (fun p : RightPath d × H => alpha (p.1.val (-1)).2) :=
      ha.comp (((continuous_apply (-1 : ℤ)).comp
        (continuous_subtype_val.comp continuous_fst)).snd)
    exact ((pathHomeomorph d).symm.continuous.comp continuous_fst).prodMk
      (continuous_snd.mul hc.inv)

end Topology

#print axioms skewHomeomorph

end D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
