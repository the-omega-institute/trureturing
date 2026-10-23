import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
import Reg.Support.DependentFamily

open D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module Submodule
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Reg.D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank

structure AlgebraContext where
  A : Type u
  ring : Ring A
  algebra : letI := ring; Algebra ℂ A
  finite : letI := ring; letI := algebra; Module.Finite ℂ A

structure RankParameters extends AlgebraContext.{u} where
  u : A
  v : A
  hu : letI := ring; u*u=1
  hv : letI := ring; v*v=1
  independent : letI := ring; letI := algebra;
    LinearIndependent ℂ (fun i : Fin 4 => (u*v)^i.val)
  forward : letI := ring; letI := algebra;
    ∀ x ∈ powerSpace u v, (u*v)*x ∈ powerSpace u v
  inverse : letI := ring; letI := algebra;
    ∀ x ∈ powerSpace u v, (v*u)*x ∈ powerSpace u v

abbrev rankSignature : Signature where
  Params := RankParameters.{u}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature.{u} := realize rankSignature.{u}
  (fun _ P n => by
    letI := P.ring
    letI := P.algebra
    letI := P.finite
    exact finrank ℂ (wordSpace P.u P.v n)) (fun e => nomatch e)

def rankArena : Arena where
  signature := rankSignature.{u}
  Law R := ∀ P n, R.readout () P n = min (n+1) 4

private theorem rankSourceBridge : (type_of% (@homogeneous_word_rank.{u})) ↔
    rankArena.{u}.Law rankActual.{u} := by
  constructor
  · intro h P n
    letI := P.ring
    letI := P.algebra
    letI := P.finite
    exact h P.u P.v P.hu P.hv P.independent P.forward P.inverse n
  · intro h A instR instA instF a b hu hv hi hR hD n
    exact h ⟨⟨A,instR,instA,instF⟩,a,b,hu,hv,hi,hR,hD⟩ n

structure ScaleParameters extends AlgebraContext.{u} where
  u : A
  v : A
  z : ℂ
  w : ℂ
  z_nonzero : z ≠ 0
  w_nonzero : w ≠ 0

abbrev scaleSignature : Signature where
  Params := ScaleParameters.{u}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => by
    letI := P.ring
    letI := P.algebra
    exact Submodule ℂ P.A
  Anchor := Empty
  finiteAnchor := inferInstance

def scaleActual : Realization scaleSignature.{u} := realize scaleSignature.{u}
  (fun _ P n => by
    letI := P.ring
    letI := P.algebra
    exact wordSpace (P.z • P.u) (P.w • P.v) n) (fun e => nomatch e)

def scaleArena : Arena where
  signature := scaleSignature.{u}
  Law R := ∀ P n, R.readout () P n = by
    letI := P.ring
    letI := P.algebra
    exact wordSpace P.u P.v n

private theorem scaleSourceBridge : (type_of% (@wordSpace_scale.{u})) ↔
    scaleArena.{u}.Law scaleActual.{u} := by
  constructor
  · intro h P n
    letI := P.ring
    letI := P.algebra
    letI := P.finite
    exact h P.u P.v P.z P.w P.z_nonzero P.w_nonzero n
  · intro h A instR instA instF a b z w hz hw n
    exact h ⟨⟨A,instR,instA,instF⟩,a,b,z,w,hz,hw⟩ n

structure MapParameters extends AlgebraContext.{u} where
  B : Type v
  ringB : Ring B
  algebraB : letI := ringB; Algebra ℂ B
  f : letI := ring; letI := algebra; letI := ringB; letI := algebraB; A →ₐ[ℂ] B
  u : A
  v : A

abbrev mapSignature : Signature where
  Params := MapParameters.{u,v}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => by
    letI := P.ringB
    letI := P.algebraB
    exact Submodule ℂ P.B
  Anchor := Empty
  finiteAnchor := inferInstance

def mapActual : Realization mapSignature.{u,v} := realize mapSignature.{u,v}
  (fun _ P n => by
    letI := P.ring
    letI := P.algebra
    letI := P.ringB
    letI := P.algebraB
    exact wordSpace (P.f P.u) (P.f P.v) n) (fun e => nomatch e)

def mapArena : Arena where
  signature := mapSignature.{u,v}
  Law R := ∀ P n, R.readout () P n = by
    letI := P.ring
    letI := P.algebra
    letI := P.ringB
    letI := P.algebraB
    exact (wordSpace P.u P.v n).map P.f.toLinearMap

private theorem mapSourceBridge : (type_of% (@wordSpace_map.{u,v})) ↔
    mapArena.{u,v}.Law mapActual.{u,v} := by
  constructor
  · intro h P n
    letI := P.ring
    letI := P.algebra
    letI := P.finite
    letI := P.ringB
    letI := P.algebraB
    exact h P.f P.u P.v n
  · intro h A instR instA instF B instRB instAB f a b n
    exact h ⟨⟨A,instR,instA,instF⟩,B,instRB,instAB,f,a,b⟩ n

#check rankSourceBridge
#check scaleSourceBridge
#check mapSourceBridge
#print axioms rankSourceBridge
#print axioms scaleSourceBridge
#print axioms mapSourceBridge

end Reg.D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
