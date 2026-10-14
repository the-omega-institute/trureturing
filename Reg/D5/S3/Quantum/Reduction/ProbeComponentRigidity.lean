import D5.S3.Quantum.Reduction.ProbeComponentRigidity
import Reg.Support.DependentFamily

noncomputable section
open Matrix
open scoped BigOperators
namespace Reg.D5.S3.Quantum.Reduction.ProbeComponentRigidity
open _root_.D5.S3.Quantum.Reduction.ProbeComponentRigidity
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u v w

structure Parameters where
  d : Type u
  s : Type v
  J : Type w
  fd : Fintype d
  eqd : DecidableEq d
  fs : Fintype s
  K : s → Matrix d d ℂ
  normalized : letI := fd; letI := eqd; letI := fs; (∑ a, (K a)ᴴ * K a) = 1
  probes : J → d → ℂ
  unit : letI := fd; ∀ j, star (probes j) ⬝ᵥ probes j = 1
  probabilities : letI := fd; letI := eqd; letI := fs;
    ∀ j (ρ : DensityState d),
      trace (probe (probes j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (probes j) * CStarMatrix.ofMatrix.symm ρ.1)
  krausIndex : s
  probeIndex : J

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State p := p.d → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.d → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u,v,w} :=
  realize signature.{u,v,w} (fun _ p x => letI := p.fd; p.K p.krausIndex *ᵥ x)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ (p : Parameters.{u,v,w}), letI := p.fd; letI := p.eqd;
    ∀ (x : p.d → ℂ), x ∈ componentSpace p.probes p.probeIndex →
      R.readout () p x = probeScalar (p.K p.krausIndex) (p.probes p.probeIndex) • x

theorem source_bridge :
    (type_of% (@kraus_scalar_on_component.{u,v,w})) ↔ arena.{u,v,w}.Law actual.{u,v,w} := by
  constructor
  · intro h p x hx
    letI := p.fd
    letI := p.eqd
    letI := p.fs
    exact h p.K p.normalized p.probes p.unit p.probabilities
      p.krausIndex p.probeIndex x hx
  · intro h d s J fd eqd fs K hTP probes unit probabilities a j x hx
    exact h ⟨d, s, J, fd, eqd, fs, K, hTP, probes, unit, probabilities, a, j⟩ x hx

private def unitParameters : Parameters.{u,v,w} where
  d := ULift.{u} Unit
  s := ULift.{v} Unit
  J := ULift.{w} Unit
  fd := inferInstance
  eqd := inferInstance
  fs := inferInstance
  K := fun _ => 1
  normalized := by simp
  probes := fun _ _ => 1
  unit := by intro j; simp [dotProduct]
  probabilities := by intro j ρ; simp
  krausIndex := ⟨()⟩
  probeIndex := ⟨()⟩

private def rejected : Realization signature.{u,v,w} :=
  realize signature.{u,v,w} (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected.{u,v,w} := by
  intro h
  let p := unitParameters.{u,v,w}
  letI := p.fd
  letI := p.eqd
  have hm : p.probes p.probeIndex ∈ componentSpace p.probes p.probeIndex :=
    Submodule.subset_span ⟨p.probeIndex, Relation.EqvGen.refl _, rfl⟩
  have hh := h p (p.probes p.probeIndex) hm
  have hK : p.K p.krausIndex = (1 : Matrix p.d p.d ℂ) := rfl
  have hs : probeScalar (p.K p.krausIndex) (p.probes p.probeIndex) = 1 := by
    rw [hK, probeScalar, Matrix.one_mulVec]
    exact p.unit p.probeIndex
  rw [hs, one_smul] at hh
  change (0 : p.d → ℂ) = p.probes p.probeIndex at hh
  have he := congrFun hh (ULift.up ())
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

/-- Faithful dependent-family kernel evidence for the complete arbitrary-family
    scalarity telescope. Source selection and Contract binding are separate. -/
def evidence : Registration arena.{u,v,w}
    (type_of% (@kraus_scalar_on_component.{u,v,w})) where
  actual := actual.{u,v,w}
  bridge := source_bridge.{u,v,w}
  variation := ⟨source_bridge.mp (@kraus_scalar_on_component.{u,v,w}),
    rejected.{u,v,w}, rejected_law.{u,v,w}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,v,w}, ?_, rfl, rejected_law.{u,v,w}⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro role
    let p := unitParameters.{u,v,w}
    letI := p.fd
    letI := p.eqd
    refine ⟨p, (0 : p.d → ℂ), (fun _ => 1), ?_⟩
    intro h
    change p.K p.krausIndex *ᵥ (0 : p.d → ℂ) =
      p.K p.krausIndex *ᵥ (fun _ => 1) at h
    have hK : p.K p.krausIndex = (1 : Matrix p.d p.d ℂ) := rfl
    rw [hK, Matrix.mulVec_zero, Matrix.one_mulVec] at h
    have he := congrFun h (ULift.up ())
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

#print axioms source_bridge
#print axioms evidence

end Reg.D5.S3.Quantum.Reduction.ProbeComponentRigidity
