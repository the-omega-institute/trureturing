import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction

noncomputable section
universe u v w
namespace Reg.D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction

structure Parameters where
  V : Type u
  [normed : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  Γ : Type v
  [group : Group Γ]
  I : Type w
  row : Γ → V
  read : V →ₗ[ℝ] (I → ℝ)
  injective : Function.Injective read
  spanning : Submodule.span ℝ (Set.range row) = ⊤
  bounded : ∀ a i, read (row a) i ∈ Set.Icc (0 : ℝ) 1
  futurePrefix : Γ → I → I
  shift : ∀ a g i, read (row (a*g)) i = read (row a) (futurePrefix g i)

attribute [instance] Parameters.normed Parameters.space Parameters.finite Parameters.group

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize signature.{u,v,w}
  (fun _ p _ => ∃ ρ : p.Γᵐᵒᵖ →* (p.V →L[ℝ] p.V)ˣ,
    (∀ a g, (ρ (MulOpposite.op g)).val (p.row a) = p.row (a*g)) ∧
    IsCompact (ρ.range.topologicalClosure : Set (p.V →L[ℝ] p.V)ˣ))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ p : Parameters.{u,v,w}, R.readout () p ()

/-- All original rows, future coordinates, bounds and futurePrefix equations remain in the telescope. -/
theorem full_telescope_bridge :
    (type_of% (@continuation_compact.{u,v,w})) ↔ arena.{u,v,w}.Law actual := by
  constructor
  · intro h p
    exact h p.row p.read p.injective p.spanning p.bounded p.futurePrefix p.shift
  · intro h V _ _ _ Γ I _ row read hinj hspan hbound futurePrefix hshift
    exact h ⟨V,Γ,I,row,read,hinj,hspan,hbound,futurePrefix,hshift⟩

theorem actual_positive : arena.{u,v,w}.Law actual :=
  full_telescope_bridge.mp (@continuation_compact.{u,v,w})


structure CenteredParameters extends Parameters.{u,v,w} where
  mass : V →ₗ[ℝ] ℝ
  normalized : ∀ a, mass (row a) = 1

abbrev centeredSignature : Signature where
  Params := CenteredParameters.{u,v,w}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def centeredActual : Realization centeredSignature.{u,v,w} := realize centeredSignature.{u,v,w}
  (fun _ p _ => ∃ ρ : p.Γᵐᵒᵖ →* (p.V →L[ℝ] p.V)ˣ,
    (∀ a g, (ρ (MulOpposite.op g)).val (p.row a) = p.row (a*g)) ∧
    IsCompact (ρ.range.topologicalClosure : Set (p.V →L[ℝ] p.V)ˣ) ∧
    ∃ c : p.V, p.mass c = 1 ∧
      (∀ g : ρ.range.topologicalClosure, g.val.val c = c) ∧
      (∀ (g : ρ.range.topologicalClosure) v, p.mass (g.val.val v) = p.mass v) ∧
      Submodule.span ℝ (Set.range (fun a => p.row a-c)) = p.mass.ker ∧
      Submodule.span ℝ (Set.range (fun g : ρ.range.topologicalClosure =>
        g.val.val (p.row 1-c))) = p.mass.ker ∧
      (p.mass.ker ≠ ⊥ → p.row 1-c ≠ 0) ∧
      ∀ g : ρ.range.topologicalClosure, (∀ v : p.mass.ker, g.val.val v = v) → g = 1)
  (fun e => nomatch e)

abbrev centeredArena : Arena where
  signature := centeredSignature.{u,v,w}
  Law R := ∀ p : CenteredParameters.{u,v,w}, R.readout () p ()

/-- The actual center, full mass kernel, orbit and identity conclusion are reconstructed. -/
theorem centered_full_telescope_bridge :
    (type_of% (@centered_continuation.{u,v,w})) ↔
      centeredArena.{u,v,w}.Law centeredActual := by
  constructor
  · intro h p
    exact h p.row p.read p.injective p.spanning p.bounded p.futurePrefix p.shift p.mass p.normalized
  · intro h V _ _ _ Γ I _ row read hinj hspan hbound futurePrefix hshift mass hmass
    exact h ⟨⟨V,Γ,I,row,read,hinj,hspan,hbound,futurePrefix,hshift⟩,mass,hmass⟩

theorem centered_actual_positive : centeredArena.{u,v,w}.Law centeredActual :=
  centered_full_telescope_bridge.mp (@centered_continuation.{u,v,w})

end Reg.D5.S3.Quantum.Algebra.OriginalProbabilityCompactAction
