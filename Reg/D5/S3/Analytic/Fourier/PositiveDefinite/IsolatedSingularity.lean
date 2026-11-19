import D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity
import Reg.Support.DependentFamily

/-! Exact dependent-family law for the isolated-singularity theorem.
The source bridge alone is not a four-slot registration. -/

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity
open Filter Asymptotics
open scoped Topology ComplexOrder

noncomputable section
universe u

private structure KernelContext where
  V : Type u
  normed : NormedAddCommGroup V
  kernel : V → ℂ

private abbrev kernelSignature : Signature where
  Params := KernelContext.{u}
  State p := p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def kernelActual : Realization kernelSignature.{u} :=
  realize kernelSignature (fun _ p t => p.kernel t) (fun e => nomatch e)

private abbrev kernelArena : Arena where
  signature := kernelSignature.{u}
  Law R := ∀ {V : Type u} [inst : NormedAddCommGroup V] {k : V → ℂ},
    (∀ (n : ℕ) (x : Fin n → V), Matrix.PosSemidef (fun i j => k (x j - x i))) →
    (∀ r : V, r ≠ 0 →
      (fun h : V => k (r + h) - k r) =O[𝓝 0] (fun h : V => h)) →
    (¬ (fun h : V => k h - k 0) =O[𝓝 0] (fun h : V => h)) →
    ∀ (n : ℕ) (x : Fin n → V), Function.Injective x →
      Matrix.PosDef (fun i j => R.readout () ⟨V, inst, k⟩ (x j - x i))

private theorem sourceBridge :
    (type_of% @posDef_of_isolated_non_lipschitz.{u}) ↔
      kernelArena.{u}.Law kernelActual.{u} := Iff.rfl

private theorem actualLaw : kernelArena.{u}.Law kernelActual.{u} :=
  sourceBridge.{u}.mp @posDef_of_isolated_non_lipschitz.{u}

end
end Reg.D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity
