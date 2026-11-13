import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
import Reg.Support.DependentFamily

/-! Exact RH-conditional kernel-output law and its variation boundary.
The source bridge alone is not a four-slot registration. -/

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open scoped ComplexOrder

noncomputable section

private abbrev kernelSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def kernelActual : Realization kernelSignature :=
  realize kernelSignature (fun _ _ t => (K t : ℂ)) (fun e => nomatch e)

private abbrev kernelArena : Arena where
  signature := kernelSignature
  Law R := ∀ (_ : RiemannHypothesis) (n : ℕ) (x : Fin n → ℝ),
    Function.Injective x → Matrix.PosDef (fun i j => R.readout () () (x j - x i))

private theorem sourceBridge : (type_of% @actual_kernel_strict_gram_of_rh) ↔
    kernelArena.Law kernelActual := Iff.rfl

private theorem actualLaw : kernelArena.Law kernelActual :=
  sourceBridge.mp actual_kernel_strict_gram_of_rh

/-- Rejection of any whole family for this exact law would already imply RH. -/
private theorem rejectedFamily_implies_rh (R : Realization kernelSignature)
    (h : ¬ kernelArena.Law R) : RiemannHypothesis := by
  by_contra hn
  apply h
  intro hRH
  exact (hn hRH).elim

private theorem variation_implies_rh (h : Variation kernelArena kernelActual) :
    RiemannHypothesis := by
  obtain ⟨_, R, hR⟩ := h
  exact rejectedFamily_implies_rh R hR

end
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity
