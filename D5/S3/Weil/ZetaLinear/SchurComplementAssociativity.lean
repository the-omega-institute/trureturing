/- GID: D5/S3/Weil/ZetaLinear/SchurComplementAssociativity
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/SchurComplementAssociativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sequential and one-shot Schur elimination give the same retained operator. -/

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Associativity of Schur-complement elimination

Nine bounded operator blocks construct a three-space operator. Assuming inverse
witnesses for the last diagonal block, its first reduced diagonal block, and
the combined lower block, eliminating the last two spaces sequentially agrees
with eliminating their product in one step.

Repository searches found no Schur-complement construction or associativity
theorem on this carrier. Pinned Mathlib supplies the canonical product and
coproduct constructors for bounded linear maps and finite-matrix Gaussian
factorizations, but no exact theorem for this infinite-dimensional identity.
-/

namespace D5.S3.Weil.ZetaLinear.SchurComplementAssociativity

/-- Solving the two lower block equations successively gives the same retained
operator as solving the combined lower block equation. -/
theorem schur_complement_associativity
    {H0 H1 H2 : Type*}
    [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] [CompleteSpace H0]
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    (A00 : H0 →L[ℂ] H0) (A01 : H1 →L[ℂ] H0) (A02 : H2 →L[ℂ] H0)
    (A10 : H0 →L[ℂ] H1) (A11 : H1 →L[ℂ] H1) (A12 : H2 →L[ℂ] H1)
    (A20 : H0 →L[ℂ] H2) (A21 : H1 →L[ℂ] H2) (A22 : H2 →L[ℂ] H2)
    (A22Inv : H2 →L[ℂ] H2) (reducedA11Inv : H1 →L[ℂ] H1)
    (lowerInv : H1 × H2 →L[ℂ] H1 × H2)
    (hA22Inv : A22Inv.comp A22 = ContinuousLinearMap.id ℂ H2)
    (hReducedA11Inv :
      reducedA11Inv.comp (A11 - A12.comp (A22Inv.comp A21)) =
        ContinuousLinearMap.id ℂ H1)
    (hLowerInv :
      ((A11.coprod A12).prod (A21.coprod A22)).comp lowerInv =
        ContinuousLinearMap.id ℂ (H1 × H2)) :
    (A00 - A02.comp (A22Inv.comp A20)) -
        (A01 - A02.comp (A22Inv.comp A21)).comp
          (reducedA11Inv.comp (A10 - A12.comp (A22Inv.comp A20))) =
      A00 - (A01.coprod A02).comp (lowerInv.comp (A10.prod A20)) := by
  ext x
  let y : H1 × H2 := lowerInv ((A10.prod A20) x)
  have hLowerAt := DFunLike.congr_fun hLowerInv ((A10.prod A20) x)
  have hy1 : A11 y.1 + A12 y.2 = A10 x := by
    exact congrArg Prod.fst hLowerAt
  have hy2 : A21 y.1 + A22 y.2 = A20 x := by
    exact congrArg Prod.snd hLowerAt
  have hA22At := DFunLike.congr_fun hA22Inv y.2
  have hy2Solved : y.2 = A22Inv (A20 x) - A22Inv (A21 y.1) := by
    calc
      y.2 = A22Inv (A22 y.2) := hA22At.symm
      _ = A22Inv (A20 x - A21 y.1) := by rw [← hy2]; congr 1; abel
      _ = A22Inv (A20 x) - A22Inv (A21 y.1) := map_sub A22Inv _ _
  have hReducedAt := DFunLike.congr_fun hReducedA11Inv y.1
  have hReducedEquation :
      (A11 - A12.comp (A22Inv.comp A21)) y.1 =
        (A10 - A12.comp (A22Inv.comp A20)) x := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    rw [hy2Solved, map_sub] at hy1
    rw [← hy1]
    abel
  have hy1Solved :
      y.1 = reducedA11Inv ((A10 - A12.comp (A22Inv.comp A20)) x) := by
    rw [← hReducedEquation]
    exact hReducedAt.symm
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply]
  change
    A00 x - A02 (A22Inv (A20 x)) -
        (A01 (reducedA11Inv (A10 x - A12 (A22Inv (A20 x)))) -
          A02 (A22Inv (A21 (reducedA11Inv (A10 x - A12 (A22Inv (A20 x))))))) =
      A00 x - (A01 y.1 + A02 y.2)
  rw [hy2Solved, hy1Solved, map_sub]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

#print axioms schur_complement_associativity

end D5.S3.Weil.ZetaLinear.SchurComplementAssociativity
