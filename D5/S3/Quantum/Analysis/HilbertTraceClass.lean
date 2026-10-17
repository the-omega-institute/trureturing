/- GID: D5/S3/Quantum/Analysis/HilbertTraceClass
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/HilbertTraceClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs, mathlib/module/Mathlib.Analysis.InnerProductSpace.StarOrder, mathlib/module/Mathlib.Analysis.InnerProductSpace.l2Space, mathlib/module/Mathlib.Analysis.InnerProductSpace.Trace, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Defs, mathlib/module/Mathlib.LinearAlgebra.Dimension.Finite, mathlib/module/Mathlib.LinearAlgebra.Trace, mathlib/module/Mathlib.LinearAlgebra.Projection, mathlib/module/Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent]
   utility: none
   digest: CFC absolute-value trace class and basis-independent positive Hilbert trace. -/

/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Hilbert trace class and positive trace

Source transplant of the consumed positive-trace closure from
leanprover-community/physlib at 0aeb3dc7e249f9acc9032252060d4fa5f35c7e20,
PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Basic.lean.
Original blob: 68b94896caae2e61806b3a22919efd06e1f2d75b.
Original SHA256: 28d6227ebfe270441086e35590473470d78ed162f846fd6c5fe6087bc3769404.

The seven declarations below retain the upstream statements, proofs, namespace,
imports and module visibility. This positive-trace closure does not include
trace-norm, finite-dimensional, self-adjoint trace or finite-multiplicity results. This is known mathematics by the named
upstream author; no mathematical novelty or independent proof is claimed.
Full Apache-2.0 license: docs/reports/hilbert-trace-class/physlib-LICENSE.txt.
The complete immutable upstream tree contains no NOTICE-named file and only
one LICENSE file, at its root. This leaf imports only Mathlib.

Retirement: evaluate only at the mathlib revision recorded in this receiver's
lake-manifest.json. Retire this module when that exact pin supplies declarations
for the CFC.abs trace-class predicate, trace, every-basis absolute-diagonal
summability, positive complex-diagonal summability and positive trace formula,
with the complete arbitrary complex Hilbert-space telescopes below, and an
exact import-only consumer check at that pin succeeds with the standard axiom
closure. A checked finite name/module substitution and, if needed, checked
predicate/trace equivalences identify the replacement. The check is a finite
explicit target suite, never a search for arbitrary theorem equivalence. If any
required supplier or check is missing, the retirement predicate is false.
Replace consumers by the pinned suppliers and remove this transplant in that
same retirement change; external acceptance or an unpinned release is irrelevant.
-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`T` is trace class**: `∑ᵢ ⟪eᵢ, |T| eᵢ⟫` converges for some Hilbert basis `{eᵢ}` of `H`
(`|T| := CFC.abs T`, Mathlib's continuous functional calculus absolute value `√(T⋆T)`). By the
basis-independence theorem below, "some" is equivalent to "every". -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H), Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re)

omit [CompleteSpace H] in
/-- **Parseval's identity**: `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` for a Hilbert basis `{eᵢ}`. -/
lemma hasSum_norm_sq_inner_basis {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ = ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

/-- For self-adjoint `S`, the sum `∑ᵢ ‖S eᵢ‖²` does not depend on the Hilbert basis. -/
lemma hasSum_norm_sq_apply_of_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
      S).symm.trans hS
  have hcol : ∀ j : w', HasSum (fun i : w => F i j) (‖S (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ = ⟪S (c j), b i⟫_ℂ := fun i => by
      have h1 := ContinuousLinearMap.adjoint_inner_left S (b i) (c j)
      rw [hSstar] at h1
      exact h1.symm
    have key : (fun i : w => F i j) = fun i : w => ‖⟪b i, S (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) (S (c j)), RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b (S (c j))
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖S (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖S (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p
      simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable (fun j : w' => ‖S (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := by
      show Summable fun j : w' => ∑' i : w, Function.uncurry G (j, i)
      exact hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' => ‖S (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

/-- **Trace class does not depend on the basis**: the diagonal of `|T|` is summable in every Hilbert
basis. -/
lemma summable_inner_abs_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  obtain ⟨w₀, b₀, hb₀⟩ := h
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
          S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    have hval : ⟪S (b' i), S (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [this, hval, Complex.ofReal_re]
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    simpa [hpt b₀] using hb₀
  have := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  simpa [hpt b] using this.summable

/-- **The trace** `Tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` of a trace-class operator, in the basis witnessing that it
is trace class. -/
def trace (T : H →L[ℂ] H) (h : IsTraceClass T) : ℂ :=
  ∑' i : h.choose, ⟪h.choose_spec.choose i, T (h.choose_spec.choose i)⟫_ℂ

lemma summable_inner_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (h : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i => ⟪b i, T (b i)⟫_ℂ) := by
  have hr : Summable (fun i : w => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) :=
    summable_inner_abs_of_hilbertBasis h b
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
  have heq (i : w) : ⟪b i, T (b i)⟫_ℂ =
      ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
    rw [habs]
    have hpos : T.IsPositive := T.nonneg_iff_isPositive.mp hT
    have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos (b i)
    have hA : ⟪T (b i), b i⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪T (b i), b i⟫_ℂ).re = (⟪b i, T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (T (b i)) (b i)]
      exact Complex.conj_re _
    have hinner : ⟪b i, T (b i)⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪T (b i), b i⟫_ℂ).re : ℂ) :=
          congrArg (starRingEnd ℂ) hA
        _ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by simp
    exact hinner.trans (congrArg (fun r : ℝ => (r : ℂ)) hre)
  have hs : Summable (fun i : w => ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ)) :=
    Complex.summable_ofReal.mpr hr
  exact hs.congr (fun i => (heq i).symm)

/-!
Basis-independent trace for positive trace-class operators.

For a positive operator the absolute value is the operator itself.  Taking its continuous-
functional-calculus square root turns every diagonal coefficient into a squared norm, so the
Parseval double-sum theorem already proved above gives the same sum in every Hilbert basis.  This
is the positive case needed by density operators and does not use polar decomposition.
-/
lemma trace_eq_of_hilbertBasis_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (h : IsTraceClass T) {w : Set H} (b : HilbertBasis w ℂ H) :
    trace T h = ∑' i, ⟪b i, T (b i)⟫_ℂ := by
  let S : H →L[ℂ] H := CFC.sqrt T
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg T)
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hdiag : ∀ {w' : Set H} (b' : HilbertBasis w' ℂ H) (i : w'),
      ⟪b' i, T (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
    intro w' b' i
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hinner : ⟪b' i, T (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hWdiag : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    have hbase : Summable (fun i : w₀ =>
        (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) := h.choose_spec.choose_spec
    have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
    apply hbase.congr
    intro i
    rw [habs, hdiag b₀ i]
    rfl
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hWdiag
  calc
    trace T h = ∑' i : w₀, ⟪b₀ i, T (b₀ i)⟫_ℂ := by
      rfl
    _ = ∑' i : w₀, ((‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro i
      exact hdiag b₀ i
    _ = ((∑' i : w₀, ‖S (b₀ i)‖ ^ 2 : ℝ) : ℂ) :=
      (Complex.ofReal_tsum (fun i : w₀ => ‖S (b₀ i)‖ ^ 2)).symm
    _ = ((∑' i : w, ‖S (b i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hnorm.tsum_eq]
    _ = ∑' i : w, ⟪b i, T (b i)⟫_ℂ := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro i
      exact (hdiag b i).symm

end ProbabilisticTheory
