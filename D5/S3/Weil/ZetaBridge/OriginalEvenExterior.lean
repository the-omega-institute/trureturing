/- GID: D5/S3/Weil/ZetaBridge/OriginalEvenExterior
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalEvenExterior
   mirror-E: none(waiver:analytic-hilbert-fourier-identification-without-executable-mirror)
   anchors: []
   utility: none
   digest: For a > 0, the closed cosine tail is the original even head complement, with its included projection equal to (id - P_head) composed with P_even. -/

import D5.S3.Weil.ZetaBridge.OriginalEvenCosineComplete
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalEvenExterior

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix PhysicalCosineTailProjection
open OriginalWindowEven OriginalEvenCosineComplete

/-- Exactly modes 0 through M, on the original complex dx-L2 carrier. -/
def finiteHead (a : ℝ) (M : ℕ) : Submodule ℂ (WindowL2 a) :=
  Submodule.span ℂ (Set.range (fun n : Fin (M + 1) => modeL2 a n))

instance finiteHead_finiteDimensional (a : ℝ) (M : ℕ) :
    FiniteDimensional ℂ (finiteHead a M) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

private lemma head_mode_mem (a : ℝ) (M n : ℕ) (hn : n ≤ M) :
    modeL2 a n ∈ finiteHead a M :=
  Submodule.subset_span ⟨⟨n, by omega⟩, rfl⟩

private lemma tail_mode_mem (a : ℝ) (M n : ℕ) (hn : M < n) :
    modeL2 a n ∈ exteriorSpace a M := by
  have he : M + (n - (M + 1)) + 1 = n := by omega
  rw [← he]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self _))

private lemma head_le_even (a : ℝ) (M : ℕ) : finiteHead a M ≤ originalEven a := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact mode_mem_originalEven a n

private lemma tail_le_even (a : ℝ) (M : ℕ) : exteriorSpace a M ≤ originalEven a := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact mode_mem_originalEven a _
  · exact originalEven_isClosed a

/-- Consumed linear-span induction, expressed using the existing singleton owner. -/
private lemma mem_orthogonal_span_range {ι : Type*} (a : ℝ) (v : ι → WindowL2 a)
    (u : WindowL2 a) (h : ∀ i, inner ℂ (v i) u = 0) :
    u ∈ (Submodule.span ℂ (Set.range v))ᗮ := by
  have hs : Submodule.span ℂ (Set.range v) ≤ (ℂ ∙ u)ᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    exact inner_eq_zero_symm.mp (h i)
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  exact inner_eq_zero_symm.mp
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hs hx))

private lemma tail_le_head_orthogonal (a : ℝ) (ha : 0 < a) (M : ℕ) :
    exteriorSpace a M ≤ (finiteHead a M)ᗮ := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply mem_orthogonal_span_range
    intro n
    have hne : (n : ℕ) ≠ M + j + 1 := by have := n.isLt; omega
    rw [orthonormal_iff_ite.mp (modes_orthonormal a ha), if_neg hne]
  · exact Submodule.isClosed_orthogonal _

/-- The returned source's closed tail span is the TRUE even exterior complement. -/
theorem exteriorSpace_eq_even_inf_head_orthogonal (a : ℝ) (ha : 0 < a) (M : ℕ) :
    exteriorSpace a M = originalEven a ⊓ (finiteHead a M)ᗮ := by
  apply le_antisymm
  · exact le_inf (tail_le_even a M) (tail_le_head_orthogonal a ha M)
  · intro u hu
    let q := (exteriorSpace a M).starProjection u
    have hq : q ∈ exteriorSpace a M := (exteriorSpace a M).starProjection_apply_mem u
    have hgE : u - q ∈ originalEven a :=
      (originalEven a).sub_mem hu.1 (tail_le_even a M hq)
    have hgH : u - q ∈ (finiteHead a M)ᗮ :=
      ((finiteHead a M)ᗮ).sub_mem hu.2 (tail_le_head_orthogonal a ha M hq)
    have hgT : u - q ∈ (exteriorSpace a M)ᗮ :=
      (exteriorSpace a M).sub_starProjection_mem_orthogonal u
    have hz : u - q = 0 := even_eq_zero_of_mode_inner_eq_zero a ha (u - q) hgE (by
      intro n
      by_cases hn : n ≤ M
      · exact (Submodule.mem_orthogonal _ _).mp hgH _ (head_mode_mem a M n hn)
      · exact (Submodule.mem_orthogonal _ _).mp hgT _
          (tail_mode_mem a M n (by omega)))
    rw [sub_eq_zero.mp hz]
    exact hq

/-- Both projections below are endomorphisms of WindowL2 a; the original
exteriorProjection has codomain exteriorSpace a M and must be embedded first. -/
def evenProjection (a : ℝ) : WindowL2 a →L[ℂ] WindowL2 a :=
  (originalEven a).starProjection

def headProjection (a : ℝ) (M : ℕ) : WindowL2 a →L[ℂ] WindowL2 a :=
  (finiteHead a M).starProjection

/-- Typed identity: inclusion ∘ Q_tail = (id - P_M) ∘ P_even, on ALL WindowL2 a. -/
theorem exteriorProjection_identity (a : ℝ) (ha : 0 < a) (M : ℕ) :
    (exteriorSpace a M).subtypeL.comp (exteriorProjection a M) =
      ((ContinuousLinearMap.id ℂ (WindowL2 a)) - headProjection a M).comp
        (evenProjection a) := by
  apply ContinuousLinearMap.ext
  intro u
  change (exteriorSpace a M).starProjection u =
    (originalEven a).starProjection u -
      (finiteHead a M).starProjection ((originalEven a).starProjection u)
  let e := (originalEven a).starProjection u
  let h := (finiteHead a M).starProjection e
  have he : e ∈ originalEven a := (originalEven a).starProjection_apply_mem u
  have hh : h ∈ finiteHead a M := (finiteHead a M).starProjection_apply_mem e
  have hy : e - h ∈ exteriorSpace a M := by
    rw [exteriorSpace_eq_even_inf_head_orthogonal a ha M]
    exact ⟨(originalEven a).sub_mem he (head_le_even a M hh),
      (finiteHead a M).sub_starProjection_mem_orthogonal e⟩
  have hresE : u - e ∈ (exteriorSpace a M)ᗮ :=
    Submodule.orthogonal_le (tail_le_even a M)
      ((originalEven a).sub_starProjection_mem_orthogonal u)
  have hHtoT : finiteHead a M ≤ (exteriorSpace a M)ᗮ :=
    (finiteHead a M).le_orthogonal_orthogonal.trans
      (Submodule.orthogonal_le (tail_le_head_orthogonal a ha M))
  have hres : u - (e - h) ∈ (exteriorSpace a M)ᗮ := by
    rw [show u - (e - h) = (u - e) + h by abel]
    exact ((exteriorSpace a M)ᗮ).add_mem hresE (hHtoT hh)
  exact Submodule.eq_starProjection_of_mem_orthogonal hy hres

/-- On the actual symmetric prime action, P_even disappears because parity
was proved for this exact object, with every prime power and both shift signs. -/
theorem exteriorProjection_prime (a : ℝ) (ha : 0 < a) (M N : ℕ) (v : ℕ → ℂ) :
    (exteriorProjection a M (primeHeadL2 a N v) : WindowL2 a) =
      primeHeadL2 a N v - headProjection a M (primeHeadL2 a N v) := by
  have h := congrArg (fun p : WindowL2 a →L[ℂ] WindowL2 a => p (primeHeadL2 a N v))
    (exteriorProjection_identity a ha M)
  have he : evenProjection a (primeHeadL2 a N v) = primeHeadL2 a N v :=
    (Submodule.starProjection_eq_self_iff).mpr (primeHead_mem_originalEven a N v)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, Submodule.subtypeL_apply, he] using h

end OriginalEvenExterior
