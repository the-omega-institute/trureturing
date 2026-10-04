/- GID: D5/S3/Quantum/Analysis/PhysicalGraphClosure
   generality: I
   mirror-B: D5/B/S3/Quantum/Analysis/PhysicalGraphClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact physical Hermite basis identifies the actual weak graph and nonnegative closure. -/

/-
The exact physical Schwartz construction and its Gaussian, Hermite and cutoff
source/license chains are imported from PhysicalHermiteTests. The eigenbasis
closure imports its attributed PhysLean resolvent construction. The joining
and nonnegative finite-graph limit use pinned Mathlib directly.
Physical orthonormality and totality are explicit separate inputs.
-/

import D5.S3.Quantum.Analysis.PhysicalHermiteTests
import D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
import D5.S3.Quantum.Analysis.EigenbasisGraphCore

open SchwartzMap MeasureTheory LinearPMap Filter
open scoped Topology ENNReal InnerProductSpace ComplexConjugate lp
noncomputable section
namespace D5.S3.Quantum.Analysis.PhysicalGraphClosure
open D5.S3.Quantum.Analysis.SchwartzCutoffGraph
open D5.S3.Quantum.Analysis.SchwartzWeakAdjoint
open D5.S3.Quantum.Analysis.PhysicalHermiteTests
open D5.S3.Quantum.Analysis.EigenbasisClosure
open D5.S3.Quantum.Analysis.EigenbasisGraphCore

set_option maxHeartbeats 800000 in
theorem physical_graph_closure (d : ℕ) (h : ℝ) (m w : Fin d → ℝ) (hh : 0 < h)
    (hm : ∀ j, 0 < m j) (hw : ∀ j, 0 < w j)
    (φ : (Fin d → ℕ) → 𝓢(Space d, ℂ))
    (hφ : ∀ n x, φ n x = value d h m w n x)
    (e : HilbertBasis (Fin d → ℕ) ℂ (Hilbert d))
    (he : ∀ n, e n = (φ n).toLp 2 volume) :
    let S := schwartzOperator d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2)
    let C := Submodule.span ℂ (Set.range e)
    let T := S.domRestrict C
    let K := T.closure
    let E := fun n : Fin d → ℕ => ∑ j, h*w j*((n j : ℝ)+1/2)
    S ≤ K ∧ S.IsClosable ∧ S.closure = K ∧ S† = K ∧
    IsSelfAdjoint K ∧ K.IsClosed ∧ K.HasCore C ∧
    (∀ u : K.domain, 0 ≤ (⟪(u : Hilbert d), K u⟫_ℂ).re) ∧
    (∀ f g : Hilbert d,
      (Weak d (fun j => h^2/(2*m j)) (fun j => m j*w j^2/2) f g ↔
        (f,g) ∈ K.graph) ∧
      ((f,g) ∈ K.graph ↔ ∀ n, ⟪e n,g⟫_ℂ = (E n : ℂ)*⟪e n,f⟫_ℂ) ∧
      (f ∈ K.domain ↔ Memℓp (fun n => (E n : ℂ)*⟪e n,f⟫_ℂ) 2) ∧
      ((f,g) ∈ K.graph → ∃ u : Finset (Fin d → ℕ) → T.domain,
        (∀ F, (u F : Hilbert d) = ∑ n ∈ F, ⟪e n,f⟫_ℂ • e n) ∧
        (∀ F, T (u F) = ∑ n ∈ F, ((E n : ℂ)*⟪e n,f⟫_ℂ) • e n) ∧
        Tendsto (fun F => (u F : Hilbert d)) atTop (𝓝 f) ∧
        Tendsto (fun F => T (u F)) atTop (𝓝 g))) := by
  classical
  dsimp only
  let a := fun j => h^2/(2*m j)
  let b := fun j => m j*w j^2/2
  let S := schwartzOperator d a b
  let C := Submodule.span ℂ (Set.range e)
  let T := S.domRestrict C
  let K := T.closure
  let E := fun n : Fin d → ℕ => ∑ j, h*w j*((n j : ℝ)+1/2)
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (Space d))
  let es := LinearEquiv.ofInjective J.toLinearMap (SchwartzMap.injective_toLp 2 volume)
  have hS (ζ : 𝓢(Space d, ℂ)) : S (es ζ) = J (differential d a b ζ) := by
    change J (differential d a b (es.symm (es ζ))) = _
    rw [es.symm_apply_apply]
  have hes (ζ : 𝓢(Space d, ℂ)) : ((es ζ : S.domain) : Hilbert d) = J ζ := rfl
  have hEφ (n : Fin d → ℕ) : differential d a b (φ n) = E n • φ n := by
    obtain ⟨ζ, hz, hd, _⟩ := physical_hermite_tests d h m w hh hm hw n
    have heq : ζ = φ n := by ext x; rw [hz, hφ]
    simpa only [heq] using hd
  have hSeig (n : Fin d → ℕ) : S (es (φ n)) = (E n : ℂ) • e n := by
    rw [hS, hEφ]
    have hr := (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (Space d))).map_smul (E n) (φ n)
    change J (E n • φ n) = _
    rw [show J (E n • φ n) = E n • J (φ n) from hr]
    rw [he, ← algebraMap_smul ℂ (E n), RCLike.algebraMap_eq_ofReal]
    rfl
  have hC : C ≤ S.domain := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [he]
    exact (es (φ n)).2
  have hdom : T.domain = C := inf_eq_left.mpr hC
  have heig (n : Fin d → ℕ) :
      T ⟨e n, hdom ▸ Submodule.subset_span ⟨n, rfl⟩⟩ = (E n : ℂ) • e n := by
    have ht : T ⟨e n, hdom ▸ Submodule.subset_span ⟨n, rfl⟩⟩ = S (es (φ n)) :=
      (show T ≤ S from domRestrict_le).2
        (x := ⟨e n, hdom ▸ Submodule.subset_span ⟨n, rfl⟩⟩) (y := es (φ n)) (he n)
    exact ht.trans (hSeig n)
  obtain ⟨hc, hsa⟩ := eigenbasis_closable_selfAdjoint e T E hdom heig
  have hchar (f g : Hilbert d) := eigenbasis_graph_coefficients e T E hdom heig f g
  obtain ⟨hd, hs, hsc, _⟩ := compact_test_adjoint_graph d a b (0 : Hilbert d) 0
  have hSadj : S ≤ S† := hs.le_adjoint hd
  have hTK : K ≤ S† := by
    apply le_of_le_graph
    rw [← hc.graph_closure_eq_closure_graph]
    exact (adjoint_isClosed hd).submodule_topologicalClosure_eq ▸
      Submodule.topologicalClosure_mono (le_graph_of_le (domRestrict_le.trans hSadj))
  have hAdjK : S† ≤ K := by
    apply le_of_le_graph
    intro p hp
    obtain ⟨z, hz, hg⟩ := (mem_graph_iff S†).mp hp
    apply (hchar p.1 p.2).1.mpr
    intro n
    have hv := adjoint_isFormalAdjoint hd z (es (φ n))
    rw [hSeig, hes, show J (φ n) = e n from (he n).symm, inner_smul_right] at hv
    change ⟪S† z, e n⟫_ℂ = (E n : ℂ) * ⟪(z : Hilbert d), e n⟫_ℂ at hv
    rw [hz, hg] at hv
    have hv' := congrArg conj hv
    simpa only [map_mul, Complex.conj_ofReal, inner_conj_symm] using hv'
  have hadj : S† = K := le_antisymm hAdjK hTK
  have hSK : S ≤ K := hadj ▸ hSadj
  have hcl : S.closure = K := by
    apply eq_of_eq_graph
    apply le_antisymm
    · rw [← hsc.graph_closure_eq_closure_graph]
      exact hsa.isClosed.submodule_topologicalClosure_eq ▸
        Submodule.topologicalClosure_mono (le_graph_of_le hSK)
    · exact le_graph_of_le (hsc.closure_mono domRestrict_le)
  have hcore : K.HasCore C := by
    change T.closure.HasCore C
    exact Eq.mp (congrArg (fun U => T.closure.HasCore U) hdom)
      (closureHasCore T)
  have hnonneg (z : K.domain) : 0 ≤ (⟪(z : Hilbert d), K z⟫_ℂ).re := by
    have hcoef := (hchar z (K z)).1.mp (K.mem_graph z)
    obtain ⟨u, hu, hi, hl, hl'⟩ := (hchar z (K z)).2.1 hcoef
    have hfinite (F : Finset (Fin d → ℕ)) : 0 ≤ (⟪(u F : Hilbert d), T (u F)⟫_ℂ).re := by
      rw [hu, hi, e.orthonormal.inner_sum]
      rw [Complex.re_sum]
      apply Finset.sum_nonneg
      intro n _
      have hen : 0 ≤ E n := Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg hh.le (hw j).le) (by positivity)
      have hid (c : ℂ) : (conj c * ((E n : ℂ)*c)).re = E n * Complex.normSq c := by
        simp [Complex.mul_re, Complex.normSq_apply]
        ring
      rw [hid]
      exact mul_nonneg hen (Complex.normSq_nonneg _)
    exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
      (hl.inner (𝕜 := ℂ) hl')) (Eventually.of_forall hfinite)
  refine ⟨hSK, hsc, hcl, hadj, hsa, hsa.isClosed, hcore, hnonneg, ?_⟩
  intro f g
  have hwfg := (compact_test_adjoint_graph d a b f g).2.2.2
  rw [hadj] at hwfg
  refine ⟨hwfg, (hchar f g).1, (hchar f g).2.2, ?_⟩
  intro hfg
  exact (hchar f g).2.1 ((hchar f g).1.mp hfg)

#print axioms physical_graph_closure
end D5.S3.Quantum.Analysis.PhysicalGraphClosure
