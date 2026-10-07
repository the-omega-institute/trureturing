/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSelector
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationIndex
import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationFamily

/-!
The actual continuous pointed coefficient selector for the free-profinite
generator retract. At finite row n it selects the code of (n, proj_n(s));
the infinity row is infinity. Every finite fiber is a clopen subset of a
single finite row. This proves continuity for empty, finite and infinite S,
without enumerating S by N or assuming derived realization.
New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez
Camargo, Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory LightProfinite OnePoint
attribute [local instance] FintypeCat.botTopology FintypeCat.discreteTopology

namespace CWSolid

def finiteApproximationSelectorFun (S : LightProfinite) :
    finiteApproximationFamilyDomain S → OnePoint ℕ
  | (∞, _) => ∞
  | (OnePoint.some n, s) =>
      OnePoint.some (finiteApproximationIndexCode S ⟨n, S.proj n s⟩)

@[simp] theorem finiteApproximationSelectorFun_infty (S : LightProfinite) (s : S) :
    finiteApproximationSelectorFun S (∞, s) = ∞ := rfl

@[simp] theorem finiteApproximationSelectorFun_nat (S : LightProfinite)
    (n : ℕ) (s : S) :
    finiteApproximationSelectorFun S ((n : OnePoint ℕ), s) =
      (finiteApproximationIndexCode S ⟨n, S.proj n s⟩ : OnePoint ℕ) := rfl

theorem finiteApproximationSelectorFun_fiber (S : LightProfinite)
    (j : finiteApproximationIndex S) :
    finiteApproximationSelectorFun S ⁻¹' {(finiteApproximationIndexCode S j : OnePoint ℕ)} =
      {x | x.1 = (j.1 : OnePoint ℕ) ∧ S.proj j.1 x.2 = j.2} := by
  ext ⟨a, s⟩
  cases a using OnePoint.rec
  · simp [finiteApproximationSelectorFun]
  · rename_i n
    change (finiteApproximationIndexCode S ⟨n, S.proj n s⟩ : OnePoint ℕ) =
      (finiteApproximationIndexCode S j : OnePoint ℕ) ↔
        (n : OnePoint ℕ) = (j.1 : OnePoint ℕ) ∧ S.proj j.1 s = j.2
    constructor
    · intro h
      have hj := (finiteApproximationIndexCode_injective S) (OnePoint.coe_injective h)
      subst j
      exact ⟨rfl, rfl⟩
    · rcases j with ⟨m, b⟩
      rintro ⟨hn, hb⟩
      have hnm : n = m := OnePoint.coe_injective hn
      subst m
      exact congrArg (fun b =>
        (finiteApproximationIndexCode S ⟨n, b⟩ : OnePoint ℕ)) hb

theorem finiteApproximationSelectorFun_fiber_clopen (S : LightProfinite) (k : ℕ) :
    IsClopen (finiteApproximationSelectorFun S ⁻¹' {(k : OnePoint ℕ)}) := by
  by_cases hk : ∃ j : finiteApproximationIndex S, finiteApproximationIndexCode S j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [finiteApproximationSelectorFun_fiber]
    have hn : IsClopen {(j.1 : OnePoint ℕ)} := by
      constructor
      · exact isClosed_singleton
      · exact (OnePoint.isOpen_iff_of_notMem (by simp)).2 (isOpen_discrete _)
    haveI : DiscreteTopology (S.component j.1) := by
      change DiscreteTopology (S.fintypeDiagram.obj ⟨j.1⟩)
      infer_instance
    exact (hn.preimage continuous_fst).inter
      ((isClopen_discrete ({j.2} : Set (S.component j.1))).preimage
        ((S.proj j.1).hom.hom.continuous.comp continuous_snd))
  · have he : finiteApproximationSelectorFun S ⁻¹' {(k : OnePoint ℕ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a, s⟩ h
      cases a using OnePoint.rec
      · simpa [finiteApproximationSelectorFun] using h
      · rename_i n
        apply hk
        exact ⟨⟨n, S.proj n s⟩, OnePoint.coe_injective h⟩
    rw [he]
    exact isClopen_empty

theorem finiteApproximationSelectorFun_continuous (S : LightProfinite) :
    Continuous (finiteApproximationSelectorFun S) := by
  rw [continuous_def]
  intro U hU
  by_cases hInf : (∞ : OnePoint ℕ) ∈ U
  · rw [← isClosed_compl_iff]
    have hfinite : (((↑) : ℕ → OnePoint ℕ) ⁻¹' U)ᶜ.Finite := by
      have h := (OnePoint.isOpen_iff_of_mem hInf).1 hU
      simpa only [isClosed_discrete, isCompact_iff_finite, true_and] using h
    have heq : (finiteApproximationSelectorFun S ⁻¹' U)ᶜ =
        ⋃ k ∈ (((↑) : ℕ → OnePoint ℕ) ⁻¹' U)ᶜ,
          finiteApproximationSelectorFun S ⁻¹' {(k : OnePoint ℕ)} := by
      ext ⟨a, s⟩
      cases a using OnePoint.rec
      · simp [finiteApproximationSelectorFun, hInf]
      · rename_i n
        simp [finiteApproximationSelectorFun]
    rw [heq]
    exact hfinite.isClosed_biUnion fun k _ =>
      (finiteApproximationSelectorFun_fiber_clopen S k).isClosed
  · have heq : finiteApproximationSelectorFun S ⁻¹' U =
        ⋃ k ∈ ((↑) : ℕ → OnePoint ℕ) ⁻¹' U,
          finiteApproximationSelectorFun S ⁻¹' {(k : OnePoint ℕ)} := by
      ext ⟨a, s⟩
      cases a using OnePoint.rec
      · simp [finiteApproximationSelectorFun, hInf]
      · rename_i n
        simp [finiteApproximationSelectorFun]
    rw [heq]
    exact isOpen_biUnion fun k _ =>
      (finiteApproximationSelectorFun_fiber_clopen S k).isOpen

def finiteApproximationSelector (S : LightProfinite) :
    finiteApproximationFamilyDomain S ⟶ LightProfinite.of (OnePoint ℕ) :=
  ConcreteCategory.ofHom ⟨finiteApproximationSelectorFun S,
    finiteApproximationSelectorFun_continuous S⟩

end CWSolid
