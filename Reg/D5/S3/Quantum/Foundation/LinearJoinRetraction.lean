import D5.S3.Quantum.Foundation.LinearJoinRetraction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The original congruence family retains the full real ROG source telescope.
The source equivalence and actual law are provided. Whole-family intervention,
role sensitivity, observational dependence and source selection remain unproved;
no four-slot registration is declared here. -/

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Foundation.LinearJoinRetraction

open _root_.D5.S3.Quantum.Foundation.LinearJoinRetraction
open _root_.D5.S3.Quantum.Foundation.SectionROGFrame
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  Index : Type u
  [finite : Fintype Index]
  [decidable : DecidableEq Index]
  join : RealJoin Index

attribute [instance] Inputs.finite Inputs.decidable

abbrev joinSignature : Signature where
  Params := Inputs.{u}
  State P := HermitianMat P.Index ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := HermitianMat P.Index ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization joinSignature.{u} :=
  realize joinSignature (fun b P X =>
    if b then P.join.swap.congruence X else P.join.congruence X)
    (fun e => nomatch e)

def observedSide {ι : Type u} [Fintype ι] [DecidableEq ι] (J : RealJoin ι)
    (readout : HermitianMat ι ℝ → HermitianMat ι ℝ) : Prop :=

  (∀ X : HermitianMat ι ℝ, X ∈ J.cone ↔ X ∈ J.L ∧ 0 ≤ X ∧ X.support ≤ J.U) ∧
  (∀ X : HermitianMat ι ℝ, X ∈ J.cone ↔ X ∈ J.space ∧ 0 ≤ X) ∧
  ROG J.space ∧
  (SectionROGFrame.base J.space).extremePoints ℝ = pureRanks J.space ∧
  (∀ p : J.space, p.val ∈ pureRanks J.space →
    (J.inclusion p).val ∈ pureRanks J.L) ∧
  (∃ R : J.L →ₗ[ℝ] J.space,
    (∀ X : J.L, (R X).val = readout X.val) ∧
    (∀ X : J.space, R (J.inclusion X) = X) ∧
    (∀ X : J.L, X ∈ sectionCone J.L →
      R X ∈ sectionCone J.space ∧ traceUnit J.space (R X) ≤ traceUnit J.L X) ∧
    (∀ g : J.space →ₗ[ℝ] ℝ, proper (sectionCone J.space) (traceUnit J.space) g →
      proper (sectionCone J.L) (traceUnit J.L) (g.comp R) ∧
      (g.comp R).comp J.inclusion = g)) ∧
  (∀ g : J.space →ₗ[ℝ] ℝ, proper (sectionCone J.space) (traceUnit J.space) g →
    ∃ f : J.L →ₗ[ℝ] ℝ, proper (sectionCone J.L) (traceUnit J.L) f ∧
      f.comp J.inclusion = g) ∧
  (∀ p x : J.space,
    comparison (sectionCone J.L) (traceUnit J.L) (J.inclusion p) (J.inclusion x) =
      comparison (sectionCone J.space) (traceUnit J.space) p x) ∧
  (∀ p x : J.space, traceUnit J.space p = 1 → x ∈ sectionCone J.space →
    ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
      g x = comparison (sectionCone J.space) (traceUnit J.space) p x) ∧
  (∀ p x : J.space, traceUnit J.space p = 1 → x ∈ sectionCone J.space →
    (comparison (sectionCone J.space) (traceUnit J.space) p x = 0 ↔
      ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
        g x = 0)) ∧
  (nativeG2 J.L → nativeG2 J.space)


abbrev arena : Arena where
  signature := joinSignature.{u}
  Law O := ∀ P : Inputs.{u},
    observedSide P.join (O.readout false P) ∧
    observedSide P.join.swap (O.readout true P)

abbrev sourceScope : Prop := type_of% (@RealJoin.real_join_retractions.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.Index P.finite P.decidable P.join
  · intro h Index finite decidable J
    exact h (@Inputs.mk Index finite decidable J)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@RealJoin.real_join_retractions.{u})

private theorem singleton_rog :
    ROG (⊤ : Submodule ℝ (HermitianMat (Fin 1) ℝ)) := by
  intro X _ hpos
  have ha : 0 ≤ X (0 : Fin 1) (0 : Fin 1) :=
    (HermitianMat.zero_le_iff.mp hpos).diag_nonneg
  by_cases hz : X (0 : Fin 1) (0 : Fin 1) = 0
  · refine ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    apply HermitianMat.ext
    ext i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    subst j
    simpa using hz
  · let v : EuclideanSpace ℝ (Fin 1) :=
      WithLp.toLp 2 (fun _ => Real.sqrt (X (0 : Fin 1) (0 : Fin 1)))
    have hv : v ≠ 0 := by
      intro h
      have hh := congrArg (fun w : EuclideanSpace ℝ (Fin 1) => w (0 : Fin 1)) h
      have hs : Real.sqrt (X (0 : Fin 1) (0 : Fin 1)) = 0 := by simpa [v] using hh
      exact hz ((Real.sqrt_eq_zero ha).mp hs)
    refine ⟨1, fun _ => v, fun _ => ⟨hv, Submodule.mem_top⟩, ?_⟩
    apply HermitianMat.ext
    ext i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    subst j
    simp [rankOne, v, ← sq, Real.sq_sqrt ha]

private def singletonJoin : RealJoin (Fin 1) where
  L := ⊤
  identity_mem := Submodule.mem_top
  rog := singleton_rog
  Y := {v | v ≠ 0}
  Z := {v | v ≠ 0}
  U := ⊤
  W := ⊤
  nonzero_Y := by simp
  nonzero_Z := by simp
  span_Y := by
    apply top_unique
    intro v _
    by_cases hv : v = 0
    · rw [hv]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hv
  span_Z := by
    apply top_unique
    intro v _
    by_cases hv : v = 0
    · rw [hv]; exact Submodule.zero_mem _
    · exact Submodule.subset_span hv
  join := by simp
  rays v hv := by simp [hv]
  overlap := by ext v; simp

/-- The full source domain includes the nonzero one dimensional real PSD section. -/
theorem source_domain_inhabited : Nonempty (RealJoin (Fin 1)) := ⟨singletonJoin⟩

example : singletonJoin.SideConclusion ∧ singletonJoin.swap.SideConclusion :=
  RealJoin.real_join_retractions singletonJoin

end Reg.D5.S3.Quantum.Foundation.LinearJoinRetraction
