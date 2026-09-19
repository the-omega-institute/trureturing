/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HasLawTrajectory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Own-history conditional distributions determine the actual trajectory law. -/

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Authors: Rémy Degenne, Paulo Rauber
Released under Apache 2.0 license; the complete original license is retained in
Library/Observer/lml2026trajectory.md.
Source: https://github.com/LeanMachineLearning/LML/tree/357e9dd450b76d6ff85955280bb4721a2c520442
Modified for Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
canonical routing and names, required pinned API adaptations, and local inlining
of upstream helper proofs and definitions. No source-specific specialization.
Retirement: delete this port and directly use an equivalent declaration when it
exists at the Mathlib revision actually adopted by this repository, preserving
all hypotheses, statement semantics and the standard axiom closure.
Utility is none: this general process theorem is neither finite enumeration,
a checker, a numerical reduction nor a certified finite instance.
-/
import Mathlib.Probability.HasCondDistrib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.FiniteDimensionalLaws
open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open ProbabilityTheory.Kernel
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
universe u v
variable {Ω : Type v} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
set_option backward.isDefEq.respectTransparency false in
theorem has_law_traj_measure [IsFiniteMeasure P]
    {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n))
    (h0 : HasLaw (Y 0) μ₀ P)
    (h_condDistrib : ∀ n, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P) :
    HasLaw (fun ω n ↦ Y n ω) (trajMeasure μ₀ κ) P := by
  let IicSuccProd (n : ℕ) :
      MeasurableEquiv (Π i : Iic (n + 1), X i) ((Π i : Iic n, X i) × X (n + 1)) :=
    (MeasurableEquiv.IicProdIoc (Nat.le_succ n)).symm.trans
      (prodCongr (refl _) (piSingleton n).symm)
  have symm_IicSuccProd (n : ℕ) :
      (IicSuccProd n).symm =
        (prodCongr (refl _) (piSingleton n)).trans
          (MeasurableEquiv.IicProdIoc (Nat.le_succ n)) := rfl
  have IicSuccProd_apply (n : ℕ) (h : Π i : Iic (n + 1), X i) :
      IicSuccProd n h = (fun i : Iic n ↦ h ⟨i.1, mem_Iic.mpr (le_trans (mem_Iic.mp i.2) (Nat.le_succ n))⟩, h ⟨n + 1, by simp⟩) := rfl
  have coe_prodCongr {α β γ δ : Type u}
      {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
      {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
      (e₁ : MeasurableEquiv α β) (e₂ : MeasurableEquiv γ δ) :
      (prodCongr e₁ e₂ : (α × γ) → (β × δ)) = Prod.map e₁ e₂ := rfl
  have coe_refl {α : Type u} {mα : MeasurableSpace α} : (refl α : α → α) = id := rfl
  have hasLaw_Iic_of_forall_hasCondDistrib'
      {Y : (n : ℕ) → Ω → X n} (h0 : HasLaw (Y 0) μ₀ P) {N n : ℕ}
      (h_condDistrib : ∀ n < N, HasCondDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P)
      (hn : n ≤ N) :
      HasLaw (fun ω (i : Iic n) ↦ Y i ω)
        ((partialTraj κ 0 n) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm)) P := by
    revert hn
    induction n with
    | zero =>
      intro _
      simp only [piUnique_symm_apply, partialTraj_self, Measure.id_comp]
      rw [← h0.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      constructor
      · have h_meas := h0.aemeasurable
        have : (fun ω (i : Iic 0) ↦ Y i ω) = (MeasurableEquiv.piUnique _).symm ∘ (Y 0) := by
          ext ω i
          simp only [piUnique_symm_apply, Function.comp_apply]
          rw [Unique.eq_default i]
          rfl
        rw [this]
        exact AEMeasurable.comp_aemeasurable (by fun_prop) h_meas
      · congr
        ext ω i
        simp only [Function.comp_apply]
        rw [Unique.eq_default i]
        rfl
    | succ n hn =>
      intro hn_le
      specialize h_condDistrib n (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn_le)
      specialize hn (le_trans (Nat.le_succ n) hn_le)
      have h_law := hn.prodMk_of_hasCondDistrib h_condDistrib
      have : (fun ω (i : Iic (n + 1)) ↦ Y i ω) =
          (IicSuccProd n).symm ∘
            (fun ω ↦ (fun i : Iic n ↦ Y i ω, Y (n + 1) ω)) := by
        suffices (IicSuccProd n) ∘ (fun ω (i : Iic (n + 1)) ↦ Y i ω) =
            (fun ω ↦ (fun i : Iic n ↦ Y i ω, Y (n + 1) ω)) by
          rw [← this, ← Function.comp_assoc, MeasurableEquiv.symm_comp_self]
          simp
        ext ω : 1
        simp [IicSuccProd_apply]
      rw [this]
      refine HasLaw.comp ⟨by fun_prop, ?_⟩ h_law
      rw [Measure.compProd_eq_comp_prod, partialTraj_succ_eq_comp (by simp), Measure.comp_assoc,
        ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc]
      congr 1
      rw [← Kernel.comp_assoc]
      congr
      rw [Kernel.deterministic_comp_eq_map, partialTraj_succ_self, symm_IicSuccProd]
      rw [MeasurableEquiv.coe_trans, coe_prodCongr]
      rw [Kernel.map_comp_right _ (by fun_prop) (by fun_prop),
        ← Kernel.map_prod_map _ _ (by fun_prop) (by fun_prop)]
      congr
      simp [coe_refl]
  have trajMeasure_map_frestrictLe (n : ℕ) :
      (trajMeasure μ₀ κ).map (frestrictLe n) =
        (partialTraj κ 0 n) ∘ₘ (μ₀.map (MeasurableEquiv.piUnique _).symm) := by
    rw [trajMeasure, ← Measure.deterministic_comp_eq_map (by fun_prop), Measure.comp_assoc,
      Kernel.deterministic_comp_eq_map, traj_map_frestrictLe]
  refine ⟨by fun_prop, ?_⟩
  refine IsProjectiveLimit.unique (P := fun (J : Finset ℕ) ↦ P.map (fun ω (i : J) ↦ Y i ω)) ?_ ?_
  · exact isProjectiveLimit_map (by fun_prop)
  rw [isProjectiveLimit_nat_iff]
  swap; · exact isProjectiveMeasureFamily_map_restrict (by fun_prop)
  intro n
  rw [(hasLaw_Iic_of_forall_hasCondDistrib' h0 (fun n _ ↦ h_condDistrib n) (le_refl n)).map_eq,
    trajMeasure_map_frestrictLe]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
