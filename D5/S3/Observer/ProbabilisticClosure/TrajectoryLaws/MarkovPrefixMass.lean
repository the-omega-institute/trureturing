/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous trajectory singleton prefix masses are products of transition weights. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; the complete original license is retained in
Library/Observer/tauceti2026markov.md.
Authors: The Tau Ceti contributors
Source: https://github.com/TauCetiProject/TauCeti/tree/fbb1ce3c887a9697c1be346d135aed8b2932997a
Original files: TauCeti/Probability/Process/MarkovChain.lean and
TauCeti/Probability/Kernel/Composition/MeasureCompProd.lean.
Modified for Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
canonical routing and names; direct local inlining of homogeneous law, step,
index equivalence and required helper proofs; pinned measurable API spelling.
The original induction and quantified measurable-singleton contract are retained.
Retirement: delete this port and directly use an equivalent declaration when it
exists at the Mathlib revision actually adopted by this repository, preserving
all hypotheses, statement semantics and the standard axiom closure.
Utility is none: arbitrary prefix lengths and measurable state spaces, with no
finite enumeration, checker, numerical reduction or certified finite instance.
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass

universe u

variable {α : Type u} [MeasurableSpace α]

theorem markov_chain_law_map_prefix_apply_singleton
    (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] [IsProbabilityMeasure ν]
    [MeasurableSingletonClass α] (n : ℕ) (w : Fin (n + 1) → α) :
    ((Kernel.trajMeasure (X := fun _ => α) ν
        (fun n => κ.comap (fun u : Iic n → α => u ⟨n, mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _))).map fun x (i : Fin (n + 1)) => x i.1) {w}
      = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ} := by
  let iicEquivFin (n : ℕ) :
      ((_ : ↥(Iic n)) → α) ≃ᵐ (Fin (n + 1) → α) :=
    (MeasurableEquiv.piCongrLeft (fun _ : ↥(Iic n) => α)
      ((Iic n).orderIsoOfFin (k := n + 1) (by simp))).symm
  have coe_orderIsoIic_apply (n : ℕ) (i : Fin (n + 1)) :
      (((Iic n).orderIsoOfFin (k := n + 1) (by simp) i : ↥(Iic n)) : ℕ) = i := by
    rw [Finset.coe_orderIsoOfFin_apply]
    symm
    exact congrFun (Finset.orderEmbOfFin_unique (by simp)
      (fun j => mem_Iic.2 (Nat.le_of_lt_succ j.2)) Fin.val_strictMono) i
  have iicEquivFin_apply (n : ℕ) (u : (_ : ↥(Iic n)) → α) (i : Fin (n + 1)) :
      iicEquivFin n u i = u ⟨i.1, mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩ :=
    by
      -- `piCongrLeft` acts by precomposition, so its coercion reduces definitionally to this value.
      change u ((Iic n).orderIsoOfFin (k := n + 1) (by simp) i) = _
      congr 1
      ext
      exact coe_orderIsoIic_apply n i
  let markovStep (κ : Kernel α α) (n : ℕ) : Kernel ((_ : ↥(Iic n)) → α) α :=
    κ.comap (fun u => u ⟨n, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)
  let (n : ℕ) : IsMarkovKernel (markovStep κ n) :=
    inferInstanceAs (IsMarkovKernel (κ.comap _ _))
  let law : Measure (ℕ → α) := Kernel.trajMeasure (X := fun _ => α) ν (markovStep κ)
  let : IsProbabilityMeasure law := inferInstanceAs (IsProbabilityMeasure (Kernel.trajMeasure _ _))
  have map_prodMap_compProd_comap {W Y Z : Type u}
      [MeasurableSpace W] [MeasurableSpace Y] [MeasurableSpace Z]
      (μ : Measure W) [SFinite μ] (κ : Kernel Y Z)
      [IsSFiniteKernel κ] {f : W → Y} (hf : Measurable f) :
      (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
    have hmap : Measurable (Prod.map f (id : Z → Z)) := hf.prodMap measurable_id
    ext s hs
    rw [MeasureTheory.Measure.map_apply hmap hs,
      MeasureTheory.Measure.compProd_apply (hs.preimage hmap),
      MeasureTheory.Measure.compProd_apply hs,
      lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
    refine lintegral_congr fun w ↦ ?_
    rw [Kernel.comap_apply]
    rfl
  have markovChainLaw_map_frestrictLe_zero :
      (law).map (frestrictLe 0) =
        ν.map (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm := by
    dsimp only [law]
    rw [Kernel.trajMeasure,
      Measure.map_comp _ _ (measurable_frestrictLe _), Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self, Measure.id_comp]
  /- **The chain starts from its initial law.** -/
  have markovChainLaw_map_eval_zero :
      (law).map (fun x => x 0) = ν := by
    have hcomp : (fun x : ℕ → α => x 0)
        = (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘ frestrictLe 0 := rfl
    have hid : (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) ∘
        (MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm = id := by
      funext a
      simp [MeasurableEquiv.piUnique, Equiv.piUnique, uniqueElim_const]
    calc (law).map (fun x => x 0)
        = ((law).map (frestrictLe 0)).map
            (fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩) := by
          rw [Measure.map_map (μ := law) (f := frestrictLe 0)
            (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
            (by fun_prop) (measurable_frestrictLe 0), hcomp]
      _ = ν := by
          rw [markovChainLaw_map_frestrictLe_zero,
            Measure.map_map (μ := ν)
              (f := ⇑(MeasurableEquiv.piUnique fun _ : ↥(Iic (0 : ℕ)) => α).symm)
              (g := fun u : ((_ : ↥(Iic (0 : ℕ))) → α) => u ⟨0, mem_Iic.2 le_rfl⟩)
              (by fun_prop) (MeasurableEquiv.measurable _), hid, Measure.map_id]
  /- The original prefix extension uses the last state of this same prefix. -/
  have markovChainLaw_map_prefix_succ_eq_compProd (n : ℕ) :
      (law).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
        = ((law).map fun x (i : Fin (n + 1)) => x i.1) ⊗ₘ
          κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply (Fin.last n)) := by
    have he : Measurable (iicEquivFin n) := (iicEquivFin n).measurable
    have hmap : Measurable (Prod.map (iicEquivFin n) (id : α → α)) := he.prodMap measurable_id
    have hpair : Measurable fun x : ℕ → α => (frestrictLe n x, x (n + 1)) := by fun_prop
    have hstep : markovStep κ n
        = (κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
            (measurable_pi_apply (Fin.last n))).comap (iicEquivFin n) he := by
      ext u s hs
      simp [markovStep, Kernel.comap_apply, iicEquivFin_apply]
    have key : ((law).map (frestrictLe n)) ⊗ₘ markovStep κ n
        = (law).map (fun x => (frestrictLe n x, x (n + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    calc (law).map (fun x => ((fun i : Fin (n + 1) => x i.1), x (n + 1)))
        = ((law).map (fun x => (frestrictLe n x, x (n + 1)))).map
            (Prod.map (iicEquivFin n) id) := by
          rw [Measure.map_map hmap hpair]
          congr 1
          funext x
          apply Prod.ext
          · funext i
            simp [frestrictLe, iicEquivFin_apply]
          · rfl
      _ = (((law).map (frestrictLe n)) ⊗ₘ markovStep κ n).map
            (Prod.map (iicEquivFin n) id) := by rw [key]
      _ = ((law).map (frestrictLe n)).map (iicEquivFin n) ⊗ₘ
            κ.comap (fun w : Fin (n + 1) → α => w (Fin.last n))
              (measurable_pi_apply (Fin.last n)) := by
          rw [hstep]; exact map_prodMap_compProd_comap _ _ he
      _ = _ := by
          rw [Measure.map_map he (measurable_frestrictLe n)]
          congr 2
          funext x i
          exact iicEquivFin_apply n (frestrictLe n x) i
  change (law.map fun x (i : Fin (n + 1)) => x i.1) {w}
    = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ}
  induction n with
  | zero =>
    have hc : (fun (x : ℕ → α) (i : Fin 1) => x i.1)
        = (fun (a : α) (_ : Fin 1) => a) ∘ (fun x : ℕ → α => x 0) := by
      funext x i
      simp
    have hpre : (fun (a : α) (_ : Fin 1) => a) ⁻¹' {w} = {w 0} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      exact ⟨fun h => h 0, fun h i => by rw [h, Subsingleton.elim (0 : Fin 1) i]⟩
    rw [hc, ← Measure.map_map (by fun_prop) (by fun_prop), markovChainLaw_map_eval_zero,
      Measure.map_apply (by fun_prop) (measurableSet_singleton w), hpre]
    simp
  | succ n ih =>
    have hprod : Measurable
        fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1)) := by fun_prop
    have hpre : (fun (x : ℕ → α) (i : Fin (n + 2)) => x i.1) ⁻¹' {w}
        = (fun x : ℕ → α => ((fun i : Fin (n + 1) => x i.1), x (n + 1))) ⁻¹'
          {(Fin.init w, w (Fin.last (n + 1)))} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, funext_iff]
      refine ⟨fun h => ⟨fun i => h i.castSucc, h (Fin.last (n + 1))⟩, fun h i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact h.2
      · exact h.1 j
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w), hpre,
      ← Measure.map_apply hprod (measurableSet_singleton _),
      markovChainLaw_map_prefix_succ_eq_compProd, Measure.compProd_apply
        (measurableSet_singleton _)]
    have hint : ∀ v : Fin (n + 1) → α,
        (κ.comap (fun y : Fin (n + 1) → α => y (Fin.last n))
            (measurable_pi_apply (Fin.last n))) v
          (Prod.mk v ⁻¹' ({(Fin.init w, w (Fin.last (n + 1)))} :
            Set ((Fin (n + 1) → α) × α)))
        = Set.indicator {Fin.init w}
            (fun _ => κ (w (Fin.last n).castSucc) {w (Fin.last (n + 1))}) v := by
      intro v
      by_cases hv : v = Fin.init w
      · subst hv
        have hfibre : (Prod.mk (Fin.init w) ⁻¹'
            ({(Fin.init w, w (Fin.last (n + 1)))} : Set ((Fin (n + 1) → α) × α)))
            = {w (Fin.last (n + 1))} := by
          ext c; simp
        rw [hfibre, Kernel.comap_apply]
        simp [Fin.init]
      · have hfibre : (Prod.mk v ⁻¹'
            ({(Fin.init w, w (Fin.last (n + 1)))} : Set ((Fin (n + 1) → α) × α))) = ∅ := by
          ext c; simp [hv]
        rw [hfibre]
        simp [hv]
    rw [lintegral_congr hint, lintegral_indicator (measurableSet_singleton _),
      setLIntegral_const, ih (Fin.init w), Fin.prod_univ_castSucc]
    have hsucc : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    simp only [Fin.init, Fin.castSucc_zero, hsucc, Fin.succ_castSucc]
    ring

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
