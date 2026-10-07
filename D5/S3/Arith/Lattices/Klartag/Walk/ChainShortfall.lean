/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainShortfall
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainShortfall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.DriftChargeTotal

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainShortfall

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.LogDetMartingale

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

section Mg

variable {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ}

theorem memLp_two_mgPart (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    MemLp (mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K) 2
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hbase : MemLp (∑ k ∈ Finset.range K,
      mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k) 2
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    memLp_finsetSum' _ fun k _ =>
      memLp_two_mgIncr (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
        hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k
  have hfun : (∑ k ∈ Finset.range K, mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k)
      = mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K := by
    funext ω; simp [mgPart]
  rwa [hfun] at hbase

theorem integrable_mgPart (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    Integrable (mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  (memLp_two_mgPart hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K).integrable (by norm_num)

theorem integrable_mgPart_sq (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    Integrable (fun ω => (mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  (memLp_two_iff_integrable_sq
    (memLp_two_mgPart hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K).aestronglyMeasurable).1
    (memLp_two_mgPart hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K)

end Mg

section DriftSq

variable {cstep η a₀ r₀ c₃ κ ε : ℝ} {N K : ℕ}

theorem integrable_driftCharge_sub_cen_sq (hN : 1 ≤ N) (hη : 0 ≤ η)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) :
    Integrable (fun ω => (DriftChargeTotal.driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω
        - DriftChargeTotal.driftCen (n := n) cstep η c₃ κ ε K) ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  set P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)) with hP
  have hcap : (0 : ℝ) ≤ η ^ 2 := by positivity
  have hGi := StepTruncVariance.integrable_sum_sqTrunc (n := n) (c := cstep) hcap K
  have hMC := DriftChargeMoments.integrable_midCap_sq (q := q) (W := W) (A₀ := A₀)
    (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  have hGbd : ∀ ω, |∑ j ∈ Finset.range K,
      StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω| ≤ (K : ℝ) * η ^ 2 := by
    intro ω
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range K,
        StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω :=
      Finset.sum_nonneg fun j _ => (StepTruncVariance.sqTrunc_mem_Icc (c := cstep) hcap j ω).1
    rw [abs_of_nonneg hnn]
    calc ∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω
        ≤ ∑ _j ∈ Finset.range K, η ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            (StepTruncVariance.sqTrunc_mem_Icc (c := cstep) hcap j ω).2
      _ = (K : ℝ) * η ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hGmem : MemLp (fun ω => ∑ j ∈ Finset.range K,
      StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω) 2 P :=
    MemLp.of_bound hGi.aestronglyMeasurable ((K : ℝ) * η ^ 2)
      (by filter_upwards with ω using by rw [Real.norm_eq_abs]; exact hGbd ω)
  have hMCmem : MemLp (fun ω =>
      MidTerm.midCap q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hMC
    exact (DriftChargeMoments.integrable_midCap (q := q) (W := W) (A₀ := A₀)
      (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K).aestronglyMeasurable
  have hDmem : MemLp (fun ω => DriftChargeTotal.driftCharge q W A₀ cstep η r₀ c₃ κ ε N K ω) 2 P := by
    have hsum : MemLp (fun ω => κ * ((1 + ε) * (∑ j ∈ Finset.range K,
          StepTruncVariance.sqTrunc (n := n) cstep (η ^ 2) j ω) + (1 + 1 / ε) * (c₃ * η) ^ 2)) 2 P :=
      (((hGmem.const_mul (1 + ε)).add (memLp_const _)).const_mul κ)
    exact hsum.add hMCmem
  exact (memLp_two_iff_integrable_sq
    ((hDmem.sub (memLp_const _)).aestronglyMeasurable)).1 (hDmem.sub (memLp_const _))

end DriftSq

section Assembly

variable {xs : ι → (Fin n → ℝ)}

/-- **`hshort` at the chain**, in the shape `CutVariance.goodPathCut_var` binds, with
`L = logDet A₀ − (driftCen + s) − t`.  Every hypothesis below is a parameter of the chain or a
sign condition; no probabilistic fact is left. -/
theorem hshort_at_chain {η a₀ r₀ c₃ rr ε cstep t t' s' : ℝ} {N K : ℕ}
    (hN : 1 ≤ N)
    (hξm : ∀ j, Measurable (ChainSetup.step (ι := UT n) cstep j))
    (hτ : Measurable (tau (fun i => ChainWiring.qUT (xs i)) W A₀
      (ChainSetup.step cstep) η r₀ c₃ N))
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪ChainWiring.qUT (xs i), ChainWiring.qUT (xs j)⟫)
    (hne : ∀ i ∈ W, ChainWiring.qUT (xs i) ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2)
    (hrm : (1 + c₃) * η ≤ rr * (a₀ - (r₀ + c₃ * η)))
    (hε : 0 < ε) (ht : 0 ≤ t) (ht' : 0 < t') (hs' : 0 < s') :
    ∫ ω, max ((ChainWiring.logDet A₀
          - (DriftChargeTotal.driftCen (n := n) cstep η c₃
              ((1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2) ε K + s') - t)
        - stoppedLogDet (fun i => ChainWiring.qUT (xs i)) W A₀
            (ChainSetup.step cstep) η r₀ c₃ N K ω) 0
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (((K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2))) / (4 * t') + t')
        + (2 * (((1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2) * (1 + ε)) ^ 2
              * ((K : ℝ) * (η ^ 2 / 2) ^ 2)
            + 2 * ((K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)))) / (4 * s') := by
  set κ := (1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2 with hκ
  have hMint := integrable_mgPart (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀)
    (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  have hDint := DriftChargeTotal.integrable_driftCharge (q := fun i => ChainWiring.qUT (xs i))
    (W := W) (A₀ := A₀) (cstep := cstep) (κ := κ) (ε := ε) (N := N) (K := K)
    hN hη hA₀ hq hne hA₀m hr₀ hc₃ hlt
  have hXint := DriftStopped6.integrable_stoppedLogDet
    (P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
    (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀)
    (ξ := ChainSetup.step cstep) (N := N) hN hξm hτ hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  refine ShortfallBound.shortfall_le (X := stoppedLogDet (fun i => ChainWiring.qUT (xs i)) W A₀
      (ChainSetup.step cstep) η r₀ c₃ N K)
    (M := mgPart (fun i => ChainWiring.qUT (xs i)) W A₀ (ChainSetup.step cstep) η r₀ c₃ N K)
    (D := DriftChargeTotal.driftCharge (fun i => ChainWiring.qUT (xs i)) W A₀
      cstep η r₀ c₃ κ ε N K)
    (c := ChainWiring.logDet A₀)
    (cen := DriftChargeTotal.driftCen (n := n) cstep η c₃ κ ε K)
    ht ht' hs' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ω
    exact StoppedShortfall.logDet_stopped_ge_final (xs := xs) (W := W) (A₀ := A₀)
      (cstep := cstep) (N := N) (K := K) (ω := ω) hA₀ hq hne hA₀m hN hη hr₀ hc₃ hlt
      hrr0 hrr hrm hε
  · exact StepTruncVariance.integrable_neg_part hMint
  · exact GoodPathVar.integrable_pos_part' hDint _
  · exact GoodPathVar.integrable_pos_part hXint _
  · exact integrable_mgPart_sq (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀)
      (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  · exact integral_mgPart_sq_le (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀)
      (cstep := cstep) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt K
  · exact integrable_driftCharge_sub_cen_sq (q := fun i => ChainWiring.qUT (xs i)) (W := W)
      (A₀ := A₀) (cstep := cstep) (κ := κ) (ε := ε) (N := N) (K := K)
      hN hη hA₀ hq hne hA₀m hr₀ hc₃ hlt
  · exact DriftChargeTotal.integral_driftCharge_sub_cen_sq_le
      (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀) (cstep := cstep)
      (κ := κ) (ε := ε) (N := N) (K := K) hN hη hA₀ hq hne hA₀m hr₀ hc₃ hlt

end Assembly

end D5.S3.Arith.Lattices.Klartag.Walk.ChainShortfall
