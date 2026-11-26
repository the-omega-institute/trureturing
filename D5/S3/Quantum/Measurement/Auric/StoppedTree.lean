/- GID: D5/S3/Quantum/Measurement/Auric/StoppedTree
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/StoppedTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forced stopping of a projective decision tree on its original register. -/

import D5.S3.Quantum.Measurement.Auric.ProtocolLimits

/-! # Forced stopping of a projective decision tree on its original register -/

namespace D5.S3.Quantum.Measurement.Auric.StoppedTree

open _root_.Matrix Filter MeasureTheory
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.Auric.ExactDistance
open D5.S3.Quantum.Measurement.Auric.DiamondClosure
open D5.S3.Quantum.Measurement.Auric.ProtocolLimits
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Measurement.Auric.ScoreReadout (protocolMap)
open D5.S3.Quantum.Measurement.Auric.SimulatorUpper
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

noncomputable section

/-- One step of a deterministic tape. Histories and classical memory can be part
of the state; the measurement remains restricted to the original register. -/
inductive Step (State : Type*)
  | halt (j : Flag) (u : Matrix.unitaryGroup Level ℂ)
  | measure (u : Matrix.unitaryGroup Level ℂ) (k : ℕ) (E : CompletePVM Level k)
      (next : Fin k → State)

structure Prefix where
  tree : Protocol Level
  halted : Terminal tree → Bool

/-- Force a stop with flag zero at the cutoff and keep the current quantum state. -/
def truncate {State : Type*} (next : State → Step State) : ℕ → State → Prefix
  | 0, _ => ⟨.leaf 0 1, fun _ => false⟩
  | n + 1, s => match next s with
    | .halt j u => ⟨.leaf j u, fun _ => true⟩
    | .measure u k E f =>
      let branches := fun i => truncate next n (f i)
      ⟨.branch u k E (fun i => (branches i).tree), fun h => (branches h.1).halted h.2⟩

private def kept (p : Prefix) (b : Bool) (h : Terminal p.tree) : Matrix (Flag × Level) Level ℂ :=
  if p.halted h = b then flagKraus (flag p.tree h) (kraus p.tree h) else 0

/-- The subnormalized channel of histories which halted before forced stopping. -/
def completed (p : Prefix) : RecordedMap := MatrixMap.of_kraus (kept p true) (kept p true)

private def unfinished (p : Prefix) : RecordedMap :=
  MatrixMap.of_kraus (kept p false) (kept p false)

private theorem split_prefix (p : Prefix) : protocolMap p.tree = completed p + unfinished p := by
  classical
  apply LinearMap.ext
  intro X
  simp only [protocolMap, completed, unfinished, MatrixMap.of_kraus, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  cases hhalt : p.halted h <;> simp [kept, hhalt]

/-- The forced-stop part of every truncated tree is completely positive. -/
theorem truncated_tail_cp (p : Prefix) : (protocolMap p.tree - completed p).IsCompletelyPositive := by
  rw [split_prefix, add_sub_cancel_left]
  exact MatrixMap.of_kraus_isCompletelyPositive _

local instance matrixContinuousENorm (ι : Type*) [Fintype ι] :
    ContinuousENorm (Matrix ι ι ℂ) := inferInstanceAs (ContinuousENorm (ι → ι → ℂ))

private theorem choi_diff (F G : RecordedMap) :
    (F - G).choi_matrix = F.choi_matrix - G.choi_matrix := rfl

private theorem cp_of_choi_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : Ω → RecordedMap) (F : RecordedMap)
    (hK : Integrable (fun ω => (K ω).choi_matrix) μ)
    (hpositive : ∀ ω, (K ω).IsCompletelyPositive)
    (hF : F.choi_matrix = ∫ ω, (K ω).choi_matrix ∂μ) : F.IsCompletelyPositive := by
  rw [MatrixMap.choi_PSD_iff_CP_map, hF]
  obtain ⟨m, w, tape, hw, _, _, he⟩ :=
    D5.S3.Analytic.Convexity.MeasurableFiniteMoments.finite_moments_probability μ hK
      (s := Set.univ) (.of_forall fun _ => Set.mem_univ _)
  rw [← he]
  apply Matrix.posSemidef_sum
  intro i _
  exact ((MatrixMap.choi_PSD_iff_CP_map _).1 (hpositive (tape i))).smul (hw i)

/-- The measured law of the actual finite-depth forced stops gives the diamond
approximation of an almost-sure terminal channel of deterministic tapes. -/
theorem inClosure_of_tape_stopping {Ω State : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (next : Ω → State → Step State) (start : Ω → State)
    (F : RecordedMap) (hF : F.IsTracePreserving) (whole stopped : ℕ → RecordedMap)
    (hwhole : ∀ n, let p := fun ω => truncate (next ω) n (start ω)
      Integrable (fun ω => (protocolMap (p ω).tree).choi_matrix) μ ∧
        (whole n).choi_matrix = ∫ ω, (protocolMap (p ω).tree).choi_matrix ∂μ)
    (hstopped : ∀ n, let p := fun ω => truncate (next ω) n (start ω)
      Integrable (fun ω => (completed (p ω)).choi_matrix) μ ∧
        (stopped n).choi_matrix = ∫ ω, (completed (p ω)).choi_matrix ∂μ)
    (hcontinuation : ∀ n, (F - stopped n).IsCompletelyPositive)
    (hhalt : Tendsto (fun n => ((F - stopped n) 1).trace.re) atTop (𝓝 0)) :
    ProtocolClosure F := by
  apply inClosure_of_almost_sure_truncations F hF whole stopped _ hcontinuation _ hhalt
  · intro n
    exact finite_of_randomized_trees μ _ _ (hwhole n).1 (hwhole n).2
  · intro n
    let p := fun ω => truncate (next ω) n (start ω)
    let K := fun ω => protocolMap (p ω).tree - completed (p ω)
    apply cp_of_choi_integral μ K
    · simp only [K, choi_diff]
      exact (hwhole n).1.sub (hstopped n).1
    · exact fun ω => truncated_tail_cp (p ω)
    · simp only [K, choi_diff]
      rw [(hwhole n).2, (hstopped n).2, integral_sub (hwhole n).1 (hstopped n).1]

end

end D5.S3.Quantum.Measurement.Auric.StoppedTree
