/- GID: D5/S3/Combinatorics/Graph/KyFanGap/BlowUp
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/BlowUp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Blow-up scaling and the supremum description of normalized graph maxima. -/

import D5.S3.Combinatorics.Graph.KyFanGap.Upper

/-! Blow-up constructions for normalized graph maxima. -/

noncomputable section

open scoped BigOperators Kronecker

namespace D5.S3.Combinatorics.Graph.KyFanGap

def blowUpMatrix {m t : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (m * t)) (Fin (m * t)) ℝ :=
  fun i j => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1

def blowUpScalingStatement : Prop :=
  ∀ (k m t : ℕ) (A : Matrix (Fin m) (Fin m) ℝ),
    kyFan k (n := m * t) (blowUpMatrix (t := t) A) = t * kyFan k A

def normalizedSupremum (k : ℕ) : ℝ :=
  ⨆ m : ℕ, xi k m / m

def limitExistenceStatement : Prop :=
  ∀ k : ℕ, ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => xi k n / n)
    Filter.atTop (nhds L) ∧ L = normalizedSupremum k

end D5.S3.Combinatorics.Graph.KyFanGap
