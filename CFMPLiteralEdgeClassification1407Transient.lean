import CFMPLiteralEdgeFibers1394Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate
open D5.S3.Geometry.Gluing.LiteralSixPairingCandidate (literalPairing)
open D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate
  (O classIndex representative related_class label_normalize original_fiber_card)

-- Exact temporary applications; all finite-instance and bind-only.
def originalGlobalEquiv : literalPairing.GlobalEdge ≃ Fin 3 where
  toFun := Quotient.lift classIndex (fun _ _ h => related_class h)
  invFun i := literalPairing.edgeLabel 0 (i.castLE (by decide))
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro o
    change literalPairing.edgeLabel 0 ((classIndex o).castLE (by decide)) =
      literalPairing.edgeLabel o.1 o.2
    exact (label_normalize o).symm
  right_inv i := by
    change classIndex (0,i.castLE (by decide)) = i
    fin_cases i <;> decide

theorem originalGlobalEquiv_label (o : O) :
    originalGlobalEquiv (literalPairing.edgeLabel o.1 o.2) = classIndex o := rfl

theorem global_card : Nat.card literalPairing.GlobalEdge = 3 := by
  simpa only [Nat.card_fin] using Nat.card_congr originalGlobalEquiv

theorem original_card_at (o : O) :
    Nat.card {z : O // literalPairing.edgeLabel z.1 z.2 =
      literalPairing.edgeLabel o.1 o.2} = (![10,8,18] : Fin 3 → ℕ) (classIndex o) := by
  have h := label_normalize o
  change literalPairing.edgeLabel o.1 o.2 =
    literalPairing.edgeLabel 0 ((classIndex o).castLE (by decide)) at h
  simpa only [h] using original_fiber_card (classIndex o)

theorem all_degrees_at_least_six (o : O) :
    6 ≤ Nat.card {z : O // literalPairing.edgeLabel z.1 z.2 =
      literalPairing.edgeLabel o.1 o.2} := by
  rw [original_card_at]
  have h : ∀ i : Fin 3, 6 ≤ (![10,8,18] : Fin 3 → ℕ) i := by decide
  exact h (classIndex o)
end D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate.originalGlobalEquiv,
      ``D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate.originalGlobalEquiv_label,
      ``D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate.global_card,
      ``D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate.original_card_at,
      ``D5.S3.Geometry.Gluing.LiteralEdgeClassification1407Candidate.all_degrees_at_least_six] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1407 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1407 disallowed {ax}"
    Lean.logInfo m!"CFMP1407 CHECKED {name} axioms={axioms}"
