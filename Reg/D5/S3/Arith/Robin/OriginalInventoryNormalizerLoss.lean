import D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators
open _root_.D5.S3.Arith.Robin.OriginalFirstClockTransport
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.Arith.Robin.OriginalMovingCutRow
open _root_.D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss

abbrev signature : Signature where
  Params := Unit
  State _ := OriginalWindow
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => selectedDomain X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

/-- The whole source telescope and every occurrence of its selected set remain
in the law. No assumed order, inventory charge or loss bound is substituted. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀
    (X : OriginalWindow) {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : StrictMono p) (hlabels : X.labels = Finset.univ.image p)
    {ell R : ℝ} (hcomplete : X.labels = originalLabelWindow ell)
    (hell : 243 ≤ ell)
    (hclocks : ∀ i : Fin (n + 1),
      Real.log (canonicalSource (p i) : ℝ) ∈ Icc ell R)
    (hlarge : R < (p 0 : ℝ)),
    let T : Fin (n + 1) → ℝ := fun i => Real.log (canonicalSource (p i) : ℝ)
    let U : Fin (n + 1) → ℕ := fun i => canonicalSource (p i) / p i
    let bad := Finset.univ.filter (fun i : Fin n => U i.castSucc ≠ U i.succ)
    let good := Finset.univ.filter (fun i : Fin n => U i.castSucc = U i.succ)
    let D := Real.log (U (Fin.last n) : ℝ) - Real.log (U 0 : ℝ)
    let C := (T 0 - ell) + (R - T (Fin.last n))
    StrictMono T ∧
    (∀ i, 0 < U i ∧ 5040 ∣ U i ∧ canonicalSource (p i) = p i * U i) ∧
    (∀ i : Fin n, U i.castSucc ∣ U i.succ ∧
      (GoodEdge X (p i.castSucc) (p i.succ) ↔ U i.castSucc = U i.succ)) ∧
    V.readout () () X = (⋃ i ∈ good, Icc (T i.castSucc) (T i.succ)) ∧
    (volume (Icc ell R \ V.readout () () X)).toReal =
      C + ∑ i ∈ bad, (T i.succ - T i.castSucc) ∧
    (volume (Icc ell R \ V.readout () () X)).toReal ≤ C + 2 * D ∧
    ∀ x : ℝ,
      windowMass ell R x - (∫ t in V.readout () () X, kernel t x) =
        windowMass ell (T 0) x +
          (∑ i ∈ bad, windowMass (T i.castSucc) (T i.succ) x) +
          windowMass (T (Fin.last n)) R x ∧
      0 ≤ windowMass ell R x - (∫ t in V.readout () () X, kernel t x) ∧
      windowMass ell R x - (∫ t in V.readout () () X, kernel t x) ≤
        ell ^ (-3 / 10 : ℝ) * (C + 2 * D)

private theorem actual_law : arena.Law actual :=
  @original_inventory_normalizer_loss

private theorem source_bridge :
    (type_of% (@original_inventory_normalizer_loss)) ↔ arena.Law actual := Iff.rfl

/-- A genuinely qualifying source would refute the whole-family intervention.
This conditional witness is not a completed Variation or Registration. -/
private theorem rejected_fails_at_source
    (X : OriginalWindow) {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : StrictMono p) (hlabels : X.labels = Finset.univ.image p)
    {ell R : ℝ} (hcomplete : X.labels = originalLabelWindow ell)
    (hell : 243 ≤ ell)
    (hclocks : ∀ i : Fin (n + 1),
      Real.log (canonicalSource (p i) : ℝ) ∈ Icc ell R)
    (hlarge : R < (p 0 : ℝ)) : ¬ arena.Law rejected := by
  intro h
  have hresult := h X p hp hlabels hcomplete hell hclocks hlarge
  have hset := hresult.2.2.2.1
  have hmem : R + 1 ∈ (Set.univ : Set ℝ) := Set.mem_univ _
  change R + 1 ∈ rejected.readout () () X at hmem
  rw [hset] at hmem
  obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hmem
  have hupper := (hclocks i.succ).2
  linarith [hi.2]

/- The exact source bridge and conditional intervention above are the audit
attempt. A Contract.Registration is not supplied: unconditional whole-family
variation/sensitivity and actual observational dependence on OriginalWindow
remain unproved. The conditional source telescope must not be treated as an
inhabited qualifying family or replaced by a smaller label selection.
Lawful sourceSelection/current binding also require the canonical audit run.
No declared_validated status is asserted. -/

#print axioms source_bridge
#print axioms rejected_fails_at_source

end Reg.D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss
