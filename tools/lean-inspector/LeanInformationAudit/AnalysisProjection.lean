import LeanInformationAudit.ProjectionCertificates

namespace LeanInformationAudit

open Lean Lean.Meta
open D5.S3.ConceptDynamics.InformationEscape

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

def projectionExclusiveTotal {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) : Nat :=
  Finset.univ.sum catalog.uniqueCaptureCount

def projectionComparisonLabel (comparison : Catalog.KernelComparison) : String :=
  match comparison with
  | .equal => "equal"
  | .strictlyFiner => "strictly_finer"
  | .strictlyCoarser => "strictly_coarser"
  | .incomparable => "incomparable"

def projectionWitnessOrdinals {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (enum : Arena.StateEnumeration arena) (finer coarser : catalog.Index) :
    Option (Nat × Nat) :=
  (catalog.refinementWitness enum finer coarser).map fun pair =>
    (enum.states.idxOf pair.1, enum.states.idxOf pair.2)

structure AnalysisProjectionRecord where
  exclusiveCaptureTotal : Nat := 0
  overlap : Array OverlapRow := #[]
  refinement : Array RefinementRow := #[]
  equivalenceClasses : Array EquivalenceRow := #[]
  roleTotals : Array (String × Nat) := #[]
  spectrum : Array SpectrumRow := #[]
  certificates : Array (String × Name) := #[]

def prepareMatrices (catalog enum : Expr) (members : Array Name) (certPrefix : Name) :
    ProjectionM (Array OverlapRow × Array RefinementRow × Array EquivalenceRow ×
      Array (String × Name)) := do
  let mut overlap := #[]
  let mut refinement := #[]
  let mut certificates := #[]
  for i in [:members.size] do
    let left ← ProjectionProof.fin i members.size
    for j in [:members.size] do
      let right ← ProjectionProof.fin j members.size
      let suffix := s!"refinement_{i}_{j}"
      let comparison ← mkAppM ``Catalog.kernelComparison #[catalog, left, right]
      let comparisonLabel : String ← reduceEval
        (← mkAppM ``projectionComparisonLabel #[comparison])
      let inclusion ← mkAppM ``Catalog.KernelRefines #[catalog, left, right]
      let inclusionInstance ← mkAppM ``Catalog.kernelRefinesDecidable #[catalog, left, right]
      let included : Bool ← reduceEval
        (← mkAppOptM ``decide #[some inclusion, some inclusionInstance])
      let ordinalExpression ← mkAppM ``projectionWitnessOrdinals #[catalog, enum, left, right]
      let ordinals ← whnf ordinalExpression
      let facts ← mkAppM ``Catalog.kernelComparison_spec #[catalog, enum, left, right]
      let proofName ← if included then
        let evidence ← mkAppOptM ``of_decide_eq_true #[some inclusion, some inclusionInstance,
          some (← mkEqRefl (mkConst ``Bool.true))]
        some <$> ProjectionProof.proof (certPrefix.str (suffix ++ "_inclusion")) evidence
      else pure none
      let counterexample ← if ordinals.isAppOfArity ``Option.some 2 then do
        let pair := ordinals.getArg! 1
        let first : Nat ← reduceEval (← mkAppM ``Prod.fst #[pair])
        let second : Nat ← reduceEval (← mkAppM ``Prod.snd #[pair])
        pure (some (first, second))
      else pure none
      let witnessEq ← mkDecideProof (← mkEq ordinalExpression (toExpr counterexample))
      let labelEq ← mkDecideProof (← mkEq
        (← mkAppM ``projectionComparisonLabel #[comparison]) (mkStrLit comparisonLabel))
      let certificate ← ProjectionProof.proof (certPrefix.str suffix)
        (← ProjectionProof.conjunction #[facts, witnessEq, labelEq])
      certificates := certificates.push (suffix, certificate)
      refinement := refinement.push {
        finer := members[i]!, coarser := members[j]!, comparison := comparisonLabel,
        proofName, counterexample }
      if i == j || members[i]!.toString < members[j]!.toString then
        let expression ← mkAppM ``Catalog.pairwiseCaptureOverlapCount #[catalog, left, right]
        let (count, certificate) ← ProjectionProof.count
          (certPrefix.str s!"overlap_{i}_{j}") expression
        overlap := overlap.push { left := members[i]!, right := members[j]!, count, certificate }
  let mut classes := #[]
  let mut visited : Array Name := #[]
  for i in [:members.size] do
    if visited.contains members[i]! then continue
    let indices := (Array.range members.size).filter fun j =>
      refinement[i * members.size + j]!.comparison == "equal"
    let classMembers := indices.map (members[·]!)
    let mut proofs := #[]
    for j in indices do
      for k in indices do
        let proposition ← mkAppM ``Catalog.KernelEquivalent
          #[catalog, ← ProjectionProof.fin j members.size, ← ProjectionProof.fin k members.size]
        let instanceValue ← mkAppM ``projectionEquivalentDecidable
          #[catalog, ← ProjectionProof.fin j members.size, ← ProjectionProof.fin k members.size]
        proofs := proofs.push (← mkAppOptM ``of_decide_eq_true
          #[some proposition, some instanceValue, some (← mkEqRefl (mkConst ``Bool.true))])
    let certificate ← ProjectionProof.proof (certPrefix.str s!"equivalence_{i}")
      (← ProjectionProof.conjunction proofs)
    classes := classes.push { members := classMembers, certificate }
    visited := visited ++ classMembers
  pure (overlap, refinement, classes, certificates)

def prepareAnalysisProjection (catalog enum : Expr) (members : Array Name) (certPrefix : Name) :
    ProjectionM AnalysisProjectionRecord := do
  let (overlap, refinement, equivalenceClasses, matrixCertificates) ←
    prepareMatrices catalog enum members certPrefix
  let (exclusiveCaptureTotal, exclusiveCertificate) ← ProjectionProof.count
    (certPrefix.str "exclusive_total") (← mkAppM ``projectionExclusiveTotal #[catalog])
  let mut certificates := matrixCertificates.push ("exclusive_total", exclusiveCertificate)
  let mut spectrum := #[]
  for k in [:members.size + 1] do
    let expression ← mkAppM ``Catalog.captureSpectrum
      #[catalog, ← ProjectionProof.fin k (members.size + 1)]
    let (count, certificate) ← ProjectionProof.count (certPrefix.str s!"spectrum_{k}") expression
    spectrum := spectrum.push { k, count, certificate }
  let mut roleTotals := #[]
  for mask in [1:16] do
    let bits := (Array.range 4).map fun bit => mask / 2 ^ (3 - bit) % 2 == 1
    let signature ← ProjectionProof.vector
      (bits.map fun bit => mkConst (if bit then ``Bool.true else ``Bool.false))
    let expression ← mkAppM ``Catalog.roleHistogramTotal #[catalog, signature]
    let label := String.ofList (bits.toList.map fun bit => if bit then '1' else '0')
    let (count, certificate) ← ProjectionProof.count (certPrefix.str s!"role_{label}") expression
    certificates := certificates.push (s!"role_{label}", certificate)
    if count != 0 then roleTotals := roleTotals.push (label, count)
  for (key, theoremName) in #[
      ("spectrum_total", ``Catalog.spectrum_total),
      ("spectrum_zero", ``Catalog.spectrum_zero),
      ("spectrum_first_moment", ``Catalog.spectrum_first_moment),
      ("spectrum_second_moment", ``Catalog.spectrum_second_moment),
      ("overlap_symmetric_diagonal", ``Catalog.overlap_symmetric_diagonal),
      ("refinement_overlap", ``Catalog.refinement_overlap),
      ("role_total", ``Catalog.catalogRoleHistogram_sum)] do
    let certificate ← ProjectionProof.proof (certPrefix.str key) (← mkAppM theoremName #[catalog])
    certificates := certificates.push (key, certificate)
  pure {
    exclusiveCaptureTotal, overlap, refinement, equivalenceClasses, roleTotals,
    spectrum, certificates }

def prepareLayerProjection (schedule : Expr) (chainId : String) (certPrefix : Name) :
    ProjectionM LayerChainRow := do
  let chain ← mkAppM ``GeneratorSchedule.toLayerChain #[schedule]
  let length : Nat ← reduceEval (← mkAppM ``LayerChain.length #[chain])
  let mut kernels := #[]
  let mut layers := #[]
  let mut inclusionCertificates := #[]
  for i in [:length + 1] do
    let index ← ProjectionProof.fin i (length + 1)
    let kernel ← mkAppM ``LayerChain.kernel #[chain, index]
    kernels := kernels.push (← ProjectionProof.value (certPrefix.str s!"kernel_{i}") kernel)
    let (count, certificate) ← if i == 0 then do
        let evidence ← mkAppM ``projectionInitialLayerCount_eq #[schedule]
        pure (0, ← ProjectionProof.proof (certPrefix.str s!"layer_{i}") evidence)
      else do
        let position ← ProjectionProof.fin (i - 1) length
        let expression ← mkAppM ``GeneratorSchedule.incrementCount #[schedule, position]
        ProjectionProof.count (certPrefix.str s!"layer_{i}") expression
    layers := layers.push { count, certificate }
    if i < length then
      let inclusion ← mkAppM ``LayerChain.refines
        #[chain, ← ProjectionProof.fin i length]
      inclusionCertificates := inclusionCertificates.push
        (← ProjectionProof.proof (certPrefix.str s!"inclusion_{i}") inclusion)
  let (count, certificate) ← ProjectionProof.count (certPrefix.str "unresolved")
    (← mkAppM ``LayerChain.unresolvedCount #[chain])
  let partitionCertificate ← ProjectionProof.proof (certPrefix.str "partition")
    (← mkAppM ``LayerChain.layeredCapture_partition #[chain])
  pure {
    chainId, kernels, inclusionCertificates, layers,
    unresolved := { count, certificate }, partitionCertificate }

end LeanInformationAudit
