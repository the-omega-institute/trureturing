import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SignedGraphSpectral.MO479815

/-! Source-bound Hermitian symmetry of the actual signed adjacency. -/

namespace Reg.D5.S3.Combinatorics.SignedGraphSpectral.MO479815

open LeanInformationAudit Matrix
open _root_.D5.S3.Combinatorics.SignedGraphSpectral.MO479815 (signedAdj signed_hermitian)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := Σ n : ℕ, SimpleGraph (Fin n)
  State p := Sym2 (Fin p.1) → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p σ => signedAdj p.2 σ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ i j => if i < j then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool),
    (r.readout () ⟨n, G⟩ σ).IsHermitian

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := Matrix.isHermitian_iff_isSymm.mp (h (⊤ : SimpleGraph (Fin 2)) (fun _ => true))
  have h01 := h'.apply 0 1
  change (if (1 : Fin 2) < 0 then (1 : ℝ) else 0) =
    (if (0 : Fin 2) < 1 then 1 else 0) at h01
  norm_num at h01

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, ⊤⟩, fun _ => true, fun _ => false, ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  change signedAdj (⊤ : SimpleGraph (Fin 2)) (fun _ => true) 0 1 =
    signedAdj (⊤ : SimpleGraph (Fin 2)) (fun _ => false) 0 1 at he
  norm_num [signedAdj, SimpleGraph.top_adj] at he

def family : Registration arena (type_of% (@signed_hermitian)) where
  actual := realize signature (fun _ p σ => signedAdj p.2 σ) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@signed_hermitian, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.SignedGraphSpectral.MO479815.signed_hermitian) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SignedGraphSpectral.MO479815.signed_hermitian_unit
  realizationName := `Reg.D5.S3.Combinatorics.SignedGraphSpectral.MO479815.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p σ => signedAdj p.2 σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SignedGraphSpectral.MO479815
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

end

end Reg.D5.S3.Combinatorics.SignedGraphSpectral.MO479815
