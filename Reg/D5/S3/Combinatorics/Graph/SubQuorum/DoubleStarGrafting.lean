import D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting

universe u

/-- The source telescope includes the entire finite nonempty graph carrier. -/
structure GraphData where
  V : Type u
  finite : Fintype V
  eq : DecidableEq V
  nonempty : Nonempty V
  graph : SimpleGraph V
  adj : DecidableRel graph.Adj

attribute [instance] GraphData.finite GraphData.eq GraphData.nonempty GraphData.adj

abbrev signature : Signature where
  Params := Unit
  State _ := GraphData.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def psiActual : Realization signature.{u} :=
  realize signature (fun _ _ p => psiSq (graftGraph p.graph)) (fun e => nomatch e)

def psiRejected : Realization signature.{u} :=
  realize signature (fun _ _ p => 5 * Fintype.card p.V + 1) (fun e => nomatch e)

abbrev psiArena : Arena where
  signature := signature.{u}
  Law r := ∀ p : GraphData.{u}, r.readout () () p = 5 * Fintype.card p.V

private def oneGraph : GraphData.{u} :=
  ⟨ULift.{u} Unit, inferInstance, inferInstance, inferInstance, ⊥, inferInstance⟩

private def twoGraph : GraphData.{u} :=
  ⟨ULift.{u} Bool, inferInstance, inferInstance, inferInstance, ⊥, inferInstance⟩

private theorem oneGraph_card : Fintype.card oneGraph.{u}.V = 1 := by
  change Fintype.card (ULift.{u} Unit) = 1
  simp

private theorem twoGraph_card : Fintype.card twoGraph.{u}.V = 2 := by
  change Fintype.card (ULift.{u} Bool) = 2
  simp

private theorem psi_actual_law : psiArena.{u}.Law psiActual.{u} := by
  intro p
  exact psiSq_graftGraph p.graph

private theorem psi_rejected_law : ¬ psiArena.{u}.Law psiRejected.{u} := by
  intro h
  have hh := h oneGraph
  change 5 * Fintype.card oneGraph.V + 1 = 5 * Fintype.card oneGraph.V at hh
  omega

private theorem psi_dependence : ObservationalDependence signature.{u} psiActual.{u} := by
  intro i
  refine ⟨(),oneGraph,twoGraph,?_⟩
  intro h
  change psiSq (graftGraph oneGraph.graph) = psiSq (graftGraph twoGraph.graph) at h
  rw [psiSq_graftGraph,psiSq_graftGraph] at h
  rw [oneGraph_card,twoGraph_card] at h
  norm_num at h

abbrev PsiSourceClaim : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [Nonempty V],
    psiSq (graftGraph F) = 5 * Fintype.card V

def psiFamilyRegistration : Registration psiArena.{u} PsiSourceClaim.{u} where
  actual := psiActual
  bridge := by
    constructor
    · intro h p; exact h p.graph
    · intro h V fv dv F nv
      exact h ⟨V,fv,dv,nv,F,Classical.decRel _⟩
  variation := ⟨psi_actual_law,psiRejected,psi_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨psiRejected,?_,rfl,psi_rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := psi_dependence

def betaActual : Realization signature.{u} :=
  realize signature (fun _ _ p => beta (graftGraph p.graph) 2) (fun e => nomatch e)

def betaRejected : Realization signature.{u} :=
  realize signature (fun _ _ p => 4 * Fintype.card p.V + beta p.graph 2 + 1)
    (fun e => nomatch e)

abbrev betaArena : Arena where
  signature := signature.{u}
  Law r := ∀ p : GraphData.{u},
    r.readout () () p = 4 * Fintype.card p.V + beta p.graph 2

private theorem beta_actual_law : betaArena.{u}.Law betaActual.{u} := by
  intro p
  exact beta_graftGraph p.graph

private theorem beta_rejected_law : ¬ betaArena.{u}.Law betaRejected.{u} := by
  intro h
  have hh := h oneGraph
  change 4 * Fintype.card oneGraph.V + beta oneGraph.graph 2 + 1 =
    4 * Fintype.card oneGraph.V + beta oneGraph.graph 2 at hh
  omega

private theorem beta_dependence : ObservationalDependence signature.{u} betaActual.{u} := by
  intro i
  refine ⟨(),oneGraph,twoGraph,?_⟩
  intro h
  change beta (graftGraph oneGraph.graph) 2 = beta (graftGraph twoGraph.graph) 2 at h
  rw [beta_graftGraph,beta_graftGraph] at h
  have hb : beta oneGraph.graph 2 ≤ Fintype.card oneGraph.V := by
    apply Finset.sup_le
    intro S _
    exact Finset.card_le_univ S
  rw [oneGraph_card,twoGraph_card] at h
  rw [oneGraph_card] at hb
  omega

abbrev BetaSourceClaim : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    [DecidableRel F.Adj] [Nonempty V],
    beta (graftGraph F) 2 = 4 * Fintype.card V + beta F 2

def betaFamilyRegistration : Registration betaArena.{u} BetaSourceClaim.{u} where
  actual := betaActual
  bridge := by
    constructor
    · intro h p; exact h p.graph
    · intro h V fv dv F fa nv
      exact h ⟨V,fv,dv,nv,F,fa⟩
  variation := ⟨beta_actual_law,betaRejected,beta_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨betaRejected,?_,rfl,beta_rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := beta_dependence

noncomputable def psiRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.psiSq_graftGraph.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.psiSq_graftGraph.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.psiFamilyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨psiArena.{u}⟩,
  objectArena := .source ⟨psiArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source psiArena.{u} ⟨psiFamilyRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ _ p => psiSq (graftGraph p.graph)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def betaRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.beta_graftGraph.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.beta_graftGraph.__information_unit,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting.betaFamilyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨betaArena.{u}⟩,
  objectArena := .source ⟨betaArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source betaArena.{u} ⟨betaFamilyRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ _ p => beta (graftGraph p.graph) 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
