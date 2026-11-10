import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.TreeMarkovStability
import Reg.Support.DependentFamily

namespace Reg.D5.S3.TotalVariation.TreeMarkovStability

open _root_.D5.S3.TotalVariation.TreeMarkovStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.Pinsker (totalVariation)
open _root_.D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)
open scoped BigOperators Classical
attribute [local instance] _root_.D5.S3.TotalVariation.TreeMarkovStability.configurationFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

structure Parameters where
  V : Type
  finiteV : Fintype V
  G : SimpleGraph V
  tree : G.IsTree
  card : 2 ≤ @Fintype.card V finiteV
  X : V → Type
  finiteX : ∀ v, Fintype (X v)

abbrev pack {V : Type} [fv : Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hV : 2 ≤ Fintype.card V) (X : V → Type) [fx : ∀ v, Fintype (X v)] : Parameters :=
  ⟨V,fv,G,hG,hV,X,fx⟩

abbrev signature : Signature where
  Params := Parameters
  State p := @Family p.V p.G p.X p.finiteX
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (∀ v, p.X v) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p F => @markovLaw p.V p.finiteV p.G p.tree p.card p.X p.finiteX F)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (hV : 2 ≤ Fintype.card V) (X : V → Type) [∀ v, Fintype (X v)]
    (F H : Family G X),
    (∀ x, 0 ≤ r.readout () (pack G hG hV X) F x) ∧ (∑ x, r.readout () (pack G hG hV X) F x) = 1 ∧
    (∀ x, 0 ≤ r.readout () (pack G hG hV X) H x) ∧ (∑ x, r.readout () (pack G hG hV X) H x) = 1 ∧
    (∀ i, pushforward (fun x : ∀ v, X v => x i) (r.readout () (pack G hG hV X) F) = F.node i) ∧
    (∀ i, pushforward (fun x : ∀ v, X v => x i) (r.readout () (pack G hG hV X) H) = H.node i) ∧
    (∀ i j, G.Adj i j → pushforward (fun x : ∀ v, X v => (x i,x j))
      (r.readout () (pack G hG hV X) F) = F.edge i j) ∧
    (∀ i j, G.Adj i j → pushforward (fun x : ∀ v, X v => (x i,x j))
      (r.readout () (pack G hG hV X) H) = H.edge i j) ∧
    totalVariation (r.readout () (pack G hG hV X) F) (r.readout () (pack G hG hV X) H) ≤
      min 1 (edgeBudget F H + nodeBudget G (fun i => totalVariation (F.node i) (H.node i))) ∧
    ((∀ i, F.node i = H.node i) →
      totalVariation (r.readout () (pack G hG hV X) F) (r.readout () (pack G hG hV X) H) ≤ min 1 (edgeBudget F H)) ∧
    (∀ root : V, ∃ t : TreeOrder G, t.root = root) ∧
    (∀ (t : TreeOrder G) (K : ∀ i j, X i → X j → ℝ),
      (∀ i j, G.Adj i j → ∀ a b, F.node i a ≠ 0 →
        K i j a b = F.edge i j (a,b) / F.node i a) →
      factorMass t F K = r.readout () (pack G hG hV X) F)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  by_contra h
  apply edge_coefficient_one_sharp
  refine ⟨0, by norm_num, ?_⟩
  intro V fv G hG hV X fx F H _
  have he : markovLaw G hG hV F = markovLaw G hG hV H := by
    by_contra hn
    exact h ⟨pack G hG hV X,F,H,hn⟩
  simp [he, totalVariation]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p,F,H,hn⟩ := dependence ()
  have hn' : ¬ ∀ x, actual.readout () p F x = actual.readout () p H x := by
    intro he
    exact hn (funext he)
  obtain ⟨x,_⟩ := not_forall.mp hn'
  have hh := (@h p.V p.finiteV p.G p.tree p.card p.X p.finiteX F H).1 x
  norm_num [rejected, realize] at hh

def source_registration : Registration arena (type_of% @actual_tree_stability) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_tree_stability,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_tree_stability) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.TotalVariation.TreeMarkovStability.unit
  realizationName := `Reg.D5.S3.TotalVariation.TreeMarkovStability.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p F => @markovLaw p.V p.finiteV p.G p.tree p.card p.X p.finiteX F)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.TotalVariation.TreeMarkovStability
