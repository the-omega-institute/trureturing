import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
open D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema
noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev lowerArena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hD : 1 ≤ G.maxDegree),
    (G.maxDegree : ℝ) / (1 + Real.sqrt G.maxDegree) ^ 2 ≤ R.readout () () (kappa G)

def lowerFamily : Registration lowerArena.{u} (type_of% @maximum_degree_lower_bound.{u}) := by
  have hn : ¬lowerArena.{u}.Law rejected := by
    intro h
    let V := ULift.{u} (Option (Fin 1))
    let G := SimpleGraph.starGraph (ULift.up none : V)
    have hd : 1 ≤ G.maxDegree := by
      have he := G.degree_le_maxDegree (ULift.up none)
      simpa [G, SimpleGraph.degree_starGraph_center] using he
    have hh := h G hd
    change (G.maxDegree : ℝ) / (1 + Real.sqrt G.maxDegree) ^ 2 ≤ -1 at hh
    have hz : 0 ≤ (G.maxDegree : ℝ) / (1 + Real.sqrt G.maxDegree) ^ 2 := by positivity
    linarith
  have hp : lowerArena.{u}.Law actual := @maximum_degree_lower_bound.{u}
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨hp, rejected, hn⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

abbrev starArena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (hm : 1 ≤ m),
    let H := SimpleGraph.starGraph (none : Option (Fin m))
    let t : ℝ := 1 / (1 + Real.sqrt m)
    let a : Option (Fin m) → Option (Fin m) → ℝ :=
      fun b _ => if b = none then t else 1 - t
    let μ : Option (Fin m) → ℝ := fun b =>
      if b = none then t else 1 / (Real.sqrt m * (1 + Real.sqrt m))
    let Φ : (Option (Fin m) → ℝ) → ℝ := fun p =>
      ∑ e ∈ H.edgeFinset, Sym2.lift
        ⟨fun b c => p b * p c / (p b + p c),
          fun b c => by simp [mul_comm, add_comm]⟩ e
    let q : ℝ := m / (1 + Real.sqrt m) ^ 2
    Feasible H a ∧ (∀ b, load H a b = q) ∧ R.readout () () (kappa H) = q ∧
      μ ∈ stdSimplex ℝ (Option (Fin m)) ∧ Φ μ = q ∧
      (∀ p ∈ stdSimplex ℝ (Option (Fin m)), Φ p ≤ q) ∧
      (m = 1 → R.readout () () (kappa H) = 1 / 4) ∧
      (m = 2 → R.readout () () (kappa H) = 2 * (3 - 2 * Real.sqrt 2))

def starFamily : Registration starArena (type_of% @star_extrema) := by
  have hn : ¬starArena.Law rejected := by
    intro h
    have he := (h 1 (by decide)).2.2.1
    norm_num [rejected, realize] at he
  have hp : starArena.Law actual := star_extrema
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨hp, rejected, hn⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def lowerAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.maximum_degree_lower_bound.{u})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.lowerUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.lowerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena.{u}⟩
  objectArena := .source ⟨lowerArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena.{u} ⟨lowerFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def starAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.star_extrema)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.starUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema.starFamily
  realizationSource := none
  generated := false
  arena := .source ⟨starArena⟩
  objectArena := .source ⟨starArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source starArena ⟨starFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lowerFamily
#print axioms starFamily
end
end Reg.D5.S3.Combinatorics.Graph.QuadraticLoad.StarExtrema
