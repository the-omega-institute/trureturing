import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer

/-! Complete conductance observations of the original tripartite source telescope. -/
noncomputable section
namespace Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
open _root_.D5.S3.Combinatorics.SpectralGraph
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
abbrev Params := ℕ × ℕ × ℕ
abbrev Weights (p : Params) := Sym2 (Fin (p.1+p.2.1+p.2.2)) → ℝ
abbrev signature : Signature where
  Params := Params
  State p := Weights p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Weights p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def observedClaim (a b c : ℕ) (observe : Weights (a,b,c) → Weights (a,b,c)) : Prop :=
  let G := K3 a b c
  let U := (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2)
  (∀ w : Weights (a,b,c), (∀ i j,G.Adj i j → 0<observe w s(i,j)) →
    0<lambda2 G (observe w) ∧ lambda2 G (observe w)*totalRes G (observe w)<U) ∧
  (∀ w : Weights (a,b,c), (∀ i j,G.Adj i j → 0 ≤ observe w s(i,j)) →
    lambda2 G (observe w)=1 → (support G (observe w)).Connected ∧ totalRes G (observe w) ≤ U ∧
      (totalRes G (observe w)=U ↔ c=a+b ∧ ∀ i j,G.Adj i j → observe w s(i,j)=observe (boundary a b c) s(i,j))) ∧
  ((∃ w : Weights (a,b,c), (∀ i j,G.Adj i j → 0 ≤ observe w s(i,j)) ∧
    lambda2 G (observe w)=1 ∧ totalRes G (observe w)=U) ↔ c=a+b) ∧
  (c=a+b → (∀ i j,G.Adj i j → 0 ≤ observe (boundary a b c) s(i,j)) ∧
    (support G (observe (boundary a b c))).Connected ∧ lambda2 G (observe (boundary a b c))=1 ∧
    totalRes G (observe (boundary a b c))=U ∧ FullSpectrum (observe (boundary a b c)) ∧
    ¬ (∀ i j,G.Adj i j → 0<observe (boundary a b c) s(i,j))) ∧
  (∀ w : Weights (a,b,c), (∀ i j,G.Adj i j → 0 ≤ observe w s(i,j)) →
    lambda2 G (observe w)=1 → Compression (observe w) ∧
      (totalRes G (observe w)=U → (wLap G (observe w)-(1-constProj (a+b+c))).rank=1))

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b c : ℕ},2 ≤ a → a ≤ b → b ≤ c →
    observedClaim a b c (R.readout () (a,b,c))
abbrev source := type_of% (@_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.result)
theorem source_bridge : source ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := @_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.result

private lemma zero_lambda {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    lambda2 G (0 : Sym2 (Fin n) → ℝ)=0 := by
  have hL : wLap G (0 : Sym2 (Fin n) → ℝ)=0 := by ext i j; simp [wLap]
  let p : Fin n := ⟨0,by omega⟩
  let q : Fin n := ⟨1,by omega⟩
  refine lambda2_eq_of_rayleigh G 0 0 (by intro x hx; simp [hL]) (delta p q)
    (delta_ne (by simp [p,q,Fin.ext_iff])) (delta_sum _ _) ?_
  simp [hL]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := ((h (a:=2) (b:=2) (c:=4) (by decide) (by decide) (by decide)).2.2.2.1
    (by decide)).2.2.1
  change lambda2 (K3 2 2 4) (0 : Weights (2,2,4))=1 at hh
  rw [zero_lambda (by decide)] at hh
  norm_num at hh

def family : Registration arena source where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(2,2,4),(0 : Weights (2,2,4)),(1 : Weights (2,2,4)),?_⟩
    intro he
    have hh := congrFun he s((0 : Fin 8),(4 : Fin 8))
    change (0:ℝ)=1 at hh
    norm_num at hh

noncomputable def sourceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.result)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence,objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
      name := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer.Theorem32
      path := #[] }
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
