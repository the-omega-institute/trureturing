import D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
open _root_.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

structure Parameters where
  R : Type u
  ring : CommRing R
  n : ℕ
  k : ℕ
  U : Finset (Fin n)
  W : Finset (Fin n)
  hU : U.card = k
  hW : W.card = k
  hk : 1 ≤ k

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (Fin p.n) (Fin p.n) p.R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def minorValue (p : Parameters.{u}) (M : signature.State p) : p.R :=
  letI := p.ring
  let row : Fin (p.n - p.k) ↪o Fin p.n :=
    p.Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, p.hW])
  let col : Fin (p.n - p.k) ↪o Fin p.n :=
    p.Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, p.hU])
  (M.submatrix row col).det

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => minorValue p M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ p : Parameters.{u}, letI := p.ring
    ∀ M : signature.State p, (∀ j, ∑ i, M i j = 0) →
    let graph := fun F : Finset (Fin p.n × Fin p.n) =>
      SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
    let Forest := {F : Finset (Fin p.n × Fin p.n) //
      (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! root, root ∈ p.U ∧ (graph F).Reachable v root) ∧
      (∀ v, ∃! mark, mark ∈ p.W ∧ (graph F).Reachable v mark) ∧
      (∀ i j, (i, j) ∈ F → ∀ root ∈ p.U, (graph F).Reachable root i →
        (graph F).dist root i < (graph F).dist root j)}
    ∃ matching : Forest → Equiv.Perm (Fin p.k),
      (∀ F a, (graph F.val).Reachable (p.U.orderEmbOfFin p.hU a)
        (p.W.orderEmbOfFin p.hW (matching F a))) ∧
      r.readout () p M =
        ∑ F : Forest,
          (((-1 : ℤ) ^ (p.n + p.k + (∑ root ∈ p.U, root.val) +
            (∑ mark ∈ p.W, mark.val)) * (Equiv.Perm.sign (matching F) : ℤ) : ℤ) : p.R) *
            ∏ edge ∈ F.val, M edge.1 edge.2

def rejectedLaw : ¬arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let p : Parameters.{u} :=
    ⟨ULift.{u} ℤ, inferInstance, 1, 1, Finset.univ, Finset.univ, by simp, by simp, by omega⟩
  letI := p.ring
  obtain ⟨matching, hmatching, hcorrect⟩ := directed_all_minors_matrix_tree
    (0 : Matrix (Fin p.n) (Fin p.n) p.R) p.U p.W p.hU p.hW p.hk (by simp)
  obtain ⟨otherMatching, hother, hwrong⟩ := h p 0 (by simp; intro j; rfl)
  have hperm : otherMatching = matching := funext fun F => Subsingleton.elim _ _
  rw [hperm] at hwrong
  simp only [rejected, realize] at hwrong
  simp only [Matrix.det_isEmpty] at hcorrect
  have hbad : (1 : p.R) = 0 := hcorrect.trans hwrong.symm
  exact one_ne_zero hbad

def dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro role
  let p : Parameters.{u} :=
    ⟨ULift.{u} ℤ, inferInstance, 2, 1, {0}, {0}, by simp, by simp, by omega⟩
  letI := p.ring
  refine ⟨p, 0, 1, ?_⟩
  intro h
  have hzero : minorValue p 0 = 0 := by
    simp [minorValue, p, Matrix.det_fin_one]
  have hone : minorValue p 1 = 1 := by
    simp [minorValue, p, Matrix.det_fin_one, Matrix.one_apply]
    rfl
  change minorValue p 0 = minorValue p 1 at h
  rw [hzero, hone] at h
  exact zero_ne_one h

open Classical in
abbrev SourceClaim : Prop :=
  ∀ {R : Type u} [CommRing R] {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (U W : Finset (Fin n))
    (hU : U.card = k) (hW : W.card = k) (hk : 1 ≤ k)
    (hcol : ∀ j, ∑ i, M i j = 0),
    let graph := fun F : Finset (Fin n × Fin n) =>
      SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
    let Forest := {F : Finset (Fin n × Fin n) //
      (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! root, root ∈ U ∧ (graph F).Reachable v root) ∧
      (∀ v, ∃! mark, mark ∈ W ∧ (graph F).Reachable v mark) ∧
      (∀ i j, (i, j) ∈ F → ∀ root ∈ U, (graph F).Reachable root i →
        (graph F).dist root i < (graph F).dist root j)}
    let row : Fin (n - k) ↪o Fin n :=
      Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, hW])
    let col : Fin (n - k) ↪o Fin n :=
      Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, hU])
    ∃ matching : Forest → Equiv.Perm (Fin k),
      (∀ F a, (graph F.val).Reachable (U.orderEmbOfFin hU a)
        (W.orderEmbOfFin hW (matching F a))) ∧
      (M.submatrix row col).det =
        ∑ F : Forest,
          (((-1 : ℤ) ^ (n + k + (∑ root ∈ U, root.val) + (∑ mark ∈ W, mark.val)) *
            (Equiv.Perm.sign (matching F) : ℤ) : ℤ) : R) *
            ∏ edge ∈ F.val, M edge.1 edge.2

def registration : Registration arena.{u} SourceClaim.{u} where
  actual := actual
  bridge := by
    constructor
    · intro h p
      letI := p.ring
      intro M hcol
      exact h M p.U p.W p.hU p.hW p.hk hcol
    · intro h R inst n k M U W hU hW hk hcol
      let p : Parameters.{u} := ⟨R, inst, n, k, U, W, hU, hW, hk⟩
      exact h p M hcol
  variation := ⟨by
    intro p
    letI := p.ring
    intro M hcol
    exact directed_all_minors_matrix_tree M p.U p.W p.hU p.hW p.hk hcol,
    rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree
  in arena readout via (realize signature (fun _ p M => minorValue p M) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
    coordinates := #[0, 1, 2, 3, 5, 6, 7, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      functionOperand := false }]
  })
  escape continues (open)

end Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
