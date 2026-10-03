/- GID: D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.claim; result=D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result; claim=D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.claim
   digest: A single edge and two isolated vertices refute token-radius Conjecture 1.1. -/

/-
proof_shape: result: bind-only (finite Laplacian evaluation, spectral identities and edge counts).
escape_witness: none
admission_basis: open-problem-resolution (#12457; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Set.PowersetCard

set_option autoImplicit false

open Matrix Finset

namespace D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation

/-- Two k-subsets differ by moving one token along an edge. -/
def tokenGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (Set.powersetCard V k) where
  Adj s t := ∃ u v, s.val \ t.val = {u} ∧ t.val \ s.val = {v} ∧ G.Adj u v
  symm := ⟨by
    rintro s t ⟨u, v, hu, hv, h⟩
    exact ⟨v, u, hv, hu, h.symm⟩⟩
  loopless := ⟨by
    rintro s ⟨u, v, hu, hv, h⟩
    simp at hu⟩

instance instTokenGraphDecidableAdj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (tokenGraph G k).Adj := by
  unfold tokenGraph
  infer_instance

/-- The largest real eigenvalue of the Laplacian D - A; zero for the empty carrier. -/
noncomputable def rho {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := by
  classical
  exact if h : (Finset.univ : Finset V).Nonempty then
    Finset.univ.sup' h (G.isHermitian_lapMatrix ℝ).eigenvalues else 0

/-- The literal all-graphs statement of Conjecture 1.1. -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (k : ℕ), 2 ≤ k → k ≤ n / 2 → rho (tokenGraph G k) = rho G) ↔
      Nonempty (G ≃g SimpleGraph.starGraph (⟨0, by omega⟩ : Fin n))

set_option maxHeartbeats 2000000 in
-- Finite subset enumeration checks the integer token Laplacian identity.
/-- The single-edge graph refutes the all-graphs statement of Conjecture 1.1. -/
theorem result : ¬ claim := by
  let witness : SimpleGraph (Fin 4) := {
    Adj := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
    symm := ⟨by decide⟩
    loopless := ⟨by decide⟩ }
  let : DecidableRel witness.Adj := by
    dsimp [witness]
    infer_instance
  have largest_eq_two {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
      (A : Matrix V V ℝ) (hA : A.IsHermitian)
      (hsq : A * A = (2 : ℝ) • A) (hne : A ≠ 0) :
      Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues = 2 := by
    classical
    have heig (i : V) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 2 := by
      let v : V → ℝ := ⇑(hA.eigenvectorBasis i)
      have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.mpr
        (hA.eigenvectorBasis.orthonormal.ne_zero i)
      have he : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
      have hs : (hA.eigenvalues i * hA.eigenvalues i) • v =
          ((2 : ℝ) * hA.eigenvalues i) • v := by
        calc
          _ = A *ᵥ (A *ᵥ v) := by rw [he, Matrix.mulVec_smul, he, smul_smul]
          _ = (A * A) *ᵥ v := Matrix.mulVec_mulVec v A A
          _ = _ := by rw [hsq, Matrix.smul_mulVec, he, smul_smul]
      have ht : hA.eigenvalues i * hA.eigenvalues i = 2 * hA.eigenvalues i :=
        smul_left_injective ℝ hv hs
      have hf : hA.eigenvalues i * (hA.eigenvalues i - 2) = 0 := by nlinarith
      exact (mul_eq_zero.mp hf).imp id sub_eq_zero.mp
    have hex : ∃ i, hA.eigenvalues i = 2 := by
      by_contra h
      apply hne
      apply hA.eigenvalues_eq_zero_iff.mp
      funext i
      rcases heig i with hi | hi
      · exact hi
      · exact False.elim (h ⟨i, hi⟩)
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      rcases heig i with h | h <;> simp [h]
    · obtain ⟨i, hi⟩ := hex
      rw [← hi]
      exact Finset.le_sup' hA.eigenvalues (Finset.mem_univ i)
  let q01 : (Set.powersetCard (Fin 4) 2) := ⟨{0, 1}, by change ({0, 1} : Finset (Fin 4)).card = 2; decide⟩
  let q02 : (Set.powersetCard (Fin 4) 2) := ⟨{0, 2}, by change ({0, 2} : Finset (Fin 4)).card = 2; decide⟩
  have witness_degree (i : Fin 4) :
      witness.degree i = if i = 0 ∨ i = 1 then 1 else 0 := by
    revert i
    decide
  have witness_lap : witness.lapMatrix ℝ =
      !![1,-1,0,0; -1,1,0,0; 0,0,0,0; 0,0,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        witness_degree, witness]
  have witness_sq : witness.lapMatrix ℝ * witness.lapMatrix ℝ =
      (2 : ℝ) • witness.lapMatrix ℝ := by
    rw [witness_lap]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  let ft : Fintype (Set.powersetCard (Fin 4) 2) := inferInstanceAs (Fintype {s : Finset (Fin 4) // s.card = 2})
  have hf : Set.powersetCard.instFintypeElemFinset (Fin 4) 2 = ft := Subsingleton.elim _ _
  have token_sq_int : (tokenGraph witness 2).lapMatrix ℤ *
      (tokenGraph witness 2).lapMatrix ℤ =
      (tokenGraph witness 2).lapMatrix ℤ + (tokenGraph witness 2).lapMatrix ℤ := by
    decide
  have token_lap_cast : (tokenGraph witness 2).lapMatrix ℝ =
      ((tokenGraph witness 2).lapMatrix ℤ).map (Int.castRingHom ℝ) := by
    ext s t
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have token_sq : (tokenGraph witness 2).lapMatrix ℝ *
      (tokenGraph witness 2).lapMatrix ℝ =
      (2 : ℝ) • (tokenGraph witness 2).lapMatrix ℝ := by
    have hc := congrArg (fun M : Matrix (Set.powersetCard (Fin 4) 2) (Set.powersetCard (Fin 4) 2) ℤ => M.map (Int.castRingHom ℝ)) token_sq_int
    rw [Matrix.map_mul, Matrix.map_add] at hc
    swap
    · intro a b
      exact map_add (Int.castRingHom ℝ) a b
    rw [token_lap_cast]
    simpa only [two_smul ℝ] using hc
  have witness_edges : witness.edgeFinset.card = 1 := by decide
  have star_edges : (SimpleGraph.starGraph (⟨0, by decide⟩ : Fin 4)).edgeFinset.card = 3 := by decide
  have witness_rho : rho witness = 2 := by
    have hnz : witness.lapMatrix ℝ ≠ 0 := by
      intro h
      have he := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 0) h
      rw [witness_lap] at he
      norm_num at he
    unfold rho
    split_ifs with h
    · exact largest_eq_two _ _ witness_sq hnz
    · exact False.elim (h ⟨0, mem_univ 0⟩)
  have token_rho : rho (tokenGraph witness 2) = 2 := by
    let : Nonempty (Set.powersetCard (Fin 4) 2) := ⟨q01⟩
    have hnz : (tokenGraph witness 2).lapMatrix ℝ ≠ 0 := by
      intro h
      have he := congrArg (fun A : Matrix (Set.powersetCard (Fin 4) 2) (Set.powersetCard (Fin 4) 2) ℝ => A q02 q02) h
      have hentry : (tokenGraph witness 2).lapMatrix ℤ q02 q02 = 1 := by
        decide
      rw [token_lap_cast] at he
      simp only [Matrix.map_apply, hentry, map_one, Matrix.zero_apply] at he
      norm_num at he
    unfold rho
    split_ifs with h
    · exact largest_eq_two _ _ token_sq hnz
    · exact False.elim (h ⟨q01, mem_univ q01⟩)
  intro h
  have heq : ∀ k : ℕ, 2 ≤ k → k ≤ 4 / 2 →
      rho (tokenGraph witness k) = rho witness := by
    intro k hk hl
    have hk2 : k = 2 := by omega
    subst k
    rw [hf]
    exact token_rho.trans witness_rho.symm
  obtain ⟨f⟩ := (h 4 (by decide) witness).mp heq
  have he := f.card_edgeFinset_eq
  rw [witness_edges, star_edges] at he
  norm_num at he


end D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation
