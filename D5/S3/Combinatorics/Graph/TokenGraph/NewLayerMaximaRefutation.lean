/- GID: D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim; result=D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result; claim=D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim
   digest: The connected four-vertex star refutes successive new-Laplacian-layer maxima monotonicity. -/

import D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix Finset Polynomial
open D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation (tokenGraph)

namespace D5.S3.Combinatorics.Graph.TokenGraph.NewLayerMaximaRefutation

/-- The entire ordinary real Laplacian spectrum, with algebraic multiplicities. -/
noncomputable def spectrum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ :=
  Multiset.map (G.isHermitian_lapMatrix ℝ).eigenvalues Finset.univ.val

/-- Consecutive MULTISET subtraction, before taking any maximum. -/
noncomputable def layer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Multiset ℝ := by
  classical
  exact spectrum (tokenGraph G k) - spectrum (tokenGraph G (k - 1))

private lemma spectrum_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (spectrum G).card = Fintype.card V := by
  simp [spectrum]

private lemma layer_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n / 2) : (layer G k).toFinset.Nonempty := by
  classical
  apply Multiset.toFinset_nonempty.mpr
  intro hz
  have hs : spectrum (tokenGraph G k) ≤ spectrum (tokenGraph G (k - 1)) :=
    tsub_eq_zero_iff_le.mp hz
  have hc := Multiset.card_le_card hs
  simp only [spectrum_card] at hc
  have card_tokens (j : ℕ) : Fintype.card (Set.powersetCard (Fin n) j) = n.choose j := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Set.powersetCard.card (α := Fin n) (n := j))
  rw [card_tokens, card_tokens] at hc
  have he := Nat.choose_succ_right_eq n (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at he
  have hp : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  have hlt : k < n - (k - 1) := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt hp
  rw [← he] at hm
  have hn : n.choose (k - 1) < n.choose k := (Nat.mul_lt_mul_right (by omega)).mp hm
  omega

/-- Definition 3.1 on its whole source-admissible nonempty domain. -/
noncomputable def rho {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n / 2) : ℝ := by
  classical
  exact (layer G k).toFinset.max' (layer_nonempty G k hk hkn)

/-- The whole successive-comparison form of Conjecture 3.3, with no order cap. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∀ (k : ℕ) (hk : 1 ≤ k) (hkn : k < n / 2),
      rho G k hk (Nat.le_of_lt hkn) ≤
        rho G (k + 1) (by omega) (by omega)

private def connectedStar : {G : SimpleGraph (Fin 4) // G.Connected} :=
  ⟨SimpleGraph.starGraph 0, SimpleGraph.connected_starGraph 0⟩

private abbrev star := connectedStar.val

private def subsets0 : Fin 1 → Set.powersetCard (Fin 4) 0 :=
  ![⟨∅, by decide⟩]

private def subsets1 : Fin 4 → Set.powersetCard (Fin 4) 1 :=
  ![⟨{0}, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩, ⟨{3}, by decide⟩]

/-- The actual two-subsets in six-cycle order 01,12,02,23,03,13. -/
private def subsets2 : Fin 6 → Set.powersetCard (Fin 4) 2 :=
  ![⟨{0,1}, by decide⟩, ⟨{1,2}, by decide⟩, ⟨{0,2}, by decide⟩,
    ⟨{2,3}, by decide⟩, ⟨{0,3}, by decide⟩, ⟨{1,3}, by decide⟩]

private def e0 : Fin 1 ≃ Set.powersetCard (Fin 4) 0 :=
  Equiv.ofBijective subsets0 (by decide)
private def e1 : Fin 4 ≃ Set.powersetCard (Fin 4) 1 :=
  Equiv.ofBijective subsets1 (by decide)
private def e2 : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective subsets2 (by decide)

private def L0 : Matrix (Fin 1) (Fin 1) ℤ := 0
private def L1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3,-1,-1,-1; -1,1,0,0; -1,0,1,0; -1,0,0,1]
private def L2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2,-1,0,0,0,-1; -1,2,-1,0,0,0; 0,-1,2,-1,0,0;
     0,0,-1,2,-1,0; 0,0,0,-1,2,-1; -1,0,0,0,-1,2]

private lemma actual_lap0 : Matrix.reindex e0.symm e0.symm
    ((tokenGraph star 0).lapMatrix ℤ) = L0 := by decide
private lemma actual_lap1 : Matrix.reindex e1.symm e1.symm
    ((tokenGraph star 1).lapMatrix ℤ) = L1 := by decide
private lemma actual_lap2 : Matrix.reindex e2.symm e2.symm
    ((tokenGraph star 2).lapMatrix ℤ) = L2 := by decide

end D5.S3.Combinatorics.Graph.TokenGraph.NewLayerMaximaRefutation
