/- GID: D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.claim; result=D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.result; claim=D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.claim
   digest: Equal independence polynomials do not determine T2 hypergraphs. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19406; Refuted).
Direct frozen dependencies: none, for every declaration below.
h5_threshold: proof_shape: bind-only; consumer: result; escape_witness: none.
k5_threshold: proof_shape: bind-only; consumer: result; escape_witness: none.
polynomials_equal: proof_shape: bind-only; consumer: result; escape_witness: none.
degree_transport: proof_shape: bind-only; consumer: not_isomorphic; escape_witness: none.
not_isomorphic: proof_shape: bind-only; consumer: result; escape_witness: none.
KHypergraph, IsIndependent, indepPoly, IsT2Threshold, Isomorphic, claim:
source definitions; H5, K5, indepH, indepK: concrete finite data.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The five-vertex case refutes the universal question; no arbitrary-size family
or antiregular identification is asserted. Literature completeness and the
unread final journal text remain ASSUMED-UNVERIFIED.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.NormNum

/-! Binding conventions for E. Zhang, "On the Independence Polynomial and Threshold of an Antiregular k-Hypergraph",
arXiv:2303.01024v1 (Discrete Appl. Math. 378 (2026) 244–258): k-hypergraphs, independent sets and the independence
polynomial (Eq. (8)), the T2-threshold property (Definition 4.1(T2)), isomorphism, and the closing question "given
two T2-threshold k-hypergraphs with the same independence polynomial, are they isomorphic?". -/

namespace D5.S3.Combinatorics.Hypergraphs.ZhangThresholdIndependenceRefutation

/-- A `k`-hypergraph `H = (V, E)`: a finite vertex type and a set of hyperedges, each a `k`-element vertex subset. -/
structure KHypergraph (k : ℕ) (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = k

variable {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- `W ⊆ V` is independent in `H` if it includes no hyperedge: `∀ e ∈ E, e ⊄ W`. -/
def IsIndependent (H : KHypergraph k V) (S : Finset V) : Prop :=
  ∀ e ∈ H.edges, ¬ e ⊆ S

/-- The independence polynomial `I(H; x) = Σ_{W ⊆ V independent} x^{|W|}` (Eq. (8)). -/
noncomputable def indepPoly (H : KHypergraph k V) : Polynomial ℤ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => IsIndependent H S), Polynomial.X ^ S.card

/-- (T2): there are a labeling `c` of `V` and a threshold `τ` such that, for every vertex subset `X` of size `k`,
`X ∈ E` if and only if `Σ_{x∈X} c(x) > τ`. -/
def IsT2Threshold (H : KHypergraph k V) : Prop :=
  ∃ (c : V → ℝ) (τ : ℝ), ∀ X : Finset V, X.card = k → (X ∈ H.edges ↔ τ < ∑ x ∈ X, c x)

/-- `H` and `H'` are isomorphic: some vertex bijection carries the hyperedges of `H` exactly onto those of `H'`. -/
def Isomorphic (H : KHypergraph k V) (H' : KHypergraph k W) : Prop :=
  ∃ σ : V ≃ W, ∀ e : Finset V, e ∈ H.edges ↔ e.map σ.toEmbedding ∈ H'.edges

/-- The closing question, read as the universal statement: two T2-threshold `k`-hypergraphs with the same
independence polynomial are isomorphic. -/
def claim : Prop :=
  ∀ (k : ℕ) (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : KHypergraph k V) (H' : KHypergraph k W),
    IsT2Threshold H → IsT2Threshold H' → indepPoly H = indepPoly H' → Isomorphic H H'


set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def H5 : KHypergraph 3 (Fin 5) :=
  { edges := {{0,2,3}, {0,2,4}, {0,3,4}, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}}
    uniform := by decide }

private def K5 : KHypergraph 3 (Fin 5) :=
  { edges := {{0,1,4}, {0,2,4}, {0,3,4}, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}}
    uniform := by decide }

private theorem h5_threshold : IsT2Threshold H5 := by
  refine ⟨(fun i : Fin 5 => if i = 0 ∨ i = 1 then (0 : ℝ) else 1), 1, ?_⟩
  intro X hX
  fin_cases X <;> norm_num [H5, Finset.sum_insert, Finset.ext_iff] at * <;> decide
private theorem k5_threshold : IsT2Threshold K5 := by
  refine ⟨(fun i : Fin 5 => if i = 0 then (0 : ℝ) else if i = 4 then 3 else 1), 2, ?_⟩
  intro X hX
  fin_cases X <;> norm_num [K5, Finset.sum_insert, Finset.ext_iff] at * <;> decide
private def indepH : Finset (Finset (Fin 5)) :=
  {∅,
   {0}, {1}, {2}, {3}, {4},
   {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4},
   {0,1,2}, {0,1,3}, {0,1,4}}

private def indepK : Finset (Finset (Fin 5)) :=
  {∅,
   {0}, {1}, {2}, {3}, {4},
   {0,1}, {0,2}, {0,3}, {0,4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4},
   {0,1,2}, {0,1,3}, {0,2,3}}

private theorem polynomials_equal : indepPoly H5 = indepPoly K5 := by
  classical
  have hH : (Finset.univ : Finset (Finset (Fin 5))).filter (fun S => IsIndependent H5 S) = indepH := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases S <;> simp only [IsIndependent, H5] <;> decide
  have hK : (Finset.univ : Finset (Finset (Fin 5))).filter (fun S => IsIndependent K5 S) = indepK := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases S <;> simp only [IsIndependent, K5] <;> decide
  simp only [indepPoly]
  rw [hH, hK]
  simp (disch := decide) [indepH, indepK, Finset.sum_insert]
private theorem degree_transport (H : KHypergraph k V) (K : KHypergraph k W)
    (σ : V ≃ W) (hσ : ∀ e : Finset V, e ∈ H.edges ↔ e.map σ.toEmbedding ∈ K.edges)
    (v : V) :
    (H.edges.filter (fun e => v ∈ e)).card = (K.edges.filter (fun e => σ v ∈ e)).card := by
  classical
  apply Finset.card_bij (fun e _ => e.map σ.toEmbedding)
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hv⟩
    exact Finset.mem_filter.mpr ⟨(hσ e).mp he, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · intro e he f hf hef
    exact Finset.map_injective _ hef
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hv⟩
    have hm : (e.map σ.symm.toEmbedding).map σ.toEmbedding = e :=
      (Equiv.finsetCongr σ).apply_symm_apply e
    refine ⟨e.map σ.symm.toEmbedding, Finset.mem_filter.mpr ⟨(hσ _).mpr (hm.symm ▸ he), ?_⟩, hm⟩
    exact Finset.mem_map.mpr ⟨σ v, hv, σ.symm_apply_apply v⟩
private theorem not_isomorphic : ¬ Isomorphic H5 K5 := by
  intro ⟨σ, hσ⟩
  have hd := degree_transport H5 K5 σ hσ 2
  have hh : (H5.edges.filter (fun e => (2 : Fin 5) ∈ e)).card = 5 :=
    Eq.symm (Nat.eq_of_beq_eq_true rfl)
  have hk : ∀ v : Fin 5, (K5.edges.filter (fun e => v ∈ e)).card ≠ 5 := by decide
  exact hk (σ 2) (hd.symm.trans hh)
theorem result : ¬ D5.S3.Combinatorics.Hypergraphs.ZhangThresholdIndependenceRefutation.claim := by
  intro h
  exact not_isomorphic (h 3 (Fin 5) (Fin 5) H5 K5 h5_threshold k5_threshold polynomials_equal)
end D5.S3.Combinatorics.Hypergraphs.ZhangThresholdIndependenceRefutation
