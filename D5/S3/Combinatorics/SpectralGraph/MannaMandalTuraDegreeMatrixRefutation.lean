/- GID: D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.not_degreeMatrix_master_identity_criterion; claim=D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.claim
   digest: The degree matrix refutes the master-identity criterion on threshold graphs. -/

/-
admission_basis: open-problem-resolution for Conjecture 13.9, #34363.
Direct frozen dependencies: none.
The result uses the characteristic root multiset, the reconstruction of the creation
sequence, and incompatible affine equations on the connected three-vertex path.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic


/-!
# The degree-matrix specialization of the master-identity criterion

Manna, Mandal and Tura formulate the criterion in Conjecture 13.9
(arXiv:2610.22838v1, printed p. 18). The threshold graph predicate uses
the creation sequence in Section 1, and the real matrices use the
conventions of Section 2. Degree-multiset reconstruction for threshold
graphs is classical (Chvátal and Hammer, *Aggregation of inequalities in
integer programming*, Annals of Discrete Mathematics 1 (1977), 145–162).
-/

set_option autoImplicit false

namespace MannaMandalTuraDegreeMatrix

open SimpleGraph
open scoped BigOperators

universe u v

/-- The index counts additions after the initial vertex. The outermost bit is
the most recent addition. -/
private inductive Creation : ℕ → Type
  | singleton : Creation 0
  | adjoin {n : ℕ} (universal : Bool) (previous : Creation n) : Creation (n + 1)

private def extend {n : ℕ} (b : Bool) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) where
  Adj := Fin.cases (Fin.cases False (fun _ => b = true))
    (fun i => Fin.cases (b = true) (G.Adj i))
  symm := by
    constructor
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · exact id
    · exact id
    · exact id
    · exact G.symm.symm i j
  loopless := by
    constructor
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact id
    · exact G.irrefl

private instance extendDecidable {n : ℕ} (b : Bool) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : DecidableRel (extend b G).Adj := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable (b = true))
  · exact inferInstanceAs (Decidable (b = true))
  · exact inferInstanceAs (Decidable (G.Adj i j))

/-- Realize each addition at vertex zero, shifting the old labels by one. -/
private def Creation.graph : {n : ℕ} → Creation n → SimpleGraph (Fin (n + 1))
  | _, .singleton => ⊥
  | _, .adjoin b c => extend b c.graph

private instance creationDecidable : {n : ℕ} → (c : Creation n) → DecidableRel c.graph.Adj
  | _, .singleton => inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 1)).Adj)
  | _, .adjoin b c =>
    letI := creationDecidable c
    extendDecidable b c.graph

/-- The paper's creation-sequence definition transported by graph isomorphism. -/
def IsThreshold {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (c : Creation n), Nonempty (G ≃g c.graph)

/-- One degree for each vertex, retaining repetitions. -/
private def degreeBag {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Multiset ℕ :=
  (Finset.univ : Finset V).val.map (fun i => G.degree i)

private theorem degree_extend_zero {n : ℕ} (b : Bool) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (extend b G).degree 0 = if b then n else 0 := by
  have h : (extend b G).degree 0 =
      ∑ j : Fin (n + 1), if (extend b G).Adj 0 j then 1 else 0 :=
    degree_eq_sum_if_adj (R := ℕ) (G := extend b G) 0
  rw [h, Fin.sum_univ_succ]
  cases b <;> simp [extend]

private theorem degree_extend_succ {n : ℕ} (b : Bool) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    (extend b G).degree i.succ = G.degree i + (if b then 1 else 0) := by
  have h : (extend b G).degree i.succ =
      ∑ j : Fin (n + 1), if (extend b G).Adj i.succ j then 1 else 0 :=
    degree_eq_sum_if_adj (R := ℕ) (G := extend b G) i.succ
  have h' : G.degree i = ∑ j : Fin n, if G.Adj i j then 1 else 0 :=
    degree_eq_sum_if_adj (R := ℕ) (G := G) i
  rw [h, Fin.sum_univ_succ, h']
  cases b <;> simp [extend, Nat.add_comm]

private theorem degreeBag_adjoin {n : ℕ} (b : Bool) (c : Creation n) :
    degreeBag (Creation.adjoin b c).graph =
      (if b then n + 1 else 0) ::ₘ
        (degreeBag c.graph).map (fun d => d + (if b then 1 else 0)) := by
  change degreeBag (extend b c.graph) = _
  unfold degreeBag
  rw [Fin.univ_val_map, List.ofFn_succ, ← Multiset.cons_coe, degree_extend_zero,
    ← Fin.univ_val_map]
  simp only [Multiset.map_map, Function.comp_def, degree_extend_succ]

private theorem zero_mem_degreeBag_adjoin {n : ℕ} (b : Bool) (c : Creation n) :
    0 ∈ degreeBag (Creation.adjoin b c).graph ↔ b = false := by
  cases b
  · simp [degreeBag_adjoin]
  · simp [degreeBag_adjoin, Multiset.mem_map]

/-- A zero degree detects an isolated last addition. After recovering the bit,
cancel the newest vertex and undo the common shift in the old degrees. -/
private theorem creation_eq_of_degreeBag_eq {n : ℕ} {c d : Creation n}
    (h : degreeBag c.graph = degreeBag d.graph) : c = d := by
  induction n with
  | zero =>
    cases c
    cases d
    rfl
  | succ n ih =>
    cases c with
    | adjoin b c =>
      cases d with
      | adjoin b' d =>
        have hb : b = b' := by
          have hm := (zero_mem_degreeBag_adjoin b c).symm.trans
            ((congrArg (fun s : Multiset ℕ => 0 ∈ s) h).to_iff.trans
              (zero_mem_degreeBag_adjoin b' d))
          cases b <;> cases b' <;> simp_all
        subst b'
        have ht := (Multiset.cons_inj_right _).mp
          ((degreeBag_adjoin b c).symm.trans (h.trans (degreeBag_adjoin b d)))
        have hi : Function.Injective (fun k : ℕ => k + (if b then 1 else 0)) := by
          intro i j he
          exact Nat.add_right_cancel he
        rw [ih (Multiset.map_injective hi ht)]

private theorem degreeBag_iso {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : degreeBag G = degreeBag H := by
  calc
    degreeBag G = ((Finset.univ : Finset V).val.map e.toEquiv).map (fun i => H.degree i) := by
      simp only [degreeBag, Multiset.map_map, Function.comp_def, RelIso.coe_fn_toEquiv, e.degree_eq]
    _ = degreeBag H := by rw [Multiset.map_univ_val_equiv, degreeBag]

private theorem threshold_iso_of_degreeBag_eq {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsThreshold G) (hH : IsThreshold H) (h : degreeBag G = degreeBag H) :
    Nonempty (G ≃g H) := by
  obtain ⟨n, c, ⟨e⟩⟩ := hG
  obtain ⟨m, d, ⟨f⟩⟩ := hH
  have hcd := (degreeBag_iso e).symm.trans (h.trans (degreeBag_iso f))
  have hn : n = m := by
    have hc := congrArg Multiset.card hcd
    simpa [degreeBag] using hc
  subst m
  have heq := creation_eq_of_degreeBag_eq hcd
  subst d
  exact ⟨e.trans f.symm⟩

/-- Real eigenvalues with their algebraic multiplicities. -/
noncomputable def degreeSpectrum {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ :=
  (G.degMatrix ℝ).charpoly.roots

private theorem degreeSpectrum_eq {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    degreeSpectrum G = (degreeBag G).map (Nat.cast : ℕ → ℝ) := by
  unfold degreeSpectrum
  rw [SimpleGraph.degMatrix, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton]
    simp only [degreeBag, Multiset.map_map, Function.comp_def]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)

private theorem degreeSpectrum_integral {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ x ∈ degreeSpectrum G, ∃ z : ℤ, x = (z : ℝ) := by
  intro x hx
  rw [degreeSpectrum_eq, Multiset.mem_map] at hx
  obtain ⟨d, _, rfl⟩ := hx
  exact ⟨d, (Int.cast_natCast d).symm⟩

private theorem threshold_iso_of_degreeSpectrum_eq {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsThreshold G) (hH : IsThreshold H) (h : degreeSpectrum G = degreeSpectrum H) :
    Nonempty (G ≃g H) := by
  rw [degreeSpectrum_eq, degreeSpectrum_eq] at h
  exact threshold_iso_of_degreeBag_eq hG hH (Multiset.map_injective Nat.cast_injective h)

/-- The new vertex 0 is adjacent to both older vertices, which are nonadjacent. -/
private def p3Code : Creation 2 := .adjoin true (.adjoin false .singleton)

private def p3 : SimpleGraph (Fin 3) := p3Code.graph

private instance p3Decidable : DecidableRel p3.Adj := creationDecidable p3Code

private theorem p3_threshold : IsThreshold p3 := ⟨2, p3Code, ⟨SimpleGraph.Iso.refl⟩⟩

private theorem p3_adj_iff (i j : Fin 3) :
    p3.Adj i j ↔ (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem p3_connected : p3.Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable p3).mpr ⟨0, fun j => ?_⟩
  have toCenter (k : Fin 3) : p3.Reachable k 0 := by
    by_cases h : k = 0
    · subst k
      exact .rfl
    · exact ((p3_adj_iff k 0).mpr (Or.inr ⟨h, rfl⟩)).reachable
  exact (toCenter j).symm

/-- The matrix with every entry equal to one. -/
def allOnes (V : Type u) : Matrix V V ℝ := Matrix.of fun _ _ => 1

private theorem p3_not_affine :
    ¬ ∃ α β γ : ℝ, p3.degMatrix ℝ =
      α • p3.lapMatrix ℝ + β • allOnes (Fin 3) +
        γ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rintro ⟨α, β, γ, h⟩
  have hNonedge := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) h
  have hEdge := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  have hCenter := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  have hLeaf := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  have h12 : ¬ p3.Adj 1 2 := by decide
  have h01 : p3.Adj 0 1 := by decide
  have h0 : p3.degree 0 = 2 := by decide
  have h1 : p3.degree 1 = 1 := by decide
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    allOnes, h12, h01, h0, h1] at hNonedge hEdge hCenter hLeaf
  have hβ : β = 0 := by linarith only [hNonedge]
  have hα : α = 0 := by linarith only [hEdge, hβ]
  linarith only [hCenter, hLeaf, hα, hβ]

/-- The matrix-specialized criterion on finite connected threshold graphs, with
affine coefficients allowed to depend on the graph. -/
def claim : Prop :=
  ((∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj], IsThreshold G → G.Connected →
            ∀ x ∈ degreeSpectrum G, ∃ z : ℤ, x = (z : ℝ)) ∧
    (∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj],
        IsThreshold G → G.Connected → IsThreshold H → H.Connected →
        degreeSpectrum G = degreeSpectrum H → Nonempty (G ≃g H))) ↔
      (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          IsThreshold G → G.Connected →
          ∃ α β γ : ℝ, G.degMatrix ℝ =
            α • G.lapMatrix ℝ + β • allOnes V + γ • (1 : Matrix V V ℝ))

/-- The degree matrix refutes Conjecture 13.9, even with graph-dependent affine
coefficients. -/
theorem not_degreeMatrix_master_identity_criterion : ¬ claim := by
  intro h
  have hAffine := h.mp ⟨fun _ _ _ G _ _ _ => degreeSpectrum_integral G,
    fun _ _ _ _ _ _ _ _ _ _ hG _ hH _ => threshold_iso_of_degreeSpectrum_eq hG hH⟩
  exact p3_not_affine (hAffine (Fin 3) p3 p3_threshold p3_connected)

end MannaMandalTuraDegreeMatrix
