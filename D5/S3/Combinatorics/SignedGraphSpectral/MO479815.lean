/- GID: D5/S3/Combinatorics/SignedGraphSpectral/MO479815
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SignedGraphSpectral/MO479815
   mirror-E: none(waiver:external-counterexample)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DeleteEdges]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SignedGraphSpectral/MO479815.claim; result=D5/S3/Combinatorics/SignedGraphSpectral/MO479815.result; claim=D5/S3/Combinatorics/SignedGraphSpectral/MO479815.claim
   digest: Deleting a negative pendant edge strictly increases the full ordered spectral deviation. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
The full assertion of MathOverflow 479815, revision 2, issue #31231.
A Boolean value on each unordered pair encodes either legal edge sign, without
restricting the graph, order, sign distribution, or deletion connectivity.
All spectra are the full decreasing Hermitian spectra with multiplicity.

Direct frozen dependencies: none (pinned Mathlib only).
All private proof helpers are consumed on the refutation's live proof path.
-/

/-
Public declaration audit:
  claim: source definition; proof_shape: definition.
  result: proof_shape: bind-only (pinned intermediate-value, characteristic-root,
    and Hermitian-spectrum applications with normalization); admission_basis:
    open-problem-resolution (issue #31231). The designated refutation settles
    the external source assertion without claiming an independent escape witness.
Direct frozen dependencies: none (pinned Mathlib only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section
open Matrix Polynomial
open scoped Matrix BigOperators
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.SignedGraphSpectral.MO479815

/-- A sign on every unordered pair; `true` means positive and `false` negative.
Only values on actual edges enter the signed adjacency matrix. -/
def signedAdj {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if G.Adj i j then (if σ s(i,j) then 1 else -1) else 0

private theorem signed_hermitian {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Sym2 (Fin n) → Bool) : (signedAdj G σ).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, signedAdj, G.adj_comm, Sym2.eq_swap]

/-- The underlying ordinary adjacency matrix over the real numbers. -/
def underlyingAdj {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact G.adjMatrix ℝ

private theorem underlying_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) :
    (underlyingAdj G).IsHermitian := by
  classical
  exact G.isHermitian_adjMatrix ℝ

/-- Full decreasing eigenvalues, with multiplicity, indexed by `Fin n`. -/
def orderedSpectrum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Fin n → ℝ := fun i => hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- The source's sum of squares of differences of the two full ordered spectra. -/
def beta {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool) : ℝ :=
  ∑ i : Fin n,
    (orderedSpectrum (signedAdj G σ) (signed_hermitian G σ) i -
      orderedSpectrum (underlyingAdj G) (underlying_hermitian G) i) ^ 2

/-- The entire source assertion, over all finite simple graphs, all independent
legal signs, and every actual edge, deleting on the identical vertex carrier.
Every finite carrier can be labelled by `Fin n`; pair signs encode all signings. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (σ : Sym2 (Fin n) → Bool)
    (u v : Fin n), G.Adj u v →
      beta (G.deleteEdges {s(u,v)}) σ ≤ beta G σ

private def paw : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(0,2), s(1,2), s(0,3)}

private def A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,1,1; 1,0,1,0; 1,1,0,0; 1,0,0,0]

private def B : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,1,0; 1,0,1,0; 1,1,0,0; 0,0,0,0]

private theorem paw_adj : underlyingAdj paw = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [underlyingAdj, SimpleGraph.adjMatrix, paw, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff, A,
      Fin.succAbove]

private theorem deleted_adj : underlyingAdj (paw.deleteEdges {s(0,3)}) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [underlyingAdj, SimpleGraph.adjMatrix, SimpleGraph.deleteEdges_adj,
      paw, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff, B]

private theorem negative_adj {n : ℕ} (G : SimpleGraph (Fin n)) :
    signedAdj G (fun _ => false) = -underlyingAdj G := by
  ext i j
  by_cases h : G.Adj i j <;> simp [signedAdj, underlyingAdj, SimpleGraph.adjMatrix, Matrix.neg_apply, h]

private theorem A_hermitian : A.IsHermitian := by
  rw [← paw_adj]
  exact underlying_hermitian paw

private theorem B_hermitian : B.IsHermitian := by
  rw [← deleted_adj]
  exact underlying_hermitian _

private def p : ℝ[X] := X^3-X^2-3*X+1

private theorem A_charpoly : A.charpoly = (X+1)*p := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Fin.succAbove, A, p]
  <;> ring_nf

private theorem negA_charpoly : (-A).charpoly = (X-1)*(X^3+X^2-3*X-1) := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Fin.succAbove, A]
  <;> ring_nf

private theorem B_charpoly : B.charpoly = (X-2)*X*(X+1)^2 := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Fin.succAbove, B]
  <;> ring_nf

private theorem negB_charpoly : (-B).charpoly = (X+2)*X*(X-1)^2 := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Fin.succAbove, B]
  <;> ring_nf

private theorem cubic_roots : ∃ a b c : ℝ,
    2 < a ∧ a < 3 ∧ 0 < b ∧ b < 1 ∧ -2 < c ∧ c < -1 ∧
    p = (X-C a)*(X-C b)*(X-C c) ∧ a+b+c=1 := by
  obtain ⟨c, hc, hpc⟩ := intermediate_value_Ioo (by norm_num : (-2:ℝ) ≤ -1)
    p.continuousOn (by norm_num [p] : (0:ℝ) ∈ Set.Ioo (p.eval (-2)) (p.eval (-1)))
  obtain ⟨b, hb, hpb⟩ := intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1)
    p.continuousOn (by norm_num [p] : (0:ℝ) ∈ Set.Ioo (p.eval 1) (p.eval 0))
  obtain ⟨a, ha, hpa⟩ := intermediate_value_Ioo (by norm_num : (2:ℝ) ≤ 3)
    p.continuousOn (by norm_num [p] : (0:ℝ) ∈ Set.Ioo (p.eval 2) (p.eval 3))
  have hm : p.Monic := by unfold p; monicity <;> norm_num
  have hd : p.natDegree = 3 := by unfold p; compute_degree!
  have hab : a ≠ b := by linarith [ha.1, hb.2]
  have hac : a ≠ c := by linarith [ha.1, hc.2]
  have hbc : b ≠ c := by linarith [hb.1, hc.2]
  have hr : ({a,b,c} : Multiset ℝ) = p.roots := by
    apply Multiset.eq_of_le_of_card_le
    · have hn : ({a,b,c} : Multiset ℝ).Nodup := by simp [hab, hac, hbc]
      apply (Multiset.le_iff_subset hn).mpr
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (Polynomial.mem_roots hm.ne_zero).mpr hpa
      · exact (Polynomial.mem_roots hm.ne_zero).mpr hpb
      · exact (Polynomial.mem_roots hm.ne_zero).mpr hpc
    · simpa [hd] using p.card_roots'
  have hs : p.Splits := Polynomial.splits_iff_card_roots.mpr (by
    rw [← hr]
    simp [hab, hac, hbc, hd])
  have hf : p = (X-C a)*(X-C b)*(X-C c) := by
    rw [hs.eq_prod_roots_of_monic hm, ← hr]
    simp [mul_assoc]
  have hexp : (X-C a)*(X-C b)*(X-C c) =
      X^3-C (a+b+c)*X^2+C (a*b+a*c+b*c)*X-C (a*b*c) := by
    simp only [map_add, map_mul]
    ring
  have hv := congrArg (fun q : ℝ[X] => q.coeff 2) (hf.trans hexp)
  norm_num [p, Polynomial.coeff_mul_X_pow, Polynomial.coeff_mul_X,
    Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_one, ← map_add] at hv
  refine ⟨a,b,c,ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hf,?_⟩
  linarith

private theorem roots_four (a b c d : ℝ) :
    ((X-C a)*(X-C b)*(X-C c)*(X-C d)).roots = ({a,b,c,d} : Multiset ℝ) := by
  have h := Polynomial.roots_multiset_prod_X_sub_C ({a,b,c,d} : Multiset ℝ)
  simpa [mul_assoc] using h

private theorem A_spectrum (a b c : ℝ)
    (ha : 2 < a ∧ a < 3) (hb : 0 < b ∧ b < 1)
    (hc : -2 < c ∧ c < -1)
    (hf : p = (X-C a)*(X-C b)*(X-C c)) :
    List.ofFn (orderedSpectrum A A_hermitian) = [a,b,-1,c] := by
  have hroots : A.charpoly.roots = ({a,b,-1,c} : Multiset ℝ) := by
    have hh : A.charpoly = (X-C a)*(X-C b)*(X-C (-1))*(X-C c) := by
      rw [A_charpoly, hf]
      simp only [map_neg, map_one]
      ring
    rw [hh, roots_four]
  have hsort := A_hermitian.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real,
    Multiset.map_coe, Multiset.coe_sort] at hsort
  rw [List.ofFn_congr (Fintype.card_fin 4)] at hsort
  change ({a,b,-1,c} : Multiset ℝ).sort (· ≥ ·) =
    List.ofFn (orderedSpectrum A A_hermitian) at hsort
  have hlist : ({a,b,-1,c} : Multiset ℝ).sort (· ≥ ·) = [a,b,-1,c] := by
    apply List.mergeSort_eq_self
    simp only [List.pairwise_cons]
    constructor
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> linarith
    constructor
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> linarith
    constructor
    · intro x hx
      simp only [List.mem_singleton] at hx
      linarith
    simp
  rw [hlist] at hsort
  exact hsort.symm

private theorem B_spectrum :
    List.ofFn (orderedSpectrum B B_hermitian) = [2,0,-1,-1] := by
  have hroots : B.charpoly.roots = ({2,0,-1,-1} : Multiset ℝ) := by
    have hh : B.charpoly = (X-C 2)*(X-C 0)*(X-C (-1))*(X-C (-1)) := by
      rw [B_charpoly]
      have htwo : C (2:ℝ) = (2:ℝ[X]) := by
        simpa using (Polynomial.C_ofNat (R := ℝ) 2)
      norm_num [htwo]
      ring
    rw [hh, roots_four]
  have hsort := B_hermitian.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real,
    Multiset.map_coe, Multiset.coe_sort] at hsort
  rw [List.ofFn_congr (Fintype.card_fin 4)] at hsort
  change ({2,0,-1,-1} : Multiset ℝ).sort (· ≥ ·) =
    List.ofFn (orderedSpectrum B B_hermitian) at hsort
  have hlist : ({2,0,-1,-1} : Multiset ℝ).sort (· ≥ ·) = [2,0,-1,-1] := by
    apply List.mergeSort_eq_self
    norm_num [List.pairwise_cons]
  rw [hlist] at hsort
  exact hsort.symm

private theorem negA_spectrum (a b c : ℝ)
    (ha : 2 < a ∧ a < 3) (hb : 0 < b ∧ b < 1)
    (hc : -2 < c ∧ c < -1)
    (hf : p = (X-C a)*(X-C b)*(X-C c)) :
    List.ofFn (orderedSpectrum (-A) A_hermitian.neg) =
      [-c,1,-b,-a] := by
  have hroots : (-A).charpoly.roots = ({-c,1,-b,-a} : Multiset ℝ) := by
    have hneg : X^3+X^2-3*X-1 =
        (X-C (-c))*(X-C (-b))*(X-C (-a)) := by
      calc
        X^3+X^2-3*X-1 = -(p.comp (-X)) := by simp [p]; ring
        _ = -(((X-C a)*(X-C b)*(X-C c)).comp (-X)) := by rw [hf]
        _ = (X-C (-c))*(X-C (-b))*(X-C (-a)) := by
          simp
          ring
    have hh : (-A).charpoly =
        (X-C (-c))*(X-C 1)*(X-C (-b))*(X-C (-a)) := by
      rw [negA_charpoly, hneg]
      simp
      ring
    rw [hh, roots_four]
  have hsort := A_hermitian.neg.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real,
    Multiset.map_coe, Multiset.coe_sort] at hsort
  rw [List.ofFn_congr (Fintype.card_fin 4)] at hsort
  change ({-c,1,-b,-a} : Multiset ℝ).sort (· ≥ ·) =
    List.ofFn (orderedSpectrum (-A) A_hermitian.neg) at hsort
  have hlist : ({-c,1,-b,-a} : Multiset ℝ).sort (· ≥ ·) = [-c,1,-b,-a] := by
    apply List.mergeSort_eq_self
    simp only [List.pairwise_cons]
    constructor
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> linarith
    constructor
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> linarith
    constructor
    · intro x hx
      simp only [List.mem_singleton] at hx
      linarith
    simp
  rw [hlist] at hsort
  exact hsort.symm

private theorem negB_spectrum :
    List.ofFn (orderedSpectrum (-B) B_hermitian.neg) =
      [1,1,0,-2] := by
  have hroots : (-B).charpoly.roots = ({1,1,0,-2} : Multiset ℝ) := by
    have hh : (-B).charpoly = (X-C 1)*(X-C 1)*(X-C 0)*(X-C (-2)) := by
      rw [negB_charpoly]
      have htwo : C (2:ℝ) = (2:ℝ[X]) := by
        simpa using (Polynomial.C_ofNat (R := ℝ) 2)
      norm_num [htwo]
      ring
    rw [hh, roots_four]
  have hsort := B_hermitian.neg.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at hsort
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real,
    Multiset.map_coe, Multiset.coe_sort] at hsort
  rw [List.ofFn_congr (Fintype.card_fin 4)] at hsort
  change ({1,1,0,-2} : Multiset ℝ).sort (· ≥ ·) =
    List.ofFn (orderedSpectrum (-B) B_hermitian.neg) at hsort
  have hlist : ({1,1,0,-2} : Multiset ℝ).sort (· ≥ ·) = [1,1,0,-2] := by
    apply List.mergeSort_eq_self
    norm_num [List.pairwise_cons]
  rw [hlist] at hsort
  exact hsort.symm

private theorem spectrum_congr {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (hN : N.IsHermitian) (h : M = N) :
    orderedSpectrum M hM = orderedSpectrum N hN := by
  subst N
  rfl

private theorem beta_before (a b c : ℝ)
    (ha : 2 < a ∧ a < 3) (hb : 0 < b ∧ b < 1)
    (hc : -2 < c ∧ c < -1)
    (hf : p = (X-C a)*(X-C b)*(X-C c)) (hsum : a+b+c=1) :
    beta paw (fun _ => false) = 4 * (1-b)^2 := by
  have hs : orderedSpectrum A A_hermitian = ![a,b,-1,c] := by
    apply List.ofFn_injective
    simpa using A_spectrum a b c ha hb hc hf
  have hn : orderedSpectrum (-A) A_hermitian.neg = ![-c,1,-b,-a] := by
    apply List.ofFn_injective
    simpa using negA_spectrum a b c ha hb hc hf
  have hsign : signedAdj paw (fun _ => false) = -A :=
    (negative_adj paw).trans (congrArg Neg.neg paw_adj)
  unfold beta
  rw [spectrum_congr (signed_hermitian paw _) A_hermitian.neg hsign,
    spectrum_congr (underlying_hermitian paw) A_hermitian paw_adj, hs, hn]
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ]
  rw [show c = 1-a-b by linarith]
  ring

private theorem beta_after :
    beta (paw.deleteEdges {s(0,3)}) (fun _ => false) = 4 := by
  have hs : orderedSpectrum B B_hermitian = ![2,0,-1,-1] := by
    apply List.ofFn_injective
    simpa using B_spectrum
  have hn : orderedSpectrum (-B) B_hermitian.neg = ![1,1,0,-2] := by
    apply List.ofFn_injective
    simpa using negB_spectrum
  have hsign : signedAdj (paw.deleteEdges {s(0,3)}) (fun _ => false) = -B :=
    (negative_adj _).trans (congrArg Neg.neg deleted_adj)
  unfold beta
  rw [spectrum_congr (signed_hermitian _ _) B_hermitian.neg hsign,
    spectrum_congr (underlying_hermitian _) B_hermitian deleted_adj, hs, hn]
  norm_num [Fin.sum_univ_four]

theorem result : ¬ claim := by
  obtain ⟨a,b,c,ha0,ha1,hb0,hb1,hc0,hc1,hf,hsum⟩ := cubic_roots
  intro h
  have hedge : paw.Adj (0 : Fin 4) 3 := by
    simp [paw, SimpleGraph.fromEdgeSet_adj]
  have hineq := h 4 paw (fun _ => false) 0 3 hedge
  rw [beta_after, beta_before a b c ⟨ha0,ha1⟩ ⟨hb0,hb1⟩ ⟨hc0,hc1⟩ hf hsum] at hineq
  have hb : 0 < b := hb0
  have hb' : b < 2 := lt_trans hb1 (by norm_num)
  nlinarith [mul_pos hb (sub_pos.mpr hb')]

end D5.S3.Combinatorics.SignedGraphSpectral.MO479815
