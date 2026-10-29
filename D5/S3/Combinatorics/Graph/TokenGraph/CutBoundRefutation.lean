/- GID: D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.claim; result=D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.result; claim=D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.claim
   digest: A phase test on a C5 blow-up refutes the token-graph cut bound. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#15417; Refuted)
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
adjMatrix_complex_map: proof_shape: bind-only; escape_witness: none; direct frozen dependencies: none; consumers: lambdaMin40, AchterbergVanMieghemSubmodularityRefutation.spectral_sup_eq_edgeMax.
Escape audit unfinished for adjMatrix_complex_map: https://github.com/the-omega-institute/trureturing/issues/22239.
The source conventions are the unit-weight specialization preregistered in #15417.
The block map is Fin.divNat with divisor 40; G40 is SimpleGraph.comap of SimpleGraph.cycleGraph 5.
The counting identity is bind-only and is consumed within this settling module.
Direct frozen dependencies (declaration GID and declaration statement_id):
F0: D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.instTokenGraphDecidableAdj sha256:286622a3b1a8bfba4acf3e45e9b82464d87a6f4146ef846a4d881081f25b8ad7
F1: D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.tokenGraph sha256:c4f5907634190da69ec39e9b5a43e6128c6502eea91d910c8d09408e881287de
F2: D5/S3/Weil/ZetaLinear/HermitianPosPart.hermForm_specMap sha256:96bd93ead0f9b49ba54ca6aec9e73fb27ae4b8f81c7753c66c267846e41b1623
F3: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F4: D5/S3/Weil/ZetaLinear/HermitianPosPart.specMap_id sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
Per-declaration classification; columns: name | proof_shape | direct frozen dependencies | escape_witness | consumers.
crosses | bind-only | none | none | cut_card_eq_sum,cut_occupancy,maxCut,maxCut40
maxCut | bind-only | none | none | claim,maxCut40,result
maxMatchingLe | bind-only | none | none | claim,maxMatchingLe_le,result
maxMatchingLe_le | bind-only | none | none | result
lambdaMin | bind-only | none | none | claim,lambdaMin40,lambdaMin_quad,real_complex_rayleigh,result
claim | bind-only | F1,F0 | none | result
cycle5_iff | bind-only | none | none | c5_energy0,cut_occupancy
G40 | bind-only | none | none | cut_occupancy,edge_re_sum,lambdaMin40,maxCut40,phi40_energy,phi40_quotient,phi40_real_energy,result
block_card | bind-only | none | none | block_sum,occ_le,out_sum
block_sum | bind-only | none | none | edge_re_sum
z | bind-only | none | none | W,W_move,W_unit,c5_energy0,edge_re_sum,phase_constant,phi40_energy,phi40_real_energy,zpowstar,zstar
sum5 | bind-only | none | none | c5_energy0
c5_energy0 | bind-only | none | none | edge_re_sum
edge_re_sum | bind-only | none | none | phi40_real_energy
expand_S | bind-only | none | none | Test.pair_sum,counting_identity
card_move_family | bind-only | none | none | counting_identity
counting_identity | bind-only | none | none | phi40_energy
Test.move | bind-only | none | none | Test.adj_mem,Test.move_adj,Test.move_diff_left,Test.move_diff_right,Test.move_injective,Test.toNbr,Test.toNbr_bij
Test.move_adj | bind-only | none | none | Test.toNbr
Test.adj_mem | bind-only | F1 | none | Test.toNbr_bij
Test.move_diff_left | bind-only | none | none | Test.move_injective
Test.move_diff_right | bind-only | none | none | Test.move_injective
Test.move_injective | bind-only | none | none | Test.toNbr_bij
zstar | bind-only | none | none | zpowstar
zpowstar | bind-only | none | none | W_unit
W | bind-only | none | none | W_move,W_unit,phi40
W_unit | bind-only | none | none | W_move,phi40_norm
W_move | bind-only | none | none | phi40_energy
Test.toNbr | bind-only | F1 | none | Test.neighbor_sum_eq_pair_sum,Test.toNbr_bij,Test.token_energy,phi40_energy
Test.toNbr_bij | bind-only | F1 | none | Test.neighbor_sum_eq_pair_sum
Test.neighbor_sum_eq_pair_sum | bind-only | F1,F0 | none | Test.token_energy
Test.token_energy | bind-only | F1,F0 | none | phi40_energy
Test.pair_sum | bind-only | none | none | phi40_energy
phi40 | bind-only | none | none | lambdaMin40,phi40_energy,phi40_ne_zero,phi40_norm,phi40_quotient,phi40_real_energy
phi40_energy | bind-only | F1,F0 | none | phi40_real_energy
cut_card_eq_sum | bind-only | none | none | cut_occupancy
occ | bind-only | none | none | cut_occupancy,maxCut40,occ_le,out_sum
occ_le | bind-only | none | none | maxCut40
cutPoly | bind-only | none | none | cutPoly_affine,cutPoly_bits,cutPoly_endpoint,cutPoly_le,cut_occupancy,maxCut40
affine_endpoint | bind-only | none | none | cutPoly_endpoint
cutPoly_affine | bind-only | none | none | cutPoly_endpoint
cutPoly_endpoint | bind-only | none | none | cutPoly_le
cutPoly_bits | bind-only | none | none | cutPoly_le
cutPoly_le | bind-only | none | none | maxCut40
occ_sum | bind-only | none | none | cut_occupancy,out_sum
out_sum | bind-only | none | none | cut_occupancy
cut_occupancy | bind-only | none | none | maxCut40
maxCut40 | bind-only | none | none | result
lambdaMin_quad | bind-only | F2,F3,F4 | none | real_complex_rayleigh
complex_real_energy | bind-only | none | none | real_complex_rayleigh
complex_real_norm | bind-only | none | none | real_complex_rayleigh
complex_norm_pos | bind-only | none | none | real_complex_rayleigh
real_complex_rayleigh | bind-only | F2,F3,F4 | none | lambdaMin40
token_card40 | bind-only | none | none | phi40_norm
phi40_norm | bind-only | none | none | phi40_ne_zero,phi40_quotient
phase_constant | bind-only | none | none | phi40_real_energy
phi40_real_energy | bind-only | F1,F0 | none | phi40_quotient
choose_ratio40 | bind-only | none | none | phi40_quotient
phi40_quotient | bind-only | F0,F1 | none | lambdaMin40
phi40_ne_zero | bind-only | none | none | lambdaMin40
adjMatrix_complex_map | bind-only | none | none | lambdaMin40
lambdaMin40 | bind-only | F3,F0,F1,F2,F4 | none | result
result | bind-only | F3,F0,F1,F2,F4 | none | settling result
-/

import D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation
import D5.S3.Weil.ZetaLinear.HermitianPosPart

open Matrix Finset
open Classical
open scoped BigOperators ComplexConjugate ComplexOrder
open D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation (tokenGraph)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation

def crosses {n : ℕ} (S : Finset (Fin n)) : Sym2 (Fin n) → Prop :=
  Sym2.lift ⟨fun u v => (u ∈ S) ≠ (v ∈ S), by
    intro u v
    apply propext
    constructor <;> intro h <;> exact h.symm⟩
noncomputable def maxCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (Finset.univ : Finset (Finset (Fin n))).sup
    (fun S => (G.edgeFinset.filter (fun e => crosses S e)).card)
noncomputable def maxMatchingLe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : ℕ := by
  classical
  exact (G.edgeFinset.powerset.filter
    (fun M : Finset (Sym2 (Fin n)) => M.card ≤ k ∧
      (M : Set (Sym2 (Fin n))).Pairwise
        (fun e f => Disjoint (e : Set (Fin n)) (f : Set (Fin n))))).sup (fun M => M.card)
private lemma maxMatchingLe_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    maxMatchingLe G k ≤ k := by
  classical
  unfold maxMatchingLe
  apply Finset.sup_le
  intro M hM
  exact (Finset.mem_filter.mp hM).2.1

noncomputable def lambdaMin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ := by
  classical
  exact if hA : A.IsHermitian then
    if h : (Finset.univ : Finset ι).Nonempty then
      Finset.univ.inf' h hA.eigenvalues else 0
  else 0

def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ),
    1 ≤ k → k ≤ n / 2 →
      -(((maxCut G : ℝ) + (maxMatchingLe G k : ℝ)) / 2) ≤
        lambdaMin ((tokenGraph G k).adjMatrix ℝ)

private lemma cycle5_iff (i j : Fin 5) : (SimpleGraph.cycleGraph 5).Adj i j ↔
  (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨
  (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3) ∨
  (i=4 ∧ j=0) ∨ (i=0 ∧ j=4) := by
  fin_cases i <;> fin_cases j <;> decide
private def G40 : SimpleGraph (Fin 200) :=
  (SimpleGraph.cycleGraph 5).comap (Fin.divNat (m := 5) (n := 40))
private lemma block_card (i : Fin 5) :
    ((Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i)).card = 40 := by
  fin_cases i <;> decide

private lemma block_sum {α : Type*} [AddCommMonoid α] (F : Fin 5 → α) :
    (∑ u : Fin 200, F ((Fin.divNat (m := 5) (n := 40)) u)) = 40 • (∑ i : Fin 5, F i) := by
  have hf := Finset.sum_fiberwise (Finset.univ : Finset (Fin 200)) (Fin.divNat (m := 5) (n := 40)) (fun u => F ((Fin.divNat (m := 5) (n := 40)) u))
  calc
    (∑ u : Fin 200, F ((Fin.divNat (m := 5) (n := 40)) u)) =
        ∑ i : Fin 5, ∑ u ∈ (Finset.univ : Finset (Fin 200)) with (Fin.divNat (m := 5) (n := 40)) u = i, F ((Fin.divNat (m := 5) (n := 40)) u) := by simpa using hf.symm
    _ = ∑ i : Fin 5, 40 • F i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.sum_filter]
      have heq : ∀ u : Fin 200, (if (Fin.divNat (m := 5) (n := 40)) u = i then F ((Fin.divNat (m := 5) (n := 40)) u) else 0) =
          if (Fin.divNat (m := 5) (n := 40)) u = i then F i else 0 := by intro u; by_cases h : (Fin.divNat (m := 5) (n := 40)) u=i <;> simp [h]
      simp_rw [heq]
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      rw [block_card i]
    _ = 40 • (∑ i : Fin 5, F i) := by simp [Finset.smul_sum]

private noncomputable def z : ℂ := (-4 + 3 * Complex.I) / 5
lemma sum5 {α : Type*} [AddCommMonoid α] (f : Fin 5 → α) :
    (∑ i : Fin 5, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ]
  abel
private lemma c5_energy0 : (∑ i : Fin 5, (40 * ∑ j : Fin 5,
        if (SimpleGraph.cycleGraph 5).Adj i j then (star (z ^ i.val) * z ^ j.val).re else 0)) =
      (2 * 40 : ℝ) * (4 * z.re + (z ^ (4 : Fin 5).val).re) := by
  classical
  have h0 : (∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj 0 j then (star (z ^ (0 : Fin 5).val) * z ^ j.val).re else 0) =
      (star (z ^ (0 : Fin 5).val) * z ^ (1 : Fin 5).val).re + (star (z ^ (0 : Fin 5).val) * z ^ (4 : Fin 5).val).re := by
    simp [Fin.sum_univ_succ, cycle5_iff]
  have h1 : (∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj 1 j then (star (z ^ (1 : Fin 5).val) * z ^ j.val).re else 0) =
      (star (z ^ (1 : Fin 5).val) * z ^ (0 : Fin 5).val).re + (star (z ^ (1 : Fin 5).val) * z ^ (2 : Fin 5).val).re := by
    simp [Fin.sum_univ_succ, cycle5_iff]
  have h2 : (∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj 2 j then (star (z ^ (2 : Fin 5).val) * z ^ j.val).re else 0) =
      (star (z ^ (2 : Fin 5).val) * z ^ (1 : Fin 5).val).re + (star (z ^ (2 : Fin 5).val) * z ^ (3 : Fin 5).val).re := by
    simp [Fin.sum_univ_succ, cycle5_iff]
  have h3 : (∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj 3 j then (star (z ^ (3 : Fin 5).val) * z ^ j.val).re else 0) =
      (star (z ^ (3 : Fin 5).val) * z ^ (2 : Fin 5).val).re + (star (z ^ (3 : Fin 5).val) * z ^ (4 : Fin 5).val).re := by
    simp [Fin.sum_univ_succ, cycle5_iff]
  have h4 : (∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj 4 j then (star (z ^ (4 : Fin 5).val) * z ^ j.val).re else 0) =
      (star (z ^ (4 : Fin 5).val) * z ^ (3 : Fin 5).val).re + (star (z ^ (4 : Fin 5).val) * z ^ (0 : Fin 5).val).re := by
    simp [Fin.sum_univ_succ, cycle5_iff] <;> ring
  rw [sum5]
  rw [h0, h1, h2, h3, h4]
  have hz2 : z^2 = (7/25 - (24/25) * Complex.I) := by
    apply Complex.ext <;> norm_num [z, pow_two, Complex.mul_re, Complex.mul_im]
  have hz3 : z^3 = (44/125 + (117/125) * Complex.I) := by
    rw [show z^3 = z^2 * z by ring, hz2]
    apply Complex.ext <;> norm_num [z, Complex.mul_re, Complex.mul_im]
  have hz4 : z^4 = (-527/625 - (336/625) * Complex.I) := by
    rw [show z^4 = z^2 * z^2 by ring, hz2]
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hzs : star z = (-4/5 - (3/5) * Complex.I) := by
    apply Complex.ext
    · norm_num [z]
    · norm_num [z]
  have t01 : (star (z ^ (0 : Fin 5).val) * z ^ (1 : Fin 5).val).re = (-4/5 : ℝ) := by
    norm_num [z, Complex.ext_iff, Complex.mul_re, Complex.mul_im, starRingEnd_apply]
  have t04 : (star (z ^ (0 : Fin 5).val) * z ^ (4 : Fin 5).val).re = (-527/625 : ℝ) := by
    rw [show z ^ (4 : Fin 5).val = z^4 by norm_num, hz4]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t10 : (star (z ^ (1 : Fin 5).val) * z ^ (0 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (1 : Fin 5).val = z by norm_num, hzs,
      show z ^ (0 : Fin 5).val = z^0 by norm_num, show z^0 = 1 by simp]
    norm_num [z, Complex.mul_re, Complex.mul_im]
  have t12 : (star (z ^ (1 : Fin 5).val) * z ^ (2 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (1 : Fin 5).val = z by norm_num, hzs,
      show z ^ (2 : Fin 5).val = z^2 by norm_num, hz2]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t21 : (star (z ^ (2 : Fin 5).val) * z ^ (1 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (2 : Fin 5).val = z^2 by norm_num, hz2,
      show z ^ (1 : Fin 5).val = z by norm_num]
    norm_num [z, Complex.mul_re, Complex.mul_im]
  have t23 : (star (z ^ (2 : Fin 5).val) * z ^ (3 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (2 : Fin 5).val = z^2 by norm_num, hz2,
      show z ^ (3 : Fin 5).val = z^3 by norm_num, hz3]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t32 : (star (z ^ (3 : Fin 5).val) * z ^ (2 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (3 : Fin 5).val = z^3 by norm_num, hz3,
      show z ^ (2 : Fin 5).val = z^2 by norm_num, hz2]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t34 : (star (z ^ (3 : Fin 5).val) * z ^ (4 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (3 : Fin 5).val = z^3 by norm_num, hz3,
      show z ^ (4 : Fin 5).val = z^4 by norm_num, hz4]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t43 : (star (z ^ (4 : Fin 5).val) * z ^ (3 : Fin 5).val).re = (-4/5 : ℝ) := by
    rw [show z ^ (4 : Fin 5).val = z^4 by norm_num, hz4,
      show z ^ (3 : Fin 5).val = z^3 by norm_num, hz3]
    norm_num [Complex.mul_re, Complex.mul_im]
  have t40 : (star (z ^ (4 : Fin 5).val) * z ^ (0 : Fin 5).val).re = (-527/625 : ℝ) := by
    rw [show z ^ (4 : Fin 5).val = z^4 by norm_num, hz4,
      show z ^ (0 : Fin 5).val = z^0 by norm_num, show z^0 = 1 by simp]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [t01, t04, t10, t12, t21, t23, t32, t34, t43, t40]
  rw [show z ^ (4 : Fin 5).val = z^4 by norm_num, hz4]
  norm_num [z, Complex.mul_re, Complex.mul_im]


private lemma edge_re_sum :
    (∑ u : Fin 200, ∑ v : Fin 200,
      if G40.Adj u v then (star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val).re else 0) =
      (2 * 40^2 : ℝ) * (4 * z.re + (z^4).re) := by
  classical
  have hinner (i : Fin 5) :
      (∑ v : Fin 200, if (SimpleGraph.cycleGraph 5).Adj i ((Fin.divNat (m := 5) (n := 40)) v) then (star (z ^ i.val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val).re else 0) =
        40 * ∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj i j then (star (z ^ i.val) * z ^ j.val).re else 0 := by
    let F : Fin 5 → ℝ := fun j => if (SimpleGraph.cycleGraph 5).Adj i j then (star (z ^ i.val) * z ^ j.val).re else 0
    simpa [F] using block_sum F
  calc
    _ = ∑ u : Fin 200, (40 * ∑ j : Fin 5,
        if (SimpleGraph.cycleGraph 5).Adj ((Fin.divNat (m := 5) (n := 40)) u) j then (star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ j.val).re else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        (∑ v : Fin 200, if G40.Adj u v then
            (star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val).re else 0) =
            ∑ v : Fin 200, if (SimpleGraph.cycleGraph 5).Adj ((Fin.divNat (m := 5) (n := 40)) u) ((Fin.divNat (m := 5) (n := 40)) v) then
            (star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val).re else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases h : (SimpleGraph.cycleGraph 5).Adj ((Fin.divNat (m := 5) (n := 40)) u) ((Fin.divNat (m := 5) (n := 40)) v) <;> simp [G40, h]
        _ = _ := hinner ((Fin.divNat (m := 5) (n := 40)) u)
    _ = 40 * ∑ i : Fin 5, (40 * ∑ j : Fin 5,
        if (SimpleGraph.cycleGraph 5).Adj i j then (star (z ^ i.val) * z ^ j.val).re else 0) := by
      let F : Fin 5 → ℝ := fun i => 40 * ∑ j : Fin 5,
        if (SimpleGraph.cycleGraph 5).Adj i j then (star (z ^ i.val) * z ^ j.val).re else 0
      simpa [F, mul_assoc] using block_sum F
    _ = (2 * 40^2 : ℝ) * (4 * z.re + (z^4).re) := by
      rw [c5_energy0]
      rw [show z ^ (4 : Fin 5).val = z^4 by norm_num]
      ring

private lemma expand_S {V α : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid α]
    (S : Finset V) (f : V → V → α) :
    (∑ u ∈ S, ∑ v ∈ ((Finset.univ : Finset V).filter (fun v => v ∉ S)), f u v) =
      ∑ u : V, ∑ v : V, if u ∈ S ∧ v ∉ S then f u v else 0 := by
  have hS : (Finset.univ : Finset V).filter (fun u => u ∈ S) = S := by simp
  rw [← hS]
  rw [Finset.sum_filter]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h1 : u ∈ S
  · simp [h1]
  · simp [h1]

private lemma card_move_family {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (u v : V) (huv : u ≠ v) :
    ((Finset.powersetCard k (Finset.univ : Finset V)).filter
      (fun S => u ∈ S ∧ v ∉ S)).card =
      Nat.choose (Fintype.card V - 2) (k - 1) := by
  classical
  have hsub : ({u} : Finset V) ⊆ (Finset.univ : Finset V).erase v := by
    simpa using huv
  have hh := Finset.card_filter_powersetCard_subset {u}
    ((Finset.univ : Finset V).erase v) k hsub (by simpa using hk)
  have hf : (Finset.powersetCard k (Finset.univ : Finset V)).filter
      (fun S => u ∈ S ∧ v ∉ S) =
      (((Finset.univ : Finset V).erase v).powersetCard k).filter
        (fun S => ({u} : Finset V) ⊆ S) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.singleton_subset_iff,
      Finset.subset_univ, true_and, Finset.subset_erase, and_assoc]
    tauto
  rw [hf, hh]
  simp [Nat.sub_sub]

private lemma counting_identity {V : Type*} [Fintype V] [DecidableEq V]
    {α : Type*} [AddCommMonoid α] (k : ℕ) (hk : 1 ≤ k)
    (f : V → V → α) :
    (∑ S : Set.powersetCard V k,
      ∑ u ∈ S.1, (∑ v ∈ ((Finset.univ : Finset V).filter (fun v => v ∉ S.1)), f u v)) =
      Nat.choose (Fintype.card V - 2) (k - 1) •
        (∑ u : V, (∑ v ∈ ((Finset.univ : Finset V).filter (fun v => v ≠ u)), f u v)) := by
  classical
  let P : Finset (Finset V) := Finset.powersetCard k (Finset.univ : Finset V)
  have hP : ∀ S : Finset V, S ∈ P ↔ S.card = k := by
    intro S; simp [P]
  rw [← Finset.sum_subtype P (by intro S; simp [hP S])
    (fun S : Finset V => ∑ u ∈ S, (∑ v ∈ ((Finset.univ : Finset V).filter (fun v => v ∉ S)), f u v))]
  simp_rw [expand_S]
  change (∑ y ∈ P, ∑ x ∈ (Finset.univ : Finset V),
      ∑ v ∈ (Finset.univ : Finset V), if x ∈ y ∧ v ∉ y then f x v else 0) = _
  have hs1 : (∑ y ∈ P, ∑ x ∈ (Finset.univ : Finset V),
      ∑ v ∈ (Finset.univ : Finset V), if x ∈ y ∧ v ∉ y then f x v else 0) =
      ∑ x ∈ (Finset.univ : Finset V), ∑ y ∈ P,
        ∑ v ∈ (Finset.univ : Finset V), if x ∈ y ∧ v ∉ y then f x v else 0 := by
    rw [Finset.sum_comm]
  rw [hs1]
  have hs2 : (∑ x ∈ (Finset.univ : Finset V), ∑ y ∈ P,
      ∑ v ∈ (Finset.univ : Finset V), if x ∈ y ∧ v ∉ y then f x v else 0) =
      ∑ x ∈ (Finset.univ : Finset V), ∑ v ∈ (Finset.univ : Finset V), ∑ y ∈ P,
        if x ∈ y ∧ v ∉ y then f x v else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
  rw [hs2]
  let C : ℕ := Nat.choose (Fintype.card V - 2) (k - 1)
  have hpair (x v : V) :
      (∑ y ∈ P, if x ∈ y ∧ v ∉ y then f x v else 0) =
        if x ≠ v then C • f x v else 0 := by
    by_cases hne : x ≠ v
    · have hc := card_move_family hk x v hne
      rw [← Finset.sum_filter]
      rw [show P.filter (fun S => x ∈ S ∧ v ∉ S) =
          (Finset.powersetCard k (Finset.univ : Finset V)).filter
            (fun S => x ∈ S ∧ v ∉ S) by rfl]
      rw [Finset.sum_const, hc]
      simp [C, hne]
    · have hxeq : x = v := by tauto
      subst v
      simp
  simp_rw [hpair]
  change (∑ x ∈ (Finset.univ : Finset V), ∑ v ∈ (Finset.univ : Finset V),
      if x ≠ v then C • f x v else 0) = _
  -- Pull out the constant and identify the off-diagonal filter.
  rw [show (∑ x ∈ (Finset.univ : Finset V), ∑ v ∈ (Finset.univ : Finset V),
      if x ≠ v then C • f x v else 0) =
      C • (∑ x ∈ (Finset.univ : Finset V), ∑ v ∈ (Finset.univ : Finset V),
        if x ≠ v then f x v else 0) by
      simp [Finset.smul_sum]]
  simp only [C]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_filter]
  simp [eq_comm]

namespace Test

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

private noncomputable def move (S : Set.powersetCard V k) (u v : V) (hu : u ∈ S.1) (hv : v ∉ S.1) : Set.powersetCard V k :=
  ⟨insert v (S.1.erase u), by
    change (insert v (S.1.erase u)).card = k
    have hv' : v ∉ S.1.erase u := by simp [hv]
    calc
      (insert v (S.1.erase u)).card = (S.1.erase u).card + 1 := Finset.card_insert_of_notMem hv'
      _ = (S.1.card - 1) + 1 := by rw [Finset.card_erase_of_mem hu]
      _ = k := by
        rw [S.2]
        have hk0 : 1 ≤ S.1.card := Finset.one_le_card.mpr ⟨u, hu⟩
        have hk : 1 ≤ k := by simpa [S.2] using hk0
        exact Nat.sub_add_cancel hk⟩

private lemma move_adj (S : Set.powersetCard V k) (u v : V) (hu : u ∈ S.1) (hv : v ∉ S.1) (hadj : G.Adj u v) :
    (tokenGraph G k).Adj S (move k S u v hu hv) := by
  refine ⟨u, v, ?_, ?_, hadj⟩
  · ext x
    by_cases hxu : x = u <;> by_cases hxv : x = v <;>
      simp [move, hxu, hxv, hu, hv, hadj.ne, Ne.symm hadj.ne]
  · ext x
    by_cases hxu : x = u <;> by_cases hxv : x = v <;>
      simp [move, hxu, hxv, hu, hv, hadj.ne, Ne.symm hadj.ne]

private lemma adj_mem (S T : Set.powersetCard V k) (h : (tokenGraph G k).Adj S T) :
    ∃ u v, ∃ hu : u ∈ S.1, ∃ hv : v ∉ S.1, G.Adj u v ∧ T = move k S u v hu hv := by
  rcases h with ⟨u, v, h1, h2, huv⟩
  have hu : u ∈ S.1 := by
    have hx := congrArg (fun q : Finset V => u ∈ q) h1
    simp at hx
    exact hx.1
  have hv : v ∉ S.1 := by
    have hx := congrArg (fun q : Finset V => v ∈ q) h2
    simp at hx
    exact hx.2
  refine ⟨u, v, hu, hv, huv, ?_⟩
  apply Subtype.ext
  ext x
  have h1x := congrArg (fun q : Finset V => x ∈ q) h1
  have h2x := congrArg (fun q : Finset V => x ∈ q) h2
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at h1x h2x
  have h1x' : (x ∈ S.1 ∧ x ∉ T.1) ↔ x = u := by rw [h1x]
  have h2x' : (x ∈ T.1 ∧ x ∉ S.1) ↔ x = v := by rw [h2x]
  by_cases hxv : x = v
  · subst x
    have hvt : v ∈ T.1 := (h2x'.mpr rfl).1
    simp [move, hvt]
  by_cases hxu : x = u
  · subst x
    have hut : u ∉ T.1 := (h1x'.mpr rfl).2
    simp [move, hu, hv, huv.ne, hut]
  simp only [move, Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro hxt
    by_cases hxs : x ∈ S.1
    · exact Or.inr ⟨hxu, hxs⟩
    · have hxv' : x = v := (h2x'.mp ⟨hxt, hxs⟩)
      exact (hxv hxv').elim
  · intro hr
    rcases hr with hxeq | ⟨hxu', hxs⟩
    · exact (hxv hxeq).elim
    · by_contra hxt
      exact hxu (h1x'.mp ⟨hxs, hxt⟩)

end Test

namespace Test
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

private lemma move_diff_left (S : Set.powersetCard V k) (u v : V) (hu : u ∈ S.1) (hv : v ∉ S.1) :
    S.1 \ (move k S u v hu hv).1 = {u} := by
  have huv : u ≠ v := by intro h; subst v; exact hv hu
  ext x
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    simp [move, hxu, hxv, hu, hv, huv, huv.symm]

private lemma move_diff_right (S : Set.powersetCard V k) (u v : V) (hu : u ∈ S.1) (hv : v ∉ S.1) :
    (move k S u v hu hv).1 \ S.1 = {v} := by
  have huv : u ≠ v := by intro h; subst v; exact hv hu
  ext x
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    simp [move, hxu, hxv, hu, hv, huv, huv.symm]

private lemma move_injective (S : Set.powersetCard V k)
    {u v u' v' : V} (hu : u ∈ S.1) (hv : v ∉ S.1)
    (hu' : u' ∈ S.1) (hv' : v' ∉ S.1)

    (h : move k S u v hu hv = move k S u' v' hu' hv') : u = u' ∧ v = v' := by
  have hL : (S.1 \ (move k S u v hu hv).1) = (S.1 \ (move k S u' v' hu' hv').1) := by rw [h]
  have hR : ((move k S u v hu hv).1 \ S.1) = ((move k S u' v' hu' hv').1 \ S.1) := by rw [h]
  have huEq : ({u} : Finset V) = {u'} := by rw [← move_diff_left k S u v hu hv, ← move_diff_left k S u' v' hu' hv', hL]
  have hvEq : ({v} : Finset V) = {v'} := by rw [← move_diff_right k S u v hu hv, ← move_diff_right k S u' v' hu' hv', hR]
  exact ⟨Finset.singleton_injective huEq, Finset.singleton_injective hvEq⟩

end Test
open scoped BigOperators ComplexConjugate
noncomputable section
private lemma zstar : star z * z = 1 := by
  norm_num [z, Complex.ext_iff, mul_add, add_mul, Complex.mul_re, Complex.mul_im]
private lemma zpowstar (n : ℕ) : star (z ^ n) * z ^ n = 1 := by
  rw [star_pow, ← mul_pow, zstar, one_pow]

private def W {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → ℕ) (S : Finset V) : ℂ := S.prod (fun x => z ^ b x)
private lemma W_unit {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → ℕ) (S : Finset V) : star (W b S) * W b S = 1 := by
  classical
  simp only [W, star_prod, ← Finset.prod_mul_distrib]
  simp only [zpowstar, Finset.prod_const_one]

private lemma W_move {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → ℕ) (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∉ S) :
    star (W b S) * W b (insert v (S.erase u)) =
      star (z ^ b u) * z ^ b v := by
  classical
  have huv : u ≠ v := by intro h; subst v; exact hv hu
  have hsu : S = insert u (S.erase u) := (Finset.insert_erase hu).symm
  have hW : W b S = z ^ b u * W b (S.erase u) := by
    unfold W
    have hnot : u ∉ S.erase u := by simp
    rw [hsu, Finset.prod_insert hnot]
    simp [hnot]
  have hWv : W b (insert v (S.erase u)) = z ^ b v * W b (S.erase u) := by
    simp [W, hv]
  rw [hW, hWv, star_mul]
  calc
    star (W b (S.erase u)) * star (z ^ b u) *
        (z ^ b v * W b (S.erase u)) =
        star (z ^ b u) * z ^ b v *
          (star (W b (S.erase u)) * W b (S.erase u)) := by ring
    _ = star (z ^ b u) * z ^ b v := by rw [W_unit]; simp
open Matrix Finset
open scoped BigOperators ComplexConjugate
namespace Test

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

private noncomputable def toNbr (S : Set.powersetCard V k) : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2} → {T : Set.powersetCard V k // (tokenGraph G k).Adj S T} := fun p =>
  ⟨move k S p.1.1 p.1.2 p.2.1 p.2.2.1,
    move_adj G k S p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2⟩

private lemma toNbr_bij (S : Set.powersetCard V k) : Function.Bijective (toNbr G k S) := by
  constructor
  · intro p q h
    have hm := congrArg Subtype.val h
    have huv := move_injective k S p.2.1 p.2.2.1 q.2.1 q.2.2.1 hm
    apply Subtype.ext
    apply Prod.ext huv.1 huv.2
  · intro T
    rcases adj_mem G k S T.1 T.2 with ⟨u, v, hu, hv, huv, hT⟩
    let p : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2} := ⟨(u, v), hu, hv, huv⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hT.symm

private lemma neighbor_sum_eq_pair_sum (S : Set.powersetCard V k) (φ : Set.powersetCard V k → ℂ) :
    (∑ T ∈ (tokenGraph G k).neighborFinset S, star (φ S) * φ T) =
      ∑ p : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2}, star (φ S) * φ (toNbr G k S p) := by
  let e : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2} ≃ {T : Set.powersetCard V k // (tokenGraph G k).Adj S T} := Equiv.ofBijective (toNbr G k S) (toNbr_bij G k S)
  have hs : (∑ T ∈ (tokenGraph G k).neighborFinset S,
      star (φ S) * φ T) = ∑ T : {T : Set.powersetCard V k // (tokenGraph G k).Adj S T}, star (φ S) * φ T.1 := by
    apply Finset.sum_subtype
    intro T
    simp [SimpleGraph.mem_neighborFinset]
  rw [hs]
  rw [← Fintype.sum_equiv e]
  intro x
  rfl

private lemma token_energy (φ : Set.powersetCard V k → ℂ) :
    dotProduct (star φ) ((tokenGraph G k).adjMatrix ℂ *ᵥ φ) =
      ∑ S : Set.powersetCard V k, ∑ p : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2},
        star (φ S) * φ (toNbr G k S p) := by
  simp only [dotProduct, SimpleGraph.adjMatrix_mulVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact neighbor_sum_eq_pair_sum G k S φ

private lemma pair_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (S : Set.powersetCard V k) (H : V → V → ℂ) :
    (∑ p : {p : V × V // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2}, H p.1.1 p.1.2) =
      ∑ u ∈ S.1, ∑ v ∈ ((Finset.univ : Finset V).filter (fun v => v ∉ S.1)),
        if G.Adj u v then H u v else 0 := by
  classical
  rw [expand_S]
  have hprod :
      (∑ u : V, ∑ v : V, if u ∈ S.1 ∧ v ∉ S.1 then
        if G.Adj u v then H u v else 0 else 0) =
      ∑ p : V × V, if p.1 ∈ S.1 ∧ p.2 ∉ S.1 then
        if G.Adj p.1 p.2 then H p.1 p.2 else 0 else 0 := by
    rw [Fintype.sum_prod_type]
  rw [hprod]
  let Q : Finset (V × V) := (Finset.univ : Finset (V × V)).filter
    (fun p => p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G.Adj p.1 p.2)
  rw [← Finset.sum_subtype Q (by intro p; simp [Q])
      (fun p : V × V => H p.1 p.2)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h1 : p.1 ∈ S.1 <;> by_cases h2 : p.2 ∉ S.1 <;> by_cases h3 : G.Adj p.1 p.2 <;> simp [h1,h2,h3]

end Test

end

open scoped BigOperators ComplexConjugate
private noncomputable def phi40 (S : Set.powersetCard (Fin 200) 100) : ℂ := W (fun v : Fin 200 => (Fin.divNat (m := 5) (n := 40) v).val) S.1

private lemma phi40_energy :
    dotProduct (star phi40) ((D5.S3.Combinatorics.Graph.TokenGraphLaplacianRadiusRefutation.tokenGraph G40 100).adjMatrix ℂ *ᵥ phi40) =
      (Nat.choose 198 99 : ℂ) *
        (∑ u : Fin 200, ∑ v ∈ (Finset.univ : Finset (Fin 200)).filter (fun v => v ≠ u),
          if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0) := by
  rw [Test.token_energy]
  have hpoint (S : Set.powersetCard (Fin 200) 100) :
      (∑ p : {p : Fin 200 × Fin 200 // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G40.Adj p.1 p.2},
        star (phi40 S) * phi40 (Test.toNbr G40 100 S p)) =
      ∑ u ∈ S.1, ∑ v ∈ ((Finset.univ : Finset (Fin 200)).filter (fun v => v ∉ S.1)),
        if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0 := by
    calc
      (∑ p : {p : Fin 200 × Fin 200 // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G40.Adj p.1 p.2},
          star (phi40 S) * phi40 (Test.toNbr G40 100 S p)) =
          ∑ p : {p : Fin 200 × Fin 200 // p.1 ∈ S.1 ∧ p.2 ∉ S.1 ∧ G40.Adj p.1 p.2},
            star (z ^ ((Fin.divNat (m := 5) (n := 40)) p.1.1).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) p.1.2).val := by
              apply Finset.sum_congr rfl
              intro p hp
              rcases p.property with ⟨hpu, hpv, hpA⟩
              change star (W (fun v : Fin 200 => (Fin.divNat (m := 5) (n := 40) v).val) S.1) *
                W (fun v : Fin 200 => (Fin.divNat (m := 5) (n := 40) v).val) (insert p.1.2 (S.1.erase p.1.1)) = _
              exact W_move (fun v : Fin 200 => (Fin.divNat (m := 5) (n := 40) v).val) S.1 p.1.1 p.1.2 hpu hpv
      _ = ∑ u ∈ S.1, ∑ v ∈ ((Finset.univ : Finset (Fin 200)).filter (fun v => v ∉ S.1)),
          if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0 := by
            exact Test.pair_sum G40 100 S (fun u v => star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val)
  simp_rw [hpoint]
  have hc := counting_identity (V := Fin 200) 100 (by norm_num)
    (fun u v => if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0)
  rw [hc]
  norm_num

private lemma cut_card_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    (G.edgeFinset.filter (crosses S)).card =
      ∑ u : Fin n, ∑ v : Fin n, if G.Adj u v ∧ u ∈ S ∧ v ∉ S then 1 else 0 := by
  classical
  let Q := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)
  have himage : Q.image (fun p => s(p.1, p.2)) = G.edgeFinset.filter (crosses S) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      simp only [Q, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change (∃ p : Fin n × Fin n, (G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S) ∧ s(p.1,p.2) = s(u,v)) ↔
        G.Adj u v ∧ (u ∈ S) ≠ (v ∈ S)
      constructor
      · rintro ⟨⟨a,b⟩, ⟨hab, ha, hb⟩, he⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hab, by tauto⟩
        · exact ⟨hab.symm, by tauto⟩
      · rintro ⟨huv, hc⟩
        by_cases hu : u ∈ S
        · exact ⟨(u,v), ⟨huv,hu,by tauto⟩,rfl⟩
        · exact ⟨(v,u), ⟨huv.symm,by tauto,hu⟩, Sym2.eq_swap⟩
  have hinj : Set.InjOn (fun p : Fin n × Fin n => s(p.1,p.2)) Q := by
    intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Prod.ext ha hb
    · exact False.elim (hq'.2.2 (ha ▸ hp'.2.1))
  rw [← himage, Finset.card_image_of_injOn hinj]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ p : Fin n × Fin n, if G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S then 1 else 0) = _
  rw [Fintype.sum_prod_type]

private noncomputable def occ (S : Finset (Fin 200)) (i : Fin 5) : ℕ :=
  ((Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i ∧ u ∈ S)).card

private lemma occ_le (S : Finset (Fin 200)) (i : Fin 5) : occ S i ≤ 40 := by
  rw [← block_card i]
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩

private noncomputable def cutPoly (x : Fin 5 → ℝ) : ℝ :=
  x 0 * (40-x 1) + x 1 * (40-x 0) +
  x 1 * (40-x 2) + x 2 * (40-x 1) +
  x 2 * (40-x 3) + x 3 * (40-x 2) +
  x 3 * (40-x 4) + x 4 * (40-x 3) +
  x 4 * (40-x 0) + x 0 * (40-x 4)

private lemma affine_endpoint (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 40) :
    a + t/40*(b-a) ≤ a ∨ a + t/40*(b-a) ≤ b := by
  by_cases h : b ≤ a
  · left; nlinarith
  · right; nlinarith

private lemma cutPoly_affine (x : Fin 5 → ℝ) (i : Fin 5) (t : ℝ) :
    cutPoly (Function.update x i t) = cutPoly (Function.update x i 0) +
      t/40 * (cutPoly (Function.update x i 40) - cutPoly (Function.update x i 0)) := by
  fin_cases i <;> simp [cutPoly, Function.update] <;> ring

private lemma cutPoly_endpoint (x : Fin 5 → ℝ) (i : Fin 5)
    (h0 : 0 ≤ x i) (h40 : x i ≤ 40) :
    ∃ t : ℝ, (t = 0 ∨ t = 40) ∧ cutPoly x ≤ cutPoly (Function.update x i t) := by
  have h := affine_endpoint (cutPoly (Function.update x i 0))
    (cutPoly (Function.update x i 40)) (x i) h0 h40
  rw [← cutPoly_affine, Function.update_eq_self] at h
  rcases h with h | h
  · exact ⟨0, Or.inl rfl, h⟩
  · exact ⟨40, Or.inr rfl, h⟩

private lemma cutPoly_bits (x : Fin 5 → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 40) :
    cutPoly x ≤ 6400 := by
  rcases hx 0 with h0 | h0 <;>
  rcases hx 1 with h1 | h1 <;>
  rcases hx 2 with h2 | h2 <;>
  rcases hx 3 with h3 | h3 <;>
  rcases hx 4 with h4 | h4 <;> norm_num [cutPoly, h0, h1, h2, h3, h4]

private lemma cutPoly_le (x : Fin 5 → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 40) :
    cutPoly x ≤ 6400 := by
  obtain ⟨t0,ht0,h0⟩ := cutPoly_endpoint x 0 (hx 0).1 (hx 0).2
  obtain ⟨t1,ht1,h1⟩ := cutPoly_endpoint (Function.update x 0 t0) 1
    (by simpa using (hx 1).1) (by simpa using (hx 1).2)
  obtain ⟨t2,ht2,h2⟩ := cutPoly_endpoint (Function.update (Function.update x 0 t0) 1 t1) 2
    (by simpa using (hx 2).1) (by simpa using (hx 2).2)
  obtain ⟨t3,ht3,h3⟩ := cutPoly_endpoint (Function.update (Function.update (Function.update x 0 t0) 1 t1) 2 t2) 3
    (by simpa using (hx 3).1) (by simpa using (hx 3).2)
  obtain ⟨t4,ht4,h4⟩ := cutPoly_endpoint (Function.update (Function.update (Function.update (Function.update x 0 t0) 1 t1) 2 t2) 3 t3) 4
    (by simpa using (hx 4).1) (by simpa using (hx 4).2)
  have hh := cutPoly_bits (Function.update (Function.update (Function.update (Function.update (Function.update x 0 t0) 1 t1) 2 t2) 3 t3) 4 t4)
    (by
      intro i
      fin_cases i
      · simpa using ht0
      · simpa using ht1
      · simpa using ht2
      · simpa using ht3
      · simpa using ht4)
  linarith

private lemma occ_sum (S : Finset (Fin 200)) (i : Fin 5) :
    (∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
      if u ∈ S then (1 : ℝ) else 0) = occ S i := by
  simp only [Finset.sum_boole, Finset.filter_filter, occ]

private lemma out_sum (S : Finset (Fin 200)) (i : Fin 5) :
    (∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
      if u ∉ S then (1 : ℝ) else 0) = 40 - occ S i := by
  have hh : (∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
      if u ∉ S then (1 : ℝ) else 0) +
      (∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
      if u ∈ S then (1 : ℝ) else 0) = 40 := by
    rw [← Finset.sum_add_distrib]
    have ht : ∀ u : Fin 200, (if u ∉ S then (1 : ℝ) else 0) +
      (if u ∈ S then (1 : ℝ) else 0) = 1 := by intro u; by_cases h : u ∈ S <;> simp [h]
    simp_rw [ht]
    simp only [Finset.sum_const, block_card, nsmul_eq_mul, mul_one, Nat.cast_ofNat]
  rw [occ_sum] at hh
  linarith

private lemma cut_occupancy (S : Finset (Fin 200)) :
    ((G40.edgeFinset.filter (crosses S)).card : ℝ) = cutPoly (fun i => occ S i) := by
  rw [cut_card_eq_sum]
  have hind : (∑ u : Fin 200, ∑ v : Fin 200,
    (if G40.Adj u v ∧ u ∈ S ∧ v ∉ S then 1 else 0 : ℕ) : ℕ) =
    ∑ u : Fin 200, ∑ v : Fin 200, if (SimpleGraph.cycleGraph 5).Adj ((Fin.divNat (m := 5) (n := 40)) u) ((Fin.divNat (m := 5) (n := 40)) v) then
      (if u ∈ S then 1 else 0)*(if v ∉ S then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases ha : G40.Adj u v <;> by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp_all [G40]
  rw [hind]
  push_cast
  let H : Fin 200 → Fin 200 → ℝ := fun u v => if (SimpleGraph.cycleGraph 5).Adj ((Fin.divNat (m := 5) (n := 40)) u) ((Fin.divNat (m := 5) (n := 40)) v) then
    (if u ∈ S then 1 else 0)*(if v ∉ S then 1 else 0) else 0
  change (∑ u, ∑ v, H u v) = _
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 200)) (Fin.divNat (m := 5) (n := 40)) (fun u => ∑ v, H u v)]
  have hp (i : Fin 5) :
      (∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i), ∑ v, H u v) =
      ∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj i j then (occ S i : ℝ)*(40 - occ S j) else 0 := by
    have hv (u : Fin 200) (hui : (Fin.divNat (m := 5) (n := 40)) u = i) :
      (∑ v, H u v) = ∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj i j then
        (if u ∈ S then (1 : ℝ) else 0)*(40 - occ S j) else 0 := by
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 200)) (Fin.divNat (m := 5) (n := 40)) (fun v => H u v)]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : (SimpleGraph.cycleGraph 5).Adj i j
      · simp only [if_pos hij]
        rw [← out_sum S j, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        have hvj := (Finset.mem_filter.mp hv).2
        simp [H, hui, hvj, hij]
      · simp only [if_neg hij]
        apply Finset.sum_eq_zero
        intro v hv
        have hvj := (Finset.mem_filter.mp hv).2
        simp [H, hui, hvj, hij]
    calc
      _ = ∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
        ∑ j : Fin 5, if (SimpleGraph.cycleGraph 5).Adj i j then (if u ∈ S then (1 : ℝ) else 0)*(40 - occ S j) else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hv u (Finset.mem_filter.mp hu).2
      _ = ∑ j : Fin 5, ∑ u ∈ (Finset.univ : Finset (Fin 200)).filter (fun u => (Fin.divNat (m := 5) (n := 40)) u = i),
        if (SimpleGraph.cycleGraph 5).Adj i j then (if u ∈ S then (1 : ℝ) else 0)*(40 - occ S j) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : (SimpleGraph.cycleGraph 5).Adj i j
        · simp only [if_pos hij]
          rw [← Finset.sum_mul, occ_sum]
        · simp [hij]
  simp_rw [hp]
  simp [Fin.sum_univ_succ, cycle5_iff, cutPoly]
  ring

private lemma maxCut40 : maxCut G40 ≤ 6400 := by
  unfold maxCut
  apply Finset.sup_le
  intro S hS
  have hh := cutPoly_le (fun i => (occ S i : ℝ))
    (by intro i; exact ⟨Nat.cast_nonneg _, by exact_mod_cast occ_le S i⟩)
  rw [← cut_occupancy] at hh
  exact_mod_cast hh

private lemma lambdaMin_quad {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (u : n → ℝ) :
    lambdaMin A * dotProduct u u ≤ dotProduct u (A *ᵥ u) := by
  classical
  have hn : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty
  rw [lambdaMin, dif_pos hA, dif_pos hn]
  have he := RHLinalg.hermForm_specMap hA id u
  have hs := RHLinalg.hermForm_specMap hA 1 u
  have hs1 : RHLinalg.specMap hA 1 = (1 : Matrix n n ℝ) := by
    unfold RHLinalg.specMap
    simp
  rw [RHLinalg.specMap_id] at he
  rw [hs1] at hs
  simp only [star_trivial, RCLike.re_to_real, Matrix.one_mulVec, Pi.one_apply, one_mul] at he hs
  rw [he, hs, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (Finset.inf'_le _ (mem_univ i)) (sq_nonneg _)

private lemma complex_real_energy {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (w : n → ℂ) :
    (dotProduct (star w) ((A.map Complex.ofReal) *ᵥ w)).re =
      dotProduct (fun i => (w i).re) (A *ᵥ (fun i => (w i).re)) +
      dotProduct (fun i => (w i).im) (A *ᵥ (fun i => (w i).im)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
    Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma complex_real_norm {n : Type*} [Fintype n] (w : n → ℂ) :
    (dotProduct (star w) w).re =
      dotProduct (fun i => (w i).re) (fun i => (w i).re) +
      dotProduct (fun i => (w i).im) (fun i => (w i).im) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma complex_norm_pos {n : Type*} [Fintype n] (w : n → ℂ) (hw : w ≠ 0) :
    0 < (dotProduct (star w) w).re := by
  exact (Complex.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hw)).1

private lemma real_complex_rayleigh {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (w : n → ℂ) (hw : w ≠ 0) :
    lambdaMin A ≤ (dotProduct (star w) ((A.map Complex.ofReal) *ᵥ w)).re /
      (dotProduct (star w) w).re := by
  classical
  haveI : Nonempty n := by
    by_contra h
    haveI : IsEmpty n := not_nonempty_iff.mp h
    exact hw (funext (fun i => isEmptyElim i))
  have h1 := lambdaMin_quad A hA (fun i => (w i).re)
  have h2 := lambdaMin_quad A hA (fun i => (w i).im)
  have hd := complex_norm_pos w hw
  apply (le_div_iff₀ hd).mpr
  rw [complex_real_energy, complex_real_norm, mul_add]
  exact add_le_add h1 h2

private lemma token_card40 : Fintype.card (Set.powersetCard (Fin 200) 100) = Nat.choose 200 100 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    (Set.powersetCard.card (α := Fin 200) (n := 100))

private lemma phi40_norm : dotProduct (star phi40) phi40 = (Nat.choose 200 100 : ℂ) := by
  change (∑ S, star (phi40 S) * phi40 S) = _
  rw [show (∑ S, star (phi40 S) * phi40 S) = ∑ S : Set.powersetCard (Fin 200) 100, (1 : ℂ) by
    apply Finset.sum_congr rfl
    intro S hS
    exact W_unit (fun v : Fin 200 => (Fin.divNat (m := 5) (n := 40) v).val) S.1]
  simp only [Finset.sum_const, Finset.card_univ, token_card40, nsmul_eq_mul, mul_one]

private lemma phase_constant : 4*z.re + (z^4).re = (-2527/625 : ℝ) := by
  norm_num [z, pow_succ, Complex.mul_re, Complex.mul_im]

private lemma phi40_real_energy :
    (dotProduct (star phi40) ((tokenGraph G40 100).adjMatrix ℂ *ᵥ phi40)).re =
      (Nat.choose 198 99 : ℝ) * ((2 * 40^2 : ℝ) * (-2527/625)) := by
  rw [phi40_energy]
  have hoff : (∑ u : Fin 200, ∑ v ∈ (Finset.univ : Finset (Fin 200)).filter (fun v => v ≠ u),
      if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0) =
      ∑ u : Fin 200, ∑ v : Fin 200,
      if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v = u
    · subst v; simp
    · simp [h]
  rw [hoff]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have hs : (∑ u : Fin 200, ∑ v : Fin 200,
      if G40.Adj u v then star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val else 0).re =
      ∑ u : Fin 200, ∑ v : Fin 200,
      if G40.Adj u v then (star (z ^ ((Fin.divNat (m := 5) (n := 40)) u).val) * z ^ ((Fin.divNat (m := 5) (n := 40)) v).val).re else 0 := by
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> rfl
  rw [hs, edge_re_sum, phase_constant]

private lemma choose_ratio40 : (Nat.choose 198 99 : ℝ) / (Nat.choose 200 100 : ℝ) = 50/199 := by
  have h1 := Nat.choose_mul_succ_eq 198 99
  have h2 := Nat.add_one_mul_choose_eq 199 99
  norm_num only [Nat.reduceAdd, Nat.reduceSub] at h1 h2
  have h1r : (Nat.choose 198 99 : ℝ)*199 = (Nat.choose 199 99 : ℝ)*100 := by exact_mod_cast h1
  have h2r : 200*(Nat.choose 199 99 : ℝ) = (Nat.choose 200 100 : ℝ)*100 := by exact_mod_cast h2
  have hb : (Nat.choose 200 100 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by decide : 100 ≤ 200)))
  apply (div_eq_iff hb).mpr
  nlinarith

private lemma phi40_quotient :
    (dotProduct (star phi40) ((tokenGraph G40 100).adjMatrix ℂ *ᵥ phi40)).re /
      (dotProduct (star phi40) phi40).re = -646912/199 := by
  rw [phi40_real_energy, phi40_norm, Complex.natCast_re]
  calc
    _ = ((2 * 40^2 : ℝ) * (-2527/625)) *
      ((Nat.choose 198 99 : ℝ) / (Nat.choose 200 100 : ℝ)) := by ring
    _ = _ := by rw [choose_ratio40]; norm_num

private lemma phi40_ne_zero : phi40 ≠ 0 := by
  intro h
  have hn := phi40_norm
  rw [h] at hn
  simp only [star_zero, dotProduct_zero, zero_mul] at hn
  have hp : (Nat.choose 200 100 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by decide : 100 ≤ 200)))
  exact hp hn.symm

lemma adjMatrix_complex_map {n : Type*} [Fintype n] [DecidableEq n]
    (G : SimpleGraph n) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).map Complex.ofReal = G.adjMatrix ℂ := by
  classical
  ext i j
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix, Matrix.map_apply, h]

private lemma lambdaMin40 : lambdaMin ((tokenGraph G40 100).adjMatrix ℝ) ≤ -646912/199 := by
  have hr := real_complex_rayleigh ((tokenGraph G40 100).adjMatrix ℝ)
    ((tokenGraph G40 100).isHermitian_adjMatrix ℝ) phi40 phi40_ne_zero
  rw [adjMatrix_complex_map, phi40_quotient] at hr
  exact hr

theorem result : ¬ claim := by
  intro h
  have hclaim := h 200 G40 100 (by norm_num) (by norm_num)
  have hc : (maxCut G40 : ℝ) ≤ 6400 := by exact_mod_cast maxCut40
  have hm : (maxMatchingLe G40 100 : ℝ) ≤ 100 := by exact_mod_cast maxMatchingLe_le G40 100
  have hr := lambdaMin40
  linarith


end D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation
