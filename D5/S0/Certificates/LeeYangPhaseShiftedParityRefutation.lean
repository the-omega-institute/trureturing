/- GID: D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/LeeYangPhaseShiftedParityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.claim; result=D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.result; claim=D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.claim
   digest: A pi-flux four-cycle refutes the phase-shifted parity conjecture. -/

/-
admission_basis: open-problem-resolution (#18759; Refuted).
Direct frozen dependencies: none.
hpq: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
H: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
eigAsc: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
claim: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
cycle: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
instDecidableCycle: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
phase: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
bits: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
bits_bijective: proof_shape: bind-only; escape_witness: none; consumers: ham_separation.
ham_expand: proof_shape: bind-only; escape_witness: none; consumers: ham_table.
oddIndex: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
odd_weight_iff_hammingNorm: proof_shape: bind-only; escape_witness: none; consumers: oddBits.
oddBits: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
oddBits_bijective: proof_shape: bind-only; escape_witness: none; consumers: ham_separation.
cycle_connected: proof_shape: bind-only; escape_witness: none; consumers: result.
concrete: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
ham_table: proof_shape: bind-only; escape_witness: none; consumers: ham_separation.
concrete_hermitian: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues, concrete_separation.
oddConcrete: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
odd_table: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation, ham_separation.
odd_polynomial: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
eigAsc_roots: proof_shape: bind-only; escape_witness: none; consumers: eigAsc_submatrix_equiv.
eigAsc_submatrix_equiv: proof_shape: bind-only; escape_witness: none; consumers: ham_separation.
eigAsc_mem_iff: proof_shape: bind-only; escape_witness: none; consumers: eigenvector_mem_eigAsc, odd_quadratic_bound.
eigenvector_mem_eigAsc: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues.
eigAsc_pairwise: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
second_le_of_two_mem: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
odd_quadratic_bound: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
ra: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
rb: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
ra_poly: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues.
rb_poly: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues.
root_order: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
va: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
vb: proof_shape: bind-only; escape_witness: none; consumers: result (through the definitions and certificate).
va_eigen: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues.
vb_eigen: proof_shape: bind-only; escape_witness: none; consumers: two_eigenvalues.
two_eigenvalues: proof_shape: bind-only; escape_witness: none; consumers: concrete_separation.
concrete_separation: proof_shape: bind-only; escape_witness: none; consumers: ham_separation.
ham_separation: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source expressions use Fin n → Fin 2 directly, without a carrier alias.
The claim inlines the source odd-weight count; oddBits uses Mathlib hammingNorm
through odd_weight_iff_hammingNorm, without a duplicate counting definition.
The second eigenvalue is indexed from zero and counted with multiplicity.
The phase function ranges over real representatives, as in #18759; the witness uses 0 and π.
Only the strict spectral separation at s = 3/5 is asserted; simplicity and a parameter interval
are not conclusions of this module.
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.List.GetD
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation

open Matrix

/-- `h(z) = |00⟩⟨00| + z |11⟩⟨00| + z* |00⟩⟨11| + |z|² |11⟩⟨11|` on qubits `p, q`, the identity on the others. -/
noncomputable def hpq {n : ℕ} (p q : Fin n) (z : ℂ) : Matrix ((Fin n → Fin 2)) ((Fin n → Fin 2)) ℂ := fun y x =>
  if ∀ k, k ≠ p → k ≠ q → y k = x k then
    (if x p = 0 ∧ x q = 0 ∧ y p = 0 ∧ y q = 0 then 1 else 0) +
    (if x p = 0 ∧ x q = 0 ∧ y p = 1 ∧ y q = 1 then z else 0) +
    (if x p = 1 ∧ x q = 1 ∧ y p = 0 ∧ y q = 0 then (starRingEnd ℂ) z else 0) +
    (if x p = 1 ∧ x q = 1 ∧ y p = 1 ∧ y q = 1 then ((Complex.normSq z : ℝ) : ℂ) else 0)
  else 0

/-- The phase-shifted EPR-like Hamiltonian `H_s(θ) = −∑_{(p,q) ∈ E} h_{p,q}(s e^{i θ_{p,q}})`, each edge counted
once (`p < q`). -/
noncomputable def H {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℝ) (θ : Fin n → Fin n → ℝ) :
    Matrix ((Fin n → Fin 2)) ((Fin n → Fin 2)) ℂ :=
  -∑ p : Fin n, ∑ q : Fin n,
    if p < q ∧ G.Adj p q then hpq p q ((s : ℂ) * Complex.exp (((θ p q : ℝ) : ℂ) * Complex.I)) else 0

/-- The eigenvalues of a Hermitian matrix, with multiplicity, in increasing order (empty if not Hermitian). -/
noncomputable def eigAsc {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : List ℝ :=
  if h : M.IsHermitian then (Finset.univ.val.map h.eigenvalues).sort (· ≤ ·) else []

/-- Wong–Bravyi–Gosset–Liu, arXiv:2602.03605v1, Section 5.6: Conjecture 2 ("Suppose n ≥ 2, s ∈ [0, 1), and the
interaction graph is connected. Then the second smallest eigenvalue of H_s coincides with the smallest eigenvalue of
H_s restricted to the odd-weight subspace.") for phase-shifted EPR-like Hamiltonians H_s(θ), every θ. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj, G.Connected →
    ∀ s : ℝ, 0 ≤ s → s < 1 → ∀ θ : Fin n → Fin n → ℝ,
      (eigAsc (H G s θ)).getD 1 0 =
        (eigAsc ((H G s θ).submatrix (Subtype.val : {x : (Fin n → Fin 2) // Odd ((Finset.univ.filter fun k => x k = 1).card)} → (Fin n → Fin 2)) Subtype.val)).getD 0 0

end D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def cycle : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ (i.val + j.val) % 2 = 1
  symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa [Nat.add_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

private instance instDecidableCycle : DecidableRel cycle.Adj := fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (i.val + j.val) % 2 = 1))

private noncomputable def phase (i j : Fin 4) : ℝ := if i = 0 ∧ j = 3 then Real.pi else 0

private def bits : Fin 16 → (Fin 4 → Fin 2) := ![
 ![0,0,0,0], ![0,0,0,1], ![0,0,1,0], ![0,0,1,1],
 ![0,1,0,0], ![0,1,0,1], ![0,1,1,0], ![0,1,1,1],
 ![1,0,0,0], ![1,0,0,1], ![1,0,1,0], ![1,0,1,1],
 ![1,1,0,0], ![1,1,0,1], ![1,1,1,0], ![1,1,1,1]]

private lemma bits_bijective : Function.Bijective bits := by
  decide +kernel

private lemma ham_expand : (H cycle (3/5) phase) = -(hpq 0 1 (3/5) + hpq 0 3 (-3/5) + hpq 1 2 (3/5) + hpq 2 3 (3/5)) := by
  simp [H, Fin.sum_univ_succ, cycle, phase, Complex.exp_pi_mul_I, neg_div, add_assoc]

private def oddIndex : Fin 8 → Fin 16 := ![1,2,4,7,8,11,13,14]

private lemma odd_weight_iff_hammingNorm {n : ℕ} (x : Fin n → Fin 2) :
    Odd ((Finset.univ.filter fun k => x k = 1).card) ↔ Odd (hammingNorm x) := by
  unfold hammingNorm
  have hfilter : (Finset.univ.filter fun k => x k = 1) =
      (Finset.univ.filter fun k => x k ≠ 0) := by
    apply Finset.filter_congr
    intro k _
    exact ⟨fun h => by simp [h], Fin.eq_one_of_ne_zero (x k)⟩
  rw [hfilter]

private def oddBits (i : Fin 8) : {x : (Fin 4 → Fin 2) // Odd ((Finset.univ.filter fun k => x k = 1).card)} :=
  ⟨bits (oddIndex i), (odd_weight_iff_hammingNorm _).mpr (by fin_cases i <;> decide +kernel)⟩

private lemma oddBits_bijective : Function.Bijective oddBits := by
  decide +kernel

private lemma cycle_connected : cycle.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable cycle).mpr
  refine ⟨0, ?_⟩
  intro i
  fin_cases i
  · exact SimpleGraph.Reachable.refl 0
  · exact (show cycle.Adj 0 1 by decide).reachable
  · exact (show cycle.Adj 0 1 by decide).reachable.trans
      (show cycle.Adj 1 2 by decide).reachable
  · exact (show cycle.Adj 0 3 by decide).reachable

private noncomputable def concrete : Matrix (Fin 16) (Fin 16) ℂ := ![
 ![-4,0,0,(-3/5),0,0,(-3/5),0,0,(3/5),0,0,(-3/5),0,0,0],
 ![0,-2,0,0,0,0,0,(-3/5),0,0,0,0,0,(-3/5),0,0],
 ![0,0,-2,0,0,0,0,0,0,0,0,(3/5),0,0,(-3/5),0],
 ![(-3/5),0,0,(-34/25),0,0,0,0,0,0,0,0,0,0,0,(-3/5)],
 ![0,0,0,0,-2,0,0,(-3/5),0,0,0,0,0,(3/5),0,0],
 ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
 ![(-3/5),0,0,0,0,0,(-34/25),0,0,0,0,0,0,0,0,(3/5)],
 ![0,(-3/5),0,0,(-3/5),0,0,(-18/25),0,0,0,0,0,0,0,0],
 ![0,0,0,0,0,0,0,0,-2,0,0,(-3/5),0,0,(-3/5),0],
 ![(3/5),0,0,0,0,0,0,0,0,(-34/25),0,0,0,0,0,(-3/5)],
 ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
 ![0,0,(3/5),0,0,0,0,0,(-3/5),0,0,(-18/25),0,0,0,0],
 ![(-3/5),0,0,0,0,0,0,0,0,0,0,0,(-34/25),0,0,(-3/5)],
 ![0,(-3/5),0,0,(3/5),0,0,0,0,0,0,0,0,(-18/25),0,0],
 ![0,0,(-3/5),0,0,0,0,0,(-3/5),0,0,0,0,0,(-18/25),0],
 ![0,0,0,(-3/5),0,0,(3/5),0,0,(-3/5),0,0,(-3/5),0,0,(-36/25)]]

private lemma ham_table : (H cycle (3/5) phase).submatrix bits bits = concrete := by
  rw [ham_expand]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.submatrix_apply, concrete, bits, hpq, Fin.forall_fin_succ,
      Complex.normSq_apply, Complex.div_re, Complex.div_im, starRingEnd_apply]

private lemma concrete_hermitian : concrete.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [concrete]

private noncomputable def oddConcrete : Matrix (Fin 8) (Fin 8) ℂ := ![
 ![-2,0,0,(-3/5),0,0,(-3/5),0],
 ![0,-2,0,0,0,(3/5),0,(-3/5)],
 ![0,0,-2,(-3/5),0,0,(3/5),0],
 ![(-3/5),0,(-3/5),(-18/25),0,0,0,0],
 ![0,0,0,0,-2,(-3/5),0,(-3/5)],
 ![0,(3/5),0,0,(-3/5),(-18/25),0,0],
 ![(-3/5),0,(3/5),0,0,0,(-18/25),0],
 ![0,(-3/5),0,0,(-3/5),0,0,(-18/25)]]

private lemma odd_table : concrete.submatrix oddIndex oddIndex = oddConcrete := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma odd_polynomial : (25 : ℂ) • (oddConcrete * oddConcrete) +
    (68 : ℂ) • oddConcrete + (18 : ℂ) • 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, oddConcrete, Matrix.one_apply]

end D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation

namespace D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation
open Matrix
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private lemma eigAsc_roots {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    eigAsc M = (M.charpoly.roots.map Complex.re).sort (· ≤ ·) := by
  have he : M.charpoly.roots.map Complex.re = Finset.univ.val.map hM.eigenvalues := by
    rw [hM.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    rfl
  simp only [eigAsc, dite_eq_left hM, he]

private lemma eigAsc_submatrix_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    eigAsc (M.submatrix e e) = eigAsc M := by
  by_cases hM : M.IsHermitian
  · rw [eigAsc_roots (hM.submatrix e), eigAsc_roots hM]
    have hc := Matrix.charpoly_reindex e.symm M
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using congrArg
      (fun p : Polynomial ℂ => (p.roots.map Complex.re).sort (· ≤ ·)) hc
  · simp [eigAsc, hM, Matrix.isHermitian_submatrix_equiv]

private lemma eigAsc_mem_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (r : ℝ) :
    r ∈ eigAsc M ↔ ∃ i, hM.eigenvalues i = r := by
  simp [eigAsc, hM, Multiset.mem_map]

private lemma eigenvector_mem_eigAsc {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (r : ℝ) (v : ι → ℂ)
    (hv : v ≠ 0) (he : M *ᵥ v = (r : ℂ) • v) : r ∈ eigAsc M := by
  have hev : Module.End.HasEigenvector M.toLin' (r : ℂ) v :=
    ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  have hsp : (r : ℂ) ∈ spectrum ℂ M := by
    rw [← Matrix.spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector hev).mem_spectrum
  rw [hM.spectrum_eq_image_range] at hsp
  rcases hsp with ⟨u, ⟨i, rfl⟩, hi⟩
  exact (eigAsc_mem_iff hM r).mpr ⟨i, Complex.ofReal_injective hi⟩

private lemma eigAsc_pairwise {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : (eigAsc M).Pairwise (· ≤ ·) := by
  simp only [eigAsc, dite_eq_left hM]
  exact Multiset.pairwise_sort _ _

private lemma second_le_of_two_mem (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (a b : ℝ) (ha : a ∈ l) (hb : b ∈ l) (hab : a < b) : l.getD 1 0 ≤ b := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => simp only [List.mem_singleton] at ha hb; linarith
    | cons y ys =>
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      have hb' : b ∈ y :: ys := by
        rcases List.mem_cons.mp hb with hbx | hbt
        · rcases List.mem_cons.mp ha with hax | hat
          · exact False.elim (by linarith)
          · have hxa : x ≤ a := (List.pairwise_cons.mp hs).1 _ hat
            exact False.elim (by linarith)
        · exact hbt
      rcases List.mem_cons.mp hb' with hby | hby
      · exact le_of_eq hby.symm
      · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 _ hby

private lemma odd_quadratic_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (hp : (25 : ℂ) • (M * M) + (68 : ℂ) • M + (18 : ℂ) • 1 = 0)
    (r : ℝ) (hr : r ∈ eigAsc M) : -(5/2 : ℝ) < r := by
  obtain ⟨i, hi⟩ := (eigAsc_mem_iff hM r).mp hr
  have hsp : (r : ℂ) ∈ spectrum ℂ M := by
    rw [hM.spectrum_eq_image_range]
    refine ⟨hM.eigenvalues i, ⟨i, rfl⟩, ?_⟩
    rw [hi]
    rfl
  have hsp' : (r : ℂ) ∈ spectrum ℂ M.toLin' := by
    rwa [Matrix.spectrum_toLin']
  obtain ⟨v, hev⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hsp').exists_hasEigenvector
  have hv : v ≠ 0 := hev.2
  have he : M *ᵥ v = (r : ℂ) • v := Module.End.mem_eigenspace_iff.mp hev.1
  have hq := congrArg (fun A : Matrix ι ι ℂ => A *ᵥ v) hp
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, he] at hq
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  have hqj := congrFun hq j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hqj
  have hpoly : (25 : ℂ) * (r : ℂ)^2 + 68 * r + 18 = 0 := by
    apply (mul_eq_zero.mp (show ((25 : ℂ)*(r : ℂ)^2 + 68*r + 18)*v j = 0 by
      calc _ = 25 * ((r : ℂ) * ((r : ℂ) * v j)) + 68 * ((r : ℂ) * v j) + 18 * v j := by ring
           _ = 0 := hqj)).resolve_right hj
  have hreal : 25*r^2 + 68*r + 18 = 0 := by exact_mod_cast hpoly
  by_contra! hn
  have hprod : 0 ≤ (r + 5/2) * (r + 11/50) := mul_nonneg_of_nonpos_of_nonpos
    (by linarith) (by linarith)
  nlinarith

private noncomputable def ra : ℝ := -(67 + Real.sqrt 1989) / 25
private noncomputable def rb : ℝ := -(35 + Real.sqrt 901) / 25

private lemma ra_poly : 25 * ra^2 + 134 * ra + 100 = 0 := by
  have hd : discrim (25 : ℝ) 134 100 = (2 * Real.sqrt 1989) * (2 * Real.sqrt 1989) := by
    calc
      _ = 4 * (Real.sqrt 1989)^2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num [discrim]
      _ = _ := by ring
  simpa only [ra, pow_two] using
    (quadratic_eq_zero_iff (by norm_num : (25 : ℝ) ≠ 0) hd
      (-(67 + Real.sqrt 1989) / 25)).mpr (Or.inr (by ring))

private lemma rb_poly : 625 * rb^2 + 1750 * rb + 324 = 0 := by
  have hd : discrim (625 : ℝ) 1750 324 = (50 * Real.sqrt 901) * (50 * Real.sqrt 901) := by
    calc
      _ = 2500 * (Real.sqrt 901)^2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num [discrim]
      _ = _ := by ring
  simpa only [rb, pow_two] using
    (quadratic_eq_zero_iff (by norm_num : (625 : ℝ) ≠ 0) hd
      (-(35 + Real.sqrt 901) / 25)).mpr (Or.inr (by ring))

private lemma root_order : ra < rb ∧ rb < -(5/2 : ℝ) := by
  have ha' : (33 : ℝ) < Real.sqrt 1989 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hb' : (30 : ℝ) < Real.sqrt 901 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hb'' : Real.sqrt 901 < (40 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [ra, rb]
  constructor <;> linarith

private noncomputable def va (r : ℂ) : Fin 16 → ℂ := ![
  6/5, 0, 0, (-r-4)/2, 0, 0, (-r-4)/2, 0,
  0, -(-r-4)/2, 0, 0, (-r-4)/2, 0, 0, 0]

private noncomputable def vb (r : ℂ) : Fin 16 → ℂ := ![
  0, 0, 0, (-r-36/25)/2, 0, 0, -(-r-36/25)/2, 0,
  0, (-r-36/25)/2, 0, 0, (-r-36/25)/2, 0, 0, 6/5]

private lemma va_eigen (r : ℂ) (hr : 25*r^2 + 134*r + 100 = 0) :
    concrete *ᵥ va r = r • va r := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, concrete, va] <;>
    first | (ring; done) | (linear_combination hr / 50; done) | (linear_combination -hr / 50; done)

private lemma vb_eigen (r : ℂ) (hr : 625*r^2 + 1750*r + 324 = 0) :
    concrete *ᵥ vb r = r • vb r := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, concrete, vb] <;>
    first | (ring; done) | (linear_combination hr / 1250; done) | (linear_combination -hr / 1250; done)

private lemma two_eigenvalues : ra ∈ eigAsc concrete ∧ rb ∈ eigAsc concrete := by
  constructor
  · apply eigenvector_mem_eigAsc concrete_hermitian ra (va (ra : ℂ))
    · intro h
      have hh := congrFun h 0
      norm_num [va] at hh
    · apply va_eigen
      exact_mod_cast ra_poly
  · apply eigenvector_mem_eigAsc concrete_hermitian rb (vb (rb : ℂ))
    · intro h
      have hh := congrFun h 15
      norm_num [vb] at hh
    · apply vb_eigen
      exact_mod_cast rb_poly

private lemma concrete_separation :
    (eigAsc concrete).getD 1 0 < (eigAsc oddConcrete).getD 0 0 := by
  have hO : oddConcrete.IsHermitian := by
    rw [← odd_table]
    exact concrete_hermitian.submatrix oddIndex
  have hlen : (eigAsc oddConcrete).length = 8 := by simp [eigAsc, hO]
  have hmem : (eigAsc oddConcrete).getD 0 0 ∈ eigAsc oddConcrete := by
    rw [List.getD_eq_getElem _ _ (by omega : 0 < (eigAsc oddConcrete).length)]
    exact List.getElem_mem _
  have hbound := odd_quadratic_bound hO odd_polynomial _ hmem
  have htwo := two_eigenvalues
  have hsecond := second_le_of_two_mem (eigAsc concrete) (eigAsc_pairwise concrete_hermitian)
    ra rb htwo.1 htwo.2 root_order.1
  linarith [root_order.2]

private lemma ham_separation :
    (eigAsc (H cycle (3/5) phase)).getD 1 0 <
    (eigAsc ((H cycle (3/5) phase).submatrix (Subtype.val : {x : (Fin 4 → Fin 2) // Odd ((Finset.univ.filter fun k => x k = 1).card)} → (Fin 4 → Fin 2)) Subtype.val)).getD 0 0 := by
  have hfull : eigAsc concrete = eigAsc (H cycle (3/5) phase) := by
    rw [← ham_table]
    exact eigAsc_submatrix_equiv (H cycle (3/5) phase) (Equiv.ofBijective bits bits_bijective)
  have hodd : eigAsc oddConcrete =
      eigAsc ((H cycle (3/5) phase).submatrix (Subtype.val : {x : (Fin 4 → Fin 2) // Odd ((Finset.univ.filter fun k => x k = 1).card)} → (Fin 4 → Fin 2)) Subtype.val) := by
    have hmatrix : ((H cycle (3/5) phase).submatrix (Subtype.val : {x : (Fin 4 → Fin 2) // Odd ((Finset.univ.filter fun k => x k = 1).card)} → (Fin 4 → Fin 2)) Subtype.val).submatrix
        (Equiv.ofBijective oddBits oddBits_bijective) (Equiv.ofBijective oddBits oddBits_bijective) = oddConcrete := by
      change ((H cycle (3/5) phase).submatrix bits bits).submatrix oddIndex oddIndex = _
      rw [ham_table]
      exact odd_table
    rw [← hmatrix]
    exact eigAsc_submatrix_equiv _ (Equiv.ofBijective oddBits oddBits_bijective)
  simpa only [hfull, hodd] using concrete_separation

theorem result : ¬ claim := by
  intro hc
  have hh := hc 4 (by norm_num) cycle inferInstance cycle_connected
    (3/5) (by norm_num) (by norm_num) phase
  exact (ne_of_lt ham_separation) hh


end D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation
