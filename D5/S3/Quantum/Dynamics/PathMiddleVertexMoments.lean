/- GID: D5/S3/Quantum/Dynamics/PathMiddleVertexMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PathMiddleVertexMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Middle-vertex weights and integer moments of odd paths with end transfer at time pi. -/

/-
proof_shape: middle_vertex_weights: content; escape_witness: the public conclusion itself (form
2; the preregistered middle-vertex weight formula of research line #14293): on the even spectral
class A, of m + 1 integer eigenvalues, the squared modulus of the eigenvector at the middle vertex
is ∏_{l ∉ A} (z k - z l) / ∏_{l ∈ A, l ≠ k} (z k - z l). It is produced by the sign classes of
the eigenvectors under the reversal, the trace count #A = m + 1, and two nodal extractions from
the moments between the first vertex and the last and middle ones; no Mathlib or frozen
declaration states it. consumer: middle_vertex_moments.
proof_shape: middle_vertex_moments: content; escape_witness: the public conclusion itself (form
2; the preregistered integer-moment parity theorem): the moments (H ^ p) c c at the middle
vertex are the integers [X^m] ((X^p * P_B) mod P_A), congruent to C(m, p) modulo 2, by the
Lagrange coefficient formula over the class A and the reduction of the nodal polynomials to
X^(m+1) and (X + 1)^m in (ZMod 2)[X]. consumer:
D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer (private step no_phase_one_transfer).
proof_shape: reversal_symmetric: bind-only (entrywise reading of the commutation of the
Hamiltonian with the reversal form of the propagator given by
D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.reversal_columns); consumer:
D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer (private step no_phase_one_transfer, as the
hypothesis of middle_moment_gram_det).
Private helpers:
proof_shape: eigenvector_rev: bind-only; consumer: middle_vertex_weights.
proof_shape: sum_phase_eq_trace: bind-only; consumer: middle_vertex_weights.
proof_shape: propagator_eq_reversal: bind-only; consumer: reversal_symmetric,
middle_vertex_weights.
admission_basis: escape-witness (research line #14293, partial progress on the rational weights
conjecture of arXiv:1708.03283: together with
D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer the conjecture is settled for every odd
number of vertices; it remains open for every even number of vertices n >= 6).
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian
  statement_id sha256:2a698170a16b6888380fcc8f26eb4e7fe06d99129518c7579da37d4ef440257a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.HasPST
  statement_id sha256:757dd0796ec75540b7989b0cc8ff7b30e16f838075ebdaf9dafec9866abcd80e.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.hamiltonianPropagator_neg
  statement_id sha256:da8dbba3289b5b062201fbfd2fbbd7c20cb092e36332ca39429a937e653cffca.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_isHermitian
  statement_id sha256:755bd6b7f287f1c2db4b69ff7180d3a28df65cd848b5650641594b8a3fef7195.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.spectral_pow_apply
  statement_id sha256:09249d0c938a2b12488df9f2e39de2d3082706016dad8e6e51bfda11594300ad.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.spectral_exp
  statement_id sha256:3e16b248dd122a54a985897b8b1c864134c9a4202fa1e8b72375fa331ccb0025.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.exists_int_of_exp_eq_one
  statement_id sha256:a641d776813aab202f943e68cf676b0c39d315528a3e281ef99f7ec954149696.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.exists_int_of_exp_eq_neg_one
  statement_id sha256:28c73025e98c6a65c928b1ba8479530ebe76c149cb532dd0b37ba420080193ae.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pst_column
  statement_id sha256:297250ae843997131559b777397296e4a906edbf7e016c834828a276476f7027.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.propagator_star_mul_self
  statement_id sha256:291ba961210b68cf2b42da1a752f3727b9881bc1ecafb5176c73f81b5f327da3.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.prod_eq_sq_of_rev
  statement_id sha256:a9933e2f666d4682cf6aa3ec73e446281823cb609903573832c6d1b6c17db3a2.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.reversal_columns
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.mul_prod_sub_eq_of_moments
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_pow_apply_column
  D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.sum_eval_div_nodal_eq_coeff
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over all m, all positive weights and all real potentials.
-/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.PathMiddleVertexMoments

open Matrix Polynomial Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer

section Reversal

variable {n : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian)

include hH in
/-- If the propagator at time `π` is the reversal permutation, then reversing an eigenvector
multiplies it by its phase `exp (i π λ)`. -/
private theorem eigenvector_rev
    (hR : ∀ i x : Fin (n + 1),
      NormedSpace.exp (((Real.pi : ℂ) * I) • H) x i = if x = i.rev then 1 else 0)
    (x k : Fin (n + 1)) :
    (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) x.rev k =
      (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) x k *
        Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k) := by
  have hUW : NormedSpace.exp (((Real.pi : ℂ) * I) • H) *
      (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
          diagonal (fun k => Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k)) := by
    rw [spectral_exp hH, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  have h := congrFun (congrFun hUW x) k
  rw [mul_apply, mul_diagonal, Finset.sum_eq_single x.rev] at h
  · rw [hR, if_pos (Fin.rev_rev x).symm, one_mul] at h
    exact h
  · intro l _ hl
    rw [hR, if_neg (fun h' => hl (by rw [h', Fin.rev_rev])), zero_mul]
  · simp

include hH in
/-- The phases `exp (i π λ)` of a Hermitian matrix sum to the trace of its propagator at time
`π`. -/
private theorem sum_phase_eq_trace :
    ∑ k, Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k) =
      (NormedSpace.exp (((Real.pi : ℂ) * I) • H)).trace := by
  rw [spectral_exp hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal]

end Reversal

section Weights

variable {m : ℕ} (r : Fin (2 * m) → ℝ) (q : Fin (2 * m + 1) → ℝ)

/-- Transfer with phase one from the last vertex to the first makes the propagator at time `π`
the reversal permutation and the weights mirror symmetric. -/
private theorem propagator_eq_reversal (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * m)) 0 = 1) :
    (∀ i x : Fin (2 * m + 1),
      NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) x i =
        if x = i.rev then 1 else 0) ∧ ∀ t : Fin (2 * m), r t = r t.rev := by
  have hH := pathHamiltonian_isHermitian r q
  have hpst : HasPST (pathHamiltonian r q) Real.pi (Fin.last (2 * m)) 0 := by
    unfold HasPST
    rw [hU, map_one]
  rw [hamiltonianPropagator_neg] at hU
  have hcol : ∀ x, NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) x 0 =
      if x = Fin.last (2 * m) then 1 else 0 := fun x => by
    rw [pst_column hH (Fin.last (2 * m)) 0 hpst x, hU]
  exact reversal_columns r q hr _ (propagator_star_mul_self hH)
    ((Commute.refl (pathHamiltonian r q)).smul_left ((Real.pi : ℂ) * I)).exp_left.eq 1
    (by simp) hcol

/-- **Mirror symmetry of the Hamiltonian.** A path Hamiltonian with positive weights and transfer
with phase one from the last vertex to the first at time `π` is invariant under the reversal of
the vertices. -/
theorem reversal_symmetric (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * m)) 0 = 1)
    (x y : Fin (2 * m + 1)) :
    pathHamiltonian r q x.rev y.rev = pathHamiltonian r q x y := by
  obtain ⟨hR, -⟩ := propagator_eq_reversal r q hr hU
  have hcomm : NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) * pathHamiltonian r q =
      pathHamiltonian r q * NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) :=
    ((Commute.refl (pathHamiltonian r q)).smul_left ((Real.pi : ℂ) * I)).exp_left.eq
  have h1 : (NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) * pathHamiltonian r q)
      x y.rev = pathHamiltonian r q x.rev y.rev := by
    rw [mul_apply, Finset.sum_eq_single x.rev]
    · rw [hR, if_pos (Fin.rev_rev x).symm, one_mul]
    · intro l _ hl
      rw [hR, if_neg (fun h' => hl (by rw [h', Fin.rev_rev])), zero_mul]
    · simp
  have h2 : (pathHamiltonian r q * NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q))
      x y.rev = pathHamiltonian r q x y := by
    rw [mul_apply, Finset.sum_eq_single y]
    · rw [hR, if_pos (Fin.rev_rev y).symm, mul_one]
    · intro l _ hl
      rw [hR, Fin.rev_rev, if_neg hl, mul_zero]
    · simp
  rw [← h1, ← h2, hcomm]

/-- **Middle-vertex spectral weights.** Let a path on `2m + 1` vertices with positive weights
have transfer with phase one from the last vertex to the first at time `π`. Then its eigenvalues
are distinct integers `z`, even on a class `A` of `m + 1` indices and odd off `A`; the
eigenvectors of the odd class vanish at the middle vertex `c`, and for `k ∈ A` the squared
modulus of the `k`-th eigenvector at `c` is
`∏_{l ∉ A} (z k - z l) / ∏_{l ∈ A, l ≠ k} (z k - z l)`. -/
theorem middle_vertex_weights (hH : (pathHamiltonian r q).IsHermitian) (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * m)) 0 = 1)
    (c : Fin (2 * m + 1)) (hc : (c : ℕ) = m) :
    ∃ (z : Fin (2 * m + 1) → ℤ) (A : Finset (Fin (2 * m + 1))),
      Function.Injective z ∧ A.card = m + 1 ∧ (∀ k ∈ A, Even (z k)) ∧
        (∀ k, k ∉ A → Odd (z k)) ∧ (∀ k, hH.eigenvalues k = z k) ∧
        (∀ k, k ∉ A →
          (hH.eigenvectorUnitary : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) c k = 0) ∧
        ∀ k ∈ A, Complex.normSq
            ((hH.eigenvectorUnitary : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) c k) =
          (∏ l ∈ Aᶜ, ((z k - z l : ℤ) : ℝ)) / ∏ l ∈ A.erase k, ((z k - z l : ℤ) : ℝ) := by
  classical
  obtain ⟨hR, hsymr⟩ := propagator_eq_reversal r q hr hU
  set W : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ := ↑hH.eigenvectorUnitary with hW
  set Λ := hH.eigenvalues with hΛ
  set E : Fin (2 * m + 1) → ℂ := fun k => Complex.exp ((Real.pi : ℂ) * I * Λ k) with hE
  have hrev : ∀ x k, W x.rev k = W x k * E k := fun x k => eigenvector_rev hH hR x k
  have hcrev : c.rev = c := Fin.ext (by rw [Fin.val_rev, hc]; omega)
  -- the phases are signs
  have hcolne : ∀ k, ∃ x, W x k ≠ 0 := by
    intro k
    by_contra hall
    push Not at hall
    have h := congrFun (congrFun (Unitary.coe_star_mul_self hH.eigenvectorUnitary) k) k
    rw [mul_apply, one_apply_eq] at h
    simp only [← hW, hall, mul_zero, Finset.sum_const_zero] at h
    exact zero_ne_one h
  have hE2 : ∀ k, E k * E k = 1 := by
    intro k
    obtain ⟨x, hx⟩ := hcolne k
    have h := hrev x.rev k
    rw [Fin.rev_rev, hrev x k, mul_assoc] at h
    exact (mul_left_cancel₀ hx (by rw [mul_one]; exact h)).symm
  set A : Finset (Fin (2 * m + 1)) := univ.filter (fun k => E k = 1) with hA
  have hEA : ∀ k ∈ A, E k = 1 := fun k hk => (Finset.mem_filter.mp hk).2
  have hEB : ∀ k, k ∉ A → E k = -1 := fun k hk =>
    (mul_self_eq_one_iff.mp (hE2 k)).resolve_left fun h =>
      hk (Finset.mem_filter.mpr ⟨mem_univ k, h⟩)
  have hz : ∀ k, ∃ n : ℤ, Λ k = n ∧ (k ∈ A → Even n) ∧ (k ∉ A → Odd n) := by
    intro k
    by_cases hk : k ∈ A
    · obtain ⟨n, hn⟩ := exists_int_of_exp_eq_one (hEA k hk)
      exact ⟨2 * n, by rw [hn]; push_cast; ring, fun _ => even_two_mul n, fun h => absurd hk h⟩
    · obtain ⟨n, hn⟩ := exists_int_of_exp_eq_neg_one (hEB k hk)
      exact ⟨2 * n + 1, by rw [hn]; push_cast; ring, fun h => absurd h hk,
        fun _ => odd_two_mul_add_one n⟩
  choose z hzΛ hzA hzB using hz
  -- the even class has `m + 1` elements: the trace of the reversal is one
  have htr : ∑ k, E k = 1 := by
    rw [hE, sum_phase_eq_trace hH, Matrix.trace]
    simp only [diag_apply, hR]
    rw [Finset.sum_eq_single c]
    · rw [if_pos hcrev.symm]
    · intro x _ hx
      rw [if_neg]
      intro h
      apply hx
      have h' := congrArg Fin.val h
      rw [Fin.val_rev] at h'
      exact Fin.ext (by omega)
    · simp
  have hcard : A.card = m + 1 := by
    have h2 : (A.card : ℂ) - (Aᶜ.card : ℂ) = 1 := by
      rw [← htr, ← Finset.sum_add_sum_compl A E, Finset.sum_congr rfl hEA,
        Finset.sum_congr rfl fun k hk => hEB k (Finset.mem_compl.mp hk)]
      simp [sub_eq_add_neg]
    have h3 : A.card + Aᶜ.card = 2 * m + 1 := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    have h4 : (A.card : ℤ) - Aᶜ.card = 1 := by exact_mod_cast h2
    omega
  -- the odd class vanishes at the middle vertex
  have hWc : ∀ k, k ∉ A → W c k = 0 := by
    intro k hk
    have h := hrev c k
    rw [hcrev, hEB k hk] at h
    linear_combination (1 / 2 : ℂ) * h
  -- the moments between the first vertex and the last and middle ones
  have hn2 : 2 * m = m + m := two_mul m
  set ρ : ℝ := ∏ i : Fin m, r (Fin.cast hn2.symm (Fin.castAdd m i)) with hρ
  have hρpos : 0 < ρ := Finset.prod_pos fun i _ => hr _
  have hPall : ∏ t, r t = ρ ^ 2 := prod_eq_sq_of_rev hn2 r hsymr
  have hmom1 : ∀ p ≤ 2 * m,
      (pathHamiltonian r q ^ p) (Fin.last (2 * m)) 0 =
        if p = 2 * m then ((ρ ^ 2 : ℝ) : ℂ) else 0 := by
    intro p hp
    split_ifs with hpm
    · rw [hpm, (pathHamiltonian_pow_apply_column r q 0 (2 * m) (Fin.last (2 * m))).2 (by simp),
        ← hPall]
      push_cast
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun t _ => ?_
      simp
    · exact (pathHamiltonian_pow_apply_column r q 0 p (Fin.last (2 * m))).1
        (Or.inl (by simp; omega))
  have hmom2 : ∀ p ≤ m, (pathHamiltonian r q ^ p) c 0 = if p = m then (ρ : ℂ) else 0 := by
    intro p hp
    split_ifs with hpm
    · rw [hpm, (pathHamiltonian_pow_apply_column r q 0 m c).2 (by simp [hc]), hρ]
      push_cast
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [dif_pos (by have := t.isLt; simp; omega)]
      congr 2
      ext
      simp
    · exact (pathHamiltonian_pow_apply_column r q 0 p c).1 (Or.inl (by simp [hc]; omega))
  have hM1 : ∀ k, W (Fin.last (2 * m)) k * starRingEnd ℂ (W 0 k) *
      ∏ l ∈ univ.erase k, ((Λ k : ℂ) - Λ l) = ((ρ ^ 2 : ℝ) : ℂ) := fun k =>
    mul_prod_sub_eq_of_moments univ (fun j => W (Fin.last (2 * m)) j * starRingEnd ℂ (W 0 j))
      (fun l => (Λ l : ℂ)) (2 * m) (by rw [Finset.card_univ, Fintype.card_fin]) _
      (fun p hp => by
        rw [← hmom1 p hp, spectral_pow_apply hH]
        exact Finset.sum_congr rfl fun j _ => by ring) k (mem_univ k)
  have hM2 : ∀ k ∈ A, W c k * starRingEnd ℂ (W 0 k) *
      ∏ l ∈ A.erase k, ((Λ k : ℂ) - Λ l) = (ρ : ℂ) := fun k hk =>
    mul_prod_sub_eq_of_moments A (fun j => W c j * starRingEnd ℂ (W 0 j))
      (fun l => (Λ l : ℂ)) m hcard _
      (fun p hp => by
        rw [← hmom2 p hp, spectral_pow_apply hH]
        symm
        rw [← Finset.sum_subset (Finset.subset_univ A)]
        · exact Finset.sum_congr rfl fun j _ => by ring
        · intro j _ hj
          rw [show (hH.eigenvectorUnitary : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) c j = 0
            from hWc j hj, zero_mul]) k hk
  have hΛinj : Function.Injective Λ := by
    intro k l hkl
    by_contra hne
    have h := hM1 k
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, mem_univ l⟩)
      (by rw [hkl, sub_self]), mul_zero] at h
    have h0 : (ρ ^ 2 : ℝ) = 0 := by exact_mod_cast h.symm
    exact (pow_pos hρpos 2).ne' h0
  have hzinj : Function.Injective z := fun k l hkl => hΛinj (by rw [hzΛ k, hzΛ l, hkl])
  refine ⟨z, A, hzinj, hcard, hzA, hzB, hzΛ, hWc, fun k hk => ?_⟩
  have hsplit : univ.erase k = A.erase k ∪ Aᶜ := by
    ext l
    by_cases h : l = k
    · subst h; simp [hk]
    · simp [h, em]
  have hdisj : Disjoint (A.erase k) Aᶜ := Finset.disjoint_left.mpr fun l h1 h2 =>
    (Finset.mem_compl.mp h2) (Finset.mem_of_mem_erase h1)
  set DA : ℝ := ∏ l ∈ A.erase k, (Λ k - Λ l) with hDA
  set DB : ℝ := ∏ l ∈ Aᶜ, (Λ k - Λ l) with hDB
  have hDAc : ∏ l ∈ A.erase k, ((Λ k : ℂ) - Λ l) = (DA : ℂ) := by
    rw [hDA]
    push_cast
    rfl
  have hDBc : ∏ l ∈ Aᶜ, ((Λ k : ℂ) - Λ l) = (DB : ℂ) := by
    rw [hDB]
    push_cast
    rfl
  have hlast : W (Fin.last (2 * m)) k = W 0 k := by
    have h := hrev 0 k
    rw [Fin.rev_zero, hEA k hk, mul_one] at h
    exact h
  have h1 := hM1 k
  rw [hsplit, Finset.prod_union hdisj, hDAc, hDBc, hlast, Complex.mul_conj] at h1
  have h1' : Complex.normSq (W 0 k) * (DA * DB) = ρ ^ 2 := by exact_mod_cast h1
  have h2 := congrArg Complex.normSq (hM2 k hk)
  rw [hDAc, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal,
    Complex.normSq_ofReal] at h2
  have h2' : Complex.normSq (W c k) * Complex.normSq (W 0 k) * DA ^ 2 = ρ ^ 2 := by
    linear_combination h2
  have hDA0 : DA ≠ 0 := fun h0 => (pow_pos hρpos 2).ne' (by rw [← h2', h0]; ring)
  have hn0 : Complex.normSq (W 0 k) ≠ 0 := fun h0 =>
    (pow_pos hρpos 2).ne' (by rw [← h1', h0]; ring)
  have key : Complex.normSq (W c k) * DA = DB :=
    mul_left_cancel₀ (mul_ne_zero hn0 hDA0) (by linear_combination h2' - h1')
  have hzD : ∀ l, ((z k - z l : ℤ) : ℝ) = Λ k - Λ l := fun l => by
    push_cast
    rw [hzΛ k, hzΛ l]
  simp only [hzD]
  rw [eq_div_iff hDA0]
  exact key

/-- **Integer middle-vertex moments with binomial parity.** Under the hypotheses of
`middle_vertex_weights`, the diagonal entries of the powers of the Hamiltonian at the middle
vertex `c` are integers `μ p`, and `μ p ≡ C(m, p)` modulo `2`. -/
theorem middle_vertex_moments (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * m)) 0 = 1)
    (c : Fin (2 * m + 1)) (hc : (c : ℕ) = m) :
    ∃ μ : ℕ → ℤ, (∀ p, (pathHamiltonian r q ^ p) c c = (μ p : ℂ)) ∧
      ∀ p, ((μ p : ℤ) : ZMod 2) = ((m.choose p : ℕ) : ZMod 2) := by
  have hH := pathHamiltonian_isHermitian r q
  obtain ⟨z, A, hzinj, hcard, hzA, hzB, hzΛ, hWc, hw⟩ := middle_vertex_weights r q hH hr hU c hc
  set PA : ℤ[X] := ∏ l ∈ A, (X - C (z l)) with hPA
  set PB : ℤ[X] := ∏ l ∈ Aᶜ, (X - C (z l)) with hPB
  refine ⟨fun p => ((X ^ p * PB) %ₘ PA).coeff m, fun p => ?_, fun p => ?_⟩
  · have hterm : ∀ k, (hH.eigenvectorUnitary : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) c k *
        ((hH.eigenvalues k : ℂ) ^ p * starRingEnd ℂ
          ((hH.eigenvectorUnitary : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) c k)) =
        if k ∈ A then (((X ^ p * PB).eval (z k) : ℤ) : ℂ) /
          ∏ l ∈ A.erase k, ((z k : ℂ) - z l) else 0 := by
      intro k
      split_ifs with hk
      · rw [mul_left_comm, Complex.mul_conj, hw k hk, hzΛ k, hPB]
        simp only [eval_mul, eval_pow, eval_X, eval_prod, eval_sub, eval_C]
        push_cast
        ring
      · rw [hWc k hk, zero_mul]
    rw [spectral_pow_apply hH, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_mem,
      Finset.univ_inter,
      ParityNodeDividedDifference.sum_eval_div_nodal_eq_coeff (K := ℂ) z A hzinj.injOn
        (X ^ p * PB), hcard]
    rfl
  · have hPAm : PA.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
    have hBcard : Aᶜ.card = m := by
      have h := Finset.card_add_card_compl A
      rw [Fintype.card_fin] at h
      omega
    have hmapA : PA.map (Int.castRingHom (ZMod 2)) = X ^ (m + 1) := by
      rw [hPA, Polynomial.map_prod, ← hcard, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Polynomial.map_sub, map_X, map_C, eq_intCast,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (by exact_mod_cast (hzA l hl).two_dvd), C_0,
        sub_zero]
    have hmapB : PB.map (Int.castRingHom (ZMod 2)) = (X + 1) ^ m := by
      rw [hPB, Polynomial.map_prod,
        show (X + 1 : (ZMod 2)[X]) ^ m = ∏ _l ∈ Aᶜ, (X + 1) by rw [Finset.prod_const, hBcard]]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Polynomial.map_sub, map_X, map_C, eq_intCast,
        (ZMod.intCast_eq_one_iff_odd).mpr (hzB l (Finset.mem_compl.mp hl)), C_1,
        CharTwo.sub_eq_add]
    have hrem : ∀ g : (ZMod 2)[X], (g %ₘ X ^ (m + 1)).coeff m = g.coeff m := by
      intro g
      have h := congrArg (fun f => f.coeff m) (modByMonic_add_div g (X ^ (m + 1)))
      simp only [coeff_add, coeff_X_pow_mul', if_neg (by omega : ¬ m + 1 ≤ m), add_zero] at h
      exact h
    change (((X ^ p * PB) %ₘ PA).coeff m : ZMod 2) = _
    rw [← eq_intCast (Int.castRingHom (ZMod 2)), ← coeff_map, map_modByMonic _ hPAm, hmapA,
      Polynomial.map_mul, Polynomial.map_pow, map_X, hmapB, hrem, coeff_X_pow_mul',
      coeff_X_add_one_pow]
    split_ifs with hp
    · rw [Nat.choose_symm hp]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp

end Weights

end D5.S3.Quantum.Dynamics.PathMiddleVertexMoments
