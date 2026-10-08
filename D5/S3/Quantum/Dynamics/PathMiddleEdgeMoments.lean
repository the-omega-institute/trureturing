/- GID: D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PathMiddleEdgeMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Middle-edge weights and integer moments of even paths with end transfer at time pi. -/

/-
proof_shape: middle_edge_weights: content; escape_witness: the public conclusion itself (form 2;
the preregistered middle-edge weight formula of research line #14293, node 3): on a path with
2k + 2 vertices the even spectral class A has k + 1 indices, the eigenvectors of the odd class
are antisymmetric at the two middle vertices a, b, and for j in A
|W a j + W b j|^2 = ∏_{l ∉ A} (z j - z l) / (ρ * ∏_{l ∈ A, l ≠ j} (z j - z l)) with ρ the weight
of the middle edge. It is produced by
D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.reversal_sign_classes, the trace count of a
reversal without fixed vertex, the splitting of the product of the weights of a mirror-symmetric
path with an odd number of edges, and a nodal extraction over the class A from the moments
between the first vertex and the two middle ones; no Mathlib or frozen declaration states it.
consumer: middle_edge_moments.
proof_shape: middle_edge_moments: content; escape_witness: the public conclusion itself (form 2; the
integrality part of the preregistered witness on the middle-edge moments): ρ times the moment of H^p
at the vector e_a + e_b is the integer [X^k] ((X^p * P_B) mod P_A), by the weight formula and the
Lagrange coefficient formula over the class A. consumer:
D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer (private step no_phase_one_transfer).
proof_shape: middle_edge_gram: bind-only (the Gram identity S 0 * S 2 - S 1 ^ 2 = 4 * r' ^ 2 of the
preregistered witness on the middle-edge moments, for a reversal-invariant path Hamiltonian with r'
the weight of the edge following the middle edge: every atomic fact is an instance of
pathHamiltonian_pow_apply_column at p = 1, of pathHamiltonian_transpose or of the invariance
hypothesis, and the rest is a finite-sum expansion and ring); consumer:
D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer (private step no_phase_one_transfer). It
provides no escape content: the escape witnesses of this module are middle_edge_weights and
middle_edge_moments.
Definitions: pairMoment (the moment of H ^ p at the sum of two basis vectors) and nodalMoment
(the coefficient of degree k of the remainder of X ^ p * P_B modulo P_A); consumers:
middle_edge_moments, middle_edge_gram and
D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.nodalMoment_det_mod_four.
Private helper:
proof_shape: pairMoment_eq_sum: bind-only (spectral form of the four entries); consumer:
middle_edge_moments.
admission_basis: escape-witness (research line #14293, node 3; partial progress on the rational
weights conjecture of arXiv:1708.03283: together with
D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer the conjecture is settled for n = 2m
vertices with m = 2 (mod 4) or m = 3, 5 (mod 8); it remains open for n = 0 (mod 8) and
n = 2, 14 (mod 16)).
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian
  statement_id sha256:2a698170a16b6888380fcc8f26eb4e7fe06d99129518c7579da37d4ef440257a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_isHermitian
  statement_id sha256:9ef82c6c2002677d2d5ca2cbbbca0f264c96cd4b9b9c894ea79af8bb10c65c8a.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_transpose
  statement_id sha256:6f605b6c72a712566fde18c5c7b05e5facf4368fdfc76d91c7e873a3bdac528b.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.spectral_pow_apply
  statement_id sha256:bc267ee8eeb16ff3b700510e62512f2a1aeb87b304d7dfa6dcd66409ae1144d7.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.prod_eq_sq_of_rev
  statement_id sha256:d04d190c835f6b795ac49dbe9b3816f27479dd678df1c421eca52fa99ccfc404.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.mul_prod_sub_eq_of_moments
  statement_id sha256:ed8a52c9d0c42c524e25b41cea86b79c9c99940c454f28b51528bba26bc369e9.
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.pathHamiltonian_pow_apply_column
  statement_id sha256:c50a132afc123692c13936889ad692366e6fb904fc589bc86bbf43f70e60e980.
  D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.sum_eval_div_nodal_eq_coeff
  statement_id sha256:1299d2cac32c96924333faa7cf62248f785306485913813ee846eef3f944d175.
Same-delivery dependency:
  D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.propagator_eq_reversal
  D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.reversal_sign_classes
  D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.normSq_eq_div_of_nodal
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over all k, all positive weights and all real potentials.
-/

import D5.S3.Quantum.Dynamics.PathMiddleVertexMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.PathMiddleEdgeMoments

open Matrix Polynomial Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.PathMiddleVertexMoments

/-- The moment `⟨f, H ^ p f⟩` of a matrix `H` at the vector `f = e_a + e_b`: the sum of the four
entries of `H ^ p` at the indices `a` and `b`. -/
def pairMoment {V : Type*} [Fintype V] [DecidableEq V] (H : Matrix V V ℂ) (a b : V) (p : ℕ) : ℂ :=
  (H ^ p) a a + (H ^ p) a b + (H ^ p) b a + (H ^ p) b b

/-- The nodal moment of order `p` of integer nodes `z` on `A` against the nodes on `B`: the
coefficient of degree `k` of the remainder of `X ^ p * ∏_{l ∈ B} (X - z l)` modulo
`∏_{l ∈ A} (X - z l)`. -/
def nodalMoment {ι : Type*} (z : ι → ℤ) (A B : Finset ι) (k p : ℕ) : ℤ :=
  ((X ^ p * ∏ l ∈ B, (X - C (z l))) %ₘ ∏ l ∈ A, (X - C (z l))).coeff k

/-- The moment of a Hermitian matrix at `e_a + e_b` in its orthonormal eigenbasis. -/
private theorem pairMoment_eq_sum {V : Type*} [Fintype V] [DecidableEq V] {H : Matrix V V ℂ}
    (hH : H.IsHermitian) (a b : V) (p : ℕ) :
    pairMoment H a b p = ∑ j, (hH.eigenvalues j : ℂ) ^ p *
      (Complex.normSq ((hH.eigenvectorUnitary : Matrix V V ℂ) a j +
        (hH.eigenvectorUnitary : Matrix V V ℂ) b j) : ℂ) := by
  unfold pairMoment
  rw [spectral_pow_apply hH p a a, spectral_pow_apply hH p a b, spectral_pow_apply hH p b a,
    spectral_pow_apply hH p b b, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj, map_add]
  ring

section Weights

variable {k : ℕ} (r : Fin (2 * k + 1) → ℝ) (q : Fin (2 * k + 1 + 1) → ℝ)

/-- **Middle-edge spectral weights.** Let a path on `2k + 2` vertices with positive weights have
transfer with phase one from the last vertex to the first at time `π`, and let `a`, `b` be the
ends of its middle edge `e`. Then its eigenvalues are distinct integers `z`, even on a class `A`
of `k + 1` indices and odd off `A`; the eigenvectors of the odd class have opposite entries at
`a` and `b`, and for `j ∈ A` the squared modulus of the sum of the entries of the `j`-th
eigenvector at `a` and `b` is
`∏_{l ∉ A} (z j - z l) / (r e * ∏_{l ∈ A, l ≠ j} (z j - z l))`. -/
theorem middle_edge_weights (hH : (pathHamiltonian r q).IsHermitian) (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * k + 1)) 0 = 1)
    (a b : Fin (2 * k + 1 + 1)) (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1)
    (e : Fin (2 * k + 1)) (he : (e : ℕ) = k) :
    ∃ (z : Fin (2 * k + 1 + 1) → ℤ) (A : Finset (Fin (2 * k + 1 + 1))),
      Function.Injective z ∧ A.card = k + 1 ∧ (∀ j ∈ A, Even (z j)) ∧
        (∀ j, j ∉ A → Odd (z j)) ∧ (∀ j, hH.eigenvalues j = z j) ∧
        (∀ j, j ∉ A →
          (hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) a j +
            (hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) b j =
              0) ∧
        ∀ j ∈ A, Complex.normSq
            ((hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) a j +
              (hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) b j) =
          (∏ l ∈ Aᶜ, ((z j - z l : ℤ) : ℝ)) /
            (r e * ∏ l ∈ A.erase j, ((z j - z l : ℤ) : ℝ)) := by
  classical
  obtain ⟨z, A, hzinj, hzA, hzB, hzΛ, -, hrevB, hcount, hfirst⟩ :=
    reversal_sign_classes r q hH hr hU
  obtain ⟨-, hsymr⟩ := propagator_eq_reversal r q hr hU
  set W : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ := ↑hH.eigenvectorUnitary with hW
  have harev : a.rev = b := Fin.ext (by rw [Fin.val_rev, ha, hb]; omega)
  -- the two classes have `k + 1` elements: the reversal has no fixed vertex
  have hfix : (univ.filter fun x : Fin (2 * k + 1 + 1) => x = x.rev) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun x _ h => ?_
    have h' := congrArg Fin.val h
    rw [Fin.val_rev] at h'
    omega
  have hcard : A.card = k + 1 := by
    have h3 := Finset.card_add_card_compl A
    rw [Fintype.card_fin] at h3
    rw [hfix, Finset.card_empty] at hcount
    omega
  -- the odd class is antisymmetric at the middle edge
  have hF0 : ∀ j, j ∉ A → W a j + W b j = 0 := by
    intro j hj
    have h := hrevB a j hj
    rw [harev] at h
    rw [h, add_neg_cancel]
  -- the product of the weights: the middle weight times a square
  have hn2 : 2 * k = k + k := two_mul k
  have herev : e.rev = e := Fin.ext (by rw [Fin.val_rev, he]; omega)
  have hgrev : ∀ t : Fin (2 * k), r (e.succAbove t) = r (e.succAbove t.rev) := by
    intro t
    rw [hsymr (e.succAbove t), Fin.rev_succAbove, herev]
  have hPall : ∏ t, r t =
      r e * (∏ i : Fin k, r (e.succAbove (Fin.cast hn2.symm (Fin.castAdd k i)))) ^ 2 := by
    rw [Fin.prod_univ_succAbove r e, prod_eq_sq_of_rev hn2 (fun t => r (e.succAbove t)) hgrev]
  set Q : ℝ := ∏ i : Fin k, r (e.succAbove (Fin.cast hn2.symm (Fin.castAdd k i))) with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun i _ => hr _
  -- the moments between the first vertex and the two middle ones
  have hmom2 : ∀ p ≤ k, (pathHamiltonian r q ^ p) a 0 + (pathHamiltonian r q ^ p) b 0 =
      if p = k then (Q : ℂ) else 0 := by
    intro p hp
    rw [(pathHamiltonian_pow_apply_column r q 0 p b).1 (Or.inl (by simp [hb]; omega)), add_zero]
    split_ifs with hpk
    · rw [hpk, (pathHamiltonian_pow_apply_column r q 0 k a).2 (by simp [ha]), hQ]
      push_cast
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun t _ => ?_
      have hlt : (Fin.cast hn2.symm (Fin.castAdd k t)).castSucc < e := by
        simp [Fin.lt_def, he]
      rw [dif_pos (by have := t.isLt; simp; omega), Fin.succAbove_of_castSucc_lt e _ hlt]
      congr 2
      ext
      simp
    · exact (pathHamiltonian_pow_apply_column r q 0 p a).1 (Or.inl (by simp [ha]; omega))
  have hM2 : ∀ j ∈ A, (W a j + W b j) * starRingEnd ℂ (W 0 j) *
      ∏ l ∈ A.erase j, ((hH.eigenvalues j : ℂ) - hH.eigenvalues l) = (Q : ℂ) := fun j hj =>
    mul_prod_sub_eq_of_moments A (fun i => (W a i + W b i) * starRingEnd ℂ (W 0 i))
      (fun l => (hH.eigenvalues l : ℂ)) k hcard _
      (fun p hp => by
        rw [← hmom2 p hp, spectral_pow_apply hH, spectral_pow_apply hH, ← Finset.sum_add_distrib,
          ← hW]
        symm
        rw [← Finset.sum_subset (Finset.subset_univ A)]
        · exact Finset.sum_congr rfl fun i _ => by ring
        · intro i _ hi
          rw [← add_mul, hF0 i hi, zero_mul]) j hj
  refine ⟨z, A, hzinj, hcard, hzA, hzB, hzΛ, hF0, fun j hj => ?_⟩
  exact normSq_eq_div_of_nodal hzΛ A j (hr e).ne' hQpos.ne'
    (by rw [← hPall]; exact hfirst j hj) (hM2 j hj)

/-- **Integer middle-edge moments.** Under the hypotheses of `middle_edge_weights`, the weight of
the middle edge times the moment of `H ^ p` at `e_a + e_b` is the nodal moment of order `p` of
the even spectral class against the odd one, both of `k + 1` integer eigenvalues. -/
theorem middle_edge_moments (hr : ∀ t, 0 < r t)
    (hU : hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * k + 1)) 0 = 1)
    (a b : Fin (2 * k + 1 + 1)) (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1)
    (e : Fin (2 * k + 1)) (he : (e : ℕ) = k) :
    ∃ (z : Fin (2 * k + 1 + 1) → ℤ) (A : Finset (Fin (2 * k + 1 + 1))),
      A.card = k + 1 ∧ Aᶜ.card = k + 1 ∧ (∀ j ∈ A, Even (z j)) ∧ (∀ j ∈ Aᶜ, Odd (z j)) ∧
        ∀ p : ℕ, (r e : ℂ) * pairMoment (pathHamiltonian r q) a b p =
          ((nodalMoment z A Aᶜ k p : ℤ) : ℂ) := by
  have hH := pathHamiltonian_isHermitian r q
  obtain ⟨z, A, hzinj, hcard, hzA, hzB, hzΛ, hF0, hw⟩ :=
    middle_edge_weights r q hH hr hU a b ha hb e he
  have hBcard : Aᶜ.card = k + 1 := by
    have h := Finset.card_add_card_compl A
    rw [Fintype.card_fin] at h
    omega
  refine ⟨z, A, hcard, hBcard, hzA, fun j hj => hzB j (Finset.mem_compl.mp hj), fun p => ?_⟩
  set PB : ℤ[X] := ∏ l ∈ Aᶜ, (X - C (z l)) with hPB
  have hterm : ∀ j, (r e : ℂ) * ((hH.eigenvalues j : ℂ) ^ p *
      (Complex.normSq
        ((hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) a j +
          (hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) b j) :
            ℂ)) =
      if j ∈ A then (((X ^ p * PB).eval (z j) : ℤ) : ℂ) /
        ∏ l ∈ A.erase j, ((z j : ℂ) - z l) else 0 := by
    intro j
    split_ifs with hj
    · have hw2 : r e * Complex.normSq
          ((hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) a j +
            (hH.eigenvectorUnitary : Matrix (Fin (2 * k + 1 + 1)) (Fin (2 * k + 1 + 1)) ℂ) b j) =
          (∏ l ∈ Aᶜ, ((z j - z l : ℤ) : ℝ)) / ∏ l ∈ A.erase j, ((z j - z l : ℤ) : ℝ) := by
        rw [hw j hj, ← mul_div_assoc, mul_div_mul_left _ _ (hr e).ne']
      rw [mul_left_comm, ← Complex.ofReal_mul, hw2, hzΛ j, hPB]
      simp only [eval_mul, eval_pow, eval_X, eval_prod, eval_sub, eval_C]
      push_cast
      ring
    · rw [hF0 j hj, map_zero, Complex.ofReal_zero, mul_zero, mul_zero]
  rw [pairMoment_eq_sum hH a b p, Finset.mul_sum, Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_mem, Finset.univ_inter,
    ParityNodeDividedDifference.sum_eval_div_nodal_eq_coeff (K := ℂ) z A hzinj.injOn
      (X ^ p * PB), hcard]
  rfl

/-- **Gram identity of the middle-edge moments.** For a reversal-invariant path Hamiltonian on
`2k + 2` vertices, with `a`, `b` the ends of the middle edge and `f` the edge following it, the
moments `S p` at `e_a + e_b` satisfy `S 0 * S 2 - S 1 ^ 2 = 4 * r f ^ 2`. -/
theorem middle_edge_gram
    (hsym : ∀ x y : Fin (2 * k + 1 + 1),
      pathHamiltonian r q x.rev y.rev = pathHamiltonian r q x y)
    (a b : Fin (2 * k + 1 + 1)) (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1)
    (f : Fin (2 * k + 1)) (hf : (f : ℕ) = k + 1) :
    pairMoment (pathHamiltonian r q) a b 0 * pairMoment (pathHamiltonian r q) a b 2 -
      pairMoment (pathHamiltonian r q) a b 1 ^ 2 = 4 * (r f : ℂ) ^ 2 := by
  have hk : k + 1 < 2 * k + 1 := by have := f.isLt; omega
  have hab : a ≠ b := Fin.ne_of_val_ne (by omega)
  have harev : a.rev = b := Fin.ext (by rw [Fin.val_rev, ha, hb]; omega)
  have hbrev : b.rev = a := by rw [← harev, Fin.rev_rev]
  have hT : ∀ x y, pathHamiltonian r q x y = pathHamiltonian r q y x := fun x y => by
    have h := congrFun (congrFun (pathHamiltonian_transpose r q) y) x
    rwa [transpose_apply] at h
  -- the column of `H` at `e_a + e_b`
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * k + 1 + 1) → ℂ,
      ∀ x, v x = pathHamiltonian r q x a + pathHamiltonian r q x b := ⟨_, fun _ => rfl⟩
  have hvrev : ∀ x, v x.rev = v x := by
    intro x
    rw [hv, hv, ← hsym x.rev a, ← hsym x.rev b, Fin.rev_rev, harev, hbrev]
    exact add_comm _ _
  have hfar : ∀ x : Fin (2 * k + 1 + 1), ((x : ℕ) + 1 < k ∨ k + 2 < (x : ℕ)) → v x = 0 := by
    intro x hx
    have h1 := (pathHamiltonian_pow_apply_column r q a 1 x).1 (by omega)
    have h2 := (pathHamiltonian_pow_apply_column r q b 1 x).1 (by omega)
    rw [pow_one] at h1 h2
    rw [hv, h1, h2, add_zero]
  set w : Fin (2 * k + 1 + 1) := ⟨k + 2, by omega⟩ with hw
  have hwv : (w : ℕ) = k + 2 := rfl
  have huv : (w.rev : ℕ) + 1 = k := by rw [Fin.val_rev, hwv]; omega
  have hvw : v w = (r f : ℂ) := by
    have h1 := (pathHamiltonian_pow_apply_column r q a 1 w).1 (Or.inl (by omega))
    have h2 := (pathHamiltonian_pow_apply_column r q b 1 w).2 (by omega)
    rw [pow_one] at h1 h2
    rw [hv, h1, h2, zero_add, Finset.prod_range_one, dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp [hb, hf])
  have hvb : v b = v a := by rw [← harev]; exact hvrev a
  -- the three moments
  have h0 : pairMoment (pathHamiltonian r q) a b 0 = 2 := by
    simp only [pairMoment, pow_zero, one_apply_eq, one_apply_ne hab, one_apply_ne hab.symm]
    norm_num
  have h1 : pairMoment (pathHamiltonian r q) a b 1 = 2 * v a := by
    have hsum : pairMoment (pathHamiltonian r q) a b 1 = v a + v b := by
      simp only [pairMoment, pow_one]
      rw [hv, hv]
      ring
    rw [hsum, hvb]
    ring
  have h2 : pairMoment (pathHamiltonian r q) a b 2 = ∑ x, v x ^ 2 := by
    simp only [pairMoment, pow_two, mul_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hv, hT a x, hT b x]
    ring
  have hsum : ∑ x, v x ^ 2 = v w.rev ^ 2 + (v a ^ 2 + (v b ^ 2 + v w ^ 2)) := by
    have hbw : b ≠ w := Fin.ne_of_val_ne (by omega)
    have haS : a ∉ ({b, w} : Finset (Fin (2 * k + 1 + 1))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega)⟩
    have huS : w.rev ∉ ({a, b, w} : Finset (Fin (2 * k + 1 + 1))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega),
        Fin.ne_of_val_ne (by omega)⟩
    have hzero : ∀ x ∈ (univ : Finset (Fin (2 * k + 1 + 1))),
        x ∉ ({w.rev, a, b, w} : Finset (Fin (2 * k + 1 + 1))) → v x ^ 2 = 0 := by
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      have hx1' := Fin.val_ne_of_ne hx1
      have hx2' := Fin.val_ne_of_ne hx2
      have hx3' := Fin.val_ne_of_ne hx3
      have hx4' := Fin.val_ne_of_ne hx4
      rw [hfar x (by omega)]
      ring
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_insert huS,
      Finset.sum_insert haS, Finset.sum_pair hbw]
  rw [h0, h1, h2, hsum, hvrev w, hvb, hvw]
  ring

end Weights

end D5.S3.Quantum.Dynamics.PathMiddleEdgeMoments
