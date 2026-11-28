/- GID: D5/S3/Quantum/Information/MultiEntropy/ReplicaTorusTransfer
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reexpress the tripartite replica sum as the trace of a unitary compression power. -/

import D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Abel

/-!
The tripartite replica contraction as a trace of a row transfer power.
The CQ torus uses the bra-ket entry convention. Transposing its transfer
gives the usual density convention for the rectangular Gram factorization.
-/

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.ReplicaTorusTransfer

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse (shift)
open CQReplica (torus stateEquiv reducedAB densityAB densityA densityB blocks mergeAB mergeBC mergeAC)
open CQReplicaRegroupingSupplier (tensorOp)
open private E_eq_reducedAB_torus trace_word_eq_cycle_sum word_constant densityAB_apply
  E_two_eq_trace_density bipartiteDensity_mergeAB bipartiteDensity_mergeBC bipartiteDensity_mergeAC
  from D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining

noncomputable section

/-- Contract a row over the A labels, with its incoming and outgoing B labels fixed. -/
def rowTransfer {A B S : Type*} [Fintype A] [CommSemiring S]
    (n : ℕ) [NeZero n] (ρ : Matrix (A × B) (A × B) S) :
    Matrix (Fin n → B) (Fin n → B) S :=
  Matrix.of fun b d => ∑ a : Fin n → A, ∏ j : Fin n, ρ (a j, b j) (a (j + 1), d j)

theorem torus_eq_trace_rowTransfer_pow {A B S : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [CommSemiring S] (n : ℕ) [NeZero n]
    (ρ : Matrix (A × B) (A × B) S) :
    torus n ρ = Matrix.trace (rowTransfer n ρ ^ n) := by
  rw [← word_constant (rowTransfer n ρ) n,
    trace_word_eq_cycle_sum n (fun _ : Fin n => rowTransfer n ρ)]
  unfold torus rowTransfer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  symm
  simp only [Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable {L : Fin 3 → Type*}

/-- The forward row contraction in CQ's entry convention, transposed on the B strings. -/
def R [Fintype (L 0)] [Fintype (L 2)] (n : ℕ) [NeZero n]
    (ψ : ((i : Fin 3) → L i) → ℂ) : Matrix (Fin n → L 1) (Fin n → L 1) ℂ :=
  (rowTransfer n (reducedAB ψ)).transpose

theorem R_apply [Fintype (L 0)] [Fintype (L 2)] (n : ℕ) [NeZero n]
    (ψ : ((i : Fin 3) → L i) → ℂ) (b d : Fin n → L 1) :
    R n ψ b d = ∑ a : Fin n → L 0, ∏ j : Fin n,
      densityAB ψ (a (j + 1), b j) (a j, d j) := rfl

theorem E_eq_trace_R_pow [∀ i, Fintype (L i)] [DecidableEq (L 1)] (n : ℕ) [NeZero n]
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    E n 3 ψ = Matrix.trace (R n ψ ^ n) := by
  rw [E_eq_reducedAB_torus, torus_eq_trace_rowTransfer_pow, R, ← Matrix.transpose_pow,
    Matrix.trace_transpose]

/-- The constant C string coordinate is carried along while A labels advance by one. -/
def advanceA (n : ℕ) [NeZero n] :
    Equiv.Perm ((Fin n → L 2) × (Fin n → L 0)) where
  toFun p := (p.1, fun j => p.2 (j + 1))
  invFun p := (p.1, fun j => p.2 (j - 1))
  left_inv p := Prod.ext rfl (funext fun j => congrArg p.2 (sub_add_cancel j 1))
  right_inv p := Prod.ext rfl (funext fun j => congrArg p.2 (add_sub_cancel_right j 1))

/-- The cyclic shift on A strings. Its entry at (p,q) is one when p = advanceA n q. -/
def P (n : ℕ) [NeZero n] [DecidableEq (L 0)] [DecidableEq (L 2)] :
    Matrix ((Fin n → L 2) × (Fin n → L 0)) ((Fin n → L 2) × (Fin n → L 0)) ℂ :=
  Equiv.Perm.permMatrix ℂ (advanceA (L := L) n).symm

/-- The adjoints of the Kraus operators for the fixed C strings, stacked in one matrix. -/
def V (n : ℕ) (ψ : ((i : Fin 3) → L i) → ℂ) :
    Matrix ((Fin n → L 2) × (Fin n → L 0)) (Fin n → L 1) ℂ :=
  Matrix.of fun p b => ∏ j : Fin n, star (ψ (stateEquiv.symm ((p.2 j, b j), p.1 j)))

private theorem sum_V_entries [Fintype (L 0)] [Fintype (L 2)] (n : ℕ)
    (ψ : ((i : Fin 3) → L i) → ℂ) (f : (Fin n → L 0) → (Fin n → L 0))
    (b d : Fin n → L 1) :
    (∑ p : (Fin n → L 2) × (Fin n → L 0),
      star (V n ψ (p.1, f p.2) b) * V n ψ p d) =
      ∑ a : Fin n → L 0, ∏ j : Fin n, densityAB ψ (f a j, b j) (a j, d j) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [V, Matrix.of_apply, star_prod, star_star, ← Finset.prod_mul_distrib]
  simpa only [densityAB_apply] using
    (Fintype.prod_sum fun (j : Fin n) (c : L 2) =>
      ψ (stateEquiv.symm ((f a j, b j), c)) *
        star (ψ (stateEquiv.symm ((a j, d j), c)))).symm

theorem R_eq_V_conjTranspose_mul_P_mul_V [Fintype (L 0)] [Fintype (L 2)]
    [DecidableEq (L 0)] [DecidableEq (L 2)] (n : ℕ) [NeZero n]
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    R n ψ = (V n ψ)ᴴ * P (L := L) n * V n ψ := by
  symm
  unfold P Equiv.Perm.permMatrix
  rw [PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
  apply Matrix.ext
  intro b d
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id_eq, Matrix.conjTranspose_apply]
  exact (sum_V_entries n ψ (fun a j => a (j + 1)) b d).trans (R_apply n ψ b d).symm

theorem V_conjTranspose_mul_V_eq_tensorOp_densityB [Fintype (L 0)] [Fintype (L 1)] [Fintype (L 2)]
    (n : ℕ) (ψ : ((i : Fin 3) → L i) → ℂ) :
    (V n ψ)ᴴ * V n ψ = tensorOp (fun _ : Fin n => densityB ψ) := by
  classical
  apply Matrix.ext
  intro b d
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tensorOp, Matrix.of_apply]
  calc
    _ = ∑ a : Fin n → L 0, ∏ j : Fin n, densityAB ψ (a j, b j) (a j, d j) :=
      sum_V_entries n ψ id b d
    _ = _ := by
      simp only [densityB, Matrix.sum_apply, blocks]
      exact (Fintype.prod_sum fun (j : Fin n) (a : L 0) =>
        densityAB ψ (a, b j) (a, d j)).symm

section PartySwaps

/-- In the relabeled state, local coordinate i is the old party σ i. -/
def relabel (σ : Equiv.Perm (Fin 3)) (ψ : ((i : Fin 3) → L i) → ℂ)
    (x : (i : Fin 3) → L (σ i)) : ℂ :=
  ψ (Equiv.piCongrLeft L σ x)

variable [localFintype : ∀ i, Fintype (L i)]

private abbrev Grid (n : ℕ) := Fin 2 → ZMod n

/-- Reindex the conjugated amplitudes by the grid permutation and the other
amplitudes by that permutation followed by a single common translation. -/
private theorem E_relabel_of_grid (n : ℕ) [NeZero n] (σ : Equiv.Perm (Fin 3))
    (g t : Equiv.Perm (Grid n))
    (h : ∀ i r, g (shift n 3 i r) = shift n 3 (σ i) (t (g r)))
    (ψ : ((i : Fin 3) → L i) → ℂ) :
    @E n 3 _ (fun i => L (σ i)) (fun i => localFintype (σ i)) (relabel σ ψ) =
      E n 3 ψ := by
  classical
  let e := Equiv.arrowCongr g (Equiv.piCongrLeft L σ)
  unfold E
  apply Fintype.sum_equiv e _ _
  intro x
  let y := e x
  have hy (r : Grid n) : y (g r) = Equiv.piCongrLeft L σ (x r) := by
    change Equiv.piCongrLeft L σ (x (g.symm (g r))) = _
    rw [g.symm_apply_apply]
  have hψ (r : Grid n) :
      Equiv.piCongrLeft L σ (fun i => x (shift n 3 i r) i) =
        (fun j => y (shift n 3 j (t (g r))) j) := by
    apply (Equiv.piCongrLeft L σ).symm.injective
    rw [Equiv.symm_apply_apply]
    funext i
    rw [Equiv.piCongrLeft_symm_apply]
    change x (shift n 3 i r) i = y (shift n 3 (σ i) (t (g r))) (σ i)
    rw [← h i r, hy, Equiv.piCongrLeft_apply_apply]
  simp only [Finset.prod_mul_distrib, relabel]
  apply congrArg₂ (· * ·)
  · exact Fintype.prod_equiv g _ _ (fun r => congrArg (fun z => star (ψ z)) (hy r).symm)
  · exact Fintype.prod_equiv (g.trans t) _ _ (fun r => congrArg ψ (hψ r))

private def swapGrid (n : ℕ) : Equiv.Perm (Grid n) where
  toFun r := ![r 1, r 0]
  invFun r := ![r 1, r 0]
  left_inv r := by funext j; fin_cases j <;> rfl
  right_inv r := by funext j; fin_cases j <;> rfl

private def shearAC (n : ℕ) : Equiv.Perm (Grid n) where
  toFun r := ![-r 0 - r 1, r 1]
  invFun r := ![-r 0 - r 1, r 1]
  left_inv r := by funext j; fin_cases j <;> simp [Fin.isValue] <;> abel
  right_inv r := by funext j; fin_cases j <;> simp [Fin.isValue] <;> abel

private def shearBC (n : ℕ) : Equiv.Perm (Grid n) where
  toFun r := ![r 0, -r 0 - r 1]
  invFun r := ![r 0, -r 0 - r 1]
  left_inv r := by funext j; fin_cases j <;> simp [Fin.isValue] <;> abel
  right_inv r := by funext j; fin_cases j <;> simp [Fin.isValue] <;> abel

/-- Swapping the two shifted parties is a transposition of the grid axes. -/
theorem E_swap_AB (n : ℕ) [NeZero n] (ψ : ((i : Fin 3) → L i) → ℂ) :
    @E n 3 _ (fun i => L (Equiv.swap 0 1 i)) (fun i => localFintype (Equiv.swap 0 1 i))
      (relabel (Equiv.swap 0 1) ψ) = E n 3 ψ := by
  refine E_relabel_of_grid n (Equiv.swap 0 1) (swapGrid n) (Equiv.refl _) ?_ ψ
  intro i r
  funext j
  fin_cases i <;> fin_cases j <;> rfl

/-- Swapping A with unshifted C uses (u,v) ↦ (-u-v,v) and translation by (-1,0). -/
theorem E_swap_AC (n : ℕ) [NeZero n] (ψ : ((i : Fin 3) → L i) → ℂ) :
    @E n 3 _ (fun i => L (Equiv.swap 0 2 i)) (fun i => localFintype (Equiv.swap 0 2 i))
      (relabel (Equiv.swap 0 2) ψ) = E n 3 ψ := by
  refine E_relabel_of_grid n (Equiv.swap 0 2) (shearAC n)
    (Equiv.addRight (![-1, 0] : Grid n)) ?_ ψ
  intro i r
  funext j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide)
      [shearAC, shift, Equiv.swap_apply_def, Equiv.coe_addRight, Pi.add_apply,
        Fin.isValue] <;> abel

/-- Swapping B with unshifted C uses (u,v) ↦ (u,-u-v) and translation by (0,-1). -/
theorem E_swap_BC (n : ℕ) [NeZero n] (ψ : ((i : Fin 3) → L i) → ℂ) :
    @E n 3 _ (fun i => L (Equiv.swap 1 2 i)) (fun i => localFintype (Equiv.swap 1 2 i))
      (relabel (Equiv.swap 1 2) ψ) = E n 3 ψ := by
  refine E_relabel_of_grid n (Equiv.swap 1 2) (shearBC n)
    (Equiv.addRight (![0, -1] : Grid n)) ?_ ψ
  intro i r
  funext j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide)
      [shearBC, shift, Equiv.swap_apply_def, Equiv.coe_addRight, Pi.add_apply,
        Fin.isValue] <;> abel

end PartySwaps

/-- The bipartite moments on the three merger right-hand sides of Eq. (1.13). -/
theorem E_merge_trace_moments [∀ i, Fintype (L i)] [DecidableEq (L 0)] [DecidableEq (L 1)]
    (n : ℕ) [NeZero n] (ψ : ((i : Fin 3) → L i) → ℂ) :
    E n 2 (mergeAB ψ) = Matrix.trace (densityAB ψ ^ n) ∧
    E n 2 (mergeBC ψ) = Matrix.trace (densityA ψ ^ n) ∧
    E n 2 (mergeAC ψ) = Matrix.trace (densityB ψ ^ n) := by
  rw [@E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 0 × L 1))) (mergeAB ψ),
    @E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 0))) (mergeBC ψ),
    @E_two_eq_trace_density n _ _ _ (inferInstanceAs (DecidableEq (L 1))) (mergeAC ψ),
    bipartiteDensity_mergeAB, bipartiteDensity_mergeBC, bipartiteDensity_mergeAC]
  exact ⟨rfl, rfl, rfl⟩

end

end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.ReplicaTorusTransfer
