/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenTransferExpansion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The eight-vertex transfer matrix has its central factorial expansion. -/
/-
admission_basis: open-problem-resolution (#19637; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19685.
Direct frozen dependencies: GVHunter.reverse_word_list (private declaration statement_id at base):
sha256:1e86b762f1ae2fa842520355cc6ac96d2996fa5d73a455e825a50299d8c83f60.
D5/S3/Estimation/DataProcessing/OneCutZeroExcess.internalFailures declaration statement_id:
sha256:ff484d19a4879db458214e0baff96b385787dd14891e0b80cb30482e80a35b40.
Unfrozen dependency Matrix.traceRight in D5/S3/Quantum/Foundation/FiniteDensityPurification is not imported;
the auxiliary trace uses the pinned Fin.snoc and finite-sum expression directly.
The source uses tensor basis indices Fin N → Fin 2; all operator products retain the stated order.
Rcoef: proof_shape: bind-only; consumer: twoSite, Rcoef_swap, Rcoef_decomposition, twoSite_swap, twoSite_factor. | Kcoef: proof_shape: bind-only; consumer: oneSite, oneSite_eq_one.
twoSite: proof_shape: bind-only; consumer: preTrace, twoSite_swap, twoSite_factor, twoSite_flip_covariance, twoSite_square, twoSite_quad_covariance, operatorWord, operatorWord_cons, operatorWord_cons_cons, operatorWord_eq_path, preTrace_eq_path. | oneSite: proof_shape: bind-only; consumer: preTrace, oneSite_eq_one, preTrace_eq_path.
preTrace: proof_shape: bind-only; consumer: transfer, preTrace_eq_path, transfer_product. | transfer: proof_shape: bind-only; consumer: claim, transfer_product, transfer_walsh, claim_of_spectral_obligations.
hamiltonian: proof_shape: bind-only; consumer: claim, hamiltonian_eq_sum_flip, hamiltonian_walsh, claim_of_spectral_obligations. | claim: proof_shape: bind-only; consumer: claim_of_spectral_obligations, claim_of_scalar_identity, result.
oneSite_eq_one: proof_shape: bind-only; consumer: preTrace_eq_path. | Rcoef_swap: proof_shape: bind-only; consumer: twoSite_swap.
Rcoef_decomposition: proof_shape: bind-only; consumer: twoSite_factor. | twoSite_swap: proof_shape: bind-only; consumer: preTrace_eq_path.
bitSign: proof_shape: bind-only; consumer: bitChar, bitChar_orthogonal, bitChar_rev, flipEigenvalue, flipOp_walsh, bitSign_mul, flipEigenvalue_pair. | bitChar: proof_shape: bind-only; consumer: walsh, bitChar_orthogonal, walsh_square, bitChar_rev, flipOp_walsh.
walsh: proof_shape: bind-only; consumer: walsh_square, flipOp_walsh, quadOp_walsh, adjacentQuad_walsh, transfer_walsh, hamiltonian_walsh, walsh_right_cancel, claim_of_spectral_obligations. | bitChar_orthogonal: proof_shape: bind-only; consumer: walsh_square.
walsh_square: proof_shape: bind-only; consumer: walsh_right_cancel. | bitChar_rev: proof_shape: bind-only; consumer: flipOp_walsh.
flipEquiv: proof_shape: bind-only; consumer: flipEquiv_apply, flipOp_walsh, twoSite_factor, flipOp_comm, flipOp_square, swap_flip_pair_general, flipOp_apply, auxTrace_lift_mul_flip.
flipEquiv_apply: proof_shape: bind-only; consumer: twoSite_factor, flipOp_comm, flipOp_square, swap_flip_pair_general, flipOp_apply.
flipEigenvalue: proof_shape: bind-only; consumer: flipOp_walsh, adjacentValue, quadOp_walsh, adjacentQuad_walsh, adjacentValue_ofFn, flipEigenvalue_pair, adjacentValue_product_closed, transfer_walsh, hEigenvalue, hamiltonian_walsh, hEigenvalue_succ. | flipOp_walsh: proof_shape: bind-only; consumer: quadOp_walsh, hamiltonian_walsh.
rev_eq_iff_ne: proof_shape: bind-only; consumer: flipConfig_pair_eq_iff. | flipConfig_pair_eq_iff: proof_shape: bind-only; consumer: hamiltonian_eq_sum_flip.
flipConfig_swap_eq_iff: proof_shape: bind-only; consumer: twoSite_factor. | twoSite_factor: proof_shape: bind-only; consumer: twoSite_flip_covariance, twoSite_square.
equivMatrix_apply: proof_shape: bind-only; consumer: flipOp_comm, flipOp_square, swapOp_square, swap_flip_pair_general, flipOp_apply. | flipConfig_comm: proof_shape: bind-only; consumer: flipOp_comm.
flipConfig_involutive: proof_shape: bind-only; consumer: flipOp_square. | flipOp_comm: proof_shape: bind-only; consumer: twoSite_flip_covariance.
flipOp_square: proof_shape: bind-only; consumer: twoSite_square. | swapOp_square: proof_shape: bind-only; consumer: twoSite_square.
swap_flip_pair_general: proof_shape: bind-only; consumer: swap_flip_comm, twoSite_flip_covariance. | swap_flip_comm: proof_shape: bind-only; consumer: twoSite_square.
quadOp: proof_shape: bind-only; consumer: twoSite_square, twoSite_quad_covariance, pathQuad, operatorWord_cons, operatorWord_cons_cons, operatorWord_eq_path, auxTrace_lift_mul_quad, auxLift_quad_pair, adjacentQuad, pathQuad_eq_adjacentQuad_last, auxLift_adjacentQuad, transfer_product, quadOp_walsh, adjacentQuad_walsh. | twoSite_flip_covariance: proof_shape: bind-only; consumer: twoSite_quad_covariance.
twoSite_square: proof_shape: bind-only; consumer: operatorWord_cons, operatorWord_eq_path. | twoSite_quad_covariance: proof_shape: bind-only; consumer: operatorWord_cons_cons, operatorWord_eq_path.
flipOp_apply: proof_shape: bind-only; consumer: auxLift_flip_pair, hamiltonian_eq_sum_flip. | operatorWord: proof_shape: bind-only; consumer: operatorWord_cons, operatorWord_cons_cons, operatorWord_eq_path.
pathQuad: proof_shape: bind-only; consumer: operatorWord_eq_path, preTrace_eq_path, pathQuad_eq_adjacentQuad_last, transfer_product. | operatorWord_cons: proof_shape: bind-only; consumer: operatorWord_cons_cons.
operatorWord_cons_cons: proof_shape: bind-only; consumer: operatorWord_eq_path. | operatorWord_eq_path: proof_shape: content; consumer: preTrace_eq_path.
preTrace_eq_path: proof_shape: content; consumer: transfer_product. | auxLift: proof_shape: bind-only; consumer: auxLift_apply, auxLift_snoc, auxLift_one, auxLift_add, auxLift_smul, auxLift_mul, auxTrace_lift, auxTrace_lift_mul_flip, auxTrace_lift_mul_quad, auxLift_flip_pair, auxLift_quad_pair, auxLift_adjacentQuad, transfer_product.
auxLift_apply: proof_shape: bind-only; consumer: auxLift_snoc, auxTrace_lift_mul_flip. | auxLift_snoc: proof_shape: bind-only; consumer: auxTrace_lift, auxLift_flip_pair.
auxLift_one: proof_shape: bind-only; consumer: auxLift_quad_pair, auxLift_adjacentQuad. | auxLift_add: proof_shape: bind-only; consumer: auxLift_quad_pair.
auxLift_smul: proof_shape: bind-only; consumer: auxLift_quad_pair. | auxLift_mul: proof_shape: bind-only; consumer: auxLift_adjacentQuad.
auxTrace: proof_shape: bind-only; consumer: auxTrace_add, auxTrace_smul, auxTrace_lift, auxTrace_lift_mul_flip, auxTrace_lift_mul_quad, transfer_product. | auxTrace_add: proof_shape: bind-only; consumer: auxTrace_lift_mul_quad.
auxTrace_smul: proof_shape: bind-only; consumer: auxTrace_lift_mul_quad. | auxTrace_lift: proof_shape: bind-only; consumer: auxTrace_lift_mul_quad.
auxTrace_lift_mul_flip: proof_shape: bind-only; consumer: auxTrace_lift_mul_quad. | auxTrace_lift_mul_quad: proof_shape: bind-only; consumer: transfer_product.
flipConfig_cast_snoc: proof_shape: bind-only; consumer: auxLift_flip_pair. | auxLift_flip_pair: proof_shape: bind-only; consumer: auxLift_quad_pair.
auxLift_quad_pair: proof_shape: bind-only; consumer: auxLift_adjacentQuad. | adjacentQuad: proof_shape: bind-only; consumer: pathQuad_eq_adjacentQuad_last, auxLift_adjacentQuad, transfer_product, adjacentQuad_walsh, transfer_walsh.
pathQuad_eq_adjacentQuad_last: proof_shape: bind-only; consumer: transfer_product. | auxLift_adjacentQuad: proof_shape: bind-only; consumer: transfer_product.
transfer_product: proof_shape: content; consumer: transfer_walsh. | adjacentValue: proof_shape: bind-only; consumer: adjacentQuad_walsh, adjacentValue_ofFn, transfer_walsh.
quadOp_walsh: proof_shape: bind-only; consumer: adjacentQuad_walsh. | adjacentQuad_walsh: proof_shape: bind-only; consumer: transfer_walsh.
adjacentValue_ofFn: proof_shape: bind-only; consumer: transfer_walsh. | bitSign_mul: proof_shape: bind-only; consumer: flipEigenvalue_pair.
flipEigenvalue_pair: proof_shape: bind-only; consumer: adjacentValue_product_closed, hEigenvalue_succ. | adjacentValue_product_closed: proof_shape: bind-only; consumer: transfer_walsh.
transfer_walsh: proof_shape: content; consumer: claim_of_scalar_identity. | aeval_intertwiner: proof_shape: bind-only; consumer: claim_of_spectral_obligations.
hamiltonian_eq_sum_flip: proof_shape: bind-only; consumer: hamiltonian_walsh. | hEigenvalue: proof_shape: bind-only; consumer: hamiltonian_walsh, hEigenvalue_succ, hEigenvalue_count, claim_of_spectral_obligations.
hamiltonian_walsh: proof_shape: bind-only; consumer: claim_of_spectral_obligations. | hEigenvalue_succ: proof_shape: bind-only; consumer: hEigenvalue_count.
hEigenvalue_count: proof_shape: bind-only; consumer: claim_of_spectral_obligations. | signChanges_le: proof_shape: bind-only; consumer: claim_of_spectral_obligations.
walsh_right_cancel: proof_shape: bind-only; consumer: claim_of_spectral_obligations. | claim_of_spectral_obligations: proof_shape: bind-only; consumer: claim_of_scalar_identity.
claim_of_scalar_identity: proof_shape: content; consumer: result. | result: proof_shape: content; consumer: none.
-/
import D5.S1.Recurrence.CentralFactorialTransferExpansion
import D5.S3.Analytic.Hunter.NCHunterPositivity
import D5.S3.Estimation.DataProcessing.OneCutZeroExcess
import Mathlib.Data.Finset.Piecewise
import Mathlib.LinearAlgebra.Matrix.Permutation
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix
variable {F : Type*} [Field F]
def Rcoef (u : F) (j k l m : Fin 2) : F :=
  if j = m ∧ l = k then 1
  else if j = l ∧ k = m ∧ j ≠ k then u
  else if j = k ∧ l = m ∧ j ≠ l then u
  else 0
def Kcoef (j k : Fin 2) : F := if j = k then 1 else 0
def twoSite (N : ℕ) (u : F) (a b : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) F :=
  fun x y => if (∀ c, c ≠ a → c ≠ b → x c = y c) then Rcoef u (y a) (x a) (y b) (x b) else 0
def oneSite (N : ℕ) (a : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) F :=
  fun x y => if (∀ c, c ≠ a → x c = y c) then Kcoef (y a) (x a) else 0
def preTrace (n : ℕ) (u : F) : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) F :=
  ((List.ofFn fun i : Fin n => twoSite (n + 1) u (Fin.castSucc (Fin.rev i)) (Fin.last n)).prod *
      oneSite (n + 1) 0) *
    ((List.ofFn fun i : Fin n => twoSite (n + 1) u (Fin.last n) (Fin.castSucc i)).prod *
      oneSite (n + 1) (Fin.last n))
def transfer (n : ℕ) (u : F) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F :=
  fun x y => ∑ s : Fin 2, preTrace n u (Fin.snoc x s) (Fin.snoc y s)
def hamiltonian (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F :=
  ∑ i : Fin n, if h : i.1 + 1 < n then
    (fun x y => if (∀ c, c ≠ i → c ≠ ⟨i.1 + 1, h⟩ → x c = y c) ∧ x i ≠ y i ∧
      x ⟨i.1 + 1, h⟩ ≠ y ⟨i.1 + 1, h⟩ then 1 else 0)
  else 0
def claim : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (n : ℕ), 1 ≤ n → ∀ u : F,
    transfer n u = (2 : F) • ∑ k ∈ Finset.range n, ((1 + u ^ 2) ^ (n - k) * (2 * u) ^ k) •
      ∑ j ∈ Finset.range (k / 2 + 1),
        (dfBinom ((n : ℤ) - k - 2 + 2 * j) (2 * j) * (-1) ^ j / ((k - 2 * j).factorial : F)) •
          Polynomial.aeval (hamiltonian n : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) (mPoly (F := F) (k - 2 * j))

end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
variable {F : Type*} [Field F]
private lemma oneSite_eq_one (N : ℕ) (a : Fin N) :
    oneSite (F := F) N a = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [oneSite, Kcoef]
  · rw [Matrix.one_apply_ne hxy]
    unfold oneSite Kcoef
    split_ifs with hrest heq
    · exfalso
      apply hxy
      funext c
      by_cases hc : c = a
      · subst c
        exact heq.symm
      · exact hrest c hc
    all_goals rfl
private lemma Rcoef_swap (u : F) (j k l m : Fin 2) :
    Rcoef u j k l m = Rcoef u l m j k := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;> simp [Rcoef]
private lemma Rcoef_decomposition (u : F) (j k l m : Fin 2) :
    Rcoef u j k l m = (if k = l ∧ m = j then 1 else 0) +
      u * (if k = Fin.rev l ∧ m = Fin.rev j then 1 else 0) := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;> norm_num [Rcoef, Fin.rev]
private lemma twoSite_swap (N : ℕ) (u : F) (a b : Fin N) :
    twoSite N u a b = twoSite N u b a := by
  ext x y
  unfold twoSite
  have h : (∀ c, c ≠ a → c ≠ b → x c = y c) ↔
      (∀ c, c ≠ b → c ≠ a → x c = y c) := by
    exact forall_congr' (fun _ => forall_comm)
  simp only [h]
  congr 1
  exact Rcoef_swap u (y a) (x a) (y b) (x b)
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private def bitSign (s : Fin 2) : F := if s = 0 then 1 else -1
private def bitChar (a s : Fin 2) : F := if a = 0 then 1 else bitSign s
private def walsh (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) F :=
  fun x s => ∏ i, bitChar (F := F) (x i) (s i)
private lemma bitChar_orthogonal (a b : Fin 2) :
    ∑ c : Fin 2, bitChar (F := F) a c * bitChar c b = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_two, bitChar, bitSign]
private lemma walsh_square (N : ℕ) :
    walsh (F := F) N * walsh N = (2 : F) ^ N • (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) F) := by
  classical
  ext x y
  change (∑ z : Fin N → Fin 2,
    (∏ i, bitChar (F := F) (x i) (z i)) *
    (∏ i, bitChar (F := F) (z i) (y i))) =
    (2 : F) ^ N * (if x = y then 1 else 0)
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i c => bitChar (F := F) (x i) c * bitChar c (y i))]
  simp_rw [bitChar_orthogonal]
  by_cases hxy : x = y
  · subst y
    simp
  · have hi : ∃ i, x i ≠ y i := by
      exact Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := hi
    have hz : (∏ c : Fin N, if x c = y c then (2 : F) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hz]
    simp [hxy]
private lemma bitChar_rev (a s : Fin 2) :
    bitChar (F := F) (Fin.rev a) s = bitSign s * bitChar a s := by
  fin_cases a <;> fin_cases s <;> simp [bitChar, bitSign, Fin.rev]
private def flipEquiv {N : ℕ} (S : Finset (Fin N)) : Equiv.Perm (Fin N → Fin 2) :=
  Equiv.piCongrRight (fun c => if c ∈ S then Fin.revPerm else Equiv.refl (Fin 2))
@[simp] private lemma flipEquiv_apply {N : ℕ} (S : Finset (Fin N)) (x : Fin N → Fin 2) :
    flipEquiv S x = S.piecewise (fun c => Fin.rev (x c)) x := by
  funext c
  simp only [flipEquiv, Equiv.piCongrRight_apply, Pi.map_apply, Finset.piecewise]
  split_ifs <;> rfl
private def flipEigenvalue {N : ℕ} (S : Finset (Fin N)) (s : Fin N → Fin 2) : F :=
  ∏ c ∈ S, bitSign (F := F) (s c)
private lemma flipOp_walsh {N : ℕ} (S : Finset (Fin N)) :
    (flipEquiv S).permMatrix F * walsh N =
      walsh N * Matrix.diagonal (fun s => flipEigenvalue (F := F) S s) := by
  classical
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext x s
  simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, walsh, id_eq,
    flipEquiv, flipEigenvalue]
  rw [mul_comm]
  rw [← Fintype.prod_ite_mem S (fun c => bitSign (F := F) (s c))]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c hc
  by_cases hcs : c ∈ S <;> simp [hcs, bitChar_rev]
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private lemma swapConfig_eq_iff {N : ℕ} (a b : Fin N) (x y : Fin N → Fin 2) :
    (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x = y ↔
      (∀ c, c ≠ a → c ≠ b → x c = y c) ∧ x a = y b ∧ x b = y a := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro c hca hcb
      simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hca hcb] using congrFun h c
    · simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap] using congrFun h b
    · simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap] using congrFun h a
  · rintro ⟨hr, ha, hb⟩
    funext c
    by_cases hca : c = a
    · subst c
      simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap] using hb
    · by_cases hcb : c = b
      · subst c
        simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap] using ha
      · simpa [Equiv.piCongrLeft'_apply, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hca hcb] using hr c hca hcb
private lemma rev_eq_iff_ne (a b : Fin 2) : Fin.rev a = b ↔ a ≠ b := by
  fin_cases a <;> fin_cases b <;> simp [Fin.rev]
private lemma flipConfig_pair_eq_iff {N : ℕ} (a b : Fin N) (x y : Fin N → Fin 2) :
    ({a, b} : Finset (Fin N)).piecewise (fun c => Fin.rev (x c)) x = y ↔
      (∀ c, c ≠ a → c ≠ b → x c = y c) ∧ x a ≠ y a ∧ x b ≠ y b := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro c hca hcb
      simpa [Finset.piecewise, hca, hcb] using congrFun h c
    · have := congrFun h a
      simpa [Finset.piecewise, rev_eq_iff_ne] using this
    · have := congrFun h b
      simpa [Finset.piecewise, rev_eq_iff_ne] using this
  · rintro ⟨hr, ha, hb⟩
    funext c
    by_cases hca : c = a
    · subst c
      simpa [Finset.piecewise, rev_eq_iff_ne] using ha
    · by_cases hcb : c = b
      · subst c
        simpa [Finset.piecewise, rev_eq_iff_ne] using hb
      · simpa [Finset.piecewise, hca, hcb] using hr c hca hcb
private lemma flipConfig_swap_eq_iff {N : ℕ} (a b : Fin N) (x y : Fin N → Fin 2) :
    ({a, b} : Finset (Fin N)).piecewise (fun c => Fin.rev (((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) c))
        ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) = y ↔
      (∀ c, c ≠ a → c ≠ b → x c = y c) ∧
        x a = Fin.rev (y b) ∧ x b = Fin.rev (y a) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro c hca hcb
      simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap, hca, hcb,
        Equiv.swap_apply_of_ne_of_ne hca hcb] using congrFun h c
    · have ht := congrArg Fin.rev (congrFun h b)
      simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap] using ht
    · have ht := congrArg Fin.rev (congrFun h a)
      simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap] using ht
  · rintro ⟨hr, ha, hb⟩
    funext c
    by_cases hca : c = a
    · subst c
      simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap] using congrArg Fin.rev hb
    · by_cases hcb : c = b
      · subst c
        simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap] using congrArg Fin.rev ha
      · simpa [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap, hca, hcb,
          Equiv.swap_apply_of_ne_of_ne hca hcb] using hr c hca hcb
private lemma twoSite_factor {N : ℕ} (u : F) (a b : Fin N) :
    twoSite N u a b = (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F * (1 + u • (flipEquiv {a, b}).permMatrix F) := by
  classical
  rw [mul_add, mul_one, mul_smul_comm]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul]
  simp only [flipEquiv_apply]
  change (if (∀ c, c ≠ a → c ≠ b → x c = y c) then
      Rcoef u (y a) (x a) (y b) (x b) else 0) =
    (if (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x = y then 1 else 0) +
      u * (if (({a, b} : Finset (Fin N)).piecewise
        (fun c => Fin.rev (((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) c))
        ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x)) = y then 1 else 0)
  simp only [swapConfig_eq_iff, flipConfig_swap_eq_iff]
  by_cases hr : ∀ c, c ≠ a → c ≠ b → x c = y c
  · simpa only [eq_true hr, true_and, ite_true] using
      Rcoef_decomposition u (y a) (x a) (y b) (x b)
  · simp [hr]
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private lemma equivMatrix_apply {ι : Type*} [DecidableEq ι]
    (e : Equiv.Perm ι) (x y : ι) :
    (e.toPEquiv.toMatrix : Matrix ι ι F) x y = if e x = y then 1 else 0 := by
  simp [PEquiv.toMatrix_apply, eq_comm]
private lemma flipConfig_comm {N : ℕ} (S T : Finset (Fin N)) (x : Fin N → Fin 2) :
    S.piecewise (fun c => Fin.rev ((T.piecewise (fun c => Fin.rev (x c)) x) c))
        (T.piecewise (fun c => Fin.rev (x c)) x) =
      T.piecewise (fun c => Fin.rev ((S.piecewise (fun c => Fin.rev (x c)) x) c))
        (S.piecewise (fun c => Fin.rev (x c)) x) := by
  funext c
  by_cases hs : c ∈ S <;> by_cases ht : c ∈ T <;>
    simp [Finset.piecewise, hs, ht]
private lemma flipConfig_involutive {N : ℕ} (S : Finset (Fin N)) (x : Fin N → Fin 2) :
    S.piecewise (fun c => Fin.rev ((S.piecewise (fun c => Fin.rev (x c)) x) c))
        (S.piecewise (fun c => Fin.rev (x c)) x) = x := by
  funext c
  by_cases hs : c ∈ S <;> simp [Finset.piecewise, hs]
private lemma flipOp_comm {N : ℕ} (S T : Finset (Fin N)) :
    (flipEquiv S).permMatrix F * (flipEquiv T).permMatrix F = (flipEquiv T).permMatrix F * (flipEquiv S).permMatrix F := by
  change (flipEquiv S).toPEquiv.toMatrix * (flipEquiv T).toPEquiv.toMatrix =
    (flipEquiv T).toPEquiv.toMatrix * (flipEquiv S).toPEquiv.toMatrix
  simp only [PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, equivMatrix_apply]
  simp only [flipEquiv_apply]
  change (if T.piecewise (fun c => Fin.rev ((S.piecewise (fun c => Fin.rev (x c)) x) c))
      (S.piecewise (fun c => Fin.rev (x c)) x) = y then (1 : F) else 0) =
    (if S.piecewise (fun c => Fin.rev ((T.piecewise (fun c => Fin.rev (x c)) x) c))
      (T.piecewise (fun c => Fin.rev (x c)) x) = y then 1 else 0)
  rw [flipConfig_comm]
private lemma flipOp_square {N : ℕ} (S : Finset (Fin N)) :
    (flipEquiv S).permMatrix F * (flipEquiv S).permMatrix F = 1 := by
  change (flipEquiv S).toPEquiv.toMatrix * (flipEquiv S).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, equivMatrix_apply, Matrix.one_apply]
  simp only [flipEquiv_apply]
  change (if S.piecewise (fun c => Fin.rev ((S.piecewise (fun c => Fin.rev (x c)) x) c))
      (S.piecewise (fun c => Fin.rev (x c)) x) = y then (1 : F) else 0) =
    (if x = y then 1 else 0)
  rw [flipConfig_involutive]
private lemma swapOp_square {N : ℕ} (a b : Fin N) :
    (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F * (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F = 1 := by
  change (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).toPEquiv.toMatrix * (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, equivMatrix_apply, Matrix.one_apply]
  change (if (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) = y then (1 : F) else 0) =
    (if x = y then 1 else 0)
  have hs : (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) = x := by
    funext c
    simp [Equiv.piCongrLeft'_apply, Equiv.symm_swap]
  rw [hs]
private lemma swap_flip_pair_general {N : ℕ} (a b c d : Fin N) :
    (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F * (flipEquiv {c,d}).permMatrix F =
      (flipEquiv {Equiv.swap a b c, Equiv.swap a b d}).permMatrix F * (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F := by
  change (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).toPEquiv.toMatrix * (flipEquiv {c,d}).toPEquiv.toMatrix =
    (flipEquiv {Equiv.swap a b c, Equiv.swap a b d}).toPEquiv.toMatrix *
      (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).toPEquiv.toMatrix
  simp only [PEquiv.toMatrix_toPEquiv_mul]
  have hc : ∀ x, ({c,d} : Finset (Fin N)).piecewise
      (fun k => Fin.rev (((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) k))
      ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) =
      (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b))
        (({Equiv.swap a b c, Equiv.swap a b d} : Finset (Fin N)).piecewise
          (fun k => Fin.rev (x k)) x) := by
    intro x
    funext k
    simp only [Finset.piecewise, Equiv.piCongrLeft'_apply, Equiv.symm_swap, mem_insert, mem_singleton]
    simp only [Equiv.apply_eq_iff_eq]
  ext x y
  simp only [Matrix.submatrix_apply, id_eq, equivMatrix_apply]
  simp only [flipEquiv_apply]
  change (if ({c,d} : Finset (Fin N)).piecewise
      (fun k => Fin.rev (((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) k))
      ((Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)) x) = y then (1 : F) else 0) =
    (if (Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b))
      (({Equiv.swap a b c, Equiv.swap a b d} : Finset (Fin N)).piecewise
        (fun k => Fin.rev (x k)) x) = y then 1 else 0)
  rw [hc]
private lemma swap_flip_comm {N : ℕ} (a b : Fin N) :
    (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F * (flipEquiv {a,b}).permMatrix F = (flipEquiv {a,b}).permMatrix F * (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F := by
  simpa [Finset.pair_comm] using swap_flip_pair_general (F := F) a b a b
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private noncomputable def quadOp {N : ℕ} (u : F) (a b : Fin N) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) F :=
  (1 + u ^ 2) • 1 + (2 * u) • (flipEquiv {a,b}).permMatrix F
private lemma twoSite_flip_covariance {N : ℕ} (u : F) (a b c d : Fin N) :
    twoSite N u a b * (flipEquiv {c,d}).permMatrix F =
      (flipEquiv {Equiv.swap a b c, Equiv.swap a b d}).permMatrix F * twoSite N u a b := by
  rw [twoSite_factor, mul_assoc]
  have hc : (1 + u • (flipEquiv {a,b}).permMatrix F) * (flipEquiv {c,d}).permMatrix F =
      (flipEquiv {c,d}).permMatrix F * (1 + u • (flipEquiv {a,b}).permMatrix F) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rw [flipOp_comm]
  rw [hc, ← mul_assoc, swap_flip_pair_general, mul_assoc]
private lemma twoSite_square {N : ℕ} (u : F) (a b : Fin N) :
    twoSite N u a b * twoSite N u a b = quadOp u a b := by
  rw [twoSite_factor]
  have hc : Commute (1 + u • (flipEquiv {a,b}).permMatrix F) ((show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F) := by
    change (1 + u • (flipEquiv {a,b}).permMatrix F) * (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F =
      (show Equiv.Perm (Fin N → Fin 2) from Equiv.piCongrLeft' (fun _ : Fin N => Fin 2) (Equiv.swap a b)).permMatrix F * (1 + u • (flipEquiv {a,b}).permMatrix F)
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rw [swap_flip_comm]
  rw [hc.mul_mul_mul_comm, swapOp_square, one_mul]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul, flipOp_square, quadOp]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring
private lemma twoSite_quad_covariance {N : ℕ} (u : F) (a b c d : Fin N) :
    twoSite N u a b * quadOp u c d =
      quadOp u (Equiv.swap a b c) (Equiv.swap a b d) * twoSite N u a b := by
  simp only [quadOp, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  rw [twoSite_flip_covariance]
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private lemma flipOp_apply {N : ℕ} (S : Finset (Fin N)) (x y : Fin N → Fin 2) :
    (flipEquiv S).permMatrix F x y =
      if S.piecewise (fun c => Fin.rev (x c)) x = y then 1 else 0 := by
  simp only [equivMatrix_apply, flipEquiv_apply]
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix
variable {F : Type*} [Field F]
private noncomputable def operatorWord {N : ℕ} (u : F) (aux : Fin N) (l : List (Fin N)) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) F :=
  (l.reverse.map (fun a => twoSite N u a aux)).prod *
    (l.map (fun a => twoSite N u a aux)).prod
private noncomputable def pathQuad {N : ℕ} (u : F) (aux : Fin N) :
    List (Fin N) → Matrix (Fin N → Fin 2) (Fin N → Fin 2) F
  | [] => 1
  | [a] => quadOp u a aux
  | a :: b :: l => quadOp u a b * pathQuad u aux (b :: l)
private lemma operatorWord_cons {N : ℕ} (u : F) (aux a : Fin N) (l : List (Fin N)) :
    operatorWord u aux (a :: l) =
      (l.reverse.map (fun b => twoSite N u b aux)).prod *
        quadOp u a aux * (l.map (fun b => twoSite N u b aux)).prod := by
  simp only [operatorWord, List.reverse_cons, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  calc
    _ = (l.reverse.map (fun b => twoSite N u b aux)).prod *
        (twoSite N u a aux * twoSite N u a aux) *
        (l.map (fun b => twoSite N u b aux)).prod := by simp only [mul_assoc]
    _ = _ := by rw [twoSite_square]
private lemma operatorWord_cons_cons {N : ℕ} (u : F) (aux a b : Fin N) (l : List (Fin N))
    (hab : a ≠ b) (haux : a ≠ aux)
    (hc : Commute (l.reverse.map (fun c => twoSite N u c aux)).prod (quadOp u a b)) :
    operatorWord u aux (a :: b :: l) = quadOp u a b * operatorWord u aux (b :: l) := by
  have hswap : twoSite N u b aux * quadOp u a aux =
      quadOp u a b * twoSite N u b aux := by
    simpa [Equiv.swap_apply_of_ne_of_ne hab haux] using
      twoSite_quad_covariance (F := F) u b aux a aux
  rw [operatorWord_cons]
  simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  calc
    _ = (l.reverse.map (fun c => twoSite N u c aux)).prod *
        ((twoSite N u b aux * quadOp u a aux) *
          (twoSite N u b aux * (l.map (fun c => twoSite N u c aux)).prod)) := by
      simp only [mul_assoc]
    _ = (l.reverse.map (fun c => twoSite N u c aux)).prod *
        ((quadOp u a b * twoSite N u b aux) *
          (twoSite N u b aux * (l.map (fun c => twoSite N u c aux)).prod)) := by rw [hswap]
    _ = ((l.reverse.map (fun c => twoSite N u c aux)).prod * quadOp u a b) *
        (twoSite N u b aux *
          (twoSite N u b aux * (l.map (fun c => twoSite N u c aux)).prod)) := by
      simp only [mul_assoc]
    _ = (quadOp u a b * (l.reverse.map (fun c => twoSite N u c aux)).prod) *
        (twoSite N u b aux *
          (twoSite N u b aux * (l.map (fun c => twoSite N u c aux)).prod)) := by rw [hc.eq]
    _ = _ := by
      simp only [operatorWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
private lemma operatorWord_eq_path {N : ℕ} (u : F) (aux : Fin N) (l : List (Fin N))
    (hl : l.Nodup) (haux : aux ∉ l) : operatorWord u aux l = pathQuad u aux l := by
  revert hl haux
  induction l with
  | nil => intros; simp [operatorWord, pathQuad]
  | cons a l ih =>
    intro hl haux
    have htail : l.Nodup := (List.nodup_cons.mp hl).2
    have hauxl : aux ∉ l := fun hx => haux (List.mem_cons_of_mem a hx)
    cases l with
    | nil => simpa [operatorWord, pathQuad] using twoSite_square (F := F) u a aux
    | cons b l =>
      have hal : a ∉ b :: l := (List.nodup_cons.mp hl).1
      have hab : a ≠ b := fun h => hal (by simp [h])
      have haa : a ≠ aux := fun h => haux (by simp [h])
      have hba : b ≠ aux := fun h => haux (by simp [h])
      have hc : Commute (l.reverse.map (fun c => twoSite N u c aux)).prod (quadOp u a b) := by
        apply Commute.list_prod_left
        intro M hM
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hM
        have hcl : c ∈ l := List.mem_reverse.mp hc
        have hac : a ≠ c := fun h => hal (List.mem_cons_of_mem b (h.symm ▸ hcl))
        have hbc : b ≠ c := by
          intro h
          apply (List.nodup_cons.mp htail).1
          exact h.symm ▸ hcl
        have hsa : Equiv.swap c aux a = a := Equiv.swap_apply_of_ne_of_ne hac haa
        have hsb : Equiv.swap c aux b = b := Equiv.swap_apply_of_ne_of_ne hbc hba
        exact (by simpa [hsa, hsb] using
          twoSite_quad_covariance (F := F) u c aux a b :
            twoSite N u c aux * quadOp u a b = quadOp u a b * twoSite N u c aux)
      rw [operatorWord_cons_cons u aux a b l hab haa hc, ih htail hauxl]
      rfl
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix
variable {F : Type*} [Field F]
private lemma preTrace_eq_path (n : ℕ) (u : F) :
    preTrace n u = pathQuad u (Fin.last n) (List.ofFn (fun i : Fin n => i.castSucc)) := by
  let l : List (Fin (n + 1)) := List.ofFn (fun i : Fin n => i.castSucc)
  have hl : l.Nodup := by
    exact List.nodup_ofFn_ofInjective (Fin.castSucc_injective n)
  have ha : Fin.last n ∉ l := by
    dsimp [l]
    simp only [List.mem_ofFn, not_exists]
    intro i
    exact Fin.castSucc_ne_last i
  have hr : (List.ofFn fun i : Fin n =>
      twoSite (n + 1) u (Fin.castSucc (Fin.rev i)) (Fin.last n)) =
      l.reverse.map (fun a => twoSite (n + 1) u a (Fin.last n)) := by
    have hrev := congrArg (List.map (fun a : Fin (n + 1) => twoSite (n + 1) u a (Fin.last n)))
      (GVHunter.reverse_word_list (fun i : Fin n => i.castSucc))
    simpa [l, List.map_reverse, List.map_ofFn, Function.comp_def,
      Equiv.piCongrLeft'_apply, Fin.revPerm_apply] using hrev
  have hf : (List.ofFn fun i : Fin n => twoSite (n + 1) u (Fin.last n) (Fin.castSucc i)) =
      l.map (fun a => twoSite (n + 1) u a (Fin.last n)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact twoSite_swap (F := F) (n + 1) u _ _
  rw [preTrace, oneSite_eq_one, oneSite_eq_one, mul_one, mul_one, hr, hf]
  exact operatorWord_eq_path u (Fin.last n) l hl ha
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix
variable {F : Type*} [Field F]
private noncomputable def auxLift {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) :
    Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) F :=
  Matrix.reindexAlgEquiv F F (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 2))
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) F) A)
private lemma auxLift_apply {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F)
    (x y : Fin (n + 1) → Fin 2) :
    auxLift A x y = if x (Fin.last n) = y (Fin.last n) then A (Fin.init x) (Fin.init y) else 0 := by
  simp [auxLift, Matrix.reindex_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Fin.snocEquiv, Matrix.coe_reindexAlgEquiv]
private lemma auxLift_snoc {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F)
    (x y : Fin n → Fin 2) (s t : Fin 2) :
    auxLift A (Fin.snoc x s) (Fin.snoc y t) = if s = t then A x y else 0 := by
  simp [auxLift_apply]
private lemma auxLift_one (n : ℕ) :
    auxLift (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) = 1 := by
  simp [auxLift, Matrix.one_kronecker_one]
private lemma auxLift_add {n : ℕ}
    (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) :
    auxLift (A + B) = auxLift A + auxLift B := by
  unfold auxLift Matrix.kronecker
  rw [Matrix.kronecker_add, map_add]
private lemma auxLift_smul {n : ℕ} (c : F)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) :
    auxLift (c • A) = c • auxLift A := by
  simp [auxLift, Matrix.kronecker_smul]
private lemma auxLift_mul {n : ℕ}
    (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) :
    auxLift (A * B) = auxLift A * auxLift B := by
  unfold auxLift Matrix.kronecker
  rw [← map_mul]
  apply congrArg (Matrix.reindexAlgEquiv F F
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 2)))
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul (1 : Matrix (Fin 2) (Fin 2) F)
      (1 : Matrix (Fin 2) (Fin 2) F) A B)
private noncomputable def auxTrace {n : ℕ}
    (A : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) F) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) F :=
  fun x y => ∑ s : Fin 2, A (Fin.snoc x s) (Fin.snoc y s)
private lemma auxTrace_add {n : ℕ}
    (A B : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) F) :
    auxTrace (A + B) = auxTrace A + auxTrace B := by
  ext x y
  simp [auxTrace, Finset.sum_add_distrib]
private lemma auxTrace_smul {n : ℕ} (c : F)
    (A : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) F) :
    auxTrace (c • A) = c • auxTrace A := by
  ext x y
  simp [auxTrace, Finset.mul_sum, mul_add]
private lemma auxTrace_lift {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) :
    auxTrace (auxLift A) = (2 : F) • A := by
  ext x y
  simp [auxTrace, auxLift_snoc, Fin.sum_univ_two, two_mul]
private lemma auxTrace_lift_mul_flip {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) (a : Fin n) :
    auxTrace (auxLift A * (flipEquiv {a.castSucc, Fin.last n}).permMatrix F) = 0 := by
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  change (∑ s : Fin 2, auxLift A (Fin.snoc x s)
    ((flipEquiv {a.castSucc, Fin.last n}).symm (Fin.snoc y s))) = 0
  apply Finset.sum_eq_zero
  intro s hs
  rw [auxLift_apply]
  have he : ((flipEquiv {a.castSucc, Fin.last n}).symm (Fin.snoc y s)) (Fin.last n) =
      Fin.rev s := by simp [flipEquiv]
  simp only [Fin.snoc_last, he]
  fin_cases s <;> simp [Fin.rev]
private lemma auxTrace_lift_mul_quad {n : ℕ}
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) F) (a : Fin n) (u : F) :
    auxTrace (auxLift A * quadOp u a.castSucc (Fin.last n)) =
      (2 * (1 + u ^ 2)) • A := by
  rw [quadOp, mul_add, mul_smul_comm, mul_smul_comm, mul_one,
    auxTrace_add, auxTrace_smul, auxTrace_smul, auxTrace_lift, auxTrace_lift_mul_flip]
  simp only [smul_smul, smul_zero, add_zero]
  congr 1
  ring
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix
variable {F : Type*} [Field F]
private lemma flipConfig_cast_snoc {n : ℕ} (a b : Fin n) (x : Fin n → Fin 2) (s : Fin 2) :
    ({a.castSucc, b.castSucc} : Finset (Fin (n + 1))).piecewise
        (fun c : Fin (n + 1) => Fin.rev
          ((Fin.snoc (α := fun _ : Fin (n + 1) => Fin 2) x s) c))
          (Fin.snoc x s) =
      Fin.snoc (({a,b} : Finset (Fin n)).piecewise (fun c => Fin.rev (x c)) x) s := by
  funext c
  refine Fin.lastCases ?_ (fun i => ?_) c
  · simp [Finset.piecewise, Ne.symm (Fin.castSucc_ne_last a), Ne.symm (Fin.castSucc_ne_last b)]
  · simp [Finset.piecewise, Fin.castSucc_inj]
private lemma auxLift_flip_pair {n : ℕ} (a b : Fin n) :
    auxLift ((flipEquiv {a,b}).permMatrix F) = (flipEquiv {a.castSucc,b.castSucc}).permMatrix F := by
  ext x y
  cases x using Fin.snocCases with
  | snoc x s =>
    cases y using Fin.snocCases with
    | snoc y t =>
      rw [auxLift_snoc]
      simp only [flipOp_apply, flipConfig_cast_snoc, Fin.snoc_inj]
      by_cases h : s = t <;> simp [h]
private lemma auxLift_quad_pair {n : ℕ} (u : F) (a b : Fin n) :
    auxLift (quadOp u a b) = quadOp u a.castSucc b.castSucc := by
  simp only [quadOp, auxLift_add, auxLift_smul, auxLift_one, auxLift_flip_pair]
private noncomputable def adjacentQuad {N : ℕ} (u : F) :
    List (Fin N) → Matrix (Fin N → Fin 2) (Fin N → Fin 2) F
  | [] => 1
  | [_] => 1
  | a :: b :: l => quadOp u a b * adjacentQuad u (b :: l)
private lemma pathQuad_eq_adjacentQuad_last {N : ℕ} (u : F) (aux : Fin N)
    (l : List (Fin N)) (hl : l ≠ []) :
    pathQuad u aux l = adjacentQuad u l * quadOp u (l.getLast hl) aux := by
  revert hl
  induction l with
  | nil => intro hl; contradiction
  | cons a l ih =>
    intro hl
    cases l with
    | nil => simp [pathQuad, adjacentQuad]
    | cons b l =>
      rw [pathQuad, adjacentQuad, List.getLast_cons_cons, ih (by simp)]
      simp only [mul_assoc]
private lemma auxLift_adjacentQuad {n : ℕ} (u : F) (l : List (Fin n)) :
    auxLift (adjacentQuad u l) = adjacentQuad u (l.map Fin.castSucc) := by
  induction l with
  | nil => simp [adjacentQuad, auxLift_one]
  | cons a l ih =>
    cases l with
    | nil => simp [adjacentQuad, auxLift_one]
    | cons b l =>
      change auxLift (quadOp u a b * adjacentQuad u (b :: l)) =
        quadOp u a.castSucc b.castSucc * adjacentQuad u ((b :: l).map Fin.castSucc)
      rw [auxLift_mul, auxLift_quad_pair, ih]
private lemma transfer_product (n : ℕ) (hn : 1 ≤ n) (u : F) :
    transfer n u = (2 * (1 + u ^ 2)) •
      adjacentQuad u (List.ofFn (fun i : Fin n => i)) := by
  let l : List (Fin n) := List.ofFn (fun i : Fin n => i)
  have hl : l ≠ [] := by
    exact mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hn)
  have hmap : List.ofFn (fun i : Fin n => i.castSucc) = l.map Fin.castSucc := by
    simp [l, List.map_ofFn, Function.comp_def]
  change auxTrace (preTrace n u) = (2 * (1 + u ^ 2)) • adjacentQuad u l
  rw [preTrace_eq_path, hmap,
    pathQuad_eq_adjacentQuad_last u (Fin.last n) (l.map Fin.castSucc) (by simpa using hl),
    List.getLast_map, ← auxLift_adjacentQuad]
  exact auxTrace_lift_mul_quad (adjacentQuad u l) (l.getLast hl) u
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private noncomputable def adjacentValue {N : ℕ} (u : F) : List (Fin N) → (Fin N → Fin 2) → F
  | [], _ => 1
  | [_], _ => 1
  | a :: b :: l, s => ((1 + u ^ 2) + 2 * u * flipEigenvalue {a,b} s) * adjacentValue u (b :: l) s
private lemma quadOp_walsh {N : ℕ} (u : F) (a b : Fin N) :
    quadOp u a b * walsh N = walsh N * Matrix.diagonal
      (fun s => (1 + u ^ 2) + 2 * u * flipEigenvalue {a,b} s) := by
  rw [quadOp, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, flipOp_walsh]
  ext x s
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
  ring
private lemma adjacentQuad_walsh {N : ℕ} (u : F) (l : List (Fin N)) :
    adjacentQuad u l * walsh N = walsh N * Matrix.diagonal (adjacentValue u l) := by
  induction l with
  | nil => simp [adjacentQuad, adjacentValue]
  | cons a l ih =>
    cases l with
    | nil => simp [adjacentQuad, adjacentValue]
    | cons b l =>
      rw [adjacentQuad, mul_assoc, ih, ← mul_assoc, quadOp_walsh,
        mul_assoc, Matrix.diagonal_mul_diagonal]
      rfl
private lemma adjacentValue_ofFn {N : ℕ} (u : F) (m : ℕ) (f : Fin (m + 1) → Fin N)
    (s : Fin N → Fin 2) :
    adjacentValue u (List.ofFn f) s =
      ∏ i : Fin m, ((1 + u ^ 2) + 2 * u * flipEigenvalue {f i.castSucc, f i.succ} s) := by
  induction m with
  | zero => simp [List.ofFn_succ, adjacentValue]
  | succ m ih =>
    have ht : List.ofFn (fun i : Fin (m + 1) => f i.succ) =
        f (0 : Fin (m + 1)).succ :: List.ofFn (fun i : Fin m => f i.succ.succ) :=
      List.ofFn_succ
    calc
      _ = ((1 + u ^ 2) + 2 * u *
            flipEigenvalue {f 0, f (0 : Fin (m + 1)).succ} s) *
          adjacentValue u (List.ofFn (fun i : Fin (m + 1) => f i.succ)) s := by
        rw [List.ofFn_succ, ht, adjacentValue, ← ht]
      _ = ((1 + u ^ 2) + 2 * u *
            flipEigenvalue {f 0, f (0 : Fin (m + 1)).succ} s) *
          ∏ i : Fin m, ((1 + u ^ 2) + 2 * u *
            flipEigenvalue {f i.castSucc.succ, f i.succ.succ} s) := by rw [ih]
      _ = _ := by
        rw [Fin.prod_univ_succ]
        rfl
private lemma bitSign_mul (a b : Fin 2) :
    bitSign (F := F) a * bitSign b = if a = b then 1 else -1 := by
  fin_cases a <;> fin_cases b <;> simp [bitSign]
private lemma flipEigenvalue_pair {N : ℕ} (a b : Fin N) (hab : a ≠ b) (s : Fin N → Fin 2) :
    flipEigenvalue (F := F) {a,b} s = if s a = s b then 1 else -1 := by
  simp [flipEigenvalue, hab, bitSign_mul]
private lemma adjacentValue_product_closed (m : ℕ) (u : F) (s : Fin (m + 1) → Fin 2) :
    (∏ i : Fin m, ((1 + u ^ 2) + 2 * u *
      flipEigenvalue {i.castSucc, i.succ} s)) =
      (1 - u) ^ (2 * ((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card)) * (1 + u) ^ (2 * (m - ((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card))) := by
  classical
  have hi (i : Fin m) : (1 + u ^ 2) + 2 * u * flipEigenvalue {i.castSucc, i.succ} s =
      if s i.castSucc = s i.succ then (1 + u) ^ 2 else (1 - u) ^ 2 := by
    rw [flipEigenvalue_pair]
    · split_ifs <;> ring
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun i : Fin m => s i.castSucc = s i.succ)
  have he : (Finset.univ.filter (fun i : Fin m => s i.castSucc = s i.succ)).card =
      m - ((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card) := by
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    unfold D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures
    simp only [ne_eq] at hc ⊢
    omega
  rw [he]
  simp only [D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures,
    ne_eq]
  have hf : (Finset.univ.filter (fun i : Fin m => ¬ s i.castSucc = s i.succ)) =
      D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s := by
    ext i
    simp [D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures]
  rw [hf]
  simp only [D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures, ← pow_mul]
  ring
private lemma transfer_walsh (m : ℕ) (u : F) :
    transfer (m + 1) u * walsh (m + 1) = walsh (m + 1) * Matrix.diagonal
      (fun s => scalarEigenvalue m (((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card)) u) := by
  rw [transfer_product (m + 1) (by omega), smul_mul_assoc, adjacentQuad_walsh]
  ext x s
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
  rw [adjacentValue_ofFn, adjacentValue_product_closed]
  unfold scalarEigenvalue
  ring
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Polynomial
variable {F : Type*} [Field F]
private lemma aeval_intertwiner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : Matrix ι ι F) (d : ι → F)
    (h : A * H = H * Matrix.diagonal d) (p : Polynomial F) :
    Polynomial.aeval A p * H = H * Matrix.diagonal (fun i => p.eval (d i)) := by
  classical
  ext i j
  rw [Matrix.mul_diagonal]
  have hx : Matrix.toLinAlgEquiv' A (H.col j) = d j • H.col j := by
    change (A * H).col j = _
    rw [h]
    funext k
    simp [Matrix.col, Matrix.mul_diagonal, smul_eq_mul, mul_comm]
  have hp := Module.End.aeval_apply_of_mem_apply_eq_smul (p := p) hx
  rw [Polynomial.aeval_algHom_apply] at hp
  simpa only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Matrix.col,
    Matrix.transpose_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    using congrFun hp i
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private lemma hamiltonian_eq_sum_flip (n : ℕ) :
    hamiltonian (F := F) n = ∑ i : Fin n, if h : i.1 + 1 < n then
      (flipEquiv {i, ⟨i.1 + 1, h⟩}).permMatrix F else 0 := by
  classical
  ext x y
  simp only [hamiltonian, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val + 1 < n
  · simp [h, flipOp_apply, flipConfig_pair_eq_iff]
  · simp [h]
private def hEigenvalue (n : ℕ) (s : Fin n → Fin 2) : F :=
  ∑ i : Fin n, if h : i.1 + 1 < n then
    flipEigenvalue (F := F) {i, ⟨i.1 + 1, h⟩} s else 0
private lemma hamiltonian_walsh (n : ℕ) :
    hamiltonian (F := F) n * walsh n =
      walsh n * Matrix.diagonal (fun s => hEigenvalue (F := F) n s) := by
  classical
  rw [hamiltonian_eq_sum_flip, Finset.sum_mul]
  calc
    _ = ∑ i : Fin n, walsh (F := F) n * Matrix.diagonal
        (fun s => if h : i.1 + 1 < n then
          flipEigenvalue (F := F) {i, ⟨i.1 + 1, h⟩} s else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i.1 + 1 < n
      · simp only [h, dite_true, ite_true]
        exact flipOp_walsh _
      · simp [h]
    _ = _ := by
      ext x s
      simp [Matrix.sum_apply, Matrix.mul_diagonal, hEigenvalue, Finset.mul_sum]
private lemma hEigenvalue_succ (m : ℕ) (s : Fin (m + 1) → Fin 2) :
    hEigenvalue (F := F) (m + 1) s =
      ∑ i : Fin m, if s i.castSucc = s i.succ then 1 else -1 := by
  unfold hEigenvalue
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt : i.val + 1 < m + 1 := by omega
  simp only [Fin.val_castSucc, hlt, dite_true]
  have hid : (⟨i.val + 1, hlt⟩ : Fin (m + 1)) = i.succ := by rfl
  rw [hid, flipEigenvalue_pair]
  intro hh
  have := congrArg Fin.val hh
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega
private lemma hEigenvalue_count (m : ℕ) (s : Fin (m + 1) → Fin 2) :
    hEigenvalue (F := F) (m + 1) s = (m : F) -
      2 * ((Finset.univ.filter (fun i : Fin m => s i.castSucc ≠ s i.succ)).card : F) := by
  rw [hEigenvalue_succ]
  have hterm (i : Fin m) : (if s i.castSucc = s i.succ then (1 : F) else -1) =
      1 - 2 * (if s i.castSucc ≠ s i.succ then 1 else 0) := by
    by_cases hi : s i.castSucc = s i.succ <;> simp [hi] <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum, Finset.sum_boole]
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
open Matrix Finset
variable {F : Type*} [Field F]
private lemma signChanges_le (m : ℕ) (s : Fin (m + 1) → Fin 2) : ((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card) ≤ m := by
  exact card_finset_fin_le (D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s)
private lemma walsh_right_cancel [CharZero F] {N : ℕ}
    (A B : Matrix (Fin N → Fin 2) (Fin N → Fin 2) F)
    (h : A * walsh N = B * walsh N) : A = B := by
  have h2 : (2 : F) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  have he := congrArg (fun M => M * walsh (F := F) N) h
  simp only [mul_assoc, walsh_square, mul_smul_comm, mul_one] at he
  have hh := congrArg (fun M => ((2 : F) ^ N)⁻¹ • M) he
  simpa only [smul_smul, inv_mul_cancel₀ h2, one_smul] using hh
private lemma claim_of_spectral_obligations
    (ht : ∀ (F : Type) [Field F] [CharZero F] (m : ℕ) (u : F),
      transfer (m + 1) u * walsh (m + 1) = walsh (m + 1) * Matrix.diagonal
        (fun s => scalarEigenvalue m (((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card)) u))
    (hs : ∀ (F : Type) [Field F] [CharZero F] (m l : ℕ), l ≤ m → ∀ u : F,
      scalarEigenvalue m l u = scalarExpansion m l u) : claim := by
  intro F _ _ _ n hn u
  cases n with
  | zero => omega
  | succ m =>
    apply walsh_right_cancel
    rw [ht]
    have hi (p : Polynomial F) :
        Polynomial.aeval (hamiltonian (F := F) (m + 1)) p * walsh (m + 1) =
          walsh (m + 1) * Matrix.diagonal
            (fun s => p.eval ((m : F) - 2 * (((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card) : F))) := by
      rw [aeval_intertwiner _ _ _ (hamiltonian_walsh (F := F) (m + 1)) p]
      simp only [hEigenvalue_count]
      congr 1
      funext s
      congr 2
      congr 1
      ext i
      simp [D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures]
    simp only [Finset.sum_mul, smul_mul_assoc]
    simp_rw [hi]
    ext x s
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [hs F m (((D5.S3.Estimation.DataProcessing.OneCutZeroExcess.internalFailures s).card)) (signChanges_le m s) u]
    unfold scalarExpansion
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
private lemma claim_of_scalar_identity
    (hs : ∀ (F : Type) [Field F] [CharZero F] (m l : ℕ), l ≤ m → ∀ u : F,
      scalarEigenvalue m l u = scalarExpansion m l u) : claim := by
  apply claim_of_spectral_obligations ?_ hs
  intro F _ _ m u
  exact transfer_walsh m u
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
namespace D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
open D5.S1.Recurrence.CentralFactorialTransferExpansion
theorem result : claim := by
  apply claim_of_scalar_identity
  intro F _ _ m l hl u
  exact scalar_settlement m l hl u
end D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenTransferExpansion
