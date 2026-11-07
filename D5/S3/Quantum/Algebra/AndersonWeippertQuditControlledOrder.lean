/- GID: D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A controlled qudit gate in the Clifford hierarchy has prime-power target order. -/
/-
admission_basis: open-problem-resolution (#19835; Proved)
escape_witness: D5/S3/Arith/Primes/CyclicDifferencePrimeContent.content_prime_power
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20302.
proof_shape: controlled: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.claim, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlled_blocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_initial, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks
proof_shape: claim: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
proof_shape: splitBasis: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_injective, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlPerm
proof_shape: blocks: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_apply, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_one, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_mul, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_star, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.blocks_injective, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_blocks_conjugation, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlled_blocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_eq_one
proof_shape: blocks_apply: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_blocks_conjugation, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlled_blocks
proof_shape: blocks_one: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_eq_one
proof_shape: blocks_mul: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_commutator
proof_shape: blocks_star: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_commutator
proof_shape: blocks_injective: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_eq_one
proof_shape: controlPerm: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlPerm_apply, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_blocks_conjugation, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_pauli, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_commutator, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks
proof_shape: controlPerm_apply: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_blocks_conjugation, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_pauli
proof_shape: controlShift_blocks_conjugation: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_commutator
proof_shape: controlShift_pauli: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
proof_shape: controlled_blocks: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_initial
proof_shape: powerBlocks: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_commutator, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_initial, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.powerBlocks_eq_one, D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
proof_shape: powerBlocks_commutator: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks
proof_shape: powerBlocks_initial: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks
proof_shape: commIter_powerBlocks: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
proof_shape: powerBlocks_eq_one: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
proof_shape: result: content; escape_witness: D5/S3/Arith/Primes/CyclicDifferencePrimeContent.content_prime_power; consumers: settling result
-/

import D5.S3.Arith.Primes.CyclicDifferencePrimeContent
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Algebra.WeylDisplacement
import D5.S3.Observer.WindowRegister
import D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
import D5.S3.Quantum.Algebra.WeylCliffordDescent

namespace D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder

open D5.S3.Quantum.Algebra.WeylCliffordDescent

variable (p : ℕ) [NeZero p]

/-- The controlled gate on `n + 1` qudits with the control at coordinate `0` and the targets at `1, …, n`:
`C(U) = Σ_j |j⟩⟨j| ⊗ U_j` with `U_1 = U` and `U_j = I` for `j ≠ 1`. -/
def controlled {n : ℕ} (U : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :
    Matrix (Fin (n + 1) → ZMod p) (Fin (n + 1) → ZMod p) ℂ :=
  fun i j => if i 0 = j 0 then
      (if i 0 = 1 then U (Fin.tail i) (Fin.tail j)
        else (1 : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) (Fin.tail i) (Fin.tail j))
    else 0


/-- The open problem of Section 4: for a prime `p` and a unitary `U` on `n` qudits, if `C(U)` lies in some level of
the Clifford hierarchy, then `U` has order `p^m` for some `m`. -/
def claim : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n : ℕ),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∀ U : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ, U ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ →
      (∃ k, controlled p U ∈ cliffordHierarchy p (n + 1) k) → ∃ m : ℕ, orderOf U = p ^ m


open Matrix D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open Finset
noncomputable section
variable {p n : ℕ} [NeZero p]

private def splitBasis (p n : ℕ) : (Fin (n + 1) → ZMod p) ≃ (Fin n → ZMod p) × ZMod p :=
  (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod p)).symm.trans (Equiv.prodComm _ _)

private def blocks (V : ZMod p → Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :
    Matrix (Fin (n + 1) → ZMod p) (Fin (n + 1) → ZMod p) ℂ :=
  (Matrix.blockDiagonal V).submatrix (splitBasis p n) (splitBasis p n)

private theorem blocks_apply (V : ZMod p → Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)
    (i j : (Fin (n + 1) → ZMod p)) :
    blocks V i j = if i 0 = j 0 then V (i 0) (Fin.tail i) (Fin.tail j) else 0 := by
  exact rfl

private theorem blocks_one : blocks (fun _ : ZMod p => (1 : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)) = 1 := by
  simp [blocks, ← Pi.one_def]

private theorem blocks_mul (V W : ZMod p → Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :
    blocks V * blocks W = blocks (fun j => V j * W j) := by
  simp only [blocks, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

private theorem blocks_star (V : ZMod p → Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :
    star (blocks V) = blocks (fun j => star (V j)) := by
  simp only [blocks, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.blockDiagonal_conjTranspose]

private theorem blocks_injective : Function.Injective
    (blocks (p := p) (n := n)) := by
  unfold blocks
  exact (Matrix.submatrix_injective (splitBasis p n).surjective
    (splitBasis p n).surjective).comp Matrix.blockDiagonal_injective

private def controlPerm (p n : ℕ) : Equiv.Perm (Fin (n + 1) → ZMod p) :=
  (splitBasis p n).trans
    ((Equiv.refl (Fin n → ZMod p)).prodCongr (Equiv.subRight (1 : ZMod p))) |>.trans
      (splitBasis p n).symm

private theorem controlPerm_apply (i : (Fin (n + 1) → ZMod p)) :
    controlPerm p n i = Fin.cons (i 0 - 1) (Fin.tail i) := by
  exact rfl

private theorem controlShift_blocks_conjugation
    (V : ZMod p → Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :
    ((controlPerm p n).permMatrix ℂ) * blocks V * star (((controlPerm p n).permMatrix ℂ)) =
      blocks (fun j => V (j - 1)) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  change blocks V (controlPerm p n i) (controlPerm p n j) = _
  simp [blocks_apply, controlPerm_apply]

private theorem controlShift_pauli (hp : 1 < p) : ((controlPerm p n).permMatrix ℂ) ∈ pauli p (n + 1) := by
  letI : Fact (1 < p) := ⟨hp⟩
  refine ⟨1, Fin.cons 1 0, 0, norm_one, ?_⟩
  rw [one_smul]
  ext i j
  simp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply,
    displacement_zero]
  have htail : (∏ k : Fin n, (1 : Matrix (ZMod p) (ZMod p) ℂ) (i k.succ) (j k.succ)) =
      (1 : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) (Fin.tail i) (Fin.tail j) := by
    exact congrFun (congrFun (D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.coordinate_product_one (ι := Fin n) (α := ZMod p)) (Fin.tail i)) (Fin.tail j)
  rw [htail]
  simp only [displacement, ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one,
    shiftMatrix, Matrix.circulant_apply, Matrix.one_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, controlPerm_apply]
  have hpermiff : Fin.cons (i 0 - 1) (Fin.tail i) = j ↔
      i 0 - 1 = j 0 ∧ Fin.tail i = Fin.tail j := by
    simpa only [Fin.cons_self_tail] using
      (Fin.cons_inj (x₀ := i 0 - 1) (y₀ := j 0) (x := Fin.tail i) (y := Fin.tail j))
  have hrel : i 0 - j 0 = 1 ↔ i 0 - 1 = j 0 := by
    exact sub_eq_iff_comm
  simp only [hpermiff, hrel]
  by_cases hc : i 0 - 1 = j 0 <;> by_cases ht : Fin.tail i = Fin.tail j <;>
    simp [hc, ht]

private theorem controlled_blocks {U : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ} :
    controlled p U = blocks (fun j => if j = 1 then U else 1) := by
  ext i j
  simp only [controlled, blocks_apply]
  split_ifs <;> rfl

private def powerBlocks (u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ) (v : ZMod p → ℤ) :
    Matrix (Fin (n + 1) → ZMod p) (Fin (n + 1) → ZMod p) ℂ :=
  blocks (fun j => ↑(u ^ v j))

private theorem powerBlocks_commutator (u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ)
    (v : ZMod p → ℤ) :
    powerBlocks u v * ((controlPerm p n).permMatrix ℂ) * star (powerBlocks u v) * star (((controlPerm p n).permMatrix ℂ)) =
      powerBlocks u ((fun j => v j - v (j - 1))) := by
  rw [mul_assoc (powerBlocks u v) (((controlPerm p n).permMatrix ℂ)),
    mul_assoc (powerBlocks u v) (((controlPerm p n).permMatrix ℂ) * star (powerBlocks u v))]
  simp only [powerBlocks, blocks_star]
  rw [controlShift_blocks_conjugation, blocks_mul]
  congr 1
  funext j
  change (↑(u ^ v j) : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) *
    star (↑(u ^ v (j - 1)) : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) =
      (↑(u ^ (v j - v (j - 1))) : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)
  rw [_root_.zpow_sub]
  rfl

end

open Matrix
noncomputable section
variable {p n : ℕ} [NeZero p]

private theorem powerBlocks_initial (u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ) :
    powerBlocks u (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff p 0) = controlled p (↑u) := by
  rw [controlled_blocks]
  unfold powerBlocks
  congr 1
  funext j
  by_cases hj : j = 1 <;> simp [D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff, hj]

private theorem commIter_powerBlocks (u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ) (r : ℕ) :
    (fun A => commutator A ((controlPerm p n).permMatrix ℂ))^[r] (controlled p (↑u)) =
      powerBlocks u (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff p r) := by
  have hs : Function.Semiconj
      (fun s : ℕ => powerBlocks u (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff p s))
      (· + 1) (fun A => commutator A ((controlPerm p n).permMatrix ℂ)) := by
    intro s
    exact (powerBlocks_commutator u
      (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff p s)).symm
  simpa only [add_right_iterate, nsmul_eq_mul, Nat.cast_id, mul_one, zero_add,
    powerBlocks_initial] using ((hs.iterate_right r) 0).symm

private theorem powerBlocks_eq_one (u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ)
    (v : ZMod p → ℤ) (h : powerBlocks u v = 1) : ∀ j, u ^ v j = 1 := by
  have he : blocks (p := p) (n := n)
      (fun j => (↑(u ^ v j) : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)) =
      blocks (fun _ => (1 : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)) := by
    simpa only [powerBlocks, blocks_one] using h
  have hf := blocks_injective he
  intro j
  apply Subtype.ext
  exact congrFun hf j

theorem result : claim := by
  intro p hp n
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro U hU hCH
  let u : Matrix.unitaryGroup (Fin n → ZMod p) ℂ := ⟨U, hU⟩
  obtain ⟨k, hk⟩ := hCH
  have ht := hierarchy_terminates k hk (controlShift_pauli (n := n) hp.one_lt)
  have hb : powerBlocks u (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.coeff p (k + 1)) = 1 := by
    rw [← commIter_powerBlocks]
    exact ht
  have he := powerBlocks_eq_one u _ hb
  obtain ⟨m, hm⟩ := D5.S3.Arith.Primes.CyclicDifferencePrimeContent.order_prime_power_of_coeff hp u k he
  refine ⟨m, ?_⟩
  exact (orderOf_submonoid u).trans hm

end

end D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder
