/- GID: D5/S3/Quantum/Algebra/WeylCliffordDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylCliffordDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated commutators with a Pauli terminate in the Clifford hierarchy. -/
/-
admission_basis: escape-witness
escape_witness: hierarchy_terminates
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20302.
proof_shape: pauli: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.controlShift_pauli, D5.S3.Quantum.Algebra.WeylCliffordDescent.cliffordHierarchy, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_mul, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_star, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_unitary, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_conjugation, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_right_pauli, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_commutator, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_commutator_scalar, D5.S3.Quantum.Algebra.WeylCliffordDescent.scalar_commutator, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: cliffordHierarchy: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.claim, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_right_pauli, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_commutator, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: tensorWord_star: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_unitary, D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_conjugation, D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_adjoint
proof_shape: tensorWord_smul: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_conjugation, D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_adjoint
proof_shape: wordOperator_zero_phase: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_mul
proof_shape: weyl_mul: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_mul
proof_shape: displacement_unitary: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.weyl_unitary
proof_shape: weyl_unitary: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_unitary
proof_shape: weyl_conjugation: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_conjugation
proof_shape: pauli_mul: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_right_pauli
proof_shape: weyl_adjoint: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_star
proof_shape: pauli_star: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_right_pauli, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_commutator
proof_shape: pauli_unitary: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_right_pauli, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_commutator_scalar, D5.S3.Quantum.Algebra.WeylCliffordDescent.scalar_commutator
proof_shape: pauli_conjugation: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_commutator_scalar
proof_shape: commutator: bind-only; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.commIter_powerBlocks, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_commutator, D5.S3.Quantum.Algebra.WeylCliffordDescent.pauli_commutator_scalar, D5.S3.Quantum.Algebra.WeylCliffordDescent.scalar_commutator, D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: hierarchy_right_pauli: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_commutator
proof_shape: hierarchy_commutator: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: pauli_commutator_scalar: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: scalar_commutator: bind-only; consumers: D5.S3.Quantum.Algebra.WeylCliffordDescent.hierarchy_terminates
proof_shape: hierarchy_terminates: content; consumers: D5.S3.Quantum.Algebra.AndersonWeippertQuditControlledOrder.result
The Pauli predicate contains the tensor expression directly, and wordOperator_zero_phase
connects it to the existing Pauli-word operator used by its proofs.
-/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Algebra.WeylDisplacement
import D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
import D5.S3.Quantum.Algebra.WeylDisplacementConjugation
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
import D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
import D5.S3.Observer.WindowRegister
import D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

namespace D5.S3.Quantum.Algebra.WeylCliffordDescent

open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Recovery.ProductPrefixRigidity
open D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

section Conventions

variable (p : ℕ)


variable [NeZero p]

/-- The Pauli group on `n` qudits: the operators `c • X^a Z^b` with `|c| = 1`. -/
def pauli (n : ℕ) : Set (Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) :=
  {A | ∃ (c : ℂ) (a b : Fin n → ZMod p), ‖c‖ = 1 ∧ A = c • (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k)))}

/-- The Clifford hierarchy on `n` qudits: `CH 1 = pauli`, and `CH (k + 1)` is the set of unitaries `V` with
`V P V† ∈ CH k` for every Pauli `P`. Level `0` is empty. -/
def cliffordHierarchy (n : ℕ) : ℕ → Set (Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ)
  | 0 => ∅
  | 1 => pauli p n
  | k + 2 => {V | V ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ ∧
      ∀ P ∈ pauli p n, V * P * star V ∈ cliffordHierarchy n (k + 1)}

end Conventions

open Matrix D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
open Finset
noncomputable section
variable {p n : ℕ} [NeZero p]

private theorem tensorWord_star (A : Fin n → Matrix (ZMod p) (ZMod p) ℂ) :
    star ((productMap (fun _ : Fin n => ZMod p)) A) = (productMap (fun _ : Fin n => ZMod p)) (fun k => star (A k)) := by
  exact (D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor.tensor_star A).symm

private theorem tensorWord_smul (c : Fin n → ℂ) (A : Fin n → Matrix (ZMod p) (ZMod p) ℂ) :
    (productMap (fun _ : Fin n => ZMod p)) (fun k => c k • A k) = (∏ k, c k) • (productMap (fun _ : Fin n => ZMod p)) A := by
  ext i j
  simp [productMap, Finset.prod_mul_distrib]

private theorem wordOperator_zero_phase (a b : Fin n → ZMod p) :
    pauliWordOperator (⟨0, a, b⟩ : PauliWord n p) =
      productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k)) := by
  simp only [pauliWordOperator, ZMod.val_zero, pow_zero, one_smul]
  rfl

private theorem weyl_mul (a b c d : Fin n → ZMod p) :
    (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k))) * (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (c k) (d k))) =
      (windowRoot p ^ (∑ k, b k * c k).val) • (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p ((a + c) k) ((b + d) k))) := by
  simpa only [wordMul, zero_add, wordOperator_zero_phase] using
    (pauli_word_mul (⟨0, a, b⟩ : PauliWord n p) (⟨0, c, d⟩ : PauliWord n p))

private theorem displacement_unitary (a b : ZMod p) :
    displacement p a b ∈ Matrix.unitaryGroup (ZMod p) ℂ := by
  exact Matrix.mem_unitaryGroup_iff'.mpr
    (D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.displacement_unitary_pair a b).1

private theorem weyl_unitary (a b : Fin n → ZMod p) :
    (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k))) ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change star ((productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (a k) (b k))) *
    (productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (a k) (b k)) = 1
  rw [tensorWord_star]
  have hm :
      productMap (fun _ : Fin n => ZMod p) (fun k => star (displacement p (a k) (b k))) *
        productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k)) =
      productMap (fun _ : Fin n => ZMod p)
        (fun k => star (displacement p (a k) (b k)) * displacement p (a k) (b k)) :=
    coordinate_product_mul _ _
  rw [hm]
  simp_rw [Matrix.mem_unitaryGroup_iff'.mp (displacement_unitary _ _)]
  exact coordinate_product_one

private theorem weyl_conjugation (a b c d : Fin n → ZMod p) :
    (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k))) * (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (c k) (d k))) * star ((productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k)))) =
      (∏ k, windowRoot p ^ (b k * c k - a k * d k).val) • (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (c k) (d k))) := by
  change (productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (a k) (b k)) *
    (productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (c k) (d k)) *
    star ((productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (a k) (b k))) = _
  rw [tensorWord_star]
  have hm (A B : Fin n → Matrix (ZMod p) (ZMod p) ℂ) :
      productMap (fun _ : Fin n => ZMod p) A * productMap (fun _ : Fin n => ZMod p) B =
        productMap (fun _ : Fin n => ZMod p) (fun k => A k * B k) :=
    coordinate_product_mul A B
  rw [hm, hm]
  have hconj (a b c d : ZMod p) :
      displacement p a b * displacement p c d * star (displacement p a b) =
        windowRoot p ^ (b * c - a * d).val • displacement p c d := by
    exact D5.S3.Quantum.Algebra.WeylDisplacementConjugation.displacement_conjugation a b c d
  simp_rw [hconj]
  exact tensorWord_smul _ _

private theorem pauli_mul {A B : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (hA : A ∈ pauli p n) (hB : B ∈ pauli p n) : A * B ∈ pauli p n := by
  obtain ⟨c, a, b, hc, rfl⟩ := hA
  obtain ⟨d, e, f, hd, rfl⟩ := hB
  refine ⟨c * d * windowRoot p ^ (∑ k, b k * e k).val, a + e, b + f, ?_, ?_⟩
  · simp [norm_mul, hc, hd, norm_prod, (windowRoot_isPrimitiveRoot p).norm'_eq_one (NeZero.ne p)]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, weyl_mul, smul_smul]

private theorem weyl_adjoint (a b : Fin n → ZMod p) :
    star ((productMap (fun _ : Fin n => ZMod p) (fun k => displacement p (a k) (b k)))) =
      (∏ k, windowRoot p ^ (a k * b k).val) • (productMap (fun _ : Fin n => ZMod p) (fun k => displacement p ((-a) k) ((-b) k))) := by
  change star ((productMap (fun _ : Fin n => ZMod p)) (fun k => displacement p (a k) (b k))) = _
  rw [tensorWord_star]
  simp_rw [displacement_adjoint]
  exact tensorWord_smul _ _

private theorem pauli_star {A : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (hA : A ∈ pauli p n) : star A ∈ pauli p n := by
  obtain ⟨c, a, b, hc, rfl⟩ := hA
  refine ⟨star c * ∏ k, windowRoot p ^ (a k * b k).val, -a, -b, ?_, ?_⟩
  · simp [norm_mul, hc, norm_prod, (windowRoot_isPrimitiveRoot p).norm'_eq_one (NeZero.ne p)]
  · rw [star_smul, weyl_adjoint, smul_smul]

private theorem pauli_unitary {A : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (hA : A ∈ pauli p n) : A ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ := by
  obtain ⟨c, a, b, hc, rfl⟩ := hA
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mem_unitaryGroup_iff'.mp (weyl_unitary a b)]
  have hc' : star c * c = 1 := by simpa [hc] using RCLike.conj_mul c
  rw [hc', one_smul]

private theorem pauli_conjugation {A B : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (hA : A ∈ pauli p n) (hB : B ∈ pauli p n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ A * B * star A = c • B := by
  obtain ⟨c, a, b, hc, rfl⟩ := hA
  obtain ⟨d, e, f, hd, rfl⟩ := hB
  refine ⟨∏ k, windowRoot p ^ (b k * e k - a k * f k).val, ?_, ?_⟩
  · simp [norm_prod, (windowRoot_isPrimitiveRoot p).norm'_eq_one (NeZero.ne p)]
  · have hc' : c * star c = 1 := by simpa [hc] using RCLike.mul_conj c
    simp only [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      weyl_conjugation]
    congr 1
    calc
      _ =
          (c * star c) * (d * (∏ k, windowRoot p ^ (b k * e k - a k * f k).val)) := by ring
      _ = (∏ k, windowRoot p ^ (b k * e k - a k * f k).val) * d := by rw [hc', one_mul, mul_comm]

end

open Matrix
noncomputable section
variable {p n : ℕ} [NeZero p]

def commutator (V Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ) := V * Q * star V * star Q

private theorem hierarchy_right_pauli {V Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (k : ℕ) (hV : V ∈ cliffordHierarchy p n k) (hQ : Q ∈ pauli p n) :
    V * Q ∈ cliffordHierarchy p n k := by
  cases k with
  | zero => exact hV.elim
  | succ k =>
    cases k with
    | zero => exact pauli_mul hV hQ
    | succ k =>
      change V ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ ∧ _ at hV
      change V * Q ∈ Matrix.unitaryGroup (Fin n → ZMod p) ℂ ∧ _
      refine ⟨(Matrix.unitaryGroup _ ℂ).mul_mem hV.1 (pauli_unitary hQ), ?_⟩
      intro A hA
      have he := hV.2 (Q * A * star Q) (pauli_mul (pauli_mul hQ hA) (pauli_star hQ))
      simpa only [star_mul, mul_assoc] using he

private theorem hierarchy_commutator {V Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (k : ℕ) (hV : V ∈ cliffordHierarchy p n (k + 2)) (hQ : Q ∈ pauli p n) :
    commutator V Q ∈ cliffordHierarchy p n (k + 1) := by
  exact hierarchy_right_pauli (k + 1) (hV.2 Q hQ) (pauli_star hQ)

private theorem pauli_commutator_scalar {V Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (hV : V ∈ pauli p n) (hQ : Q ∈ pauli p n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ commutator V Q = c • 1 := by
  obtain ⟨c, hc, he⟩ := pauli_conjugation hV hQ
  refine ⟨c, hc, ?_⟩
  rw [commutator, he, Matrix.smul_mul, Matrix.mem_unitaryGroup_iff.mp (pauli_unitary hQ)]

private theorem scalar_commutator (c : ℂ) (hc : ‖c‖ = 1)
    {Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ} (hQ : Q ∈ pauli p n) :
    commutator (c • 1) Q = 1 := by
  have hc' : star c * c = 1 := by simpa [hc] using RCLike.conj_mul c
  simp only [commutator, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, one_mul, mul_one]
  rw [hc', one_smul, Matrix.mem_unitaryGroup_iff.mp (pauli_unitary hQ)]

theorem hierarchy_terminates {V Q : Matrix (Fin n → ZMod p) (Fin n → ZMod p) ℂ}
    (k : ℕ) (hV : V ∈ cliffordHierarchy p n k) (hQ : Q ∈ pauli p n) :
    (fun A => commutator A Q)^[k + 1] V = 1 := by
  induction k generalizing V with
  | zero => exact hV.elim
  | succ k ih =>
    cases k with
    | zero =>
      obtain ⟨c, hc, he⟩ := pauli_commutator_scalar hV hQ
      change commutator (commutator V Q) Q = 1
      rw [he]
      exact scalar_commutator c hc hQ
    | succ k =>
      have hd := hierarchy_commutator k hV hQ
      have he := ih hd
      simpa only [Function.iterate_succ_apply] using he

end

end D5.S3.Quantum.Algebra.WeylCliffordDescent
