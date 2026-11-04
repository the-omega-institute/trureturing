/- GID: D5/S3/Quantum/CampoamorStursbergZernikeLadder
   generality: I
   mirror-B: D5/B/S3/Quantum/CampoamorStursbergZernikeLadder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All polynomial Zernike Hamiltonians have factorized ladder operators. -/

/-
result: proof_shape: content; escape_witness: none.
admission_basis: open-problem-resolution (#19957; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21497
The operator type is written in full; k1 is the source's angular momentum generator.
-/

import D5.S3.Quantum.CampoamorStursbergZernikeLadderCore
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore
/-- Conjecture 1 (iii), with the quantum symmetries of Conjecture 1 (i): for every `N ≥ 1` and all coefficients,
there are symmetries `Î_N`, `Î'_N` of the form (2.6), and operators `K̂`, `K̂₊`, `K̂₋` built from `K̂₁, K̂₂, K̂₃`
that satisfy (2.9) and (2.10) with the factorizing terms (5.1). -/
def claim : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ γ : ℕ → ℂ, ∃ I I' : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)),
    IsSymmetry N γ (p 1 ^ 2) I ∧ IsSymmetry N γ (p 0 ^ 2) I' ∧
    ∃ K ∈ Algebra.adjoin ℂ {k1, k2 I I', k3 I I'},
    ∃ Kp ∈ Algebra.adjoin ℂ {k1, k2 I I', k3 I I'},
    ∃ Km ∈ Algebra.adjoin ℂ {k1, k2 I I', k3 I I'},
      K * Kp - Kp * K = Kp ∧ K * Km - Km * K = -Km ∧
      Kp * Km = phi N γ (hamiltonian N γ) K ∧
      Km * Kp - Kp * Km = phi N γ (hamiltonian N γ) (K + 1) - phi N γ (hamiltonian N γ) K

end D5.S3.Quantum.CampoamorStursbergZernikeLadder

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl MvPolynomial

private noncomputable def x : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := p 0 + Complex.I • p 1
private noncomputable def y : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := p 0 - Complex.I • p 1
private noncomputable def qp : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := q 0 + Complex.I • q 1
private noncomputable def qm : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := q 0 - Complex.I • q 1

private theorem prod_p (i j k : Fin 2) :
    (q i * p j) * p k - p k * (q i * p j) =
      (if k = i then Complex.I else 0) • p j := by
  calc
    _ = q i * (p j * p k) - (p k * q i) * p j := by noncomm_ring
    _ = _ := by
      rw [pp j k, pq k i]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

private theorem prod_q (i j k : Fin 2) :
    (q i * p j) * q k - q k * (q i * p j) =
      -((if j = k then Complex.I else 0) • q i) := by
  calc
    _ = q i * (p j * q k) - (q k * q i) * p j := by noncomm_ring
    _ = _ := by
      rw [pq j k, qq k i]
      simp only [mul_sub, mul_smul_comm, mul_one]
      noncomm_ring

private theorem Dp (k : Fin 2) : dot * p k - p k * dot = Complex.I • p k := by
  unfold dot
  calc
    _ = ((q 0 * p 0) * p k - p k * (q 0 * p 0)) +
        ((q 1 * p 1) * p k - p k * (q 1 * p 1)) := by simp only [sub_mul, mul_sub, add_mul, mul_add]; abel
    _ = _ := by rw [prod_p, prod_p]; fin_cases k <;> simp <;> module

private theorem Dq (k : Fin 2) : dot * q k - q k * dot = -Complex.I • q k := by
  unfold dot
  calc
    _ = ((q 0 * p 0) * q k - q k * (q 0 * p 0)) +
        ((q 1 * p 1) * q k - q k * (q 1 * p 1)) := by simp only [sub_mul, mul_sub, add_mul, mul_add]; abel
    _ = _ := by rw [prod_q, prod_q]; fin_cases k <;> simp <;> module

private theorem Cp (k : Fin 2) : angularMomentum * p k - p k * angularMomentum =
    if k = 0 then Complex.I • p 1 else -Complex.I • p 0 := by
  unfold angularMomentum
  calc
    _ = ((q 0 * p 1) * p k - p k * (q 0 * p 1)) -
        ((q 1 * p 0) * p k - p k * (q 1 * p 0)) := by simp only [sub_mul, mul_sub, add_mul, mul_add]; abel
    _ = _ := by rw [prod_p, prod_p]; fin_cases k <;> simp <;> module

private theorem Cq (k : Fin 2) : angularMomentum * q k - q k * angularMomentum =
    if k = 0 then Complex.I • q 1 else -Complex.I • q 0 := by
  unfold angularMomentum
  calc
    _ = ((q 0 * p 1) * q k - q k * (q 0 * p 1)) -
        ((q 1 * p 0) * q k - q k * (q 1 * p 0)) := by simp only [sub_mul, mul_sub, add_mul, mul_add]; abel
    _ = _ := by rw [prod_q, prod_q]; fin_cases k <;> simp <;> module

private theorem comm_add (A B C : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : A * (B + C) - (B + C) * A =
    (A * B - B * A) + (A * C - C * A) := by
  letI : LieRing (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LieRing.ofAssociativeRing
  simpa only [Ring.lie_def] using (lie_add A B C)
private theorem comm_sub (A B C : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : A * (B - C) - (B - C) * A =
    (A * B - B * A) - (A * C - C * A) := by
  letI : LieRing (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LieRing.ofAssociativeRing
  simpa only [Ring.lie_def] using (lie_sub A B C)
private theorem comm_smul (A B : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (c : ℂ) : A * (c • B) - (c • B) * A =
    c • (A * B - B * A) := by
  letI : LieRing (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LieRing.ofAssociativeRing
  simpa only [Ring.lie_def] using (lie_smul c A B)

private theorem Dx : dot * x - x * dot = Complex.I • x := by
  unfold x
  rw [comm_add, comm_smul, Dp, Dp]
  module
private theorem Dy : dot * y - y * dot = Complex.I • y := by
  unfold y
  rw [comm_sub, comm_smul, Dp, Dp]
  module
private theorem Dqp : dot * qp - qp * dot = -Complex.I • qp := by
  unfold qp
  rw [comm_add, comm_smul, Dq, Dq]
  module
private theorem Dqm : dot * qm - qm * dot = -Complex.I • qm := by
  unfold qm
  rw [comm_sub, comm_smul, Dq, Dq]
  module
private theorem Cx : angularMomentum * x - x * angularMomentum = x := by
  unfold x
  rw [comm_add, comm_smul, Cp, Cp]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by exact Fin.zero_ne_one.symm, ite_false,
    smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module
private theorem Cy : angularMomentum * y - y * angularMomentum = -y := by
  unfold y
  rw [comm_sub, comm_smul, Cp, Cp]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by exact Fin.zero_ne_one.symm, ite_false,
    smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module
private theorem Cqp : angularMomentum * qp - qp * angularMomentum = qp := by
  unfold qp
  rw [comm_add, comm_smul, Cq, Cq]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by exact Fin.zero_ne_one.symm, ite_false,
    smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module
private theorem Cqm : angularMomentum * qm - qm * angularMomentum = -qm := by
  unfold qm
  rw [comm_sub, comm_smul, Cq, Cq]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by exact Fin.zero_ne_one.symm, ite_false,
    smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module

private theorem xy : x * y = p 0 ^ 2 + p 1 ^ 2 := by
  unfold x y
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, Complex.I_mul_I, pp 1 0, pow_two]
  module

private theorem yqp : y * qp = dot - Complex.I • (angularMomentum + 2) := by
  unfold y qp dot angularMomentum
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_smul, Complex.I_mul_I]
  rw [pq 0 0, pq 0 1, pq 1 0, pq 1 1]
  simp only [ite_true, ite_false, zero_smul, sub_zero, smul_add, smul_sub, smul_smul,
    Complex.I_mul_I, smul_neg, neg_smul]
  simp only [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm, smul_add]
  simp <;> module

private theorem xqm : x * qm = dot - Complex.I • (2 - angularMomentum) := by
  unfold x qm dot angularMomentum
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_smul, Complex.I_mul_I]
  rw [pq 0 0, pq 0 1, pq 1 0, pq 1 1]
  simp only [ite_true, ite_false, zero_smul, sub_zero, smul_add, smul_sub, smul_smul,
    Complex.I_mul_I, smul_neg, neg_smul]
  simp only [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm, smul_add]
  simp <;> module

private theorem comm_mul (A B C : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : A * (B * C) - (B * C) * A =
    (A * B - B * A) * C + B * (A * C - C * A) := by
  simp only [mul_sub, sub_mul, mul_assoc]
  abel
private theorem comm_sub_left (A B C : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (A - B) * C - C * (A - B) =
    (A * C - C * A) - (B * C - C * B) := by
  letI : LieRing (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LieRing.ofAssociativeRing
  simpa only [Ring.lie_def] using (sub_lie A B C)
private theorem comm_smul_left (A B : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (c : ℂ) : (c • A) * B - B * (c • A) =
    c • (A * B - B * A) := by
  letI : LieRing (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LieRing.ofAssociativeRing
  simpa only [Ring.lie_def] using (smul_lie c A B)
private theorem right_shift (A B : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (c : ℂ) (h : A * B - B * A = c • B) :
    A * B = B * (A + c • 1) := by
  rw [mul_add, mul_smul_comm, mul_one]
  rw [sub_eq_iff_eq_add.mp h]
  module

private theorem DC : Commute dot angularMomentum := by
  change dot * angularMomentum = angularMomentum * dot
  apply sub_eq_zero.mp
  unfold angularMomentum
  rw [comm_sub, comm_mul, comm_mul, Dq, Dp, Dq, Dp]
  simp only [smul_mul_assoc, mul_smul_comm]
  module

private theorem DU : Commute dot (x * qp) := by
  change dot * (x * qp) = (x * qp) * dot
  apply sub_eq_zero.mp
  rw [comm_mul, Dx, Dqp]
  simp only [smul_mul_assoc, mul_smul_comm]
  module
private theorem DV : Commute dot (y * qm) := by
  change dot * (y * qm) = (y * qm) * dot
  apply sub_eq_zero.mp
  rw [comm_mul, Dy, Dqm]
  simp only [smul_mul_assoc, mul_smul_comm]
  module
private theorem CT : Commute angularMomentum (x * y) := by
  change angularMomentum * (x * y) = (x * y) * angularMomentum
  apply sub_eq_zero.mp
  rw [comm_mul, Cx, Cy]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    LinearMap.smul_apply, Module.End.mul_apply, map_neg]
  module
private theorem CU : angularMomentum * (x * qp) - (x * qp) * angularMomentum =
    (2 : ℂ) • (x * qp) := by
  rw [comm_mul, Cx, Cqp]
  module
private theorem CV : angularMomentum * (y * qm) - (y * qm) * angularMomentum =
    (-2 : ℂ) • (y * qm) := by
  rw [comm_mul, Cy, Cqm]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    LinearMap.smul_apply, Module.End.mul_apply, map_neg]
  module
private theorem CR : angularMomentum * (x * x) - (x * x) * angularMomentum =
    (2 : ℂ) • (x * x) := by rw [comm_mul, Cx]; module
private theorem CS : angularMomentum * (y * y) - (y * y) * angularMomentum =
    (-2 : ℂ) • (y * y) := by
  rw [comm_mul, Cy]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    LinearMap.smul_apply, Module.End.mul_apply, map_neg]
  module
private theorem DT : dot * (x * y) = (x * y) * (dot + (2 * Complex.I) • 1) := by
  apply right_shift
  rw [comm_mul, Dx, Dy]
  simp only [smul_mul_assoc, mul_smul_comm]
  module
private theorem DR : dot * (x * x) = (x * x) * (dot + (2 * Complex.I) • 1) := by
  apply right_shift
  rw [comm_mul, Dx]
  simp only [smul_mul_assoc, mul_smul_comm]
  module
private theorem DS : dot * (y * y) = (y * y) * (dot + (2 * Complex.I) • 1) := by
  apply right_shift
  rw [comm_mul, Dy]
  simp only [smul_mul_assoc, mul_smul_comm]
  module

private theorem qpy : qp * y = dot - Complex.I • angularMomentum := by
  unfold qp y dot angularMomentum
  simp only [add_mul, mul_sub, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  module
private theorem qmx : qm * x = dot + Complex.I • angularMomentum := by
  unfold qm x dot angularMomentum
  simp only [add_mul, mul_sub, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  module
private theorem xqp_comm : x * qp = qp * x := by
  unfold x qp
  simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    smul_smul, Complex.I_mul_I]
  rw [pq 0 0, pq 0 1, pq 1 0, pq 1 1]
  simp [smul_add, smul_sub, smul_smul, Complex.I_mul_I] <;> module
private theorem yqm_comm : y * qm = qm * y := by
  unfold y qm
  simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_smul, Complex.I_mul_I]
  rw [pq 0 0, pq 0 1, pq 1 0, pq 1 1]
  simp [smul_add, smul_sub, smul_smul, Complex.I_mul_I] <;> module

private theorem xy_comm : Commute x y := by
  unfold x y
  change _ = _
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc,
    smul_smul, smul_add, smul_sub, Complex.I_mul_I, pp 1 0]
  module
private theorem TR : (x * y) * (x * x) = (x * x) * (x * y) := by
  simpa only [pow_two] using
    (((Commute.refl x).mul_right xy_comm).pow_left 2).symm.eq

private theorem UT : (x * qp) * (x * y) = (x * x) * (dot - Complex.I • angularMomentum) := by
  calc
    _ = x * ((qp * x) * y) := by simp only [mul_assoc]
    _ = x * ((x * qp) * y) := by rw [← xqp_comm]
    _ = (x * x) * (qp * y) := by simp only [mul_assoc]
    _ = _ := by rw [qpy]

private theorem yqp_clear : y * qp = dot - Complex.I • angularMomentum -
    (2 * Complex.I) • 1 := by
  rw [yqp]
  rw [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm]
  simp only [smul_add]
  module

private theorem TU : (x * y) * (x * qp) = (x * qp) * (x * y) -
    (2 * Complex.I) • (x * x) := by
  have h : (x * y) * (x * qp) = (x * x) * (y * qp) := by
    rw [mul_assoc x y, ← mul_assoc y x, xy_comm.symm.eq]
    simp only [mul_assoc]
  rw [h, yqp_clear, UT]
  simp only [mul_sub, mul_smul_comm, mul_one]

private theorem DminusA_qm : Commute (dot - Complex.I • angularMomentum) qm := by
  change _ = _
  apply sub_eq_zero.mp
  rw [comm_sub_left, comm_smul_left, Dqm, Cqm]
  module

private theorem UV : (x * qp) * (y * qm) =
    (dot - Complex.I • (2 - angularMomentum)) * (dot - Complex.I • angularMomentum) := by
  calc
    _ = x * ((qp * y) * qm) := by simp only [mul_assoc]
    _ = x * ((dot - Complex.I • angularMomentum) * qm) := by rw [qpy]
    _ = x * (qm * (dot - Complex.I • angularMomentum)) := by rw [DminusA_qm.eq]
    _ = (x * qm) * (dot - Complex.I • angularMomentum) := by simp only [mul_assoc]
    _ = _ := by rw [xqm]

private theorem DminusA_y : (dot - Complex.I • angularMomentum) * y =
    y * (dot + (2 * Complex.I) • 1 - Complex.I • angularMomentum) := by
  have h : (dot - Complex.I • angularMomentum) * y -
      y * (dot - Complex.I • angularMomentum) = (2 * Complex.I) • y := by
    rw [comm_sub_left, comm_smul_left, Dy, Cy]
    module
  rw [right_shift _ _ _ h]
  apply congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => y * Z)
  module

private theorem US : (x * qp) * (y * y) =
    (x * y) * (dot + (2 * Complex.I) • 1 - Complex.I • angularMomentum) := by
  calc
    _ = x * ((qp * y) * y) := by simp only [mul_assoc]
    _ = x * ((dot - Complex.I • angularMomentum) * y) := by rw [qpy]
    _ = _ := by rw [DminusA_y]; simp only [mul_assoc]

private theorem RV : (x * x) * (y * qm) =
    (x * y) * (dot - Complex.I • (2 - angularMomentum)) := by
  calc
    _ = x * ((x * y) * qm) := by simp only [mul_assoc]
    _ = x * ((y * x) * qm) := by rw [xy_comm.eq]
    _ = (x * y) * (x * qm) := by simp only [mul_assoc]
    _ = _ := by rw [xqm]

private theorem RS : (x * x) * (y * y) = (x * y) * (x * y) := by
  simpa only [pow_two] using (xy_comm.mul_pow 2).symm

private theorem ES : (Complex.I • angularMomentum + (2 * Complex.I) • 1) * (y * y) =
    (y * y) * (Complex.I • angularMomentum) := by
  have h : (Complex.I • angularMomentum) * (y * y) -
      (y * y) * (Complex.I • angularMomentum) = (-2 * Complex.I) • (y * y) := by
    rw [comm_smul_left, CS, smul_smul]
    congr 1
    ring
  rw [add_mul, sub_eq_iff_eq_add.mp h]
  simp only [smul_mul_assoc, one_mul]
  module

private theorem EV : (Complex.I • angularMomentum + (2 * Complex.I) • 1) * (y * qm) =
    (y * qm) * (Complex.I • angularMomentum) := by
  have h : (Complex.I • angularMomentum) * (y * qm) -
      (y * qm) * (Complex.I • angularMomentum) = (-2 * Complex.I) • (y * qm) := by
    rw [comm_smul_left, CV, smul_smul]
    congr 1
    ring
  rw [add_mul, sub_eq_iff_eq_add.mp h]
  simp only [smul_mul_assoc, one_mul]
  module

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff

private noncomputable def raising (N : ℕ) (γ : ℕ → ℂ) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  (1 / 2 : ℂ) • (x ^ 2 + (x * qp) * divided N γ dot (Complex.I • (angularMomentum + 2)))
private noncomputable def lowering (N : ℕ) (γ : ℕ → ℂ) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  (1 / 2 : ℂ) • (y ^ 2 + (y * qm) * divided N γ dot (Complex.I • (2 - angularMomentum)))

private theorem ep_eq : Complex.I • (angularMomentum + 2) =
    Complex.I • angularMomentum + (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) := by
  rw [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm]
  simp only [smul_add]
  module
private theorem em_eq : Complex.I • (2 - angularMomentum) =
    (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) - Complex.I • angularMomentum := by
  rw [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm]
  simp only [smul_add, smul_sub]
  module
private theorem hamiltonian_eq (N : ℕ) (γ : ℕ → ℂ) :
    hamiltonian N γ = x * y + peval N γ dot := by rw [xy]; rfl

private theorem raising_commutes (N : ℕ) (γ : ℕ → ℂ) :
    hamiltonian N γ * raising N γ = raising N γ * hamiltonian N γ := by
  have h := D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.HamiltonianIdentity.symmetry N γ (2 * Complex.I)
    dot (Complex.I • angularMomentum) (x * y) (x * x) (x * qp)
    (DC.smul_right Complex.I) DU DT (CT.smul_left Complex.I).eq DR TR TU UT
  have hh := congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => (1 / 2 : ℂ) • Z) h
  simpa only [raising, hamiltonian_eq, ep_eq, pow_two,
    mul_smul_comm, smul_mul_assoc] using hh

private theorem raising_lowering_product (N : ℕ) (γ : ℕ → ℂ) :
    raising N γ * lowering N γ = (1 / 4 : ℂ) •
      ((hamiltonian N γ - peval N γ (Complex.I • angularMomentum)) *
        (hamiltonian N γ - peval N γ (Complex.I • (2 - angularMomentum)))) := by
  have huv : (x * qp) * (y * qm) =
      (dot - ((2 * Complex.I) • 1 - Complex.I • angularMomentum)) *
        (dot - Complex.I • angularMomentum) := by
    simpa only [em_eq] using UV
  have hrv : (x * x) * (y * qm) =
      (x * y) * (dot - ((2 * Complex.I) • 1 - Complex.I • angularMomentum)) := by
    simpa only [em_eq] using RV
  have h := D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.ProductIdentity.factorization N γ (2 * Complex.I)
    dot (Complex.I • angularMomentum) (x * y) (x * x) (y * y) (x * qp) (y * qm)
    (DC.smul_right Complex.I) DS ES DV.eq EV DT (CT.smul_left Complex.I).eq
    RS hrv US huv
  have hh := congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => (1 / 4 : ℂ) • Z) h
  simpa only [raising, lowering, hamiltonian_eq, ep_eq, em_eq, pow_two,
    smul_mul_smul_comm, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num] using hh

private theorem C_raising (N : ℕ) (γ : ℕ → ℂ) :
    angularMomentum * raising N γ - raising N γ * angularMomentum =
      (2 : ℂ) • raising N γ := by
  let Q := divided N γ dot (Complex.I • (angularMomentum + 2))
  have hCE : Commute angularMomentum (Complex.I • (angularMomentum + 2)) := by
    rw [ep_eq]
    exact ((Commute.refl angularMomentum).smul_right Complex.I).add_right
      ((Commute.one_right angularMomentum).smul_right (2 * Complex.I))
  have hCQ : Commute angularMomentum Q :=
    divided_commute_left N γ _ _ _ DC.symm hCE
  have h : angularMomentum * (x * x + (x * qp) * Q) -
      (x * x + (x * qp) * Q) * angularMomentum =
        (2 : ℂ) • (x * x + (x * qp) * Q) := by
    rw [comm_add, CR, comm_mul, CU, sub_eq_zero.mpr hCQ.eq]
    simp only [mul_zero, add_zero, smul_mul_assoc]
    module
  calc
    _ = (1 / 2 : ℂ) • (angularMomentum * (x * x + (x * qp) * Q) -
      (x * x + (x * qp) * Q) * angularMomentum) := by
      simp only [raising, pow_two, Q, mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = _ := by rw [h]; simp only [raising, pow_two, Q]; module

private theorem C_lowering (N : ℕ) (γ : ℕ → ℂ) :
    angularMomentum * lowering N γ - lowering N γ * angularMomentum =
      (-2 : ℂ) • lowering N γ := by
  let Q := divided N γ dot (Complex.I • (2 - angularMomentum))
  have hCE : Commute angularMomentum (Complex.I • (2 - angularMomentum)) := by
    rw [em_eq]
    exact ((Commute.one_right angularMomentum).smul_right (2 * Complex.I)).sub_right
      ((Commute.refl angularMomentum).smul_right Complex.I)
  have hCQ : Commute angularMomentum Q :=
    divided_commute_left N γ _ _ _ DC.symm hCE
  have h : angularMomentum * (y * y + (y * qm) * Q) -
      (y * y + (y * qm) * Q) * angularMomentum =
        (-2 : ℂ) • (y * y + (y * qm) * Q) := by
    rw [comm_add, CS, comm_mul, CV, sub_eq_zero.mpr hCQ.eq]
    simp only [mul_zero, add_zero, smul_mul_assoc]
    module
  calc
    _ = (1 / 2 : ℂ) • (angularMomentum * (y * y + (y * qm) * Q) -
      (y * y + (y * qm) * Q) * angularMomentum) := by
      simp only [lowering, pow_two, Q, mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = _ := by rw [h]; simp only [lowering, pow_two, Q]; module

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff

private theorem VT : (y * qm) * (x * y) = (y * y) * (dot + Complex.I • angularMomentum) := by
  calc
    _ = (y * qm) * (y * x) := by rw [xy_comm.eq]
    _ = y * ((qm * y) * x) := by simp only [mul_assoc]
    _ = y * ((y * qm) * x) := by rw [← yqm_comm]
    _ = (y * y) * (qm * x) := by simp only [mul_assoc]
    _ = _ := by rw [qmx]

private theorem xqm_clear : x * qm = dot + Complex.I • angularMomentum -
    (2 * Complex.I) • 1 := by
  rw [xqm]
  rw [show (2 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) = 1 + 1 by exact one_add_one_eq_two.symm]
  simp only [smul_sub, smul_add]
  module

private theorem TV : (x * y) * (y * qm) = (y * qm) * (x * y) -
    (2 * Complex.I) • (y * y) := by
  have h : (x * y) * (y * qm) = (y * y) * (x * qm) := by
    calc
      _ = (y * x) * (y * qm) := by rw [xy_comm.eq]
      _ = y * ((x * y) * qm) := by simp only [mul_assoc]
      _ = y * ((y * x) * qm) := by rw [xy_comm.eq]
      _ = _ := by simp only [mul_assoc]
  rw [h, xqm_clear, VT]
  simp only [mul_sub, mul_add, mul_smul_comm, mul_one]

private theorem TS : (x * y) * (y * y) = (y * y) * (x * y) := by
  simpa only [pow_two] using
    ((xy_comm.symm.mul_right (Commute.refl y)).pow_left 2).symm.eq

private theorem DplusA_qp : Commute (dot + Complex.I • angularMomentum) qp := by
  change _ = _
  apply sub_eq_zero.mp
  have h : (dot + Complex.I • angularMomentum) * qp -
      qp * (dot + Complex.I • angularMomentum) =
      (dot * qp - qp * dot) + Complex.I • (angularMomentum * qp - qp * angularMomentum) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
    abel
  rw [h, Dqp, Cqp]
  module

private theorem DplusA_x : (dot + Complex.I • angularMomentum) * x =
    x * (dot + (2 * Complex.I) • 1 + Complex.I • angularMomentum) := by
  have h : (dot + Complex.I • angularMomentum) * x -
      x * (dot + Complex.I • angularMomentum) = (2 * Complex.I) • x := by
    have he : (dot + Complex.I • angularMomentum) * x -
        x * (dot + Complex.I • angularMomentum) =
        (dot * x - x * dot) + Complex.I • (angularMomentum * x - x * angularMomentum) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
      abel
    rw [he, Dx, Cx]
    module
  rw [right_shift _ _ _ h]
  apply congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => x * Z)
  module

private theorem VU : (y * qm) * (x * qp) =
    (dot - ((2 * Complex.I) • 1 + Complex.I • angularMomentum)) *
      (dot + Complex.I • angularMomentum) := by
  calc
    _ = y * ((qm * x) * qp) := by simp only [mul_assoc]
    _ = y * ((dot + Complex.I • angularMomentum) * qp) := by rw [qmx]
    _ = y * (qp * (dot + Complex.I • angularMomentum)) := by rw [DplusA_qp.eq]
    _ = (y * qp) * (dot + Complex.I • angularMomentum) := by simp only [mul_assoc]
    _ = _ := by rw [yqp_clear]; congr 1; module

private theorem VR : (y * qm) * (x * x) =
    (x * y) * (dot + (2 * Complex.I) • 1 + Complex.I • angularMomentum) := by
  calc
    _ = y * ((qm * x) * x) := by simp only [mul_assoc]
    _ = y * ((dot + Complex.I • angularMomentum) * x) := by rw [qmx]
    _ = (y * x) * (dot + (2 * Complex.I) • 1 + Complex.I • angularMomentum) := by
      rw [DplusA_x]; simp only [mul_assoc]
    _ = _ := by rw [xy_comm.symm.eq]

private theorem SU : (y * y) * (x * qp) =
    (x * y) * (dot - ((2 * Complex.I) • 1 + Complex.I • angularMomentum)) := by
  calc
    _ = y * ((y * x) * qp) := by simp only [mul_assoc]
    _ = y * ((x * y) * qp) := by rw [xy_comm.symm.eq]
    _ = (y * x) * (y * qp) := by simp only [mul_assoc]
    _ = _ := by rw [xy_comm.symm.eq, yqp_clear]; congr 1; module

private theorem SR : (y * y) * (x * x) = (x * y) * (x * y) := by
  simpa only [pow_two, xy_comm.eq] using (xy_comm.symm.mul_pow 2).symm

private theorem ER : ((-Complex.I) • angularMomentum + (2 * Complex.I) • 1) * (x * x) =
    (x * x) * ((-Complex.I) • angularMomentum) := by
  have h : ((-Complex.I) • angularMomentum) * (x * x) -
      (x * x) * ((-Complex.I) • angularMomentum) = (-2 * Complex.I) • (x * x) := by
    rw [comm_smul_left, CR, smul_smul]
    congr 1
    ring
  rw [add_mul, sub_eq_iff_eq_add.mp h]
  simp only [smul_mul_assoc, one_mul]
  module

private theorem EU : ((-Complex.I) • angularMomentum + (2 * Complex.I) • 1) * (x * qp) =
    (x * qp) * ((-Complex.I) • angularMomentum) := by
  have h : ((-Complex.I) • angularMomentum) * (x * qp) -
      (x * qp) * ((-Complex.I) • angularMomentum) = (-2 * Complex.I) • (x * qp) := by
    rw [comm_smul_left, CU, smul_smul]
    congr 1
    ring
  rw [add_mul, sub_eq_iff_eq_add.mp h]
  simp only [smul_mul_assoc, one_mul]
  module

set_option maxHeartbeats 800000 in
private theorem lowering_commutes (N : ℕ) (γ : ℕ → ℂ) :
    hamiltonian N γ * lowering N γ = lowering N γ * hamiltonian N γ := by
  have hUT : (y * qm) * (x * y) = (y * y) * (dot - (-Complex.I) • angularMomentum) := by
    have he : dot - (-Complex.I) • angularMomentum = dot + Complex.I • angularMomentum := by module
    rw [he]
    exact VT
  have h := D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.HamiltonianIdentity.symmetry N γ (2 * Complex.I)
    dot ((-Complex.I) • angularMomentum) (x * y) (y * y) (y * qm)
    (DC.smul_right (-Complex.I)) DV DT (CT.smul_left (-Complex.I)).eq DS TS TV hUT
  have hh := congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => (1 / 2 : ℂ) • Z) h
  have he : Complex.I • (2 - angularMomentum) =
      (-Complex.I) • angularMomentum + (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) := by rw [em_eq]; module
  simpa only [lowering, hamiltonian_eq, he, pow_two,
    mul_smul_comm, smul_mul_assoc] using hh

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff
set_option maxHeartbeats 800000 in
private theorem lowering_raising_product (N : ℕ) (γ : ℕ → ℂ) :
    lowering N γ * raising N γ = (1 / 4 : ℂ) •
      ((hamiltonian N γ - peval N γ ((-Complex.I) • angularMomentum)) *
        (hamiltonian N γ - peval N γ (Complex.I • (angularMomentum + 2)))) := by
  have hm : dot - (-Complex.I) • angularMomentum = dot + Complex.I • angularMomentum := by module
  have hp : (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) - (-Complex.I) • angularMomentum =
      (2 * Complex.I) • 1 + Complex.I • angularMomentum := by module
  have hpe : (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) + Complex.I • angularMomentum =
      Complex.I • (angularMomentum+2) := by rw [ep_eq]; module
  have he : (-Complex.I) • angularMomentum + (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) =
      Complex.I • (2 - angularMomentum) := by rw [em_eq]; module
  have huv : (y * qm) * (x * qp) =
      (dot - ((2 * Complex.I) • 1 - (-Complex.I) • angularMomentum)) *
        (dot - (-Complex.I) • angularMomentum) := by
    rw [hm, hp]
    exact VU
  have hrv : (y * y) * (x * qp) =
      (x * y) * (dot - ((2 * Complex.I) • 1 - (-Complex.I) • angularMomentum)) := by
    rw [hp]
    exact SU
  have hus : (y * qm) * (x * x) =
      (x * y) * (dot + (2 * Complex.I) • 1 - (-Complex.I) • angularMomentum) := by
    have ht : dot + (2 * Complex.I) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) - (-Complex.I) • angularMomentum =
        dot + (2 * Complex.I) • 1 + Complex.I • angularMomentum := by module
    rw [ht]
    exact VR
  have h := D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.ProductIdentity.factorization N γ (2 * Complex.I)
    dot ((-Complex.I) • angularMomentum) (x * y) (y * y) (x * x) (y * qm) (x * qp)
    (DC.smul_right (-Complex.I)) DR ER DU.eq EU DT (CT.smul_left (-Complex.I)).eq
    SR hrv hus huv
  have hh := congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => (1 / 4 : ℂ) • Z) h
  simpa only [lowering, raising, hamiltonian_eq, he, hp, hpe, pow_two,
    smul_mul_smul_comm, show (1 / 2 : ℂ) * (1 / 2) = 1 / 4 by norm_num] using hh
end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff
private theorem weighted_power (s c : ℂ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (k : ℕ) :
    (s^k * c) • A^k = c • (s • A)^k := by
  rw [smul_pow, smul_smul]
  congr 1
  ring

private theorem phi_as_eval (N : ℕ) (γ : ℕ → ℂ) (H K : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) :
    phi N γ H K = (1/4 : ℂ) •
      ((H - peval N γ ((2*Complex.I) • K)) *
        (H - peval N γ ((-2*Complex.I) • (K-1)))) := by
  unfold phi phi1 phi2
  have h1 : (∑ k ∈ Finset.Icc 1 N, ((2*Complex.I)^k * γ k) • K^k) =
      peval N γ ((2*Complex.I) • K) := by
    unfold peval
    apply Finset.sum_congr rfl
    intro k hk
    exact weighted_power _ _ _ _
  have h2 : (∑ k ∈ Finset.Icc 1 N, ((-2*Complex.I)^k * γ k) • (K-1)^k) =
      peval N γ ((-2*Complex.I) • (K-1)) := by
    unfold peval
    apply Finset.sum_congr rfl
    intro k hk
    exact weighted_power _ _ _ _
  rw [h1, h2, smul_mul_assoc]

private theorem phi_half (N : ℕ) (γ : ℕ → ℂ) (H : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) :
    phi N γ H ((1/2 : ℂ) • angularMomentum) = (1/4 : ℂ) •
      ((H - peval N γ (Complex.I • angularMomentum)) *
        (H - peval N γ (Complex.I • (2-angularMomentum)))) := by
  rw [phi_as_eval]
  have h1 : (2*Complex.I) • ((1/2 : ℂ) • angularMomentum) = Complex.I • angularMomentum := by module
  have h2 : (-2*Complex.I) • ((1/2 : ℂ) • angularMomentum - 1) =
      Complex.I • (2-angularMomentum) := by rw [em_eq]; module
  rw [h1, h2]

private theorem phi_half_shift (N : ℕ) (γ : ℕ → ℂ) (H : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) :
    phi N γ H ((1/2 : ℂ) • angularMomentum + 1) = (1/4 : ℂ) •
      ((H - peval N γ (Complex.I • (angularMomentum+2))) *
        (H - peval N γ ((-Complex.I) • angularMomentum))) := by
  rw [phi_as_eval]
  have h1 : (2*Complex.I) • ((1/2 : ℂ) • angularMomentum + 1) =
      Complex.I • (angularMomentum+2) := by rw [ep_eq]; module
  have h2 : (-2*Complex.I) • (((1/2 : ℂ) • angularMomentum + 1)-1) =
      (-Complex.I) • angularMomentum := by module
  rw [h1, h2]

private theorem C_H (N : ℕ) (γ : ℕ → ℂ) : Commute angularMomentum (hamiltonian N γ) := by
  rw [hamiltonian_eq]
  exact (show Commute angularMomentum (x*y) from CT).add_right
    (peval_commute_left N γ _ _ DC.symm)

private theorem reverse_factors_commute (N : ℕ) (γ : ℕ → ℂ) :
    Commute
      (hamiltonian N γ - peval N γ ((-Complex.I) • angularMomentum))
      (hamiltonian N γ - peval N γ (Complex.I • (angularMomentum+2))) := by
  have h1 : Commute (hamiltonian N γ) ((-Complex.I) • angularMomentum) :=
    (C_H N γ).symm.smul_right _
  have h2 : Commute (hamiltonian N γ) (Complex.I • (angularMomentum+2)) := by
    rw [ep_eq]
    exact ((C_H N γ).symm.smul_right _).add_right ((Commute.one_right _).smul_right _)
  have h3 : Commute ((-Complex.I) • angularMomentum) (Complex.I • (angularMomentum+2)) := by
    rw [ep_eq]
    exact (((Commute.refl angularMomentum).smul_left _).smul_right _).add_right
      ((Commute.one_right _).smul_right _)
  have hf1 := peval_commute_left N γ _ _ h1
  have hf2 := peval_commute_left N γ _ _ h2
  have hf3 := (peval_commute_left N γ _ _
    (peval_commute_left N γ _ _ h3.symm).symm)
  exact ((Commute.refl _).sub_right hf2).sub_left (hf1.symm.sub_right hf3)

private theorem raising_lowering_phi (N : ℕ) (γ : ℕ → ℂ) :
    raising N γ * lowering N γ = phi N γ (hamiltonian N γ) ((1/2 : ℂ) • angularMomentum) := by
  rw [phi_half]
  exact raising_lowering_product N γ

private theorem lowering_raising_phi (N : ℕ) (γ : ℕ → ℂ) :
    lowering N γ * raising N γ = phi N γ (hamiltonian N γ) ((1/2 : ℂ) • angularMomentum+1) := by
  rw [phi_half_shift, lowering_raising_product, (reverse_factors_commute N γ).eq]

private theorem half_C_raising (N : ℕ) (γ : ℕ → ℂ) :
    ((1/2 : ℂ) • angularMomentum) * raising N γ - raising N γ * ((1/2 : ℂ) • angularMomentum) =
      raising N γ := by
  calc
    _ = (1/2 : ℂ) • (angularMomentum * raising N γ - raising N γ * angularMomentum) := by
      exact comm_smul_left angularMomentum (raising N γ) (1 / 2)
    _ = _ := by rw [C_raising]; module
private theorem half_C_lowering (N : ℕ) (γ : ℕ → ℂ) :
    ((1/2 : ℂ) • angularMomentum) * lowering N γ - lowering N γ * ((1/2 : ℂ) • angularMomentum) =
      -lowering N γ := by
  calc
    _ = (1/2 : ℂ) • (angularMomentum * lowering N γ - lowering N γ * angularMomentum) := by
      exact comm_smul_left angularMomentum (lowering N γ) (1 / 2)
    _ = _ := by rw [C_lowering]; module

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.CorrectionLadders
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections

private theorem U_expansion : x * qp = q 0 * p 0 - q 1 * p 1 +
    Complex.I • (q 0 * p 1 + q 1 * p 0) := by
  rw [xqp_comm]
  simp only [qp, x, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, Complex.I_mul_I]
  module

private theorem V_expansion : y * qm = q 0 * p 0 - q 1 * p 1 -
    Complex.I • (q 0 * p 1 + q 1 * p 0) := by
  rw [yqm_comm]
  simp only [qm, y, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_sub, smul_smul, Complex.I_mul_I]
  module

private theorem U_mem : x * qp ∈ corrections 1 := by
  rw [U_expansion]
  exact (corrections 1).add_mem
    ((corrections 1).sub_mem (firstOrder_mem 1 (by decide) 0 0) (firstOrder_mem 1 (by decide) 1 1))
    ((corrections 1).smul_mem Complex.I
      ((corrections 1).add_mem (firstOrder_mem 1 (by decide) 0 1) (firstOrder_mem 1 (by decide) 1 0)))

private theorem V_mem : y * qm ∈ corrections 1 := by
  rw [V_expansion]
  exact (corrections 1).sub_mem
    ((corrections 1).sub_mem (firstOrder_mem 1 (by decide) 0 0) (firstOrder_mem 1 (by decide) 1 1))
    ((corrections 1).smul_mem Complex.I
      ((corrections 1).add_mem (firstOrder_mem 1 (by decide) 0 1) (firstOrder_mem 1 (by decide) 1 0)))

private theorem normal_raise (N : ℕ) (γ : ℕ → ℂ) :
    (x*qp) * divided N γ dot (Complex.I • (angularMomentum+2)) =
      divided N γ dot (Complex.I • angularMomentum) * (x*qp) := by
  have ht : (Complex.I • angularMomentum) * (x*qp) =
      (x*qp) * (Complex.I • (angularMomentum+2)) := by
    rw [smul_mul_assoc, sub_eq_iff_eq_add.mp CU, ep_eq]
    simp only [mul_add, mul_smul_comm, mul_one, smul_add, smul_smul]
    module
  exact (intertwine_divided N γ (x*qp) dot (Complex.I • angularMomentum)
    dot (Complex.I • (angularMomentum+2)) DU.eq ht).symm

private theorem normal_lower (N : ℕ) (γ : ℕ → ℂ) :
    (y*qm) * divided N γ dot (Complex.I • (2-angularMomentum)) =
      divided N γ dot ((-Complex.I) • angularMomentum) * (y*qm) := by
  have ht : ((-Complex.I) • angularMomentum) * (y*qm) =
      (y*qm) * (Complex.I • (2-angularMomentum)) := by
    rw [smul_mul_assoc, sub_eq_iff_eq_add.mp CV, em_eq]
    simp only [mul_sub, mul_smul_comm, mul_one, smul_add, smul_smul]
    module
  exact (intertwine_divided N γ (y*qm) dot ((-Complex.I) • angularMomentum)
    dot (Complex.I • (2-angularMomentum)) DV.eq ht).symm

private theorem divided_mul_mem (N : ℕ) (γ : ℕ → ℂ) (U : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hU : U ∈ corrections 1) (s : ℂ) :
    divided N γ dot (s • angularMomentum) * U ∈ corrections N := by
  unfold divided
  rw [Finset.sum_mul]
  apply (corrections N).sum_mem
  intro k hk
  rw [smul_mul_assoc]
  apply (corrections N).smul_mem
  rw [Finset.sum_mul]
  apply (corrections N).sum_mem
  intro j hj
  rw [mul_assoc]
  have h := dot_pow_mul_mem (1+j) (k-1-j) _ (C_pow_mul_mem 1 j U hU s)
  exact monotone (by have := Finset.mem_Icc.mp hk; have := Finset.mem_range.mp hj; omega) h

private theorem peval_dot_mem (N : ℕ) (γ : ℕ → ℂ) : peval N γ dot ∈ corrections N := by
  unfold peval
  apply (corrections N).sum_mem
  intro k hk
  apply (corrections N).smul_mem
  have hkl := (Finset.mem_Icc.mp hk).1
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [pow_succ]
  exact monotone (by have := (Finset.mem_Icc.mp hk).2; omega)
    (dot_pow_mul_mem 1 r dot (dot_mem 1 (by decide)))

private theorem raising_correction_mem (N : ℕ) (γ : ℕ → ℂ) :
    (x*qp) * divided N γ dot (Complex.I • (angularMomentum+2)) ∈ corrections N := by
  rw [normal_raise]
  exact divided_mul_mem N γ _ U_mem _
private theorem lowering_correction_mem (N : ℕ) (γ : ℕ → ℂ) :
    (y*qm) * divided N γ dot (Complex.I • (2-angularMomentum)) ∈ corrections N := by
  rw [normal_lower]
  exact divided_mul_mem N γ _ V_mem _

private theorem kinetic_sum : (1/4 : ℂ) • (x^2+y^2) = (1/2 : ℂ) • (p 0^2-p 1^2) := by
  simp only [x, y, pow_two, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  module

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.CorrectionLadders

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.WitnessAlgebra
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore
private noncomputable def firstSymmetry (H U V : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) := (1 / 2 : ℂ) • H - (1 / 2 : ℂ) • (U + V)
private noncomputable def secondSymmetry (H U V : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) := (1 / 2 : ℂ) • H + (1 / 2 : ℂ) • (U + V)

private theorem k2_formula (H U V : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) :
    k2 (firstSymmetry H U V) (secondSymmetry H U V) = (1 / 2 : ℂ) • (U + V) := by
  unfold k2 firstSymmetry secondSymmetry
  module

private theorem k3_formula (H U V : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)))
    (hU : angularMomentum * U - U * angularMomentum = (2 : ℂ) • U)
    (hV : angularMomentum * V - V * angularMomentum = -(2 : ℂ) • V) :
    k3 (firstSymmetry H U V) (secondSymmetry H U V) = U - V := by
  unfold k3 k1
  rw [k2_formula]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  have h : angularMomentum * U + angularMomentum * V -
      (U * angularMomentum + V * angularMomentum) = (2 : ℂ) • U - (2 : ℂ) • V := by
    rw [show angularMomentum * U + angularMomentum * V -
      (U * angularMomentum + V * angularMomentum) =
      (angularMomentum * U - U * angularMomentum) +
      (angularMomentum * V - V * angularMomentum) by abel, hU, hV]
    module
  calc
    _ = (1 / 2 : ℂ) • (angularMomentum * U + angularMomentum * V -
      (U * angularMomentum + V * angularMomentum)) := by module
    _ = _ := by rw [h]; module

private theorem ladder_membership (H U V : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)))
    (hU : angularMomentum * U - U * angularMomentum = (2 : ℂ) • U)
    (hV : angularMomentum * V - V * angularMomentum = -(2 : ℂ) • V) :
    let I := firstSymmetry H U V
    let I' := secondSymmetry H U V
    (1 / 2 : ℂ) • angularMomentum ∈ Algebra.adjoin ℂ {angularMomentum, k2 I I', k3 I I'} ∧
    U ∈ Algebra.adjoin ℂ {angularMomentum, k2 I I', k3 I I'} ∧
    V ∈ Algebra.adjoin ℂ {angularMomentum, k2 I I', k3 I I'} := by
  dsimp only
  let S := Algebra.adjoin ℂ
    {angularMomentum, k2 (firstSymmetry H U V) (secondSymmetry H U V),
      k3 (firstSymmetry H U V) (secondSymmetry H U V)}
  have hc : angularMomentum ∈ S := Algebra.subset_adjoin (by simp)
  have ha : k2 (firstSymmetry H U V) (secondSymmetry H U V) ∈ S :=
    Algebra.subset_adjoin (by simp)
  have hb : k3 (firstSymmetry H U V) (secondSymmetry H U V) ∈ S :=
    Algebra.subset_adjoin (by simp)
  refine ⟨S.smul_mem hc _, ?_, ?_⟩
  · have h : k2 (firstSymmetry H U V) (secondSymmetry H U V) +
        (1 / 2 : ℂ) • k3 (firstSymmetry H U V) (secondSymmetry H U V) = U := by
      rw [k2_formula, k3_formula H U V hU hV]
      module
    have hm := S.add_mem ha (S.smul_mem hb (1 / 2 : ℂ))
    exact (congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => Z ∈ S) h).mp hm
  · have h : k2 (firstSymmetry H U V) (secondSymmetry H U V) -
        (1 / 2 : ℂ) • k3 (firstSymmetry H U V) (secondSymmetry H U V) = V := by
      rw [k2_formula, k3_formula H U V hU hV]
      module
    have hm := S.sub_mem ha (S.smul_mem hb (1 / 2 : ℂ))
    exact (congrArg (fun Z : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => Z ∈ S) h).mp hm

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.WitnessAlgebra

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder.Settlement
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections D5.S3.Quantum.CampoamorStursbergZernikeLadder.CorrectionLadders D5.S3.Quantum.CampoamorStursbergZernikeLadder.WitnessAlgebra

private theorem symmetry_forms (N : ℕ) (γ : ℕ → ℂ) :
    firstSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) - p 1 ^ 2 ∈ corrections N ∧
    secondSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) - p 0 ^ 2 ∈ corrections N := by
  let P := (x*qp) * divided N γ dot (Complex.I • (angularMomentum+2))
  let M := (y*qm) * divided N γ dot (Complex.I • (2-angularMomentum))
  have hp : P ∈ corrections N := raising_correction_mem N γ
  have hm : M ∈ corrections N := lowering_correction_mem N γ
  have hplus : P+M ∈ corrections N := (corrections N).add_mem hp hm
  constructor
  · have he : firstSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) - p 1 ^ 2 =
        (1/2 : ℂ) • peval N γ dot - (1/4 : ℂ) • (P+M) := by
      calc
        _ = (1/2 : ℂ) • (p 0^2+p 1^2+peval N γ dot) -
            (1/4 : ℂ) • (x^2+y^2) - (1/4 : ℂ) • (P+M) - p 1^2 := by
          simp only [firstSymmetry, raising, lowering, hamiltonian_eq, xy, P, M]
          module
        _ = _ := by rw [kinetic_sum]; module
    rw [he]
    exact (corrections N).sub_mem ((corrections N).smul_mem _ (peval_dot_mem N γ))
      ((corrections N).smul_mem _ hplus)
  · have he : secondSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) - p 0 ^ 2 =
        (1/2 : ℂ) • peval N γ dot + (1/4 : ℂ) • (P+M) := by
      calc
        _ = (1/2 : ℂ) • (p 0^2+p 1^2+peval N γ dot) +
            (1/4 : ℂ) • (x^2+y^2) + (1/4 : ℂ) • (P+M) - p 0^2 := by
          simp only [secondSymmetry, raising, lowering, hamiltonian_eq, xy, P, M]
          module
        _ = _ := by rw [kinetic_sum]; module
    rw [he]
    exact (corrections N).add_mem ((corrections N).smul_mem _ (peval_dot_mem N γ))
      ((corrections N).smul_mem _ hplus)

private theorem symmetries_commute (N : ℕ) (γ : ℕ → ℂ) :
    firstSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) * hamiltonian N γ -
      hamiltonian N γ * firstSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) = 0 ∧
    secondSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) * hamiltonian N γ -
      hamiltonian N γ * secondSymmetry (hamiltonian N γ) (raising N γ) (lowering N γ) = 0 := by
  constructor <;>
    simp only [firstSymmetry, secondSymmetry, sub_mul, add_mul, mul_sub, mul_add,
      smul_mul_assoc, mul_smul_comm, raising_commutes, lowering_commutes] <;> module

end D5.S3.Quantum.CampoamorStursbergZernikeLadder.Settlement

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadder

open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadder.Ladders D5.S3.Quantum.CampoamorStursbergZernikeLadder.WitnessAlgebra D5.S3.Quantum.CampoamorStursbergZernikeLadder.Settlement in
theorem result : claim := by
  intro N hN γ
  let H := hamiltonian N γ
  let U := raising N γ
  let V := lowering N γ
  let I := firstSymmetry H U V
  let I' := secondSymmetry H U V
  let K : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := (1/2 : ℂ) • angularMomentum
  let Kp := k2 I I' + (1/2 : ℂ) • k3 I I'
  let Km := k2 I I' - (1/2 : ℂ) • k3 I I'
  have hp : Kp = U := by
    dsimp only [Kp, I, I']
    rw [k2_formula, k3_formula H U V (C_raising N γ) (C_lowering N γ)]
    module
  have hm : Km = V := by
    dsimp only [Km, I, I']
    rw [k2_formula, k3_formula H U V (C_raising N γ) (C_lowering N γ)]
    module
  have hmem := ladder_membership H U V (C_raising N γ) (C_lowering N γ)
  have hforms := symmetry_forms N γ
  have hcomm := symmetries_commute N γ
  refine ⟨I, I', ⟨hforms.1, hcomm.1⟩, ⟨hforms.2, hcomm.2⟩,
    K, hmem.1, Kp, ?_, Km, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact hmem.2.1
  · rw [hm]
    exact hmem.2.2
  · rw [hp]
    exact half_C_raising N γ
  · rw [hm]
    exact half_C_lowering N γ
  · rw [hp, hm]
    exact raising_lowering_phi N γ
  · rw [hp, hm]
    exact congrArg₂ (fun A B : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) => A-B) (lowering_raising_phi N γ) (raising_lowering_phi N γ)

end D5.S3.Quantum.CampoamorStursbergZernikeLadder
