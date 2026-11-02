/- GID: D5/S3/Quantum/CampoamorStursbergZernikeLadderCore
   generality: I
   mirror-B: D5/B/S3/Quantum/CampoamorStursbergZernikeLadderCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normal ordering preserves the Zernike correction filtration. -/

/-
Weyl.pp: proof_shape: bind-only; escape_witness: none.
Weyl.qq: proof_shape: bind-only; escape_witness: none.
Weyl.pq: proof_shape: bind-only; escape_witness: none.
DivDiff.peval_commute_left: proof_shape: bind-only; escape_witness: none.
DivDiff.intertwine_divided: proof_shape: bind-only; escape_witness: none.
DivDiff.divided_commute_left: proof_shape: bind-only; escape_witness: none.
HamiltonianIdentity.symmetry: proof_shape: bind-only; escape_witness: none.
ProductIdentity.factorization: proof_shape: bind-only; escape_witness: none.
Corrections.monotone: proof_shape: bind-only; escape_witness: none.
Corrections.firstOrder_mem: proof_shape: bind-only; escape_witness: none.
Corrections.dot_mem: proof_shape: bind-only; escape_witness: none.
Corrections.dot_pow_mul_mem: proof_shape: content; escape_witness: Corrections.dot_pow_mul_mem.
Corrections.C_pow_mul_mem: proof_shape: content; escape_witness: Corrections.C_pow_mul_mem.
admission_basis: escape-witness
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21497
The operator type is written in full; k1 is the source's angular momentum generator.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Algebra.Ring.GeomSum

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore

open MvPolynomial

/-- Eq. (2.1): `q̂ᵢ ψ = qᵢ ψ`. -/
noncomputable def q (i : Fin 2) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := LinearMap.mulLeft ℂ (X i)

/-- Eq. (2.1): `p̂ᵢ ψ = −i ∂ψ/∂qᵢ`. -/
noncomputable def p (i : Fin 2) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := (-Complex.I) • (pderiv i).toLinearMap

/-- `q̂ · p̂ = q̂₁p̂₁ + q̂₂p̂₂`. -/
noncomputable def dot : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := q 0 * p 0 + q 1 * p 1

/-- Eq. (2.5): the quantum angular momentum `Ĉ = q̂₁p̂₂ − q̂₂p̂₁`. -/
noncomputable def angularMomentum : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := q 0 * p 1 - q 1 * p 0

/-- Eq. (2.3): `Ĥ_N = p̂² + Σ_{k=1}^N γ_k (q̂ · p̂)^k`. -/
noncomputable def hamiltonian (N : ℕ) (γ : ℕ → ℂ) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  p 0 ^ 2 + p 1 ^ 2 + ∑ k ∈ Finset.Icc 1 N, γ k • dot ^ k

/-- The monomial `q̂₁^a q̂₂^b p̂₁^c p̂₂^d`, of degree `a + b + c + d` and grading `a + b − c − d`. -/
noncomputable def monomial (a b c d : ℕ) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := q 0 ^ a * q 1 ^ b * p 0 ^ c * p 1 ^ d

/-- Eq. (2.6): the span of the grading-zero monomials of degree `1 ≤ ℓ ≤ 2N`. -/
noncomputable def corrections (N : ℕ) : Submodule ℂ (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  Submodule.span ℂ {A | ∃ a b c d : ℕ, a + b = c + d ∧ 1 ≤ a + b + c + d ∧ a + b + c + d ≤ 2 * N ∧
    A = monomial a b c d}

/-- Eqs. (2.6)–(2.7): `I` has kinetic term `T` plus corrections of the form (2.6), and commutes with `Ĥ_N`. -/
def IsSymmetry (N : ℕ) (γ : ℕ → ℂ) (T I : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : Prop :=
  I - T ∈ corrections N ∧ I * hamiltonian N γ - hamiltonian N γ * I = 0

/-- Eq. (2.8): `K̂₁ = Ĉ`. -/
noncomputable def k1 : Module.End ℂ (MvPolynomial (Fin 2) ℂ) := angularMomentum

/-- Eq. (2.8): `K̂₂ = (Î'_N − Î_N)/2`. -/
noncomputable def k2 (I I' : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := (1 / 2 : ℂ) • (I' - I)

/-- Eq. (2.8): `K̂₃ = [K̂₁, K̂₂]`. -/
noncomputable def k3 (I I' : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := k1 * k2 I I' - k2 I I' * k1

/-- Eq. (5.1): `Φ₁(Ĥ, K̂) = ¼ (Ĥ − Σ_{k=1}^N (2i)^k γ_k K̂^k)`. -/
noncomputable def phi1 (N : ℕ) (γ : ℕ → ℂ) (H K : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  (1 / 4 : ℂ) • (H - ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I) ^ k * γ k) • K ^ k)

/-- Eq. (5.1): `Φ₂(Ĥ, K̂) = Ĥ − Σ_{k=1}^N (−2i)^k γ_k (K̂ − Id)^k`. -/
noncomputable def phi2 (N : ℕ) (γ : ℕ → ℂ) (H K : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) :=
  H - ∑ k ∈ Finset.Icc 1 N, ((-2 * Complex.I) ^ k * γ k) • (K - 1) ^ k

/-- Eq. (2.10): the structure function `Φ = Φ₁ Φ₂`. -/
noncomputable def phi (N : ℕ) (γ : ℕ → ℂ) (H K : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) : (Module.End ℂ (MvPolynomial (Fin 2) ℂ)) := phi1 N γ H K * phi2 N γ H K

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl MvPolynomial
theorem pp (i j : Fin 2) : p i * p j = p j * p i := by
  ext f
  simp [p, Module.End.mul_apply, MvPolynomial.pderiv_comm]

theorem qq (i j : Fin 2) : q i * q j = q j * q i := by
  ext f
  simp [q, Module.End.mul_apply, mul_left_comm]

theorem pq (i j : Fin 2) : p i * q j = q j * p i - (if i = j then Complex.I else 0) • (1 : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) := by
  apply LinearMap.ext
  intro f
  change (-Complex.I) • pderiv i (X j * f) =
    X j * ((-Complex.I) • pderiv i f) - (if i = j then Complex.I else 0) • f
  by_cases h : i = j
  · subst j
    simp only [pderiv_mul, pderiv_X_self, one_mul, ite_true]
    simp only [smul_add, neg_smul, mul_neg, Algebra.mul_smul_comm]
    module
  · simp [pderiv_mul, pderiv_X_of_ne (Ne.symm h), h]

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff
open Finset
variable {A : Type*} [Ring A] [Algebra ℂ A]
noncomputable def peval (N : ℕ) (γ : ℕ → ℂ) (s : A) : A :=
  ∑ k ∈ Icc 1 N, γ k • s ^ k
noncomputable def divided (N : ℕ) (γ : ℕ → ℂ) (s t : A) : A :=
  ∑ k ∈ Icc 1 N, γ k • ∑ j ∈ range k, s ^ (k - 1 - j) * t ^ j

omit [Algebra ℂ A] in
private theorem geometric (s t : A) (h : Commute s t) (k : ℕ) :
    (s - t) * (∑ j ∈ range k, s ^ (k - 1 - j) * t ^ j) = s^k - t^k := by
  have hs : (∑ j ∈ range k, s ^ (k - 1 - j) * t ^ j) =
      ∑ j ∈ range k, t ^ j * s ^ (k - 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (h.pow_pow _ _).eq
  rw [hs]
  exact h.symm.mul_neg_geom_sum₂ k

private theorem difference (N : ℕ) (γ : ℕ → ℂ) (s t : A) (h : Commute s t) :
    peval N γ s - peval N γ t = (s - t) * divided N γ s t := by
  unfold peval divided
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← smul_sub, mul_smul_comm, geometric s t h k]

theorem peval_commute_left (N : ℕ) (γ : ℕ → ℂ) (r s : A) (h : Commute r s) :
    Commute r (peval N γ s) := by
  unfold peval
  exact Commute.sum_right _ _ _ (fun k hk => (h.pow_right k).smul_right (γ k))

omit [Algebra ℂ A] in
private theorem intertwine_power (r s t : A) (h : r * s = t * r) (k : ℕ) :
    r * s^k = t^k * r := by
  exact (SemiconjBy.pow_right h k).eq

private theorem intertwine_eval (N : ℕ) (γ : ℕ → ℂ) (r s t : A) (h : r * s = t * r) :
    r * peval N γ s = peval N γ t * r := by
  simp only [peval, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun a : A => γ k • a) (intertwine_power r s t h k)

theorem intertwine_divided (N : ℕ) (γ : ℕ → ℂ) (r s t s' t' : A)
    (hs : s * r = r * s') (ht : t * r = r * t') :
    divided N γ s t * r = r * divided N γ s' t' := by
  simp only [divided, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ← intertwine_power r t' t ht.symm,
    ← mul_assoc, ← intertwine_power r s' s hs.symm, mul_assoc]

theorem divided_commute_left (N : ℕ) (γ : ℕ → ℂ) (r s t : A)
    (hs : Commute r s) (ht : Commute r t) :
    Commute r (divided N γ s t) := by
  unfold divided
  apply Commute.sum_right
  intro k hk
  apply Commute.smul_right
  apply Commute.sum_right
  intro j hj
  exact (hs.pow_right _).mul_right (ht.pow_right _)

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.HamiltonianIdentity
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem symmetry (N : ℕ) (γ : ℕ → ℂ) (α : ℂ) (D A T R U : B)
    (hDA : Commute D A) (hDU : Commute D U)
    (hDT : D * T = T * (D + α • 1))
    (hAT : A * T = T * A)
    (hDR : D * R = R * (D + α • 1))
    (hTR : T * R = R * T)
    (hTU : T * U = U * T - α • R)
    (hUT : U * T = R * (D - A)) :
    (T + peval N γ D) * (R + U * divided N γ D (A + α • 1)) =
      (R + U * divided N γ D (A + α • 1)) * (T + peval N γ D) := by
  let E := A + α • (1 : B)
  let Q := divided N γ D E
  let Q' := divided N γ (D + α • (1 : B)) E
  let F : B → B := peval N γ
  have hDE : Commute D E := hDA.add_right ((Commute.one_right D).smul_right α)
  have hDET : E * T = T * E := by
    dsimp [E]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAT]
  have hQT : Q * T = T * Q' :=
    intertwine_divided N γ T D E (D + α • 1) E hDT hDET
  have hFQ : F D * Q = Q * F D :=
    (peval_commute_left N γ Q D
      (divided_commute_left N γ D D E (Commute.refl D) hDE).symm).symm.eq
  have hFU : F D * U = U * F D :=
    (peval_commute_left N γ U D hDU.symm).symm.eq
  have hFR : F D * R = R * F (D + α • 1) :=
    (intertwine_eval N γ R (D + α • 1) D hDR.symm).symm
  have h1 : T * (U * Q) = R * ((D - A) * Q) - α • (R * Q) := by
    rw [← mul_assoc, hTU, sub_mul, hUT, mul_assoc, smul_mul_assoc]
  have h2 : (U * Q) * T = R * ((D - A) * Q') := by
    rw [mul_assoc, hQT, ← mul_assoc U T, hUT, mul_assoc]
  have h3 : F D * (U * Q) = (U * Q) * F D := by
    rw [← mul_assoc, hFU, mul_assoc, hFQ, ← mul_assoc]
  have hd1 : F D - F E = (D - E) * Q := difference N γ D E hDE
  have hd2 : F (D + α • 1) - F E = (D + α • 1 - E) * Q' :=
    difference N γ (D + α • 1) E
      (hDE.add_left ((Commute.one_left E).smul_left α))
  have heq : F (D + α • 1) - F D + (D - A) * Q - α • Q - (D - A) * Q' = 0 := by
    have he : D + α • (1 : B) - E = D - A := by
      exact add_sub_add_right_eq_sub D A (α • 1)
    rw [he] at hd2
    have hd : D - E = D - A - α • (1 : B) := by
      exact sub_add_eq_sub_sub D A (α • 1)
    rw [hd, sub_mul, smul_mul_assoc, one_mul] at hd1
    rw [sub_eq_iff_eq_add.mp hd1, sub_eq_iff_eq_add.mp hd2]
    abel
  change (T + F D) * (R + U * Q) = (R + U * Q) * (T + F D)
  apply sub_eq_zero.mp
  calc
    _ = R * (F (D + α • 1) - F D + (D - A) * Q - α • Q - (D - A) * Q') := by
      simp only [add_mul, mul_add]
      rw [h1, h2, h3, hFR, hTR]
      simp only [mul_add, mul_sub, mul_smul_comm]
      abel
    _ = 0 := by rw [heq, mul_zero]

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.HamiltonianIdentity

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.ProductIdentity
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.DivDiff
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem factorization (N : ℕ) (γ : ℕ → ℂ) (α : ℂ) (D A T R S U V : B)
    (hDA : Commute D A)
    (hDS : D * S = S * (D + α • 1))
    (hES : (A + α • 1) * S = S * A)
    (hDV : D * V = V * D)
    (hEV : (A + α • 1) * V = V * A)
    (hDT : D * T = T * (D + α • 1))
    (hAT : A * T = T * A)
    (hRS : R * S = T * T)
    (hRV : R * V = T * (D - (α • 1 - A)))
    (hUS : U * S = T * (D + α • 1 - A))
    (hUV : U * V = (D - (α • 1 - A)) * (D - A)) :
    (R + U * divided N γ D (A + α • 1)) *
        (S + V * divided N γ D (α • 1 - A)) =
      (T + peval N γ D - peval N γ A) *
        (T + peval N γ D - peval N γ (α • 1 - A)) := by
  let F : B → B := peval N γ
  let B' := α • (1 : B) - A
  let Q := divided N γ D (A + α • 1)
  let Qs := divided N γ (D + α • 1) A
  let Qa := divided N γ D A
  let Qb := divided N γ D B'
  have hDB : Commute D B' :=
    ((Commute.one_right D).smul_right α).sub_right hDA
  have hQS : Q * S = S * Qs :=
    intertwine_divided N γ S D (A + α • 1) (D + α • 1) A hDS hES
  have hQV : Q * V = V * Qa :=
    intertwine_divided N γ V D (A + α • 1) D A hDV hEV
  have h1 : (U * Q) * S = T * ((D + α • 1 - A) * Qs) := by
    rw [mul_assoc, hQS, ← mul_assoc U S, hUS, mul_assoc]
  have h2 : (U * Q) * (V * Qb) = (D - B') * (((D - A) * Qa) * Qb) := by
    rw [← mul_assoc (U * Q) V, mul_assoc U Q V, hQV,
      ← mul_assoc U V, hUV]
    simp only [mul_assoc, B']
  have h3 : R * (V * Qb) = T * ((D - B') * Qb) := by
    rw [← mul_assoc, hRV, mul_assoc]
  have hdA : (D - A) * Qa = F D - F A := (difference N γ D A hDA).symm
  have hdB : (D - B') * Qb = F D - F B' := (difference N γ D B' hDB).symm
  have hdS : (D + α • 1 - A) * Qs = F (D + α • 1) - F A :=
    (difference N γ (D + α • 1) A
      (hDA.add_left ((Commute.one_left A).smul_left α))).symm
  have hBD : Commute (D - B') D := (Commute.refl D).sub_left hDB.symm
  have hBA : Commute (D - B') A := hDA.sub_left
    (((Commute.one_left A).smul_left α).sub_left (Commute.refl A))
  have hBR : (D - B') * (F D - F A) = (F D - F A) * (D - B') :=
    ((peval_commute_left N γ _ _ hBD).sub_right
      (peval_commute_left N γ _ _ hBA)).eq
  have h4 : (U * Q) * (V * Qb) = (F D - F A) * (F D - F B') := by
    rw [h2, hdA, ← mul_assoc, hBR, mul_assoc, hdB]
  have hFT : F D * T = T * F (D + α • 1) :=
    (intertwine_eval N γ T (D + α • 1) D hDT.symm).symm
  have hFaT : F A * T = T * F A :=
    (peval_commute_left N γ T A hAT.symm).symm.eq
  have h5 : (F D - F A) * T = T * (F (D + α • 1) - F A) := by
    rw [sub_mul, hFT, hFaT, mul_sub]
  change (R + U * Q) * (S + V * Qb) = (T + F D - F A) * (T + F D - F B')
  calc
    _ = T * T + T * (F D - F B') + T * (F (D + α • 1) - F A) +
        (F D - F A) * (F D - F B') := by
      simp only [add_mul, mul_add]
      rw [hRS, h1, h3, h4, hdB, hdS]
      abel
    _ = _ := by
      rw [show T + F D - F A = T + (F D - F A) by abel,
        show T + F D - F B' = T + (F D - F B') by abel]
      simp only [add_mul, mul_add, h5]
      abel

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.ProductIdentity

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl MvPolynomial
private theorem p_qpow (i : Fin 2) (n : ℕ) :
    p i * q i ^ (n+1) = q i ^ (n+1) * p i -
      (((n : ℂ)+1)*Complex.I) • q i ^ n := by
  apply LinearMap.ext
  intro f
  simp only [q, LinearMap.pow_mulLeft, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.sub_apply, LinearMap.smul_apply]
  change (-Complex.I) • pderiv i (X i ^ (n+1) * f) =
    X i ^ (n+1) * ((-Complex.I) • pderiv i f) -
      (((n : ℂ)+1)*Complex.I) • (X i ^ n * f)
  rw [pderiv_mul, pderiv_pow, pderiv_X_self]
  simp only [Nat.add_sub_cancel, mul_one, smul_eq_C_mul, map_neg, map_mul, map_add,
    map_one, map_natCast, Nat.cast_add, Nat.cast_one]
  ring

private theorem p_qcross (i j : Fin 2) (h : i ≠ j) : Commute (p i) (q j) := by
  change _ = _
  rw [pq]
  simp [h]

private theorem p_qpow_all (i : Fin 2) (n : ℕ) :
    p i * q i ^ n = q i ^ n * p i - ((n : ℂ) * Complex.I) • q i ^ (n-1) := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using p_qpow i n

private theorem q0_monomial (a b c d : ℕ) :
    q 0 * monomial a b c d = monomial (a+1) b c d := by
  simp only [D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.monomial, pow_succ', mul_assoc]

private theorem q1_monomial (a b c d : ℕ) :
    q 1 * monomial a b c d = monomial a (b+1) c d := by
  have h := ((show Commute (q 1) (q 0) from qq 1 0).pow_right a).eq
  simp only [D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.monomial, pow_succ', mul_assoc]
  rw [← mul_assoc (q 1) (q 0 ^ a), h]
  simp only [mul_assoc]

private theorem p0_monomial (a b c d : ℕ) :
    p 0 * monomial a b c d = monomial a b (c+1) d -
      ((a : ℂ) * Complex.I) • monomial (a-1) b c d := by
  have h := ((p_qcross 0 1 (by decide)).pow_right b).eq
  unfold D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.monomial
  rw [pow_succ' (p 0) c]
  calc
    _ = (p 0 * q 0 ^ a) * q 1 ^ b * p 0 ^ c * p 1 ^ d := by simp only [mul_assoc]
    _ = _ := by
      rw [p_qpow_all]
      simp only [sub_mul, smul_mul_assoc]
      rw [mul_assoc (q 0 ^ a) (p 0), h]
      simp only [mul_assoc]

private theorem p1_monomial (a b c d : ℕ) :
    p 1 * monomial a b c d = monomial a b c (d+1) -
      ((b : ℂ) * Complex.I) • monomial a (b-1) c d := by
  have hq := ((p_qcross 1 0 (by decide)).pow_right a).eq
  have hp := ((show Commute (p 1) (p 0) from pp 1 0).pow_right c).eq
  unfold D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.monomial
  rw [pow_succ' (p 1) d]
  calc
    _ = q 0 ^ a * (p 1 * q 1 ^ b) * p 0 ^ c * p 1 ^ d := by
      calc
        _ = (p 1 * q 0 ^ a) * q 1 ^ b * p 0 ^ c * p 1 ^ d := by simp only [mul_assoc]
        _ = _ := by rw [hq]; simp only [mul_assoc]
    _ = _ := by
      rw [p_qpow_all]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      simp only [mul_assoc]
      rw [← mul_assoc (p 1) (p 0 ^ c) (p 1 ^ d), hp]
      simp only [mul_assoc]

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore
private theorem monomial_mem (N a b c d : ℕ) (hb : a + b = c + d)
    (hpos : 1 ≤ a + b + c + d) (hbound : a + b + c + d ≤ 2 * N) :
    monomial a b c d ∈ corrections N :=
  Submodule.subset_span ⟨a, b, c, d, hb, hpos, hbound, rfl⟩

theorem monotone {N M : ℕ} (h : N ≤ M) : corrections N ≤ corrections M := by
  apply Submodule.span_mono
  rintro A ⟨a, b, c, d, hb, hp, hu, rfl⟩
  exact ⟨a, b, c, d, hb, hp, by omega, rfl⟩

theorem firstOrder_mem (N : ℕ) (hN : 1 ≤ N) (i j : Fin 2) :
    q i * p j ∈ corrections N := by
  fin_cases i <;> fin_cases j
  · simpa [monomial] using monomial_mem N 1 0 1 0 (by decide) (by decide) (by omega)
  · simpa [monomial] using monomial_mem N 1 0 0 1 (by decide) (by decide) (by omega)
  · simpa [monomial] using monomial_mem N 0 1 1 0 (by decide) (by decide) (by omega)
  · simpa [monomial] using monomial_mem N 0 1 0 1 (by decide) (by decide) (by omega)

theorem dot_mem (N : ℕ) (hN : 1 ≤ N) : dot ∈ corrections N :=
  (corrections N).add_mem (firstOrder_mem N hN 0 0) (firstOrder_mem N hN 1 1)

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections

namespace D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections
open D5.S3.Quantum.CampoamorStursbergZernikeLadderCore D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Weyl D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal
private theorem firstOrder_mul_monomial_mem (N a b c d : ℕ)
    (hb : a + b = c + d) (hpos : 1 ≤ a+b+c+d) (hu : a+b+c+d ≤ 2*N)
    (i j : Fin 2) : (q i * p j) * monomial a b c d ∈ corrections (N+1) := by
  fin_cases i <;> fin_cases j
  · change (q 0 * p 0) * monomial a b c d ∈ corrections (N+1)
    rw [mul_assoc, D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal.p0_monomial, mul_sub, mul_smul_comm, q0_monomial, q0_monomial]
    have htop := monomial_mem (N+1) (a+1) b (c+1) d (by omega) (by omega) (by omega)
    cases a with
    | zero => simpa only [Nat.cast_zero, zero_mul, zero_smul, sub_zero] using htop
    | succ a =>
      apply (corrections (N+1)).sub_mem htop
      apply (corrections (N+1)).smul_mem
      exact monomial_mem _ _ _ _ _ (by omega) (by omega) (by omega)
  · change (q 0 * p 1) * monomial a b c d ∈ corrections (N+1)
    rw [mul_assoc, D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal.p1_monomial, mul_sub, mul_smul_comm, q0_monomial, q0_monomial]
    have htop := monomial_mem (N+1) (a+1) b c (d+1) (by omega) (by omega) (by omega)
    cases b with
    | zero => simpa only [Nat.cast_zero, zero_mul, zero_smul, sub_zero] using htop
    | succ b =>
      apply (corrections (N+1)).sub_mem htop
      apply (corrections (N+1)).smul_mem
      exact monomial_mem _ _ _ _ _ (by omega) (by omega) (by omega)
  · change (q 1 * p 0) * monomial a b c d ∈ corrections (N+1)
    rw [mul_assoc, D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal.p0_monomial, mul_sub, mul_smul_comm, q1_monomial, q1_monomial]
    have htop := monomial_mem (N+1) a (b+1) (c+1) d (by omega) (by omega) (by omega)
    cases a with
    | zero => simpa only [Nat.cast_zero, zero_mul, zero_smul, sub_zero] using htop
    | succ a =>
      apply (corrections (N+1)).sub_mem htop
      apply (corrections (N+1)).smul_mem
      exact monomial_mem _ _ _ _ _ (by omega) (by omega) (by omega)
  · change (q 1 * p 1) * monomial a b c d ∈ corrections (N+1)
    rw [mul_assoc, D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Normal.p1_monomial, mul_sub, mul_smul_comm, q1_monomial, q1_monomial]
    have htop := monomial_mem (N+1) a (b+1) c (d+1) (by omega) (by omega) (by omega)
    cases b with
    | zero => simpa only [Nat.cast_zero, zero_mul, zero_smul, sub_zero] using htop
    | succ b =>
      apply (corrections (N+1)).sub_mem htop
      apply (corrections (N+1)).smul_mem
      exact monomial_mem _ _ _ _ _ (by omega) (by omega) (by omega)

private theorem firstOrder_mul_mem (N : ℕ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hA : A ∈ corrections N) (i j : Fin 2) :
    (q i * p j) * A ∈ corrections (N+1) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    rcases hA with ⟨a,b,c,d,hb,hp,hu,rfl⟩
    exact firstOrder_mul_monomial_mem N a b c d hb hp hu i j
  | zero => simpa only [mul_zero] using (corrections (N+1)).zero_mem
  | add A B hA hB ihA ihB => simpa only [mul_add] using (corrections (N+1)).add_mem ihA ihB
  | smul r A hA ihA => simpa only [mul_smul_comm] using (corrections (N+1)).smul_mem r ihA

private theorem dot_mul_mem (N : ℕ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hA : A ∈ corrections N) : dot * A ∈ corrections (N+1) := by
  simpa only [dot, add_mul] using (corrections (N+1)).add_mem
    (firstOrder_mul_mem N A hA 0 0) (firstOrder_mul_mem N A hA 1 1)

private theorem C_mul_mem (N : ℕ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hA : A ∈ corrections N) : angularMomentum * A ∈ corrections (N+1) := by
  simpa only [angularMomentum, sub_mul] using (corrections (N+1)).sub_mem
    (firstOrder_mul_mem N A hA 0 1) (firstOrder_mul_mem N A hA 1 0)

theorem dot_pow_mul_mem (N r : ℕ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hA : A ∈ corrections N) :
    dot ^ r * A ∈ corrections (N+r) := by
  induction r with
  | zero => simpa only [pow_zero, one_mul, Nat.add_zero] using hA
  | succ r ih => simpa only [pow_succ', mul_assoc, Nat.add_succ] using dot_mul_mem (N+r) _ ih

theorem C_pow_mul_mem (N r : ℕ) (A : (Module.End ℂ (MvPolynomial (Fin 2) ℂ))) (hA : A ∈ corrections N) (s : ℂ) :
    (s • angularMomentum) ^ r * A ∈ corrections (N+r) := by
  induction r with
  | zero => simpa only [pow_zero, one_mul, Nat.add_zero] using hA
  | succ r ih =>
    simpa only [pow_succ', mul_assoc, smul_mul_assoc, Nat.add_succ] using
      (corrections (N+r+1)).smul_mem s (C_mul_mem (N+r) _ ih)

end D5.S3.Quantum.CampoamorStursbergZernikeLadderCore.Corrections
