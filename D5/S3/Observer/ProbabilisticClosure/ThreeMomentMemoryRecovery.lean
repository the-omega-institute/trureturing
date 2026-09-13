/- GID: D5/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryRecovery
   mirror-E: none(waiver:unbounded-symbolic-reconstruction)
   anchors: []
   utility: none
   digest: Three fixed observer-relative matrix elements recover every memory lag
     of an arbitrary symmetric two-copy dynamics, including zero coupling. -/

import D5.S3.Observer.ProbabilisticClosure.TwinedTraceMemoryObstruction

set_option autoImplicit false
open scoped Matrix Kronecker

namespace D5.S3.Observer.ProbabilisticClosure.ThreeMomentMemoryRecovery

/-- The full symmetric multiplicity block; it need not have equal diagonal entries. -/
def block (u v w : Real) : Matrix (Fin 2) (Fin 2) Real := ![![u, v], ![v, w]]

/-- Reconstruction from scalar response moments, rather than traces. -/
noncomputable def recovered (s1 s2 s3 : Real) (k : Nat) : Real :=
  let g := s2 - s1^2
  let z := s3 - 2*s1*s2 + s1^3
  if g = 0 then 0 else g * (z/g)^k

open TwinedTraceMemoryObstruction

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A single fixed diagonal matrix element on the retained copy. The chosen
coordinate is the same at every time; no hidden-coordinate response is queried. -/
def moment (u v w : Real) (i0 : I) (t : Nat) : Real :=
  ((liftCopies (block u v w))^t) (0, i0) (0, i0)

/-- For any supplied representation acting identically on two copies, the actual
operator and fixed observation respect the representation. Three scalar samples
at times 1,2,3 then determine the entire operator-valued memory kernel.
The coupling sign need not be recovered, and zero coupling requires no division. -/
theorem three_moments_recover_all_lags
    {G : Type*} [Group G] (rho : G →* Matrix I I Real)
    (u v w : Real) (i0 : I) :
    (∀ g : G,
      liftCopies (block u v w) * copyAction (rho g) =
        copyAction (rho g) * liftCopies (block u v w) ∧
      liftCopies firstCopy * copyAction (rho g) =
        copyAction (rho g) * liftCopies firstCopy) ∧
    moment u v w i0 1 = u ∧
    moment u v w i0 2 = u^2 + v^2 ∧
    moment u v w i0 3 = u^3 + 2*u*v^2 + v^2*w ∧
    (∀ k : Nat,
      returnKernel (liftCopies (block u v w) : Matrix (Fin 2 × I) (Fin 2 × I) Real) k =
        (v^2*w^k) • liftCopies firstCopy) ∧
    (∀ k : Nat,
      recovered (moment u v w i0 1) (moment u v w i0 2)
        (moment u v w i0 3) k • liftCopies firstCopy =
      returnKernel (liftCopies (block u v w) : Matrix (Fin 2 × I) (Fin 2 × I) Real) k) := by
  have hmul (U V : Matrix (Fin 2) (Fin 2) Real) :
      liftCopies (I := I) (U*V) = liftCopies U * liftCopies V := by
    simp only [liftCopies, ← Matrix.mul_kronecker_mul, mul_one]
  have hpow (U : Matrix (Fin 2) (Fin 2) Real) (t : Nat) :
      (liftCopies (I := I) U)^t = liftCopies (U^t) := by
    induction t with
    | zero => simpa [liftCopies] using
        (Matrix.one_kronecker_one (m := Fin 2) (n := I) (α := Real)).symm
    | succ t ih => rw [pow_succ, pow_succ, ih, hmul]
  have hQ : (1 : Matrix (Fin 2 × I) (Fin 2 × I) Real) - liftCopies firstCopy =
      liftCopies secondCopy := by
    ext i j
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    fin_cases i <;> fin_cases j <;>
      simp [liftCopies, firstCopy, secondCopy, Matrix.one_apply]
  let U := block u v w
  let B := firstCopy * U * secondCopy
  let C := secondCopy * U * firstCopy
  let D := secondCopy * U * secondCopy
  have hDC : D*C = w • C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, C, U, block, firstCopy, secondCopy,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hBC : B*C = v^2 • firstCopy := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, C, U, block, firstCopy, secondCopy,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hDCpow : ∀ k : Nat, D^k*C = w^k • C := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, hDC, smul_smul, pow_succ]
  have hreturn (k : Nat) :
      returnKernel (liftCopies U : Matrix (Fin 2 × I) (Fin 2 × I) Real) k =
        (v^2*w^k) • liftCopies firstCopy := by
    unfold returnKernel
    rw [hQ]
    change (liftCopies firstCopy * liftCopies U * liftCopies secondCopy) *
      (liftCopies secondCopy * liftCopies U * liftCopies secondCopy)^k *
      (liftCopies secondCopy * liftCopies U * liftCopies firstCopy) = _
    rw [← hmul, ← hmul, ← hmul, ← hmul, ← hmul, ← hmul, hpow,
      ← hmul, ← hmul]
    change liftCopies (I := I) (B*D^k*C) = _
    rw [mul_assoc, hDCpow, mul_smul_comm, hBC, smul_smul]
    simp only [liftCopies, Matrix.smul_kronecker]
    congr 1
    ring
  have h1 : moment u v w i0 1 = u := by
    simp [moment, liftCopies, block]
  have h2 : moment u v w i0 2 = u^2+v^2 := by
    rw [moment, hpow]
    norm_num [liftCopies, block, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h3 : moment u v w i0 3 = u^3+2*u*v^2+v^2*w := by
    rw [moment, hpow]
    norm_num [liftCopies, block, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨?_, h1, h2, h3, hreturn, ?_⟩
  · intro g
    simp only [liftCopies, copyAction, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    exact ⟨rfl, rfl⟩
  · intro k
    rw [h1, h2, h3, hreturn]
    have hg : u^2+v^2-u^2 = v^2 := by ring
    have hz : u^3+2*u*v^2+v^2*w-2*u*(u^2+v^2)+u^3 = v^2*w := by ring
    simp only [recovered, hg, hz]
    by_cases hv : v^2 = 0
    · simp [hv]
    · simp [hv, mul_div_cancel_left₀]

#print axioms three_moments_recover_all_lags

end D5.S3.Observer.ProbabilisticClosure.ThreeMomentMemoryRecovery
