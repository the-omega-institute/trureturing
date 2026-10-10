/- GID: D5/S3/Quantum/Algebra/CarryTransport/FibonacciEndpointAlgebra
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CarryTransport/FibonacciEndpointAlgebra
   mirror-E: none(waiver:unbounded-symbolic-transport)
   anchors: []
   utility: none
   digest: Exact integer-quotient carry fibers classify every native Fibonacci endpoint algebra. -/

import D5.S3.Quantum.Transport.FibonacciPrefix
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix Kronecker
namespace D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra
open D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
open D5.S3.Quantum.Transport.FibonacciPrefix
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step matrixM)

/-- The integer Fibonacci evolution of canonical low representatives. -/
def integerEvolution (d m : ℕ) (a : Labels d) : ℤ × ℤ :=
  step^[m] ((a.1.val : ℤ), (a.2.val : ℤ))

/-- Definition 4.1: the original coordinatewise integer quotient, reduced modulo e. -/
def sourceCarry (d e m : ℕ) (a : Labels d) : Labels e :=
  ((((integerEvolution d m a).1 - (lowTrajectory d m a).1.val) / (d : ℤ) : ℤ),
   (((integerEvolution d m a).2 - (lowTrajectory d m a).2.val) / (d : ℤ) : ℤ))

/-- The source matrix on the modulus-r composition labels. -/
def sourceMatrix (r : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod r) :=
  matrixM.map (Int.castRingHom (ZMod r))

private def integralCarry (d : ℕ) (a : Labels d) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | m + 1 => ((integralCarry d a m).2,
      (integralCarry d a m).1 + (integralCarry d a m).2 + (carryHistory d a m : ℤ))

private theorem integer_decomposition (d : ℕ) [NeZero d] (a : Labels d) (m : ℕ) :
    integerEvolution d m a =
      ((lowTrajectory d m a).1.val + (d : ℤ) * (integralCarry d a m).1,
       (lowTrajectory d m a).2.val + (d : ℤ) * (integralCarry d a m).2) := by
  induction m with
  | zero => simp [integerEvolution, integralCarry, lowTrajectory]
  | succ m ih =>
    have hdiv := congrArg (fun n : ℕ => (n : ℤ))
      (Nat.mod_add_div ((lowTrajectory d m a).1.val + (lowTrajectory d m a).2.val) d)
    simp only [Nat.cast_add, Nat.cast_mul] at hdiv
    rw [integerEvolution, Function.iterate_succ_apply']
    change step (integerEvolution d m a) = _
    rw [ih]
    apply Prod.ext
    · simp [step, integralCarry, lowTrajectory, Equiv.trans_apply, fibonacci]
    · simp only [step, integralCarry, lowTrajectory, Equiv.trans_apply, fibonacci,
        Equiv.coe_fn_mk, ZMod.val_add, Prod.snd]
      unfold carryHistory FibonacciOutputAlgebra.carry
      push_cast at hdiv ⊢
      linear_combination -hdiv

private theorem quotient_eq (d e m : ℕ) [NeZero d] (a : Labels d) :
    sourceCarry d e m a =
      (((integralCarry d a m).1 : ZMod e), ((integralCarry d a m).2 : ZMod e)) := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  rw [sourceCarry, integer_decomposition]
  simp only [Prod.fst, Prod.snd, add_sub_cancel_left]
  rw [Int.mul_ediv_cancel_left _ hd, Int.mul_ediv_cancel_left _ hd]

private theorem fibre_affine (d e m : ℕ) [NeZero d] (a : Labels d) (h : Labels e) :
    fibreTrajectory d e a m h = lowTrajectory e m h + sourceCarry d e m a := by
  rw [quotient_eq]
  induction m with
  | zero => simp [fibreTrajectory, lowTrajectory, integralCarry]
  | succ m ih =>
    simp only [fibreTrajectory, Equiv.trans_apply, Equiv.coe_fn_mk]
    rw [ih]
    ext <;> simp [lowTrajectory, Equiv.trans_apply, fibonacci, integralCarry,
      Prod.fst_add, Prod.snd_add] <;> ring

private theorem fibre_eq_iff (d e m : ℕ) [NeZero d] (a b : Labels d) :
    fibreTrajectory d e a m = fibreTrajectory d e b m ↔
      sourceCarry d e m a = sourceCarry d e m b := by
  constructor
  · intro h
    have hh := congrArg (fun q : Equiv.Perm (Labels e) => q (0, 0)) h
    simpa only [fibre_affine, add_left_cancel_iff] using hh
  · intro h
    apply Equiv.ext
    intro u
    rw [fibre_affine, fibre_affine, h]

private theorem matrix_evolution {R : Type*} [CommRing R]
    (m : ℕ) (x : R × R) :
    ((matrixM.map (Int.castRingHom R)) ^ m).mulVec ![x.1, x.2] =
      ![(step^[m] x).1, (step^[m] x).2] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Function.iterate_succ_apply']
    ext i
    fin_cases i <;>
      simp [matrixM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, step]

private theorem low_power (r m : ℕ) : lowTrajectory r m = fibonacci r ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', ← ih]
    simp [lowTrajectory, Equiv.Perm.mul_def]

private theorem low_iterate (r m : ℕ) (a : Labels r) :
    lowTrajectory r m a = step^[m] a := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [lowTrajectory, Equiv.trans_apply, Function.iterate_succ_apply']
    rw [ih]
    rfl

private theorem joint_power (d e : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) (m : ℕ) :
    jointTrajectory d e m = transport d e ^ m := by
  have hact := (FibonacciOutputAlgebra.result d e hd he).1
  induction m with
  | zero => apply Equiv.ext; intro x; rfl
  | succ m ih =>
    rw [pow_succ', ← ih]
    apply Equiv.ext
    rintro ⟨a,h⟩
    simp [jointTrajectory, lowTrajectory, fibreTrajectory, Equiv.Perm.mul_apply,
      Equiv.trans_apply, hact, carryHistory]

/-- The native endpoint pullback, with no intermediate-time observation. -/
def endpointPullback (d e m : ℕ) [NeZero d] [NeZero e] :=
  (Matrix.reindexAlgEquiv ℂ ℂ (transport d e ^ m).symm).toAlgHom.comp (lowTensor d e)

/-- All complex low operators whose native endpoint pullback lies in low tensor I. -/
def endpointAlgebra (d e m : ℕ) [NeZero d] [NeZero e] :
    Subalgebra ℂ (Matrix (Labels d) (Labels d) ℂ) :=
  (lowTensor d e).range.comap (endpointPullback d e m)

def endpointAlpha (d m : ℕ) [NeZero d] := Matrix.reindexAlgEquiv ℂ ℂ (lowTrajectory d m).symm

abbrev CarryLabels (d e m : ℕ) (γ : Labels e) :=
  {a : Labels d // sourceCarry d e m a = γ}

abbrev CarryBlocks (d e m : ℕ) [NeZero d] [NeZero e] :=
  ∀ γ : Labels e, Matrix (CarryLabels d e m γ) (CarryLabels d e m γ) ℂ

/-- The full matrix algebra on every actual carry fiber; empty fibers contribute zero. -/
def carryBlockEmbedding (d e m : ℕ) [NeZero d] [NeZero e] :
    CarryBlocks d e m →ₐ[ℂ] Matrix (Labels d) (Labels d) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.sigmaFiberEquiv (sourceCarry d e m))).toAlgHom.comp
    (D5.S3.Quantum.FixedAlgebra.RecordFixedAlgebraDecomposition.blockDiagonalAlgHom
      (CarryLabels d e m))

private theorem block_mem (d e m : ℕ) [NeZero d] [NeZero e]
    (B : Matrix (Labels d) (Labels d) ℂ) :
    B ∈ (carryBlockEmbedding d e m).range ↔
      ∀ a b, sourceCarry d e m a ≠ sourceCarry d e m b → B a b = 0 := by
  classical
  constructor
  · rintro ⟨blocks,rfl⟩ a b hab
    change Matrix.blockDiagonal' blocks
      ⟨sourceCarry d e m a, a, rfl⟩ ⟨sourceCarry d e m b, b, rfl⟩ = 0
    simp [Matrix.blockDiagonal'_apply, hab]
  · intro hB
    let blocks : CarryBlocks d e m := fun γ a b => B a.1 b.1
    refine ⟨blocks, ?_⟩
    ext a b
    change Matrix.blockDiagonal' blocks
      ⟨sourceCarry d e m a, a, rfl⟩ ⟨sourceCarry d e m b, b, rfl⟩ = B a b
    by_cases h : sourceCarry d e m a = sourceCarry d e m b
    · let bb : CarryLabels d e m (sourceCarry d e m a) := ⟨b,h.symm⟩
      have hbb : (⟨sourceCarry d e m b, b, rfl⟩ : Sigma (CarryLabels d e m)) =
          ⟨sourceCarry d e m a, bb⟩ := by
        apply (Equiv.sigmaFiberEquiv (sourceCarry d e m)).injective
        rfl
      rw [hbb, Matrix.blockDiagonal'_apply_eq]
    · rw [hB a b h]
      simp [Matrix.blockDiagonal'_apply, h]

private theorem moving_mem (d e m : ℕ) [NeZero d] [NeZero e]
    (B : Matrix (Labels d) (Labels d) ℂ) :
    movingPullback d e m B ∈ (lowTensor d e).range ↔
      ∀ a b, sourceCarry d e m a ≠ sourceCarry d e m b → B a b = 0 := by
  classical
  have hentry (a b : Labels d) (h h' : Labels e) :
      movingPullback d e m B (a,h) (b,h') =
        if fibreTrajectory d e a m h = fibreTrajectory d e b m h' then B a b else 0 := by
    simp [movingPullback, Matrix.reindex_apply, jointTrajectory,
      lowTensor, Matrix.one_apply, mul_ite]
  have hlowentry (C : Matrix (Labels d) (Labels d) ℂ)
      (a b : Labels d) (h h' : Labels e) :
      lowTensor d e C (a,h) (b,h') = if h = h' then C a b else 0 := by
    simp [lowTensor, Matrix.one_apply, mul_ite]
  constructor
  · rintro ⟨C, hC⟩ a b hab
    change lowTensor d e C = movingPullback d e m B at hC
    by_contra hB
    apply hab
    apply (fibre_eq_iff d e m a b).1
    apply Equiv.ext
    intro h
    let h' := (fibreTrajectory d e b m).symm (fibreTrajectory d e a m h)
    have hh : h' = h := by
      by_contra hne
      have heq := congrArg (fun X => X (a,h) (b,h')) hC
      rw [hentry, hlowentry] at heq
      have himg : fibreTrajectory d e a m h = fibreTrajectory d e b m h' := by simp [h']
      rw [if_neg (Ne.symm hne), if_pos himg] at heq
      exact hB heq.symm
    have himg : fibreTrajectory d e b m h' = fibreTrajectory d e a m h := by simp [h']
    rw [hh] at himg
    exact himg.symm
  · intro h
    refine ⟨B, ?_⟩
    change lowTensor d e B = movingPullback d e m B
    ext ⟨a,u⟩ ⟨b,v⟩
    rw [hentry, hlowentry]
    by_cases hB : B a b = 0
    · simp [hB]
    · have hab : sourceCarry d e m a = sourceCarry d e m b := by
        by_contra hab
        exact hB (h a b hab)
      rw [(fibre_eq_iff d e m a b).2 hab]
      simp only [Equiv.apply_eq_iff_eq]

private theorem endpoint_moving (d e m : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) (B : Matrix (Labels d) (Labels d) ℂ) :
    endpointPullback d e m B = movingPullback d e m (endpointAlpha d m B) := by
  rw [endpointPullback, ← joint_power d e hd he m]
  ext ⟨a,h⟩ ⟨b,g⟩
  simp [movingPullback, endpointAlpha, Matrix.reindex_apply, jointTrajectory, lowTensor]

private theorem endpoint_characterization (d e m : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) (B : Matrix (Labels d) (Labels d) ℂ) :
    B ∈ endpointAlgebra d e m ↔
      ∀ a b, sourceCarry d e m a ≠ sourceCarry d e m b → endpointAlpha d m B a b = 0 := by
  change endpointPullback d e m B ∈ (lowTensor d e).range ↔ _
  rw [endpoint_moving d e m hd he, moving_mem]

private theorem endpoint_blocks (d e m : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) :
    endpointAlgebra d e m =
      (carryBlockEmbedding d e m).range.map (endpointAlpha d m).symm.toAlgHom := by
  ext B
  rw [endpoint_characterization d e m hd he, ← block_mem]
  constructor
  · intro h
    exact ⟨endpointAlpha d m B, h, (endpointAlpha d m).symm_apply_apply B⟩
  · rintro ⟨C,hC,h⟩
    have hh : endpointAlpha d m B = C := by
      rw [← h]
      exact (endpointAlpha d m).apply_symm_apply C
    rw [hh]
    exact hC

private theorem matrix_pullback {X : Type*} [Fintype X] [DecidableEq X]
    (q : Equiv.Perm X) (B : Matrix X X ℂ) :
    (Matrix.permMatrixHom (R := ℂ) q)ᴴ * B * Matrix.permMatrixHom q =
      B.submatrix q q := by
  simp only [Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
    inv_inv, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem native_matrix (d e m : ℕ) [NeZero d] [NeZero e]
    (B : Matrix (Labels d) (Labels d) ℂ) :
    endpointPullback d e m B =
      (jointUnitary d e ^ m)ᴴ * lowTensor d e B * jointUnitary d e ^ m := by
  rw [jointUnitary, ← map_pow, matrix_pullback]
  rfl

private theorem alpha_matrix (d m : ℕ) [NeZero d]
    (B : Matrix (Labels d) (Labels d) ℂ) :
    endpointAlpha d m B = (lowUnitary d ^ m)ᴴ * B * lowUnitary d ^ m := by
  rw [lowUnitary, ← map_pow, matrix_pullback]
  rw [← low_power]
  rfl

private theorem transport_conjugate (d e m : ℕ) [NeZero d] [NeZero e]
    (x : Labels d × Labels e) :
    (transport d e ^ m) x =
      (digitJoin d e).symm ((fibonacci (d * e) ^ m) (digitJoin d e x)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [ih]
    simp [transport, Equiv.trans_apply]

private theorem matrix_period_iff (r m : ℕ) :
    sourceMatrix r ^ m = 1 ↔ fibonacci r ^ m = 1 := by
  constructor
  · intro h
    apply Equiv.ext
    intro a
    have hh := matrix_evolution m a
    rw [show matrixM.map (Int.castRingHom (ZMod r)) = sourceMatrix r from rfl, h,
      Matrix.one_mulVec] at hh
    apply Prod.ext
    · change ((fibonacci r ^ m) a).1 = a.1
      have hh0 := congrFun hh 0
      simpa only [Matrix.cons_val_zero, ← low_iterate, low_power] using hh0.symm
    · change ((fibonacci r ^ m) a).2 = a.2
      have hh1 := congrFun hh 1
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, ← low_iterate, low_power]
        using hh1.symm
  · intro h
    have heq (x : Labels r) :
        (sourceMatrix r ^ m).mulVec ![x.1,x.2] = ![x.1,x.2] := by
      rw [sourceMatrix, matrix_evolution, ← low_iterate, low_power, h]
      rfl
    have h0 := heq (1,0)
    have h1 := heq (0,1)
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using congrFun h0 0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using congrFun h1 0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using congrFun h0 1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using congrFun h1 1

private theorem period_recurrence (d e m : ℕ) [NeZero d] [NeZero e]
    (hperiod : sourceMatrix (d * e) ^ m = 1) :
    jointUnitary d e ^ m = 1 ∧ endpointAlgebra d e m = ⊤ := by
  have ht : transport d e ^ m = 1 := by
    apply Equiv.ext
    intro x
    rw [transport_conjugate, (matrix_period_iff (d * e) m).1 hperiod]
    simp
  constructor
  · rw [jointUnitary, ← map_pow, ht, map_one]
  · ext B
    simp [endpointAlgebra, endpointPullback, ht, Subalgebra.mem_comap]

private theorem alpha_inverse_matrix (d m : ℕ) [NeZero d]
    (B : Matrix (Labels d) (Labels d) ℂ) :
    (endpointAlpha d m).symm B = lowUnitary d ^ m * B * (lowUnitary d ^ m)ᴴ := by
  rw [lowUnitary, ← map_pow]
  simp only [Matrix.permMatrixHom_apply, Matrix.conjTranspose_permMatrix,
    inv_inv, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rw [← low_power]
  rfl

private theorem endpoint_one_proper (d e : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) : endpointAlgebra d e 1 ≠ ⊤ := by
  classical
  let a : Labels d := (0,0)
  let b : Labels d := ((d - 1 : ℕ), (1 : ℕ))
  have ha : carry d a = 0 := by simp [a, carry]
  have hb : carry d b = 1 := by
    simp only [b, carry, ZMod.val_natCast_of_lt (by omega : d - 1 < d),
      ZMod.val_natCast_of_lt (by omega : 1 < d)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.div_self (by omega : 0 < d)]
  let C : Matrix (Labels d) (Labels d) ℂ := Matrix.single a b 1
  let B := (alpha d).symm C
  intro htop
  have hB : B ∈ outputAlgebra d e := by
    have hh : B ∈ endpointAlgebra d e 1 := by rw [htop]; trivial
    simpa [endpointAlgebra, endpointPullback, outputAlgebra, pullback] using hh
  have hz := ((FibonacciOutputAlgebra.result d e hd he).2.1 B).1 hB a b
    (by rw [ha,hb]; omega)
  have hval : alpha d B a b = 1 := by
    simp [B, C, Matrix.single_apply]
  rw [hval] at hz
  exact one_ne_zero hz

/-- Complete Theorem 4.5 on the original digit-transported Fibonacci objects. -/
theorem result (d e : ℕ) [NeZero d] [NeZero e] (hd : 2 ≤ d) (he : 2 ≤ e) :
    (∀ m a, ![(integerEvolution d m a).1, (integerEvolution d m a).2] =
      (matrixM ^ m).mulVec ![(a.1.val : ℤ), (a.2.val : ℤ)]) ∧
    (∀ m a, (d : ℤ) ∣ (integerEvolution d m a).1 - (lowTrajectory d m a).1.val ∧
      (d : ℤ) ∣ (integerEvolution d m a).2 - (lowTrajectory d m a).2.val) ∧
    (∀ m a h, fibreTrajectory d e a m h =
      lowTrajectory e m h + sourceCarry d e m a) ∧
    (∀ m a b, fibreTrajectory d e a m = fibreTrajectory d e b m ↔
      sourceCarry d e m a = sourceCarry d e m b) ∧
    (∀ m B, endpointPullback d e m B =
      (jointUnitary d e ^ m)ᴴ * lowTensor d e B * jointUnitary d e ^ m) ∧
    (∀ m B, endpointAlpha d m B = (lowUnitary d ^ m)ᴴ * B * lowUnitary d ^ m) ∧
    (∀ m B, (endpointAlpha d m).symm B =
      lowUnitary d ^ m * B * (lowUnitary d ^ m)ᴴ) ∧
    (∀ m B, B ∈ endpointAlgebra d e m ↔
      ∀ a b, sourceCarry d e m a ≠ sourceCarry d e m b → endpointAlpha d m B a b = 0) ∧
    (∀ m, endpointAlgebra d e m =
      (carryBlockEmbedding d e m).range.map (endpointAlpha d m).symm.toAlgHom) ∧
    (∀ m, sourceMatrix (d * e) ^ m = 1 →
      jointUnitary d e ^ m = 1 ∧ endpointAlgebra d e m = ⊤) ∧
    (∃ m : ℕ, 1 ≤ m ∧ sourceMatrix (d * e) ^ m = 1) ∧
    ¬ (∀ m n : ℕ, 1 ≤ m → m ≤ n → endpointAlgebra d e n ≤ endpointAlgebra d e m) := by
  classical
  have hpositive : ∃ m : ℕ, 1 ≤ m ∧ sourceMatrix (d * e) ^ m = 1 := by
    refine ⟨orderOf (fibonacci (d * e)), ?_, ?_⟩
    · exact orderOf_pos (fibonacci (d * e))
    · exact (matrix_period_iff _ _).2 (pow_orderOf_eq_one _)
  have hnotanti : ¬ (∀ m n : ℕ, 1 ≤ m → m ≤ n →
      endpointAlgebra d e n ≤ endpointAlgebra d e m) := by
    intro hanti
    obtain ⟨m,hm,hperiod⟩ := hpositive
    have hh := hanti 1 m le_rfl hm
    rw [(period_recurrence d e m hperiod).2] at hh
    exact endpoint_one_proper d e hd he (top_le_iff.mp hh)
  refine ⟨?_, ?_, (fun m => fibre_affine d e m), (fun m => fibre_eq_iff d e m),
    (fun m => native_matrix d e m), (fun m => alpha_matrix d m),
    (fun m => alpha_inverse_matrix d m),
    (fun m => endpoint_characterization d e m hd he),
    (fun m => endpoint_blocks d e m hd he),
    (fun m => period_recurrence d e m), hpositive, hnotanti⟩
  · intro m a
    have hh := matrix_evolution m ((a.1.val : ℤ), (a.2.val : ℤ))
    simpa [integerEvolution, Matrix.map_id] using hh.symm
  · intro m a
    rw [integer_decomposition]
    simp only [Prod.fst, Prod.snd, add_sub_cancel_left]
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

#print axioms result
#print axioms integer_decomposition
#print axioms fibre_affine
end D5.S3.Quantum.Algebra.CarryTransport.FibonacciEndpointAlgebra
