/- GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ClauseHamiltonian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential]
   utility: none
   digest: Local raw clause projectors encode a Boolean count in a centered full complex trace. -/

import Std.Sat.CNF.Basic
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace PredictiveThermodynamic.Physical

open scoped Matrix Kronecker CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

abbrev Assignment (n : Nat) := Fin n -> Bool
abbrev Formula (n : Nat) := List (Std.Sat.CNF.Clause (Fin n))

def standardFormula {n : Nat} (F : Formula n) : Std.Sat.CNF (Fin n) :=
  ⟨F.toArray⟩

def satisfyingCount {n : Nat} (F : Formula n) : Nat :=
  (Finset.univ.filter (fun a : Assignment n => (standardFormula F).eval a = true)).card

def violations {n : Nat} (F : Formula n) (a : Assignment n) : Nat :=
  (F.filter (fun c => !(c.eval a))).length

def clauseProjector {n : Nat} (c : Std.Sat.CNF.Clause (Fin n)) :
    Matrix (Assignment n) (Assignment n) Complex :=
  Matrix.diagonal (fun a => if c.eval a then 0 else 1)

def hiddenHamiltonian {n : Nat} (F : Formula n) :
    Matrix (Assignment n) (Assignment n) Complex :=
  ((n + 1 : Nat) : Complex) • (F.map clauseProjector).sum

def visibleProjector : Matrix Bool Bool Complex :=
  Matrix.diagonal (fun b => if b then 1 else 0)

def fullHamiltonian {n : Nat} (F : Formula n) :
    Matrix (Bool × Assignment n) (Bool × Assignment n) Complex :=
  visibleProjector ⊗ₖ 1 + (1 : Matrix Bool Bool Complex) ⊗ₖ hiddenHamiltonian F

def fullPartition {n : Nat} (F : Formula n) : Complex :=
  Matrix.trace (NormedSpace.exp (-(Real.log 2 : Complex) • fullHamiltonian F))

def partitionNumerator {n : Nat} (F : Formula n) : Nat :=
  ∑ a : Assignment n, 2 ^ ((n + 1) * (F.length - violations F a))

theorem clause_partition_recovery {n : Nat} (F : Formula n) :
    (fullPartition F =
        3 * (partitionNumerator F : Complex) / 2 ^ ((n + 1) * F.length + 1) ∧
      Int.floor ((2 / 3 : Real) * (fullPartition F).re) = (satisfyingCount F : Int)) ∧
    (hiddenHamiltonian F).IsHermitian ∧ (fullHamiltonian F).IsHermitian ∧
    (∀ c ∈ F, (clauseProjector c).IsHermitian ∧
      clauseProjector c * clauseProjector c = clauseProjector c ∧
      ∃ s : Finset (Fin n), s.card ≤ c.length ∧
        ∀ a b : Assignment n, (∀ i ∈ s, a i = b i) →
          clauseProjector c a a = clauseProjector c b b) ∧
    ((Fintype.card (Assignment n) : Complex)⁻¹ •
        partialTraceRight (fullHamiltonian F) -
      (Matrix.trace (fullHamiltonian F) /
        (2 * (Fintype.card (Assignment n) : Complex))) • (1 : Matrix Bool Bool Complex) =
      visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)) ∧
    (1 / 2 : Complex) • partialTraceLeft (fullHamiltonian F) =
      hiddenHamiltonian F + (1 / 2 : Complex) •
        (1 : Matrix (Assignment n) (Assignment n) Complex) ∧
    fullHamiltonian F =
      (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)) ⊗ₖ 1 +
      (1 : Matrix Bool Bool Complex) ⊗ₖ
        (hiddenHamiltonian F + (1 / 2 : Complex) •
          (1 : Matrix (Assignment n) (Assignment n) Complex)) ∧
    (∀ M : Matrix Bool Bool Complex,
      fullHamiltonian F * (M ⊗ₖ 1) - (M ⊗ₖ 1) * fullHamiltonian F =
        (visibleProjector * M - M * visibleProjector) ⊗ₖ
          (1 : Matrix (Assignment n) (Assignment n) Complex)) ∧
    (∀ c d : Std.Sat.CNF.Clause (Fin n),
      clauseProjector c * clauseProjector d = clauseProjector d * clauseProjector c) ∧
    clauseProjector (n := n) [] = 1 ∧
    (∀ M : Matrix Bool Bool Complex,
      let C := fullHamiltonian F * (M ⊗ₖ 1) - (M ⊗ₖ 1) * fullHamiltonian F
      C - ((Fintype.card (Assignment n) : Complex)⁻¹ • partialTraceRight C) ⊗ₖ
        (1 : Matrix (Assignment n) (Assignment n) Complex) = 0) ∧
    (∀ (t : Real) (rho : Matrix (Bool × Assignment n) (Bool × Assignment n) Complex),
      let U := NormedSpace.exp ((-Complex.I * (t : Complex)) • fullHamiltonian F)
      let U_A := NormedSpace.exp ((-Complex.I * (t : Complex)) •
        (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)))
      partialTraceRight (U * rho * star U) =
        U_A * partialTraceRight rho * star U_A) ∧
    (let beta := Real.log 2
     let X := CStarMatrix.ofMatrix (-(beta : Complex) • fullHamiltonian F)
     let A := CStarMatrix.ofMatrix (-(beta : Complex) • visibleProjector)
     let B := CStarMatrix.ofMatrix (-(beta : Complex) • hiddenHamiltonian F)
     let Ac := CStarMatrix.ofMatrix (-(beta : Complex) •
       (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)))
     let Bc := CStarMatrix.ofMatrix (-(beta : Complex) •
       (hiddenHamiltonian F + (1 / 2 : Complex) •
         (1 : Matrix (Assignment n) (Assignment n) Complex)))
     ∃ hX : IsSelfAdjoint X, ∃ hA : IsSelfAdjoint A, ∃ hB : IsSelfAdjoint B,
     ∃ hAc : IsSelfAdjoint Ac, ∃ hBc : IsSelfAdjoint Bc,
       gibbsState X hX = productState (gibbsState Ac hAc) (gibbsState B hB) ∧
       gibbsState Ac hAc = gibbsState A hA ∧
       gibbsState Bc hBc = gibbsState B hB ∧
       partialTraceLeft (CStarMatrix.ofMatrix.symm (gibbsState X hX).1) =
         CStarMatrix.ofMatrix.symm (gibbsState B hB).1 ∧
       (n = 0 → CStarMatrix.ofMatrix.symm (gibbsState B hB).1 = 1) ∧
       ∀ rho : DensityState Bool,
         SupportContained rho (gibbsState Ac hAc) ∧
         SupportContained (productState rho (gibbsState B hB)) (gibbsState X hX) ∧
         partialTraceRight (CStarMatrix.ofMatrix.symm
           (productState rho (gibbsState B hB)).1) = CStarMatrix.ofMatrix.symm rho.1 ∧
         extendedQuantumRelativeEntropy (productState rho (gibbsState B hB))
           (gibbsState X hX) = extendedQuantumRelativeEntropy rho (gibbsState Ac hAc) ∧
         quantumRelativeEntropy (productState rho (gibbsState B hB)) (gibbsState X hX) -
           quantumRelativeEntropy rho (gibbsState Ac hAc) = 0 ∧
         extendedQuantumRelativeEntropy (productState rho (gibbsState B hB))
           (productState rho (gibbsState B hB)) = 0) := by
  classical
  have hsum : (F.map clauseProjector).sum =
      Matrix.diagonal (fun a => (violations F a : Complex)) := by
    induction F with
    | nil => simp [violations]
    | cons c F ih =>
      simp only [List.map_cons, List.sum_cons, ih, clauseProjector]
      rw [Matrix.diagonal_add]
      congr 1
      funext a
      cases h : c.eval a <;> simp [violations, h, add_comm]
  have hiddenDiagonal : hiddenHamiltonian F =
      Matrix.diagonal (fun a => (((n + 1) * violations F a : Nat) : Complex)) := by
    rw [hiddenHamiltonian, hsum]
    ext a b
    by_cases h : a = b
    · subst b; simp [Matrix.diagonal, Nat.cast_mul, smul_eq_mul]
    · simp [Matrix.diagonal, h]
  have fullDiagonal : fullHamiltonian F = Matrix.diagonal
      (fun ba : Bool × Assignment n =>
        ((ba.1.toNat + (n + 1) * violations F ba.2 : Nat) : Complex)) := by
    rw [fullHamiltonian, visibleProjector, hiddenDiagonal,
      show (1 : Matrix Bool Bool Complex) = Matrix.diagonal (fun _ => 1) by simp,
      show (1 : Matrix (Assignment n) (Assignment n) Complex) =
        Matrix.diagonal (fun _ => 1) by simp,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_add]
    congr 1
    funext ba
    rcases ba with ⟨b, a⟩
    cases b <;> simp
  have boltzmann : ∀ k : Nat,
      Complex.exp (-(Real.log 2 : Complex) * (k : Complex)) = (1 / 2 : Complex) ^ k := by
    intro k
    have base : Complex.exp (-(Real.log 2 : Complex)) = 1 / 2 := by
      rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
      norm_num
    rw [show -(Real.log 2 : Complex) * (k : Complex) =
      (k : Complex) * -(Real.log 2 : Complex) by ring, Complex.exp_nat_mul, base]
  let z : Real := ∑ a : Assignment n, (1 / 2 : Real) ^ ((n + 1) * violations F a)
  have traceFormula : fullPartition F = ((3 / 2 : Real) * z : Real) := by
    unfold fullPartition
    rw [fullDiagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.trace_diagonal]
    simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul,
      ← Complex.exp_eq_exp_ℂ, boltzmann]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add, pow_add, pow_one,
      ]
    simp only [← Finset.mul_sum]
    dsimp [z]
    push_cast
    ring
  have satZero : ∀ a : Assignment n,
      violations F a = 0 ↔ (standardFormula F).eval a = true := by
    intro a
    induction F with
    | nil => simp [violations, standardFormula, Std.Sat.CNF.eval]
    | cons c F ih =>
      cases h : c.eval a <;>
        simp_all [violations, standardFormula, Std.Sat.CNF.eval,
          List.all_cons]
  let tail : Real := ∑ a : Assignment n,
    if (standardFormula F).eval a then 0 else (1 / 2 : Real) ^ ((n + 1) * violations F a)
  have splitSum : z = (satisfyingCount F : Real) + tail := by
    have splitPoint : ∀ a : Assignment n,
        (1 / 2 : Real) ^ ((n + 1) * violations F a) =
          (if (standardFormula F).eval a then 1 else 0) +
          (if (standardFormula F).eval a then 0
            else (1 / 2 : Real) ^ ((n + 1) * violations F a)) := by
      intro a
      cases h : (standardFormula F).eval a
      · simp
      · have hv := (satZero a).mpr h
        simp [hv]
    dsimp [z, tail]
    rw [Finset.sum_congr rfl (fun a _ => splitPoint a)]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [satisfyingCount]
  have weightBound : ∀ a : Assignment n,
      0 ≤ (if (standardFormula F).eval a then 0
        else (1 / 2 : Real) ^ ((n + 1) * violations F a)) ∧
      (if (standardFormula F).eval a then 0
        else (1 / 2 : Real) ^ ((n + 1) * violations F a)) ≤ (1 / 2 : Real) ^ (n + 1) := by
    intro a
    cases h : (standardFormula F).eval a with
    | true => simp
    | false =>
      have hv : 0 < violations F a := by
        apply Nat.pos_of_ne_zero
        intro hv
        have := (satZero a).mp hv
        simp [h] at this
      simp only [Bool.false_eq_true, if_false]
      constructor
      · positivity
      · apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
        nlinarith
  have tailNonnegative : 0 ≤ tail :=
    Finset.sum_nonneg (fun a _ => (weightBound a).1)
  have tailBound : tail ≤ 1 / 2 := by
    calc
      tail ≤ ∑ _a : Assignment n, (1 / 2 : Real) ^ (n + 1) :=
        Finset.sum_le_sum (fun a _ => (weightBound a).2)
      _ = (2 : Real) ^ n * (1 / 2 : Real) ^ (n + 1) := by
        simp
      _ = 1 / 2 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]
        norm_num
  have recoveredReal : (2 / 3 : Real) * (fullPartition F).re = z := by
    rw [traceFormula]
    simp only [Complex.ofReal_re]
    ring
  have numeratorFormula : z = (partitionNumerator F : Real) / 2 ^ ((n + 1) * F.length) := by
    have termFormula : ∀ a : Assignment n,
        (1 / 2 : Real) ^ ((n + 1) * violations F a) =
          (2 : Real) ^ ((n + 1) * (F.length - violations F a)) /
            (2 : Real) ^ ((n + 1) * F.length) := by
      intro a
      have hv : violations F a ≤ F.length := List.length_filter_le _ _
      have hpower : (n + 1) * (F.length - violations F a) +
          (n + 1) * violations F a = (n + 1) * F.length := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hv]
      rw [one_div_pow, eq_div_iff (by positivity), ← hpower, pow_add]
      field_simp
    dsimp [z, partitionNumerator]
    simp_rw [termFormula]
    rw [← Finset.sum_div]
    norm_cast
  have localCommutator : ∀ M : Matrix Bool Bool Complex,
      fullHamiltonian F * (M ⊗ₖ 1) - (M ⊗ₖ 1) * fullHamiltonian F =
        (visibleProjector * M - M * visibleProjector) ⊗ₖ
          (1 : Matrix (Assignment n) (Assignment n) Complex) := by
    intro M
    rw [fullHamiltonian, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
    ext ab cd
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, localCommutator, ?_, ?_, ?_, ?_, ?_⟩
  · rw [traceFormula, numeratorFormula]
    push_cast
    rw [pow_succ]
    field_simp
  · rw [recoveredReal]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> rw [splitSum]
    · linarith
    · linarith
  · rw [hiddenDiagonal]
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro a
    simp [isSelfAdjoint_iff]
  · rw [fullDiagonal]
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro a
    simp [isSelfAdjoint_iff]
  · intro c _
    refine ⟨?_, ?_, (c.map Prod.fst).toFinset, ?_, ?_⟩
    · apply Matrix.isHermitian_diagonal_iff.mpr
      intro a
      cases c.eval a <;> simp [isSelfAdjoint_iff]
    · simp only [clauseProjector, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      cases c.eval a <;> simp
    · exact (List.toFinset_card_le _).trans (by simp)
    · intro a b hab
      have same := Std.Sat.CNF.Clause.eval_congr a b c (by
        intro i hi
        apply hab i
        rcases hi with hi | hi
        · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(i, false), hi, rfl⟩)
        · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(i, true), hi, rfl⟩))
      simp only [clauseProjector, Matrix.diagonal_apply_eq, same]
  · have visibleTrace : Matrix.trace visibleProjector = 1 := by
      simp [visibleProjector, Matrix.trace_diagonal, Fintype.sum_bool]
    have cardNonzero : (Fintype.card (Assignment n) : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Assignment n)))
    have rightVisible : partialTraceRight
        (visibleProjector ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) =
        Matrix.trace (1 : Matrix (Assignment n) (Assignment n) Complex) •
          visibleProjector := partialTraceRight_kronecker _ _
    have rightHidden : partialTraceRight
        ((1 : Matrix Bool Bool Complex) ⊗ₖ hiddenHamiltonian F) =
        Matrix.trace (hiddenHamiltonian F) • (1 : Matrix Bool Bool Complex) :=
      partialTraceRight_kronecker _ _
    rw [fullHamiltonian, partialTraceRight_add, rightVisible, rightHidden, Matrix.trace_add,
      Matrix.trace_kronecker, Matrix.trace_kronecker, visibleTrace]
    simp only [Matrix.trace_one, Fintype.card_bool, Nat.cast_ofNat, one_mul,
      smul_add, smul_smul]
    rw [inv_mul_cancel₀ cardNonzero, one_smul]
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  · have visibleTrace : Matrix.trace visibleProjector = 1 := by
      simp [visibleProjector, Matrix.trace_diagonal, Fintype.sum_bool]
    have leftVisible : partialTraceLeft
        (visibleProjector ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) =
        Matrix.trace visibleProjector • (1 : Matrix (Assignment n) (Assignment n) Complex) :=
      partialTraceLeft_kronecker _ _
    have leftHidden : partialTraceLeft
        ((1 : Matrix Bool Bool Complex) ⊗ₖ hiddenHamiltonian F) =
        Matrix.trace (1 : Matrix Bool Bool Complex) • hiddenHamiltonian F :=
      partialTraceLeft_kronecker _ _
    rw [fullHamiltonian, partialTraceLeft_add, leftVisible, leftHidden, visibleTrace]
    simp only [Matrix.trace_one, Fintype.card_bool, Nat.cast_ofNat, one_smul,
      smul_add, smul_smul]
    norm_num
    rw [add_comm]
  · ext ab cd
    simp only [fullHamiltonian, Matrix.add_apply, Matrix.sub_apply,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · intro c d
    simp only [clauseProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring
  · ext a b
    simp [clauseProjector, Std.Sat.CNF.Clause.eval, Matrix.diagonal, Matrix.one_apply]
  · intro M
    dsimp only
    have htrace : partialTraceRight
        ((visibleProjector * M - M * visibleProjector) ⊗ₖ
          (1 : Matrix (Assignment n) (Assignment n) Complex)) =
        Matrix.trace (1 : Matrix (Assignment n) (Assignment n) Complex) •
          (visibleProjector * M - M * visibleProjector) :=
      partialTraceRight_kronecker _ _
    rw [localCommutator, htrace]
    have hc : (Fintype.card (Assignment n) : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Assignment n)))
    simp only [Matrix.trace_one, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_self]
  · intro t rho
    dsimp only
    have fullExp : NormedSpace.exp ((-Complex.I * (t : Complex)) • fullHamiltonian F) =
        Matrix.diagonal (fun ba : Bool × Assignment n =>
          Complex.exp (-Complex.I * (t : Complex) *
            ((ba.1.toNat + (n + 1) * violations F ba.2 : Nat) : Complex))) := by
      rw [fullDiagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
      congr 1
      funext ba
      simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
    have visibleDiagonal : visibleProjector -
        (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex) =
        Matrix.diagonal (fun b : Bool => (b.toNat : Complex) - 1 / 2) := by
      ext b c
      cases b <;> cases c <;> simp [visibleProjector, Matrix.diagonal]
    have visibleExp : NormedSpace.exp ((-Complex.I * (t : Complex)) •
        (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex))) =
        Matrix.diagonal (fun b : Bool => Complex.exp
          (-Complex.I * (t : Complex) * ((b.toNat : Complex) - 1 / 2))) := by
      rw [visibleDiagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
      congr 1
      funext b
      simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
    have phaseCancellation (b c : Bool) (a : Assignment n) :
        Complex.exp (-Complex.I * (t : Complex) *
            ((b.toNat + (n + 1) * violations F a : Nat) : Complex)) *
          star (Complex.exp (-Complex.I * (t : Complex) *
            ((c.toNat + (n + 1) * violations F a : Nat) : Complex))) =
        Complex.exp (-Complex.I * (t : Complex) * ((b.toNat : Complex) - 1 / 2)) *
          star (Complex.exp (-Complex.I * (t : Complex) *
            ((c.toNat : Complex) - 1 / 2))) := by
      simp only [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, map_neg, map_sub, Complex.conj_I, Complex.conj_ofReal,
        map_natCast, map_div₀, map_ofNat, map_add, map_one, Nat.cast_add, Nat.cast_mul]
      ring
    rw [fullExp, visibleExp]
    ext ab cd
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal, partialTraceRight,
      Pi.star_def]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = rho (ab, a) (cd, a) *
          (Complex.exp (-Complex.I * (t : Complex) *
            ((ab.toNat + (n + 1) * violations F a : Nat) : Complex)) *
          star (Complex.exp (-Complex.I * (t : Complex) *
            ((cd.toNat + (n + 1) * violations F a : Nat) : Complex)))) := by ring
      _ = _ := by rw [phaseCancellation]; ring
  · classical
    have adjoint {D : Type} [Fintype D] [DecidableEq D] (f : D → Real) :
        IsSelfAdjoint (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex)))) := by
      change (Matrix.diagonal (fun d => (f d : Complex))).IsHermitian
      apply Matrix.isHermitian_diagonal_iff.mpr
      intro d
      simp [isSelfAdjoint_iff]
    have exponent {D : Type} [Fintype D] [DecidableEq D] (f : D → Real) :
        NormedSpace.exp (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex)))) =
          CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (Real.exp (f d) : Complex))) := by
      letI : NormedAlgebra Rat (Matrix D D Complex) :=
        NormedAlgebra.restrictScalars Rat Complex _
      letI : NormedAlgebra Rat (CStarMatrix D D Complex) :=
        NormedAlgebra.restrictScalars Rat Complex _
      have bridge : CStarMatrix.ofMatrix
          (NormedSpace.exp (Matrix.diagonal (fun d => (f d : Complex)))) =
          NormedSpace.exp (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex)))) :=
        NormedSpace.map_exp CStarMatrix.ofMatrixRingEquiv
          CStarMatrix.ofMatrixL.continuous (Matrix.diagonal (fun d => (f d : Complex)))
      rw [← bridge, Matrix.exp_diagonal]
      change Matrix.diagonal (NormedSpace.exp (fun d => (f d : Complex))) =
        Matrix.diagonal (fun d => (Real.exp (f d) : Complex))
      congr 1
      funext d
      simp only [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
    have partition {D : Type} [Fintype D] [DecidableEq D] (f : D → Real) :
        partitionFunction (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex)))) =
          ∑ d, Real.exp (f d) := by
      rw [partitionFunction, exponent]
      change (Matrix.trace (Matrix.diagonal (fun d => (Real.exp (f d) : Complex)))).re = _
      simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
    have shift {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
        (f : D → Real) (c : Real) :
        gibbsState (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => ((f d + c : Real) : Complex))))
            (adjoint (fun d => f d + c)) =
          gibbsState (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex))))
            (adjoint f) := by
      have shiftedPartition : partitionFunction (CStarMatrix.ofMatrix
          (Matrix.diagonal (fun d => ((f d + c : Real) : Complex)))) =
          partitionFunction (CStarMatrix.ofMatrix (Matrix.diagonal (fun d => (f d : Complex)))) *
            Real.exp c := by
        rw [partition, partition]
        simp_rw [Real.exp_add]
        rw [Finset.sum_mul]
      apply Subtype.ext
      change (partitionFunction _)⁻¹ • NormedSpace.exp _ =
        (partitionFunction _)⁻¹ • NormedSpace.exp _
      rw [shiftedPartition, exponent, exponent]
      change ((partitionFunction _) * Real.exp c)⁻¹ •
          Matrix.diagonal (fun d => (Real.exp (f d + c) : Complex)) =
        (partitionFunction _)⁻¹ • Matrix.diagonal (fun d => (Real.exp (f d) : Complex))
      rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul]
      congr 1
      funext d
      simp only [Pi.smul_apply, Complex.real_smul, Real.exp_add,
        Complex.ofReal_mul, mul_inv_rev, Complex.ofReal_inv]
      have hc : (Real.exp c : Complex) ≠ 0 := by exact_mod_cast Real.exp_ne_zero c
      field_simp
    let x : Bool → Real := fun b => -Real.log 2 * b.toNat
    let y : Assignment n → Real := fun a => -Real.log 2 * ((n + 1) * violations F a)
    let zxy : Bool × Assignment n → Real := fun ba => x ba.1 + y ba.2
    have diagA : -(Real.log 2 : Complex) • visibleProjector =
        Matrix.diagonal (fun b => (x b : Complex)) := by
      ext b c
      cases b <;> cases c <;> simp [visibleProjector, Matrix.diagonal, x, smul_eq_mul]
    have diagB : -(Real.log 2 : Complex) • hiddenHamiltonian F =
        Matrix.diagonal (fun a => (y a : Complex)) := by
      rw [hiddenDiagonal, ← Matrix.diagonal_smul]
      congr 1
      funext a
      simp [y, smul_eq_mul]
    have diagX : -(Real.log 2 : Complex) • fullHamiltonian F =
        Matrix.diagonal (fun ba => (zxy ba : Complex)) := by
      rw [fullDiagonal, ← Matrix.diagonal_smul]
      congr 1
      funext ba
      simp [zxy, x, y, smul_eq_mul]
      ring
    have diagAc : -(Real.log 2 : Complex) •
        (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)) =
        Matrix.diagonal (fun b => ((x b + Real.log 2 / 2 : Real) : Complex)) := by
      rw [smul_sub, diagA]
      ext b c
      by_cases h : b = c
      · subst c
        simp [Matrix.diagonal, x, smul_eq_mul]
        ring
      · simp [Matrix.diagonal, h, Matrix.one_apply]
    have diagBc : -(Real.log 2 : Complex) •
        (hiddenHamiltonian F + (1 / 2 : Complex) •
          (1 : Matrix (Assignment n) (Assignment n) Complex)) =
        Matrix.diagonal (fun a => ((y a + -(Real.log 2 / 2) : Real) : Complex)) := by
      rw [smul_add, diagB]
      ext a b
      by_cases h : a = b
      · subst b
        simp [Matrix.diagonal, y, smul_eq_mul]
        ring
      · simp [Matrix.diagonal, h, Matrix.one_apply]
    dsimp only
    rw [diagX, diagA, diagB, diagAc, diagBc]
    let hX := adjoint zxy
    let hA := adjoint x
    let hB := adjoint y
    let hAc := adjoint (fun b => x b + Real.log 2 / 2)
    let hBc := adjoint (fun a => y a + -(Real.log 2 / 2))
    let X := CStarMatrix.ofMatrix (Matrix.diagonal (fun ba => (zxy ba : Complex)))
    let A := CStarMatrix.ofMatrix (Matrix.diagonal (fun b => (x b : Complex)))
    let B := CStarMatrix.ofMatrix (Matrix.diagonal (fun a => (y a : Complex)))
    let gammaA := gibbsState A hA
    let gammaB := gibbsState B hB
    have partitionProduct : partitionFunction X = partitionFunction A * partitionFunction B := by
      dsimp [X, A, B]
      rw [partition, partition, partition, Fintype.sum_prod_type]
      simp_rw [zxy, Real.exp_add]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    have gibbsProduct : gibbsState X hX = productState gammaA gammaB := by
      apply Subtype.ext
      change (partitionFunction X)⁻¹ • NormedSpace.exp X = CStarMatrix.ofMatrix
        (((partitionFunction A)⁻¹ • CStarMatrix.ofMatrix.symm (NormedSpace.exp A)) ⊗ₖ
          ((partitionFunction B)⁻¹ • CStarMatrix.ofMatrix.symm (NormedSpace.exp B)))
      rw [partitionProduct]
      dsimp [X, A, B]
      rw [exponent, exponent, exponent]
      change ((partitionFunction _) * (partitionFunction _))⁻¹ •
          Matrix.diagonal (fun ba => (Real.exp (zxy ba) : Complex)) =
        (((partitionFunction _)⁻¹ • Matrix.diagonal (fun b => (Real.exp (x b) : Complex))) ⊗ₖ
          ((partitionFunction _)⁻¹ • Matrix.diagonal (fun a => (Real.exp (y a) : Complex))))
      rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul,
        Matrix.diagonal_kronecker_diagonal]
      congr 1
      funext ba
      simp only [zxy, Pi.smul_apply, mul_inv_rev, Complex.real_smul,
        Real.exp_add, Complex.ofReal_mul]
      ring
    have tensorSum : CStarMatrix.ofMatrix.symm X =
        CStarMatrix.ofMatrix.symm A ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex) +
          (1 : Matrix Bool Bool Complex) ⊗ₖ CStarMatrix.ofMatrix.symm B := by
      change Matrix.diagonal (fun ba => (zxy ba : Complex)) =
        Matrix.diagonal (fun b => (x b : Complex)) ⊗ₖ
          (1 : Matrix (Assignment n) (Assignment n) Complex) +
        (1 : Matrix Bool Bool Complex) ⊗ₖ Matrix.diagonal (fun a => (y a : Complex))
      rw [show (1 : Matrix Bool Bool Complex) = Matrix.diagonal (fun _ => 1) by simp,
        show (1 : Matrix (Assignment n) (Assignment n) Complex) =
          Matrix.diagonal (fun _ => 1) by simp,
        Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal,
        Matrix.diagonal_add]
      congr 1
      funext ba
      simp [zxy]
    have supported {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
        (Z : CStarMatrix D D Complex) (hZ : IsSelfAdjoint Z) (state : DensityState D) :
        SupportContained state (gibbsState Z hZ) := by
      have hp := gibbs_state_posDef Z hZ
      intro v hv
      change CStarMatrix.ofMatrix.symm (gibbsState Z hZ).1 *ᵥ v = 0 at hv
      have hz : v = 0 := Matrix.mulVec_injective_of_isUnit hp.isUnit (by
        simpa only [Matrix.mulVec_zero] using hv)
      subst v
      exact Matrix.mulVec_zero _
    refine ⟨hX, hA, hB, hAc, hBc, ?_, shift x (Real.log 2 / 2),
      shift y (-(Real.log 2 / 2)), ?_, ?_, ?_⟩
    · rw [shift x (Real.log 2 / 2)]
      exact gibbsProduct
    · rw [gibbsProduct]
      exact congrArg (fun s : DensityState (Assignment n) => CStarMatrix.ofMatrix.symm s.1)
        (marginalLeft_productState gammaA gammaB)
    · intro hn
      subst n
      have ht : Matrix.trace (CStarMatrix.ofMatrix.symm gammaB.1) = 1 := gammaB.2.2
      ext a b
      have ab : a = b := Subsingleton.elim _ _
      subst b
      change CStarMatrix.ofMatrix.symm gammaB.1 a a = 1
      have same (c : Assignment 0) : CStarMatrix.ofMatrix.symm gammaB.1 c c =
          CStarMatrix.ofMatrix.symm gammaB.1 a a := by
        have h : c = a := Subsingleton.elim _ _
        subst c
        rfl
      simp only [Matrix.trace, Matrix.diag_apply] at ht
      simp_rw [same] at ht
      simpa using ht
    · intro rho
      have rhoTrace : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 := rho.2.2
      have sigmaTrace : Matrix.trace (CStarMatrix.ofMatrix.symm gammaB.1) = 1 := gammaB.2.2
      have selfZero : quantumRelativeEntropy gammaB gammaB = 0 := by
        simp only [quantumRelativeEntropy, sub_self, mul_zero]
        change (Matrix.trace (0 : Matrix (Assignment n) (Assignment n) Complex)).re = 0
        simp
      have energies :
          (Matrix.trace (CStarMatrix.ofMatrix.symm (X * (productState rho gammaB).1))).re =
            (Matrix.trace (CStarMatrix.ofMatrix.symm (A * rho.1))).re +
              (Matrix.trace (CStarMatrix.ofMatrix.symm (B * gammaB.1))).re := by
        change (Matrix.trace (CStarMatrix.ofMatrix.symm X *
          (CStarMatrix.ofMatrix.symm rho.1 ⊗ₖ CStarMatrix.ofMatrix.symm gammaB.1))).re = _
        rw [tensorSum, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
          Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker,
          rhoTrace, sigmaTrace, mul_one, one_mul, Complex.add_re]
        rfl
      have logarithms : Real.log (partitionFunction X) =
          Real.log (partitionFunction A) + Real.log (partitionFunction B) := by
        rw [partitionProduct, Real.log_mul
          (ne_of_gt (partition_function_pos A hA)) (ne_of_gt (partition_function_pos B hB))]
      have joint := gibbs_variational_identity X hX (productState rho gammaB)
      have visible := gibbs_variational_identity A hA rho
      have hidden := gibbs_variational_identity B hB gammaB
      change _ = _ + _ + quantumRelativeEntropy gammaB gammaB at hidden
      rw [selfZero] at hidden
      rw [energies, vonNeumannEntropy_productState, logarithms] at joint
      have equality : quantumRelativeEntropy (productState rho gammaB) (gibbsState X hX) =
          quantumRelativeEntropy rho gammaA := by linarith
      rw [shift x (Real.log 2 / 2)]
      refine ⟨supported A hA rho, supported X hX _, ?_, ?_, ?_,
        extendedQuantumRelativeEntropy_self _⟩
      · exact congrArg (fun s : DensityState Bool => CStarMatrix.ofMatrix.symm s.1)
          (marginalRight_productState rho gammaB)
      · rw [extendedQuantumRelativeEntropy_eq_coe_of_support (supported X hX _),
          extendedQuantumRelativeEntropy_eq_coe_of_support (supported A hA rho)]
        exact congrArg (fun r : Real => (r : WithTop Real)) equality
      · exact sub_eq_zero.mpr equality

end PredictiveThermodynamic.Physical
