/- GID: D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/CoPRelativeQuantumnessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.claim; result=D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result; claim=D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.claim
   digest: A commutativity-preserving qubit channel increases Q at alpha zero. -/

/-
proof_shape: result: bind-only. After inlining local proofs, the argument uses existing
  spectral/CFC identities, four explicit Kraus operators, and exact algebraic normalization of the
  registered qubit matrices. No private theorem, lemma or proposition-valued def is added.
escape_witness: none
admission_basis: open-problem-resolution (#11472; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  Mathlib constants are pinned upstream dependencies, not frozen repository nodes.
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import D5.S3.Quantum.Foundation.FiniteKrausChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

noncomputable section
namespace D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

/-! Conjecture 15 of A. Meunson and T. Deesuwan, arXiv:2606.31205v1 (p. 18),
asserts data processing for Q = -S_0^Q under commutativity-preserving channels.
The regularized qubit states below have strictly larger Q after the channel:
the two positive trace arguments are 50401283/7340144 and 1879639/266240.
The channel is completely positive, trace preserving, and preserves every
commuting pair of qubit density matrices. All logarithms use continuous
functional calculus in the matrix L2 operator norm. -/

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def IsDensity {d : ℕ} (A : Mat d) : Prop := A.PosSemidef ∧ Matrix.trace A = 1

def reg {d : ℕ} (ε : ℝ) (A : Mat d) : Mat d :=
  (1 - ε) • A + (ε / d) • 1

def Q {d : ℕ} (A B : Mat d) : ℝ :=
  -(1 / ((0 : ℝ) - 1) * Real.log (Matrix.trace
    (A * NormedSpace.exp (((0 : ℝ) - 1) • (CFC.log A - CFC.log B)))).re)

def IsCPTP {d : ℕ} (N : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  MatrixMap.IsCompletelyPositive N ∧ ∀ A, Matrix.trace (N A) = Matrix.trace A

def IsCoP {d : ℕ} (N : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  ∀ A B, IsDensity A → IsDensity B → A * B = B * A → N A * N B = N B * N A

def supp {d : ℕ} (A : Mat d) : Submodule ℂ (Fin d → ℂ) :=
  LinearMap.range (Matrix.toLin' A)

def claim : Prop := ∀ (d : ℕ) (ρ σ : Mat d) (ε : ℝ)
    (N : MatrixMap (Fin d) (Fin d) ℂ),
  IsDensity ρ → IsDensity σ → ρ * σ ≠ σ * ρ → 0 < ε → ε < 1 →
  IsCPTP N → IsCoP N → supp (N (reg ε ρ)) ≤ supp (N (reg ε σ)) →
  Q (N (reg ε ρ)) (N (reg ε σ)) ≤ Q (reg ε ρ) (reg ε σ) ∧
    0 ≤ Q (N (reg ε ρ)) (N (reg ε σ))

private def pauli (z x : ℝ) : Mat 2 := !![(z : ℂ), (x : ℂ); (x : ℂ), -(z : ℂ)]

private def t (n : ℕ) : ℝ := (4^n-1)/(4^n+1)

private def state (n : ℕ) (H : Mat 2) : Mat 2 := (1/2 : ℝ) • 1 + (t n/2) • H

private def Z : Mat 2 := pauli 1 0

private def H : Mat 2 := pauli (11/14) (5*Real.sqrt 3/14)

private def J : Mat 2 := pauli (29/36) (Real.sqrt 455/36)

private def R : Mat 2 := state 7 Z

private def S : Mat 2 := state 8 H

private def Rp : Mat 2 := state 6 Z

private def Sp : Mat 2 := state 3 J

private def channel (u v w : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun A := !![
    (A 0 0 + A 1 1 + (w:ℂ)*(A 0 0 - A 1 1) + (v:ℂ)*(A 0 1+A 1 0))/2,
    (u:ℂ)*((1+(w:ℂ))*A 0 1+(1-(w:ℂ))*A 1 0)/2;
    (u:ℂ)*((1-(w:ℂ))*A 0 1+(1+(w:ℂ))*A 1 0)/2,
    (A 0 0 + A 1 1 - (w:ℂ)*(A 0 0 - A 1 1) - (v:ℂ)*(A 0 1+A 1 0))/2]
  map_add' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

private def K : Mat 2 := pauli (-1/7) (4*Real.sqrt 3/7)

private def L : Mat 2 := pauli (-43/48) (Real.sqrt 455/48)

private def u : ℝ := (3211313/127793250)*Real.sqrt 1365

private def v : ℝ := -(727356123473/168188824118250)*Real.sqrt 3

private def w : ℝ := 22365525/22373717

private def N : MatrixMap (Fin 2) (Fin 2) ℂ := channel u v w

private def bp (k : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  if p.1=0 then if p.2=0 then 1 else k else if p.2=0 then -(k:ℂ) else 1

private def bm (k : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  if p.1=0 then if p.2=0 then 1 else k else if p.2=0 then k else -1

private def ep (p : Fin 2 × Fin 2) : ℂ :=
  if p.1=0 then if p.2=0 then 0 else 1 else if p.2=0 then -1 else 0

private def em (p : Fin 2 × Fin 2) : ℂ :=
  if p.1=0 then if p.2=0 then 0 else 1 else if p.2=0 then 1 else 0

private def ε : ℝ := 1/65537

private def ρ : Mat 2 := (1/2:ℝ) • 1 + (t 7/(2*(1-ε))) • Z

private def σ : Mat 2 := (1/2:ℝ) • 1 + (t 8/(2*(1-ε))) • H

set_option maxHeartbeats 2000000 in
/-- Conjecture 15 fails for a commutativity-preserving channel on two-dimensional states. -/
theorem result : ¬ claim := by
  have involution_spectrum {n : Type} [Fintype n] [DecidableEq n]
      (H : Matrix n n ℂ) (hH : IsSelfAdjoint H) (hHH : H * H = 1)
      {x : ℝ} (hx : x ∈ spectrum ℝ H) : x = 1 ∨ x = -1 := by
    have hc : cfc (fun x : ℝ => x * x) H = cfc (fun _ : ℝ => 1) H := by
      rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) H, cfc_id' ℝ H hH, cfc_const 1 H hH, Algebra.algebraMap_eq_smul_one]
      simpa using hHH
    have hsq := eqOn_of_cfc_eq_cfc hc (ha := hH) (by fun_prop) (by fun_prop) hx
    dsimp at hsq
    rcases eq_or_eq_neg_of_sq_eq_sq x 1 (by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr h

  have two_point_cfc {n : Type} [Fintype n] [DecidableEq n]
      (f : ℝ → ℝ) (a b : ℝ) (H : Matrix n n ℂ)
      (hH : IsSelfAdjoint H) (hHH : H * H = 1) :
      cfc f (a • (1 : Matrix n n ℂ) + b • H) =
        ((f (a+b) + f (a-b))/2) • (1 : Matrix n n ℂ) +
        ((f (a+b) - f (a-b))/2) • H := by
    have haff : cfc (fun x : ℝ => a + b*x) H = a • (1 : Matrix n n ℂ) + b • H := by
      rw [cfc_const_add a (fun x : ℝ => b*x) H (by fun_prop) hH, cfc_const_mul_id b H hH, Algebra.algebraMap_eq_smul_one]
    rw [← haff, ← cfc_comp f (fun x : ℝ => a+b*x) H hH ((H.finite_real_spectrum.image _).continuousOn _) (by fun_prop)]
    · calc
        cfc (fun x : ℝ => f (a+b*x)) H =
          cfc (fun x : ℝ => (f (a+b)+f (a-b))/2 + ((f (a+b)-f (a-b))/2)*x) H := by
            apply cfc_congr
            intro x hx
            rcases involution_spectrum H hH hHH hx with rfl | rfl <;> dsimp <;>
              simp only [mul_one, mul_neg_one, ← sub_eq_add_neg] <;> ring
        _ = _ := by
          rw [cfc_const_add _ (fun x : ℝ => ((f (a+b)-f (a-b))/2)*x) H (by fun_prop) hH, cfc_const_mul_id _ H hH, Algebra.algebraMap_eq_smul_one]

  have affine_posDef {n : Type} [Fintype n] [DecidableEq n]
      (a b : ℝ) (H : Matrix n n ℂ) (hH : IsSelfAdjoint H) (hHH : H*H=1)
      (hp : 0 < a+b) (hm : 0 < a-b) :
      (a • (1 : Matrix n n ℂ) + b • H).PosDef := by
    have haff : cfc (fun x : ℝ => a+b*x) H = a • (1 : Matrix n n ℂ) + b • H := by
      rw [cfc_const_add a (fun x : ℝ => b*x) H (by fun_prop) hH,
        cfc_const_mul_id b H hH, Algebra.algebraMap_eq_smul_one]
    rw [← haff]
    apply Matrix.isStrictlyPositive_iff_posDef.mp
    apply (cfc_isStrictlyPositive_iff _ _ (by fun_prop) hH).mpr
    intro x hx
    rcases involution_spectrum H hH hHH hx with rfl | rfl
    · simpa using hp
    · simpa [sub_eq_add_neg] using hm

  have pauli_sa (z x : ℝ) : IsSelfAdjoint (pauli z x) := by
    change Matrix.conjTranspose (pauli z x) = pauli z x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply]

  have pauli_sq (z x : ℝ) (h : z^2+x^2=1) : pauli z x * pauli z x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
    · have hc : (z : ℂ)^2+(x : ℂ)^2=1 := by exact_mod_cast h
      linear_combination hc
    · ring
    · ring
    · have hc : (z : ℂ)^2+(x : ℂ)^2=1 := by exact_mod_cast h
      linear_combination hc

  have Z_sq : Z*Z=1 := pauli_sq 1 0 (by norm_num)

  have H_sq : H*H=1 := by
    apply pauli_sq
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

  have J_sq : J*J=1 := by
    apply pauli_sq
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 455 by norm_num)]

  have log_state (n : ℕ) (K : Mat 2) (hK : IsSelfAdjoint K) (hKK : K*K=1) :
      CFC.log (state n K) =
        ((n:ℝ)*Real.log 2 - Real.log (4^n+1)) • (1 : Mat 2) +
        ((n:ℝ)*Real.log 2) • K := by
    have hd : (4:ℝ)^n+1 ≠ 0 := by positivity
    have ep : (1/2:ℝ)+t n/2 = 4^n/(4^n+1) := by dsimp [t]; field_simp; ring
    have em : (1/2:ℝ)-t n/2 = 1/(4^n+1) := by dsimp [t]; field_simp; ring
    have l4 : Real.log (4:ℝ) = 2*Real.log 2 := by
      convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
    have lp : Real.log ((1/2:ℝ)+t n/2) = 2*(n:ℝ)*Real.log 2 - Real.log (4^n+1) := by
      rw [ep, Real.log_div (by positivity) hd, Real.log_pow, l4]; ring
    have lm : Real.log ((1/2:ℝ)-t n/2) = -Real.log (4^n+1) := by
      rw [em, Real.log_div (by norm_num) hd, Real.log_one, zero_sub]
    change cfc Real.log (state n K) = _
    rw [state, two_point_cfc Real.log (1/2) (t n/2) K hK hKK, lp, lm]
    congr 1 <;> ring

  have channel_tp (u v w : ℝ) (A : Mat 2) :
      Matrix.trace (channel u v w A) = Matrix.trace A := by
    simp [channel, Matrix.trace, Fin.sum_univ_two]
    ring

  have channel_cop (u v w : ℝ) : IsCoP (channel u v w) := by
    intro A B _ _ h
    have h0 := congrArg (fun M : Mat 2 => M 0 0) h
    have h1 := congrArg (fun M : Mat 2 => M 0 1) h
    have h2 := congrArg (fun M : Mat 2 => M 1 0) h
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h0 h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [channel, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (u:ℂ)^2*(w:ℂ)*h0
    · linear_combination -(u:ℂ)*(v:ℂ)*(w:ℂ)*h0 +
        (u:ℂ)*(w:ℂ)*(1+(w:ℂ))/2*h1 - (u:ℂ)*(w:ℂ)*(1-(w:ℂ))/2*h2
    · linear_combination -(u:ℂ)*(v:ℂ)*(w:ℂ)*h0 -
        (u:ℂ)*(w:ℂ)*(1-(w:ℂ))/2*h1 + (u:ℂ)*(w:ℂ)*(1+(w:ℂ))/2*h2
    · linear_combination -(u:ℂ)^2*(w:ℂ)*h0

  have K_sq : K*K=1 := by
    apply pauli_sq
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

  have L_sq : L*L=1 := by
    apply pauli_sq
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 455 by norm_num)]

  have log_difference : CFC.log S - CFC.log R =
      Real.log (32770/65537) • (1 : Mat 2) + (5*Real.log 2) • K := by
    have hv : (8:ℝ) • H - (7:ℝ) • Z = (5:ℝ) • K := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [H,Z,K,pauli] <;> ring
    have hs : (8*Real.log 2 - Real.log 65537) - (7*Real.log 2 - Real.log 16385) =
        Real.log (32770/65537) := by
      have h : Real.log (32770:ℝ) = Real.log 2 + Real.log 16385 := by
        rw [show (32770:ℝ)=2*16385 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      rw [Real.log_div (by norm_num) (by norm_num), h]
      ring
    rw [S,R,log_state 8 H (pauli_sa _ _) H_sq,log_state 7 Z (pauli_sa _ _) Z_sq]
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_succ, pow_zero, mul_one] at *
    calc
      _ = ((8*Real.log 2 - Real.log 65537) - (7*Real.log 2 - Real.log 16385)) •
          (1:Mat 2) + Real.log 2 • ((8:ℝ) • H - (7:ℝ) • Z) := by module
      _ = _ := by rw [hv,hs,smul_smul]; congr 1; ring

  have log_difference_prime : CFC.log Sp - CFC.log Rp =
      Real.log (4097/520) • (1 : Mat 2) + (4*Real.log 2) • L := by
    have hv : (3:ℝ) • J - (6:ℝ) • Z = (4:ℝ) • L := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [J,Z,L,pauli] <;> ring
    have hs : (3*Real.log 2 - Real.log 65) - (6*Real.log 2 - Real.log 4097) =
        Real.log (4097/520) := by
      have h : Real.log (520:ℝ) = 3*Real.log 2 + Real.log 65 := by
        rw [show (520:ℝ)=2^3*65 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        norm_num
      rw [Real.log_div (by norm_num) (by norm_num), h]
      ring
    rw [Sp,Rp,log_state 3 J (pauli_sa _ _) J_sq,log_state 6 Z (pauli_sa _ _) Z_sq]
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_succ, pow_zero, mul_one] at *
    calc
      _ = ((3*Real.log 2 - Real.log 65) - (6*Real.log 2 - Real.log 4097)) •
          (1:Mat 2) + Real.log 2 • ((3:ℝ) • J - (6:ℝ) • Z) := by module
      _ = _ := by rw [hv,hs,smul_smul]; congr 1; ring

  have exp_affine (a b : ℝ) (M : Mat 2) (hM : IsSelfAdjoint M) (hMM : M*M=1) :
      NormedSpace.exp (a • (1 : Mat 2)+b • M) =
        ((Real.exp (a+b)+Real.exp (a-b))/2) • (1:Mat 2) +
        ((Real.exp (a+b)-Real.exp (a-b))/2) • M := by
    have hsa : IsSelfAdjoint (a • (1 : Mat 2)+b • M) :=
      ((isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint a).smul (IsSelfAdjoint.one (Mat 2))).add
        ((isSelfAdjoint_iff.mpr (by simp) : IsSelfAdjoint b).smul hM)
    rw [← CFC.real_exp_eq_normedSpace_exp hsa]
    exact two_point_cfc Real.exp a b M hM hMM

  have exp_input : NormedSpace.exp (CFC.log S-CFC.log R) =
      (32770/65537:ℝ) • ((1025/64:ℝ) • (1:Mat 2) + (1023/64:ℝ) • K) := by
    have ep : Real.exp (Real.log (32770/65537) + 5*Real.log 2) = (32770/65537:ℝ)*32 := by
      rw [Real.exp_add, show (5:ℝ)*Real.log 2 = (5:ℕ)*Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
      norm_num
    have em : Real.exp (Real.log (32770/65537) - 5*Real.log 2) = (32770/65537:ℝ)/32 := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
        show (5:ℝ)*Real.log 2 = (5:ℕ)*Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
      norm_num
    rw [log_difference, exp_affine _ _ K (pauli_sa _ _) K_sq, ep,em]
    simp only [smul_add,smul_smul]
    congr 1 <;> norm_num

  have exp_output : NormedSpace.exp (CFC.log Sp-CFC.log Rp) =
      (4097/520:ℝ) • ((257/32:ℝ) • (1:Mat 2) + (255/32:ℝ) • L) := by
    have ep : Real.exp (Real.log (4097/520) + 4*Real.log 2) = (4097/520:ℝ)*16 := by
      rw [Real.exp_add, show (4:ℝ)*Real.log 2 = (4:ℕ)*Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
      norm_num
    have em : Real.exp (Real.log (4097/520) - 4*Real.log 2) = (4097/520:ℝ)/16 := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
        show (4:ℝ)*Real.log 2 = (4:ℕ)*Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
      norm_num
    rw [log_difference_prime, exp_affine _ _ L (pauli_sa _ _) L_sq, ep,em]
    simp only [smul_add,smul_smul]
    congr 1 <;> norm_num

  have trace_input : (Matrix.trace (R * NormedSpace.exp (CFC.log S-CFC.log R))).re =
      (50401283/7340144:ℝ) := by
    rw [exp_input]
    norm_num [R,state,Z,K,pauli,t,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]

  have trace_output : (Matrix.trace (Rp * NormedSpace.exp (CFC.log Sp-CFC.log Rp))).re =
      (1879639/266240:ℝ) := by
    rw [exp_output]
    norm_num [Rp,state,Z,L,pauli,t,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]

  have Q_eq (A B : Mat 2) : Q A B =
      Real.log (Matrix.trace (A * NormedSpace.exp (CFC.log B - CFC.log A))).re := by
    have he : ((0 : ℝ) - 1) • (CFC.log A - CFC.log B) = CFC.log B - CFC.log A := by
      module
    unfold Q
    rw [he]
    norm_num

  have Q_increases : Q R S < Q Rp Sp := by
    rw [Q_eq, Q_eq]
    rw [trace_input,trace_output]
    apply Real.log_lt_log (by norm_num)
    norm_num

  have u_sq : u^2 = (72187718287783/83749306387500:ℝ) := by
    unfold u
    rw [mul_pow,Real.sq_sqrt (by norm_num)]
    norm_num

  have parameters : 0 < u ∧ u < 1 ∧ 0 < w ∧ w < 1 ∧
      0 < (1-u^2)*(1-w^2)-v^2 := by
    have hu0 : 0 < u := by unfold u; positivity
    have hu1 : u < 1 := by nlinarith [u_sq]
    have hw0 : 0 < w := by norm_num [w]
    have hw1 : w < 1 := by norm_num [w]
    refine ⟨hu0,hu1,hw0,hw1,?_⟩
    rw [u_sq]
    norm_num [w,v,mul_pow,Real.sq_sqrt]

  have channel_cp (u v w : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
      (hw0 : 0 < w) (hd : 0 < (1-u^2)*(1-w^2)-v^2) :
      MatrixMap.IsCompletelyPositive (channel u v w) := by
    let a : ℝ := (1+u)*(1+w)
    let b : ℝ := (1-u)*(1+w)
    let δ : ℝ := (1-u^2)*(1-w^2)-v^2
    have ha : 0 < a := mul_pos (by linarith) (by linarith)
    have hb : 0 < b := mul_pos (by linarith) (by linarith)
    have hδ : 0 < δ := hd
    let reshape (x : Fin 2 × Fin 2 → ℂ) : Mat 2 := fun i j => x (i,j)
    let coeff : Fin 4 → ℝ := ![a/4, (δ/a)/4, b/4, (δ/b)/4]
    let vectors : Fin 4 → (Fin 2 × Fin 2 → ℂ) := ![bp (v/a), ep, bm (v/b), em]
    let kraus (k : Fin 4) : Mat 2 := Real.sqrt (coeff k) • reshape (vectors k)
    have hcoeff (k : Fin 4) : 0 ≤ coeff k := by
      fin_cases k <;> simp [coeff] <;> positivity
    have term (k : Fin 4) (A : Mat 2) :
        kraus k * A * (kraus k).conjTranspose =
          coeff k • (reshape (vectors k) * A * (reshape (vectors k)).conjTranspose) := by
      simp only [kraus, Matrix.conjTranspose_smul, star_trivial,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (hcoeff k)]
    have heq : MatrixMap.of_kraus kraus kraus = channel u v w := by
      ext A i j
      change (∑ k : Fin 4, kraus k * A * (kraus k).conjTranspose) i j = _
      simp_rw [term]
      have hucp : 1+(u:ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (show 0 < 1+u by linarith)
      have hucm : 1-(u:ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (show 0 < 1-u by linarith)
      have hwcp : 1+(w:ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (show 0 < 1+w by linarith)
      simp only [Fin.sum_univ_four, Matrix.add_apply, Matrix.smul_apply,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
      fin_cases i <;> fin_cases j <;>
        simp [coeff, vectors, reshape, channel, bp, bm, ep, em, a, b, δ] <;>
        field_simp [hucp,hucm,hwcp] <;> ring
    rw [← heq]
    exact MatrixMap.of_kraus_isCompletelyPositive kraus

  have N_cptp : IsCPTP N :=
    ⟨channel_cp u v w parameters.1 parameters.2.1 parameters.2.2.1
      parameters.2.2.2.2, channel_tp u v w⟩

  have sqrt_relation : Real.sqrt 1365*Real.sqrt 3 = 3*Real.sqrt 455 := by
    rw [show (1365:ℝ)=3*455 by norm_num, Real.sqrt_mul (by norm_num)]
    calc
      _ = (Real.sqrt 3)^2 * Real.sqrt 455 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num)]

  have N_R : N R = Rp := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [N,channel,R,Rp,state,t,Z,pauli,w]

  have N_S : N S = Sp := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [N,channel,S,Sp,state,t,H,J,pauli,u,v,w] <;>
      ring_nf <;> nlinarith [sqrt_relation,Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

  have reg_ρ : reg ε ρ = R := by
    unfold reg ρ R state
    simp only [smul_add,smul_smul]
    norm_num [ε,t]
    module

  have reg_σ : reg ε σ = S := by
    unfold reg σ S state
    simp only [smul_add,smul_smul]
    norm_num [ε,t]
    module

  have ρ_density : IsDensity ρ := by
    constructor
    · exact (affine_posDef _ _ Z (pauli_sa _ _) Z_sq (by norm_num [t,ε])
        (by norm_num [t,ε])).posSemidef
    · norm_num [ρ,Matrix.trace,Fin.sum_univ_two,Z,pauli]
      ring

  have σ_density : IsDensity σ := by
    constructor
    · exact (affine_posDef _ _ H (pauli_sa _ _) H_sq (by norm_num [t,ε])
        (by norm_num [t,ε])).posSemidef
    · norm_num [σ,Matrix.trace,Fin.sum_univ_two,H,pauli]
      ring

  have noncommuting : ρ*σ ≠ σ*ρ := by
    intro h
    have hh := congrArg (fun M : Mat 2 => (M 0 1).re) h
    norm_num [ρ,σ,Z,H,pauli,t,ε,Matrix.mul_apply,Fin.sum_univ_two] at hh
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ)<3 by norm_num)]

  have supp_posDef {d : ℕ} (M : Mat d) (hM : M.PosDef) : supp M = ⊤ := by
    unfold supp
    rw [← Matrix.toLin_eq_toLin']
    exact Matrix.range_toLin_eq_top (Pi.basisFun ℂ (Fin d)) M
      ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit)

  have Rp_posDef : Rp.PosDef :=
    affine_posDef _ _ Z (pauli_sa _ _) Z_sq (by norm_num [t]) (by norm_num [t])

  have Sp_posDef : Sp.PosDef :=
    affine_posDef _ _ J (pauli_sa _ _) J_sq (by norm_num [t]) (by norm_num [t])

  intro h
  have hsupp : supp (N (reg ε ρ)) ≤ supp (N (reg ε σ)) := by
    rw [reg_ρ,reg_σ,N_R,N_S,supp_posDef Rp Rp_posDef,supp_posDef Sp Sp_posDef]
  have hi := h 2 ρ σ ε N ρ_density σ_density noncommuting (by norm_num [ε])
    (by norm_num [ε]) N_cptp (channel_cop u v w) hsupp
  rw [reg_ρ,reg_σ,N_R,N_S] at hi
  exact (not_le.mpr Q_increases) hi.1

end D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
