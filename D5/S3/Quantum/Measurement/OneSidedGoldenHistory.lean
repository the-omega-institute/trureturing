/- GID: D5/S3/Quantum/Measurement/OneSidedGoldenHistory
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OneSidedGoldenHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The retained golden Kraus branches give the complete finite-history next-zero law. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Measurement.OneSidedGoldenHistory

open Matrix
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

/-- Inverse golden ratio, with the source's square-root normalization. -/
def x : ℝ := Real.goldenRatio⁻¹

/-- The source record phase. -/
def zeta : ℂ := Complex.exp ((3*Real.pi/5 : ℝ) * Complex.I)

/-- The source's relative phase on the P branch. -/
def phase : ℂ := (Complex.exp ((3*Real.pi/5 : ℝ) * Complex.I)) ^ (-3 : ℤ)

private theorem x_properties : 0 < x ∧ x < 1 ∧ x+x^2=1 := by
  refine ⟨inv_pos.mpr Real.goldenRatio_pos, inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio, ?_⟩
  rw [x, Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

variable {d : ℕ}

private def block (P : Matrix (Fin d) (Fin d) ℂ) (a b : ℂ) := a • (1-P) + b • P

private theorem block_mul (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P) (a b c e : ℂ) :
    block P a b * block P c e = block P (a*c) (b*e) := by
  have hEE : (1-P)*(1-P) = 1-P := by noncomm_ring [hP]
  have hEP : (1-P)*P = 0 := by simp [sub_mul,hP]
  have hPE : P*(1-P) = 0 := by simp [mul_sub,hP]
  simp [block,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,hEE,hEP,hPE,hP,smul_smul,mul_comm]

private theorem block_star (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) (a b : ℂ) :
    (block P a b).conjTranspose = block P (star a) (star b) := by
  simp [block,Matrix.conjTranspose_smul,hP.eq]

/-- Both complete retained CP branches, with false denoting outcome zero. -/
def kraus (P : Matrix (Fin d) (Fin d) ℂ) : Bool → Matrix (Fin d) (Fin d) ℂ
  | false => (Real.sqrt x : ℂ) • (1-P)
  | true => (x : ℂ) • (1-P) + phase • P

def branch (P : Matrix (Fin d) (Fin d) ℂ) (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :=
  kraus P b * ρ * (kraus P b).conjTranspose

/-- Every result is retained and applied in source order. -/
def branchState (P : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) :=
  runWord (branch P) h ρ

def mass (P : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) : ℝ :=
  (Matrix.trace (branchState P ρ h)).re

def nextZero (P : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) : ℝ :=
  mass P ρ (h ++ [false]) / mass P ρ h

/-- Actual posterior projection weight, normalized by the retained branch trace. -/
def posterior (P : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) : ℝ :=
  (Matrix.trace (P*branchState P ρ h)).re / mass P ρ h

def ageProbability (q : ℝ) (n : ℕ) : ℝ :=
  x*(1-q)*x^(2*n)/(q+(1-q)*x^(2*n))

private def exponent : List Bool → ℕ
  | [] => 0
  | false :: h => 1+exponent h
  | true :: h => 2+exponent h

private def alive (h : List Bool) : ℂ := if false ∈ h then 0 else 1

private theorem phase_unit : star phase * phase = 1 := by
  have he : ‖Complex.exp ((3*Real.pi/5 : ℝ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have hp : ‖phase‖ = 1 := by
    unfold phase
    rw [norm_zpow, he]
    norm_num
  have hn : (Complex.normSq phase : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hp]
    norm_num
  simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using hn

private theorem complete_kraus (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P*P=P) (hPh : P.IsHermitian) :
    (kraus P false).conjTranspose * kraus P false +
      (kraus P true).conjTranspose * kraus P true = 1 := by
  have hs : star (Real.sqrt x : ℂ)*(Real.sqrt x : ℂ) = x := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show Real.sqrt x * Real.sqrt x = x by
      nlinarith [Real.sq_sqrt x_properties.1.le])
  have h0 : kraus P false = block P (Real.sqrt x) 0 := by simp [kraus,block]
  have h1 : kraus P true = block P x phase := rfl
  have he : (kraus P false).conjTranspose * kraus P false = (x : ℂ) • (1-P) := by
    rw [h0,block_star P hPh,block_mul P hP]
    simp only [block,hs,star_zero,zero_mul,zero_smul,add_zero]
  have hq : (kraus P true).conjTranspose * kraus P true = (x : ℂ)^2 • (1-P)+P := by
    rw [h1,block_star P hPh,block_mul P hP]
    simp only [block,phase_unit,one_smul]
    rw [show star (x : ℂ)*(x : ℂ) = (x : ℂ)^2 by simp [pow_two]]
  have hx : (x : ℂ)+(x : ℂ)^2 = 1 := by exact_mod_cast x_properties.2.2
  rw [he,hq,← add_assoc,← add_smul,hx,one_smul]
  simp

/-- The two coefficient operators of the source preparation V. -/
def preparation (P : Matrix (Fin d) (Fin d) ℂ) : Bool → Matrix (Fin d) (Fin d) ℂ
  | false => (Real.sqrt x : ℂ) • 1
  | true => (x : ℂ) • ((1-P)+zeta • P)

/-- The record-basis coefficients of the source reader B_R. -/
def reader : Bool → Bool → ℂ
  | false, false => -(x : ℂ)
  | false, true => (Real.sqrt x : ℂ)*zeta⁻¹
  | true, false => (Real.sqrt x : ℂ)*zeta⁻¹
  | true, true => -(x : ℂ)*zeta^3

/-- Coefficients of (I tensor B_R)V, retaining both record coordinates. -/
def nativePort (P : Matrix (Fin d) (Fin d) ℂ) (b : Bool) :=
  reader b false • preparation P false + reader b true • preparation P true

private theorem zeta_relations :
    zeta+zeta⁻¹ = -(x : ℂ) ∧ zeta^5 = -1 := by
  have hn : ‖zeta‖ = 1 := by simp [zeta,Complex.norm_exp]
  have hi : zeta⁻¹ = star zeta := by
    simp [Complex.inv_def,Complex.normSq_eq_norm_sq,hn,Complex.star_def]
  have hcos : 2*Real.cos (3*Real.pi/5) = -x := by
    rw [show 3*Real.pi/5 = Real.pi-2*(Real.pi/5) by ring,
      Real.cos_pi_sub,Real.cos_two_mul,Real.cos_pi_div_five,x,Real.inv_goldenRatio]
    dsimp [Real.goldenConj]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  constructor
  · rw [hi]
    apply Complex.ext
    · simpa only [Complex.add_re,Complex.star_def,Complex.conj_re,zeta,
        Complex.exp_ofReal_mul_I_re,Complex.neg_re,Complex.ofReal_re,two_mul] using hcos
    · simp [Complex.star_def]
  · have hf : zeta^5 = Complex.exp (3*((Real.pi : ℂ)*Complex.I)) := by
      rw [zeta,← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have he := Complex.exp_nat_mul ((Real.pi : ℂ)*Complex.I) 3
    norm_num [Complex.exp_pi_mul_I] at he
    exact hf.trans he

private theorem native_port_identity (P : Matrix (Fin d) (Fin d) ℂ) (b : Bool) :
    nativePort P b = zeta^2 • kraus P b := by
  have hz0 : zeta ≠ 0 := Complex.exp_ne_zero _
  have hx : (x : ℂ)+(x : ℂ)^2 = 1 := by exact_mod_cast x_properties.2.2
  have hinv : zeta⁻¹ = -(x : ℂ)-zeta := by linear_combination zeta_relations.1
  have hp : zeta^2+(x : ℂ)*zeta+1 = 0 := by
    have h := congrArg (fun a : ℂ => a*zeta) zeta_relations.1
    simp only [add_mul,inv_mul_cancel₀ hz0] at h
    linear_combination h
  have hz4 : zeta^4 = -zeta⁻¹ := by
    calc
      zeta^4 = zeta^5/zeta := by field_simp [hz0] <;> ring
      _ = -zeta⁻¹ := by rw [zeta_relations.2]; ring
  have hphase : zeta^2*phase = zeta⁻¹ := by
    change zeta^2*zeta^(-3 : ℤ) = zeta⁻¹
    rw [_root_.zpow_neg]
    field_simp [hz0] <;> ring
  have hzero : (x : ℂ)*(zeta⁻¹-1) = zeta^2 := by
    rw [hinv]
    linear_combination -hp-hx
  have hone : (x : ℂ)*zeta⁻¹-(x : ℂ)^2*zeta^3 = (x : ℂ)*zeta^2 := by
    rw [hinv]
    linear_combination -(x : ℂ)^2*(zeta+1)*hp+(x : ℂ)*(zeta^2+zeta)*hx
  have hproj : (x : ℂ)*zeta⁻¹-(x : ℂ)^2*zeta^4 = zeta^2*phase := by
    rw [hz4,hphase]
    linear_combination zeta⁻¹*hx
  have hs : (Real.sqrt x : ℂ)^2 = x := by exact_mod_cast Real.sq_sqrt x_properties.1.le
  cases b
  · calc
      nativePort P false = ((Real.sqrt x : ℂ)*(x : ℂ)*(zeta⁻¹-1)) • (1-P) := by
        ext i j
        simp only [nativePort,reader,preparation,Matrix.add_apply,
          Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
        field_simp [hz0] <;> ring
      _ = zeta^2 • kraus P false := by
        rw [mul_assoc,hzero]
        simp only [kraus,smul_smul,mul_comm]
  · calc
      nativePort P true =
          ((Real.sqrt x : ℂ)^2*zeta⁻¹-(x : ℂ)^2*zeta^3) • (1-P)+
          ((Real.sqrt x : ℂ)^2*zeta⁻¹-(x : ℂ)^2*zeta^4) • P := by
        dsimp [nativePort,reader,preparation]
        module
      _ = zeta^2 • kraus P true := by
        rw [hs,hone,hproj]
        simp only [kraus,smul_add,smul_smul,mul_comm]

private theorem native_port_branch (P : Matrix (Fin d) (Fin d) ℂ)
    (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    nativePort P b * ρ * (nativePort P b).conjTranspose = branch P b ρ := by
  have hn : ‖zeta‖ = 1 := by simp [zeta,Complex.norm_exp]
  have hu : star (zeta^2)*zeta^2 = 1 := by
    have hh : (Complex.normSq (zeta^2) : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq,norm_pow,hn]
      norm_num
    simpa only [Complex.normSq_eq_conj_mul_self,Complex.star_def] using hh
  rw [native_port_identity]
  calc
    _ = (star (zeta^2)*zeta^2) • (kraus P b*ρ*(kraus P b).conjTranspose) := by
      simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul] <;> module
    _ = branch P b ρ := by rw [hu,one_smul]; rfl

private theorem sector_trace (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P)
    (hPh : P.IsHermitian) (a b : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace ((1-P)*(block P a b * ρ * (block P a b).conjTranspose)) =
      (star a*a)*Matrix.trace ((1-P)*ρ) ∧
    Matrix.trace (P*(block P a b * ρ * (block P a b).conjTranspose)) =
      (star b*b)*Matrix.trace (P*ρ) := by
  have hE : (1-P : Matrix (Fin d) (Fin d) ℂ) = block P 1 0 := by simp [block]
  have hQ : P = block P 0 1 := by simp [block]
  have htrace (Q : Matrix (Fin d) (Fin d) ℂ) :
      Matrix.trace (Q*(block P a b*ρ*(block P a b).conjTranspose)) =
        Matrix.trace (((block P a b).conjTranspose*Q*block P a b)*ρ) := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  have ht (c e : ℂ) :
      (block P a b).conjTranspose * block P c e * block P a b =
        block P (star a*c*a) (star b*e*b) := by
    rw [block_star P hPh, block_mul P hP, block_mul P hP]
  constructor
  · have hi : (block P a b).conjTranspose*(1-P)*block P a b = (star a*a) • (1-P) := by
      calc
        _ = (block P a b).conjTranspose * block P 1 0 * block P a b := by rw [← hE]
        _ = _ := by rw [ht]; simp [block]
    rw [htrace, hi]
    simp [Matrix.smul_mul, Matrix.trace_smul]
  · have hi : (block P a b).conjTranspose*P*block P a b = (star b*b) • P := by
      calc
        _ = (block P a b).conjTranspose * block P 0 1 * block P a b := by rw [← hQ]
        _ = _ := by rw [ht]; simp [block]
    rw [htrace, hi]
    simp [Matrix.smul_mul, Matrix.trace_smul]

private theorem word_trace (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P)
    (hPh : P.IsHermitian) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) :
    Matrix.trace (branchState P ρ h) =
      (x : ℂ)^exponent h * Matrix.trace ((1-P)*ρ) + alive h*Matrix.trace (P*ρ) := by
  induction h generalizing ρ with
  | nil => simp [branchState,runWord,exponent,alive,sub_mul,Matrix.trace_sub]
  | cons bit h ih =>
    change Matrix.trace (branchState P (branch P bit ρ) h) = _
    rw [ih]
    cases bit
    · have hh := sector_trace P hP hPh (Real.sqrt x) 0 ρ
      have hs : (star (Real.sqrt x : ℂ))*(Real.sqrt x : ℂ) = x := by
        simp only [Complex.star_def, Complex.conj_ofReal]
        exact_mod_cast (show Real.sqrt x * Real.sqrt x = x by nlinarith [Real.sq_sqrt x_properties.1.le])
      have hE : Matrix.trace ((1-P)*branch P false ρ) =
          (x : ℂ)*Matrix.trace ((1-P)*ρ) := by
        rw [hs] at hh
        simpa only [branch,kraus,block,zero_smul,add_zero] using hh.1
      have hQ : Matrix.trace (P*branch P false ρ) = 0 := by
        simpa only [branch,kraus,block,zero_smul,add_zero,star_zero,zero_mul] using hh.2
      rw [hE,hQ]
      simp [exponent,alive,pow_add]
      ring
    · have hh := sector_trace P hP hPh x phase ρ
      rw [show star (x : ℂ)*(x : ℂ) = (x : ℂ)^2 by simp [pow_two],phase_unit] at hh
      rw [show Matrix.trace ((1-P)*branch P true ρ) =
          (x : ℂ)^2*Matrix.trace ((1-P)*ρ) from hh.1,
        show Matrix.trace (P*branch P true ρ) = Matrix.trace (P*ρ) by simpa only [branch,kraus,block,one_mul] using hh.2]
      simp [exponent,alive,pow_add]
      ring

private theorem word_projection_trace (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P)
    (hPh : P.IsHermitian) (ρ : Matrix (Fin d) (Fin d) ℂ) (h : List Bool) :
    Matrix.trace (P*branchState P ρ h) = alive h*Matrix.trace (P*ρ) := by
  induction h generalizing ρ with
  | nil => simp [branchState,runWord,alive]
  | cons bit h ih =>
    change Matrix.trace (P*branchState P (branch P bit ρ) h) = _
    rw [ih]
    cases bit
    · have hh := (sector_trace P hP hPh (Real.sqrt x) 0 ρ).2
      have hQ : Matrix.trace (P*branch P false ρ) = 0 := by
        simpa only [branch,kraus,block,zero_smul,add_zero,star_zero,zero_mul] using hh
      simp [hQ,alive]
    · have hh := (sector_trace P hP hPh x phase ρ).2
      have hQ : Matrix.trace (P*branch P true ρ) = Matrix.trace (P*ρ) := by
        rw [phase_unit,one_mul] at hh
        simpa only [branch,kraus,block] using hh
      simp [hQ,alive]

private theorem exponent_append (a b : List Bool) : exponent (a++b) = exponent a+exponent b := by
  induction a with
  | nil => simp [exponent]
  | cons t a ih => cases t <;> simp [exponent,ih,Nat.add_assoc]

private theorem exponent_no_zero (h : List Bool) (hz : false ∉ h) : exponent h = 2*h.length := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    have hh : false ∉ h := fun ht => hz (by simp [ht])
    cases b
    · exact (hz (by simp)).elim
    · simp [exponent,ih hh]
      omega

private theorem real_mass (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P)
    (hPh : P.IsHermitian) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : Matrix.trace ρ = 1) (h : List Bool) :
    mass P ρ h = x^exponent h * (1-(Matrix.trace (P*ρ)).re) +
      if false ∈ h then 0 else (Matrix.trace (P*ρ)).re := by
  unfold mass
  rw [word_trace P hP hPh,sub_mul,one_mul,Matrix.trace_sub,hρ]
  by_cases hz : false ∈ h <;> simp [alive,hz,← Complex.ofReal_pow,Complex.mul_re]

/-- All finite histories have positive mass. Conditional trace probabilities
are x after any zero and the exact decaying formula after an all-one history.
The state can have arbitrary coherence between the projection sectors. -/
private theorem native_history_law (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P*P=P) (hPh : P.IsHermitian) (ρ : DensityState (Fin d))
    (hq : 0 < (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re ∧
      (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re < 1) :
    let state := CStarMatrix.ofMatrix.symm ρ.val
    let q := (Matrix.trace (P*state)).re
    (∀ h, 0 < mass P state h) ∧
    (∀ n, mass P state (List.replicate n true) = q+(1-q)*x^(2*n)) ∧
    (∀ h, nextZero P state h = if false ∈ h then x else ageProbability q h.length) := by
  dsimp only
  let state := CStarMatrix.ofMatrix.symm ρ.val
  let q := (Matrix.trace (P*state)).re
  have hn : Matrix.trace state = 1 := ρ.property.2
  have hm (h : List Bool) : mass P state h = x^exponent h * (1-q) +
      if false ∈ h then 0 else q := real_mass P hP hPh state hn h
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have hpos (h : List Bool) : 0 < mass P state h := by
    rw [hm]
    have hp : 0 < x^exponent h * (1-q) := mul_pos (pow_pos x_properties.1 _) (by linarith)
    by_cases hz : false ∈ h <;> simp only [hz,↓reduceIte] <;> dsimp [q] at * <;> linarith
  refine ⟨hpos,?_,?_⟩
  · intro n
    have hz : false ∉ List.replicate n true := by simp
    rw [hm,if_neg hz,exponent_no_zero _ hz]
    simp only [List.length_replicate]
    ring
  · intro h
    unfold nextZero
    rw [hm (h++[false]),exponent_append]
    simp only [List.mem_append,List.mem_singleton,or_true,↓reduceIte,exponent,add_zero]
    by_cases hz : false ∈ h
    · rw [if_pos hz,hm h,if_pos hz,add_zero,pow_add,pow_one]
      apply (div_eq_iff (ne_of_gt (mul_pos (pow_pos x_properties.1 _) (by linarith : 0 < 1-q)))).mpr
      ring
    · rw [if_neg hz,hm h,if_neg hz,exponent_no_zero _ hz,pow_add,pow_one]
      unfold ageProbability
      congr 1 <;> ring

open Filter Topology
open D5.S3.ObserverMemory.Prediction.OneSidedPredictorMinimum

/-- Error is tested on actual conditional trace probabilities of every positive history. -/
def NativeCorrect {S : Type*} (M : Predictor S) (P : Matrix (Fin d) (Fin d) ℂ)
    (ρ : DensityState (Fin d)) (ε : ℝ) : Prop :=
  ∀ h, 0 < mass P (CStarMatrix.ofMatrix.symm ρ.val) h →
    |M.output (M.run h) - nextZero P (CStarMatrix.ofMatrix.symm ρ.val) h| ≤ ε

private theorem age_properties (q : ℝ) (hq : 0 < q ∧ q < 1) :
    (∀ n, 0 < ageProbability q n ∧ ageProbability q n ≤ x) ∧
    Antitone (ageProbability q) ∧ Tendsto (ageProbability q) atTop (𝓝 0) := by
  have hx := x_properties
  have hd (n : ℕ) : 0 < q+(1-q)*x^(2*n) :=
    add_pos hq.1 (mul_pos (by linarith) (pow_pos hx.1 _))
  refine ⟨?_,?_,?_⟩
  · intro n
    constructor
    · exact div_pos (mul_pos (mul_pos hx.1 (by linarith)) (pow_pos hx.1 _)) (hd n)
    · unfold ageProbability
      apply (div_le_iff₀ (hd n)).mpr
      nlinarith [mul_pos hx.1 hq.1]
  · intro m n hmn
    have ht : x^(2*n) ≤ x^(2*m) := by
      exact pow_le_pow_of_le_one hx.1.le hx.2.1.le (Nat.mul_le_mul_left 2 hmn)
    unfold ageProbability
    apply (div_le_div_iff₀ (hd n) (hd m)).mpr
    nlinarith [mul_nonneg (mul_nonneg hx.1.le (by linarith : 0 ≤ 1-q))
      (sub_nonneg.mpr ht),hq.1]
  · have hh : x^2 < 1 := by nlinarith [hx.2]
    have ht : Tendsto (fun n : ℕ => x^(2*n)) atTop (𝓝 0) := by
      simpa [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg x) hh
    have hn : Tendsto (fun n : ℕ => x*(1-q)*x^(2*n)) atTop (𝓝 0) := by
      simpa using ht.const_mul (x*(1-q))
    have hd : Tendsto (fun n : ℕ => q+(1-q)*x^(2*n)) atTop (𝓝 q) := by
      simpa using (ht.const_mul (1-q)).const_add q
    have hquot : Tendsto
        (fun n : ℕ => x*(1-q)*x^(2*n)/(q+(1-q)*x^(2*n))) atTop (𝓝 (0/q)) :=
      hn.div hd (ne_of_gt hq.1)
    change Tendsto (fun n : ℕ => x*(1-q)*x^(2*n)/(q+(1-q)*x^(2*n))) atTop (𝓝 0)
    simpa only [zero_div] using hquot

/-- Natural ceiling includes truncation at zero. -/
def cutoff (q ε : ℝ) : ℕ :=
  ⌈Real.log ((1-q)*(x-2*ε)/(2*ε*q))/(2*Real.log Real.goldenRatio)⌉₊

private theorem cutoff_iff (q ε : ℝ) (hq : 0 < q ∧ q < 1)
    (hε : 0 < ε) (hsmall : ε < x/2) (n : ℕ) :
    ageProbability q n ≤ 2*ε ↔ cutoff q ε ≤ n := by
  let A := (1-q)*(x-2*ε)/(2*ε*q)
  have hx := x_properties
  have hd : 0 < q+(1-q)*x^(2*n) :=
    add_pos hq.1 (mul_pos (by linarith) (pow_pos hx.1 _))
  have hden : 0 < 2*ε*q := mul_pos (mul_pos (by norm_num) hε) hq.1
  have hA : 0 < A := div_pos (mul_pos (by linarith) (by linarith)) hden
  have ht : 0 < x^(2*n) := pow_pos hx.1 _
  have hphi : 0 < Real.goldenRatio^(2*n) := pow_pos Real.goldenRatio_pos _
  have hinv : Real.goldenRatio^(2*n)*x^(2*n) = 1 := by
    rw [← mul_pow]
    change (Real.goldenRatio*Real.goldenRatio⁻¹)^(2*n) = 1
    rw [mul_inv_cancel₀ Real.goldenRatio_ne_zero,one_pow]
  have ha : ageProbability q n ≤ 2*ε ↔ A*x^(2*n) ≤ 1 := by
    dsimp [ageProbability,A]
    rw [div_le_iff₀ hd,div_mul_eq_mul_div,div_le_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  have hb : A*x^(2*n) ≤ 1 ↔ A ≤ Real.goldenRatio^(2*n) := by
    calc
      A*x^(2*n) ≤ 1 ↔ A*x^(2*n) ≤ Real.goldenRatio^(2*n)*x^(2*n) := by rw [hinv]
      _ ↔ A ≤ Real.goldenRatio^(2*n) := by
        simpa only [mul_comm] using (mul_le_mul_iff_right₀ ht :
          x^(2*n)*A ≤ x^(2*n)*Real.goldenRatio^(2*n) ↔ A ≤ Real.goldenRatio^(2*n))
  have hc : A ≤ Real.goldenRatio^(2*n) ↔
      Real.log A/(2*Real.log Real.goldenRatio) ≤ (n : ℝ) := by
    rw [← Real.log_le_log_iff hA hphi,Real.log_pow,
      div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos Real.one_lt_goldenRatio))]
    push_cast
    constructor <;> intro h <;> nlinarith
  rw [ha,hb,hc]
  exact Nat.ceil_le.symm

private theorem native_correct_iff {S : Type*} (M : Predictor S) (ε : ℝ)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P) (hPh : P.IsHermitian)
    (ρ : DensityState (Fin d))
    (hq : 0 < (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re ∧
      (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re < 1) :
    NativeCorrect M P ρ ε ↔ Correct M x
      (ageProbability (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re) ε := by
  have hlaw := native_history_law P hP hPh ρ hq
  constructor
  · intro h hst
    have hh := h hst (hlaw.1 hst)
    simpa only [historyLaw,hlaw.2.2 hst] using hh
  · intro h hst _
    simpa only [historyLaw,hlaw.2.2 hst] using h hst

universe u

/-- The actual retained golden process has the attained N+2 state minimum at
the first nonstrict threshold, a one-state high-error predictor, and no exact
finite predictor. The nonstrict logarithmic cutoff includes zero and integer ties. -/
theorem native_predictor_minimum (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P*P=P) (hPh : P.IsHermitian) (ρ : DensityState (Fin d))
    (hq : 0 < (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re ∧
      (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re < 1) :
    let state := CStarMatrix.ofMatrix.symm ρ.val
    let q := (Matrix.trace (P*state)).re
    (∀ h, 0 < mass P state h ∧
      nextZero P state h = if false ∈ h then x else ageProbability q h.length) ∧
    (∀ n, mass P state (List.replicate n true) = q+(1-q)*x^(2*n) ∧
      posterior P state (List.replicate n true) = q/(q+(1-q)*x^(2*n))) ∧
    (∀ ε : ℝ, 0 < ε → ε < x/2 → ∃ N : ℕ, N = cutoff q ε ∧
      (∀ n, ageProbability q n ≤ 2*ε ↔ N ≤ n) ∧
      (∃ M : Predictor (Fin (N+1) ⊕ Unit), NativeCorrect M P ρ ε) ∧
      Fintype.card (Fin (N+1) ⊕ Unit) = N+2 ∧
      ∀ (S : Type u) [Fintype S] (M : Predictor S), NativeCorrect M P ρ ε → N+2 ≤ Fintype.card S) ∧
    (∀ ε : ℝ, x/2 ≤ ε → ∃ M : Predictor Unit, NativeCorrect M P ρ ε) ∧
    (∀ (S : Type u) [Fintype S] (M : Predictor S), ¬ NativeCorrect M P ρ 0) ∧
    ((kraus P false).conjTranspose * kraus P false +
      (kraus P true).conjTranspose * kraus P true = 1) ∧
    (∀ b, nativePort P b = zeta^2 • kraus P b) ∧
    (∀ b σ, nativePort P b * σ * (nativePort P b).conjTranspose = branch P b σ) ∧
    (∀ h, false ∈ h → posterior P state h = 0) := by
  dsimp only
  let state := CStarMatrix.ofMatrix.symm ρ.val
  let q := (Matrix.trace (P*state)).re
  have hlaw := native_history_law P hP hPh ρ hq
  have hp := age_properties q hq
  refine ⟨fun h => ⟨hlaw.1 h,hlaw.2.2 h⟩,?_,?_,?_,?_,complete_kraus P hP hPh,native_port_identity P,native_port_branch P,?_⟩
  · intro n
    refine ⟨hlaw.2.1 n,?_⟩
    unfold posterior
    rw [word_projection_trace P hP hPh,hlaw.2.1 n]
    simp [alive,q,state]
  · intro ε hε hsmall
    let N := cutoff q ε
    have hcut (n : ℕ) : ageProbability q n ≤ 2*ε ↔ N ≤ n :=
      cutoff_iff q ε hq hε hsmall n
    have hmin := sharp_predictor_minimum x ε (ageProbability q) N
      ⟨x_properties.1,x_properties.2.1.le⟩ hε.le (by linarith)
      (fun n => (hp.1 n).1.le) (fun n => (hp.1 n).2) hp.2.1 hp.2.2 hcut
    obtain ⟨M,hM⟩ := hmin.1
    exact ⟨N,rfl,hcut,⟨M,(native_correct_iff M ε P hP hPh ρ hq).mpr hM⟩,hmin.2.1,
      fun S _ M hM => hmin.2.2 S M ((native_correct_iff M ε P hP hPh ρ hq).mp hM)⟩
  · intro ε hε
    let M : Predictor Unit := {
      initial := ()
      update := fun _ _ => ()
      output := fun _ => x/2
      output_mem := fun _ => ⟨by linarith [x_properties.1],by linarith [x_properties.2.1]⟩ }
    refine ⟨M,(native_correct_iff M ε P hP hPh ρ hq).mpr (fun h => ?_)⟩
    change |x/2 - historyLaw x (ageProbability q) h| ≤ ε
    by_cases hz : false ∈ h
    · rw [historyLaw,if_pos hz]
      exact abs_le.mpr ⟨by linarith,by linarith [x_properties.1]⟩
    · rw [historyLaw,if_neg hz]
      exact abs_le.mpr ⟨by linarith [(hp.1 h.length).2],by linarith [(hp.1 h.length).1]⟩
  · intro S _ M hm
    exact exact_prediction_impossible x (ageProbability q) (fun n => (hp.1 n).1)
      hp.2.2 M ((native_correct_iff M 0 P hP hPh ρ hq).mp hm)

  · intro h hz
    unfold posterior
    rw [word_projection_trace P hP hPh]
    simp [alive,hz]

#print axioms native_predictor_minimum

end D5.S3.Quantum.Measurement.OneSidedGoldenHistory
