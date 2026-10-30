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
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Measurement.OneSidedGoldenHistory

open Matrix
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)

/-- Inverse golden ratio, with the source's square-root normalization. -/
def x : ℝ := Real.goldenRatio⁻¹

/-- The source's relative phase on the P branch. -/
def phase : ℂ := (Complex.exp ((3*Real.pi/5 : ℝ) * Complex.I)) ^ (-3 : ℤ)

private theorem x_properties : 0 < x ∧ x < 1 ∧ x+x^2=1 := by
  refine ⟨inv_pos.mpr Real.goldenRatio_pos, inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio, ?_⟩
  dsimp [x]
  have hp := Real.goldenRatio_sq
  field_simp
  nlinarith

variable {d : ℕ}

private def block (P : Matrix (Fin d) (Fin d) ℂ) (a b : ℂ) := a • (1-P) + b • P

private theorem block_mul (P : Matrix (Fin d) (Fin d) ℂ) (hP : P*P=P) (a b c e : ℂ) :
    block P a b * block P c e = block P (a*c) (b*e) := by
  have hEE : (1-P)*(1-P) = 1-P := by noncomm_ring [hP]
  have hEP : (1-P)*P = 0 := by simp [sub_mul,hP]
  have hPE : P*(1-P) = 0 := by simp [mul_sub,hP]
  simp [block,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,hEE,hEP,hPE,smul_smul]

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
  have hp : ‖phase‖ = 1 := by simp [phase,norm_zpow,he]
  simpa [Complex.normSq_eq_conj_mul_self,Complex.sq_norm] using congrArg (fun r : ℝ => (r^2 : ℂ)) hp

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
  constructor
  · rw [htrace,block_star P hPh,hE,block_mul P hP,block_mul P hP]
    simp [block,Matrix.smul_mul,Matrix.trace_smul]
  · rw [htrace,block_star P hPh,hQ,block_mul P hP,block_mul P hP]
    simp [block,Matrix.smul_mul,Matrix.trace_smul]

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
        norm_cast
        exact Real.sq_sqrt x_properties.1.le
      have hE : Matrix.trace ((1-P)*branch P false ρ) =
          (x : ℂ)*Matrix.trace ((1-P)*ρ) := by
        simpa [branch,kraus,block,hs] using hh.1
      have hQ : Matrix.trace (P*branch P false ρ) = 0 := by
        simpa [branch,kraus,block] using hh.2
      rw [hE,hQ]
      simp [exponent,alive,pow_add]
      ring
    · have hh := sector_trace P hP hPh x phase ρ
      rw [show star (x : ℂ)*(x : ℂ) = (x : ℂ)^2 by simp [pow_two],phase_unit] at hh
      rw [show Matrix.trace ((1-P)*branch P true ρ) =
          (x : ℂ)^2*Matrix.trace ((1-P)*ρ) from hh.1,
        show Matrix.trace (P*branch P true ρ) = Matrix.trace (P*ρ) by simpa using hh.2]
      simp [exponent,alive,pow_add]
      ring

private theorem exponent_append (a b : List Bool) : exponent (a++b) = exponent a+exponent b := by
  induction a with
  | nil => rfl
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
  have hm := real_mass P hP hPh state hn
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
    dsimp [q,state]
    ring
  · intro h
    unfold nextZero
    rw [hm (h++[false]),exponent_append]
    simp only [List.mem_append,List.mem_singleton,or_true,↓reduceIte,exponent,add_zero]
    by_cases hz : false ∈ h
    · rw [if_pos hz,hm h,if_pos hz]
      dsimp [q] at *
      rw [pow_add,pow_one]
      field_simp
      <;> ring
    · rw [if_neg hz,hm h,if_neg hz,exponent_no_zero _ hz]
      unfold ageProbability
      dsimp [q]
      rw [pow_add,pow_one]
      ring

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
      exact pow_le_pow_of_le_one hx.1.le hx.2.le (Nat.mul_le_mul_left 2 hmn)
    unfold ageProbability
    apply (div_le_div_iff₀ (hd n) (hd m)).mpr
    nlinarith [mul_nonneg (mul_nonneg hx.1.le (by linarith : 0 ≤ 1-q))
      (sub_nonneg.mpr ht),hq.1]
  · have hh : x^2 < 1 := by nlinarith [hx.2]
    have ht : Tendsto (fun n : ℕ => x^(2*n)) atTop (𝓝 0) := by
      simpa [pow_mul] using tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg x) hh
    have hl := ((tendsto_const_nhds.mul ht).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul ht)) (ne_of_gt hq.1))
    simpa [ageProbability] using hl

/-- The actual retained golden process has the attained N+2 state minimum at
the first nonstrict threshold, a one-state high-error predictor, and no exact
finite predictor. The logarithmic evaluation of N is a separate assertion. -/
theorem native_predictor_minimum (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P*P=P) (hPh : P.IsHermitian) (ρ : DensityState (Fin d))
    (hq : 0 < (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re ∧
      (Matrix.trace (P*CStarMatrix.ofMatrix.symm ρ.val)).re < 1) :
    let state := CStarMatrix.ofMatrix.symm ρ.val
    let q := (Matrix.trace (P*state)).re
    (∀ h, 0 < mass P state h ∧
      nextZero P state h = if false ∈ h then x else ageProbability q h.length) ∧
    (∀ ε : ℝ, 0 < ε → ε < x/2 → ∃ N : ℕ,
      (∀ n, ageProbability q n ≤ 2*ε ↔ N ≤ n) ∧
      (∃ M : Predictor (Fin (N+1) ⊕ Unit), NativeCorrect M P ρ ε) ∧
      Fintype.card (Fin (N+1) ⊕ Unit) = N+2 ∧
      ∀ (S : Type*) [Fintype S] (M : Predictor S), NativeCorrect M P ρ ε → N+2 ≤ Fintype.card S) ∧
    (∀ ε : ℝ, x/2 ≤ ε → ∃ M : Predictor Unit, NativeCorrect M P ρ ε) ∧
    (∀ (S : Type*) [Fintype S] (M : Predictor S), ¬ NativeCorrect M P ρ 0) := by
  dsimp only
  let state := CStarMatrix.ofMatrix.symm ρ.val
  let q := (Matrix.trace (P*state)).re
  have hlaw := native_history_law P hP hPh ρ hq
  have hp := age_properties q hq
  have heq {S : Type*} (M : Predictor S) (ε : ℝ) :
      NativeCorrect M P ρ ε ↔ Correct M x (ageProbability q) ε := by
    constructor
    · intro h hst
      have hh := h hst (hlaw.1 hst)
      simpa [Correct,historyLaw,hlaw.2.2 hst,q,state] using hh
    · intro h hst _
      simpa [historyLaw,hlaw.2.2 hst,q,state] using h hst
  refine ⟨fun h => ⟨hlaw.1 h,hlaw.2.2 h⟩,?_,?_,?_⟩
  · intro ε hε hsmall
    have hex : ∃ n, ageProbability q n ≤ 2*ε := by
      have hh := hp.2.2.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 2*ε))
      obtain ⟨n,hn⟩ := hh.exists
      exact ⟨n,hn.le⟩
    let N := Nat.find hex
    have hcut (n : ℕ) : ageProbability q n ≤ 2*ε ↔ N ≤ n := by
      constructor
      · intro hn
        exact Nat.find_min' hex hn
      · intro hn
        exact (hp.2.1 hn).trans (Nat.find_spec hex)
    have hmin := sharp_predictor_minimum x ε (ageProbability q) N
      ⟨x_properties.1,x_properties.2.1.le⟩ hε.le (by linarith)
      (fun n => (hp.1 n).1.le) (fun n => (hp.1 n).2) hp.2.1 hp.2.2 hcut
    obtain ⟨M,hM⟩ := hmin.1
    exact ⟨N,hcut,⟨M,(heq M ε).mpr hM⟩,hmin.2.1,
      fun S _ M hM => hmin.2.2 S M ((heq M ε).mp hM)⟩
  · intro ε hε
    let M : Predictor Unit := {
      initial := ()
      update := fun _ _ => ()
      output := fun _ => x/2
      output_mem := fun _ => ⟨by linarith [x_properties.1],by linarith [x_properties.2.1]⟩ }
    refine ⟨M,(heq M ε).mpr (fun h => ?_)⟩
    change |x/2 - historyLaw x (ageProbability q) h| ≤ ε
    by_cases hz : false ∈ h
    · rw [historyLaw,if_pos hz]
      exact abs_le.mpr ⟨by linarith,by linarith [x_properties.1]⟩
    · rw [historyLaw,if_neg hz]
      exact abs_le.mpr ⟨by linarith [(hp.1 h.length).2],by linarith [(hp.1 h.length).1]⟩
  · intro S _ M hm
    exact exact_prediction_impossible x (ageProbability q) (fun n => (hp.1 n).1)
      hp.2.2 M ((heq M 0).mp hm)

#print axioms native_predictor_minimum

end D5.S3.Quantum.Measurement.OneSidedGoldenHistory
