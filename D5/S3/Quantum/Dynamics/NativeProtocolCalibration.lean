/- GID: D5/S3/Quantum/Dynamics/NativeProtocolCalibration
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolCalibration
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Actual native source calibration and retained-event reduction feed the empty Petz comparison. -/

import D5.S3.Quantum.Dynamics.NativeProtocolEventArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Dynamics.NativeProtocolGraft
open Tree

namespace Actual
open scoped ComplexOrder MatrixOrder

/-- A computational vector on the complete original carrier. -/
def ket (b : Basis) : Basis → ℂ := fun z => if z = b then 1 else 0

private theorem flip_ne (i : Fin 16) (b : Basis) : flip i b ≠ b := by
  intro h
  have hi := congrFun h i
  cases hb : b i <;> simpa [flip, hb] using hi

private theorem flip_eq (i : Fin 16) (z b : Basis) :
    flip i z = b ↔ z = flip i b := by
  constructor <;> intro h
  · rw [← h, Coeff.flip_flip]
  · rw [h, Coeff.flip_flip]

private theorem gate_ket (j : Address) (b : Basis) :
    (gate j).mulVec (ket b) =
      (zeta * (1 + (zeta - 1) * Coeff.evalO t Coeff.t_sq (Coeff.diagonal j b))) • ket b +
      (if Coeff.active j b then zeta * (zeta - 1) * beta^3 else 0) •
        ket (flip (center j) b) := by
  funext z
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, Coeff.p_action, ket]
  by_cases hz : z = b
  · subst z
    simp [flip_ne, Ne.symm (flip_ne (center j) b)] <;> ring
  · by_cases hf : z = flip (center j) b
    · subst z
      simp only [Coeff.flip_flip, if_pos rfl, hz, if_false, mul_zero,
        mul_one, zero_add, Coeff.active_flip]
      split_ifs <;> ring
    · have hfb : flip (center j) z ≠ b := by
        exact fun h => hf ((flip_eq (center j) z b).mp h)
      simp [hz, hf, hfb]

/-- Source sites b1,b2,b3 are shifted positions 2,3,4; all other bits
remain the original root bits. -/
def sourceWord (x y z : Bool) : Basis :=
  Function.update (Function.update (Function.update rootWord 2 x) 3 y) 4 z

def a : ℂ := zeta * (1 + (zeta - 1) * t)
def b : ℂ := zeta * (zeta - 1) * beta^3
def c : ℂ := zeta * (1 + (zeta - 1) * t^2)

/-- The original three forward source calls, in chronological order. -/
def sourceTree : Tree Cut :=
  .call 3 .forward (.call 2 .forward (.call 1 .forward (.leaf .active)))

def sourceVector : Basis → ℂ :=
  (gate 1).mulVec ((gate 2).mulVec ((gate 3).mulVec omega0))

def fiveTermVector : Basis → ℂ :=
  (a^2*b) • ket (sourceWord false false false) +
  (a*b^2) • ket (sourceWord true false false) +
  (zeta*a*c) • ket (sourceWord false false true) +
  (zeta*b*c) • ket (sourceWord true false true) +
  (zeta*b^2) • ket (sourceWord false true false)

private theorem source_start : omega0 = ket (sourceWord false false true) := by
  have h : rootWord = sourceWord false false true := by decide
  change ket rootWord = ket (sourceWord false false true)
  exact congrArg ket h

private theorem source_steps :
    sourceVector = fiveTermVector := by
  have h3 : (gate 3).mulVec (ket (sourceWord false false true)) =
      b • ket (sourceWord false false false) +
      c • ket (sourceWord false false true) := by
    rw [gate_ket]
    have hf : flip (center 3) (sourceWord false false true) =
        sourceWord false false false := by decide
    rw [hf, show Coeff.diagonal 3 (sourceWord false false true) = Coeff.tau^2 by rfl,
      show Coeff.active 3 (sourceWord false false true) = true by rfl]
    simp only [Bool.true_eq, if_true, map_pow, Coeff.evalO_tau]
    change c • _ + b • _ = _
    abel
  have h20 : (gate 2).mulVec (ket (sourceWord false false false)) =
      a • ket (sourceWord false false false) +
      b • ket (sourceWord false true false) := by
    rw [gate_ket]
    have hf : flip (center 2) (sourceWord false false false) =
        sourceWord false true false := by decide
    rw [hf, show Coeff.diagonal 2 (sourceWord false false false) = Coeff.tau by rfl,
      show Coeff.active 2 (sourceWord false false false) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h21 : (gate 2).mulVec (ket (sourceWord false false true)) =
      zeta • ket (sourceWord false false true) := by
    rw [gate_ket, show Coeff.diagonal 2 (sourceWord false false true) = 0 by rfl,
      show Coeff.active 2 (sourceWord false false true) = false by rfl]
    simp
  have h10 : (gate 1).mulVec (ket (sourceWord false false false)) =
      a • ket (sourceWord false false false) +
      b • ket (sourceWord true false false) := by
    rw [gate_ket]
    have hf : flip (center 1) (sourceWord false false false) =
        sourceWord true false false := by decide
    rw [hf, show Coeff.diagonal 1 (sourceWord false false false) = Coeff.tau by rfl,
      show Coeff.active 1 (sourceWord false false false) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h11 : (gate 1).mulVec (ket (sourceWord false false true)) =
      a • ket (sourceWord false false true) +
      b • ket (sourceWord true false true) := by
    rw [gate_ket]
    have hf : flip (center 1) (sourceWord false false true) =
        sourceWord true false true := by decide
    rw [hf, show Coeff.diagonal 1 (sourceWord false false true) = Coeff.tau by rfl,
      show Coeff.active 1 (sourceWord false false true) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h12 : (gate 1).mulVec (ket (sourceWord false true false)) =
      zeta • ket (sourceWord false true false) := by
    rw [gate_ket, show Coeff.diagonal 1 (sourceWord false true false) = 0 by rfl,
      show Coeff.active 1 (sourceWord false true false) = false by rfl]
    simp
  rw [sourceVector, source_start, h3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h20, h21, h10, h11, h12]
  dsimp only [fiveTermVector]
  module

/-- Exact sparse action of the actual original full matrices on the fixed root. -/
private theorem original_source_vector :
    (operator sourceTree ()).mulVec omega0 = fiveTermVector ∧
    calls sourceTree () = 3 := by
  constructor
  · simpa [sourceTree, operator, callMatrix, sourceVector, Matrix.mulVec_mulVec, Matrix.mul_assoc] using source_steps
  · rfl


/-- The original complement contains all fifteen other native bits. -/
abbrev Rest := {i : Fin 16 // i ≠ 2} → Bool
def cut : Basis ≃ Fin 2 × Rest :=
  (Equiv.funSplitAt 2 Bool).trans (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl Rest))
abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
local instance : NormedAddCommGroup Qubit := Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ Qubit := Matrix.instL2OpNormedSpace
local instance : NormedRing Qubit := Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ Qubit := Matrix.instL2OpNormedAlgebra

/-- Mathematical reduction at original site b1. Original records remain
outside this operation; it asserts no physical deletion or fresh preparation. -/
def cross (v w : Basis → ℂ) : Qubit :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (Matrix.vecMulVec (v ∘ cut.symm) (star (w ∘ cut.symm)))

def reduced (v : Basis → ℂ) : Qubit := cross v v

/-! The raw reduced matrix supplied by one actual history event at the fixed
original b1 cut. The sum retains every selected history and all complement
coordinates; it performs no normalization. -/
def eventReduced {L : Type} (T : Tree L) (event : Path T → Bool) : Qubit :=
  ∑ p, if event p then reduced ((operator T p).mulVec omega0) else 0

private theorem reduced_trace (v : Basis → ℂ) :
    (Matrix.trace (reduced v)).re = ∑ z, Complex.normSq (v z) := by
  rw [reduced, cross,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply]
  rw [← (cut : Basis ≃ Fin 2 × Rest).sum_comp]
  simp only [Equiv.symm_apply_apply]
  calc
    (∑ x, v x * star (v x)).re =
        ∑ x, (v x * star (v x)).re := by
      exact Complex.re_sum Finset.univ (fun x => v x * star (v x))
    _ = ∑ x, Complex.normSq (v x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]

private theorem eventReduced_trace {L : Type} (T : Tree L)
    (event : Path T → Bool) :
    (Matrix.trace (eventReduced T event)).re = eventMass T (historyEvent event) := by
  classical
  change
    (Matrix.trace (∑ p, if event p then reduced ((operator T p).mulVec omega0) else 0)).re =
      ∑ p, ∑ z, if event p then
        Complex.normSq ((operator T p).mulVec omega0 z) else 0
  rw [Matrix.trace_sum]
  calc
    (∑ p, Matrix.trace (if event p then reduced ((operator T p).mulVec omega0) else 0)).re =
        ∑ p, (Matrix.trace (if event p then
          reduced ((operator T p).mulVec omega0) else 0)).re := by
      exact Complex.re_sum Finset.univ (fun p => Matrix.trace (if event p then
        reduced ((operator T p).mulVec omega0) else 0))
    _ = ∑ p, ∑ z, if event p then
        Complex.normSq ((operator T p).mulVec omega0 z) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : event p
      · simp [hp, reduced_trace]
      · simp [hp]

private theorem ket_cut (x : Basis) (i : Fin 2) (e : Rest) :
    ket x (cut.symm (i,e)) =
      if i = (cut x).1 then if e = (cut x).2 then 1 else 0 else 0 := by
  have h : cut.symm (i,e) = x ↔ i = (cut x).1 ∧ e = (cut x).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  simp only [ket, h]
  split_ifs <;> simp_all

private theorem source_rest (x y z x' y' z' : Bool) :
    (cut (sourceWord x y z)).2 = (cut (sourceWord x' y' z')).2 ↔
      y = y' ∧ z = z' := by
  cases x <;> cases y <;> cases z <;>
    cases x' <;> cases y' <;> cases z' <;> decide

/-- The lawful reduction is positive on every actual full-carrier vector. -/
private theorem reduced_positive (v : Basis → ℂ) : (reduced v).PosSemidef :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star (v ∘ cut.symm))

private theorem eventReduced_posSemidef {L : Type} (T : Tree L)
    (event : Path T → Bool) : (eventReduced T event).PosSemidef := by
  classical
  unfold eventReduced
  apply Matrix.posSemidef_sum
  intro p _
  split_ifs with hp
  · exact reduced_positive ((operator T p).mulVec omega0)
  · exact Matrix.PosSemidef.zero


private theorem cut_source_bit (x y z : Bool) :
    (cut (sourceWord x y z)).1 = if x then 1 else 0 := by
  cases x <;> rfl

open D5.S3.Quantum.Information.PartialTraceMutualInformation

private theorem cross_add_left (u v w : Basis → ℂ) :
    cross (u+v) w = cross u w + cross v w := by
  unfold cross
  change partialTraceRight
    (Matrix.vecMulVec ((u ∘ cut.symm)+(v ∘ cut.symm)) (star (w ∘ cut.symm))) = _
  rw [Matrix.add_vecMulVec, partialTraceRight_add]

private theorem cross_add_right (u v w : Basis → ℂ) :
    cross u (v+w) = cross u v + cross u w := by
  unfold cross
  change partialTraceRight
    (Matrix.vecMulVec (u ∘ cut.symm) (star ((v ∘ cut.symm)+(w ∘ cut.symm)))) = _
  rw [star_add, Matrix.vecMulVec_add, partialTraceRight_add]

private theorem cross_ket_smul (a b : ℂ) (x y : Basis) (i j : Fin 2) :
    cross (a • ket x) (b • ket y) i j =
      if i = (cut x).1 ∧ j = (cut y).1 ∧ (cut x).2 = (cut y).2
      then a * star b else 0 := by
  classical
  simp only [cross, partialTraceRight, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, map_mul, ket_cut]
  by_cases hi : i = (cut x).1 <;> by_cases hj : j = (cut y).1 <;>
    simp [hi, hj, mul_ite, ite_mul, apply_ite (starRingEnd ℂ), eq_comm]

def sourceLocal (i : Fin 2) : ℂ := if i = 0 then a else b
def p0 : Qubit := fun i j => if i = 0 ∧ j = 0 then 1 else 0
def sourceMixture : Qubit := fun i j =>
  (a * star a * b * star b + c * star c) * sourceLocal i * star (sourceLocal j) +
  (b * star b)^2 * p0 i j

private theorem source_reduction : reduced sourceVector = sourceMixture := by
  change cross sourceVector sourceVector = _
  rw [source_steps]
  simp only [fiveTermVector, cross_add_left, cross_add_right]
  ext i j
  simp only [Matrix.add_apply, cross_ket_smul, cut_source_bit, source_rest]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceMixture, sourceLocal, p0, Matrix.vecMulVec_apply,
      Pi.star_apply]
  all_goals simp only [starRingEnd_apply, star_mul, star_pow]
  · linear_combination
      (a * star a * c * star c + b^2 * (star b)^2) * Coeff.zeta_norm
  · linear_combination (a * star b * c * star c) * Coeff.zeta_norm
  · linear_combination (b * star a * c * star c) * Coeff.zeta_norm
  · linear_combination (b * star b * c * star c) * Coeff.zeta_norm

private theorem zeta_cube : zeta^3 = t-t*zeta := by
  calc
    zeta^3 = zeta*zeta^2 := by ring
    _ = zeta*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = -zeta-t*zeta^2 := by ring
    _ = -zeta-t*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = t+(t^2-1)*zeta := by ring
    _ = t-t*zeta := by rw [Coeff.t_sq]; ring

private theorem zeta_four : zeta^4 = t+zeta := by
  calc
    zeta^4 = zeta^3*zeta := by ring
    _ = (t-t*zeta)*zeta := by rw [zeta_cube]
    _ = t*zeta-t*zeta^2 := by ring
    _ = t*zeta-t*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = t+(t+t^2)*zeta := by ring
    _ = t+zeta := by rw [Coeff.t_sq]; ring

private theorem a_value : a = -t := by
  unfold a
  calc
    _ = zeta+(zeta^2-zeta)*t := by ring
    _ = zeta+(-1-t*zeta-zeta)*t := by rw [Coeff.zeta_sq]
    _ = -t := by linear_combination -zeta * Coeff.t_sq

private theorem b_value : b = -beta*zeta^4 := by
  have hb : beta^3 = beta*t := by rw [pow_succ, Coeff.beta_sq]; ring
  unfold b
  rw [hb, zeta_four]
  calc
    _ = (zeta^2-zeta)*beta*t := by ring
    _ = (-1-t*zeta-zeta)*beta*t := by rw [Coeff.zeta_sq]
    _ = -beta*(t+zeta) := by linear_combination -(beta*zeta) * Coeff.t_sq

private theorem c_value : c = -t*zeta^3 := by
  unfold c
  rw [Coeff.t_sq, zeta_cube]
  calc
    _ = zeta^2-(zeta+(zeta^2-zeta)*t)+zeta := by ring
    _ = -1-t*zeta-(-t)+zeta := by
      rw [show zeta+(zeta^2-zeta)*t = a by unfold a; ring,
        a_value, Coeff.zeta_sq]
    _ = -t*(t-t*zeta) := by linear_combination (1-zeta)*Coeff.t_sq

theorem star_t : star t = t := by simp [t]
theorem star_beta : star beta = beta := by simp [beta]
private theorem phase_norm (n : ℕ) : zeta^n * star (zeta^n) = 1 := by
  rw [star_pow, ← mul_pow, Coeff.zeta_norm, one_pow]

theorem a_norm : a * star a = t^2 := by
  rw [a_value, star_neg, star_t]; ring
theorem b_norm : b * star b = t := by
  rw [b_value, star_mul, star_neg, star_beta]
  calc
    _ = beta^2 * (zeta^4*star (zeta^4)) := by ring
    _ = t := by rw [phase_norm, Coeff.beta_sq, mul_one]
theorem c_norm : c * star c = t^2 := by
  rw [c_value, star_mul, star_neg, star_t]
  calc
    _ = t^2*(zeta^3*star (zeta^3)) := by ring
    _ = t^2 := by rw [phase_norm, mul_one]

def gamma : ℂ := t^2 * beta * star (zeta^4)
def chi : Qubit := !![t,gamma;star gamma,t^2]

private theorem mixture_chi : sourceMixture = chi := by
  have hw : a * star a * b * star b + c * star c = t := by
    rw [show a * star a * b * star b = (a*star a)*(b*star b) by ring,
      a_norm, b_norm, c_norm]
    linear_combination t * Coeff.t_sq
  ext i j
  simp only [sourceMixture, hw, b_norm]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceLocal, p0, chi, Matrix.vecMulVec_apply, Pi.star_apply]
  all_goals try simp only [starRingEnd_apply]
  · rw [show t*a*star a = t*(a*star a) by ring, a_norm]
    linear_combination t*Coeff.t_sq
  · rw [a_value, b_value, star_mul, star_neg, star_beta]
    unfold gamma
    ring
  · rw [a_value, b_value, star_neg, star_t]
    simp only [gamma, star_mul, star_pow, star_t, star_beta, star_star, starRingEnd_apply]
    ring
  · rw [show t*b*star b = t*(b*star b) by ring, b_norm]
    ring

/-- The full-carrier source calls give exactly the same native marginal chi. -/
private theorem original_source_calibration :
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧ chi.PosSemidef := by
  have hv := original_source_vector.1
  have hc : reduced ((operator sourceTree ()).mulVec omega0) = chi := by
    rw [hv, ← source_steps, source_reduction, mixture_chi]
  exact ⟨hc, hc ▸ reduced_positive _⟩



private theorem t_nonzero : t ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero Coeff.phi_positive.ne')

private theorem gamma_norm : gamma * star gamma = t^5 := by
  simp only [gamma, star_mul, star_pow, star_t, star_beta, star_star]
  calc
    _ = t^4 * beta^2 * (zeta^4 * star (zeta^4)) := by rw [star_pow]; ring
    _ = t^5 := by rw [phase_norm, Coeff.beta_sq]; ring

private theorem chi_det : chi.det = t^4 := by
  rw [Matrix.det_fin_two]
  change t * t^2 - gamma * star gamma = t^4
  rw [gamma_norm]
  linear_combination -(t^3)*Coeff.t_sq

private theorem chi_trace : chi.trace = 1 := by
  simp only [chi, Matrix.trace, Fin.sum_univ_two]
  norm_num
  linear_combination Coeff.t_sq

private theorem chi_faithful : chi.PosDef :=
  original_source_calibration.2.posDef_iff_det_ne_zero.mpr
    (chi_det ▸ pow_ne_zero 4 t_nonzero)

private theorem empty_reduction : reduced omega0 = p0 := by
  rw [source_start]
  change cross (ket (sourceWord false false true))
    (ket (sourceWord false false true)) = _
  rw [← one_smul ℂ (ket (sourceWord false false true))]
  ext i j
  rw [cross_ket_smul, cut_source_bit]
  fin_cases i <;> fin_cases j <;> norm_num [p0]

def rootScale : ℝ := Real.sqrt (1+2*(phi⁻¹)^2)
def chiRoot : Qubit := (rootScale : ℂ)⁻¹ • (chi + t^2 • (1 : Qubit))

private theorem rootScale_pos : 0 < rootScale := by
  dsimp [rootScale]
  positivity

private theorem rootScale_sq : (rootScale : ℂ)^2 = 1+2*t^2 := by
  dsimp [rootScale, t]
  norm_cast
  exact Real.sq_sqrt (by positivity)

private theorem chi_square : chi*chi = chi-t^4 • (1 : Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chi, Matrix.mul_apply, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul, star_t, star_pow]
  all_goals try simp only [starRingEnd_apply]
  · rw [gamma_norm]
    linear_combination (t^3+t)*Coeff.t_sq
  · linear_combination gamma*Coeff.t_sq
  · linear_combination (star gamma)*Coeff.t_sq
  · rw [mul_comm (star gamma) gamma, gamma_norm]
    linear_combination (t^3+t^2)*Coeff.t_sq

private theorem chiRoot_square : chiRoot*chiRoot = chi := by
  have hn : (rootScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr rootScale_pos.ne'
  have hnum : (chi+t^2 • (1 : Qubit)) * (chi+t^2 • (1 : Qubit)) =
      (1+2*t^2) • chi := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, chi_square]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
      smul_smul]
    module
  rw [chiRoot, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hnum, smul_smul]
  have hc : (rootScale : ℂ)⁻¹*(rootScale : ℂ)⁻¹*(1+2*t^2) = 1 := by
    rw [← rootScale_sq]
    field_simp
  rw [hc, one_smul]

private theorem chiRoot_positive : chiRoot.PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact original_source_calibration.2.add
      (Matrix.PosSemidef.one.smul (by
        simp only [t, ← Complex.ofReal_pow, Complex.nonneg_iff, Complex.ofReal_re,
          Complex.ofReal_im, and_true]
        positivity))
  · exact_mod_cast (inv_nonneg.mpr rootScale_pos.le : 0 ≤ rootScale⁻¹)

private theorem chi_sqrt : cfc Real.sqrt chi = chiRoot := by
  have h : CFC.sqrt chi = chiRoot :=
    CFC.sqrt_unique chiRoot_square chiRoot_positive.nonneg
  rwa [CFC.sqrt_eq_real_sqrt _ original_source_calibration.2.nonneg,
    cfcₙ_eq_cfc] at h


/-- The same original b1 instrument, after summing its retained read. -/
def delta (X : Qubit) : Qubit := Matrix.diagonal (fun i => X i i)

private theorem read_cut (i : Fin 2) (e : Rest) :
    readBit 2 (cut.symm (i,e)) = i := by
  fin_cases i <;> rfl

private theorem projected_cut (v : Basis → ℂ) (j i : Fin 2) (e : Rest) :
    ((projector (readBit 2) j).mulVec v) (cut.symm (i,e)) =
      if i = j then v (cut.symm (i,e)) else 0 := by
  simp [projector, Matrix.mulVec_diagonal, read_cut]

private theorem reduced_projector (v : Basis → ℂ) (o : Fin 2) :
    reduced ((projector (readBit 2) o).mulVec v) =
      fun i j => if i = o ∧ j = o then reduced v i j else 0 := by
  ext i j
  simp only [reduced, cross, partialTraceRight, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, projected_cut]
  by_cases hi : i = o <;> by_cases hj : j = o <;>
    simp [hi, hj, apply_ite (starRingEnd ℂ)]

private theorem native_delta (v : Basis → ℂ) :
    (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
      delta (reduced v) := by
  rw [Fin.sum_univ_two, reduced_projector, reduced_projector]
  ext i j
  change (if i = 0 ∧ j = 0 then reduced v i j else 0) +
    (if i = 1 ∧ j = 1 then reduced v i j else 0) =
    if i = j then reduced v i i else 0
  fin_cases i <;> fin_cases j <;> simp

private theorem read_empty (j : Fin 2) :
    (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0 := by
  funext z
  simp only [projector, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  by_cases hz : z = rootWord
  · subst z
    fin_cases j <;> norm_num [omega0, readBit, rootWord]
  · by_cases hj : j = 0 <;> simp [omega0, hz, hj]

def inverseRoot : Qubit := Matrix.diagonal ![beta⁻¹,t⁻¹]

private theorem h_diagonal :
    delta chi = Matrix.diagonal (fun i => ((![(phi⁻¹),(phi⁻¹)^2] : Fin 2 → ℝ) i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [delta, chi, t]

private theorem inverse_root :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi) = inverseRoot := by
  rw [h_diagonal,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseRoot, beta, t, Real.sqrt_sq (inv_nonneg.mpr Coeff.phi_positive.le),
      Real.sqrt_sq Coeff.phi_positive.le]

/-- The fixed mathematical Petz formula. This definition adds no native gate. -/
def petz (Y : Qubit) : Qubit :=
  cfc Real.sqrt chi *
    delta (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi) * Y *
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi)) *
    cfc Real.sqrt chi

private theorem petz_empty_entry :
    petz p0 1 1 = t^4/(1+2*t^2) := by
  have hb : beta ≠ 0 := by
    intro h
    have hs := Coeff.beta_sq
    rw [h, zero_pow (by decide)] at hs
    exact t_nonzero hs.symm
  have hr : (rootScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr rootScale_pos.ne'
  have hd : 1+2*t^2 ≠ 0 := by rw [← rootScale_sq]; exact pow_ne_zero 2 hr
  rw [petz, chi_sqrt, inverse_root]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, chiRoot, inverseRoot,
    delta, p0, chi, Pi.smul_apply, smul_eq_mul]
  simp only [starRingEnd_apply]
  have hg : star gamma * gamma = t^5 := by rw [mul_comm, gamma_norm]
  calc
    _ = (star gamma * gamma) / ((rootScale : ℂ)^2 * beta^2) := by field_simp <;> ring
    _ = t^4/(1+2*t^2) := by
      rw [hg, rootScale_sq, Coeff.beta_sq]
      field_simp <;> ring

private theorem empty_target_value :
    ((emptyTarget : ℝ) : ℂ) = t^4/(1+2*t^2) := by
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]
    ring
  have he : ((emptyTarget : ℝ) : ℂ) = (4-5*t)/11 := by
    simp only [t, emptyTarget, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hi]
    push_cast
    dsimp [phi]
    push_cast
    ring
  rw [he]
  have hd : 1+2*t^2 ≠ 0 := by
    rw [← rootScale_sq]
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr rootScale_pos.ne')
  apply (eq_div_iff hd).2
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff (by norm_num : (11 : ℂ) ≠ 0)).2
  linear_combination -(11*t^2-t+4)*Coeff.t_sq

end Actual

section
open Actual
open scoped ComplexOrder MatrixOrder
local instance : NormedAddCommGroup Actual.Qubit := Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ Actual.Qubit := Matrix.instL2OpNormedSpace
local instance : NormedRing Actual.Qubit := Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ Actual.Qubit := Matrix.instL2OpNormedAlgebra

/-- The actual three-call calibration, native read and fixed Petz empty-input
event are linked to every complete original continuation's raw discrepancy.
The separate five-call retained-history and full-record targets remain open. -/
theorem original_empty_petz_consumer :
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧
    calls sourceTree () = 3 ∧ chi.PosDef ∧ chi.trace = 1 ∧ chi.det = t^4 ∧
    cfc Real.sqrt chi = chiRoot ∧
    (∀ v : Basis → ℂ,
      (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
        delta (reduced v)) ∧
    reduced omega0 = p0 ∧
    (∀ j : Fin 2, (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0) ∧
    petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) ∧
    (∀ C : Fin 2 → Tree Stop,
      let T := extensionAt .active C
      eventMass T (fun _ z => z 2) ≠ (petz (reduced omega0) 1 1).re ∧
      1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
        |eventMass T (fun _ z => z 2) - (petz (reduced omega0) 1 1).re|) := by
  have hp : petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) := by
    rw [empty_reduction, petz_empty_entry, empty_target_value]
  refine ⟨original_source_calibration.1, original_source_vector.2,
    chi_faithful, chi_trace, chi_det, chi_sqrt, native_delta, empty_reduction,
    read_empty, hp, ?_⟩
  intro C
  dsimp only
  rw [hp, Complex.ofReal_re]
  exact ⟨(original_event_arithmetic _ _).2.1,
    (original_event_resource_bounds _ _).2.1⟩

#print axioms original_empty_petz_consumer

/-! The first proved bridge toward V88 theorem 24.1: at the actual original
b1 cut, a history event supplies its unnormalized positive reduced matrix and
the exact raw trace. The determinant and full-rank spectral clauses remain
separate obligations. -/
theorem original_event_cut_mass_and_psd {L : Type} (T : Tree L)
    (event : Path T → Bool) :
    (Matrix.trace (eventReduced T event)).re = eventMass T (historyEvent event) ∧
    (eventReduced T event).PosSemidef ∧
    (0 < eventMass T (historyEvent event) →
      (Coeff.kappa ^ (2 * maxCalls T))⁻¹ ≤ eventMass T (historyEvent event)) := by
  refine ⟨eventReduced_trace T event, eventReduced_posSemidef T event, ?_⟩
  exact (original_event_resource_bounds T (historyEvent event)).1

#print axioms original_event_cut_mass_and_psd

end

end D5.S3.Quantum.Dynamics.NativeProtocolGraft
