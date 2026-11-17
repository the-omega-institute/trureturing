/- GID: D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolBornNormalization
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Complete original protocol trees conserve Born mass at every position cut. -/

import D5.S3.Quantum.Dynamics.NativeProtocolCalibration
import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound

/-! Physical normalization of the complete original native protocol tree. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
open D5.S3.Quantum.Dynamics.NativeProtocolGraft
open D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree
open D5.S3.Quantum.Dynamics.NativeProtocolGraft.Actual

private theorem block_orthogonal : a * star b + b * star c = 0 := by
  have hs : t + t^2 = 1 := by linear_combination Coeff.t_sq
  have hz := Coeff.zeta_norm
  have he : a * star b + b * star c =
      (zeta * star zeta) * beta^3 *
        ((star zeta - 1) + (zeta - 1) +
          (zeta - 1) * (star zeta - 1) * (t + t^2)) := by
    simp only [a, b, c, star_mul, star_add, star_sub, star_one, star_pow,
      star_t, star_beta]
    ring
  rw [he, hs, hz]
  linear_combination beta^3 * hz

private theorem block_energy (x y : ℂ) :
    Complex.normSq (a*x+b*y) + Complex.normSq (b*x+c*y) =
      Complex.normSq x + Complex.normSq y := by
  have ha : a * star a + b * star b = 1 := by
    rw [a_norm, b_norm]
    linear_combination Coeff.t_sq
  have hc : b * star b + c * star c = 1 := by
    rw [b_norm, c_norm]
    linear_combination Coeff.t_sq
  have ho := block_orthogonal
  have ho' : star a * b + star b * c = 0 := by
    simpa only [star_add, star_mul, star_star, star_zero, mul_comm] using congrArg star ho
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, ← Complex.star_def,
    star_add, star_mul]
  linear_combination (star x*x)*ha + (star y*y)*hc + (star y*x)*ho +
    (star x*y)*ho'

private theorem gate_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (gate j).mulVec w z =
      if z (left j) then (if z (right j) then zeta^2 * w z else zeta * w z)
      else if z (right j) then zeta * w z
      else if z (center j) then b * w (NativeProtocolGraft.flip (center j) z) + c * w z
      else a * w z + b * w (NativeProtocolGraft.flip (center j) z) := by
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, Coeff.p_action]
  have ht : Coeff.evalO t Coeff.t_sq Coeff.tau = t := by
    simp [Coeff.evalO, Coeff.tau]
  cases hl : z (left j) <;> cases hr : z (right j) <;> cases hc : z (center j) <;>
    simp [Coeff.diagonal, Coeff.active, hl, hr, hc, map_pow, ht, a, b, c] <;> ring

private theorem gate_pair (j : Address) (w : Basis → ℂ) (z : Basis) :
    Complex.normSq ((gate j).mulVec w z) +
      Complex.normSq ((gate j).mulVec w (NativeProtocolGraft.flip (center j) z)) =
      Complex.normSq (w z) + Complex.normSq (w (NativeProtocolGraft.flip (center j) z)) := by
  have hf : NativeProtocolGraft.flip (center j) z (center j) = !(z (center j)) := by
    simp [NativeProtocolGraft.flip]
  have hl : NativeProtocolGraft.flip (center j) z (left j) = z (left j) := by
    apply Function.update_of_ne
    intro h
    have hh := congrArg Fin.val h
    simp [left, center] at hh
  have hr : NativeProtocolGraft.flip (center j) z (right j) = z (right j) := by
    apply Function.update_of_ne
    intro h
    have hh := congrArg Fin.val h
    simp [right, center] at hh
  have hz : Complex.normSq zeta = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [← Complex.star_def, mul_comm, Complex.ofReal_one] using Coeff.zeta_norm
  rw [gate_action, gate_action]
  simp only [hl, hr, hf, Coeff.flip_flip]
  cases hzl : z (left j) <;> cases hzr : z (right j) <;> cases hzc : z (center j) <;>
    simp only [hzl, hzr, hzc, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true]
  all_goals first
    | exact block_energy _ _
    | simpa only [add_comm] using block_energy (w (NativeProtocolGraft.flip (center j) z)) (w z)
    | simp only [map_mul, map_pow, hz, one_pow, one_mul]

private theorem gate_energy (j : Address) (w : Basis → ℂ) :
    Coeff.energy ((gate j).mulVec w) = Coeff.energy w := by
  classical
  have h := congrArg (fun f : Basis → ℝ => ∑ z, f z) (funext (gate_pair j w))
  simp only [Finset.sum_add_distrib] at h
  have hg := Coeff.flip_sum (center j) (fun z => Complex.normSq ((gate j).mulVec w z))
  have hw := Coeff.flip_sum (center j) (fun z => Complex.normSq (w z))
  rw [hg, hw] at h
  dsimp [Coeff.energy]
  linarith

private theorem power_energy (j : Address) (n : ℕ) (w : Basis → ℂ) :
    Coeff.energy ((gate j ^ n).mulVec w) = Coeff.energy w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, gate_energy]

private theorem call_energy (j : Address) (d : Direction) (w : Basis → ℂ) :
    Coeff.energy ((callMatrix j d).mulVec w) = Coeff.energy w := by
  cases d
  · exact gate_energy j w
  · exact power_energy j 9 w

private theorem measurement_energy {n : ℕ} (select : Basis → Fin n)
    (w : Basis → ℂ) :
    (∑ o, Coeff.energy ((projector select o).mulVec w)) = Coeff.energy w := by
  classical
  unfold Coeff.energy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [projector, Matrix.mulVec_diagonal, apply_ite]

/-- Conservation for arbitrary incoming vectors, proved on the original
finite tree with every outcome and its own continuation retained. -/
private theorem whole_tree_energy {L : Type} (T : NativeProtocolGraft.Tree L) (w : Basis → ℂ) :
    (∑ p : Path T, Coeff.energy ((operator T p).mulVec w)) = Coeff.energy w := by
  classical
  induction T generalizing w with
  | leaf l =>
    change (∑ _p : Unit, Coeff.energy ((1 : Mat).mulVec w)) = Coeff.energy w
    simp
  | call j d U ih =>
    change (∑ p : Path U, Coeff.energy
      ((operator U p * callMatrix j d).mulVec w)) = _
    simp only [← Matrix.mulVec_mulVec]
    rw [ih, call_energy]
  | measure n select U ih =>
    change (∑ p : (o : Fin n) × Path (U o), Coeff.energy
      ((operator (U p.1) p.2 * projector select p.1).mulVec w)) = _
    simp only [← Matrix.mulVec_mulVec]
    rw [Fintype.sum_sigma]
    simp_rw [ih]
    exact measurement_energy select w

/-- Computational coordinates on precisely the selected original positions. -/
abbrev CutBasis (I : Finset (Fin 16)) := {i : Fin 16 // i ∈ I} → Bool
abbrev CutRest (I : Finset (Fin 16)) := {i : Fin 16 // i ∉ I} → Bool

def splitAt (I : Finset (Fin 16)) : Basis ≃ CutBasis I × CutRest I :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun _ => Bool)

/-- The original branch vector reduced at the actual position subset. -/
def cutReduced (I : Finset (Fin 16)) (v : Basis → ℂ) :
    Matrix (CutBasis I) (CutBasis I) ℂ :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (Matrix.vecMulVec (v ∘ (splitAt I).symm) (star (v ∘ (splitAt I).symm)))

/-- Sum of original unnormalized branch reductions over the acquired paths. -/
def eventCut {L : Type} (T : NativeProtocolGraft.Tree L) (I : Finset (Fin 16))
    (event : Path T → Bool) : Matrix (CutBasis I) (CutBasis I) ℂ :=
  ∑ p, if event p then cutReduced I ((operator T p).mulVec omega0) else 0

private theorem cutReduced_trace (I : Finset (Fin 16)) (v : Basis → ℂ) :
    (cutReduced I v).trace = (Coeff.energy v : ℂ) := by
  rw [cutReduced,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.trace_partialTraceRight]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, Coeff.energy]
  rw [← (splitAt I).sum_comp]
  simp only [Equiv.symm_apply_apply, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem event_mass_energy {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) :
    eventMass T (historyEvent event) =
      ∑ p, if event p then Coeff.energy ((operator T p).mulVec omega0) else 0 := by
  unfold eventMass historyEvent mass
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : event p
  · simp [he, Coeff.energy]
  · simp [he]

private theorem eventCut_trace {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (eventCut T I event).trace = (eventMass T (historyEvent event) : ℂ) := by
  rw [event_mass_energy, eventCut, Matrix.trace_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : event p <;> simp [he, cutReduced_trace]

private theorem eventCut_positive {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (eventCut T I event).PosSemidef := by
  classical
  unfold eventCut
  apply Matrix.posSemidef_sum
  intro p _
  split_ifs
  · exact D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star _)
  · exact Matrix.PosSemidef.zero

/-- The original complete Born law and the raw trace of the same acquired
history event at every original position cut, without normalization premises. -/
theorem original_complete_born_law {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) (I : Finset (Fin 16)) :
    (∑ p, ∑ z, mass T p z) = 1 ∧
    (0 ≤ eventMass T (historyEvent event) ∧ eventMass T (historyEvent event) ≤ 1) ∧
    (eventCut T I event).PosSemidef ∧
    (eventCut T I event).trace = (eventMass T (historyEvent event) : ℂ) := by
  classical
  have ht : (∑ p, ∑ z, mass T p z) = 1 := by
    change (∑ p, Coeff.energy ((operator T p).mulVec omega0)) = 1
    rw [whole_tree_energy]
    simp [Coeff.energy, omega0]
  have hn : 0 ≤ eventMass T (historyEvent event) := by
    have hc := original_event_cut_mass_and_psd T event
    rw [← hc.1]
    exact (RCLike.nonneg_iff.mp hc.2.1.trace_nonneg).1
  have hb : eventMass T (historyEvent event) ≤ ∑ p, ∑ z, mass T p z := by
    unfold eventMass
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro z _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  exact ⟨ht, ⟨hn, hb.trans_eq ht⟩, eventCut_positive T I event, eventCut_trace T I event⟩


/-- Hamming parity on the retained and complementary original positions. -/
def rowParity (I : Finset (Fin 16)) (i : CutBasis I) : ZMod 2 :=
  ∑ k, if i k then 1 else 0

def restParity (I : Finset (Fin 16)) (z : CutRest I) : ZMod 2 :=
  (∑ k, if z k then 1 else 0) -
    ∑ k : Fin 16, if rootWord k then 1 else 0

def rowExponent (I : Finset (Fin 16)) (i : CutBasis I) : ℕ :=
  if rowParity I i = 0 then 0 else 1

def restExponent (I : Finset (Fin 16)) (z : CutRest I) : ℕ :=
  if restParity I z = 0 then 0 else 1

private theorem zmod_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hv := x.val_lt
  have hr := ZMod.natCast_zmod_val x
  interval_cases x.val <;> simp_all

private theorem split_parity (I : Finset (Fin 16)) (i : CutBasis I) (z : CutRest I) :
    Coeff.parity ((splitAt I).symm (i,z)) = rowParity I i + restParity I z := by
  classical
  have hl (k : {k : Fin 16 // k ∈ I}) :
      ((splitAt I).symm (i,z)) k = i k := by
    change (if h : k.val ∈ I then i ⟨k.val,h⟩ else z ⟨k.val,h⟩) = i k
    simp only [dite_eq_left k.property]
  have hr (k : {k : Fin 16 // k ∉ I}) :
      ((splitAt I).symm (i,z)) k = z k := by
    change (if h : k.val ∈ I then i ⟨k.val,h⟩ else z ⟨k.val,h⟩) = z k
    simp only [dite_eq_right k.property]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun k : Fin 16 => k ∈ I)
    (fun k => if ((splitAt I).symm (i,z)) k then (1 : ZMod 2) else 0)
  simp only [hl,hr] at hs
  unfold Coeff.parity rowParity restParity
  rw [← hs, add_sub_assoc]
  congr 1
  apply Finset.sum_congr
  · ext k; simp
  · intro k _; rfl

private theorem split_exponent (I : Finset (Fin 16)) (i : CutBasis I) (z : CutRest I) :
    Coeff.exponent ((splitAt I).symm (i,z)) =
      (rowExponent I i + restExponent I z) % 2 := by
  rcases zmod_cases (rowParity I i) with hi | hi <;>
    rcases zmod_cases (restParity I z) with hz | hz <;>
    norm_num [Coeff.exponent, split_parity, rowExponent, restExponent, hi, hz] <;> decide

/-- Removing the row and column square-root factors stays in the original
four-integer coefficient ring, since tau inverse is tau plus one. -/
def cutCoefficient (I : Finset (Fin 16)) (h : Basis → Coeff.S)
    (i : CutBasis I) (z : CutRest I) : Coeff.S :=
  Coeff.inc ((Coeff.tau+1)^(rowExponent I i * restExponent I z)) *
    h ((splitAt I).symm (i,z))

private theorem cut_amplitude (I : Finset (Fin 16)) (h : Basis → Coeff.S)
    (i : CutBasis I) (z : CutRest I) :
    Coeff.amplitude h ((splitAt I).symm (i,z)) =
      beta^rowExponent I i * beta^restExponent I z *
        Coeff.physical (cutCoefficient I h i z) := by
  have hi : rowExponent I i = 0 ∨ rowExponent I i = 1 := by
    unfold rowExponent; split_ifs <;> simp
  have hz : restExponent I z = 0 ∨ restExponent I z = 1 := by
    unfold restExponent; split_ifs <;> simp
  have ht : Coeff.physical (Coeff.inc Coeff.tau) = t := by
    simp [Coeff.physical, Coeff.evalS, Coeff.inc]
  have he := split_exponent I i z
  unfold Coeff.amplitude cutCoefficient
  simp only [map_mul, map_pow, map_add, map_one, ht]
  rw [he]
  rcases hi with hi | hi <;> rcases hz with hz | hz <;>
    simp only [hi,hz,Nat.zero_mul,Nat.mul_zero,Nat.one_mul,Nat.mul_one,
      Nat.zero_add,Nat.add_zero,pow_zero,pow_one,one_mul] <;> norm_num
  rw [← mul_assoc, ← pow_two, Coeff.beta_sq]
  have htq := Coeff.t_sq
  linear_combination -(Coeff.physical (h ((splitAt I).symm (i,z)))) * htq


private theorem evalS_star (u v : ℂ) (hu hv) (huStar : star u = u)
    (hvStar : v + star v = -u) (x : Coeff.S) :
    Coeff.evalS u v hu hv (star x) = star (Coeff.evalS u v hu hv x) := by
  have hr (a : Coeff.O) : star (Coeff.evalO u hu a) = Coeff.evalO u hu a := by
    simp [Coeff.evalO, huStar]
  change Coeff.evalO u hu (star x).re + Coeff.evalO u hu (star x).im * v =
    star (Coeff.evalO u hu x.re + Coeff.evalO u hu x.im * v)
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    map_add, map_mul, map_neg, Coeff.evalO_tau, star_add, star_mul, hr]
  linear_combination -(Coeff.evalO u hu x.im) * hvStar

private theorem physical_star (x : Coeff.S) :
    Coeff.physical (star x) = star (Coeff.physical x) := by
  have hz : zeta ≠ 0 := by
    intro hz
    simpa [hz] using Coeff.zeta_norm
  have hs : zeta + star zeta = -t := by
    apply mul_left_cancel₀ hz
    rw [mul_add, Coeff.zeta_norm]
    linear_combination Coeff.zeta_sq
  unfold Coeff.physical
  apply evalS_star t zeta _ _ (by simp [t]) hs

private theorem nonphysical_star (x : Coeff.S) :
    Coeff.nonphysical (star x) = star (Coeff.nonphysical x) := by
  have hs : Coeff.conjugateZeta + star Coeff.conjugateZeta = (phi : ℂ) := by
    apply Complex.ext
    · simp [Coeff.conjugateZeta, Complex.exp_re, Real.cos_pi_div_five, phi]
      ring
    · simp
  unfold Coeff.nonphysical
  apply evalS_star (-(phi : ℂ)) Coeff.conjugateZeta _ _ (by simp) (by simpa using hs)

private theorem inc_star (x : Coeff.O) : star (Coeff.inc x) = Coeff.inc x := by
  apply QuadraticAlgebra.ext
  · change x + (-Coeff.tau)*0 = x
    ring
  · change -(0 : Coeff.O) = 0
    exact neg_zero

/-- Coefficients for the same original cut after extracting its row factors. -/
def cutKernel {L : Type} (T : NativeProtocolGraft.Tree L) (I : Finset (Fin 16))
    (event : Path T → Bool) : Matrix (CutBasis I) (CutBasis I) Coeff.S :=
  fun i j => ∑ p, ∑ z : CutRest I, if event p then
    Coeff.inc (Coeff.tau ^ restExponent I z) *
      cutCoefficient I (Coeff.branch T p Coeff.initial) i z *
      star (cutCoefficient I (Coeff.branch T p Coeff.initial) j z) else 0

private theorem cutKernel_hermitian {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (cutKernel T I event)ᴴ = cutKernel T I event := by
  classical
  apply Matrix.ext
  intro i j
  simp only [Matrix.conjTranspose_apply, cutKernel, star_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp only [star_mul, star_star, inc_star, star_zero] <;> ring

private theorem eventCut_factor {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    eventCut T I event =
      Matrix.diagonal (fun i => beta^rowExponent I i) *
        (cutKernel T I event).map Coeff.physical *
      Matrix.diagonal (fun i => beta^rowExponent I i) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, cutKernel,
    map_sum, mul_assoc, Finset.mul_sum, Finset.sum_mul]
  simp only [eventCut, Matrix.sum_apply]
  change (∑ p, (if event p then cutReduced I ((operator T p).mulVec omega0) else 0) i j) = _
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : event p
  · simp only [he, ite_true, map_mul, map_pow, physical_star, cutReduced,
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      Matrix.vecMulVec_apply, Function.comp_apply, Pi.star_apply]
    rw [← (Coeff.original_branch_evaluations T).1 p]
    apply Finset.sum_congr rfl
    intro z _
    rw [cut_amplitude, cut_amplitude]
    have ht : Coeff.physical (Coeff.inc Coeff.tau) = t := by
      simp [Coeff.physical, Coeff.evalS, Coeff.inc]
    rw [ht]
    simp only [star_mul, star_pow, show star beta = beta by simp [beta]]
    have hb : beta^restExponent I z * beta^restExponent I z = t^restExponent I z := by
      rw [← mul_pow, ← pow_two, Coeff.beta_sq]
    linear_combination
      (beta^rowExponent I i * beta^rowExponent I j *
        Coeff.physical (cutCoefficient I (Coeff.branch T p Coeff.initial) i z) *
        star (Coeff.physical (cutCoefficient I (Coeff.branch T p Coeff.initial) j z))) * hb
  · simp [he]

private theorem fixed_coefficient (x : Coeff.S) (hx : star x = x) :
    Coeff.inc x.re = x := by
  have hi : -x.im = x.im := congrArg QuadraticAlgebra.im hx
  have hir := congrArg QuadraticAlgebra.re hi
  have hii := congrArg QuadraticAlgebra.im hi
  have hz : x.im = 0 := by
    apply QuadraticAlgebra.ext <;> simp only [QuadraticAlgebra.re_neg,
      QuadraticAlgebra.im_neg, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero] at * <;> omega
  apply QuadraticAlgebra.ext <;> simp [Coeff.inc, hz]

/-- The actual determinant's inverse-golden integer coordinates. -/
def cutDetCoordinates {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) : Coeff.O :=
  (∏ i : CutBasis I, Coeff.tau^rowExponent I i) * (cutKernel T I event).det.re


private def evaluatedCut {L : Type} (f : Coeff.S →+* ℂ) (b : ℂ)
    (T : NativeProtocolGraft.Tree L) (I : Finset (Fin 16)) (event : Path T → Bool) :
    Matrix (CutBasis I) (CutBasis I) ℂ :=
  Matrix.diagonal (fun i => b^rowExponent I i) *
    (cutKernel T I event).map f * Matrix.diagonal (fun i => b^rowExponent I i)

/-- Apply the chosen nonphysical evaluation to the same integral cut formula.
Both row factors use beta-prime, without conjugating the second one. -/
def conjugateEventCut {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    Matrix (CutBasis I) (CutBasis I) ℂ :=
  evaluatedCut Coeff.nonphysical Coeff.conjugateBeta T I event

private theorem evaluatedCut_det {L : Type} (f : Coeff.S →+* ℂ) (b u : ℂ)
    (hu : u ^ 2 = 1 - u) (hf : ∀ x, f (Coeff.inc x) = Coeff.evalO u hu x)
    (hb : b ^ 2 = u) (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (evaluatedCut f b T I event).det = Coeff.evalO u hu (cutDetCoordinates T I event) := by
  classical
  have hx : Coeff.inc (cutKernel T I event).det.re = (cutKernel T I event).det := by
    apply fixed_coefficient
    rw [← Matrix.det_conjTranspose, cutKernel_hermitian]
  have hp : (∏ i : CutBasis I, b^rowExponent I i) *
      (∏ i : CutBasis I, b^rowExponent I i) = ∏ i : CutBasis I, u^rowExponent I i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow, ← pow_two, hb]
  have hd : ((cutKernel T I event).map f).det = f (cutKernel T I event).det :=
    (f.map_det _).symm
  simp only [evaluatedCut, Matrix.det_mul, Matrix.det_diagonal]
  rw [hd, ← hx, hf]
  unfold cutDetCoordinates
  simp only [map_mul, map_prod, map_pow, Coeff.evalO_tau]
  linear_combination Coeff.evalO u hu (cutKernel T I event).det.re * hp

private theorem cut_det_physical {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (eventCut T I event).det = (Coeff.realPhysical (cutDetCoordinates T I event) : ℂ) := by
  rw [eventCut_factor]
  change (evaluatedCut Coeff.physical beta T I event).det = _
  rw [evaluatedCut_det Coeff.physical beta t Coeff.t_sq
    (fun x => by simp [Coeff.physical, Coeff.evalS, Coeff.inc]) Coeff.beta_sq]
  simp [Coeff.realPhysical, Coeff.evalO, t]

private theorem cut_det_conjugate {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (conjugateEventCut T I event).det =
      (Coeff.realConjugate (cutDetCoordinates T I event) : ℂ) := by
  have hb : Coeff.conjugateBeta^2 = -(phi : ℂ) := by
    simp [Coeff.conjugateBeta, mul_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt Coeff.phi_positive.le]
  have hu : (-(phi : ℂ))^2 = 1- (-(phi : ℂ)) := by
    have hh : phi^2 = phi+1 := Real.goldenRatio_sq
    exact_mod_cast (by nlinarith only [hh] : (-phi)^2 = 1-(-phi))
  unfold conjugateEventCut
  rw [evaluatedCut_det Coeff.nonphysical Coeff.conjugateBeta (-(phi : ℂ)) hu
    (fun x => by simp [Coeff.nonphysical, Coeff.evalS, Coeff.inc]) hb]
  simp [Coeff.realConjugate, Coeff.evalO]


private theorem cut_conjugate_amplitude (I : Finset (Fin 16)) (h : Basis → Coeff.S)
    (i : CutBasis I) (z : CutRest I) :
    Coeff.conjugateAmplitude h ((splitAt I).symm (i,z)) =
      Coeff.conjugateBeta^rowExponent I i * Coeff.conjugateBeta^restExponent I z *
        Coeff.nonphysical (cutCoefficient I h i z) := by
  have hi : rowExponent I i = 0 ∨ rowExponent I i = 1 := by
    unfold rowExponent; split_ifs <;> simp
  have hz : restExponent I z = 0 ∨ restExponent I z = 1 := by
    unfold restExponent; split_ifs <;> simp
  have ht : Coeff.nonphysical (Coeff.inc Coeff.tau) = -(phi : ℂ) := by
    simp [Coeff.nonphysical, Coeff.evalS, Coeff.inc]
  have hb : Coeff.conjugateBeta^2 = -(phi : ℂ) := by
    simp [Coeff.conjugateBeta, mul_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt Coeff.phi_positive.le]
  have he := split_exponent I i z
  unfold Coeff.conjugateAmplitude cutCoefficient
  simp only [map_mul, map_pow, map_add, map_one, ht]
  rw [he]
  rcases hi with hi | hi <;> rcases hz with hz | hz <;>
    simp only [hi,hz,Nat.zero_mul,Nat.mul_zero,Nat.one_mul,Nat.mul_one,
      Nat.zero_add,Nat.add_zero,pow_zero,pow_one,one_mul] <;> norm_num
  rw [← mul_assoc, ← pow_two, hb]
  have htq : (-(phi : ℂ))^2 = 1- (-(phi : ℂ)) := by
    have hh : phi^2 = phi+1 := Real.goldenRatio_sq
    exact_mod_cast (by nlinarith only [hh] : (-phi)^2 = 1-(-phi))
  linear_combination -(Coeff.nonphysical (h ((splitAt I).symm (i,z)))) * htq

private theorem conjugateEventCut_signed {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) (i j : CutBasis I) :
    conjugateEventCut T I event i j =
      ∑ p, ∑ z : CutRest I, if event p then
        (-1 : ℂ)^(restExponent I z + rowExponent I j) *
        Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (i,z)) *
        star (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (j,z)))
      else 0 := by
  classical
  simp only [conjugateEventCut, evaluatedCut, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply, cutKernel, map_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  by_cases he : event p
  · simp only [he, ite_true, map_mul, map_pow, nonphysical_star]
    rw [cut_conjugate_amplitude, cut_conjugate_amplitude]
    have ht : Coeff.nonphysical (Coeff.inc Coeff.tau) = -(phi : ℂ) := by
      simp [Coeff.nonphysical, Coeff.evalS, Coeff.inc]
    have hb : Coeff.conjugateBeta^2 = -(phi : ℂ) := by
      simp [Coeff.conjugateBeta, mul_pow, ← Complex.ofReal_pow,
        Real.sq_sqrt Coeff.phi_positive.le]
    have hs : star Coeff.conjugateBeta = -Coeff.conjugateBeta := by
      simp [Coeff.conjugateBeta]
    rw [ht]
    simp only [star_mul, star_pow, hs]
    have hj : rowExponent I j = 0 ∨ rowExponent I j = 1 := by
      unfold rowExponent; split_ifs <;> simp
    have hz : restExponent I z = 0 ∨ restExponent I z = 1 := by
      unfold restExponent; split_ifs <;> simp
    have hh := congrArg (fun a : ℂ =>
      (Coeff.conjugateBeta^rowExponent I i * Coeff.conjugateBeta^rowExponent I j *
        Coeff.nonphysical (cutCoefficient I (Coeff.branch T p Coeff.initial) i z) *
        star (Coeff.nonphysical (cutCoefficient I (Coeff.branch T p Coeff.initial) j z))) * a) hb
    rcases hj with hj | hj <;> rcases hz with hz | hz <;>
      simp only [hj,hz,Nat.zero_add,Nat.add_zero,show (1+1 : ℕ) = 2 by rfl,
        pow_zero,pow_one,neg_one_sq,mul_one,one_mul,neg_one_mul,neg_neg] at hh ⊢ <;>
      first | (solve | ring) | linear_combination -hh
  · simp [he]

/-- The actual same-cut determinant has quadratic integer coordinates, and
its other evaluation is the determinant of the exact signed embedded cut. -/
theorem original_event_cut_integer_coordinates {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) (I : Finset (Fin 16)) :
    (eventCut T I event).trace = (eventMass T (historyEvent event) : ℂ) ∧
    (eventCut T I event).det = (Coeff.realPhysical (cutDetCoordinates T I event) : ℂ) ∧
    (conjugateEventCut T I event).det =
      (Coeff.realConjugate (cutDetCoordinates T I event) : ℂ) ∧
    ∀ i j : CutBasis I, conjugateEventCut T I event i j =
      ∑ p, ∑ z : CutRest I, if event p then
        (-1 : ℂ)^(restExponent I z + rowExponent I j) *
        Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (i,z)) *
        star (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) ((splitAt I).symm (j,z)))
      else 0 :=
  ⟨eventCut_trace T I event, cut_det_physical T I event, cut_det_conjugate T I event,
    conjugateEventCut_signed T I event⟩

private theorem determinant_frobenius_bound {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hM : (∑ i, ∑ j, ‖M i j‖^2) ≤ R^2) :
    ‖M.det‖ ≤ R^Fintype.card n := by
  let G := Mᴴ * M
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have ht : (∑ i, hG.1.eigenvalues i) = ∑ i, ∑ j, ‖M i j‖^2 := by
    have hh := congrArg Complex.re hG.1.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] at hh
    rw [← hh]
    dsimp [G]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.star_def, Complex.conj_mul', Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_pow]
  have he (i : n) : hG.1.eigenvalues i ≤ R^2 :=
    (Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j) (Finset.mem_univ i)).trans
      (ht ▸ hM)
  have hd : ‖M.det‖^2 = ∏ i, hG.1.eigenvalues i := by
    have hh := congrArg Complex.re hG.1.det_eq_prod_eigenvalues
    simp only [G, Matrix.det_mul, Matrix.det_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re] at hh
    rw [← hh]
    simp [Complex.star_def, Complex.conj_mul', Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_pow]
  have hp := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => hG.eigenvalues_nonneg i)
    (fun i _ => he i)
  simp only [Finset.prod_const, Finset.card_univ] at hp
  rw [← hd, ← pow_mul, Nat.mul_comm 2, pow_mul] at hp
  exact (sq_le_sq₀ (norm_nonneg _) (pow_nonneg hR _)).mp hp

private theorem conjugate_cut_frobenius {L : Type} (T : NativeProtocolGraft.Tree L)
    (I : Finset (Fin 16)) (event : Path T → Bool) :
    (∑ i, ∑ j, ‖conjugateEventCut T I event i j‖^2) ≤
      (Coeff.treeEnergy T Coeff.initial)^2 := by
  classical
  let A (i : CutBasis I) (q : Path T × CutRest I) : ℂ :=
    Coeff.conjugateAmplitude (Coeff.branch T q.1 Coeff.initial) ((splitAt I).symm (i,q.2))
  have hb (i j : CutBasis I) : ‖conjugateEventCut T I event i j‖ ≤
      ∑ q : Path T × CutRest I, ‖A i q‖ * ‖A j q‖ := by
    rw [conjugateEventCut_signed, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z _ => ?_))
    by_cases he : event p
    · simp [he, norm_mul, norm_pow, A]
    · simp [he, mul_nonneg (norm_nonneg _) (norm_nonneg _)]
  have hs (i j : CutBasis I) : ‖conjugateEventCut T I event i j‖^2 ≤
      (∑ q, ‖A i q‖^2) * (∑ q, ‖A j q‖^2) :=
    (pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)
  have ht : (∑ i, ∑ q, ‖A i q‖^2) = Coeff.treeEnergy T Coeff.initial := by
    simp only [Fintype.sum_prod_type, A, Coeff.treeEnergy, Coeff.energy,
      Complex.normSq_eq_norm_sq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simpa only [Fintype.sum_prod_type] using (splitAt I).symm.sum_comp
      (fun z => ‖Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) z‖^2)
  calc
    _ ≤ ∑ i, ∑ j, (∑ q, ‖A i q‖^2) * (∑ q, ‖A j q‖^2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hs i j))
    _ = (∑ i, ∑ q, ‖A i q‖^2)^2 := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = _ := by rw [ht]

/-- The other embedding of the actual same-cut determinant has the sharp
resource exponent, using the complete original tree energy without path counts. -/
private theorem original_event_cut_conjugate_bound {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) (I : Finset (Fin 16)) :
    |Coeff.realConjugate (cutDetCoordinates T I event)| ≤
      Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I)) := by
  have hn : 0 ≤ Coeff.treeEnergy T Coeff.initial := by
    exact Finset.sum_nonneg (fun p _ =>
      Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _))
  have hd := determinant_frobenius_bound (conjugateEventCut T I event)
    (Coeff.treeEnergy T Coeff.initial) hn (conjugate_cut_frobenius T I event)
  rw [(original_event_cut_integer_coordinates T event I).2.2.1,
    Complex.norm_real, Real.norm_eq_abs] at hd
  exact hd.trans (by
    rw [pow_mul]
    exact pow_le_pow_left₀ hn (Coeff.original_branch_evaluations T).2 _)

private theorem determinant_le_eigenvalue {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (ht : A.trace.re ≤ 1) (i : n) :
    A.det.re ≤ hA.1.eigenvalues i := by
  have hs : (∑ j, hA.1.eigenvalues j) ≤ 1 := by
    have hh := congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] at hh
    rwa [← hh]
  have he (j : n) : hA.1.eigenvalues j ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ j)).trans hs
  have hd : A.det.re = ∏ j, hA.1.eigenvalues j := by
    have hh := congrArg Complex.re hA.1.det_eq_prod_eigenvalues
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod,
      Complex.ofReal_re] using hh
  rw [hd]
  simpa only [Finset.prod_singleton] using
    (Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.subset_univ ({i} : Finset n)) (fun j _ => hA.eigenvalues_nonneg j)
      (fun j _ _ => he j))

/-- Resource bounds for the same original acquired event and actual position
cut. Spectral assertions are conditional on positive mass and full actual rank. -/
theorem original_event_cut_resource_bounds {L : Type} (T : NativeProtocolGraft.Tree L)
    (event : Path T → Bool) (I : Finset (Fin 16)) :
    let Xi := eventCut T I event
    let p := eventMass T (historyEvent event)
    let K := Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I))
    let rho := ((p⁻¹ : ℝ) : ℂ) • Xi
    Xi.trace = (p : ℂ) ∧
    |Coeff.realConjugate (cutDetCoordinates T I event)| ≤ K ∧
    (0 < p → (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ p ∧
      (Xi.rank = Fintype.card (CutBasis I) →
        K⁻¹ ≤ Xi.det.re ∧
        ∃ hXi : Xi.IsHermitian, ∃ hRho : rho.IsHermitian,
          K⁻¹ ≤ iInf hXi.eigenvalues ∧ K⁻¹/p ≤ iInf hRho.eigenvalues)) := by
  classical
  dsimp only
  have hborn := original_complete_born_law T event I
  have hXi := hborn.2.2.1
  have hconj := original_event_cut_conjugate_bound T event I
  refine ⟨hborn.2.2.2,hconj,?_⟩
  intro hp
  refine ⟨(original_event_resource_bounds T (historyEvent event)).1 hp,?_⟩
  intro hfull
  have hu : IsUnit (eventCut T I event) := Matrix.mulVec_surjective_iff_isUnit.mp
    (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hfull)
  have hdpos : 0 < (eventCut T I event).det.re :=
    (RCLike.pos_iff.mp (hXi.posDef_iff_isUnit.mpr hu).det_pos).1
  have hcoord : Coeff.realPhysical (cutDetCoordinates T I event) =
      (eventCut T I event).det.re := by
    have hh := congrArg Complex.re (original_event_cut_integer_coordinates T event I).2.1
    simpa only [Complex.ofReal_re] using hh.symm
  have hK : 0 < Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I)) :=
    pow_pos (lt_of_lt_of_le zero_lt_one Coeff.kappa_one) _
  have hdlo : (Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I)))⁻¹ ≤
      (eventCut T I event).det.re := by
    rw [← hcoord]
    exact Coeff.positive_lower _ _ hK (hcoord.symm ▸ hdpos) hconj
  have ht : (eventCut T I event).trace.re ≤ 1 := by
    rw [hborn.2.2.2, Complex.ofReal_re]
    exact hborn.2.1.2
  have he (i : CutBasis I) :
      (Coeff.kappa^(2*maxCalls T*Fintype.card (CutBasis I)))⁻¹ ≤ hXi.1.eigenvalues i :=
    hdlo.trans (determinant_le_eigenvalue _ hXi ht i)
  have hRho : ((((eventMass T (historyEvent event))⁻¹ : ℝ) : ℂ) •
      eventCut T I event).IsHermitian :=
    (hXi.smul (show (0 : ℂ) ≤ (((eventMass T (historyEvent event))⁻¹ : ℝ) : ℂ) by
      exact_mod_cast (inv_nonneg.mpr hp.le))).1
  refine ⟨hdlo,hXi.1,hRho,le_ciInf he,?_⟩
  apply le_ciInf
  intro i
  have hscale : hRho.eigenvalues i =
      (eventMass T (historyEvent event))⁻¹ * hXi.1.eigenvalues i := by
    exact D5.S3.Quantum.Matrix.LinGProperty.eigenvalues_zero_smul_finite _ hXi.1 _
      (inv_nonneg.mpr hp.le) hRho _
  rw [hscale]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (he i) (inv_nonneg.mpr hp.le)

#print axioms original_event_cut_resource_bounds

#print axioms original_event_cut_conjugate_bound

#print axioms original_event_cut_integer_coordinates

#print axioms original_complete_born_law
end D5.S3.Quantum.Dynamics.NativeProtocolBornNormalization
