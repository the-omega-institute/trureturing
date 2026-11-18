/- GID: D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite coordinate transport for the original twisted half-current oscillator. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Binomial

/-! The original lowering operator and its half-current transport in formal order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

open LatticeGeneratingFieldLocality LatticeHalfFock MvPolynomial
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open TwistedGround.OriginalFourMChargeCoset (oscillatorLower)
open LatticeHalfFockChargedCoefficients (omega)
open private L_zero_of_homogeneous_int halfEnergy_eq_signedOddWeight_half from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero

private abbrev End (D : LatticeData) := Module.End ℂ (Oscillator D)

private def adjoint (D : LatticeData) : Module.End ℂ (End D) :=
  LinearMap.mulLeft ℂ (oscillatorLower D) - LinearMap.mulRight ℂ (oscillatorLower D)

private theorem choose_step (z : ℂ) (n : ℕ) :
    (n+1 : ℂ) * Ring.choose z (n+1) = (z-(n:ℂ)) * Ring.choose z n := by
  have h := Ring.choose_smul_choose z (by omega : n ≤ n+1)
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul, mul_comm] using h

private theorem adjoint_current (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : ℤ) (n : ℕ) :
    (adjoint D ^ n) (current D i j) =
      ((n.factorial : ℂ) * Ring.choose (-frequency j) n) • current D i (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul]
    have h : adjoint D (current D i (j+n)) =
        -frequency (j+n) • current D i (1+(j+n)) :=
      L_current_commutator D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) i 1 (j+n)
    rw [h, smul_smul, show 1+(j+(n:ℤ)) = j+((n+1:ℕ):ℤ) by omega]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      show -frequency (j+n) = -frequency j - (n:ℂ) by
        simp only [frequency, Int.cast_add, Int.cast_natCast]; ring]
    linear_combination -(n.factorial : ℂ) * choose_step (-frequency j) n

/-- The ordinary coefficient of the formal lowering flow on a current applied
to an arbitrary oscillator polynomial. -/
theorem lowering_current_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : ℤ) (n : ℕ) (f : Oscillator D) :
    (n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n) (current D i j f) =
      ∑ k ∈ Finset.range (n+1),
        (Ring.choose (-frequency j) k * ((n-k).factorial : ℂ)⁻¹) •
          current D i (j+k) ((oscillatorLower D ^ (n-k)) f) := by
  let R : Module.End ℂ (End D) := LinearMap.mulRight ℂ (oscillatorLower D)
  let S : Module.End ℂ (End D) := LinearMap.mulLeft ℂ (oscillatorLower D)
  have hc : Commute (adjoint D) R :=
    (LinearMap.commute_mulLeft_right (R := ℂ) (oscillatorLower D) (oscillatorLower D)).sub_left
      (Commute.refl R)
  have hs : adjoint D + R = S := sub_add_cancel _ _
  have exp := congrArg (fun A : Module.End ℂ (End D) => A (current D i j)) (hc.add_pow n)
  rw [hs] at exp
  have exp' := congrArg (fun A : End D => A f) exp
  simp only [S, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply,
    Module.End.mul_apply, LinearMap.sum_apply] at exp'
  rw [exp', Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have commute : Commute (adjoint D ^ k) (R ^ (n-k)) := (hc.pow_left k).pow_right (n-k)
  have step :
      (adjoint D ^ k) ((R ^ (n-k)) ((n.choose k : Module.End ℂ (End D))
        (current D i j))) f =
      ((n.choose k : ℂ) * (k.factorial : ℂ) * Ring.choose (-frequency j) k) •
        current D i (j+k) ((oscillatorLower D ^ (n-k)) f) := by
    rw [← Module.End.mul_apply, commute.eq, Module.End.mul_apply]
    simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, map_smul,
      adjoint_current D hu, R, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.smul_apply, smul_smul, Module.End.mul_apply]
    ring_nf
  rw [step, smul_smul, Nat.cast_choose ℂ hk']
  congr 1
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hm : ((n-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
  field_simp


/-- The lowering flow, considered coefficientwise on the algebraic oscillator. -/
def loweringFlow (D : LatticeData) : PowerSeries (End D) :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ • oscillatorLower D ^ n

/-- The mode expansion of the conjugated current for the unit-scale map. -/
def transportedCurrent (D : LatticeData) (i : Fin D.rank) (j : ℤ) :
    PowerSeries (End D) :=
  PowerSeries.mk fun n => Ring.choose (-frequency j) n • current D i (j+n)

theorem lowering_flow_intertwines (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : ℤ) :
    loweringFlow D * PowerSeries.C (current D i j) =
      transportedCurrent D i j * loweringFlow D := by
  apply PowerSeries.ext
  intro n
  apply LinearMap.ext
  intro f
  rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [loweringFlow, transportedCurrent, PowerSeries.coeff_mk, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul, mul_comm] using
      lowering_current_coefficient D hu i j n f

private theorem lower_vacuum (D : LatticeData) : oscillatorLower D 1 = 0 := by
  simpa [oscillatorLower, L] using rawL_ground_nonnegative D (actualInverse D) 1 (by omega)

/-- The creation part of a transported creation mode. -/
def creationPart (D : LatticeData) (x : Index D) : PowerSeries (End D) :=
  PowerSeries.mk fun k => if k ≤ x.2 then
    Ring.choose ((x.2 : ℂ)+1/2) k • current D x.1 ((k : ℤ)-x.2-1) else 0

/-- The annihilation part of a transported creation mode. -/
def annihilationPart (D : LatticeData) (x : Index D) : PowerSeries (End D) :=
  PowerSeries.mk fun k => if x.2 < k then
    Ring.choose ((x.2 : ℂ)+1/2) k • current D x.1 ((k : ℤ)-x.2-1) else 0

private theorem current_split (D : LatticeData) (x : Index D) :
    transportedCurrent D x.1 (-(x.2 : ℤ)-1) =
      creationPart D x + annihilationPart D x := by
  apply PowerSeries.ext
  intro n
  have hf : -frequency (-(x.2 : ℤ)-1) = (x.2 : ℂ)+1/2 := by
    simp only [frequency, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
    ring
  have hj : -(x.2 : ℤ)-1+n = (n : ℤ)-x.2-1 := by omega
  simp only [map_add, transportedCurrent, creationPart, annihilationPart,
    PowerSeries.coeff_mk, hf, hj]
  by_cases h : n ≤ x.2
  · simp [h, show ¬ x.2 < n by omega]
  · simp [h, show x.2 < n by omega]

/-- The scalar of the regular pair contraction, with the parameter power
recorded in formal order `p+q+1`. -/
def contractionScalar (p q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (q+1),
    ((n : ℂ)+1/2) * Ring.choose ((p : ℂ)+1/2) (p+n+1) *
      Ring.choose ((q : ℂ)+1/2) (q-n)

/-- The central operator of a contracted pair on the original oscillator. -/
def contraction (D : LatticeData) (x y : Index D) : PowerSeries (End D) :=
  PowerSeries.monomial (x.2+y.2+1)
    (((D.G x.1 y.1 : ℂ) * contractionScalar x.2 y.2) • 1)

private theorem summand_bracket (D : LatticeData) (x y : Index D) (k l : ℕ) :
    PowerSeries.coeff k (annihilationPart D x) * PowerSeries.coeff l (creationPart D y) -
      PowerSeries.coeff l (creationPart D y) * PowerSeries.coeff k (annihilationPart D x) =
      if x.2 < k ∧ l ≤ y.2 ∧ k+l = x.2+y.2+1 then
        (Ring.choose ((x.2 : ℂ)+1/2) k * Ring.choose ((y.2 : ℂ)+1/2) l *
          (frequency ((k : ℤ)-x.2-1) * (D.G x.1 y.1 : ℂ))) • 1 else 0 := by
  simp only [creationPart, annihilationPart, PowerSeries.coeff_mk]
  by_cases hk : x.2 < k <;> by_cases hl : l ≤ y.2 <;> simp only [hk, hl, true_and,
    false_and, ite_true, ite_false, mul_zero, zero_mul, sub_zero]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm (Ring.choose ((y.2 : ℂ)+1/2) l),
    ← smul_sub, current_heisenberg]
  have h : (k:ℤ)-x.2-1 + ((l:ℤ)-y.2-1) + 1 = 0 ↔ k+l = x.2+y.2+1 := by omega
  by_cases hz : k+l = x.2+y.2+1
  · simp [hz, h.mpr hz, smul_smul]
  · have hn : ¬ ((k:ℤ)-x.2-1 + ((l:ℤ)-y.2-1) + 1 = 0) := fun he => hz (h.mp he)
    rw [if_neg hn, if_neg hz, zero_smul, smul_zero]

theorem annihilation_creation_contraction (D : LatticeData) (x y : Index D) :
    annihilationPart D x * creationPart D y - creationPart D y * annihilationPart D x =
      contraction D x y := by
  apply PowerSeries.ext
  intro n
  rw [map_sub, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_lhs =>
    congr
    · skip
    · rw [← Finset.Nat.sum_antidiagonal_swap]
  rw [← Finset.sum_sub_distrib, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [contraction, PowerSeries.coeff_monomial, Prod.fst_swap, Prod.snd_swap,
    Nat.succ_eq_add_one]
  by_cases hn : n = x.2+y.2+1
  · rw [if_pos hn, hn, show x.2 + y.2 + 1 + 1 = (x.2+1)+(y.2+1) by omega,
      Finset.sum_range_add]
    have hz : (∑ k ∈ Finset.range (x.2+1),
        (PowerSeries.coeff k (annihilationPart D x) *
            PowerSeries.coeff (x.2+y.2+1-k) (creationPart D y) -
          PowerSeries.coeff (x.2+y.2+1-k) (creationPart D y) *
            PowerSeries.coeff k (annihilationPart D x))) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [summand_bracket, if_neg]
        have := Finset.mem_range.mp hk
        omega
    rw [hz, zero_add, contractionScalar, Finset.mul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hdiff : x.2+y.2+1-(x.2+1+k) = y.2-k := by omega
    rw [summand_bracket, hdiff, if_pos (by omega)]
    have hf : frequency ((↑(x.2+1+k) : ℤ)-x.2-1) = (k:ℂ)+1/2 := by
      rw [show (↑(x.2+1+k) : ℤ)-x.2-1 = (k:ℤ) by omega]
      simp [frequency]
    rw [hf, show x.2+1+k = x.2+k+1 by omega]
    congr 1
    ring
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro k hk
    rw [summand_bracket, if_neg]
    have := Finset.mem_range.mp hk
    omega


private theorem lower_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Oscillator D) (z : ℤ)
    (hf : L D (actualInverse D) 0 f = ((D.rank : ℂ)/16+(z:ℂ)/2) • f)
    (n : ℕ) :
    L D (actualInverse D) 0 ((oscillatorLower D ^ n) f) =
      ((D.rank : ℂ)/16+((z:ℂ)-2*(n:ℂ))/2) • (oscillatorLower D ^ n) f := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := LinearMap.congr_fun
      (L_virasoro D (actualInverse D) (actualInverse_left D hu) (actualInverse_right D hu) 0 1)
      ((oscillatorLower D ^ n) f)
    change
      (L D (actualInverse D) 0 * oscillatorLower D -
        oscillatorLower D * L D (actualInverse D) 0) ((oscillatorLower D ^ n) f) =
      _ at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ih, map_smul] at h
    norm_num [oscillatorLower] at h
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ]
    unfold oscillatorLower
    linear_combination (norm := module) h

private theorem negative_oscillator_eigen (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Oscillator D) (z : ℤ) (hz : z < 0)
    (hf : L D (actualInverse D) 0 f = ((D.rank : ℂ)/16+(z:ℂ)/2) • f) :
    f = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  change f.coeff d = lcoeff ℂ d (0 : Oscillator D)
  rw [map_zero]
  have h := congrArg (fun f : Oscillator D => f.coeff d) hf
  change (L D (actualInverse D) 0 f).coeff d = _ at h
  have hcoeff : (L D (actualInverse D) 0 f).coeff d =
      ((D.rank : ℂ)/16+
        ((Finsupp.weight (fun x => (omega D x : ℤ)) d : ℤ) : ℂ)/2) *
        f.coeff d := by
    conv_lhs => rw [MvPolynomial.as_sum f, map_sum, coeff_sum]
    simp only [L_zero_monomial_coeff D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu), halfEnergy_eq_signedOddWeight_half,
      coeff_smul, smul_eq_mul, coeff_monomial]
    by_cases hd : d ∈ f.support
    · rw [Finset.sum_eq_single_of_mem d hd]
      · simp
      · intro e _ he
        simp [he]
    · have hzero := notMem_support_iff.mp hd
      rw [hzero, mul_zero]
      apply Finset.sum_eq_zero
      intro e he
      have hne : d ≠ e := fun h => hd (h ▸ he)
      simp [Ne.symm hne]
  rw [hcoeff, coeff_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h
  have hweight := Finsupp.weight_apply (fun x => (omega D x : ℤ)) d
  have hnonneg : 0 ≤ Finsupp.weight (fun x => (omega D x : ℤ)) d := by
    rw [hweight, Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hgap : (D.rank : ℂ)/16 +
      ((Finsupp.weight (fun x => (omega D x : ℤ)) d : ℤ) : ℂ)/2 -
      ((D.rank : ℂ)/16+(z:ℂ)/2) ≠ 0 := by
    intro he
    have hc : ((Finsupp.weight (fun x => (omega D x : ℤ)) d : ℤ) : ℂ) = (z:ℂ) := by
      linear_combination 2*he
    have hi : Finsupp.weight (fun x => (omega D x : ℤ)) d = z := by exact_mod_cast hc
    omega
  simpa using (mul_eq_zero.mp h).resolve_left hgap

/-- The actual lowering mode drops two units of doubled oscillator energy.
This is the nonnegative-energy cutoff, including odd energy and the vacuum. -/
theorem lowering_after_energy_cutoff (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Oscillator D) (z : ℤ)
    (hf : IsWeightedHomogeneous (fun x => (omega D x : ℤ)) f z)
    (n : ℕ) (hn : z < 2*(n:ℤ)) :
    (oscillatorLower D ^ n) f = 0 := by
  have h := lower_eigen D hu f z
    (L_zero_of_homogeneous_int D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu) f z hf) n
  apply negative_oscillator_eigen D hu _ (z-2*(n:ℤ)) (by omega)
  push_cast
  exact h


private abbrev OperatorSeries (D : LatticeData) := PowerSeries (End D)

private def vacuumProjection (D : LatticeData) : End D :=
  (show Oscillator D →ₗ[ℂ] ℂ from
    { toFun := constantCoeff
      map_add' := map_add constantCoeff
      map_smul' := constantCoeff_smul }).smulRight 1

private theorem vacuumProjection_apply (D : LatticeData) (f : Oscillator D) :
    vacuumProjection D f = f.constantCoeff • (1 : Oscillator D) := rfl

private def vacuum (D : LatticeData) : OperatorSeries D :=
  PowerSeries.C (vacuumProjection D)

private theorem lowering_vacuum (D : LatticeData) :
    loweringFlow D * vacuum D = vacuum D := by
  apply PowerSeries.ext
  intro n
  apply LinearMap.ext
  intro f
  rw [vacuum, PowerSeries.coeff_mul_C, loweringFlow, PowerSeries.coeff_mk]
  cases n with
  | zero => simp
  | succ n =>
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, LinearMap.zero_apply,
      LinearMap.smul_apply, Module.End.mul_apply, vacuumProjection_apply, map_smul]
    rw [pow_succ, Module.End.mul_apply, lower_vacuum, map_zero, smul_zero, smul_zero]

private theorem annihilation_vacuum (D : LatticeData) (x : Index D) :
    annihilationPart D x * vacuum D = 0 := by
  apply PowerSeries.ext
  intro k
  apply LinearMap.ext
  intro f
  rw [vacuum, PowerSeries.coeff_mul_C, map_zero, annihilationPart, PowerSeries.coeff_mk]
  split_ifs with hk
  · simp only [LinearMap.smul_apply, Module.End.mul_apply, vacuumProjection_apply, map_smul]
    rw [current_vanish D x.1 (1 : Oscillator D) _ (by simp; omega), smul_zero, smul_zero,
      LinearMap.zero_apply]
  · simp

private theorem annihilation_commutes (D : LatticeData) (x y : Index D) :
    Commute (annihilationPart D x) (annihilationPart D y) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Prod.fst_swap, Prod.snd_swap, annihilationPart, PowerSeries.coeff_mk]
  split_ifs with hx hy hy
  · have h := current_heisenberg D x.1 y.1 ((k.1:ℤ)-x.2-1) ((k.2:ℤ)-y.2-1)
    rw [if_neg (by omega), zero_smul, sub_eq_zero] at h
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, h]
    rw [mul_comm (Ring.choose ((x.2:ℂ)+1/2) k.1)]
  all_goals simp

private theorem contraction_central (D : LatticeData) (x y : Index D)
    (F : OperatorSeries D) : Commute (contraction D x y) F := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  apply Finset.sum_congr rfl
  intro k _
  simp only [contraction, PowerSeries.coeff_monomial, Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

private def transformed (D : LatticeData) (x : Index D) :=
  transportedCurrent D x.1 (-(x.2 : ℤ)-1)

private theorem annihilation_transformed (D : LatticeData) (x y : Index D) :
    annihilationPart D x * transformed D y =
      transformed D y * annihilationPart D x + contraction D x y := by
  rw [transformed, current_split, mul_add, add_mul, (annihilation_commutes D x y).eq]
  have h := annihilation_creation_contraction D x y
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

private def transformedWord (D : LatticeData) (xs : List (Index D)) : OperatorSeries D :=
  (xs.map (transformed D)).prod

private theorem contract_word (D : LatticeData) (x : Index D) (xs : List (Index D)) :
    annihilationPart D x * (transformedWord D xs * vacuum D) =
      ∑ j : Fin xs.length,
        contraction D x (xs.get j) * (transformedWord D (xs.eraseIdx j) * vacuum D) := by
  induction xs with
  | nil => simpa [transformedWord] using annihilation_vacuum D x
  | cons y ys ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, transformedWord, List.map_cons,
      List.prod_cons, List.get_cons_zero, List.get_cons_succ', Fin.val_zero,
      Fin.val_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] at *
    rw [mul_assoc (transformed D y), ← mul_assoc (annihilationPart D x),
      annihilation_transformed, add_mul, mul_assoc (transformed D y), ih, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc (transformed D y), (contraction_central D x (ys.get j) _).eq.symm,
      mul_assoc (contraction D x (ys.get j)), mul_assoc (transformed D y)]

/-- Sum over partial matchings of a word of modes. The first slot is either
unpaired or paired with one later slot. Distinct slots retain their own
multiplicities, including repeated oscillator modes. -/
def normalOrder (D : LatticeData) : List (Index D) → OperatorSeries D
  | [] => vacuum D
  | x :: xs => creationPart D x * normalOrder D xs +
      ∑ j : Fin xs.length,
        contraction D x (xs.get j) * normalOrder D (xs.eraseIdx j)
termination_by xs => xs.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem transformed_word_normal (D : LatticeData) (xs : List (Index D)) :
    transformedWord D xs * vacuum D = normalOrder D xs := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [transformedWord, normalOrder]
    | cons x xs =>
      rw [normalOrder]
      change (transformed D x * transformedWord D xs) * vacuum D = _
      rw [mul_assoc, show transformed D x = creationPart D x + annihilationPart D x from
        current_split D x, add_mul, contract_word, ih xs (Nat.lt_succ_self _)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih _ (by exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..))]

private theorem flow_word (D : LatticeData) (hu : IsUnit D.G.det) (xs : List (Index D)) :
    loweringFlow D * ((xs.map (fun x => PowerSeries.C
      (LinearMap.mulLeft ℂ (X x : Oscillator D)))).prod * vacuum D) =
      transformedWord D xs * vacuum D := by
  induction xs with
  | nil => simpa [transformedWord] using lowering_vacuum D
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, transformedWord] at *
    rw [← mul_assoc _ _ (vacuum D), ← mul_assoc (loweringFlow D), ← current_negative D x.1 x.2,
      lowering_flow_intertwines D hu]
    simp only [mul_assoc]
    rw [ih]
    rfl

private theorem original_word_apply (D : LatticeData) (xs : List (Index D)) :
    ((xs.map (fun x => LinearMap.mulLeft ℂ (X x : Oscillator D))).prod *
      vacuumProjection D) (1 : Oscillator D) =
      (xs.map (fun x => (X x : Oscillator D))).prod := by
  induction xs with
  | nil => simp [vacuumProjection_apply]
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_assoc,
      Module.End.mul_apply, ih, LinearMap.mulLeft_apply]

/-- Every coefficient of the original lowering action on a creation word,
with all unpaired creators and all ordinary-coefficient contractions. -/
theorem lowering_normal_order_word (D : LatticeData) (hu : IsUnit D.G.det)
    (xs : List (Index D)) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n)
      ((xs.map (fun x => (X x : Oscillator D))).prod) =
      PowerSeries.coeff n (normalOrder D xs) (1 : Oscillator D) := by
  have h := congrArg (fun S : OperatorSeries D =>
    PowerSeries.coeff n S (1 : Oscillator D)) (flow_word D hu xs)
  rw [transformed_word_normal] at h
  have hp := List.prod_hom (xs.map fun x => LinearMap.mulLeft ℂ (X x : Oscillator D))
    (PowerSeries.C (R := End D))
  rw [List.map_map] at hp
  change (xs.map (fun x => PowerSeries.C (LinearMap.mulLeft ℂ (X x : Oscillator D)))).prod = _ at hp
  rw [hp, vacuum, ← map_mul] at h
  change PowerSeries.coeff n (loweringFlow D * PowerSeries.C
      ((xs.map fun x => LinearMap.mulLeft ℂ (X x : Oscillator D)).prod *
        vacuumProjection D)) (1 : Oscillator D) = _ at h
  rw [PowerSeries.coeff_mul_C, loweringFlow, PowerSeries.coeff_mk] at h
  change (n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n)
    (((xs.map fun x => LinearMap.mulLeft ℂ (X x : Oscillator D)).prod *
      vacuumProjection D) (1 : Oscillator D)) = _ at h
  rw [original_word_apply] at h
  exact h


/-- Half-integral mode scale with a specified lift of the nonzero base scale. -/
def modeScale (root lambda : ℂ) (j : ℤ) : ℂ :=
  root * lambda ^ (-j-1)

private theorem scale_opposites (root lambda : ℂ) (hroot : root^2 = lambda)
    (hlambda : lambda ≠ 0) (n : ℤ) :
    modeScale root lambda n * modeScale root lambda (-n-1) = 1 := by
  unfold modeScale
  rw [show -(-n-1)-1 = n by omega]
  calc
    root * lambda ^ (-n-1) * (root * lambda ^ n) =
        root^2 * (lambda ^ (-n-1) * lambda ^ n) := by ring
    _ = 1 := by
      rw [hroot, ← zpow_add₀ hlambda, show -n-1+n = -1 by omega, zpow_neg_one,
        mul_inv_cancel₀ hlambda]

/-- The half-coordinate scale cancels at every matched positive-negative
frequency. The chosen lift is part of the data. -/
theorem scaled_contraction_term (root lambda : ℂ) (hroot : root^2 = lambda)
    (hlambda : lambda ≠ 0) (eta : ℂ) (p q n : ℕ) (hn : n ≤ q) :
    (eta^(p+n+1) * Ring.choose ((p:ℂ)+1/2) (p+n+1) *
      modeScale root lambda n) *
    (eta^(q-n) * Ring.choose ((q:ℂ)+1/2) (q-n) *
      modeScale root lambda (-(n:ℤ)-1)) * ((n:ℂ)+1/2) =
    eta^(p+q+1) * (((n:ℂ)+1/2) * Ring.choose ((p:ℂ)+1/2) (p+n+1) *
      Ring.choose ((q:ℂ)+1/2) (q-n)) := by
  calc
    _ = (eta^(p+n+1)*eta^(q-n)) *
          (modeScale root lambda n * modeScale root lambda (-(n:ℤ)-1)) *
          (((n:ℂ)+1/2) * Ring.choose ((p:ℂ)+1/2) (p+n+1) *
            Ring.choose ((q:ℂ)+1/2) (q-n)) := by ring
    _ = _ := by rw [scale_opposites root lambda hroot hlambda, mul_one, ← pow_add,
      show p+n+1+(q-n) = p+q+1 by omega]

/-- The normalized binomial series for `(1-eta*u)^a`. -/
def unitPower (eta a : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (-eta)^n * Ring.choose a n

private theorem binomial_reflection (a : ℂ) (k : ℕ) :
    (-1:ℂ)^k * Ring.choose a k = Ring.choose (-a+(k:ℂ)-1) k := by
  have h := Ring.choose_neg (-a) k
  rw [neg_neg] at h
  rw [h]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- The ordinary nonnegative coefficient extracted in the (v)-inner chamber.
The undressed term has no such coefficient in the outer variable. In the
dressed term with index `n`, the two coefficient indices are `p+n+1` and
`q-n`, and the inner power `v^n` restricts the sum to `n ≤ q`. -/
def chamberCoefficient (eta : ℂ) (p q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (q+1), ((n:ℂ)+1/2) *
    PowerSeries.coeff (p+n+1) (unitPower eta ((n:ℂ)-1/2)) *
    PowerSeries.coeff (q-n) (unitPower eta (-(n:ℂ)-3/2))

/-- The two reexpanded chamber binomials give precisely the contraction
coefficient in the original oscillator. -/
theorem chamber_coefficient_eq_contraction (eta : ℂ) (p q : ℕ) :
    chamberCoefficient eta p q = eta^(p+q+1) * contractionScalar p q := by
  unfold chamberCoefficient contractionScalar
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ q := by simpa using hn
  simp only [unitPower, PowerSeries.coeff_mk]
  have cf (a : ℂ) (k : ℕ) : (-eta)^k * Ring.choose a k =
      eta^k * Ring.choose (-a+(k:ℂ)-1) k := by
    rw [show -eta = eta*(-1) by ring, mul_pow, mul_assoc, binomial_reflection]
  rw [cf, cf, show -((n:ℂ)-1/2) + ((p+n+1:ℕ):ℂ)-1 = (p:ℂ)+1/2 by
      push_cast; ring,
    show -(-(n:ℂ)-3/2) + ((q-n:ℕ):ℂ)-1 = (q:ℂ)+1/2 by
      rw [Nat.cast_sub hn']; ring,
    ← show p+n+1+(q-n) = p+q+1 by omega, pow_add]
  ring

/-- Rational identity for the local Cauchy correction with the specified
half-coordinate roots. The expression on the right also extends across the
diagonal whenever the two roots and their sum are nonzero. -/
theorem regular_cauchy_correction (eta lambda root u v b c : ℂ)
    (hroot : root^2 = lambda) (hlambda : lambda ≠ 0)
    (hb : b^2 = 1-eta*u) (hc : c^2 = 1-eta*v)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b+c ≠ 0) (huv : u ≠ v) :
    (root / b^3) * (root / c^3) *
      ((lambda*u/b^2 + lambda*v/c^2) /
        (2*(lambda*u/b^2-lambda*v/c^2)^2)) -
      (u+v)/(2*(u-v)^2) = eta*(1+b*c)/(2*b*c*(b+c)^2) := by
  have hd : u*c^2-v*b^2 = u-v := by rw [hc, hb]; ring
  have hv : lambda*u/b^2-lambda*v/c^2 = lambda*(u-v)/(b^2*c^2) := by
    field_simp
    linear_combination hd
  have hdifference : (c-b)*(b+c) = eta*(u-v) := by
    linear_combination hc - hb
  have hnumerator : (u*c-v*b)*(b+c) = (u-v)*(1+b*c) := by
    rw [show (u*c-v*b)*(b+c) = (u-v)*(b*c+c^2) + v*((c-b)*(b+c)) by ring,
      hdifference, hc]
    ring
  have hfirst : (root / b^3) * (root / c^3) *
      ((lambda*u/b^2 + lambda*v/c^2) /
        (2*(lambda*u/b^2-lambda*v/c^2)^2)) -
      (u+v)/(2*(u-v)^2) = ((c-b)*(u*c-v*b))/(2*b*c*(u-v)^2) := by
    rw [hv]
    have hd0 := sub_ne_zero.mpr huv
    have hlift : root / b^3 * (root / c^3) = lambda / (b^3*c^3) := by
      field_simp
      linear_combination hroot
    rw [hlift]
    field_simp
    ring
  rw [hfirst,
    show c-b = eta*(u-v)/(b+c) by apply (eq_div_iff hbc).mpr; exact hdifference,
    show u*c-v*b = (u-v)*(1+b*c)/(b+c) by apply (eq_div_iff hbc).mpr; exact hnumerator]
  have hd0 := sub_ne_zero.mpr huv
  field_simp


private def monomialWord {D : LatticeData} (d : Index D →₀ ℕ) : List (Index D) :=
  d.support.toList.flatMap fun x => List.replicate (d x) x

private theorem monomialWord_prod {D : LatticeData} (d : Index D →₀ ℕ) :
    ((monomialWord d).map (fun x => (X x : Oscillator D))).prod = monomial d 1 := by
  have h (xs : List (Index D)) :
      ((xs.flatMap fun x => List.replicate (d x) x).map (fun x =>
        (X x : Oscillator D))).prod = (xs.map fun x => (X x : Oscillator D) ^ d x).prod := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
        List.prod_replicate, List.map_cons, List.prod_cons, ih]
  rw [monomialWord, h, Finset.prod_map_toList, prod_X_pow_eq_monomial]

/-- The normal-order coefficient of any original oscillator polynomial.
The outer sum is its actual finite support in the oscillator monomial basis. -/
def polynomialCoefficient (D : LatticeData) (f : Oscillator D) (n : ℕ) : Oscillator D :=
  ∑ d ∈ f.support, f.coeff d •
    PowerSeries.coeff n (normalOrder D (monomialWord d)) (1 : Oscillator D)

/-- Identifies the coefficient of every occupation polynomial with the actual
factorial-normalized power of the lowering operator. -/
theorem lowering_normal_order (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Oscillator D) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n) f =
      polynomialCoefficient D f n := by
  unfold polynomialCoefficient
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (f.coeff d) = f.coeff d • monomial d (1:ℂ) by
    rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_comm,
    ← monomialWord_prod, lowering_normal_order_word D hu]

/-- Evaluating the formally normally ordered coefficients at any finite
cutoff gives the original finite lowering sum. -/
theorem lowering_normal_order_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (f : Oscillator D) (eta : ℂ) (cutoff : ℕ) :
    (∑ n ∈ Finset.range cutoff,
        (eta^n / (n.factorial : ℂ)) • (oscillatorLower D ^ n) f) =
      ∑ n ∈ Finset.range cutoff, eta^n • polynomialCoefficient D f n := by
  apply Finset.sum_congr rfl
  intro n _
  rw [← lowering_normal_order D hu, smul_smul, div_eq_mul_inv]

open TwistedGround.OriginalFourMChargeCoset (oscillatorKernel oscillatorCorrected)
open SignedOscillatorWick (wick)

/-- Both lowering factors in the original four-point oscillator kernel can
be read as normally ordered coefficients with their original ranges and
field exponents. -/
theorem oscillator_kernel_normal_order (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k : ℤ) (a : Charge D) (p P Q : Oscillator D) :
    oscillatorKernel D hu H K k a p P Q =
      ∑ i ∈ Finset.range (K-1), ∑ j ∈ Finset.range (H-1),
        let s : ℤ := k+1-(i : ℤ)-2*(H : ℤ)+(j : ℤ)
        (-1 : ℂ)^((H : ℤ)+s) *
          wick D (polynomialCoefficient D Q i)
            (oscillatorCorrected D hu a (2*s) p (polynomialCoefficient D P j)) := by
  unfold oscillatorKernel
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [← lowering_normal_order D hu, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv, mul_inv]
  ring


/-- Each monomial has finite doubled energy, so the largest energy on the
original finite support gives a cutoff even for inhomogeneous input. -/
theorem exists_lowering_cutoff (D : LatticeData) (hu : IsUnit D.G.det) (f : Oscillator D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (oscillatorLower D ^ n) f = 0 := by
  let w := fun d : Index D →₀ ℕ => Finsupp.weight (omega D) d
  refine ⟨f.support.sup w / 2 + 1, fun n hn => ?_⟩
  conv_lhs => rw [MvPolynomial.as_sum f, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hle : w d ≤ f.support.sup w := Finset.le_sup hd
  have hlt : (w d : ℤ) < 2*(n:ℤ) := by omega
  have hw : Finsupp.weight (fun x => (omega D x : ℤ)) d = (w d : ℤ) := by
    simp only [w, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Int.cast_id,
      Int.natCast_mul]
    push_cast
    rfl
  exact lowering_after_energy_cutoff D hu _ _ (isWeightedHomogeneous_monomial _ _ _ hw) n hlt

open LatticeActualAnnihilation

/-- Diagonal scale on the actual oscillator polynomial algebra. -/
def scaleOscillator (D : LatticeData) (root lambda : ℂ) : Oscillator D →ₐ[ℂ] Oscillator D :=
  MvPolynomial.aeval fun x : Index D =>
    modeScale root lambda (-(x.2 : ℤ)-1) • (X x : Oscillator D)

private theorem positive_scale (D : LatticeData) (root lambda : ℂ)
    (i : Fin D.rank) (k : ℕ) (f : Oscillator D) :
    annihilate D i k (scaleOscillator D root lambda f) =
      modeScale root lambda (-(k:ℤ)-1) • scaleOscillator D root lambda (annihilate D i k f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : annihilate D i k (MvPolynomial.C a) = 0 := by
      rw [← annihilation_apply]
      exact (annihilationDerivation D i k).map_algebraMap a
    rw [show scaleOscillator D root lambda (MvPolynomial.C a) = MvPolynomial.C a by
      simp [scaleOscillator], h, map_zero, smul_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    rcases x with ⟨j,l⟩
    let S := scaleOscillator D root lambda
    let a := modeScale root lambda (-(k:ℤ)-1)
    let b := modeScale root lambda (-(l:ℤ)-1)
    have hx : S (X (j,l)) = b • X (j,l) := by simp [S, b, scaleOscillator]
    rw [map_mul, hx, annihilate_mul, map_smul, hp, annihilate_mul, map_add,
      map_mul, map_mul, hx, smul_add]
    rw [annihilate_X]
    by_cases h : k = l
    · subst l
      simp only [ite_true, map_smul, map_one, mul_smul_comm, smul_mul_assoc]
      rw [smul_comm b a]
    · simp only [if_neg h, smul_zero, map_zero, mul_zero, add_zero, mul_smul_comm,
        smul_mul_assoc]
      rw [smul_comm b a]

private theorem scale_current (D : LatticeData) (root lambda : ℂ)
    (hroot : root^2 = lambda) (hlambda : lambda ≠ 0) (i : Fin D.rank)
    (j : ℤ) (f : Oscillator D) :
    scaleOscillator D root lambda (current D i j f) =
      modeScale root lambda j • current D i j (scaleOscillator D root lambda f) := by
  by_cases hj : j < 0
  · let k := (-j-1).toNat
    have hk : j = -(k:ℤ)-1 := by dsimp [k]; omega
    rw [hk, current_negative]
    simp only [LinearMap.mulLeft_apply, map_mul]
    rw [show scaleOscillator D root lambda (X (i,k)) =
      modeScale root lambda (-(k:ℤ)-1) • X (i,k) by simp [scaleOscillator], smul_mul_assoc]
  · let k := j.toNat
    have hk : j = (k:ℤ) := by dsimp [k]; omega
    rw [hk]
    simp only [current, if_neg (not_lt.mpr (Int.natCast_nonneg k)), Int.toNat_natCast,
      LinearMap.smul_apply, map_smul, positive_scale]
    rw [smul_comm (modeScale root lambda (k:ℤ)) (frequency (k:ℤ))]
    congr 1
    rw [smul_smul, scale_opposites root lambda hroot hlambda, one_smul]

/-- The scaled formal current carries the specified half-coordinate weight
at each shifted frequency. -/
def scaledCurrent (D : LatticeData) (root lambda : ℂ) (i : Fin D.rank) (j : ℤ) :
    PowerSeries (End D) :=
  PowerSeries.mk fun n =>
    (Ring.choose (-frequency j) n * modeScale root lambda (j+n)) • current D i (j+n)

/-- Coordinate transport for the actual current with an explicit lift of
the nonzero scale. The lowering flow acts before the diagonal scale. -/
theorem scaled_lowering_flow_intertwines (D : LatticeData) (hu : IsUnit D.G.det)
    (root lambda : ℂ) (hroot : root^2 = lambda) (hlambda : lambda ≠ 0)
    (i : Fin D.rank) (j : ℤ) :
    let S := PowerSeries.C (scaleOscillator D root lambda).toLinearMap
    (S * loweringFlow D) * PowerSeries.C (current D i j) =
      scaledCurrent D root lambda i j * (S * loweringFlow D) := by
  have hs :
      PowerSeries.C (scaleOscillator D root lambda).toLinearMap * transportedCurrent D i j =
      scaledCurrent D root lambda i j *
        PowerSeries.C (scaleOscillator D root lambda).toLinearMap := by
    apply PowerSeries.ext
    intro n
    apply LinearMap.ext
    intro f
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, transportedCurrent, scaledCurrent,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      map_smul, scale_current D root lambda hroot hlambda, smul_smul]
  dsimp only
  rw [mul_assoc, lowering_flow_intertwines D hu, ← mul_assoc, hs, mul_assoc]


open TwistedGround.OriginalFourMChargeCoset (cosetKernel channelB channelD)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)

private theorem cosetKernel_detector_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k t : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) (c : ℂ) :
    cosetKernel D hu H K k t P Q R (c • S) a =
      c * cosetKernel D hu H K k t P Q R S a := by
  unfold cosetKernel
  rw [mul_left_comm c]
  congr 1
  rw [← smul_eq_mul c, smul_finsum]
  apply finsum_congr
  intro b
  split_ifs
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · simp

/-- The skew-channel detector lowering is the same normal ordering on the
actual polynomial, with the original skew cutoff and phase. -/
theorem skew_channels_normal_order (D : LatticeData) (hu : IsUnit D.G.det)
    (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    channelB D hu H K L m n r P Q R S a =
      (∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
        ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) *
            cosetKernel D hu K L (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ))
              Q R P (polynomialCoefficient D S ell) a) ∧
    channelD D hu H K L m n r P Q R S a =
      (∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
        ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
          Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) *
            cosetKernel D hu H L (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ))
              P R Q (polynomialCoefficient D S ell) a) := by
  constructor
  · unfold channelB
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ell _
    rw [← lowering_normal_order D hu, cosetKernel_detector_smul]
    ring
  · unfold channelD
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ell _
    rw [← lowering_normal_order D hu, cosetKernel_detector_smul]
    ring

end D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
