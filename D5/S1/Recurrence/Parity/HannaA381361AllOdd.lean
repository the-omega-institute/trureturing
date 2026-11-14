/- GID: D5/S1/Recurrence/Parity/HannaA381361AllOdd
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/HannaA381361AllOdd
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's implicit exponential generating series has odd integral coefficients. -/

/-
admission_basis: open-problem-resolution (#24232; Proved)
escape_witness: none
Every declaration below has proof_shape: bind-only.
The public surface is IsSourceSeries, claim, and the settling result.
The source equation uses coefficientwise absolute value and a zero-constant formal primitive.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26285.
Direct frozen dependencies are extracted from elaborated types and proof terms,
with same-module helper dependencies followed transitively. F-labels name the following declarations.
Declaration statement_id values are unverified: Stage A prohibits report production,
and the available cached report does not establish identities at this source tree.
Stage B must supply the current declaration identities before freezing.
F1: D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence.absSeries
F2: D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
F3: D5.S1.Recurrence.Invariants.UnitReversionSquareParity.Agree
F4: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.Series
F5: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.Series._proof_1
F6: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.X
F7: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.coeff
F8: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.coeff_mul_egf
F9: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.coeff_one
F10: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.coeff_seriesOf
F11: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul
F12: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul.eq_1
F13: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfMul_congr_at
F14: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfOne
F15: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.seriesOf
F16: D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.square_collapse
F17: D5.S1.Recurrence.Residue.HannaEGFMachinery.conv_map
F18: D5.S1.Recurrence.Residue.HannaEGFMachinery.eCoeff_inv
F19: D5.S1.Recurrence.Residue.HannaEGFMachinery.seqInv
F20: D5.S1.Recurrence.Residue.HannaEGFMachinery.seqInv.eq_1
F21: D5.S1.Recurrence.Residue.HannaEGFMachinery.seqInv.eq_2
F22: D5.S1.Recurrence.Residue.HannaEGFMachinery.seqInv_congr
F23: D5.S1.Recurrence.Residue.HannaEGFMachinery.seqInv_map
F24: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
F25: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
F26: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_derivative
F27: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
F28: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
F29: D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique
F30: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.constantCoeff_encode
F31: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
F32: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_ext
F33: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
F34: _private.D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.0.D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.F2
F35: _private.D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.0.D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.SAlg
IsSourceSeries: proof_shape: bind-only; escape_witness: none; consumers: claim, source_ode, ode_source, integral_source_exists_unique, result
  Direct frozen dependencies: F1
claim: proof_shape: bind-only; escape_witness: none; consumers: result
  Direct frozen dependencies: F1, F25
next: proof_shape: bind-only; escape_witness: none; consumers: next_congr, sequence_exists_unique, next_cast, eCoeff_next, next_mod_two, sequence_odd, result
  Direct frozen dependencies: F11, F19
next_congr: proof_shape: bind-only; escape_witness: none; consumers: sequence_exists_unique
  Direct frozen dependencies: F11, F13, F19, F22
sequence_exists_unique: proof_shape: bind-only; escape_witness: none; consumers: integral_source_exists_unique
  Direct frozen dependencies: F2, F3, F11, F13, F19, F22
next_cast: proof_shape: bind-only; escape_witness: none; consumers: integral_source_exists_unique, result
  Direct frozen dependencies: F11, F17, F19, F23
eCoeff_abs: proof_shape: bind-only; escape_witness: none; consumers: eCoeff_next
  Direct frozen dependencies: F1, F25
eCoeff_next: proof_shape: bind-only; escape_witness: none; consumers: integral_source_exists_unique, result
  Direct frozen dependencies: F1, F11, F12, F18, F19, F25, F27
source_ode: proof_shape: bind-only; escape_witness: none; consumers: integral_source_exists_unique, result
  Direct frozen dependencies: F1
ode_source: proof_shape: bind-only; escape_witness: none; consumers: integral_source_exists_unique
  Direct frozen dependencies: F1, F25, F26, F29, F30, F31, F32, F33
integral_source_exists_unique: proof_shape: bind-only; escape_witness: none; consumers: result
  Direct frozen dependencies: F1, F2, F3, F11, F12, F13, F17, F18, F19, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33
square_mod_two: proof_shape: bind-only; escape_witness: none; consumers: next_mod_two
  Direct frozen dependencies: F4, F5, F6, F7, F8, F9, F10, F11, F14, F15, F16, F34, F35
seqInv_one: proof_shape: bind-only; escape_witness: none; consumers: next_mod_two
  Direct frozen dependencies: F14, F19, F20, F21
egfMul_one_right: proof_shape: bind-only; escape_witness: none; consumers: next_mod_two
  Direct frozen dependencies: F11, F12, F14
next_mod_two: proof_shape: bind-only; escape_witness: none; consumers: sequence_odd
  Direct frozen dependencies: F4, F5, F6, F7, F8, F9, F10, F11, F12, F14, F15, F16, F17, F19, F20, F21, F23, F34, F35
sequence_odd: proof_shape: bind-only; escape_witness: none; consumers: result
  Direct frozen dependencies: F4, F5, F6, F7, F8, F9, F10, F11, F12, F14, F15, F16, F17, F19, F20, F21, F23, F34, F35
result: proof_shape: bind-only; escape_witness: none; consumers: settling result
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31, F32, F33, F34, F35
-/

import D5.S1.Recurrence.Residue.HannaEGFMachinery
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree
import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence

namespace D5.S1.Recurrence.Parity.HannaA381361AllOdd

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition (eCoeff)
open D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence (absSeries)

/-- A(0) = 1 and A = exp(integral_0^x abs(1/A^2)); I is that formal primitive. -/
def IsSourceSeries (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    ∃ I : PowerSeries ℚ,
      constantCoeff I = 0 ∧
      PowerSeries.derivative I = absSeries ((A ^ 2)⁻¹) ∧
      A = (PowerSeries.exp ℚ).subst I

/-- Source assertion: for every n >= 0, the EGF coefficient a(n) is an odd integer. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsSourceSeries A) ∧
    ∀ A : PowerSeries ℚ, IsSourceSeries A →
      ∀ n : ℕ, ∃ z : ℤ, eCoeff A n = (2 : ℚ) * (z : ℚ) + 1

end D5.S1.Recurrence.Parity.HannaA381361AllOdd

set_option maxHeartbeats 800000
set_option autoImplicit false
open PowerSeries Finset
open D5.S1.Recurrence.Algebraic.HannaAbsoluteCubicCongruence (absSeries)
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
open D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree (egfMul)
open D5.S1.Recurrence.Residue.HannaEGFMachinery (seqInv seqInv_map seqInv_congr eCoeff_inv conv_map)
open D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree
  (egfMul_congr_at egfOne Series seriesOf coeff_seriesOf square_collapse coeff_mul_egf coeff_one coeff X)

namespace D5.S1.Recurrence.Parity.HannaA381361AllOdd

-- The same triangular operator is used over integers and rationals.
private def next {R : Type*} [CommRing R] (norm : R → R) (f : ℕ → R) (n : ℕ) : R :=
  egfMul f (fun j => norm (seqInv (egfMul f f) j)) n

private theorem next_congr {R : Type*} [CommRing R] (norm : R → R)
    {f g : ℕ → R} {n : ℕ} (h : ∀ j ≤ n, f j = g j) :
    next norm f n = next norm g n := by
  apply egfMul_congr_at h
  intro j hj
  congr 1
  apply seqInv_congr
  intro i hi
  exact egfMul_congr_at (fun k hk => h k (by omega)) (fun k hk => h k (by omega))

private theorem sequence_exists_unique {R : Type*} [CommRing R] (norm : R → R) :
    ∃ a : ℕ → R, a 0 = 1 ∧ (∀ n, a (n+1) = next norm a n) ∧
      ∀ b : ℕ → R, b 0 = 1 → (∀ n, b (n+1) = next norm b n) → b = a := by
  let update (f : PowerSeries R) : PowerSeries R :=
    mk (fun | 0 => 1 | n+1 => next norm (fun j => PowerSeries.coeff j f) n)
  obtain ⟨f, hf0, hff, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      update (by intro f hf; simp [update]) (by
        intro d f g hd hf hg h n hn
        cases n
        · simp [update]
        · rename_i n
          simp only [update, coeff_mk]
          exact next_congr norm (fun i hi => h i (by omega)))
  refine ⟨fun n => PowerSeries.coeff n f, ?_, ?_, ?_⟩
  · simpa only [coeff_zero_eq_constantCoeff] using hf0
  · intro n
    simpa only [update, coeff_mk] using congrArg (PowerSeries.coeff (n+1)) hff
  · intro b hb0 hb
    have hbfix : mk b = update (mk b) := by
      ext n
      cases n
      · simpa [update] using hb0
      · rename_i n
        simpa [update] using hb n
    have hbeq := huniq (mk b) (by simpa using hb0) hbfix
    funext n
    simpa using congrArg (PowerSeries.coeff n) hbeq

private theorem next_cast (a : ℕ → ℤ) (n : ℕ) :
    ((next abs a n : ℤ) : ℚ) = next abs (fun j => (a j : ℚ)) n := by
  unfold next
  have hm := conv_map (Int.castRingHom ℚ) a
    (fun j => |seqInv (egfMul a a) j|) n
  simp only [Int.coe_castRingHom] at hm
  rw [hm]
  congr 1
  funext j
  rw [Int.cast_abs]
  have hi := seqInv_map (Int.castRingHom ℚ) (egfMul a a) j
  simp only [Int.coe_castRingHom] at hi
  rw [hi]
  exact congrArg abs (congrArg (fun f : ℕ → ℚ => seqInv f j)
    (funext (conv_map (Int.castRingHom ℚ) a a)))

private theorem eCoeff_abs (F : PowerSeries ℚ) (n : ℕ) :
    eCoeff (absSeries F) n = |eCoeff F n| := by
  simp only [absSeries, eCoeff, coeff_mk, abs_mul,
    abs_of_nonneg (show (0 : ℚ) ≤ n.factorial by positivity)]

private theorem eCoeff_next (A : PowerSeries ℚ) (h0 : constantCoeff A = 1) (n : ℕ) :
    eCoeff (A * absSeries ((A^2)⁻¹)) n = next abs (eCoeff A) n := by
  rw [eCoeff_mul, next, egfMul]
  apply sum_congr rfl
  intro k hk
  rw [eCoeff_abs, eCoeff_inv (by simp [h0])]
  have he : eCoeff (A^2) = egfMul (eCoeff A) (eCoeff A) := by
    funext j
    simpa only [pow_two, egfMul] using eCoeff_mul A A j
  rw [he]

private theorem source_ode {A : PowerSeries ℚ} (h : IsSourceSeries A) :
    PowerSeries.derivative A = A * absSeries ((A^2)⁻¹) := by
  obtain ⟨h0, I, hI0, hI, hA⟩ := h
  conv_lhs => rw [hA]
  rw [derivative_subst (.of_constantCoeff_zero hI0), derivative_exp, hI, ← hA]

private theorem ode_source {A : PowerSeries ℚ} (h0 : constantCoeff A = 1)
    (he : PowerSeries.derivative A = A * absSeries ((A^2)⁻¹)) : IsSourceSeries A := by
  let H := absSeries ((A^2)⁻¹)
  let I := encode (fun | 0 => 0 | n+1 => eCoeff H n)
  have hI0 : constantCoeff I = 0 := by exact constantCoeff_encode _
  have hI : PowerSeries.derivative I = H := by
    apply eCoeff_ext
    intro n
    rw [eCoeff_derivative, show I = encode _ from rfl, eCoeff_encode]
  let E := (PowerSeries.exp ℚ).subst I
  have hE : PowerSeries.derivative E = E * H := by
    rw [show E = (PowerSeries.exp ℚ).subst I from rfl,
      derivative_subst (.of_constantCoeff_zero hI0), derivative_exp, hI]
  have hE0 : constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst I) = 1
    simpa only [constantCoeff_exp, map_one] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hI0 (PowerSeries.exp ℚ)
  refine ⟨h0, I, hI0, hI, ?_⟩
  exact D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique
    A E H (by simpa only [coeff_zero_eq_constantCoeff] using h0.trans hE0.symm)
    (by simpa only [mul_comm] using he) (by simpa only [mul_comm] using hE)

private theorem integral_source_exists_unique :
    ∃ A : PowerSeries ℚ, IsSourceSeries A ∧ Integral A ∧
      ∀ B : PowerSeries ℚ, IsSourceSeries B → B = A := by
  obtain ⟨a, ha0, ha, _⟩ := sequence_exists_unique (R := ℤ) abs
  let A := encode (fun n => (a n : ℚ))
  have hA0 : constantCoeff A = 1 := by simp [A, ha0]
  have hA : IsSourceSeries A := by
    apply ode_source hA0
    apply eCoeff_ext
    intro n
    rw [eCoeff_derivative, eCoeff_next A hA0]
    simp only [A, eCoeff_encode, show eCoeff (encode (fun n => (a n : ℚ))) =
      (fun n => (a n : ℚ)) from funext (eCoeff_encode _)]
    rw [ha, next_cast]
  refine ⟨A, hA, ?_, ?_⟩
  · intro n
    exact ⟨a n, eCoeff_encode _ n⟩
  · intro B hB
    obtain ⟨c, hc0, hc, hcu⟩ := sequence_exists_unique (R := ℚ) abs
    have hrec (F : PowerSeries ℚ) (hF : IsSourceSeries F) :
        ∀ n, eCoeff F (n+1) = next abs (eCoeff F) n := by
      intro n
      rw [← eCoeff_derivative, source_ode hF, eCoeff_next F hF.1]
    apply eCoeff_ext
    exact congrFun ((hcu (eCoeff B) (by simpa using hB.1) (hrec B hB)).trans
      (hcu (eCoeff A) (by simpa using hA.1) (hrec A hA)).symm)


private theorem square_mod_two (f : ℕ → ZMod 2) (h0 : f 0 = 1) (n : ℕ) :
    egfMul f f n = egfOne n := by
  let F : Series := seriesOf f
  have hF0 : F.ofConv 1 = 1 := by
    have hz := coeff_seriesOf f 0
    change F.ofConv (X ^ 0) = f 0 at hz
    simpa only [pow_zero, h0] using hz
  have hF : F * F = 1 := by rw [square_collapse F, hF0, one_mul, map_one]
  have hc : coeff F = f := funext (coeff_seriesOf f)
  calc
    egfMul f f n = coeff (F * F) n := by rw [coeff_mul_egf, hc]
    _ = egfOne n := by rw [hF]; exact coeff_one n

private theorem seqInv_one {R : Type*} [CommRing R] (n : ℕ) :
    seqInv (egfOne : ℕ → R) n = egfOne n := by
  cases n <;> simp [seqInv, egfOne]

private theorem egfMul_one_right {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    egfMul f egfOne n = f n := by
  rw [egfMul, sum_eq_single n]
  · simp [egfOne]
  · intro k hk hkn
    have hne : n-k ≠ 0 := by have := mem_range.mp hk; omega
    simp [egfOne, hne]
  · simp

private theorem next_mod_two (a : ℕ → ℤ) (h0 : a 0 = 1) (n : ℕ) :
    ((next abs a n : ℤ) : ZMod 2) = (a n : ZMod 2) := by
  let hom := Int.castRingHom (ZMod 2)
  have hc : (fun j => ((egfMul a a j : ℤ) : ZMod 2)) = egfOne := by
    funext j
    exact (conv_map hom a a j).trans (square_mod_two _ (by simp [h0]) j)
  have hb (j : ℕ) : ((seqInv (egfMul a a) j : ℤ) : ZMod 2) = egfOne j := by
    have hi := seqInv_map hom (egfMul a a) j
    simp only [hom, Int.coe_castRingHom] at hi
    rw [hi]
    change seqInv (fun i => ((egfMul a a i : ℤ) : ZMod 2)) j = egfOne j
    rw [hc, seqInv_one]
  have hab : (fun j => ((|seqInv (egfMul a a) j| : ℤ) : ZMod 2)) = egfOne := by
    funext j
    rw [ZMod.intCast_abs_mod_two, hb]
  have hm := conv_map hom a (fun j => |seqInv (egfMul a a) j|) n
  simp only [hom, Int.coe_castRingHom] at hm
  rw [next, hm]
  change egfMul (fun j => (a j : ZMod 2))
    (fun j => ((|seqInv (egfMul a a) j| : ℤ) : ZMod 2)) n = (a n : ZMod 2)
  rw [hab, egfMul_one_right]

private theorem sequence_odd (a : ℕ → ℤ) (h0 : a 0 = 1)
    (ha : ∀ n, a (n+1) = next abs a n) (n : ℕ) : (a n : ZMod 2) = 1 := by
  have hs : ∀ k, (a k : ZMod 2) = (a (k+1) : ZMod 2) := by
    intro k
    rw [ha, next_mod_two a h0]
  have hn := Nat.rel_of_forall_rel_succ_of_le Eq hs (Nat.zero_le n)
  exact hn.symm.trans (by simp [h0])

theorem result : D5.S1.Recurrence.Parity.HannaA381361AllOdd.claim := by
  obtain ⟨A, hA, hAi, hu⟩ := integral_source_exists_unique
  refine ⟨⟨A, hA⟩, ?_⟩
  intro B hB
  rw [hu B hB]
  choose a ha using hAi
  have ha0 : a 0 = 1 := by
    have h := ha 0
    simp only [eCoeff_zero, hA.1] at h
    exact_mod_cast h.symm
  have harec : ∀ n, a (n+1) = next abs a n := by
    intro n
    have h : eCoeff A (n+1) = next abs (eCoeff A) n := by
      rw [← eCoeff_derivative, source_ode hA, eCoeff_next A hA.1]
    rw [ha, show eCoeff A = (fun n => (a n : ℚ)) from funext ha, ← next_cast] at h
    exact_mod_cast h
  intro n
  have hm := sequence_odd a ha0 harec n
  have hd : (2 : ℤ) ∣ a n - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using hm
  obtain ⟨z, hz⟩ := hd
  refine ⟨z, ?_⟩
  have heq : a n = 2*z+1 := by exact Int.sub_eq_iff_eq_add.mp hz
  rw [ha, heq]
  push_cast
  rfl

end D5.S1.Recurrence.Parity.HannaA381361AllOdd
