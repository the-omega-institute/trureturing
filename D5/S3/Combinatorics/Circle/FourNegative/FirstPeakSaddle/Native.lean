/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Native
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Six exhaustive native choices with exact rectangle, gate and submask conversions. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Structure
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.GeneralArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HighMiddle
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfStep
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.QuarterStep
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain.Arithmetic

/-! Every branch constructs actual natural masks.
The small-c2 branch uses its direct twelve gates and its separate submask;
it has no fixed-q, grain-bound or anchor obligation. The other five branches
use the fixed-q rectangle construction, with its general z>=4 implication.
All conversions below are mathematical terms, not external truth flags. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle

open private gate JointChoice JointChoice.mk JointChoice.s JointChoice.r JointChoice.h JointChoice.v
  JointChoice.bounds JointChoice.submask JointChoice.good from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Structure
open private D A B L M Bn Ln Mn C gateMargin rectangleMargin from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates
open private ParameterChoice ParameterChoice.s ParameterChoice.r ParameterChoice.v
  ParameterChoice.h ParameterChoice.r_pos ParameterChoice.r_le_s ParameterChoice.s_cap
  ParameterChoice.v_cap ParameterChoice.h_cap ParameterChoice.submask ParameterChoice.gates
  parameterChoice rectangle_to_twelve from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.GeneralArithmetic
open private rectangle NativeChoice NativeChoice.s NativeChoice.r NativeChoice.h
  NativeChoice.v NativeChoice.bounds NativeChoice.anchor NativeChoice.submask NativeChoice.good from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic
open private high_middle_choice_exists from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HighMiddle
open private half_step_choice_exists from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfStep
open private quarter_step_choice_exists from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.QuarterStep
open private margin Margins from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain.Certificates
open private Choice Choice.s Choice.r Choice.h Choice.v Choice.bounds Choice.submask
  Choice.good arithmetic_choice_exists from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain.Arithmetic
open private half_power from
  D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

-- The diagonal interface orders powers as x,y,z,t; the physical one as t,z,x,y.
private theorem gate_agrees (t z x y s r h v : ℤ) :
    gate t z x y s r h v = gateMargin x y z t s r h v := by
  funext i
  fin_cases i <;> dsimp [gate,gateMargin,D,A,B,L,M,Bn,Ln,Mn] <;> ring

-- The remaining interface writes H directly; diagonal writes H=E+rD-h(z+1).
private theorem rectangle_agrees (t z x y g q r h v : ℤ) :
    rectangle t z x y g q r h v =
      rectangleMargin x y z t g q (q+r) r h v := by
  funext i
  fin_cases i <;> dsimp [rectangle,rectangleMargin,D,A,L,M,Ln,Mn,C] <;> ring

private theorem double_power_le (u v : ℕ) (huv : u<v) :
    2*(2:ℤ)^u ≤ (2:ℤ)^v := by
  calc
    2*(2:ℤ)^u = (2:ℤ)^(u+1) := by rw [pow_succ]; ring
    _ ≤ (2:ℤ)^v := pow_le_pow_right₀ (by norm_num) (by omega)

private theorem diagonal_joint_choice (a b c d : ℕ)
    (hc : 3≤c) (hcd : c<d) (hdb : d<b) (hba : b<a) (ha : a≤c+d) :
    Nonempty (JointChoice a b c d) := by
  obtain ⟨ch⟩ := parameterChoice a b c d hc hcd hdb hba ha
  have hpow : (2:ℕ)^(b-c-1)≤2^(b-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨JointChoice.mk (ParameterChoice.s ch) (ParameterChoice.r ch) (ParameterChoice.h ch)
    (ParameterChoice.v ch)
    ⟨(ParameterChoice.r_pos ch),(ParameterChoice.r_le_s ch),(ParameterChoice.s_cap ch),(ParameterChoice.v_cap ch),
      lt_of_lt_of_le (ParameterChoice.h_cap ch) hpow⟩
    (by intro e _ he; exact (ParameterChoice.submask ch) e he) ?_⟩
  intro i
  rw [gate_agrees]
  exact (ParameterChoice.gates ch) i

-- Shared conversion for high-middle, half-step and quarter-step. No gates
-- are assumed: the four actual rectangle margins imply all twelve here.
private def remaining_joint_choice (a b c d : ℕ)
    (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a)
    (ch : NativeChoice a b c d) : JointChoice a b c d := by
  have hz : (4:ℤ)≤2^c := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
    norm_num at hp
    exact hp
  have hs : ((NativeChoice.s ch):ℤ)=(2:ℤ)^(a-d)*((2:ℤ)^(d-1)-1)+((NativeChoice.r ch):ℤ) := by
    rw [(NativeChoice.anchor ch)]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_sub Nat.one_le_two_pow,Nat.cast_one]
  have hprod : (2:ℤ)^(a-d)*(2:ℤ)^d=(2:ℤ)^a := by
    rw [←pow_add]
    congr 1
    omega
  have hq : 2*(((NativeChoice.s ch):ℤ)-((NativeChoice.r ch):ℤ))=(2:ℤ)^a-2*(2:ℤ)^(a-d) := by
    rw [half_power d (by omega)] at hprod
    rw [hs]
    nlinarith only [hprod]
  have hq0 : 0≤((NativeChoice.s ch):ℤ)-((NativeChoice.r ch):ℤ) := by
    have hr : ((NativeChoice.r ch):ℤ)≤((NativeChoice.s ch):ℤ) := by exact_mod_cast (NativeChoice.bounds ch).2.1
    omega
  have hr : (1:ℤ)≤((NativeChoice.r ch):ℤ) := by exact_mod_cast (NativeChoice.bounds ch).1
  have hsc : 2*((NativeChoice.s ch):ℤ)≤(2:ℤ)^a := by
    have hh : ((NativeChoice.s ch):ℤ)≤(2:ℤ)^(a-1) := by exact_mod_cast (NativeChoice.bounds ch).2.2.1
    rw [half_power a (by omega)]
    omega
  have hR : (2:ℤ)^b=2*(2:ℤ)^c*(2:ℤ)^(b-c-1) := by
    have he : b=c+(b-c-1)+1 := by omega
    conv_lhs => rw [he]
    simp only [pow_add,pow_one]
    ring
  have hcap : 2*(2:ℤ)^c*(((NativeChoice.h ch):ℤ)+1)≤(2:ℤ)^b := by
    have hh : ((NativeChoice.h ch):ℤ)<(2:ℤ)^(b-c-1) := by
      exact_mod_cast (NativeChoice.bounds ch).2.2.2.2
    rw [hR]
    exact mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have hrect : ∀ i, 0≤rectangleMargin (2^a) (2^b) (2^c) (2^d)
      (2^(a-d)) (((NativeChoice.s ch):ℤ)-((NativeChoice.r ch):ℤ)) (NativeChoice.s ch) (NativeChoice.r ch) (NativeChoice.h ch) (NativeChoice.v ch) i := by
    intro i
    have hh := (NativeChoice.good ch) i
    rw [rectangle_agrees] at hh
    simpa only [sub_add_cancel] using hh
  have hgates := rectangle_to_twelve (2^a) (2^b) (2^c) (2^d)
    (2^(a-d)) (((NativeChoice.s ch):ℤ)-((NativeChoice.r ch):ℤ)) (NativeChoice.s ch) (NativeChoice.r ch) (NativeChoice.h ch) (NativeChoice.v ch)
    hz (double_power_le c d hcd) (double_power_le d b hdb)
    (double_power_le b a hba) hq (by ring) hq0 hr hsc
    (by positivity) hcap hrect
  have hpow : (2:ℕ)^(b-c-1)≤2^(b-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  refine JointChoice.mk (NativeChoice.s ch) (NativeChoice.r ch) (NativeChoice.h ch) (NativeChoice.v ch)
    ⟨(NativeChoice.bounds ch).1,(NativeChoice.bounds ch).2.1,(NativeChoice.bounds ch).2.2.1,
      (NativeChoice.bounds ch).2.2.2.1,lt_of_lt_of_le (NativeChoice.bounds ch).2.2.2.2 hpow⟩
    (by intro e _ he; exact (NativeChoice.submask ch) e he) ?_
  intro i
  rw [gate_agrees]
  exact hgates i

-- Fin 19 has twelve actual gates followed by seven native capacities.
-- In particular this conversion does not demand r<=g or s=q+r.
private def small_c2_joint_choice (a b d : ℕ) (ch : Choice a b d) :
    JointChoice a b 2 d := by
  refine JointChoice.mk (Choice.s ch) (Choice.r ch) (Choice.h ch) (Choice.v ch)
    (Choice.bounds ch) (Choice.submask ch) ?_
  intro i
  have hm := (Choice.good ch) (⟨i.val,by omega⟩ : Fin 19)
  have he : margin (2^d) (2^a) (2^b) (Choice.s ch) (Choice.r ch) (Choice.h ch) (Choice.v ch)
      (⟨i.val,by omega⟩ : Fin 19) =
      gate (2^d) (2^2) (2^a) (2^b) (Choice.s ch) (Choice.r ch) (Choice.h ch) (Choice.v ch) i := by
    fin_cases i <;> dsimp [margin,gate] <;> norm_num <;> ring
  rw [he] at hm
  exact hm

private theorem native_choice_exists (a b c d : ℕ)
    (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a) :
    Nonempty (JointChoice a b c d) := by
  by_cases hb : c+d<b
  · -- I. High-middle, including c=2.
    obtain ⟨ch⟩ := high_middle_choice_exists a b c d hc hcd hdb hba hb
    exact ⟨remaining_joint_choice a b c d hc hcd hdb hba ch⟩
  · have hble : b≤c+d := by omega
    by_cases hc3 : 3≤c
    · by_cases ha : a<c+d
      · -- IIa. Strict diagonal, arbitrary grain.
        exact diagonal_joint_choice a b c d hc3 hcd hdb hba (by omega)
      · by_cases he : a=c+d
        · -- IIb. Equality diagonal; the native arithmetic proves its boundary.
          exact diagonal_joint_choice a b c d hc3 hcd hdb hba (by omega)
        · -- IIc. Half-step above the diagonal.
          obtain ⟨ch⟩ := half_step_choice_exists a b c d hc3 hcd hdb hba
            (by omega) hble
          exact ⟨remaining_joint_choice a b c d hc hcd hdb hba ch⟩
    · have hc2 : c=2 := by omega
      subst c
      have hb2 : b≤d+2 := by omega
      by_cases ha : a≤d+3
      · -- IIIa. Direct 285-margin small-c2 selection, without fixed q.
        obtain ⟨ch⟩ := arithmetic_choice_exists a b d (by omega) hdb hba ha
        exact ⟨small_c2_joint_choice a b d ch⟩
      · -- IIIb. Quarter-step; b≤d+2 was derived, not assumed publicly.
        obtain ⟨ch⟩ := quarter_step_choice_exists a b d (by omega) hdb hba
          hb2 (by omega)
        exact ⟨remaining_joint_choice a b 2 d (by omega) hcd hdb hba ch⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
