/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Physical
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 PermutationStabilizer Physical on original physical labels. -/
/- Source only: not elaborated or kernel checked. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open SourceWidth ZeroSumSubsets
open D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
  (degree base seed total slice Qmask Q_exact)
open MersenneExceptional19Stabilizer (actual_sum_blocks charge base_facts floor_unique)
open private word_mask physical_slices
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary

def aa (r : ℕ) : ℤ := (2*(base r : ℤ)-3)/19
def bb (r : ℕ) : ℤ := (3*(base r : ℤ)+5)/19
def ss (r : ℕ) : ℤ := aa r+bb r
def eighth (r : ℕ) : ℤ := (base r : ℤ)/8
def correction (B L M U : ℤ) : ℤ :=
  -(2*L/B)+8*M/B-4*M/B-4*U/B

theorem parameter_exact (r : ℕ) :
    19*aa r=2*(base r : ℤ)-3 ∧ 19*bb r=3*(base r : ℤ)+5 ∧
    19*ss r=5*(base r : ℤ)+2 := by
  have hB : (base r : ℤ)%19=11 := by exact_mod_cast (base_facts r).2.1
  have ha : (2*(base r : ℤ)-3)%19=0 := by omega
  have hb : (3*(base r : ℤ)+5)%19=0 := by omega
  have hea := Int.emod_add_mul_ediv (2*(base r : ℤ)-3) 19
  have heb := Int.emod_add_mul_ediv (3*(base r : ℤ)+5) 19
  dsimp [aa, bb, ss]
  omega

private theorem base_multiple (r k : ℕ) (hk : k≤degree r) :
    (base r : ℤ)=(2 : ℤ)^k*2^(degree r-k) := by
  rw [← pow_add, Nat.add_sub_of_le hk]
  simp [base]

theorem eighth_facts (r : ℕ) :
    (base r : ℤ)=8*eighth r ∧ 512≤eighth r ∧ eighth r%8=0 := by
  have hb : (4096 : ℤ)≤base r := by exact_mod_cast (base_facts r).1
  have h64 : (base r : ℤ)=64*(2 : ℤ)^(degree r-6) := by
    simpa using base_multiple r 6 (by dsimp [degree]; omega)
  have hmod : (base r : ℤ)%64=0 := by rw [h64]; omega
  dsimp [eighth]
  omega

/-- Strict integer margins; these are uniform in r, including r=0. -/
theorem parameter_margins (r : ℕ) :
    eighth r+2<2*aa r ∧ aa r+1<eighth r ∧
    eighth r+1<bb r ∧ 2*bb r+2<3*eighth r ∧
    2*eighth r+1<ss r ∧ ss r+1<3*eighth r := by
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  obtain ⟨hB,hq,hmod⟩ := eighth_facts r
  generalize hbase : (base r : ℤ) = B at *
  generalize haa : aa r = a at *
  generalize hbb : bb r = b at *
  generalize hss : ss r = s at *
  generalize heighth : eighth r = E at *
  clear hbase haa hbb hss heighth
  omega

theorem parameter_parities (r : ℕ) :
    aa r%2=1 ∧ bb r%2=1 ∧ ss r%4=2 := by
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  obtain ⟨hB,hq,hmod⟩ := eighth_facts r
  generalize hbase : (base r : ℤ) = B at *
  generalize haa : aa r = a at *
  generalize hbb : bb r = b at *
  generalize hss : ss r = s at *
  generalize heighth : eighth r = E at *
  clear hbase haa hbb hss heighth
  omega

private theorem physical_total (r : ℕ) (L M U : ℤ)
    (hL : 0≤L ∧ L<base r) (hM : 0≤M ∧ M<base r)
    (hU : 0≤U ∧ U<base r) :
    total r (physical (degree r) L M U) =
      19*((base r : ℤ)-1)*
        (aa r*L-ss r*M+bb r*U+(Qmask r : ℤ)*correction (base r) L M U) := by
  have hd : 0<degree r := by dsimp [degree]; omega
  have hp : (2 : ℤ)^degree r=base r := by simp [base]
  obtain ⟨h0,h1,h2⟩ := physical_slices (degree r) hd L M U
  rw [actual_sum_blocks, h0, h1, h2,
    word_mask (degree r) L hL.1 (by simpa [hp] using hL.2),
    word_mask (degree r) M hM.1 (by simpa [hp] using hM.2),
    word_mask (degree r) U hU.1 (by simpa [hp] using hU.2)]
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  have hQ := Q_exact r
  unfold charge correction
  rw [← ha, ← hb, ← hs, ← hQ]
  ring

private def affine (r : ℕ) (M : ℤ) : Finset (Fin (3*degree r)) :=
  physical (degree r) (M+bb r) M (M-aa r)

def affineRange (r : ℕ) (M : ℤ) : Prop :=
  M=aa r ∨ (3*eighth r≤M ∧ M≤4*eighth r+aa r-1) ∨
    (5*eighth r≤M ∧ M≤8*eighth r-bb r-1)

theorem affine_digits (r : ℕ) (M : ℤ) (hM : affineRange r M) :
    (0≤M+bb r ∧ M+bb r<base r) ∧
    (0≤M ∧ M<base r) ∧ (0≤M-aa r ∧ M-aa r<base r) ∧
    correction (base r) (M+bb r) M (M-aa r)=0 := by
  obtain ⟨hB,hq,hmod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  have hs : ss r=aa r+bb r := rfl
  have hBp : (0 : ℤ)<base r := by omega
  rcases hM with hM | hM | hM
  · subst M
    have f0 : 2*(aa r+bb r)/(base r : ℤ)=0 := by
      apply floor_unique hBp <;> omega
    have f1 : 8*aa r/(base r : ℤ)=0 := by
      apply floor_unique hBp <;> omega
    have f2 : 4*aa r/(base r : ℤ)=0 := by
      apply floor_unique hBp <;> omega
    refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,
      ⟨by omega,by omega⟩,?_⟩
    simp [correction, f0, f1, f2]
  · have f0 : 2*(M+bb r)/(base r : ℤ)=1 := by
      apply floor_unique hBp <;> omega
    have f2 : 4*(M-aa r)/(base r : ℤ)=1 := by
      apply floor_unique hBp <;> omega
    have f1 : 8*M/(base r : ℤ)-4*M/(base r : ℤ)=2 := by
      by_cases hm : M<4*eighth r
      · have f8 : 8*M/(base r : ℤ)=3 := by apply floor_unique hBp <;> omega
        have f4 : 4*M/(base r : ℤ)=1 := by apply floor_unique hBp <;> omega
        omega
      · have f8 : 8*M/(base r : ℤ)=4 := by apply floor_unique hBp <;> omega
        have f4 : 4*M/(base r : ℤ)=2 := by apply floor_unique hBp <;> omega
        omega
    refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,
      ⟨by omega,by omega⟩,?_⟩
    dsimp [correction]
    omega
  · have f0 : 2*(M+bb r)/(base r : ℤ)=1 := by
      apply floor_unique hBp <;> omega
    have f2 : 4*(M-aa r)/(base r : ℤ)=2 := by
      apply floor_unique hBp <;> omega
    have f1 : 8*M/(base r : ℤ)-4*M/(base r : ℤ)=3 := by
      by_cases hm : M<6*eighth r
      · have f8 : 8*M/(base r : ℤ)=5 := by apply floor_unique hBp <;> omega
        have f4 : 4*M/(base r : ℤ)=2 := by apply floor_unique hBp <;> omega
        omega
      · have f8 : 8*M/(base r : ℤ)=6 := by apply floor_unique hBp <;> omega
        have f4 : 4*M/(base r : ℤ)=3 := by apply floor_unique hBp <;> omega
        omega
    refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,
      ⟨by omega,by omega⟩,?_⟩
    dsimp [correction]
    omega

/-- Every row used below is literally zero in the original integer weights. -/
private theorem affine_zero (r : ℕ) (M : ℤ) (hM : affineRange r M) :
    total r (affine r M)=0 := by
  obtain ⟨hL,hM',hU,hC⟩ := affine_digits r M hM
  unfold affine
  rw [physical_total r _ _ _ hL hM' hU, hC]
  dsimp [ss]
  ring

def qLow (r : ℕ) : ℤ := (12*(base r : ℤ)+1)/19
def qMid (r : ℕ) : ℤ := ((base r : ℤ)-11)/19
def q8Low (r : ℕ) : ℤ := ((base r : ℤ)+8)/19
def q8Mid (r : ℕ) : ℤ := (8*(base r : ℤ)+7)/19

private theorem q_digits_exact (r : ℕ) :
    19*qLow r=12*(base r : ℤ)+1 ∧ 19*qMid r=(base r : ℤ)-11 ∧
    19*q8Low r=(base r : ℤ)+8 ∧ 19*q8Mid r=8*(base r : ℤ)+7 := by
  have hB : (base r : ℤ)%19=11 := by exact_mod_cast (base_facts r).2.1
  have h0 := Int.emod_add_mul_ediv (12*(base r : ℤ)+1) 19
  have h1 := Int.emod_add_mul_ediv ((base r : ℤ)-11) 19
  have h2 := Int.emod_add_mul_ediv ((base r : ℤ)+8) 19
  have h3 := Int.emod_add_mul_ediv (8*(base r : ℤ)+7) 19
  dsimp [qLow,qMid,q8Low,q8Mid]
  omega

/-- The entire final two by two certificate, as uniform integer equalities. -/
theorem q_readings (r : ℕ) :
    (0≤qLow r ∧ qLow r<base r) ∧ (0≤qMid r ∧ qMid r<base r) ∧
    (0≤q8Low r ∧ q8Low r<base r) ∧ (0≤q8Mid r ∧ q8Mid r<base r) ∧
    qLow r%2=1 ∧ q8Low r%2=0 ∧
    correction (base r) (qLow r) (qMid r) 0 = -1 ∧
    correction (base r) (q8Low r) (q8Mid r) 0 = 2 ∧
    aa r*qLow r-ss r*qMid r=(Qmask r : ℤ) ∧
    aa r*q8Low r-ss r*q8Mid r= -2*(Qmask r : ℤ) := by
  obtain ⟨h0,h1,h2,h3⟩ := q_digits_exact r
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  obtain ⟨hB,hq,hmod⟩ := eighth_facts r
  have hQ := Q_exact r
  generalize hbase : (base r : ℤ) = B at *
  generalize haa : aa r = a at *
  generalize hbb : bb r = b at *
  generalize hss : ss r = s at *
  generalize heighth : eighth r = E at *
  clear hbase haa hbb hss heighth
  generalize hlow : qLow r = L at *
  generalize hmid : qMid r = M at *
  generalize hlow8 : q8Low r = L8 at *
  generalize hmid8 : q8Mid r = M8 at *
  generalize hqm : (Qmask r : ℤ) = Q at *
  clear hlow hmid hlow8 hmid8 hqm
  have hBp : (0 : ℤ)<base r := by omega
  have f0 : 2*L/B=1 := by apply floor_unique hBp <;> omega
  have f1 : 8*M/B=0 := by apply floor_unique hBp <;> omega
  have f2 : 4*M/B=0 := by apply floor_unique hBp <;> omega
  have g0 : 2*L8/B=0 := by apply floor_unique hBp <;> omega
  have g1 : 8*M8/B=3 := by apply floor_unique hBp <;> omega
  have g2 : 4*M8/B=1 := by apply floor_unique hBp <;> omega
  have e0 : a*L-s*M=Q := by
    have he : 361*(a*L-s*M-Q)=0 := by
      linear_combination
        (19*L)*ha-(19*M)*hs+(2*B-3)*h0-
        (5*B+2)*h1-19*hQ
    nlinarith only [he]
  have e1 : a*L8-s*M8= -2*Q := by
    have he : 361*(a*L8-s*M8+2*Q)=0 := by
      linear_combination
        (19*L8)*ha-(19*M8)*hs+(2*B-3)*h2-
        (5*B+2)*h3+38*hQ
    nlinarith only [he]
  refine ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    by omega,by omega,?_,?_,e0,e1⟩
  · simp [correction, f0, f1, f2]
  · simp [correction, g0, g1, g2]

theorem q_zero (r : ℕ) :
    total r (physical (degree r) (qLow r) (qMid r) 0)=0 ∧
    total r (physical (degree r) (q8Low r) (q8Mid r) 0)=0 := by
  obtain ⟨hL,hM,hL8,hM8,hp,hp8,hC,hC8,hG,hG8⟩ := q_readings r
  have hU : (0 : ℤ)≤0 ∧ (0 : ℤ)<base r := by
    have := (eighth_facts r).1
    have := (eighth_facts r).2.1
    omega
  constructor
  · rw [physical_total r _ _ _ hL hM hU, hC, mul_zero, add_zero, hG]
    ring
  · rw [physical_total r _ _ _ hL8 hM8 hU, hC8, mul_zero, add_zero, hG8]
    ring

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
