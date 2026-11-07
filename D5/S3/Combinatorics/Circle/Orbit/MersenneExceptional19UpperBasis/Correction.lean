/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis Correction on original physical labels. -/
/- UNCOMPILED. The C*theta correction is read in INTEGER coefficients first.
   Reuses the sealed general physical readout; no cancellation in A. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Readings

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss eighth read read_sub block correction top_digits affineRange affine_digits)
open MersenneExceptional19ZeroLattice (first middle last)
open private read_first read_middle read_last
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Readings

variable {A : Type*} [AddCommGroup A]

/-- Exactly the six nonzero coefficients of C*theta. Existing physical normal
form functions are reused with all geometric generators zero. -/
def correctionBlock (r : ℕ) (θ : A) (p : Fin 3) (j : ℕ) : A :=
  if p=0 then first (degree r) 0 0 0 θ j
  else if p=1 then middle (degree r) 0 θ j
  else last (degree r) 0 0 0 0 θ j

def correctedBlock (r : ℕ) (X : Fin (3*degree r) → A) (θ : A)
    (p : Fin 3) (j : ℕ) : A := block X p j-correctionBlock r θ p j

def highTheta (r : ℕ) (X : Fin (3*degree r) → A) : A :=
  (2 : ℤ) • block X 1 (degree r-3)-block X 1 (degree r-2)

/-- Actual C-incidence on any valid three-word physical mask. This equality
is proved by binary readout in Z before any use with arbitrary A. -/
theorem physical_correction_read (r : ℕ) (θ : A) (L M U : ℤ)
    (hL : 0≤L ∧ L<base r) (hM : 0≤M ∧ M<base r)
    (hU : 0≤U ∧ U<base r) :
    read (degree r) (correctionBlock r θ 0) L+
      read (degree r) (correctionBlock r θ 1) M+
      read (degree r) (correctionBlock r θ 2) U=
        correction (base r) L M U • θ := by
  have hd : 3≤degree r := by dsimp [degree]; omega
  have hp : (2 : ℤ)^degree r=(base r : ℤ) := by simp [base]
  have hL' : 0≤L ∧ L<(2 : ℤ)^degree r := by simpa [hp] using hL
  have hM' : 0≤M ∧ M<(2 : ℤ)^degree r := by simpa [hp] using hM
  have hU' : 0≤U ∧ U<(2 : ℤ)^degree r := by simpa [hp] using hU
  simp only [correctionBlock,ite_true,show (1 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false]
  rw [read_first _ hd 0 0 0 θ L hL',read_middle _ hd 0 θ M hM',
    read_last _ hd 0 0 0 0 θ U hU']
  obtain ⟨l2,l4,l8⟩ := top_digits (degree r) hd L hL'.1 hL'.2
  obtain ⟨m2,m4,m8⟩ := top_digits (degree r) hd M hM'.1 hM'.2
  obtain ⟨u2,u4,u8⟩ := top_digits (degree r) hd U hU'.1 hU'.2
  rw [hp] at l2 m4 m8 u4
  simp only [correction,l2,m8,m4,u4]
  module

/-- In particular C dot R_M=0 in Z for every permitted affine row. The
physical digit theorem already proves the integer correction is zero, so
there is no need to cancel Q or any integer scalar inside the target group. -/
theorem affine_correction_integer_zero (r : ℕ) (M : ℤ) (hM : affineRange r M) :
    read (degree r) (correctionBlock r (1 : ℤ) 0) (M+bb r)+
      read (degree r) (correctionBlock r (1 : ℤ) 1) M+
      read (degree r) (correctionBlock r (1 : ℤ) 2) (M-aa r)=0 := by
  obtain ⟨hL,hM',hU,hC⟩ := affine_digits r M hM
  rw [physical_correction_read r 1 _ _ _ hL hM' hU,hC,zero_smul]

/-- Subtracting the actual correction preserves every permitted affine
readout. This is used for selected UPPER rows only in the descent. -/
theorem corrected_affine_read (r : ℕ) (X : Fin (3*degree r) → A)
    (θ : A) (M : ℤ) (hM : affineRange r M) :
    read (degree r) (correctedBlock r X θ 0) (M+bb r)+
      read (degree r) (correctedBlock r X θ 1) M+
      read (degree r) (correctedBlock r X θ 2) (M-aa r)=affineRead r X M := by
  obtain ⟨hL,hM',hU,hC⟩ := affine_digits r M hM
  have hc := physical_correction_read r θ _ _ _ hL hM' hU
  have hci := affine_correction_integer_zero r M hM
  rw [physical_correction_read r (1 : ℤ) _ _ _ hL hM' hU,
    smul_eq_mul,mul_one] at hci
  rw [hci,zero_smul] at hc
  simp only [correctedBlock,read_sub,affineRead]
  linear_combination (norm := abel) -hc

/-- The high starting condition for the actual descending induction. -/
theorem selected_corrected_high (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    let Y := correctedBlock r X (highTheta r X)
    (∀ p, Y p (degree r-2)=(2 : ℤ) • Y p (degree r-3)) ∧
    (∀ p, Y p (degree r-1)=(4 : ℤ) • Y p (degree r-3)) ∧
    Y 0 (degree r-3)+Y 1 (degree r-3)+Y 2 (degree r-3)=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := selected_high_normal_form r X hX
  dsimp only at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  have hn0 : degree r-3≠0 := by omega
  have hn1 : degree r-2≠0 := by omega
  have hn2 : degree r-1≠0 := by omega
  have hn01 : degree r-3≠degree r-2 := by omega
  have hn02 : degree r-3≠degree r-1 := by omega
  have hn12 : degree r-2≠degree r-1 := by omega
  refine ⟨?_,?_,?_⟩
  · intro p
    fin_cases p <;>
      simp only [correctedBlock,correctionBlock,first,middle,last,
        ite_true,show (1 : Fin 3)≠0 by decide,show (2 : Fin 3)≠0 by decide,
        show (2 : Fin 3)≠1 by decide,ite_false,if_neg hn0,if_neg hn1,
        if_neg hn01,if_neg hn02,if_neg hn12,
        if_neg (Ne.symm hn01),zero_smul,sub_zero,zero_add,add_zero,sub_self] <;>
      dsimp only [highTheta]
    · exact h2
    · linear_combination (norm := module) h3-(2 : ℤ) • h0
    · linear_combination (norm := module) h4-(2 : ℤ) • h1
  · intro p
    fin_cases p <;>
      simp only [correctedBlock,correctionBlock,first,middle,last,
        ite_true,show (1 : Fin 3)≠0 by decide,show (2 : Fin 3)≠0 by decide,
        show (2 : Fin 3)≠1 by decide,ite_false,if_neg hn0,if_neg hn2,
        if_neg hn01,if_neg hn02,if_neg (Ne.symm hn02),if_neg (Ne.symm hn12),
        zero_smul,sub_zero,zero_add,add_zero,sub_self] <;>
      dsimp only [highTheta]
    · linear_combination (norm := module) h5
    · linear_combination (norm := module) h6-(4 : ℤ) • h0
    · linear_combination (norm := module) h7-(4 : ℤ) • h1
  · simp only [correctedBlock,correctionBlock,first,middle,last,
      ite_true,show (1 : Fin 3)≠0 by decide,show (2 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠1 by decide,ite_false,if_neg hn0,
      if_neg hn01,if_neg hn02,zero_smul,sub_zero,zero_add,add_zero,sub_self]
    dsimp only [highTheta]
    linear_combination (norm := module) h0+h1

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
