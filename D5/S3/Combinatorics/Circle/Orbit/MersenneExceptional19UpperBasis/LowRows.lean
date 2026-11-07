/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/LowRows
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis LowRows on original physical labels. -/
/- UNCOMPILED. The actual low upper rows, not an assumed boundary table.
   The d-bit readout is reduced by the proved corrected ladders. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.InternalRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Readout
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.InternalRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss eighth eighth_facts parameter_exact parameter_parities parameter_margins
    read read_succ read_congr read_sub digit block affineRange affine_digits)
open MersenneExceptional19ZeroLattice (first middle last)
open private gPoint gPoint_data fPoint fPoint_data eighth_power four_eighth_power
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
open private affine
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
open private triple
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
open private read_split read_geom_smul
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Readout
open private g_selected_read f_selected_read terminal_selected_read triple_read
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
open private digit_add_dvd two_pow_dvd
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.InternalRows

variable {A : Type*} [AddCommGroup A]

private theorem correction_low (r : ℕ) (θ : A) (p : Fin 3) (j : ℕ) (hj : j≤2) :
    correctionBlock r θ p j=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  fin_cases p <;>
    simp [correctionBlock,first,middle,last,
      show j≠degree r-3 by omega,show j≠degree r-2 by omega,
      show j≠degree r-1 by omega]

private theorem corrected_low (r : ℕ) (X : Fin (3*degree r) → A) (θ : A)
    (p : Fin 3) (j : ℕ) (hj : j≤2) : correctedBlock r X θ p j=block X p j := by
  rw [correctedBlock,correction_low r θ p j hj,sub_zero]

private theorem read_two_low (d : ℕ) (hd : 2≤d) (f : ℕ → A) (z : ℤ)
    (hz : 0≤z ∧ z<(2 : ℤ)^d)
    (hf : ∀ j, 2≤j → j<d → f j=(2 : ℤ)^(j-2) • f 2) :
    read d f z=(z%2) • f 0+(z/2%2) • f 1+(z/4) • f 2 := by
  have he : d=2+(d-2) := by omega
  conv_lhs => rw [he]
  rw [read_split]
  have htail : read (d-2) (fun i => f (2+i)) (z/(2 : ℤ)^2)=
      (z/4) • f 2 := by
    calc
      _=read (d-2) (fun i => (2 : ℤ)^i • f 2) (z/4) := by
        change read (d-2) (fun i => f (2+i)) (z/4)=_
        apply read_congr
        intro i hi
        simpa only [show 2+i-2=i by omega] using hf (2+i) (by omega) (by omega)
      _=(z/4) • f 2 := by
        apply read_geom_smul
        constructor
        · exact Int.ediv_nonneg hz.1 (by norm_num)
        · have hp : (2 : ℤ)^d=4*(2 : ℤ)^(d-2) := by rw [he,pow_add]; ring
          rw [hp] at hz
          omega
  rw [htail,read_succ,read_succ]
  simp [read]

private theorem selected_low_triples (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    block X 2 0=-block X 0 0-block X 1 0 ∧
    block X 2 1=-block X 0 1-block X 1 1 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  have t0 := terminal_selected_read r X hX 0
  have t1 := terminal_selected_read r X hX 1
  change (∑ i ∈ triple ⟨0,by omega⟩, X i)=0 at t0
  change (∑ i ∈ triple ⟨1,by omega⟩, X i)=0 at t1
  rw [triple_read] at t0 t1
  constructor
  · linear_combination (norm := abel) t0
  · linear_combination (norm := abel) t1

/-- Complete readout of an ACTUAL permitted affine row after high descent.
All floor quotients are integers. The three high coefficients have been
reduced using the proved zero-sum corrected triple at level 2. -/
private theorem affine_low_read (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) (M : ℤ) (hM : affineRange r M) :
    affineRead r X M=
      ((M+bb r)%2) • block X 0 0+((M+bb r)/2%2) • block X 0 1+
      (M%2) • block X 1 0+(M/2%2) • block X 1 1+
      ((M-aa r)%2) • block X 2 0+((M-aa r)/2%2) • block X 2 1+
      ((M+bb r)/4-(M-aa r)/4) • block X 0 2+
      (M/4-(M-aa r)/4) • block X 1 2 := by
  let θ := highTheta r X
  let Y := correctedBlock r X θ
  obtain ⟨hl,hT⟩ := selected_corrected_ladders r X hX
  obtain ⟨hL,hM',hU,hC⟩ := affine_digits r M hM
  have hp : (2 : ℤ)^degree r=(base r : ℤ) := by simp [base]
  have lo (p : Fin 3) (z : ℤ) (hz : 0≤z ∧ z<base r) :
      read (degree r) (Y p) z=(z%2) • block X p 0+(z/2%2) • block X p 1+
        (z/4) • block X p 2 := by
    have h := read_two_low (degree r) (by dsimp [degree]; omega) (Y p) z
      (by simpa only [hp] using hz) (hl p)
    simpa only [Y,corrected_low r X θ p 0 (by omega),
      corrected_low r X θ p 1 (by omega),corrected_low r X θ p 2 (by omega)] using h
  have hsum : block X 0 2+block X 1 2+block X 2 2=0 := by
    simpa only [corrected_low r X θ 0 2 le_rfl,corrected_low r X θ 1 2 le_rfl,
      corrected_low r X θ 2 2 le_rfl] using hT 2 le_rfl (by dsimp [degree]; omega)
  have hcorr := corrected_affine_read r X θ M hM
  change read (degree r) (Y 0) (M+bb r)+read (degree r) (Y 1) M+
    read (degree r) (Y 2) (M-aa r)=affineRead r X M at hcorr
  rw [lo 0 _ hL,lo 1 _ hM',lo 2 _ hU] at hcorr
  linear_combination (norm := module) -hcorr+((M-aa r)/4) • hsum

/-- The j=1 G upper difference reads F2-2*f1 after T1. This supplies F2=2*f1
without cancelling 2 in the group. -/
private theorem selected_f2 (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) : block X 0 2=(2 : ℤ) • block X 0 1 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  let θ := highTheta r X
  let Y := correctedBlock r X θ
  obtain ⟨hl,hT⟩ := selected_corrected_ladders r X hX
  have hdouble (p : Fin 3) (i : ℕ) (hi : 1<i) (hid : i<degree r) :
      Y p i=(2 : ℤ)^(i-1-1) • Y p 2 := by
    simpa only [show i-1-1=i-2 by omega] using hl p i (by omega) hid
  have hbase : affineRange r (4*eighth r) := by
    simpa only [gPoint,ite_true] using
      (gPoint_data r (degree r-1) ⟨by omega,by omega,by omega⟩).1
  have hupper := (gPoint_data r 1 ⟨by omega,by omega,by omega⟩).1
  have eg : gPoint r 1=4*eighth r+2 := by
    simp [gPoint,show 1≠degree r-1 by omega,show 1≠degree r-2 by omega]
  obtain ⟨b0,b1,b2,bC⟩ := affine_digits r _ hbase
  obtain ⟨u0,u1,u2,uC⟩ := affine_digits r _ hupper
  have step (p : Fin 3) (m m' : ℤ) (he : m'=m+2)
      (hm : 0≤m ∧ m<base r) (hm' : 0≤m' ∧ m'<base r) :
      read (degree r) (Y p) m'-read (degree r) (Y p) m=
        (1-2*digit m 1) • Y p 1+digit m 1 • Y p 2 := by
    rw [he]
    apply read_add_power _ _ _ _ (by omega)
    · simpa only [pow_one,← he,show (2 : ℤ)^degree r=(base r : ℤ) by simp [base]] using
        And.intro hm.1 hm'.2
    · exact hdouble p
  have c0 := step 0 _ _ (by rw [eg]; ring) b0 u0
  have c1 := step 1 _ _ eg b1 u1
  have c2 := step 2 _ _ (by rw [eg]; ring) b2 u2
  obtain ⟨hae,hbe,hse⟩ := parameter_exact r
  obtain ⟨hB,hE,hemod⟩ := eighth_facts r
  have ha4 : aa r%4=3 := by omega
  have hb4 : bb r%4=3 := by omega
  have bit0 : digit (4*eighth r+bb r) 1=1 := by dsimp [digit]; omega
  have bit1 : digit (4*eighth r) 1=0 := by dsimp [digit]; omega
  have bit2 : digit (4*eighth r-aa r) 1=0 := by dsimp [digit]; omega
  rw [bit0] at c0
  rw [bit1] at c1
  rw [bit2] at c2
  have gb := g_selected_read r (degree r-1) X hX ⟨by omega,by omega,by omega⟩
  simp only [gPoint,ite_true] at gb
  have gu := g_selected_read r 1 X hX ⟨by omega,by omega,by omega⟩
  have cb := corrected_affine_read r X θ _ hbase
  have cu := corrected_affine_read r X θ _ hupper
  rw [gb] at cb
  rw [gu] at cu
  have t1 := (selected_low_triples r X hX).2
  simp only [Y,corrected_low r X θ 0 1 (by omega),corrected_low r X θ 1 1 (by omega),
    corrected_low r X θ 2 1 (by omega),corrected_low r X θ 0 2 le_rfl] at c0 c1 c2
  linear_combination (norm := module) -c0-c1-c2+cu-cb-t1

/-- The three remaining ACTUAL affine readouts. Each entry is derived from
its modulo-4 digits and integer floors, not supplied as a coefficient premise. -/
theorem actual_low_row_table (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    let x := block X 0 1
    let y := block X 1 0
    let z := block X 1 1
    let G := block X 1 2
    let k := ss r/2
    let η := (aa r+1)/4
    affineRead r X (4*eighth r)=k • x+η • G-y ∧
    affineRead r X (7*eighth r-bb r)=k • x+η • G+y-z ∧
    affineRead r X (aa r)=k • x+(η-1) • G+y+z := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨hB,hE,hemod⟩ := eighth_facts r
  obtain ⟨hae,hbe,hse⟩ := parameter_exact r
  have ha4 : aa r%4=3 := by omega
  have hb4 : bb r%4=3 := by omega
  have hs4 : ss r%4=2 := by omega
  have hs : ss r=aa r+bb r := rfl
  have rb : affineRange r (4*eighth r) := by
    simpa only [gPoint,ite_true] using
      (gPoint_data r (degree r-1) ⟨by omega,by omega,by omega⟩).1
  have rf : affineRange r (7*eighth r-bb r) := by
    have ht := (fPoint_data r (degree r-3)
      ⟨by omega,by omega⟩).1
    simpa only [fPoint,
      show degree r-3≠degree r-2 by omega,ite_false,
      ← eighth_power,
      show 8*eighth r-bb r-eighth r=7*eighth r-bb r by ring] using ht
  have eb := affine_low_read r X hX _ rb
  have ef := affine_low_read r X hX _ rf
  have ea := affine_low_read r X hX _ (Or.inl rfl)
  have hbase : (4*eighth r+bb r)%2=1 ∧ (4*eighth r+bb r)/2%2=1 ∧
      (4*eighth r)%2=0 ∧ (4*eighth r)/2%2=0 ∧
      (4*eighth r-aa r)%2=1 ∧ (4*eighth r-aa r)/2%2=0 ∧
      (4*eighth r+bb r)/4-(4*eighth r-aa r)/4=(ss r-2)/4 ∧
      (4*eighth r)/4-(4*eighth r-aa r)/4=(aa r+1)/4 := by omega
  have hftop : (7*eighth r-bb r+bb r)%2=0 ∧
      (7*eighth r-bb r+bb r)/2%2=0 ∧
      (7*eighth r-bb r)%2=1 ∧ (7*eighth r-bb r)/2%2=0 ∧
      (7*eighth r-bb r-aa r)%2=0 ∧ (7*eighth r-bb r-aa r)/2%2=1 ∧
      (7*eighth r-bb r+bb r)/4-(7*eighth r-bb r-aa r)/4=(ss r+2)/4 ∧
      (7*eighth r-bb r)/4-(7*eighth r-bb r-aa r)/4=(aa r+1)/4 := by omega
  have hat : (aa r+bb r)%2=0 ∧ (aa r+bb r)/2%2=1 ∧
      aa r%2=1 ∧ aa r/2%2=1 ∧ (aa r-aa r)%2=0 ∧ (aa r-aa r)/2%2=0 ∧
      (aa r+bb r)/4-(aa r-aa r)/4=(ss r-2)/4 ∧
      aa r/4-(aa r-aa r)/4=(aa r+1)/4-1 := by omega
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩ := hbase
  obtain ⟨f0,f1,f2,f3,f4,f5,f6,f7⟩ := hftop
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩ := hat
  rw [b0,b1,b2,b3,b4,b5,b6,b7] at eb
  rw [f0,f1,f2,f3,f4,f5,f6,f7] at ef
  rw [a0,a1,a2,a3,a4,a5,a6,a7] at ea
  obtain ⟨t0,t1⟩ := selected_low_triples r X hX
  have hf2 := selected_f2 r X hX
  rw [hf2,t0] at eb
  rw [hf2,t1] at ef
  rw [hf2] at ea
  have kb : 2*((ss r-2)/4)+1=ss r/2 := by omega
  have kf : 2*((ss r+2)/4)-1=ss r/2 := by omega
  dsimp only
  refine ⟨?_,?_,?_⟩
  · calc
      _=(2*((ss r-2)/4)+1) • block X 0 1+
          ((aa r+1)/4) • block X 1 2-block X 1 0 := by
        linear_combination (norm := module) eb
      _=_ := by rw [kb]
  · calc
      _=(2*((ss r+2)/4)-1) • block X 0 1+
          ((aa r+1)/4) • block X 1 2+block X 1 0-block X 1 1 := by
        linear_combination (norm := module) ef
      _=_ := by rw [kf]
  · calc
      _=(2*((ss r-2)/4)+1) • block X 0 1+
          ((aa r+1)/4-1) • block X 1 2+block X 1 0+block X 1 1 := by
        linear_combination (norm := module) ea
      _=_ := by rw [kb]

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
