/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Reconstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis Reconstruction on original physical labels. -/
/- UNCOMPILED. Torsion-safe arbitrary-group reconstruction for the ACTUAL
   upper-only family. No determinant, span, rank or certificate premise. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.LowRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base place Qmask)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss eighth eighth_facts parameter_exact parameter_parities read block
    physical_read qLow qMid q8Low q8Mid q_readings)
open MersenneExceptional19ZeroLattice (first middle last integral_read primitive phaseWeight)
open private primitive_place forall_place scaled_first scaled_middle scaled_last
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
open private gPoint fPoint eighth_power
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
open private q_digits_exact affine
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
open private g_selected_read f_selected_read terminal_selected_read affine_sum
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
open private selected_low_triples selected_f2 corrected_low
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.LowRows

variable {A : Type*} [AddCommGroup A]

/-- The physical low table completes the geometric part of the normal form.
The first coordinate still has its separate generator u, pending the Q rows. -/
private theorem selected_four_parameter_form (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    let u := block X 0 0
    let x := block X 0 1
    let y := block X 1 0
    let θ := highTheta r X
    (∀ j, j < degree r → block X 0 j=first (degree r) u x 0 θ j) ∧
    (∀ j, j < degree r → block X 1 j=middle (degree r) y θ j) ∧
    (∀ j, j < degree r → block X 2 j=last (degree r) u x y 0 θ j) ∧
    (ss r/2) • x+aa r • y=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨eb,ef,ea⟩ := actual_low_row_table r X hX
  have zb := g_selected_read r (degree r-1) X hX ⟨by omega,by omega,by omega⟩
  simp only [gPoint,ite_true] at zb
  have zf := f_selected_read r (degree r-3) X hX ⟨by omega,by omega⟩
  simp only [fPoint,show degree r-3≠degree r-2 by omega,ite_false,
    ← eighth_power,show 8*eighth r-bb r-eighth r=7*eighth r-bb r by ring] at zf
  have za := terminal_selected_read r X hX 4
  change (∑ i ∈ affine r (aa r), X i)=0 at za
  rw [affine_sum] at za
  rw [zb] at eb
  rw [zf] at ef
  rw [za] at ea
  dsimp only at eb ef ea ⊢
  have hz : block X 1 1=(2 : ℤ) • block X 1 0 := by
    linear_combination (norm := module) ef-eb
  have hG : block X 1 2=(4 : ℤ) • block X 1 0 := by
    linear_combination (norm := module) ea-eb+hz
  obtain ⟨hae,hbe,hse⟩ := parameter_exact r
  obtain ⟨hB,hE,hmod⟩ := eighth_facts r
  have ha4 : aa r%4=3 := by omega
  have hη : 4*((aa r+1)/4)-1=aa r := by omega
  have slope : (ss r/2) • block X 0 1+aa r • block X 1 0=0 := by
    calc
      _=(ss r/2) • block X 0 1+
          (4*((aa r+1)/4)-1) • block X 1 0 := by rw [hη]
      _=(ss r/2) • block X 0 1+
          ((aa r+1)/4) • ((4 : ℤ) • block X 1 0)-block X 1 0 := by module
      _=0 := by rw [← hG]; exact eb.symm
  have hF := selected_f2 r X hX
  obtain ⟨ht0,ht1⟩ := selected_low_triples r X hX
  obtain ⟨hl,hT⟩ := selected_corrected_ladders r X hX
  have ht2 : block X 2 2=-(2 : ℤ) • block X 0 1-(4 : ℤ) • block X 1 0 := by
    have h := hT 2 le_rfl (by omega)
    simp only [corrected_low r X (highTheta r X) 0 2 le_rfl,
      corrected_low r X (highTheta r X) 1 2 le_rfl,
      corrected_low r X (highTheta r X) 2 2 le_rfl,hF,hG] at h
    linear_combination (norm := module) h
  have high (p : Fin 3) (j : ℕ) (hj : 2≤j) (hjd : j < degree r) :
      block X p j=(2 : ℤ)^(j-2) • block X p 2+
        correctionBlock r (highTheta r X) p j := by
    have h := hl p j hj hjd
    rw [corrected_low r X (highTheta r X) p 2 le_rfl] at h
    change block X p j-correctionBlock r (highTheta r X) p j=_ at h
    linear_combination (norm := abel) h
  refine ⟨?_,?_,?_,slope⟩
  · intro j hjd
    by_cases h0 : j=0
    · subst j
      simp [first,show (0 : ℕ)≠degree r-1 by omega]
    by_cases h1 : j=1
    · subst j
      simp [first,show (1 : ℕ)≠degree r-1 by omega]
    have hp : (2 : ℤ)^(j-1)=(2 : ℤ)^(j-2)*2 := by
      rw [show j-1=(j-2)+1 by omega,pow_succ]
    rw [high 0 j (by omega) hjd,hF]
    simp only [correctionBlock,ite_true,first,if_neg h0,smul_zero,zero_add]
    rw [hp]
    split_ifs <;> module
  · intro j hjd
    by_cases h0 : j=0
    · subst j
      simp [middle,show (0 : ℕ)≠degree r-3 by omega,
        show (0 : ℕ)≠degree r-2 by omega,show (0 : ℕ)≠degree r-1 by omega]
    by_cases h1 : j=1
    · subst j
      simpa [middle,show (1 : ℕ)≠degree r-3 by omega,
        show (1 : ℕ)≠degree r-2 by omega,show (1 : ℕ)≠degree r-1 by omega] using hz
    have hp : (2 : ℤ)^j=(2 : ℤ)^(j-2)*4 := by
      calc
        (2 : ℤ)^j=(2 : ℤ)^((j-2)+2) := by congr 1; omega
        _=(2 : ℤ)^(j-2)*4 := by rw [pow_add]; norm_num
    rw [high 1 j (by omega) hjd,hG]
    simp only [correctionBlock,show (1 : Fin 3)≠0 by decide,ite_false,ite_true,
      middle,smul_zero,zero_add]
    rw [hp]
    module
  · intro j hjd
    by_cases h0 : j=0
    · subst j
      simpa [last,show (0 : ℕ)≠degree r-2 by omega,
        show (0 : ℕ)≠degree r-1 by omega] using ht0
    by_cases h1 : j=1
    · subst j
      rw [hz] at ht1
      simpa [last,show (1 : ℕ)≠degree r-2 by omega,
        show (1 : ℕ)≠degree r-1 by omega] using ht1
    have hp : (2 : ℤ)^(j-1)=(2 : ℤ)^(j-2)*2 := by
      rw [show j-1=(j-2)+1 by omega,pow_succ]
    rw [high 2 j (by omega) hjd,ht2]
    simp only [correctionBlock,show (2 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠1 by decide,ite_false,last,if_neg h0,smul_zero,
      neg_zero,sub_zero,zero_sub,zero_add]
    rw [hp]
    split_ifs <;> module

/-- Actual terminal coefficient identities, derived uniformly from their
sealed digit definitions. These are identities in Z, not finite controls. -/
private theorem terminal_coefficients (r : ℕ) :
    2*qLow r+q8Low r=5*ss r ∧ 2*qMid r+q8Mid r=5*aa r ∧
    2*(ss r/2)=ss r ∧ 2*ss r-5*aa r=1 ∧
    2*(qLow r/2)+q8Low r/2-5*(ss r/2)= -1 := by
  obtain ⟨q0,q1,q2,q3⟩ := q_digits_exact r
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  obtain ⟨hap,hbp,hsp⟩ := parameter_parities r
  obtain ⟨hL,hM,hL8,hM8,hp,hp8,hC,hC8,hG,hG8⟩ := q_readings r
  omega

/-- Torsion-safe reconstruction in every AddCommGroup on ALL original
physical labels. Its sole presentation hypothesis is the ACTUAL selected
upper family; in particular no all-zero annihilator premise is imported. -/
theorem actual_selected_upper_reconstruction (r : ℕ)
    (X : Fin (3*degree r) → A) (hX : SelectedAnnihilates r X)
    (i : Fin (3*degree r)) :
    X i=primitive r i •
      ((-3 : ℤ) • X (place 0 ⟨0,by dsimp [degree]; omega⟩)+
        (2 : ℤ) • X (place 2 ⟨0,by dsimp [degree]; omega⟩)) := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  let u := block X 0 0
  let x := block X 0 1
  let y := block X 1 0
  let θ := highTheta r X
  obtain ⟨hf,hg,hh,slope⟩ := selected_four_parameter_form r X hX
  change (ss r/2) • x+aa r • y=0 at slope
  have hread := integral_read r X u x y 0 θ hf hg hh
  obtain ⟨hL,hM,hL8,hM8,hp,hp8,hC,hC8,hG,hG8⟩ := q_readings r
  have hU : (0 : ℤ)≤0 ∧ (0 : ℤ)<base r := by
    obtain ⟨hB,hE,hmod⟩ := eighth_facts r
    omega
  have eqQ := terminal_selected_read r X hX 6
  have eq8 := terminal_selected_read r X hX 7
  change (∑ i ∈ MersenneExceptional19PermutationStabilizer.physical
    (degree r) (qLow r) (qMid r) 0, X i)=0 at eqQ
  change (∑ i ∈ MersenneExceptional19PermutationStabilizer.physical
    (degree r) (q8Low r) (q8Mid r) 0, X i)=0 at eq8
  rw [physical_read (by omega)] at eqQ eq8
  have nq := hread (qLow r) (qMid r) 0 hL hM hU
  have n8 := hread (q8Low r) (q8Mid r) 0 hL8 hM8 hU
  rw [eqQ,hp,hC] at nq
  rw [eq8,hp8,hC8] at n8
  simp only [Int.zero_emod,Int.zero_ediv,Int.mul_zero,sub_zero,zero_smul,smul_zero,
    one_smul,zero_add,add_zero,neg_one_zsmul] at nq n8
  have eqQ' : u+(qLow r/2) • x+qMid r • y-θ=0 := by
    linear_combination (norm := module) -nq
  have eq8' : (q8Low r/2) • x+q8Mid r • y+(2 : ℤ) • θ=0 := by
    linear_combination (norm := module) -n8
  obtain ⟨cL,cM,ck,cunit,cx⟩ := terminal_coefficients r
  have xunit : (2 : ℤ) • u-x=0 := by
    calc
      _=(2 : ℤ) • u+
          (2*(qLow r/2)+q8Low r/2-5*(ss r/2)) • x+
          (2*qMid r+q8Mid r-5*aa r) • y := by
        rw [cx,cM]
        module
      _=(2 : ℤ) • (u+(qLow r/2) • x+qMid r • y-θ)+
          ((q8Low r/2) • x+q8Mid r • y+(2 : ℤ) • θ)-
          (5 : ℤ) • ((ss r/2) • x+aa r • y) := by module
      _=0 := by rw [eqQ',eq8',slope]; simp
  have hxu : x=(2 : ℤ) • u := (sub_eq_zero.mp xunit).symm
  have R : ss r • u+aa r • y=0 := by
    calc
      _=(ss r/2) • x+aa r • y := by rw [hxu,smul_smul,ck]
      _=0 := slope
  let c : A := -(5 : ℤ) • u-(2 : ℤ) • y
  have hu : u=aa r • c := by
    calc
      u=(2*ss r-5*aa r) • u := by rw [cunit]; simp
      _=(-5*aa r) • u+(-2*aa r) • y := by
        linear_combination (norm := module) (2 : ℤ) • R
      _=aa r • c := by dsimp [c]; module
  have hy : y=(-ss r) • c := by
    calc
      y=(2*ss r-5*aa r) • y := by rw [cunit]; simp
      _=(5*ss r) • u+(2*ss r) • y := by
        linear_combination (norm := module) (-5 : ℤ) • R
      _=(-ss r) • c := by dsimp [c]; module
  have hx : x=(2*aa r) • c := by rw [hxu,hu]; module
  have hθ : θ=(Qmask r : ℤ) • c := by
    have hodd : qLow r=2*(qLow r/2)+1 := by omega
    calc
      θ=u+(qLow r/2) • x+qMid r • y := by
        linear_combination (norm := abel) -eqQ'
      _=(aa r*(2*(qLow r/2)+1)-ss r*qMid r) • c := by
        rw [hu,hx,hy]
        module
      _=(aa r*qLow r-ss r*qMid r) • c := by rw [← hodd]
      _=(Qmask r : ℤ) • c := by rw [hG]
  have at_place (p : Fin 3) (j : Fin (degree r)) :
      X (place p j)=primitive r (place p j) • c := by
    rw [primitive_place]
    fin_cases p
    · have h := hf j.val j.isLt
      rw [hu,hx,hθ] at h
      simp only [block,dif_pos j.isLt] at h
      exact h.trans (scaled_first r c j.val)
    · have h := hg j.val j.isLt
      rw [hy,hθ] at h
      simp only [block,dif_pos j.isLt] at h
      exact h.trans (scaled_middle r c j.val)
    · have h := hh j.val j.isLt
      rw [hu,hx,hy,hθ] at h
      simp only [block,dif_pos j.isLt] at h
      exact h.trans (scaled_last r c j.val)
  have every : ∀ i, X i=primitive r i • c :=
    forall_place r (fun i => X i=primitive r i • c) at_place
  have hc : (-3 : ℤ) • X (place 0 ⟨0,by omega⟩)+
      (2 : ℤ) • X (place 2 ⟨0,by omega⟩)=c := by
    have ht0 := (selected_low_triples r X hX).1
    change block X 2 0= -u-y at ht0
    change (-3 : ℤ) • u+(2 : ℤ) • block X 2 0=c
    rw [ht0]
    dsimp [c]
    module
  rw [hc]
  exact every i

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
