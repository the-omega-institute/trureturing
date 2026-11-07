/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis HighRows on original physical labels. -/
/- UNCOMPILED. Actual high-row bridge on the original Fin (3d) labels.
   No matrix-entry table or group equation is supplied as a hypothesis. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Readout
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base place)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss eighth eighth_facts parameter_margins physical physical_read read read_succ block)
open private gPoint fPoint hPoint eighth_power
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
open private affine
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
open private triple sum_triple triples_disjoint
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
open MersenneExceptional19Stabilizer (floor_unique)

variable {A : Type*} [AddCommGroup A]

/-- Exactly the actual selected upper indicators, evaluated in any group. -/
def SelectedAnnihilates (r : ℕ) (X : Fin (3*degree r) → A) : Prop :=
  ∀ k : UpperIndex r, (∑ i ∈ selectedMask r k, X i)=0

/-- The three actual binary words of R_M; coefficients act through Z. -/
def affineRead (r : ℕ) (X : Fin (3*degree r) → A) (M : ℤ) : A :=
  read (degree r) (block X 0) (M+bb r)+
    read (degree r) (block X 1) M+read (degree r) (block X 2) (M-aa r)

private theorem affine_sum (r : ℕ) (X : Fin (3*degree r) → A) (M : ℤ) :
    (∑ i ∈ affine r M, X i)=affineRead r X M := by
  exact physical_read (by dsimp [degree]; omega) X _ _ _

private theorem g_selected_read (r j : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X)
    (hj : 1≤j ∧ j<degree r ∧ j≠degree r-3) :
    affineRead r X (gPoint r j)=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  by_cases hs : j≤degree r-4
  · have h := hX (.inl (.inl ⟨j-1,by omega⟩))
    change (∑ i ∈ affine r (gPoint r (j-1+1)), X i)=0 at h
    rw [show j-1+1=j by omega,affine_sum] at h
    exact h
  · by_cases ht : j=degree r-2
    · subst j
      have h := hX (.inl (.inr 0))
      simpa only [selectedMask,Sum.elim_inl,Sum.elim_inr,ite_true,affine_sum] using h
    · have he : j=degree r-1 := by omega
      subst j
      have h := hX (.inl (.inr 1))
      simpa only [selectedMask,Sum.elim_inl,Sum.elim_inr,
        show (1 : Fin 2)≠0 by decide,ite_false,affine_sum] using h

private theorem f_selected_read (r j : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) (hj : 2≤j ∧ j≤degree r-2) :
    affineRead r X (fPoint r j)=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  by_cases ht : j=degree r-2
  · subst j
    have h := hX (.inr (.inl (.inr 0)))
    change (∑ i ∈ affine r (fPoint r (degree r-2)), X i)=0 at h
    rwa [affine_sum] at h
  · have h := hX (.inr (.inl (.inl ⟨j-2,by omega⟩)))
    change (∑ i ∈ affine r (fPoint r (j-2+2)), X i)=0 at h
    rwa [show j-2+2=j by omega,affine_sum] at h

private theorem h_selected_read (r j : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) (hj : 2≤j ∧ j≤degree r-3) :
    affineRead r X (hPoint r j)=0 := by
  have h := hX (.inr (.inr (.inl ⟨j-2,by have := hj.2; omega⟩)))
  change (∑ i ∈ affine r (hPoint r (j-2+2)), X i)=0 at h
  rwa [show j-2+2=j by omega,affine_sum] at h

private theorem terminal_selected_read (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) (k : Fin 8) :
    (∑ i ∈ terminalMask r k, X i)=0 := hX (.inr (.inr (.inr k)))

/-- These are quotient/remainder data of the SEVEN actual affine masks,
not a proposed row table. E=2^(d-3), so each quotient is its top three bits. -/
private theorem actual_high_quotients (r : ℕ) :
    (6*eighth r+bb r)/eighth r=7 ∧ (6*eighth r)/eighth r=6 ∧
    (6*eighth r-aa r)/eighth r=5 ∧
    (4*eighth r+bb r)/eighth r=5 ∧ (4*eighth r)/eighth r=4 ∧
    (4*eighth r-aa r)/eighth r=3 ∧
    (6*eighth r-bb r+bb r)/eighth r=6 ∧
    (6*eighth r-bb r)/eighth r=4 ∧
    (6*eighth r-bb r-aa r)/eighth r=3 ∧
    (7*eighth r-bb r+bb r)/eighth r=7 ∧
    (7*eighth r-bb r)/eighth r=5 ∧
    (7*eighth r-bb r-aa r)/eighth r=4 ∧
    (3*eighth r+aa r+bb r)/eighth r=5 ∧
    (3*eighth r+aa r)/eighth r=3 ∧ (3*eighth r)/eighth r=3 ∧
    (aa r+bb r)/eighth r=2 ∧ aa r/eighth r=0 ∧
    (aa r-aa r)/eighth r=0 ∧
    (3*eighth r+bb r)/eighth r=4 ∧
    (3*eighth r-aa r)/eighth r=2 := by
  obtain ⟨hB,hE,hmod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  have hs : ss r=aa r+bb r := rfl
  clear hB hmod
  generalize heq : eighth r = E at *
  generalize haq : aa r = a at *
  generalize hbq : bb r = b at *
  generalize hsq : ss r = s at *
  clear heq haq hbq hsq
  have hEp : 0<E := by omega
  repeat' constructor
  all_goals apply floor_unique hEp <;> omega

/-- The four ACTUAL upper-to-upper high differences. The low d-3 bits
cancel by exact powers of two; only the displayed nine coordinates remain. -/
theorem actual_high_row_differences (r : ℕ) (X : Fin (3*degree r) → A) :
    let f := block X 0
    let g := block X 1
    let h := block X 2
    affineRead r X (6*eighth r)-affineRead r X (4*eighth r)=
        f (degree r-2)+g (degree r-2)-h (degree r-2)+h (degree r-1) ∧
    affineRead r X (6*eighth r-bb r)-affineRead r X (7*eighth r-bb r)=
        -f (degree r-3)-g (degree r-3)+h (degree r-3)+
          h (degree r-2)-h (degree r-1) ∧
    affineRead r X (3*eighth r+aa r)-affineRead r X (aa r)=
        f (degree r-3)+g (degree r-3)+h (degree r-3)-f (degree r-2)+
          g (degree r-2)+h (degree r-2)+f (degree r-1) ∧
    affineRead r X (3*eighth r)-affineRead r X (4*eighth r)=
        -f (degree r-3)+g (degree r-3)-h (degree r-3)+
          g (degree r-2)-g (degree r-1) := by
  dsimp only
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,
    q15,q16,q17,q18,q19⟩ := actual_high_quotients r
  have td (p : Fin 3) (z z' q q' k : ℤ)
      (hq : z/eighth r=q) (hq' : z'/eighth r=q')
      (he : z=z'+eighth r*k) :
      read (degree r) (block X p) z-read (degree r) (block X p) z'=
        read 3 (fun i => block X p (degree r-3+i)) q-
          read 3 (fun i => block X p (degree r-3+i)) q' := by
    simpa only [Nat.sub_add_cancel (by omega : 3≤degree r),← eighth_power] using
      read_top_difference (degree r-3) (block X p) z z' q q' k
        (by simpa only [← eighth_power] using hq)
        (by simpa only [← eighth_power] using hq')
        (by simpa only [← eighth_power] using he)
  have e10 := td 0 _ _ _ _ 2 q0 q3 (by ring)
  have e11 := td 1 _ _ _ _ 2 q1 q4 (by ring)
  have e12 := td 2 _ _ _ _ 2 q2 q5 (by ring)
  have e20 := td 0 _ _ _ _ (-1) q6 q9 (by ring)
  have e21 := td 1 _ _ _ _ (-1) q7 q10 (by ring)
  have e22 := td 2 _ _ _ _ (-1) q8 q11 (by ring)
  have e30 := td 0 _ _ _ _ 3 q12 q15 (by ring)
  have e31 := td 1 _ _ _ _ 3 q13 q16 (by ring)
  have e32 := td 2 _ _ _ _ 3 q14 q17 (by ring)
  have e40 := td 0 _ _ _ _ (-1) q18 q3 (by ring)
  have e41 := td 1 _ _ _ _ (-1) q14 q4 (by ring)
  have e42 := td 2 _ _ _ _ (-1) q19 q5 (by ring)
  have hi1 : degree r-3+1=degree r-2 := by omega
  have hi2 : degree r-3+2=degree r-1 := by omega
  have rz (f : ℕ → A) (z : ℤ) : read 0 f z=0 := by
    simp [MersenneExceptional19PermutationStabilizer.read]
  norm_num [read_succ 2,read_succ 1,read_succ 0,rz,
    MersenneExceptional19PermutationStabilizer.digit,hi1,hi2]
    at e10 e11 e12 e20 e21 e22 e30 e31 e32 e40 e41 e42
  dsimp only [affineRead]
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (norm := abel) e10+e11+e12
  · linear_combination (norm := abel) e20+e21+e22
  · linear_combination (norm := abel) e30+e31+e32
  · linear_combination (norm := abel) e40+e41+e42

private theorem triple_read (r : ℕ) (X : Fin (3*degree r) → A)
    (j : Fin (degree r)) :
    (∑ i ∈ triple j, X i)=block X 0 j.val+block X 1 j.val+block X 2 j.val := by
  have h := sum_triple (by dsimp [degree]; omega : 0<degree r) X j
  simpa only [block,dif_pos j.isLt] using h

/-- Six selected rows force the corrected high geometric progression over
EVERY abelian group. The union terminal is evaluated as one disjoint mask. -/
theorem selected_high_normal_form (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    let p := block X 0 (degree r-3)
    let t := block X 1 (degree r-2)-block X 1 (degree r-3)
    let θ := (2 : ℤ) • block X 1 (degree r-3)-block X 1 (degree r-2)
    block X 1 (degree r-3)=t+θ ∧ block X 2 (degree r-3)=-p-t ∧
    block X 0 (degree r-2)=(2 : ℤ) • p ∧
    block X 1 (degree r-2)=(2 : ℤ) • t+θ ∧
    block X 2 (degree r-2)=-(2 : ℤ) • p-(2 : ℤ) • t-θ ∧
    block X 0 (degree r-1)=(4 : ℤ) • p-θ ∧
    block X 1 (degree r-1)=(4 : ℤ) • t+(2 : ℤ) • θ ∧
    block X 2 (degree r-1)=-(4 : ℤ) • p-(4 : ℤ) • t-(2 : ℤ) • θ := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  have hb := g_selected_read r (degree r-1) X hX ⟨by omega,by omega,by omega⟩
  have hg := g_selected_read r (degree r-2) X hX ⟨by omega,by omega,by omega⟩
  have hf := f_selected_read r (degree r-2) X hX ⟨by omega,by omega⟩
  have hft := f_selected_read r (degree r-3) X hX ⟨by omega,by omega⟩
  have hht := h_selected_read r (degree r-3) X hX ⟨by omega,by omega⟩
  have ha := terminal_selected_read r X hX 4
  have h3 := terminal_selected_read r X hX 5
  change (∑ i ∈ affine r (aa r), X i)=0 at ha
  change (∑ i ∈ affine r (3*eighth r), X i)=0 at h3
  rw [affine_sum] at ha h3
  have he := eighth_power r
  simp only [gPoint,ite_true] at hb
  simp only [gPoint,show degree r-2≠degree r-1 by omega,ite_false,ite_true] at hg
  simp only [fPoint,ite_true] at hf
  simp only [fPoint,show degree r-3≠degree r-2 by omega,ite_false,← he,
    show 8*eighth r-bb r-eighth r=7*eighth r-bb r by ring] at hft
  simp only [hPoint,← he,
    show 4*eighth r+aa r-eighth r=3*eighth r+aa r by ring] at hht
  obtain ⟨e1,e2,e3,e4⟩ := actual_high_row_differences r X
  rw [hg,hb] at e1
  rw [hf,hft] at e2
  rw [hht,ha] at e3
  rw [h3,hb] at e4
  have e5 := terminal_selected_read r X hX 2
  change (∑ i ∈ triple ⟨degree r-2,by omega⟩, X i)=0 at e5
  rw [triple_read] at e5
  have e6 := terminal_selected_read r X hX 3
  change (∑ i ∈ triple ⟨degree r-3,by omega⟩ ∪
    triple ⟨degree r-1,by omega⟩, X i)=0 at e6
  rw [Finset.sum_union (triples_disjoint (by omega) _ _ (by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_mk] at this
    omega)),triple_read,triple_read] at e6
  simp only [sub_self,Fin.val_mk] at e1 e2 e3 e4 e5 e6
  have hu : block X 0 (degree r-2)=(2 : ℤ) • block X 0 (degree r-3) := by
    linear_combination (norm := module) -e2+e3-e4+e6
  dsimp only
  refine ⟨by module,?_,hu,by module,?_,?_,?_,?_⟩
  · linear_combination (norm := module) -e1-e3+e4-e6
  · linear_combination (norm := module) e2-e3+e4+e5-e6
  · linear_combination (norm := module) e1-(2 : ℤ) • e2+(2 : ℤ) • e3-(3 : ℤ) • e4-e5+(3 : ℤ) • e6
  · linear_combination (norm := module) e1+e3+e6
  · linear_combination (norm := module) -e1+(2 : ℤ) • e2-(2 : ℤ) • e3+(2 : ℤ) • e4+e5-(2 : ℤ) • e6

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
