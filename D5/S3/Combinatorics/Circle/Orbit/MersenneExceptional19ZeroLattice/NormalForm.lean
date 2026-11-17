/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/NormalForm
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm]
   utility: none
   digest: Integral exceptional19 ZeroLattice NormalForm on original physical labels. -/
/- Source candidate only: UNCOMPILED. The shared-helper delta is required.
Ordinary provenance is stated in the owning Result Scribe. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
public import Mathlib.Tactic.Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree)
open MersenneExceptional19PermutationStabilizer
  (block Annihilates carry carry_step g_equation f_equation h_equation
    triple_equations geom_sum)

variable {A : Type*} [AddCommGroup A]

/-- The low digit has its own generator; no halving of a group element. -/
def first (d : ℕ) (u x ρ θ : A) (j : ℕ) : A :=
  (if j=0 then u else (2 : ℤ)^(j-1) • x) +
    (if j=d-1 then ρ-θ else 0)

def middle (d : ℕ) (y θ : A) (j : ℕ) : A :=
  (2 : ℤ)^j • y + (if j=d-3 then θ else 0) +
    (if j=d-2 then θ else 0) + (if j=d-1 then (2 : ℤ) • θ else 0)

def last (d : ℕ) (u x y ρ θ : A) (j : ℕ) : A :=
  (if j=0 then -u-y else (2 : ℤ)^(j-1) • (-x-(2 : ℤ) • y)) -
    (if j=d-2 then θ else 0) - (if j=d-1 then ρ+(2 : ℤ) • θ else 0)

private theorem prefix_zsmul (f : ℕ → A) (y : A) (m : ℕ)
    (hf : ∀ j, j<m → f j=(2 : ℤ)^j • y) :
    (∑ i : Fin m, f i.val)=((2 : ℤ)^m-1) • y := by
  calc
    (∑ i : Fin m, f i.val)=(∑ i : Fin m, (2 : ℤ)^i.val • y) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hf i.val i.isLt
    _=(∑ i : Fin m, (2 : ℤ)^i.val) • y := by rw [Finset.sum_smul]
    _=((2 : ℤ)^m-1) • y := by rw [geom_sum]

/-- Integral elimination from the actual zero masks. Valid in every abelian
 group, including arbitrary torsion. The high coordinates are exhaustive. -/
theorem integral_normal_form (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : Annihilates r X) :
    ∃ u x y ρ θ : A,
      (∀ j, j<degree r → block X 0 j=first (degree r) u x ρ θ j) ∧
      (∀ j, j<degree r → block X 1 j=middle (degree r) y θ j) ∧
      (∀ j, j<degree r → block X 2 j=last (degree r) u x y ρ θ j) := by
  let d := degree r
  let f := block X 0
  let g := block X 1
  let h := block X 2
  have hd : 12≤d := by dsimp [d,degree]; omega
  obtain ⟨t0,t1,t2,t3⟩ := triple_equations r X hX
  change f 0+g 0+h 0=0 at t0
  change f 1+g 1+h 1=0 at t1
  change f (d-2)+g (d-2)+h (d-2)=0 at t2
  change (f (d-3)+g (d-3)+h (d-3))+
    (f (d-1)+g (d-1)+h (d-1))=0 at t3
  have gg (j : ℕ) (hj : 1≤j ∧ j<d ∧ j≠d-3) :
      f 0+carry g j+h 0=0 := g_equation r X hX j hj
  have ff (j : ℕ) (hj : 2≤j ∧ j≤d-2) :
      carry f j+g 0+carry h 1=0 := f_equation r X hX j hj
  have hh (j : ℕ) (hj : 2≤j ∧ j≤d-3) :
      carry f 1+g 0+carry h j=0 := h_equation r X hX j hj
  have gg1 := gg 1 ⟨by omega,by omega,by omega⟩
  have gg1' : g 1=(2 : ℤ) • g 0 := by
    simp only [carry, Fin.sum_univ_one, Fin.val_zero] at gg1
    linear_combination (norm := module) gg1-t0
  have gr (j : ℕ) (hj : 1≤j ∧ j+1≤d-4) : g (j+1)=(2 : ℤ) • g j := by
    have h0 := gg j ⟨hj.1,by omega,by omega⟩
    have h1 := gg (j+1) ⟨by omega,by omega,by omega⟩
    have hc := carry_step g j
    linear_combination (norm := abel) h1-h0-hc
  have fr2 : f 2=(2 : ℤ) • f 1 := by
    have hF := ff 2 ⟨by omega,by omega⟩
    simp only [carry, Fin.sum_univ_two, Fin.sum_univ_one,
      Fin.val_zero, Fin.val_one] at hF gg1
    linear_combination (norm := module) hF+gg1-t1
  have hr2 : h 2=(2 : ℤ) • h 1 := by
    have hH := hh 2 ⟨by omega,by omega⟩
    simp only [carry, Fin.sum_univ_two, Fin.sum_univ_one,
      Fin.val_zero, Fin.val_one] at hH gg1
    linear_combination (norm := module) hH+gg1-t1
  have fr (j : ℕ) (hj : 2≤j ∧ j+1≤d-2) : f (j+1)=(2 : ℤ) • f j := by
    have h0 := ff j ⟨hj.1,by omega⟩
    have h1 := ff (j+1) ⟨by omega,hj.2⟩
    have hc := carry_step f j
    linear_combination (norm := abel) h1-h0-hc
  have hr (j : ℕ) (hj : 2≤j ∧ j+1≤d-3) : h (j+1)=(2 : ℤ) • h j := by
    have h0 := hh j ⟨hj.1,by omega⟩
    have h1 := hh (j+1) ⟨by omega,hj.2⟩
    have hc := carry_step h j
    linear_combination (norm := abel) h1-h0-hc
  let u := f 0
  let x := f 1
  let y := g 0
  let z := -x-(2 : ℤ) • y
  have hzero : h 0= -u-y := by
    dsimp [u,y]
    linear_combination (norm := abel) t0
  have hone : h 1=z := by
    dsimp [z,x,y]
    linear_combination (norm := module) t1-gg1'
  have g_low (j : ℕ) (hj : j≤d-4) : g j=(2 : ℤ)^j • y := by
    induction j with
    | zero => simp [y]
    | succ j ih =>
        by_cases hj0 : j=0
        · subst j; simpa [y] using gg1'
        · rw [gr j ⟨by omega,hj⟩, ih (by omega), pow_succ]
          module
  have f_low (j : ℕ) (hj : 1≤j ∧ j≤d-2) : f j=(2 : ℤ)^(j-1) • x := by
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hj0 : j=0
        · subst j; simp [x]
        by_cases hj1 : j=1
        · subst j; simpa [x] using fr2
        · rw [fr j ⟨by omega,hj.2⟩, ih ⟨by omega,by omega⟩]
          have hp : (2 : ℤ)^j=2*2^(j-1) := by
            calc
              (2 : ℤ)^j=(2 : ℤ)^((j-1)+1) := by congr 1; omega
              _=2*2^(j-1) := by rw [pow_succ]; ring
          simp only [Nat.add_sub_cancel]
          rw [hp]
          module
  have h_low (j : ℕ) (hj : 1≤j ∧ j≤d-3) : h j=(2 : ℤ)^(j-1) • z := by
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hj0 : j=0
        · subst j; simpa using hone
        by_cases hj1 : j=1
        · subst j; simpa [hone] using hr2
        · rw [hr j ⟨by omega,hj.2⟩, ih ⟨by omega,by omega⟩]
          have hp : (2 : ℤ)^j=2*2^(j-1) := by
            calc
              (2 : ℤ)^j=(2 : ℤ)^((j-1)+1) := by congr 1; omega
              _=2*2^(j-1) := by rw [pow_succ]; ring
          simp only [Nat.add_sub_cancel]
          rw [hp]
          module
  let θ := g (d-3)-(2 : ℤ)^(d-3) • y
  let ρ := f (d-1)-(2 : ℤ)^(d-2) • x+θ
  have g3 : g (d-3)=(2 : ℤ)^(d-3) • y+θ := by dsimp [θ]; abel
  have sum3 : (∑ i : Fin (d-3), g i.val)=((2 : ℤ)^(d-3)-1) • y :=
    prefix_zsmul g y (d-3) (fun j hj => g_low j (by omega))
  have sum2 : (∑ i : Fin (d-2), g i.val)=((2 : ℤ)^(d-2)-1) • y+θ := by
    rw [show d-2=(d-3)+1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sum3, g3, pow_succ]
    module
  have g2 : g (d-2)=(2 : ℤ)^(d-2) • y+θ := by
    have he := gg (d-2) ⟨by omega,by omega,by omega⟩
    dsimp [carry] at he
    rw [sum2] at he
    dsimp only [y] at he ⊢
    linear_combination (norm := module) he-t0
  have sum1 : (∑ i : Fin (d-1), g i.val)=
      ((2 : ℤ)^(d-1)-1) • y+(2 : ℤ) • θ := by
    rw [show d-1=(d-2)+1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sum2, g2, pow_succ]
    module
  have g1 : g (d-1)=(2 : ℤ)^(d-1) • y+(2 : ℤ) • θ := by
    have he := gg (d-1) ⟨by omega,by omega,by omega⟩
    dsimp [carry] at he
    rw [sum1] at he
    dsimp only [y] at he ⊢
    linear_combination (norm := module) he-t0
  have hp23 : (2 : ℤ)^(d-2)=2*2^(d-3) := by
    rw [show d-2=(d-3)+1 by omega, pow_succ]; ring
  have hp34 : (2 : ℤ)^(d-3)=2*2^(d-4) := by
    rw [show d-3=(d-4)+1 by omega, pow_succ]; ring
  have h2 : h (d-2)=(2 : ℤ)^(d-3) • z-θ := by
    rw [f_low (d-2) ⟨by omega,by omega⟩, g2] at t2
    simp only [show d-2-1=d-3 by omega, hp23] at t2
    dsimp [z]
    linear_combination (norm := module) t2
  have f1 : f (d-1)=(2 : ℤ)^(d-2) • x+ρ-θ := by dsimp [ρ]; abel
  have h1 : h (d-1)=(2 : ℤ)^(d-2) • z-ρ-(2 : ℤ) • θ := by
    rw [f_low (d-3) ⟨by omega,by omega⟩, g3,
      h_low (d-3) ⟨by omega,by omega⟩, f1, g1] at t3
    simp only [show d-3-1=d-4 by omega, hp34] at t3
    have hp12 : (2 : ℤ)^(d-1)=2*2^(d-2) := by
      rw [show d-1=(d-2)+1 by omega, pow_succ]; ring
    rw [hp12] at t3
    dsimp [z] at t3 ⊢
    linear_combination (norm := module) t3
  refine ⟨u,x,y,ρ,θ,?_,?_,?_⟩
  · intro j hj
    change f j=first d u x ρ θ j
    by_cases hz : j=0
    · subst j; simp [first,u,show (0 : ℕ)≠d-1 by omega]
    by_cases ht : j=d-1
    · subst j
      simpa [first,show d-1≠0 by omega,show d-1-1=d-2 by omega,sub_eq_add_neg,add_assoc] using f1
    · rw [f_low j ⟨by omega,by omega⟩]
      simp [first,hz,ht]
  · intro j hj
    change g j=middle d y θ j
    by_cases h3 : j=d-3
    · subst j
      simpa [middle,show d-3≠d-2 by omega,show d-3≠d-1 by omega] using g3
    by_cases h2' : j=d-2
    · subst j
      simpa [middle,show d-2≠d-3 by omega,show d-2≠d-1 by omega] using g2
    by_cases h1' : j=d-1
    · subst j
      simpa [middle,show d-1≠d-3 by omega,show d-1≠d-2 by omega] using g1
    · rw [g_low j (by omega)]
      simp [middle,h3,h2',h1']
  · intro j hj
    change h j=last d u x y ρ θ j
    by_cases hz : j=0
    · subst j
      simpa [last,show (0 : ℕ)≠d-2 by omega,show (0 : ℕ)≠d-1 by omega] using hzero
    by_cases h2' : j=d-2
    · subst j
      simpa [last,z,show d-2≠0 by omega,show d-2≠d-1 by omega,
        show d-2-1=d-3 by omega] using h2
    by_cases h1' : j=d-1
    · subst j
      simpa [last,z,show d-1≠0 by omega,show d-1≠d-2 by omega,
        show d-1-1=d-2 by omega,sub_add_eq_sub_sub] using h1
    · rw [h_low j ⟨by omega,by omega⟩]
      simp [last,z,hz,h2',h1']

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
