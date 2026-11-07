/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Weights
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 ZeroLattice Weights on original physical labels. -/
/- UNCOMPILED source candidate. Original physical coordinates throughout. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Reconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
open scoped BigOperators
open MersenneExceptional19Stabilizer
  (degree base seed place Qmask Q_exact source_phases v0 v1 v2)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss parameter_exact block Annihilates)
open SourceWidth

/-- Primitive weights in the original three physical blocks. -/
def phaseWeight (r : ℕ) (p : Fin 3) (j : ℕ) : ℤ :=
  if p=0 then aa r*2^j-(Qmask r : ℤ)*(if j=degree r-1 then 1 else 0)
  else if p=1 then -ss r*2^j+(Qmask r : ℤ)*
    ((if j=degree r-3 then 1 else 0)+(if j=degree r-2 then 1 else 0)+
      2*(if j=degree r-1 then 1 else 0))
  else bb r*2^j-(Qmask r : ℤ)*
    ((if j=degree r-2 then 1 else 0)+2*(if j=degree r-1 then 1 else 0))

/-- A weight at every original physical index, with no coordinate deletion. -/
def primitive (r : ℕ) (i : Fin (3*degree r)) : ℤ :=
  phaseWeight r
    ⟨i.val/degree r,Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩
    (i.val%degree r)

private theorem primitive_place (r : ℕ) (p : Fin 3) (j : Fin (degree r)) :
    primitive r (place p j)=phaseWeight r p j.val := by
  have hd : 0<degree r := by dsimp [degree]; omega
  have hdiv : (place p j).val/degree r=p.val := by
    dsimp [place]
    rw [Nat.mul_comm p.val (degree r),Nat.mul_add_div hd,
      Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hmod : (place p j).val%degree r=j.val := by
    simp [place,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  unfold primitive
  rw [hmod]
  congr 1
  exact Fin.ext hdiv

private theorem forall_place (r : ℕ) (P : Fin (3*degree r) → Prop)
    (h : ∀ p : Fin 3, ∀ j : Fin (degree r), P (place p j)) : ∀ i, P i := by
  intro i
  have hd : 0<degree r := by dsimp [degree]; omega
  let p : Fin 3 := ⟨i.val/degree r,
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩
  let j : Fin (degree r) := ⟨i.val%degree r,Nat.mod_lt _ hd⟩
  have hi : place p j=i := by
    apply Fin.ext
    dsimp [place,p,j]
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div i.val (degree r)
  simpa only [hi] using h p j

/-- Exact integer scaling of actualSource, proved from the sealed centered
source formulas, rather than from a rational-span assertion. -/
theorem source_eq_scale_primitive (r : ℕ) (i : Fin (3*degree r)) :
    actualSource (3*degree r) (seed r) i =
      (19*((base r : ℤ)-1))*primitive r i := by
  refine forall_place r (fun i => actualSource (3*degree r) (seed r) i =
    (19*((base r : ℤ)-1))*primitive r i) ?_ i
  intro p j
  rw [primitive_place]
  obtain ⟨h0,h1,h2⟩ := source_phases r j
  obtain ⟨ha,hb,hs⟩ := parameter_exact r
  have hQ := Q_exact r
  dsimp [v0,v1,v2] at h0 h1 h2
  fin_cases p <;> simp only [phaseWeight,ite_true,ite_false,
    show (1 : Fin 3)≠0 by decide,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide]
  · simp only [place,Fin.val_mk,show (0 : Fin 3).val=0 from rfl,zero_mul,zero_add]
    linear_combination h0-((base r : ℤ)-1)*2^j.val*ha+
      ((base r : ℤ)-1)*(if j.val=degree r-1 then 1 else 0)*hQ
  · simp only [place,Fin.val_mk,show (1 : Fin 3).val=1 from rfl,one_mul]
    linear_combination h1+((base r : ℤ)-1)*2^j.val*hs-
      ((base r : ℤ)-1)*((if j.val=degree r-3 then 1 else 0)+
        (if j.val=degree r-2 then 1 else 0)+2*(if j.val=degree r-1 then 1 else 0))*hQ
  · simp only [place,Fin.val_mk,show (2 : Fin 3).val=2 from rfl]
    linear_combination h2-((base r : ℤ)-1)*2^j.val*hb+
      ((base r : ℤ)-1)*((if j.val=degree r-2 then 1 else 0)+
        2*(if j.val=degree r-1 then 1 else 0))*hQ

variable {A : Type*} [AddCommGroup A]

private theorem scaled_first (r : ℕ) (c : A) (j : ℕ) :
    first (degree r) (aa r • c) ((2*aa r) • c) 0 ((Qmask r : ℤ) • c) j =
      phaseWeight r 0 j • c := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  by_cases hz : j=0
  · subst j
    simp [first,phaseWeight,show (0 : ℕ)≠degree r-1 by omega]
  · have hp : (2 : ℤ)^j=2*2^(j-1) := by
      rw [show j=(j-1)+1 by omega,pow_succ]
      ring
    simp only [first,phaseWeight,ite_true,if_neg hz]
    rw [hp]
    split_ifs <;> module

private theorem scaled_middle (r : ℕ) (c : A) (j : ℕ) :
    middle (degree r) ((-ss r) • c) ((Qmask r : ℤ) • c) j =
      phaseWeight r 1 j • c := by
  simp only [middle,phaseWeight,show (1 : Fin 3)≠0 by decide,
    ite_false,ite_true]
  split_ifs <;> module

private theorem scaled_last (r : ℕ) (c : A) (j : ℕ) :
    last (degree r) (aa r • c) ((2*aa r) • c) ((-ss r) • c)
      0 ((Qmask r : ℤ) • c) j = phaseWeight r 2 j • c := by
  have hs : ss r=aa r+bb r := rfl
  simp only [last,phaseWeight,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide,ite_false,hs]
  by_cases hz : j=0
  · subst j
    simp only [ite_true,pow_zero]
    split_ifs <;> module
  · have hp : (2 : ℤ)^j=2*2^(j-1) := by
      rw [show j=(j-1)+1 by omega,pow_succ]
      ring
    rw [if_neg hz,hp]
    split_ifs <;> module

/-- Torsion-sensitive reconstruction, with the explicit coordinate generator
-3 e_(0,0)+2 e_(2,0). Its hypothesis is exactly annihilation of literal actual
integer zero finsets. It is consumed by the quotient proof in Result. -/
theorem integral_reconstruction (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : Annihilates r X) (i : Fin (3*degree r)) :
    X i=primitive r i •
      ((-3 : ℤ) • X (place 0 ⟨0,by dsimp [degree]; omega⟩)+
        (2 : ℤ) • X (place 2 ⟨0,by dsimp [degree]; omega⟩)) := by
  obtain ⟨c,hf,hg,hh⟩ := reconstructed_normal_form r X hX
  have at_place (p : Fin 3) (j : Fin (degree r)) :
      X (place p j)=primitive r (place p j) • c := by
    rw [primitive_place]
    fin_cases p
    · have he := hf j.val j.isLt
      simp only [block,dif_pos j.isLt] at he
      exact he.trans (scaled_first r c j.val)
    · have he := hg j.val j.isLt
      simp only [block,dif_pos j.isLt] at he
      exact he.trans (scaled_middle r c j.val)
    · have he := hh j.val j.isLt
      simp only [block,dif_pos j.isLt] at he
      exact he.trans (scaled_last r c j.val)
  have every : ∀ i, X i=primitive r i • c :=
    forall_place r (fun i => X i=primitive r i • c) at_place
  let j0 : Fin (degree r) := ⟨0,by dsimp [degree]; omega⟩
  have hd : 12≤degree r := by dsimp [degree]; omega
  have w0 : primitive r (place 0 j0)=aa r := by
    simp [primitive_place,phaseWeight,j0,show (0 : ℕ)≠degree r-1 by omega]
  have w2 : primitive r (place 2 j0)=bb r := by
    simp [primitive_place,phaseWeight,j0,show (0 : ℕ)≠degree r-2 by omega,
      show (0 : ℕ)≠degree r-1 by omega]
  have hunit : -3*aa r+2*bb r=1 := by
    obtain ⟨ha,hb,hs⟩ := parameter_exact r
    omega
  have hc : (-3 : ℤ) • X (place 0 j0)+(2 : ℤ) • X (place 2 j0)=c := by
    rw [every (place 0 j0),every (place 2 j0),w0,w2,
      smul_smul,smul_smul,← add_smul,hunit,one_smul]
  change X i=primitive r i •
    ((-3 : ℤ) • X (place 0 j0)+(2 : ℤ) • X (place 2 j0))
  rw [hc]
  exact every i

end D5.S3.Combinatorics.Circle.MersenneExceptional19ZeroLattice
