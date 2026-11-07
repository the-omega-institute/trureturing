/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 PermutationStabilizer CarryRows on original physical labels. -/
/- Source only: not elaborated or kernel checked. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
  (degree base seed total)
open MersenneExceptional19Stabilizer (floor_unique)
open private read_carry_mod
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
open private base_multiple affine affine_zero
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical

def Annihilates {A : Type*} [AddCommGroup A]
    (r : ℕ) (x : Fin (3*degree r) → A) : Prop :=
  ∀ A : Finset (Fin (3*degree r)), total r A=0 → (∑ i ∈ A, x i)=0

def carry {A : Type*} [AddCommGroup A] (f : ℕ → A) (j : ℕ) : A :=
  f j-∑ i : Fin j, f i.val

private theorem carry_zero {A : Type*} [AddCommGroup A] (f : ℕ → A) : carry f 0=f 0 := by simp [carry]

theorem carry_step {A : Type*} [AddCommGroup A] (f : ℕ → A) (j : ℕ) :
    carry f (j+1)-carry f j=f (j+1)-(2 : ℤ) • f j := by
  simp only [carry, Fin.sum_univ_castSucc, Fin.val_last, Fin.val_castSucc]
  abel

theorem affine_annihilates {A : Type*} [AddCommGroup A] (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) (M : ℤ) (hM : affineRange r M) :
    read (degree r) (block x 0) (M+bb r)+
      read (degree r) (block x 1) M+
      read (degree r) (block x 2) (M-aa r)=0 := by
  have h := hx (affine r M) (affine_zero r M hM)
  simpa only [affine, physical_read (by dsimp [degree]; omega)] using h

private theorem consecutive_equation {A : Type*} [AddCommGroup A] (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) (M : ℤ) (j0 j1 j2 : ℕ)
    (hM : affineRange r M) (hM' : affineRange r (M-1))
    (hj0 : j0<degree r) (hj1 : j1<degree r) (hj2 : j2<degree r)
    (hc0 : (M+bb r)%(2 : ℤ)^(j0+1)=(2 : ℤ)^j0)
    (hc1 : M%(2 : ℤ)^(j1+1)=(2 : ℤ)^j1)
    (hc2 : (M-aa r)%(2 : ℤ)^(j2+1)=(2 : ℤ)^j2) :
    carry (block x 0) j0+carry (block x 1) j1+carry (block x 2) j2=0 := by
  have h := affine_annihilates r x hx M hM
  have h' := affine_annihilates r x hx (M-1) hM'
  have c0 := read_carry_mod (degree r) j0 (block x 0) (M+bb r) hj0 hc0
  have c1 := read_carry_mod (degree r) j1 (block x 1) M hj1 hc1
  have c2 := read_carry_mod (degree r) j2 (block x 2) (M-aa r) hj2 hc2
  rw [show M-1+bb r=M+bb r-1 by ring,
    show M-1-aa r=M-aa r-1 by ring] at h'
  dsimp [carry]
  linear_combination (norm := abel) h-h'-c0-c1-c2

private theorem power_mod_zero (u v : ℕ) (h : v≤u) :
    (2 : ℤ)^u%(2 : ℤ)^v=0 := by
  have he : (2 : ℤ)^u=(2 : ℤ)^(u-v)*(2 : ℤ)^v := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [he, Int.mul_emod]
  simp

private theorem add_power_mod (z : ℤ) (j : ℕ)
    (hz : z%(2 : ℤ)^(j+1)=0) :
    (z+(2 : ℤ)^j)%(2 : ℤ)^(j+1)=(2 : ℤ)^j := by
  have hp0 : (0 : ℤ)≤2^j := by positivity
  have hp1 : (2 : ℤ)^j<2^(j+1) := by
    rw [pow_succ]
    have : (0 : ℤ)<2^j := by positivity
    omega
  rw [Int.add_emod, hz, zero_add, Int.emod_eq_of_lt hp0 hp1,
    Int.emod_eq_of_lt hp0 hp1]

private theorem sub_power_mod (z : ℤ) (j : ℕ)
    (hz : z%(2 : ℤ)^(j+1)=0) :
    (z-(2 : ℤ)^j)%(2 : ℤ)^(j+1)=(2 : ℤ)^j := by
  have hp : (0 : ℤ)<2^j := by positivity
  have hf : (-(2 : ℤ)^j)/(2 : ℤ)^(j+1)= -1 := by
    apply floor_unique (by positivity)
    · rw [pow_succ]
      nlinarith only [hp]
    · rw [pow_succ]
      nlinarith only [hp]
  have hm := Int.emod_add_mul_ediv (-(2 : ℤ)^j) ((2 : ℤ)^(j+1))
  rw [hf, pow_succ] at hm
  have hn : (-(2 : ℤ)^j)%(2 : ℤ)^(j+1)=(2 : ℤ)^j := by omega
  have hrem : (2 : ℤ)^j%(2 : ℤ)^(j+1)=(2 : ℤ)^j := by
    apply Int.emod_eq_of_lt (by positivity)
    rw [pow_succ]
    omega
  rw [Int.sub_emod, hz, hrem, zero_sub]
  exact hn

private theorem eighth_power (r : ℕ) : eighth r=(2 : ℤ)^(degree r-3) := by
  have he := base_multiple r 3 (by dsimp [degree]; omega)
  have hB := (eighth_facts r).1
  norm_num at he
  omega

private theorem four_eighth_power (r : ℕ) :
    4*eighth r=(2 : ℤ)^(degree r-1) := by
  rw [eighth_power]
  have hd : degree r-1=(degree r-3)+2 := by dsimp [degree]; omega
  rw [hd, pow_add]
  ring

private theorem six_eighth_mod (r : ℕ) :
    (6*eighth r)%(2 : ℤ)^(degree r-2+1)=(2 : ℤ)^(degree r-2) := by
  have hd : degree r-2=(degree r-3)+1 := by dsimp [degree]; omega
  have he : 6*eighth r=(2 : ℤ)^(degree r-2+1)+(2 : ℤ)^(degree r-2) := by
    simp only [eighth_power, hd, pow_succ]
    ring
  have hp0 : (0 : ℤ)≤2^(degree r-2) := by positivity
  have hp1 : (2 : ℤ)^(degree r-2)<2^(degree r-2+1) := by
    rw [pow_succ]
    have : (0 : ℤ)<2^(degree r-2) := by positivity
    omega
  rw [he, Int.add_emod, Int.emod_self, zero_add,
    Int.emod_eq_of_lt hp0 hp1, Int.emod_eq_of_lt hp0 hp1]

private theorem four_eighth_mod (r : ℕ) :
    (4*eighth r)%(2 : ℤ)^(degree r-1+1)=(2 : ℤ)^(degree r-1) := by
  rw [four_eighth_power]
  apply Int.emod_eq_of_lt (by positivity)
  rw [pow_succ]
  have : (0 : ℤ)<2^(degree r-1) := by positivity
  omega

private def gPoint (r j : ℕ) : ℤ :=
  if j=degree r-1 then 4*eighth r
  else if j=degree r-2 then 6*eighth r
  else 4*eighth r+(2 : ℤ)^j

private def fPoint (r j : ℕ) : ℤ :=
  if j=degree r-2 then 6*eighth r-bb r
  else 8*eighth r-bb r-(2 : ℤ)^j

private def hPoint (r j : ℕ) : ℤ := 4*eighth r+aa r-(2 : ℤ)^j

private theorem gPoint_data (r j : ℕ)
    (hj : 1≤j ∧ j<degree r ∧ j≠degree r-3) :
    affineRange r (gPoint r j) ∧ affineRange r (gPoint r j-1) ∧
    (gPoint r j+bb r)%2=1 ∧
    gPoint r j%(2 : ℤ)^(j+1)=(2 : ℤ)^j ∧
    (gPoint r j-aa r)%2=1 := by
  obtain ⟨hB,hq,hqmod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  obtain ⟨ha,hb,hs⟩ := parameter_parities r
  have hpmod : (2 : ℤ)^j%2=0 := by simpa using power_mod_zero j 1 hj.1
  by_cases ht : j=degree r-1
  · subst j
    simp only [gPoint, if_pos]
    refine ⟨Or.inr (Or.inl ⟨by omega,by omega⟩),
      Or.inr (Or.inl ⟨by omega,by omega⟩),by omega,
      four_eighth_mod r,by omega⟩
  by_cases hn : j=degree r-2
  · subst j
    simp only [gPoint, if_neg ht, if_pos]
    refine ⟨Or.inr (Or.inr ⟨by omega,by omega⟩),
      Or.inr (Or.inr ⟨by omega,by omega⟩),by omega,
      six_eighth_mod r,by omega⟩
  have hj4 : j≤degree r-4 := by omega
  have hp : 2*(2 : ℤ)^j≤eighth r := by
    rw [eighth_power]
    have he : degree r-3=(degree r-4)+1 := by dsimp [degree]; omega
    rw [he, pow_succ]
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2) hj4
    linarith
  have hp0 : (0 : ℤ)<2^j := by positivity
  have hm : (4*eighth r)%(2 : ℤ)^(j+1)=0 := by
    rw [four_eighth_power]
    exact power_mod_zero _ _ (by omega)
  simp only [gPoint, if_neg ht, if_neg hn]
  exact ⟨Or.inr (Or.inl ⟨by omega,by omega⟩),
    Or.inr (Or.inl ⟨by omega,by omega⟩),by omega,
    add_power_mod _ _ hm,by omega⟩

private theorem fPoint_data (r j : ℕ) (hj : 2≤j ∧ j≤degree r-2) :
    affineRange r (fPoint r j) ∧ affineRange r (fPoint r j-1) ∧
    (fPoint r j+bb r)%(2 : ℤ)^(j+1)=(2 : ℤ)^j ∧
    fPoint r j%2=1 ∧ (fPoint r j-aa r)%4=2 := by
  obtain ⟨hB,hq,hqmod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  obtain ⟨ha,hb,hs⟩ := parameter_parities r
  have hs' : ss r=aa r+bb r := rfl
  have hpmod : (2 : ℤ)^j%4=0 := by simpa using power_mod_zero j 2 hj.1
  by_cases hn : j=degree r-2
  · subst j
    simp only [fPoint, if_pos]
    refine ⟨Or.inr (Or.inl ⟨by omega,by omega⟩),
      Or.inr (Or.inl ⟨by omega,by omega⟩),?_,by omega,by omega⟩
    simpa only [sub_add_cancel] using six_eighth_mod r
  have hj3 : j≤degree r-3 := by omega
  have hp : (2 : ℤ)^j≤eighth r := by
    rw [eighth_power]
    exact pow_le_pow_right₀ (by norm_num) hj3
  have hp4 : (4 : ℤ)≤2^j := by
    change (2 : ℤ)^2≤2^j
    exact pow_le_pow_right₀ (by norm_num) hj.1
  have hm : (8*eighth r)%(2 : ℤ)^(j+1)=0 := by
    rw [← hB]
    rw [show (base r : ℤ)=(2 : ℤ)^degree r by simp [base]]
    exact power_mod_zero _ _ (by omega)
  simp only [fPoint, if_neg hn]
  refine ⟨Or.inr (Or.inr ⟨by omega,by omega⟩),
    Or.inr (Or.inr ⟨by omega,by omega⟩),?_,by omega,by omega⟩
  convert sub_power_mod (8*eighth r) j hm using 1 <;> congr 1 <;> ring

private theorem hPoint_data (r j : ℕ) (hj : 2≤j ∧ j≤degree r-3) :
    affineRange r (hPoint r j) ∧ affineRange r (hPoint r j-1) ∧
    (hPoint r j+bb r)%4=2 ∧ hPoint r j%2=1 ∧
    (hPoint r j-aa r)%(2 : ℤ)^(j+1)=(2 : ℤ)^j := by
  obtain ⟨hB,hq,hqmod⟩ := eighth_facts r
  obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
  obtain ⟨ha,hb,hs⟩ := parameter_parities r
  have hs' : ss r=aa r+bb r := rfl
  have hpmod : (2 : ℤ)^j%4=0 := by simpa using power_mod_zero j 2 hj.1
  have hp : (2 : ℤ)^j≤eighth r := by
    rw [eighth_power]
    exact pow_le_pow_right₀ (by norm_num) hj.2
  have hp4 : (4 : ℤ)≤2^j := by
    change (2 : ℤ)^2≤2^j
    exact pow_le_pow_right₀ (by norm_num) hj.1
  have hm : (4*eighth r)%(2 : ℤ)^(j+1)=0 := by
    rw [four_eighth_power]
    exact power_mod_zero _ _ (by omega)
  dsimp [hPoint]
  refine ⟨Or.inr (Or.inl ⟨by omega,by omega⟩),
    Or.inr (Or.inl ⟨by omega,by omega⟩),by omega,by omega,?_⟩
  convert sub_power_mod (4*eighth r) j hm using 1 <;> congr 1 <;> ring

theorem g_equation {A : Type*} [AddCommGroup A] (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) (j : ℕ)
    (hj : 1≤j ∧ j<degree r ∧ j≠degree r-3) :
    block x 0 0+carry (block x 1) j+block x 2 0=0 := by
  obtain ⟨hM,hM',h0,h1,h2⟩ := gPoint_data r j hj
  have h := consecutive_equation r x hx (gPoint r j) 0 j 0 hM hM'
    (by dsimp [degree]; omega) hj.2.1 (by dsimp [degree]; omega)
    (by simpa using h0) h1 (by simpa using h2)
  simpa only [carry_zero] using h

theorem f_equation {A : Type*} [AddCommGroup A] (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) (j : ℕ) (hj : 2≤j ∧ j≤degree r-2) :
    carry (block x 0) j+block x 1 0+carry (block x 2) 1=0 := by
  obtain ⟨hM,hM',h0,h1,h2⟩ := fPoint_data r j hj
  have h := consecutive_equation r x hx (fPoint r j) j 0 1 hM hM'
    (by dsimp [degree] at *; omega) (by dsimp [degree]; omega)
    (by dsimp [degree]; omega) h0 (by simpa using h1) (by simpa using h2)
  simpa only [carry_zero] using h

theorem h_equation {A : Type*} [AddCommGroup A] (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) (j : ℕ) (hj : 2≤j ∧ j≤degree r-3) :
    carry (block x 0) 1+block x 1 0+carry (block x 2) j=0 := by
  obtain ⟨hM,hM',h0,h1,h2⟩ := hPoint_data r j hj  have h := consecutive_equation r x hx (hPoint r j) 1 0 j hM hM'
    (by dsimp [degree]; omega) (by dsimp [degree]; omega)
    (by dsimp [degree] at *; omega) (by simpa using h0)
    (by simpa using h1) h2
  simpa only [carry_zero] using h

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
