/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 PermutationStabilizer NormalForm on original physical labels. -/
/- Source only: not elaborated or kernel checked. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open SourceWidth
open D5.S3.Combinatorics.Circle.MersenneExceptional19Stabilizer
  (degree base seed total place source_phases v0 v1 v2)
open private place_eq_iff
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary

private def triple {d : ℕ} (j : Fin d) : Finset (Fin (3*d)) :=
  {place 0 j, place 1 j, place 2 j}

private theorem sum_triple {R : Type*} [AddCommMonoid R] {d : ℕ}
    (hd : 0<d) (x : Fin (3*d) → R) (j : Fin d) :
    (∑ i ∈ triple j, x i)=x (place 0 j)+x (place 1 j)+x (place 2 j) := by
  classical
  have h01 : place (0 : Fin 3) j≠place 1 j := by
    simp [place_eq_iff hd]
  have h02 : place (0 : Fin 3) j≠place 2 j := by
    simp [place_eq_iff hd]
  have h12 : place (1 : Fin 3) j≠place 2 j := by
    simp [place_eq_iff hd]
  simp [triple, h01, h02, h12, add_assoc]

private theorem triple_total (r : ℕ) (j : Fin (degree r)) :
    total r (triple j)=((base r : ℤ)-1)*((base r : ℤ)^2+base r+1)*
      ((if j.val=degree r-3 then 1 else 0)-(if j.val=degree r-1 then 1 else 0)) := by
  have hd : 0<degree r := by dsimp [degree]; omega
  unfold total
  rw [sum_triple hd]
  have h0 := (source_phases r j).1
  have h1 := (source_phases r j).2.1
  have h2 := (source_phases r j).2.2
  simp only [place, Fin.val_mk, show (0 : Fin 3).val=0 from rfl,
    show (1 : Fin 3).val=1 from rfl, show (2 : Fin 3).val=2 from rfl,
    zero_mul,zero_add,one_mul]
  rw [h0,h1,h2]
  dsimp [v0,v1,v2]
  ring

private theorem triples_disjoint {d : ℕ} (hd : 0<d) (j k : Fin d)
    (hjk : j≠k) : Disjoint (triple j) (triple k) := by
  classical
  simp [triple, Finset.disjoint_left, place_eq_iff hd, hjk]

theorem triple_equations {A : Type*} [AddCommGroup A]
    (r : ℕ) (x : Fin (3*degree r) → A)
    (hx : Annihilates r x) :
    block x 0 0+block x 1 0+block x 2 0=0 ∧
    block x 0 1+block x 1 1+block x 2 1=0 ∧
    block x 0 (degree r-2)+block x 1 (degree r-2)+block x 2 (degree r-2)=0 ∧
    (block x 0 (degree r-3)+block x 1 (degree r-3)+block x 2 (degree r-3))+
      (block x 0 (degree r-1)+block x 1 (degree r-1)+block x 2 (degree r-1))=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  have single (j : ℕ) (hj : j<degree r) (h3 : j≠degree r-3)
      (h1 : j≠degree r-1) :
      block x 0 j+block x 1 j+block x 2 j=0 := by
    have ht : total r (triple (⟨j,hj⟩ : Fin (degree r)))=0 := by
      rw [triple_total]
      simp [h3,h1]
    have h := hx _ ht
    rw [sum_triple (by omega)] at h
    simpa only [block, dif_pos hj] using h
  refine ⟨single 0 (by omega) (by omega) (by omega),
    single 1 (by omega) (by omega) (by omega),
    single (degree r-2) (by omega) (by omega) (by omega),?_⟩
  let j : Fin (degree r) := ⟨degree r-3,by omega⟩
  let k : Fin (degree r) := ⟨degree r-1,by omega⟩
  have hjk : j≠k := by intro h; have := congrArg Fin.val h; dsimp [j,k] at this; omega
  have hdis := triples_disjoint (by omega) j k hjk
  have ht : total r (triple j ∪ triple k)=0 := by
    unfold total
    rw [Finset.sum_union hdis]
    change total r (triple j)+total r (triple k)=0
    rw [triple_total,triple_total]
    simp [j,k, show degree r-3≠degree r-1 by omega,
      show degree r-1≠degree r-3 by omega]
  have h := hx _ ht
  rw [Finset.sum_union hdis, sum_triple (by omega), sum_triple (by omega)] at h
  simpa [block,j,k,show degree r-3<degree r by omega,
    show degree r-1<degree r by omega] using h

private def n0 (d : ℕ) (α η ρ θ : ℚ) (j : ℕ) : ℚ :=
  α*2^j+η*(if j=0 then 1 else 0)+(ρ-θ)*(if j=d-1 then 1 else 0)
private def n1 (d : ℕ) (β θ : ℚ) (j : ℕ) : ℚ :=
  β*2^j+θ*(if j=d-3 then 1 else 0)+θ*(if j=d-2 then 1 else 0)+
    (2*θ)*(if j=d-1 then 1 else 0)
private def n2 (d : ℕ) (γ η ρ θ : ℚ) (j : ℕ) : ℚ :=
  γ*2^j-η*(if j=0 then 1 else 0)-θ*(if j=d-2 then 1 else 0)-
    (ρ+2*θ)*(if j=d-1 then 1 else 0)

theorem geom_sum {R : Type*} [CommRing R] (m : ℕ) :
    (∑ i : Fin m, (2 : R)^i.val)=(2 : R)^m-1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, pow_succ]
      ring

private theorem prefix_geom (f : ℕ → ℚ) (β : ℚ) (m : ℕ)
    (hf : ∀ j, j<m → f j=β*2^j) :
    (∑ i : Fin m, f i.val)=β*((2 : ℚ)^m-1) := by
  calc
    (∑ i : Fin m, f i.val)=(∑ i : Fin m, β*(2 : ℚ)^i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hf i.val i.isLt
    _=β*((2 : ℚ)^m-1) := by rw [← Finset.mul_sum, geom_sum]

/-- Exhaustive coordinate elimination. The only input equations are the
three carry families and the four literal-zero triple indicators. -/
private theorem normal_form (r : ℕ) (x : Fin (3*degree r) → ℚ)
    (hx : Annihilates r x) :
    ∃ α β γ η ρ θ : ℚ, α+β+γ=0 ∧
      (∀ j, j<degree r → block x 0 j=n0 (degree r) α η ρ θ j) ∧
      (∀ j, j<degree r → block x 1 j=n1 (degree r) β θ j) ∧
      (∀ j, j<degree r → block x 2 j=n2 (degree r) γ η ρ θ j) := by
  let d := degree r
  let f := block x 0
  let g := block x 1
  let h := block x 2
  have hd : 12≤d := by dsimp [d,degree]; omega
  obtain ⟨t0,t1,t2,t3⟩ := triple_equations r x hx
  change f 0+g 0+h 0=0 at t0
  change f 1+g 1+h 1=0 at t1
  change f (d-2)+g (d-2)+h (d-2)=0 at t2
  change (f (d-3)+g (d-3)+h (d-3))+(f (d-1)+g (d-1)+h (d-1))=0 at t3
  have gg (j : ℕ) (hj : 1≤j ∧ j<d ∧ j≠d-3) :
      f 0+carry g j+h 0=0 := g_equation r x hx j hj
  have ff (j : ℕ) (hj : 2≤j ∧ j≤d-2) :
      carry f j+g 0+carry h 1=0 := f_equation r x hx j hj
  have hh (j : ℕ) (hj : 2≤j ∧ j≤d-3) :
      carry f 1+g 0+carry h j=0 := h_equation r x hx j hj
  have gg1 := gg 1 ⟨by omega,by omega,by omega⟩
  have gg1' : g 1=2*g 0 := by
    have hc : carry g 1=g 1-g 0 := by simp [carry]
    rw [hc] at gg1
    linarith
  have gr (j : ℕ) (hj : 1≤j ∧ j+1≤d-4) : g (j+1)=2*g j := by
    have h0 := gg j ⟨hj.1,by omega,by omega⟩
    have h1 := gg (j+1) ⟨by omega,by omega,by omega⟩
    have hc := carry_step g j
    norm_num [zsmul_eq_mul] at hc
    linarith
  have fr2 : f 2=2*f 1 := by
    have hF := ff 2 ⟨by omega,by omega⟩
    have cF : carry f 2=f 2-f 0-f 1 := by
      simp [carry, Fin.sum_univ_two]
      ring
    have cH : carry h 1=h 1-h 0 := by simp [carry]
    rw [cF,cH] at hF
    linarith
  have hr2 : h 2=2*h 1 := by
    have hH := hh 2 ⟨by omega,by omega⟩
    have cH : carry h 2=h 2-h 0-h 1 := by
      simp [carry, Fin.sum_univ_two]
      ring
    have cF : carry f 1=f 1-f 0 := by simp [carry]
    rw [cF,cH] at hH
    linarith
  have fr (j : ℕ) (hj : 2≤j ∧ j+1≤d-2) : f (j+1)=2*f j := by
    have h0 := ff j ⟨hj.1,by omega⟩
    have h1 := ff (j+1) ⟨by omega,hj.2⟩
    have hc := carry_step f j
    norm_num [zsmul_eq_mul] at hc
    linarith
  have hr (j : ℕ) (hj : 2≤j ∧ j+1≤d-3) : h (j+1)=2*h j := by
    have h0 := hh j ⟨hj.1,by omega⟩
    have h1 := hh (j+1) ⟨by omega,hj.2⟩
    have hc := carry_step h j
    norm_num [zsmul_eq_mul] at hc
    linarith
  let α : ℚ := f 1/2
  let β : ℚ := g 0
  let γ : ℚ := h 1/2
  have g_low (j : ℕ) (hj : j≤d-4) : g j=β*2^j := by
    induction j with
    | zero => simp [β]
    | succ j ih =>
        have ih' := ih (by omega)
        by_cases hj0 : j=0
        · subst j
          simpa [β,mul_comm] using gg1'
        · rw [gr j ⟨by omega,hj⟩, ih', pow_succ]
          ring
  have f_low (j : ℕ) (hj : 1≤j ∧ j≤d-2) : f j=α*2^j := by
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hj0 : j=0
        · subst j
          simp [α] <;> ring
        by_cases hj1 : j=1
        · subst j
          rw [fr2]
          simp [α] <;> ring
        · rw [fr j ⟨by omega,hj.2⟩, ih ⟨by omega,by omega⟩, pow_succ]
          ring
  have h_low (j : ℕ) (hj : 1≤j ∧ j≤d-3) : h j=γ*2^j := by
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hj0 : j=0
        · subst j
          simp [γ] <;> ring
        by_cases hj1 : j=1
        · subst j
          rw [hr2]
          simp [γ] <;> ring
        · rw [hr j ⟨by omega,hj.2⟩, ih ⟨by omega,by omega⟩, pow_succ]
          ring
  have slopes : α+β+γ=0 := by
    have hf1 := f_low 1 ⟨by omega,by omega⟩
    have hg1 := g_low 1 (by omega)
    have hh1 := h_low 1 ⟨by omega,by omega⟩
    norm_num at hf1 hg1 hh1
    linarith
  let η := f 0-α
  let θ := g (d-3)-β*2^(d-3)
  let ρ := f (d-1)-α*2^(d-1)+θ
  have f_zero : f 0=α+η := by dsimp [η]; ring
  have h_zero : h 0=γ-η := by dsimp [η,β] at *; linarith
  have g3 : g (d-3)=β*2^(d-3)+θ := by dsimp [θ]; ring
  have sum3 : (∑ i : Fin (d-3), g i.val)=β*((2 : ℚ)^(d-3)-1) :=
    prefix_geom g β (d-3) (fun j hj => g_low j (by omega))
  have sum2 : (∑ i : Fin (d-2), g i.val)=β*((2 : ℚ)^(d-2)-1)+θ := by
    rw [show d-2=(d-3)+1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sum3, g3, pow_succ]
    ring
  have g2 : g (d-2)=β*2^(d-2)+θ := by
    have he := gg (d-2) ⟨by omega,by omega,by omega⟩
    dsimp [carry] at he
    rw [sum2] at he
    dsimp [β] at *
    linear_combination he-t0
  have sum1 : (∑ i : Fin (d-1), g i.val)=β*((2 : ℚ)^(d-1)-1)+2*θ := by
    rw [show d-1=(d-2)+1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sum2, g2, pow_succ]
    ring
  have g1 : g (d-1)=β*2^(d-1)+2*θ := by
    have he := gg (d-1) ⟨by omega,by omega,by omega⟩
    dsimp [carry] at he
    rw [sum1] at he
    dsimp [β] at *
    linear_combination he-t0
  have h2 : h (d-2)=γ*2^(d-2)-θ := by
    rw [f_low (d-2) ⟨by omega,by omega⟩,g2] at t2
    linear_combination t2-(2 : ℚ)^(d-2)*slopes
  have f1 : f (d-1)=α*2^(d-1)+ρ-θ := by dsimp [ρ]; ring
  have h1 : h (d-1)=γ*2^(d-1)-ρ-2*θ := by
    rw [f_low (d-3) ⟨by omega,by omega⟩,g3,
      h_low (d-3) ⟨by omega,by omega⟩,f1,g1] at t3
    linear_combination t3-((2 : ℚ)^(d-3)+(2 : ℚ)^(d-1))*slopes
  refine ⟨α,β,γ,η,ρ,θ,slopes,?_,?_,?_⟩
  · intro j hj
    change f j=n0 d α η ρ θ j
    by_cases hz : j=0
    · subst j
      simpa [n0,show (0 : ℕ)≠d-1 by omega] using f_zero
    by_cases ht : j=d-1
    · subst j
      simpa [n0,show d-1≠0 by omega,sub_eq_add_neg,add_assoc] using f1
    · rw [f_low j ⟨by omega,by omega⟩]
      simp [n0,hz,ht]
  · intro j hj
    change g j=n1 d β θ j
    by_cases h3 : j=d-3
    · subst j
      simpa [n1,show d-3≠d-2 by omega,show d-3≠d-1 by omega] using g3
    by_cases h2' : j=d-2
    · subst j
      simpa [n1,show d-2≠d-3 by omega,show d-2≠d-1 by omega] using g2
    by_cases h1' : j=d-1
    · subst j
      simpa [n1,show d-1≠d-3 by omega,show d-1≠d-2 by omega] using g1
    · rw [g_low j (by omega)]
      simp [n1,h3,h2',h1']
  · intro j hj
    change h j=n2 d γ η ρ θ j
    by_cases hz : j=0
    · subst j
      simpa [n2,show (0 : ℕ)≠d-2 by omega,show (0 : ℕ)≠d-1 by omega] using h_zero
    by_cases h2' : j=d-2
    · subst j
      simpa [n2,show d-2≠0 by omega,show d-2≠d-1 by omega] using h2
    by_cases h1' : j=d-1
    · subst j
      simpa [n2,show d-1≠0 by omega,show d-1≠d-2 by omega,sub_add_eq_sub_sub] using h1
    · rw [h_low j ⟨by omega,by omega⟩]
      simp [n2,hz,h2',h1']

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
