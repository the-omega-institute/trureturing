import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.LargeThird

/-! UNELABORATED. Three unbounded residue selectors. A finite split of residues
does not bound the exponent or the ratio s. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open private A B L K SU SV SW AfterWWindows afterW_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic

private def smallY : Fin 3 → ℤ := ![4,4,8]
private def smallM : Fin 3 → ℤ := ![2,4,4]
private def denominator : Fin 3 → ℤ := ![5,5,9]
private def numerator : Fin 3 → ℤ := ![8,16,32]
private def defect (s : ℤ) : Fin 3 → ℤ := ![136*s+2,72*s-6,784*s-14]
private def loss : Fin 3 → ℤ := ![2,1,1]
private def residueCap : Fin 3 → ℤ := ![1,3,7]
private def threshold : Fin 3 → ℤ := ![8,4,4]
private def selectedR (i : Fin 3) (s : ℤ) : ℤ :=
  if i=0 then
    if s%5=0 ∨ s%5=2 then s else if s%5=1 ∨ s%5=3 then s-1 else s-2
  else if i=1 then if s%5=4 then s-1 else s
  else if s%9=7 then s-1 else s

private theorem residue_bounds (i : Fin 3) (s : ℤ) (hs : threshold i ≤ s) :
    let r := selectedR i s
    let h := denominator i
    let n := numerator i
    let v := n*r/h
    let e := (n*r)%h
    1 ≤ r ∧ s-loss i ≤ r ∧ r ≤ s ∧ 1 ≤ v ∧
      0 ≤ e ∧ e ≤ residueCap i ∧ n*r=h*v+e ∧
      2*r ≤ smallY i*s ∧ 2*v < smallM i*smallY i*s := by
  fin_cases i
  all_goals dsimp [threshold,denominator,numerator,selectedR,loss,residueCap,smallY,smallM] at *
  all_goals split_ifs <;> omega

/-- The ten positive certificates from the ordinary proof, in exactly the
selected family's unbounded variable s. -/
private theorem small_certificates (i : Fin 3) (s : ℤ) (hs : threshold i ≤ s) :
    let y := smallY i
    let m := smallM i
    let x := s*y
    let z := m*x
    let h := denominator i
    let n := numerator i
    let D := defect s i
    let U := SU x y
    0 < D-n ∧ U-s*D > 0 ∧
    2*h*A x y z=n*U+D ∧
    h*(A x y z-1)-2*(residueCap i*U+s*D) > 0 ∧
    (4*s-4*loss i-1)*A x y z-2*L x z-1 > 0 ∧
    (i=0 → (s-2)*D-5*(8*s-3) > 0) := by
  fin_cases i
  all_goals dsimp [threshold] at hs
  · obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ s=u+8 := ⟨s-8,by omega,by ring⟩
    dsimp [smallY,smallM,denominator,numerator,defect,residueCap,loss,A,B,L,SU]
    refine ⟨?_,?_,by ring,?_,?_,?_⟩
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · intro _; ring_nf; positivity
  · obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ s=u+4 := ⟨s-4,by omega,by ring⟩
    dsimp [smallY,smallM,denominator,numerator,defect,residueCap,loss,A,B,L,SU]
    refine ⟨?_,?_,by ring,?_,?_,?_⟩
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · intro h; exact (by norm_num at h)
  · obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ s=u+4 := ⟨s-4,by omega,by ring⟩
    dsimp [smallY,smallM,denominator,numerator,defect,residueCap,loss,A,B,L,SU]
    refine ⟨?_,?_,by ring,?_,?_,?_⟩
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · intro h; exact (by norm_num at h)

set_option maxHeartbeats 1800000 in
private theorem small_selector (i : Fin 3) (s : ℤ) (hs : threshold i ≤ s) :
    ∃ r v : ℤ, 1 ≤ r ∧ 2*r ≤ smallY i*s ∧ 1 ≤ v ∧
      2*v < smallM i*smallY i*s ∧
      AfterWWindows (s*smallY i) (smallY i) (smallM i*(s*smallY i)) r v := by
  let y := smallY i
  let m := smallM i
  let x := s*y
  let z := m*x
  let h := denominator i
  let n := numerator i
  let D := defect s i
  let U := SU x y
  let AA := A x y z
  let BB := B x y
  let r := selectedR i s
  let v := n*r/h
  let e := (n*r)%h
  let ε := 2*r*AA-v*U
  let δ := r*AA-v*BB
  obtain ⟨hr,hrlo,hrhi,hv,he0,hemax,heq,hrcap,hvcap⟩ := residue_bounds i s hs
  obtain ⟨hDn,hUD,hident,hslack,hfirst,hAsecond⟩ := small_certificates i s hs
  have hh : 0 < h := by fin_cases i <;> norm_num [h,denominator]
  have hn : 0 < n := by fin_cases i <;> norm_num [n,numerator]
  have hD : 0 < D := by change 0 < D-n at hDn; omega
  have hU : 0 < U := by
    have : 0 ≤ s*D := mul_nonneg (by fin_cases i <;> norm_num [threshold] at hs <;> omega) hD.le
    change U-s*D > 0 at hUD
    omega
  have hεident : h*ε=e*U+r*D := by
    have hq : n*r=h*v+e := heq
    have hi : 2*h*AA=n*U+D := hident
    have h1 := congrArg (fun t : ℤ => t*U) hq
    have h2 := congrArg (fun t : ℤ => r*t) hi
    dsimp [ε]
    nlinarith only [h1,h2]
  have hrel : ε=2*δ+v := by dsimp [ε,δ,U,SU,BB]; ring
  have hεv : 0 < ε-v := by
    have hp := mul_pos (show 0 < r by omega) (show 0 < D-n from hDn)
    have hq := mul_nonneg (show 0 ≤ e from he0) (show 0 ≤ U+1 by omega)
    have hqeq : n*r=h*v+e := heq
    have hpos : 0 < h*(ε-v) := by nlinarith only [hp,hq,hqeq,hεident]
    by_contra hn'
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hh.le (show ε-v ≤ 0 by omega)
    omega
  have hδ : 0 < δ := by omega
  have heupper : 2*ε ≤ AA-1 := by
    have hE := mul_le_mul_of_nonneg_right (show e ≤ residueCap i from hemax) hU.le
    have hR := mul_le_mul_of_nonneg_right (show r ≤ s from hrhi) hD.le
    change h*(AA-1)-2*(residueCap i*U+s*D) > 0 at hslack
    have hmul : h*(2*ε) < h*(AA-1) := by nlinarith only [hE,hR,hεident,hslack]
    exact (le_of_lt ((mul_lt_mul_iff_of_pos_left hh).mp hmul))
  have hAA : 0 < AA := by omega
  have hrA := mul_le_mul_of_nonneg_right (show s-loss i ≤ r from hrlo) hAA.le
  have hfirstv : 2*v*U > 2*L x z+2 := by
    change (4*s-4*loss i-1)*AA-2*L x z-1 > 0 at hfirst
    dsimp [ε] at heupper
    nlinarith only [heupper,hrA,hfirst]
  have hsecond : 0 ≤ SW x y z-2*AA+ε := by
    by_cases hi : i=0
    · subst i
      have hp := hAsecond rfl
      change (s-2)*D-5*(8*s-3) > 0 at hp
      have hR := mul_le_mul_of_nonneg_right (show s-2 ≤ r by simpa [loss] using hrlo) hD.le
      have hE := mul_nonneg (show 0 ≤ e from he0) hU.le
      have heps : 8*s-3 < ε := by
        change 5*ε=e*U+r*D at hεident
        nlinarith only [hp,hR,hE,hεident]
      have hid : SW x y z-2*AA=3-8*s := by
        dsimp [x,y,z,m,smallY,smallM,AA,A,K,SW]; ring
      omega
    · have hbase : 0 < SW x y z-2*AA := by
        fin_cases i
        · exact (hi rfl).elim
        all_goals obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0 ≤ u ∧ s=u+4 := ⟨s-4,by norm_num [threshold] at hs; omega,by ring⟩
        all_goals dsimp [x,y,z,m,smallY,smallM,AA,A,K,SW]
        all_goals ring_nf
        all_goals positivity
      omega
  refine ⟨r,v,hr,hrcap,hv,hvcap,?_⟩
  apply afterW_windows s y z r v
    (by fin_cases i <;> norm_num [threshold] at hs <;> omega)
    (by fin_cases i <;> norm_num [y,smallY])
    (by have hm : 2 ≤ m := by fin_cases i <;> norm_num [m,smallM]
        have hx : 0 ≤ x := by dsimp [x,y]; fin_cases i <;> norm_num [smallY,threshold] at * <;> omega
        dsimp [z,x] at *; nlinarith [mul_nonneg (m-2) hx])
    hrhi (by omega) hδ heupper hfirstv hsecond

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
