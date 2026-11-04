/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Arithmetic
   generality: I
   mirror-B: none(waiver:physical-dependent-source-family)
   mirror-E: none(waiver:physical-dependent-source-family)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact seam identities and strict six-window certificates for all five branches. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Banks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open private x y z t AA BB LL KK SU SV SW q h H rho fmask jmask mmask Rmask deltaMask isFinite cone_powers power_links
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private branch Branch from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters

private def window (e M : ℤ) : Prop := 0 < 2*e ∧ 2*e < M

private theorem first_seams (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    window (LL a c d-h b c*BB d a b) (LL a c d) ∧
    window (SV a c d-h b c*SU a b d) (SV a c d) := by
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  have hh := (power_links a b c d hb hba hac hd hda).2.1
  have hx : 0<x a := by omega
  have hz : 0<z c := by omega
  have hy' : 0<y b := by omega
  have ht' : 0<t d := by omega
  have hym : 0<y b-1 := by omega
  have hy2 : 0<2*y b-1 := by omega
  have idold : 2*y b*(LL a c d-(h b c : ℤ)*BB d a b) =
      2*y b+z c*(2*y b-1)*(1+t d)+x a*z c*t d*(y b-1) := by
    calc
      _ = 2*y b*LL a c d-z c*BB d a b := by
        linear_combination -(BB d a b)*hh
      _ = _ := by dsimp [LL,BB]; ring
  have idnew : 2*y b*(SV a c d-(h b c : ℤ)*SU a b d) =
      2*y b+z c*(2*y b-1)*(1+2*t d)+2*x a*z c*t d*(y b-1) := by
    calc
      _ = 2*y b*SV a c d-z c*SU a b d := by
        linear_combination -(SU a b d)*hh
      _ = _ := by dsimp [SV,SU,LL,BB]; ring
  have posold : 0<2*y b+z c*(2*y b-1)*(1+t d)+
      x a*z c*t d*(y b-1) := by positivity
  have posnew : 0<2*y b+z c*(2*y b-1)*(1+2*t d)+
      2*x a*z c*t d*(y b-1) := by positivity
  let P := (x a-2*y b)*t d+y b*(t d-1)+t d+1
  have hP : y b<P := by
    have h0 := mul_nonneg (show 0≤x a-2*y b by omega) ht'.le
    have h1 := mul_nonneg hy'.le (show 0≤t d-2 by omega)
    dsimp [P]
    nlinarith only [h0,h1,ht]
  have hPpos : 0<P := by omega
  have hZP := mul_nonneg (show 0≤z c-1 by omega) hPpos.le
  have idgap : y b*(2*(h b c : ℤ)*BB d a b-LL a c d)=z c*P-y b := by
    calc
      _ = z c*BB d a b-y b*LL a c d := by
        linear_combination (BB d a b)*hh
      _ = _ := by dsimp [P,BB,LL]; ring
  have gap : 0<2*(h b c : ℤ)*BB d a b-LL a c d := by
    nlinarith only [idgap,hZP,hP,hy']
  have hsmall : 0≤z c-2*(h b c : ℤ) := by
    have hp := mul_nonneg (show 0≤y b-1 by omega)
      (show 0≤(h b c : ℤ) by positivity)
    nlinarith only [hh,hp]
  have newgap : 0<2*(h b c : ℤ)*SU a b d-SV a c d := by
    have hid : 2*(h b c : ℤ)*SU a b d-SV a c d =
        2*(2*(h b c : ℤ)*BB d a b-LL a c d)+z c+1-2*(h b c : ℤ) := by
      dsimp [SU,SV]; ring
    linarith only [hid,gap,hsmall]
  dsimp only [window]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · nlinarith only [idold,posold,hy']
  · linarith only [gap]
  · nlinarith only [idnew,posnew,hy']
  · linarith only [newgap]

private theorem A_seams (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b≤d) (ha1 : a=d+1) :
    window (KK b c d-H a c*BB d a b) (KK b c d) ∧
    window (SW b c d-H a c*SU a b d) (SW b c d) ∧
    window (AA a b c-KK b c d-H a c*BB d a b) (AA a b c) ∧
    window (2*AA a b c-SW b c d-H a c*SU a b d) (AA a b c) := by
  have hp:=cone_powers a b c d hb hba hac hd hda
  subst a
  constructor <;> constructor <;>
    dsimp [window,AA,BB,LL,KK,SU,SV,SW,H,x,y,z,t] <;>
    norm_num at * <;> nlinarith

private theorem A_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b≤d) :
    window (KK b c d-H a c*BB d a b) (KK b c d) ∧
    window (SW b c d-H a c*SU a b d) (SW b c d) := by
  have hp:=cone_powers a b c d hb hba hac hd hda
  dsimp [window,AA,BB,KK,SW,SU,H,x,y,z,t]
  constructor <;> constructor <;> norm_num at * <;> nlinarith

private theorem A2_B_third (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (ha2 : d+2≤a)
    (hbranch : (b≤d ∧ ¬isFinite a b c d) ∨
      (d+2≤b ∨ b=d+1 ∧ a+2≤c)) :
    window (AA a b c-fmask a d*KK b c d-BB d a b) (AA a b c) ∧
    window (2*AA a b c-fmask a d*SW b c d-SU a b d) (AA a b c) := by
  have hp:=cone_powers a b c d hb hba hac hd hda
  dsimp [window,AA,BB,KK,SW,SU,fmask,x,y,z,t]
  constructor <;> constructor <;> norm_num at * <;> nlinarith

private theorem B_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hB : d+2≤b ∨ b=d+1 ∧ a+2≤c) :
    let j := (jmask a b d : ℤ)
    let δ : ℤ := if d+2≤b then 0 else deltaMask a b c d
    window (j*(KK b c d-q a c*BB d a b)+δ*BB d a b) (KK b c d) ∧
    window (j*(SW b c d-q a c*SU a b d)+δ*SU a b d) (SW b c d) := by
  dsimp
  have hp:=cone_powers a b c d hb hba hac hd hda
  rcases hB with hB|⟨rfl,hB⟩
  · simp [jmask,mmask,Rmask,deltaMask,hB,BB,KK,SU,SW,q,x,y,z,t,window]
    constructor <;> constructor <;> nlinarith
  · by_cases hR : Rmask a b c d < 2^a*2^b
    · simp [jmask,mmask,Rmask,deltaMask,hR,BB,KK,SU,SW,q,x,y,z,t,window]
      constructor <;> constructor <;> nlinarith
    · simp [jmask,mmask,Rmask,deltaMask,hR,BB,KK,SU,SW,q,x,y,z,t,window]
      constructor <;> constructor <;> nlinarith

private theorem C_seams (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b=d+1) (hca : c=a+1) :
    window (AA a b c-(fmask a d : ℤ)*KK b c d) (AA a b c) ∧
    window (2*AA a b c-(fmask a d : ℤ)*SW b c d) (AA a b c) ∧
    window (AA a b c-2*LL a c d+BB d a b) (KK b c d) ∧
    window (2*AA a b c-2*SV a c d+SU a b d) (SW b c d) ∧
    window (AA a b c-LL a c d-(rho a d/2+1)*BB d a b) (LL a c d) ∧
    window (2*AA a b c-SV a c d-(rho a d/2+1)*SU a b d) (SV a c d) := by
  subst b
  subst c
  have hp:=cone_powers a (d+1) (a+1) d hb hba hac hd hda
  dsimp [window,AA,BB,LL,KK,SU,SV,SW,rho,x,y,z,t]
  constructor <;> constructor <;> norm_num at * <;> nlinarith

private theorem finite_windows :
    window 113 8191 ∧ window 206 16383 ∧
    window 469 8191 ∧ window 898 16383 ∧
    window 1383 16383 ∧ window 564 32767 ∧
    window 741 32767 ∧ window 1442 65535 ∧
    window 160 32767 ∧ window 255 65535 := by
  norm_num [window]

private theorem all_windows (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    (window (LL a c d-h b c*BB d a b) (LL a c d) ∧
      window (SV a c d-h b c*SU a b d) (SV a c d)) ∧
    (b≤d →
      (window (KK b c d-H a c*BB d a b) (KK b c d) ∧
        window (SW b c d-H a c*SU a b d) (SW b c d))) ∧
    (b≤d → a=d+1 →
      (window (AA a b c-KK b c d-H a c*BB d a b) (AA a b c) ∧
        window (2*AA a b c-SW b c d-H a c*SU a b d) (AA a b c))) ∧
    (d+2≤a → ((b≤d ∧ ¬isFinite a b c d) ∨
        (d+2≤b ∨ b=d+1 ∧ a+2≤c)) →
      (window (AA a b c-fmask a d*KK b c d-BB d a b) (AA a b c) ∧
        window (2*AA a b c-fmask a d*SW b c d-SU a b d) (AA a b c))) ∧
    ((d+2≤b ∨ b=d+1 ∧ a+2≤c) →
      let δ : ℤ := if d+2≤b then 0 else deltaMask a b c d
      window ((jmask a b d : ℤ)*(KK b c d-q a c*BB d a b)+δ*BB d a b) (KK b c d) ∧
      window ((jmask a b d : ℤ)*(SW b c d-q a c*SU a b d)+δ*SU a b d) (SW b c d)) ∧
    (b=d+1 → c=a+1 →
      window (AA a b c-(fmask a d : ℤ)*KK b c d) (AA a b c) ∧
      window (2*AA a b c-(fmask a d : ℤ)*SW b c d) (AA a b c) ∧
      window (AA a b c-2*LL a c d+BB d a b) (KK b c d) ∧
      window (2*AA a b c-2*SV a c d+SU a b d) (SW b c d) ∧
      window (AA a b c-LL a c d-(rho a d/2+1)*BB d a b) (LL a c d) ∧
      window (2*AA a b c-SV a c d-(rho a d/2+1)*SU a b d) (SV a c d)) := by
  refine ⟨first_seams a b c d hb hba hac hd hda, ?_, ?_, ?_, ?_, ?_⟩
  · exact A_second a b c d hb hba hac hd hda
  · intro hbd ha
    exact (A_seams a b c d hb hba hac hd hda hbd ha).2.2
  · exact A2_B_third a b c d hb hba hac hd hda
  · exact B_second a b c d hb hba hac hd hda
  · exact C_seams a b c d hb hba hac hd hda

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
