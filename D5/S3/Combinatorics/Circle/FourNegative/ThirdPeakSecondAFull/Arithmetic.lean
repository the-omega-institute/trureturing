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
open private x y z t AA BB LL KK SU SV SW q h H rho fmask jmask mmask Rmask deltaMask isFinite cone_powers power_links from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters
open private branch  from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Parameters

open SourceWidth
open private packetChecks strip_iff_packetChecks from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private blocksWord insertAt from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private size sourceMod base oldValue newValue from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private bankWord genericBanks finiteBanks from
  D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull.Banks
open private freshCut from
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

private theorem A_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b≤d) :
    window (KK b c d-H a c*BB d a b) (KK b c d) ∧
    window (SW b c d-H a c*SU a b d) (SW b c d) := by
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  obtain ⟨hqz,_,hHz,_,_⟩ := power_links a b c d hb hba hac hd hda
  have hyt : y b≤t d := by
    simpa [y,t] using (pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hbd)
  have hx : 0<x a := by omega
  have hy' : 0<y b := by omega
  have ht' : 0<t d := by omega
  have hz : 0<z c := by omega
  have hq : 2≤(q a c : ℤ) := by nlinarith only [hqz,hxz,hx]
  have hQH : (q a c : ℤ)=2*(H a c : ℤ) := by nlinarith only [hqz,hHz,hx]
  have hprod : 0≤x a*(y b-1)-1 := by
    have hp := mul_nonneg (show 0≤x a-1 by omega) (show 0≤y b-1 by omega)
    nlinarith only [hp,hy]
  have hTprod := mul_nonneg ht'.le hprod
  have hxypos : 0<x a*y b := mul_pos hx hy'
  have hbracket : 0<2*x a*y b+x a*t d*(y b-1)-1-t d := by
    nlinarith only [hTprod,hxypos]
  have hbracketnew : 0<2*x a*y b+2*x a*t d*(y b-1)-1-2*t d := by
    nlinarith only [hTprod,hxypos]
  have idold : 2*(KK b c d-(H a c : ℤ)*BB d a b)=
      2*(1+y b)+(q a c : ℤ)*(2*x a*y b+x a*t d*(y b-1)-1-t d) := by
    dsimp [KK,BB]
    rw [←hqz,hQH]
    ring
  have idnew : 2*(SW b c d-(H a c : ℤ)*SU a b d)=
      2*(1+y b)+(q a c : ℤ)*(2*x a*y b+2*x a*t d*(y b-1)-1-2*t d) := by
    dsimp [SW,SU,KK,BB]
    rw [←hqz,hQH]
    ring
  have posold : 0<2*(1+y b)+(q a c : ℤ)*
      (2*x a*y b+x a*t d*(y b-1)-1-t d) := by positivity
  have posnew : 0<2*(1+y b)+(q a c : ℤ)*
      (2*x a*y b+2*x a*t d*(y b-1)-1-2*t d) := by positivity
  have idgap : (q a c : ℤ)*BB d a b-KK b c d=
      (q a c : ℤ)*(1+t d)-1-y b+z c*(t d-y b) := by
    dsimp [BB,KK]
    rw [←hqz]
    ring
  have idgapnew : (q a c : ℤ)*SU a b d-SW b c d=
      (q a c : ℤ)*(1+2*t d)-1-y b+z c*(2*t d-y b) := by
    dsimp [SU,SW,BB,KK]
    rw [←hqz]
    ring
  have hg0 := mul_nonneg (show 0≤(q a c : ℤ)-2 by omega)
    (show 0≤1+t d by omega)
  have hg1 := mul_nonneg hz.le (show 0≤t d-y b by omega)
  have hgn0 := mul_nonneg (show 0≤(q a c : ℤ)-2 by omega)
    (show 0≤1+2*t d by omega)
  have hgn1 := mul_nonneg hz.le (show 0≤2*t d-y b by omega)
  dsimp only [window]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · linarith only [idold,posold]
  · rw [hQH] at idgap
    nlinarith only [idgap,hg0,hg1,hyt,ht,hQH]
  · linarith only [idnew,posnew]
  · rw [hQH] at idgapnew
    nlinarith only [idgapnew,hgn0,hgn1,hyt,ht,hQH]

private theorem A_seams (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b≤d) (ha1 : a=d+1) :
    window (KK b c d-H a c*BB d a b) (KK b c d) ∧
    window (SW b c d-H a c*SU a b d) (SW b c d) ∧
    window (AA a b c-KK b c d-H a c*BB d a b) (AA a b c) ∧
    window (2*AA a b c-SW b c d-H a c*SU a b d) (AA a b c) := by
  obtain ⟨hsecond,hsecondnew⟩ := A_second a b c d hb hba hac hd hda hbd
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  obtain ⟨hqz,_,hHz,_,_⟩ := power_links a b c d hb hba hac hd hda
  have hx : 0<x a := by omega
  have hxx : x a=2*t d := by simp [x,t,ha1,pow_succ,mul_comm]
  have hq : 2≤(q a c : ℤ) := by nlinarith only [hqz,hxz,hx]
  have hQH : (q a c : ℤ)=2*(H a c : ℤ) := by nlinarith only [hqz,hHz,hx]
  have hsmall : 4≤t d*(y b-1)-2*y b := by
    have hp := mul_nonneg (show 0≤y b-4 by omega) (show 0≤t d-2 by omega)
    nlinarith only [hp,ht]
  have hbracket : 0<2*(t d)^2*(y b-1)-4*t d*y b-t d-1 := by
    have hp := mul_nonneg (show 0≤t d by omega)
      (show 0≤t d*(y b-1)-2*y b-4 by omega)
    nlinarith only [hp,ht]
  have htail : 0<4*t d+4*t d*y b-2*y b := by
    have hp := mul_nonneg (show 0≤y b by omega) (show 0≤2*t d-1 by omega)
    nlinarith only [hp,ht]
  have hid : 2*(AA a b c-KK b c d-(H a c : ℤ)*BB d a b)=
      (q a c : ℤ)*(2*(t d)^2*(y b-1)-4*t d*y b-t d-1)+
        4*t d+4*t d*y b-2*y b := by
    dsimp [AA,KK,BB]
    rw [←hqz,hQH,hxx]
    ring
  have hposrhs : 0<(q a c : ℤ)*(2*(t d)^2*(y b-1)-4*t d*y b-t d-1)+
      4*t d+4*t d*y b-2*y b := by
    have hp := mul_nonneg (show 0≤(q a c : ℤ) by omega) hbracket.le
    linarith only [hp,htail]
  have hpos : 0<AA a b c-KK b c d-(H a c : ℤ)*BB d a b := by
    linarith only [hid,hposrhs]
  have hypos : 0<y b := by omega
  have hzpos : 0<z c := by omega
  have hC : 0<1+y b+y b*z c := by positivity
  have hrelation : 2*AA a b c-SW b c d-(H a c : ℤ)*SU a b d=
      2*(AA a b c-KK b c d-(H a c : ℤ)*BB d a b)+
        (1+y b+y b*z c)+(H a c : ℤ) := by dsimp [SW,SU]; ring
  have hnewpos : 0<2*AA a b c-SW b c d-(H a c : ℤ)*SU a b d := by
    have hh : 0≤(H a c : ℤ) := by positivity
    linarith only [hrelation,hpos,hC,hh]
  have hgapid : AA a b c-2*(2*AA a b c-SW b c d-(H a c : ℤ)*SU a b d)=
      ((q a c : ℤ)-2)*(1+2*t d+4*(t d)^2+4*t d*y b)+
        8*(t d)^2+2*t d*y b-2*t d+2*y b+1 := by
    dsimp [AA,SW,SU,KK,BB]
    rw [←hqz,hQH,hxx]
    ring
  have hgaprhs : 0<((q a c : ℤ)-2)*(1+2*t d+4*(t d)^2+4*t d*y b)+
        8*(t d)^2+2*t d*y b-2*t d+2*y b+1 := by
    have h0 := mul_nonneg (show 0≤(q a c : ℤ)-2 by omega)
      (show 0≤1+2*t d+4*(t d)^2+4*t d*y b by positivity)
    have h1 := mul_nonneg (show 0≤t d by omega) (show 0≤4*t d-1 by omega)
    have h2 := mul_nonneg (show 0≤t d by omega) (show 0≤y b by omega)
    nlinarith only [h0,h1,h2,hy]
  refine ⟨hsecond,hsecondnew,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · linarith only [hpos]
  · have hh : 0≤(H a c : ℤ) := by positivity
    linarith only [hgapid,hgaprhs,hrelation,hC,hh,hpos]
  · linarith only [hnewpos]
  · linarith only [hgapid,hgaprhs]


private theorem C_seams (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hbd : b=d+1) (hca : c=a+1) :
    window (AA a b c-(fmask a d : ℤ)*KK b c d) (AA a b c) ∧
    window (2*AA a b c-(fmask a d : ℤ)*SW b c d) (AA a b c) ∧
    window (AA a b c-2*LL a c d+BB d a b) (KK b c d) ∧
    window (2*AA a b c-2*SV a c d+SU a b d) (SW b c d) ∧
    window (AA a b c-LL a c d-(((rho a d/2 : ℕ) : ℤ)+1)*BB d a b) (LL a c d) ∧
    window (2*AA a b c-SV a c d-(((rho a d/2 : ℕ) : ℤ)+1)*SU a b d) (SV a c d) := by
  have ha2 : d+2≤a := by omega
  have ht : 4≤t d := (cone_powers a b c d hb hba hac hd hda).2.1
  let u : ℤ := ((2^(a-d-2) : ℕ) : ℤ)-1
  let v : ℤ := t d-4
  have hu : 0≤u := by
    dsimp [u]
    have hp : (0:ℤ)<2^(a-d-2) := by positivity
    have hh : (1:ℤ)≤2^(a-d-2) := by omega
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using sub_nonneg.mpr hh
  have hv : 0≤v := by dsimp [v]; omega
  have hY : y b=2*t d := by simp [y,t,hbd,pow_succ,mul_comm]
  have hZ : z c=2*x a := by simp [z,x,hca,pow_succ,mul_comm]
  have hF : (fmask a d : ℤ)=3*(u+1) := by dsimp [fmask,u]; push_cast; ring
  have hf := (power_links a b c d hb hba hac hd hda).2.2.2.2 ha2
  have hX : x a=4*t d*(u+1) := by rw [hF] at hf; nlinarith only [hf]
  have hnu : ((rho a d/2 : ℕ) : ℤ)=2*(u+1) := by
    have hn : rho a d/2=2*2^(a-d-2) := by
      dsimp [rho]
      rw [show a-d=(a-d-2)+2 by omega,pow_add]
      norm_num
      omega
    rw [hn]
    dsimp [u]
    push_cast
    ring
  have hnuInt : (rho a d : ℤ)/2=2*(u+1) := by
    have hr : (rho a d : ℤ)=4*(u+1) := by
      dsimp [rho,u]
      rw [show a-d=(a-d-2)+2 by omega,pow_add]
      push_cast
      ring
    rw [hr]
    omega
  have hT : t d=v+4 := by dsimp [v]; ring
  dsimp only [window]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · have hid : AA a b c-(fmask a d : ℤ)*KK b c d=
        16*u^2*v^3+144*u^2*v^2+384*u^2*v+256*u^2+32*u*v^3+296*u*v^2+830*u*v+629*u+16*v^3+152*v^2+446*v+374 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<16*u^2*v^3+144*u^2*v^2+384*u^2*v+256*u^2+32*u*v^3+296*u*v^2+830*u*v+629*u+16*v^3+152*v^2+446*v+374 := by positivity
    linarith only [hid,hp]
  · have hid : AA a b c-2*(AA a b c-(fmask a d : ℤ)*KK b c d)=
        32*u^2*v^3+480*u^2*v^2+2304*u^2*v+3584*u^2+64*u*v^3+952*u*v^2+4552*u*v+7078*u+32*v^3+472*v^2+2248*v+3493 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<32*u^2*v^3+480*u^2*v^2+2304*u^2*v+3584*u^2+64*u*v^3+952*u*v^2+4552*u*v+7078*u+32*v^3+472*v^2+2248*v+3493 := by positivity
    linarith only [hid,hp]
  · have hid : 2*AA a b c-(fmask a d : ℤ)*SW b c d=
        32*u^2*v^3+336*u^2*v^2+1152*u^2*v+1280*u^2+64*u*v^3+688*u*v^2+2434*u*v+2821*u+32*v^3+352*v^2+1282*v+1543 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<32*u^2*v^3+336*u^2*v^2+1152*u^2*v+1280*u^2+64*u*v^3+688*u*v^2+2434*u*v+2821*u+32*v^3+352*v^2+1282*v+1543 := by positivity
    linarith only [hid,hp]
  · have hid : AA a b c-2*(2*AA a b c-(fmask a d : ℤ)*SW b c d)=
        96*u^2*v^2+768*u^2*v+1536*u^2+168*u*v^2+1344*u*v+2694*u+72*v^2+576*v+1155 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<96*u^2*v^2+768*u^2*v+1536*u^2+168*u*v^2+1344*u*v+2694*u+72*v^2+576*v+1155 := by positivity
    linarith only [hid,hp]
  · have hid : AA a b c-2*LL a c d+BB d a b=
        8*u*v^3+92*u*v^2+340*u*v+400*u+8*v^3+92*v^2+341*v+404 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<8*u*v^3+92*u*v^2+340*u*v+400*u+8*v^3+92*v^2+341*v+404 := by positivity
    linarith only [hid,hp]
  · have hid : KK b c d-2*(AA a b c-2*LL a c d+BB d a b)=
        24*u*v^2+216*u*v+480*u+24*v^2+216*v+481 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<24*u*v^2+216*u*v+480*u+24*v^2+216*v+481 := by positivity
    linarith only [hid,hp]
  · have hid : 2*AA a b c-2*SV a c d+SU a b d=
        16*u*v^3+184*u*v^2+696*u*v+864*u+16*v^3+184*v^2+698*v+873 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<16*u*v^3+184*u*v^2+696*u*v+864*u+16*v^3+184*v^2+698*v+873 := by positivity
    linarith only [hid,hp]
  · have hid : SW b c d-2*(2*AA a b c-2*SV a c d+SU a b d)=
        32*u*v^2+272*u*v+576*u+32*v^2+270*v+567 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<32*u*v^2+272*u*v+576*u+32*v^2+270*v+567 := by positivity
    linarith only [hid,hp]
  · have hid : AA a b c-LL a c d-(((rho a d/2 : ℕ) : ℤ)+1)*BB d a b=
        16*u^2*v^3+184*u^2*v^2+704*u^2*v+896*u^2+24*u*v^3+268*u*v^2+986*u*v+1190*u+8*v^3+84*v^2+281*v+289 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<16*u^2*v^3+184*u^2*v^2+704*u^2*v+896*u^2+24*u*v^3+268*u*v^2+986*u*v+1190*u+8*v^3+84*v^2+281*v+289 := by positivity
    linarith only [hid,hp]
  · have hid : LL a c d-2*(AA a b c-LL a c d-(((rho a d/2 : ℕ) : ℤ)+1)*BB d a b)=
        16*u^2*v^2+128*u^2*v+256*u^2+16*u*v^3+240*u*v^2+1172*u*v+1876*u+16*v^3+224*v^2+1046*v+1631 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<16*u^2*v^2+128*u^2*v+256*u^2+16*u*v^3+240*u*v^2+1172*u*v+1876*u+16*v^3+224*v^2+1046*v+1631 := by positivity
    linarith only [hid,hp]
  · have hid : 2*AA a b c-SV a c d-(((rho a d/2 : ℕ) : ℤ)+1)*SU a b d=
        32*u^2*v^3+368*u^2*v^2+1408*u^2*v+1792*u^2+48*u*v^3+536*u*v^2+1980*u*v+2414*u+16*v^3+168*v^2+570*v+614 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<32*u^2*v^3+368*u^2*v^2+1408*u^2*v+1792*u^2+48*u*v^3+536*u*v^2+1980*u*v+2414*u+16*v^3+168*v^2+570*v+614 := by positivity
    linarith only [hid,hp]
  · have hid : SV a c d-2*(2*AA a b c-SV a c d-(((rho a d/2 : ℕ) : ℤ)+1)*SU a b d)=
        32*u^2*v^2+256*u^2*v+512*u^2+32*u*v^3+480*u*v^2+2320*u*v+3652*u+32*v^3+448*v^2+2068*v+3157 := by
      dsimp [AA,BB,LL,KK,SU,SV,SW]
      simp only [hY,hZ,hX,hF,hnu,hnuInt,hT]
      ring
    have hp : 0<32*u^2*v^2+256*u^2*v+512*u^2+32*u*v^3+480*u*v^2+2320*u*v+3652*u+32*v^3+448*v^2+2068*v+3157 := by positivity
    linarith only [hid,hp]

private theorem j_bounds (a b d : ℕ) (hba : b<a) (hd : 2≤d) :
    1≤(jmask a b d : ℤ) ∧ 4*(jmask a b d : ℤ)≤t d := by
  have hpos : 1≤jmask a b d := by
    dsimp [jmask]
    exact le_min (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide))
  have hle : jmask a b d≤2^(d-2) := Nat.min_le_right _ _
  have ht : t d=4*((2^(d-2) : ℕ) : ℤ) := by
    dsimp [t]
    rw [show d=(d-2)+2 by omega,pow_add]
    push_cast
    ring
  exact ⟨by exact_mod_cast hpos,by rw [ht]; exact_mod_cast (show 4*jmask a b d≤4*2^(d-2) by omega)⟩

private theorem B0_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hb0 : d+2≤b) :
    window ((jmask a b d : ℤ)*(KK b c d-q a c*BB d a b)) (KK b c d) ∧
    window ((jmask a b d : ℤ)*(SW b c d-q a c*SU a b d)) (SW b c d) := by
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  have hqz := (power_links a b c d hb hba hac hd hda).1
  obtain ⟨hj,hjt⟩ := j_bounds a b d hba hd
  have hx : 0<x a := by omega
  have hypos : 0<y b := by omega
  have htpos : 0<t d := by omega
  have hzpos : 0<z c := by omega
  have hq : 0<(q a c : ℤ) := by dsimp [q]; positivity
  have hy4 : 4*t d≤y b := by
    have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hb0
    simpa [y,t,pow_add,mul_comm] using hp
  let F := KK b c d-(q a c : ℤ)*BB d a b
  let G := SW b c d-(q a c : ℤ)*SU a b d
  have hbrG : 0<x a*(y b-2*t d)-(2*t d+1) := by
    have hp := mul_nonneg (show 0≤x a-2 by omega) (show 0≤y b-2*t d by omega)
    nlinarith only [hp,hy4,ht]
  have hbrF : 0<x a*(y b-t d)-(t d+1) := by
    have hp := mul_nonneg hx.le htpos.le
    nlinarith only [hp,hbrG,ht]
  have hF : 0<F := by
    have hid : F=(q a c : ℤ)*(x a*(y b-t d)-(t d+1))+y b+1 := by
      dsimp [F,KK,BB]; rw [←hqz]; ring
    rw [hid]
    positivity
  have hG : 0<G := by
    have hid : G=(q a c : ℤ)*(x a*(y b-2*t d)-(2*t d+1))+y b+1 := by
      dsimp [G,SW,SU,KK,BB]; rw [←hqz]; ring
    rw [hid]
    positivity
  have hidF : 2*KK b c d-t d*F=
      (t d+2)*y b*(z c-1)+(4*y b-t d+2)+(t d)^2*z c+
        t d*(q a c : ℤ)*(t d+1) := by
    dsimp [F,KK,BB]; rw [←hqz]; ring
  have hidG : 2*SW b c d-t d*G=
      (3*t d+2)*y b*(z c-1)+2*t d*y b+(4*y b-t d+2)+2*(t d)^2*z c+
        t d*(q a c : ℤ)*(2*t d+1) := by
    dsimp [G,SW,SU,KK,BB]; rw [←hqz]; ring
  have hz1 : 0≤z c-1 := by omega
  have hyterm : 0<4*y b-t d+2 := by omega
  have hgapF : 0<2*KK b c d-t d*F := by rw [hidF]; positivity
  have hgapG : 0<2*SW b c d-t d*G := by rw [hidG]; positivity
  have hpF := mul_nonneg (show 0≤t d-4*(jmask a b d : ℤ) by omega) hF.le
  have hpG := mul_nonneg (show 0≤t d-4*(jmask a b d : ℤ) by omega) hG.le
  have hposF := mul_pos (show 0<(jmask a b d : ℤ) by omega) hF
  have hposG := mul_pos (show 0<(jmask a b d : ℤ) by omega) hG
  change window ((jmask a b d : ℤ)*F) _ ∧ window ((jmask a b d : ℤ)*G) _
  dsimp only [window]
  exact ⟨⟨by linarith only [hposF],by nlinarith only [hgapF,hpF]⟩,
    ⟨by linarith only [hposG],by nlinarith only [hgapG,hpG]⟩⟩

private theorem delta_product (a b c d : ℕ)
    (hR : ¬Rmask a b c d<2^a*2^b) :
    1≤deltaMask a b c d ∧
      deltaMask a b c d*(2^a*2^b)=Rmask a b c d := by
  let J := min (a-b-1) (d-2)
  have hj : jmask a b d=2^J := by
    dsimp [jmask,J]
    by_cases he : a-b-1≤d-2
    · rw [Nat.min_eq_left he,Nat.min_eq_left (Nat.pow_le_pow_right Nat.zero_lt_two he)]
    · have he' : d-2≤a-b-1 := by omega
      rw [Nat.min_eq_right he',Nat.min_eq_right (Nat.pow_le_pow_right Nat.zero_lt_two he')]
  have hr : Rmask a b c d=2^(c-a+J) := by dsimp [Rmask,q]; rw [hj,←pow_add]
  have he : a+b≤c-a+J := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [←pow_add,hr] using (Nat.le_of_not_gt hR)
  let D := 2^(c-a+J-(a+b))
  have hm : (2^a*2^b)*D=Rmask a b c d := by
    dsimp [D]
    rw [hr,←pow_add,←pow_add,show a+b+(c-a+J-(a+b))=c-a+J by omega]
  have hδ : deltaMask a b c d=D := by
    rw [deltaMask,if_neg hR,←hm,Nat.mul_div_cancel_left _ (by positivity)]
  rw [hδ]
  exact ⟨by
    have hp : 0<D := by dsimp [D]; positivity
    omega,by simpa only [Nat.mul_comm] using hm⟩

private theorem B1_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hb1 : b=d+1) (hc2 : a+2≤c) :
    window ((jmask a b d : ℤ)*(KK b c d-q a c*BB d a b)+
      (deltaMask a b c d : ℤ)*BB d a b) (KK b c d) ∧
    window ((jmask a b d : ℤ)*(SW b c d-q a c*SU a b d)+
      (deltaMask a b c d : ℤ)*SU a b d) (SW b c d) := by
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  have hqz := (power_links a b c d hb hba hac hd hda).1
  obtain ⟨hj,hjt⟩ := j_bounds a b d hba hd
  have hY : y b=2*t d := by simp [y,t,hb1,pow_succ,mul_comm]
  have hq : 4≤(q a c : ℤ) := by
    have hp := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤c-a by omega)
    dsimp [q]; exact_mod_cast hp
  have hx : 0<x a := by omega
  have hypos : 0<y b := by omega
  have htpos : 0<t d := by omega
  have hzpos : 0<z c := by omega
  have hBB : 0<BB d a b := by dsimp [BB]; positivity
  have hSU : 0<SU a b d := by
    have hBB1 : 1≤BB d a b := by omega
    dsimp [SU]; omega
  have hRcast : (Rmask a b c d : ℤ)=(q a c : ℤ)*(jmask a b d : ℤ) := by
    simp only [Rmask,Nat.cast_mul]
  have hδ : 1≤(deltaMask a b c d : ℤ) ∧
      (Rmask a b c d : ℤ)≤(deltaMask a b c d : ℤ)*x a*y b ∧
      4*(deltaMask a b c d : ℤ)≤(q a c : ℤ) := by
    by_cases hr : Rmask a b c d<2^a*2^b
    · have he : deltaMask a b c d=1 := by simp [deltaMask,hr]
      have hh : (Rmask a b c d : ℤ)<x a*y b := by
        dsimp [x,y]
        exact_mod_cast hr
      simp only [he,Nat.cast_one,one_mul]
      exact ⟨by omega,hh.le,hq⟩
    · obtain ⟨hdpos,hdmul⟩ := delta_product a b c d hr
      have he : (deltaMask a b c d : ℤ)*x a*y b=(Rmask a b c d : ℤ) := by
        have hh := congrArg (fun n : ℕ => (n : ℤ)) hdmul
        simpa only [x,y,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hh
      have hxybig : t d≤x a*y b := by
        have hp := mul_nonneg hx.le (show 0≤y b-1 by omega)
        nlinarith only [hp,hxt,ht]
      have hp := mul_nonneg (show 0≤(q a c : ℤ) by omega) (show 0≤x a*y b-t d by omega)
      have hjq := mul_nonneg (show 0≤(q a c : ℤ) by omega)
        (show 0≤t d-4*(jmask a b d : ℤ) by omega)
      have hxypos : 0<x a*y b := mul_pos hx hypos
      refine ⟨by exact_mod_cast hdpos,he.ge,?_⟩
      by_contra hh
      have hm := mul_pos (show 0<4*(deltaMask a b c d : ℤ)-(q a c : ℤ) by omega) hxypos
      nlinarith only [hp,hjq,he,hRcast,hm]
  let F := KK b c d-(q a c : ℤ)*BB d a b
  let G := SW b c d-(q a c : ℤ)*SU a b d
  let C := 1+y b+y b*z c
  let E := (jmask a b d : ℤ)*F+(deltaMask a b c d : ℤ)*BB d a b
  let Enew := (jmask a b d : ℤ)*G+(deltaMask a b c d : ℤ)*SU a b d
  have hbrF : 0<x a*t d-t d-1 := by
    have hp := mul_nonneg (show 0≤x a-2 by omega) htpos.le
    nlinarith only [hp,ht]
  have hF : 0<F := by
    have hid : F=(q a c : ℤ)*(x a*t d-t d-1)+y b+1 := by
      dsimp [F,KK,BB]; rw [←hqz,hY]; ring
    rw [hid]; positivity
  have hposE : 0<E := by dsimp [E]; positivity
  have hnewid : Enew=(2*t d+1)*
      ((deltaMask a b c d : ℤ)*x a*y b-(Rmask a b c d : ℤ)+
        (deltaMask a b c d : ℤ)+(jmask a b d : ℤ)) := by
    dsimp [Enew,G,SW,SU,KK,BB]
    rw [hRcast,←hqz,hY]
    ring
  have hbrnew : 0<(deltaMask a b c d : ℤ)*x a*y b-(Rmask a b c d : ℤ)+
      (deltaMask a b c d : ℤ)+(jmask a b d : ℤ) := by omega
  have hposEnew : 0<Enew := by rw [hnewid]; positivity
  have hremid : KK b c d-(t d-1)*F=
      t d*(t d+3)*(z c-2*t d)+2*(t d)^3+4*(t d)^2+3*t d+2+
        ((t d)^2-1)*(q a c : ℤ) := by
    dsimp [F,KK,BB]; rw [←hqz,hY]; ring
  have hzt : 0≤z c-2*t d := by omega
  have ht2 : 0≤(t d)^2-1 := by nlinarith only [ht]
  have hrem : 0<KK b c d-(t d-1)*F := by rw [hremid]; positivity
  have hgapid : 2*(KK b c d-2*E)=
      (t d-4*(jmask a b d : ℤ))*F+
      ((q a c : ℤ)-4*(deltaMask a b c d : ℤ))*BB d a b+
      (KK b c d-(t d-1)*F) := by dsimp [E,F]; ring
  have hp0 := mul_nonneg (show 0≤t d-4*(jmask a b d : ℤ) by omega) hF.le
  have hp1 := mul_nonneg (show 0≤(q a c : ℤ)-4*(deltaMask a b c d : ℤ) by omega) hBB.le
  have hgap : 0<KK b c d-2*E := by linarith only [hgapid,hp0,hp1,hrem]
  have hC : 0<C-2*(q a c : ℤ) := by
    have hxy2 : 0≤x a*y b-2 := by
      have hp := mul_nonneg (show 0≤x a-1 by omega) hypos.le
      nlinarith only [hp,hy]
    have hp := mul_nonneg (show 0≤(q a c : ℤ) by omega) hxy2
    dsimp [C]
    rw [←hqz]
    nlinarith only [hp,hy]
  have hid : SW b c d-2*Enew=2*(KK b c d-2*E)+
      2*((jmask a b d : ℤ)-1)*(C-(q a c : ℤ))+
        (C-2*(q a c : ℤ))+2*(deltaMask a b c d : ℤ) := by
    dsimp [Enew,E,F,G,C,SW,SU]
    ring
  have hp := mul_nonneg (show 0≤(jmask a b d : ℤ)-1 by omega)
    (show 0≤C-(q a c : ℤ) by omega)
  have hgapnew : 0<SW b c d-2*Enew := by linarith only [hid,hgap,hp,hC,hδ.1]
  change window E _ ∧ window Enew _
  dsimp only [window]
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

private theorem B_second (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (hB : d+2≤b ∨ b=d+1 ∧ a+2≤c) :
    let j := (jmask a b d : ℤ)
    let δ : ℤ := if d+2≤b then 0 else deltaMask a b c d
    window (j*(KK b c d-q a c*BB d a b)+δ*BB d a b) (KK b c d) ∧
    window (j*(SW b c d-q a c*SU a b d)+δ*SU a b d) (SW b c d) := by
  rcases hB with hb0|⟨hb1,hc2⟩
  · simpa only [if_pos hb0,zero_mul,add_zero] using B0_second a b c d hb hba hac hd hda hb0
  · have hb0 : ¬d+2≤b := by omega
    simpa only [if_neg hb0] using B1_second a b c d hb hba hac hd hda hb1 hc2

private theorem third_of_positive (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (ha2 : d+2≤a)
    (hpos : 0<AA a b c-(fmask a d : ℤ)*KK b c d-BB d a b) :
    window (AA a b c-fmask a d*KK b c d-BB d a b) (AA a b c) ∧
    window (2*AA a b c-fmask a d*SW b c d-SU a b d) (AA a b c) := by
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  have hf := (power_links a b c d hb hba hac hd hda).2.2.2.2 ha2
  have hx : 0<x a := by omega
  have hy' : 0<y b := by omega
  have hz : 0<z c := by omega
  have ht' : 0<t d := by omega
  have hC : 0<1+y b+y b*z c := by positivity
  have hF : 0≤(fmask a d : ℤ) := by positivity
  have hrelation : 2*AA a b c-(fmask a d : ℤ)*SW b c d-SU a b d=
      2*(AA a b c-(fmask a d : ℤ)*KK b c d-BB d a b)+
        (fmask a d : ℤ)*(1+y b+y b*z c)+1 := by dsimp [SW,SU]; ring
  have hFC := mul_nonneg hF hC.le
  have hnewpos : 0<2*AA a b c-(fmask a d : ℤ)*SW b c d-SU a b d := by
    linarith only [hrelation,hpos,hFC]
  have hid : 2*t d*(AA a b c-2*(2*AA a b c-(fmask a d : ℤ)*SW b c d-SU a b d))=
      8*(t d)^2-2*t d+x a*(3*y b*z c+(8*(t d)^2-6*t d+3)*(1+y b)) := by
    calc
      _ = -6*t d*AA a b c+3*x a*SW b c d+4*t d*SU a b d := by
        linear_combination (SW b c d)*hf
      _ = _ := by dsimp [AA,SW,SU,KK,BB]; ring
  have hc : 0<8*(t d)^2-6*t d+3 := by
    have hp := mul_nonneg ht'.le (show 0≤8*t d-6 by omega)
    nlinarith only [hp]
  have hgaprhs : 0<8*(t d)^2-2*t d+x a*(3*y b*z c+(8*(t d)^2-6*t d+3)*(1+y b)) := by
    have hp := mul_nonneg ht'.le (show 0≤8*t d-2 by omega)
    have hrest : 0<x a*(3*y b*z c+(8*(t d)^2-6*t d+3)*(1+y b)) := by positivity
    nlinarith only [hp,hrest]
  have hgap : 0<AA a b c-2*(2*AA a b c-(fmask a d : ℤ)*SW b c d-SU a b d) := by
    nlinarith only [hid,hgaprhs,ht']
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · linarith only [hpos]
  · linarith only [hgap,hrelation,hFC,hpos]
  · linarith only [hnewpos]
  · linarith only [hgap]

private theorem A2_B_third (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a)
    (ha2 : d+2≤a)
    (hbranch : (b≤d ∧ ¬isFinite a b c d) ∨
      (d+2≤b ∨ b=d+1 ∧ a+2≤c)) :
    window (AA a b c-fmask a d*KK b c d-BB d a b) (AA a b c) ∧
    window (2*AA a b c-fmask a d*SW b c d-SU a b d) (AA a b c) := by
  apply third_of_positive a b c d hb hba hac hd hda ha2
  obtain ⟨hy,ht,hxy,hxt,hxz⟩ := cone_powers a b c d hb hba hac hd hda
  have hf := (power_links a b c d hb hba hac hd hda).2.2.2.2 ha2
  have hx4 : 4*t d≤x a := by
    have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) ha2
    simpa [x,t,pow_add,mul_comm] using hp
  have scaled : 4*t d*(AA a b c-(fmask a d : ℤ)*KK b c d-BB d a b)=
      4*t d*AA a b c-3*x a*KK b c d-4*t d*BB d a b := by
    linear_combination -(KK b c d)*hf
  rcases hbranch with ⟨hbd,hnf⟩|hB
  · by_cases hd2 : d=2
    · have hb2 : b=2 := by omega
      have hc7 : 7≤c := by
        simp only [isFinite,Prod.mk.injEq] at hnf
        omega
      have hx16 : 16≤x a := by
        have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) (show 4≤a by omega)
        simpa [x] using hp
      have hz128 : 128≤z c := by
        have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hc7
        simpa [z] using hp
      have hT : t d=4 := by simp [t,hd2]
      have hY : y b=4 := by simp [y,hb2]
      have hid : 4*t d*AA a b c-3*x a*KK b c d-4*t d*BB d a b=
          x a*(4*z c-255)-64 := by dsimp [AA,KK,BB]; rw [hT,hY]; ring
      have hp := mul_nonneg (show 0≤x a-16 by omega) (show 0≤4*z c-255 by omega)
      rw [hid,hT] at scaled
      nlinarith only [scaled,hp,hz128]
    · have ht8 : 8≤t d := by
        have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) (show 3≤d by omega)
        simpa [t] using hp
      let u : ℤ := x a-4*t d
      let v : ℤ := t d-8
      let w : ℤ := y b-4
      let r : ℤ := z c-8*t d
      have hu : 0≤u := by dsimp [u]; omega
      have hv : 0≤v := by dsimp [v]; omega
      have hw : 0≤w := by dsimp [w]; omega
      have hr : 0≤r := by dsimp [r]; omega
      have hid : 4*t d*AA a b c-3*x a*KK b c d-4*t d*BB d a b=
          4*u*v^2*w+12*u*v^2+1*u*v*w*r+44*u*v*w+4*u*v*r+116*u*v+5*u*w*r+93*u*w+20*u*r+145*u+16*v^3*w+48*v^3+4*v^2*w*r+304*v^2*w+16*v^2*r+844*v^2+52*v*w*r+1780*v*w+208*v*r+4228*v+160*w*r+2976*w+640*r+4384 := by dsimp [AA,BB,KK,u,v,w,r]; ring
      have hp : 0<4*u*v^2*w+12*u*v^2+1*u*v*w*r+44*u*v*w+4*u*v*r+116*u*v+5*u*w*r+93*u*w+20*u*r+145*u+16*v^3*w+48*v^3+4*v^2*w*r+304*v^2*w+16*v^2*r+844*v^2+52*v*w*r+1780*v*w+208*v*r+4228*v+160*w*r+2976*w+640*r+4384 := by positivity
      rw [hid] at scaled
      have htpos : 0<t d := by omega
      nlinarith only [scaled,hp,htpos]
  · have hy2 : 2*t d≤y b := by
      rcases hB with hb0|⟨hb1,hc1⟩
      · have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) (show d+1≤b by omega)
        simpa [t,y,pow_succ,mul_comm] using hp
      · simp [y,t,hb1,pow_succ,mul_comm]
    have hz16 : 16*t d≤z c := by
      rcases hB with hb0|⟨hb1,hc1⟩
      · have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hb0
        have hy4 : 4*t d≤y b := by simpa [t,y,pow_add,mul_comm] using hp
        omega
      · have hp := pow_le_pow_right₀ (a := (2:ℤ)) (by norm_num) hc1
        have hz4 : 4*x a≤z c := by simpa [x,z,pow_add,mul_comm] using hp
        omega
    let v : ℤ := t d-4
    have hv : 0≤v := by dsimp [v]; omega
    have hx : 0<x a := by omega
    have hy' : 0<y b := by omega
    have ht' : 0<t d := by omega
    have htm : 0<t d-3 := by omega
    have hzm : 0≤z c-16*t d := by omega
    have hym : 0≤y b-2*t d := by omega
    have hxm : 0<x a-t d := by omega
    have hid : 4*t d*AA a b c-3*x a*KK b c d-4*t d*BB d a b=
        x a*y b*(t d-3)*(z c-16*t d)+x a*(y b-2*t d)*(12*v^2+52*v+13)+
        x a*(24*v^3+196*v^2+410*v+37)+4*t d*(x a-t d) := by
      dsimp [AA,KK,BB,v]
      ring
    have hp : 0<x a*y b*(t d-3)*(z c-16*t d)+x a*(y b-2*t d)*(12*v^2+52*v+13)+
        x a*(24*v^3+196*v^2+410*v+37)+4*t d*(x a-t d) := by positivity
    rw [hid] at scaled
    nlinarith only [scaled,hp,ht']

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
      window (AA a b c-LL a c d-(((rho a d/2 : ℕ) : ℤ)+1)*BB d a b) (LL a c d) ∧
      window (2*AA a b c-SV a c d-(((rho a d/2 : ℕ) : ℤ)+1)*SU a b d) (SV a c d)) := by
  refine ⟨first_seams a b c d hb hba hac hd hda, ?_, ?_, ?_, ?_, ?_⟩
  · exact A_second a b c d hb hba hac hd hda
  · intro hbd ha
    exact (A_seams a b c d hb hba hac hd hda hbd ha).2.2
  · exact A2_B_third a b c d hb hba hac hd hda
  · exact B_second a b c d hb hba hac hd hda
  · exact C_seams a b c d hb hba hac hd hda


private theorem four_packet_strip (f : ℕ→ℤ) (C N : ℤ)
    (P0 P1 P2 P3 : List ℕ) (n0 n1 n2 n3 : ℕ) (H0 H1 H2 H3 : ℤ)
    (hC : 0≤C) (hNC : N≤2*C+1)
    (hp : ∀ p∈[(P0,n0),(P1,n1),(P2,n2),(P3,n3)], ∀ i∈p.1, 0≤f i)
    (hn : ∀ p∈[(P0,n0),(P1,n1),(P2,n2),(P3,n3)], f p.2≤0)
    (ht0 : 2*f n0=H0-N) (ht1 : 2*f n1=H1-N)
    (ht2 : 2*f n2=H2-N) (ht3 : 2*f n3=H3-N)
    (hH3 : 0<H3)
    (h0 : window ((P0.map f).sum+f n0) H0)
    (h1 : window ((P0.map f).sum+f n0+(P1.map f).sum+f n1) H1)
    (h2 : window ((P0.map f).sum+f n0+(P1.map f).sum+f n1+
      (P2.map f).sum+f n2) H2)
    (hzero : ((blocksWord [(P0,n0),(P1,n1),(P2,n2),(P3,n3)]).map f).sum=0) :
    InStrip f C 0 (blocksWord [(P0,n0),(P1,n1),(P2,n2),(P3,n3)]) := by
  apply (strip_iff_packetChecks f C 0 _ ⟨le_rfl,hC⟩ hp hn).mpr
  simp only [blocksWord,List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil] at hzero
  dsimp only [window] at h0 h1 h2
  simp only [packetChecks,zero_add]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩ <;> omega

private theorem finite_strips (a b c d : ℕ) (hf : isFinite a b c d) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (bankWord a b c d) ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (bankWord a b c d) (freshCut a b c d)) := by
  rcases hf with hf|hf|hf
  all_goals
    simp only [Prod.mk.injEq] at hf
    rcases hf with ⟨rfl,rfl,rfl,rfl⟩
    norm_num [InStrip,bankWord,genericBanks,finiteBanks,branch,insertAt,freshCut,
      oldValue,newValue,base,sourceMod,size,centered]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
