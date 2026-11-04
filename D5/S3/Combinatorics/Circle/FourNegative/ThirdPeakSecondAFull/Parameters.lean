/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Parameters
   generality: I
   mirror-B: none(waiver:physical-dependent-source-family)
   mirror-E: none(waiver:physical-dependent-source-family)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise, mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Original five-case cone parameters, native masks, and literal cuts. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import Mathlib.Data.Int.DivMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size sourceMod base newBase charge oldValue newValue negatives chainLength chainStart
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def x (a : ℕ) : ℤ := 2^a
private def y (b : ℕ) : ℤ := 2^b
private def z (c : ℕ) : ℤ := 2^c
private def t (d : ℕ) : ℤ := 2^d

private def AA (a b c : ℕ) : ℤ := 1+x a+x a*y b+x a*y b*z c
private def BB (d a b : ℕ) : ℤ := 1+t d+x a*t d+x a*y b*t d
private def LL (a c d : ℕ) : ℤ := 1+z c+z c*t d+x a*z c*t d
private def KK (b c d : ℕ) : ℤ := 1+y b+y b*z c+y b*z c*t d
private def SU (a b d : ℕ) : ℤ := 2*BB d a b-1
private def SV (a c d : ℕ) : ℤ := 2*LL a c d-z c-1
private def SW (b c d : ℕ) : ℤ := 2*KK b c d-(1+y b+y b*z c)

private def full (a b c d : ℕ) (r : Fin 4) : ℕ :=
  2^(chainLength a b c d r-1)-1
private def stock (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) mask
private def complement (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  stock a b c d r (full a b c d r ^^^ mask)
private def terminal (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d-1,d+c-1,d+c+b-1,a+b+c+d-1]

private def q (a c : ℕ) : ℕ := 2^(c-a)
private def h (b c : ℕ) : ℕ := 2^(c-b-1)
private def H (a c : ℕ) : ℕ := 2^(c-a-1)
private def rho (a d : ℕ) : ℕ := 2^(a-d)
private def fmask (a d : ℕ) : ℕ := 3*2^(a-d-2)
private def jmask (a b d : ℕ) : ℕ := min (2^(a-b-1)) (2^(d-2))
private def mmask (a b d : ℕ) : ℕ := jmask a b d-1
private def Rmask (a b c d : ℕ) : ℕ := q a c*jmask a b d
private def deltaMask (a b c d : ℕ) : ℕ :=
  if Rmask a b c d < 2^a*2^b then 1 else Rmask a b c d/(2^a*2^b)

private def isFinite (a b c d : ℕ) : Prop :=
  (a,b,c,d)=(4,2,5,2) ∨ (a,b,c,d)=(4,2,6,2) ∨ (a,b,c,d)=(5,2,6,2)

inductive Branch
  | a1 | a2 | b0 | b1one | b1quot | c | finite1 | finite2 | finite3
deriving DecidableEq

private def branch (a b c d : ℕ) : Branch :=
  if (a,b,c,d)=(4,2,5,2) then .finite1 else
  if (a,b,c,d)=(4,2,6,2) then .finite2 else
  if (a,b,c,d)=(5,2,6,2) then .finite3 else
  if b≤d then if a=d+1 then .a1 else .a2 else
  if d+2≤b then .b0 else
  if a+2≤c then
    if Rmask a b c d < 2^a*2^b then .b1one else .b1quot
  else .c

private def freshCut (a b c d : ℕ) : ℕ :=
  if (a,b,c,d)=(4,2,5,2) then 7 else
  if (a,b,c,d)=(4,2,6,2) then 8 else
  if (a,b,c,d)=(5,2,6,2) then 8 else
  if b≤d then a+b+1 else
  if d+2≤b then a+b else
  if a+2≤c then a+b+1 else 1

private theorem cone_powers (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    4≤y b ∧ 4≤t d ∧ 2*y b≤x a ∧ 2*t d≤x a ∧ 2*x a≤z c := by
  have hpow : ∀ {u v : ℕ}, u≤v → (2:ℤ)^u≤2^v := by
    intro u v huv
    exact pow_le_pow_right₀ (by norm_num) huv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [y] using hpow hb
  · simpa [t] using hpow hd
  · simpa [x,y,pow_succ,mul_comm] using hpow (show b+1≤a by omega)
  · simpa [x,t,pow_succ,mul_comm] using hpow (show d+1≤a by omega)
  · simpa [x,z,pow_succ,mul_comm] using hpow (show a+1≤c by omega)

private theorem power_links (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    x a*(q a c : ℤ)=z c ∧
    2*y b*(h b c : ℤ)=z c ∧
    2*x a*(H a c : ℤ)=z c ∧
    t d*(rho a d : ℤ)=x a ∧
    (d+2≤a → 4*t d*(fmask a d : ℤ)=3*x a) := by
  have splitpow (u v w : ℕ) (he : u+v=w) :
      (2:ℤ)^u*2^v=2^w := by rw [←pow_add,he]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [x,q,z] using splitpow a (c-a) c (by omega)
  · dsimp [y,h,z]
    push_cast
    calc
      2*2^b*2^(c-b-1) = (2:ℤ)^(b+1)*2^(c-b-1) := by rw [pow_succ]; ring
      _ = 2^c := splitpow _ _ _ (by omega)
  · dsimp [x,H,z]
    push_cast
    calc
      2*2^a*2^(c-a-1) = (2:ℤ)^(a+1)*2^(c-a-1) := by rw [pow_succ]; ring
      _ = 2^c := splitpow _ _ _ (by omega)
  · simpa [t,rho,x] using splitpow d (a-d) a (by omega)
  · intro ha2
    dsimp [t,fmask,x]
    push_cast
    have he := splitpow (d+2) (a-d-2) a (by omega)
    simp only [pow_add] at he
    norm_num at he
    linear_combination 3*he

private theorem cut_bounds (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : 2≤d) (hda : d<a) :
    0 < freshCut a b c d ∧ freshCut a b c d < size a b c d := by
  unfold freshCut size
  split_ifs <;> simp_all only [Prod.mk.injEq] <;> omega

private theorem bases_identify (a b c d : ℕ) :
    base a b c d 0=AA a b c ∧ base a b c d 1=BB d a b ∧
    base a b c d 2=LL a c d ∧ base a b c d 3=KK b c d := by
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [base,AA,BB,LL,KK,x,y,z,t] <;> ring

private theorem new_bases_identify (a b c d : ℕ) :
    newBase a b c d 0=2*AA a b c ∧ newBase a b c d 1=SU a b d ∧
    newBase a b c d 2=SV a c d ∧ newBase a b c d 3=SW b c d := by
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [newBase,base,charge,SU,SV,SW,AA,BB,LL,KK,x,y,z,t] <;> ring


end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakSecondAFull
