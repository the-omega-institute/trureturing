/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/PalindromicMasks
   generality: I
   mirror-B: none(waiver:private-consumed-OR-completion)
   mirror-E: none(waiver:private-consumed-OR-completion)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Bounded ceilings and nested actual W masks, with the OR cost paid. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.PalindromicArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

/-! Bounded ceilings and nested actual W masks, with the OR cost paid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SecondPeakHighD (Submask submask_le)
open private A B L H K SU SV SW pow_split pow_lower
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

private theorem or_cost (t r : ℕ) : t ||| r≤t+r := by
  classical
  have he : (t ||| r).bitIndices.toFinset=t.bitIndices.toFinset∪r.bitIndices.toFinset := by
    ext i
    simp only [List.mem_toFinset,Nat.mem_bitIndices,Finset.mem_union,Nat.testBit_or,Bool.or_eq_true]
  have hs:=Finset.sum_union_inter (f:=fun i : ℕ => (2:ℕ)^i)
    (s₁:=t.bitIndices.toFinset) (s₂:=r.bitIndices.toFinset)
  rw [←he] at hs
  simp only [Finset.sum_toFinset_bitIndices_two_pow] at hs
  omega

private def palin_r1 (x q : ℤ) : ℕ :=
  let E0:=L x (q*x)-B x (q*x)+K x (q*x) (q*x)-q*L x (q*x)
  if E0<0 then ((-E0+L x (q*x)-1)/L x (q*x)).toNat else 0
private def palin_t (x q : ℤ) : ℕ :=
  let F0:=L x (q*x)-B x (q*x)+A x (q*x) (q*x)-q*L x (q*x)
  ((-F0+L x (q*x)-1)/L x (q*x)).toNat
private def palin_r2 (x q : ℤ) : ℕ := palin_t x q ||| palin_r1 x q

private theorem ceil_remainder (F C : ℤ) (hC : 0<C) (hF : F<0) :
    let r:=(-F+C-1)/C
    1≤r ∧ 0≤F+r*C ∧ F+r*C<C := by
  have h0:=Int.emod_nonneg (-F+C-1) (ne_of_gt hC)
  have h1:=Int.emod_lt_of_pos (-F+C-1) hC
  have he:=Int.ediv_mul_add_emod (-F+C-1) C
  have hr : 1≤(-F+C-1)/C := by
    by_contra hn
    have hm:=mul_nonpos_of_nonpos_of_nonneg (show (-F+C-1)/C≤0 by omega) hC.le
    omega
  exact ⟨hr,by omega,by omega⟩

set_option maxHeartbeats 2400000 in
private theorem palin_choices (a b : ℕ) (ha : 2≤a) (hab : a+2≤b) :
    let x : ℤ:=2^a
    let q : ℤ:=2^(b-a)
    let r1:=palin_r1 x q
    let t:=palin_t x q
    let r2:=palin_r2 x q
    let cap:=2^(b-1)
    let high:=2^(b-a)*(2^(a-1)-1)
    let M1:=high+r1
    let M2:=high+r2
    0≤(r1:ℤ) ∧ 1≤(t:ℤ) ∧
    ((r1:ℤ)≤r2 ∧ (t:ℤ)≤r2 ∧ (r2:ℤ)≤(t:ℤ)+r1 ∧ (r2:ℤ)<q) ∧
    (0≤L x (q*x)-B x (q*x)+K x (q*x) (q*x)-(q-r1)*L x (q*x) ∧
      L x (q*x)-B x (q*x)+K x (q*x) (q*x)-(q-r1)*L x (q*x)<L x (q*x)) ∧
    (0≤L x (q*x)-B x (q*x)+A x (q*x) (q*x)-(q-t)*L x (q*x) ∧
      L x (q*x)-B x (q*x)+A x (q*x) (q*x)-(q-t)*L x (q*x)<L x (q*x)) ∧
    (q=4 ∨ q=8 ∨ 16≤q) ∧ (x=4 ∨ 8≤x) ∧
    (x=4 → q=8 → r1=1 ∧ t=2 ∧ r2=3) ∧
    M1<cap ∧ M2<cap ∧ Submask M1 M2 ∧
    (M1:ℤ)=(cap:ℤ)-q+r1 ∧ (M2:ℤ)=(cap:ℤ)-q+r2 := by
  let x : ℤ:=2^a
  let q : ℤ:=2^(b-a)
  let y:=q*x
  let E0:=L x y-B x y+K x y y-q*L x y
  let F0:=L x y-B x y+A x y y-q*L x y
  have hx : 4≤x := by simpa [x] using pow_lower a 2 ha
  have hq : 4≤q := by simpa [q] using pow_lower (b-a) 2 (by omega)
  have hx0 : 0≤x := by omega
  have hq0 : 0≤q := by omega
  have hy : 0≤y := by dsimp [y]; positivity
  have hL : 0<L x y := by dsimp [L]; positivity
  let u:=x-4
  let w:=q-4
  have hu : 0≤u := by dsimp [u]; omega
  have hw : 0≤w := by dsimp [w]; omega
  have ex : x=u+4 := by dsimp [u]; ring
  have eq : q=w+4 := by dsimp [w]; ring
  have ehi : E0<L x y := by
    have hp : 0<L x y-E0 := by dsimp [E0,K,H,L,B,y]; rw [ex,eq]; ring_nf; positivity
    omega
  have ecap : 0<E0+(q-1)*L x y := by dsimp [E0,K,H,L,B,y]; rw [ex,eq]; ring_nf; positivity
  have flo : F0<0 := by
    have hp : 0< -F0 := by dsimp [F0,A,L,B,y]; rw [ex,eq]; ring_nf; positivity
    omega
  have fcap : 0<F0+(q-1)*L x y := by dsimp [F0,A,L,B,y]; rw [ex,eq]; ring_nf; positivity
  let r1:=palin_r1 x q
  let t:=palin_t x q
  let r2:=palin_r2 x q
  have er : 0≤E0+(r1:ℤ)*L x y ∧ E0+(r1:ℤ)*L x y<L x y := by
    by_cases hn : E0<0
    · have hc:=ceil_remainder E0 (L x y) hL hn
      have cast : (r1:ℤ)=(-E0+L x y-1)/L x y := by
        have rr : r1=((-E0+L x y-1)/L x y).toNat := by
          change (if E0<0 then ((-E0+L x y-1)/L x y).toNat else 0)=_
          rw [if_pos hn]
        rw [rr]
        exact Int.toNat_of_nonneg (by omega)
      rw [cast]
      exact hc.2
    · have hr0 : r1=0 := by simp [r1,palin_r1,E0,y,hn]
      rw [hr0]
      simp only [Nat.cast_zero,zero_mul,add_zero]
      exact ⟨by omega,ehi⟩
  have tr:=ceil_remainder F0 (L x y) hL flo
  have tc : (t:ℤ)=(-F0+L x y-1)/L x y := by
    change (((-F0+L x y-1)/L x y).toNat:ℤ)=_
    exact Int.toNat_of_nonneg (by omega)
  have ft : 1≤(t:ℤ) ∧ 0≤F0+(t:ℤ)*L x y ∧ F0+(t:ℤ)*L x y<L x y := by simpa only [tc] using tr
  have rcap : (r1:ℤ)<q := by
    by_contra hn
    have hm:=mul_le_mul_of_nonneg_right (show q≤(r1:ℤ) by omega) hL.le
    nlinarith only [hm,er.2,ecap]
  have tcap : (t:ℤ)<q := by
    by_contra hn
    have hm:=mul_le_mul_of_nonneg_right (show q≤(t:ℤ) by omega) hL.le
    nlinarith only [hm,ft.2.2,fcap]
  have r1N : r1<2^(b-a) := by exact_mod_cast (show (r1:ℤ)<(2:ℤ)^(b-a) from rcap)
  have tN : t<2^(b-a) := by exact_mod_cast (show (t:ℤ)<(2:ℤ)^(b-a) from tcap)
  have r2N : r2<2^(b-a) := Nat.or_lt_two_pow tN r1N
  have sr : Submask r1 r2 := by
    intro i hi
    change (t ||| r1).testBit i=true
    rw [Nat.testBit_or]
    simp only [Bool.or_eq_true]
    exact Or.inr hi
  have st : Submask t r2 := by
    intro i hi
    change (t ||| r1).testBit i=true
    rw [Nat.testBit_or]
    simp only [Bool.or_eq_true]
    exact Or.inl hi
  have rr:=submask_le r1 r2 sr
  have tt:=submask_le t r2 st
  have cost:=or_cost t r1
  have qd : q=4 ∨ q=8 ∨ 16≤q := by
    by_cases h2 : b-a=2
    · left; simp [q,h2]
    · by_cases h3 : b-a=3
      · exact Or.inr (Or.inl (by simp [q,h3]))
      · exact Or.inr (Or.inr (by simpa [q] using pow_lower (b-a) 4 (by omega)))
  have xd : x=4 ∨ 8≤x := by
    by_cases ha2 : a=2
    · left; simp [x,ha2]
    · right; simpa [x] using pow_lower a 3 (by omega)
  have exceptional : x=4 → q=8 → r1=1 ∧ t=2 ∧ r2=3 := by
    intro ex4 eq8
    norm_num [r1,t,r2,palin_r1,palin_t,palin_r2,ex4,eq8,A,B,L,H,K]
  let high:=2^(b-a)*(2^(a-1)-1)
  have capid : (2^(b-1):ℕ)=2^(b-a)*2^(a-1) := by rw [←pow_add]; congr 1; omega
  have highid : high+2^(b-a)=2^(b-1) := by
    dsimp [high]
    rw [capid]
    calc
      2^(b-a)*(2^(a-1)-1)+2^(b-a)=2^(b-a)*((2^(a-1)-1)+1) := by ring
      _ = 2^(b-a)*2^(a-1) := by rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]
  have mc1 : high+r1<2^(b-1) := by omega
  have mc2 : high+r2<2^(b-1) := by omega
  have nested : Submask (high+r1) (high+r2) := by
    intro i hi
    dsimp [high] at hi ⊢
    rw [Nat.testBit_two_pow_mul_add (2^(a-1)-1) r1N i] at hi
    rw [Nat.testBit_two_pow_mul_add (2^(a-1)-1) r2N i]
    by_cases hii : i<b-a
    · simp only [if_pos hii] at hi ⊢
      exact sr i hi
    · simp only [if_neg hii] at hi ⊢
      exact hi
  have mids (r : ℕ) : ((high+r:ℕ):ℤ)=((2^(b-1):ℕ):ℤ)-q+r := by
    have hh : (high:ℤ)+(2:ℤ)^(b-a)=((2^(b-1):ℕ):ℤ) := by exact_mod_cast highid
    rw [Nat.cast_add]
    change (high:ℤ)+(r:ℤ)=((2^(b-1):ℕ):ℤ)-(2:ℤ)^(b-a)+(r:ℤ)
    linarith only [hh]
  dsimp only
  exact ⟨by positivity,ft.1,⟨by exact_mod_cast rr,by exact_mod_cast tt,
      by exact_mod_cast (show r2≤t+r1 from cost),by exact_mod_cast (show r2<2^(b-a) from r2N)⟩,
    by
      dsimp [E0,y] at er
      constructor <;> nlinarith only [er.1,er.2],
    by
      dsimp [F0,y] at ft
      constructor <;> nlinarith only [ft.2.1,ft.2.2],
    qd,xd,exceptional,mc1,mc2,nested,mids r1,mids r2⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
