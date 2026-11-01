/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerSeams
   generality: I
   mirror-B: none(waiver:private-consumed-cumulative-seams)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Local bank increments, cumulative postterminal prefixes and all twelve gates. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerCeiling
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private heads newHeads successor newSuccessor sourceN delta eight_recurrences
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private F E
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private lowerC
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerCeiling
open private lowerPolynomial
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerPolynomial
open private dot termOrder doubledSeams gate
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams

-- The complement f-c occurs only in bank FOUR. Bank THREE is all V positives.
private def lowerAllocation (u c f e : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![u,0,0,0], ![0,0,c,e], ![0,u,0,0], ![0,0,f-c,0]]
private def lowerNativeAllocation (a b s : ℕ) : Fin 4 → Fin 4 → ℤ :=
  lowerAllocation ((2:ℤ)^(s-1)-1) (lowerC a b s) (F b) (E a)

-- d1,d2,d3 and e1,e2,e3 are INDIVIDUAL doubled bank increments.
-- In particular e3 includes the fresh 2A at the START of bank 3.
private theorem lower_local_increments (x y z u c f e : ℤ)
    (hu : 2*(u+1)=z) (he : 2*(e+1)=x) :
    let A := heads x y z 0
    let B := heads x y z 1
    let L := heads x y z 2
    let M := heads x y z 3
    let Bn := newHeads x y z 1
    let Ln := newHeads x y z 2
    let Mn := newHeads x y z 3
    (∀ r : Fin 3,
      2*dot (heads x y z) (lowerAllocation u c f e r.castSucc)+
          successor x y z (termOrder r.castSucc)-sourceN x y z =
        ![B+M-2*A,A+B-2*M+2*c*L,L-2*B+A] r) ∧
    (∀ r : Fin 3,
      2*dot (newHeads x y z) (lowerAllocation u c f e r.castSucc)+
          (if r=2 then 2*A else 0)+newSuccessor x y z (termOrder r.castSucc)-
          (2*sourceN x y z+1) =
        ![Bn+Mn-4*A,A+Bn-2*Mn+2*c*Ln,Ln-2*Bn+3*A] r) := by
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩ := eight_recurrences x y z
  have hn0 : newHeads x y z 0=2*heads x y z 0 := rfl
  rw [hn0] at r4
  dsimp only
  constructor
  · intro r
    fin_cases r <;> dsimp only [lowerAllocation,dot,successor,termOrder,Fin.castSucc] <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    · linear_combination (heads x y z 0)*hu+r0
    · linear_combination (heads x y z 3)*he+r3
    · linear_combination (heads x y z 1)*hu+r1
  · intro r
    fin_cases r <;> dsimp only [lowerAllocation,dot,newSuccessor,termOrder,Fin.castSucc] <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;> simp only [hn0]
    · linear_combination (2*heads x y z 0)*hu+r4
    · linear_combination (newHeads x y z 3)*he+r7
    · linear_combination (newHeads x y z 1)*hu+r5

-- The actual seams are CUMULATIVE POSTTERMINAL prefixes:
-- S2=d1+d2, S3=d1+d2+d3; T2=e1+e2, T3=e1+e2+e3.
private theorem lower_cumulative_seams (x y z u c f e : ℤ)
    (hu : 2*(u+1)=z) (he : 2*(e+1)=x) :
    let A := heads x y z 0
    let B := heads x y z 1
    let L := heads x y z 2
    let M := heads x y z 3
    let Bn := newHeads x y z 1
    let Ln := newHeads x y z 2
    let Mn := newHeads x y z 3
    doubledSeams (heads x y z) (successor x y z) (sourceN x y z) 0
        (lowerAllocation u c f e) =
      ![B+M-2*A,2*B-A-M+2*c*L,(2*c+1)*L-M] ∧
    doubledSeams (newHeads x y z) (newSuccessor x y z) (2*sourceN x y z+1) A
        (lowerAllocation u c f e) =
      ![Bn+Mn-4*A,2*Bn-3*A-Mn+2*c*Ln,(2*c+1)*Ln-Mn] := by
  have h := lower_local_increments x y z u c f e hu he
  have a0 := h.1 0
  have a1 := h.1 1
  have a2 := h.1 2
  have b0 := h.2 0
  have b1 := h.2 1
  have b2 := h.2 2
  dsimp only [Fin.castSucc] at a0 a1 a2 b0 b1 b2 ⊢
  simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at a0 a1 a2 b0 b1 b2
  constructor <;> funext r <;> fin_cases r <;>
    dsimp only [doubledSeams] <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;> linarith

private theorem lower_last_seams (x y z u c f e : ℤ)
    (hu : 2*(u+1)=z) (hf : 2*(f+1)=y) (he : 2*(e+1)=x) :
    doubledSeams (heads x y z) (successor x y z) (sourceN x y z) 0
        (lowerAllocation u c f e) 2+
      2*dot (heads x y z) (lowerAllocation u c f e 3)+
      successor x y z 1-sourceN x y z=0 ∧
    doubledSeams (newHeads x y z) (newSuccessor x y z) (2*sourceN x y z+1)
        (heads x y z 0) (lowerAllocation u c f e) 2+
      2*dot (newHeads x y z) (lowerAllocation u c f e 3)+
      newSuccessor x y z 1-(2*sourceN x y z+1)=0 := by
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩ := eight_recurrences x y z
  have r8 : newHeads x y z 0=2*heads x y z 0 := rfl
  rw [←hu,←hf,←he] at r0 r1 r2 r3 r4 r5 r6 r7 r8 ⊢
  dsimp only [doubledSeams,dot,lowerAllocation,successor,newSuccessor]
  simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  constructor
  · linear_combination r0+r1+r2+r3
  · linear_combination r4+r5+r6+r7-2*r8

private theorem lower_delta (x y z : ℤ) :
    heads x y z 3*newHeads x y z 2-newHeads x y z 3*heads x y z 2=
      heads x y z 0*z^2 := by
  dsimp [heads,newHeads,delta]
  ring

private theorem lower_gate_bounds (x y z u c f e : ℤ)
    (hu : 2*(u+1)=z) (he : 2*(e+1)=x)
    (hL : 1≤heads x y z 2) (hLn : 1≤newHeads x y z 2)
    (hP : ∀ i, 0<lowerPolynomial x y z i)
    (hc : heads x y z 3-heads x y z 2≤2*heads x y z 2*c ∧
      2*heads x y z 2*c≤heads x y z 3+heads x y z 2-1) :
    ∀ r slot, 0≤gate x y z (lowerAllocation u c f e) r slot := by
  let A := heads x y z 0
  let B := heads x y z 1
  let L := heads x y z 2
  let M := heads x y z 3
  let Bn := newHeads x y z 1
  let Ln := newHeads x y z 2
  let Mn := newHeads x y z 3
  have hD : M*Ln-Mn*L=A*z^2 := lower_delta x y z
  have p0 := hP 0
  have p1 := hP 1
  have p2 := hP 2
  have p3 := hP 3
  have p4 := hP 4
  have p5 := hP 5
  have p6 := hP 6
  have p7 := hP 7
  have p8 := hP 8
  have p9 := hP 9
  have p10 := hP 10
  change 0<B+M-2*A at p0
  change 0<2*A-B-1 at p1
  change 0<Bn+Mn-4*A at p2
  change 0<4*A-Bn-1 at p3
  change 0<2*B-A-L at p4
  change 0<A-B-L at p5
  change 0<L*(2*Bn-3*A-Ln)+A*z^2 at p6
  change 0<L*(3*A-Bn-1-Ln)-A*z^2 at p7
  change 0<A-2*L at p8
  change 0<A*z^2 at p9
  change 0<L*(A-1-2*Ln)-A*z^2 at p10
  change 1≤L at hL
  change 1≤Ln at hLn
  change M-L≤2*L*c ∧ 2*L*c≤M+L-1 at hc
  have cancel (t : ℤ) (ht : 0≤L*t) : 0≤t := by
    by_contra h
    have hn := mul_neg_of_pos_of_neg (show 0<L by omega) (show t<0 by omega)
    omega
  have lo := mul_nonneg (show 0≤Ln by omega) (sub_nonneg.mpr hc.1)
  have hi := mul_nonneg (show 0≤Ln by omega) (sub_nonneg.mpr hc.2)
  have n2 : 0≤2*Bn-3*A-Mn+2*c*Ln := by
    apply cancel
    have hiD : L*(2*Bn-3*A-Mn+2*c*Ln)=
        (L*(2*Bn-3*A-Ln)+A*z^2)+Ln*(2*L*c-(M-L)) := by
      rw [←hD]
      ring
    rw [hiD]
    linarith
  have n2cap : 0≤Bn-1-(2*Bn-3*A-Mn+2*c*Ln) := by
    apply cancel
    have hiD : L*(Bn-1-(2*Bn-3*A-Mn+2*c*Ln))=
        (L*(3*A-Bn-1-Ln)-A*z^2)+Ln+Ln*(M+L-1-2*L*c) := by
      rw [←hD]
      ring
    rw [hiD]
    linarith
  have n3 : 0≤(2*c+1)*Ln-Mn := by
    apply cancel
    have hiD : L*((2*c+1)*Ln-Mn)=A*z^2+Ln*(2*L*c-(M-L)) := by
      rw [←hD]
      ring
    rw [hiD]
    linarith
  have n3cap : 0≤A-1-((2*c+1)*Ln-Mn) := by
    apply cancel
    have hiD : L*(A-1-((2*c+1)*Ln-Mn))=
        (L*(A-1-2*Ln)-A*z^2)+Ln+Ln*(M+L-1-2*L*c) := by
      rw [←hD]
      ring
    rw [hiD]
    linarith
  -- Explicit old cumulative bounds use the signed rounding interval itself.
  -- No positivity assumption is made on the residual M-2*c*L.
  have o2 : 0≤2*B-A-M+2*c*L := by
    nlinarith only [hc.1,p4]
  have o2cap : 0≤B-1-(2*B-A-M+2*c*L) := by
    nlinarith only [hc.2,p5]
  have o3 : 0≤(2*c+1)*L-M := by
    nlinarith only [hc.1]
  have o3cap : 0≤A-1-((2*c+1)*L-M) := by
    nlinarith only [hc.2,p8]
  have seams := lower_cumulative_seams x y z u c f e hu he
  intro r slot
  dsimp only [gate]
  rw [seams.1,seams.2]
  fin_cases r <;> fin_cases slot <;>
    dsimp only [successor,newSuccessor] <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] <;> change 0≤_ <;>
    dsimp only [A,B,L,M,Bn,Ln,Mn] at * <;>
    linarith only [p0,p1,p2,p3,o2,o2cap,o3,o3cap,n2,n2cap,n3,n3cap]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
