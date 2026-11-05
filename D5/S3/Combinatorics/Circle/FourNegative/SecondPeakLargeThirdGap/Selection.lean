/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Selection
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Signed ceiling, its exact remainder, and all paired seam gates. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.FirstSeams
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.CeilingGates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.RoundingGates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.TailGates

/-! Signed ceiling, its exact remainder, and all paired seam gates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open private DD AA BB LL MM NN BBn LLn MMn EE KK JJ dyadicT dyadicZ dyadicY gate
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.Algebra
open private first_old_lower_2S1 first_new_lower_2T1 first_old_upper first_new_upper
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.FirstSeams
open private ceil_E_lower ceil_H_upper ceil_old_cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.CeilingGates
open private ceil_new_lower_K ceil_new_upper_J
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.RoundingGates
open private third_old_lower_S3 third_new_lower_T3 third_old_upper third_new_upper fresh_N_minus_A
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.TailGates

private theorem all_gates (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    ∀ i : Fin 14, 0 ≤ gate i x R Z lam := by
  intro i
  fin_cases i
  · exact first_old_lower_2S1 x R Z lam hx hR hZ hlam
  · exact first_new_lower_2T1 x R Z lam hx hR hZ hlam
  · exact first_old_upper x R Z lam hx hR hZ hlam
  · exact first_new_upper x R Z lam hx hR hZ hlam
  · exact ceil_E_lower x R Z lam hx hR hZ hlam
  · exact ceil_H_upper x R Z lam hx hR hZ hlam
  · exact ceil_old_cap x R Z lam hx hR hZ hlam
  · exact ceil_new_lower_K x R Z lam hx hR hZ hlam
  · exact ceil_new_upper_J x R Z lam hx hR hZ hlam
  · exact third_old_lower_S3 x R Z lam hx hR hZ hlam
  · exact third_new_lower_T3 x R Z lam hx hR hZ hlam
  · exact third_old_upper x R Z lam hx hR hZ hlam
  · exact third_new_upper x R Z lam hx hR hZ hlam
  · exact fresh_N_minus_A x R Z lam hx hR hZ hlam

/-- Signed integer ceiling; no real approximation or nonnegative truncation. -/
private def ceilDiv (E den : ℤ) : ℤ := -((-E)/den)
private def chooseH (x y z t lam : ℤ) : ℤ :=
  ceilDiv (EE x y z t) (2*lam*LL x z t)
private def roundDelta (x y z t lam : ℤ) : ℤ :=
  2*lam*LL x z t*chooseH x y z t lam-EE x y z t
private def secondNew (x y z t lam : ℤ) : ℤ :=
  2*roundDelta x y z t lam+AA x y z-DD y z
    -2*(lam*chooseH x y z t lam)*(z+1)-2

/-- Both signed ceiling bounds precede every natural-mask conversion. -/
private theorem ceiling_range (E den z : ℤ) (hd : 0<den)
    (hE : 0 ≤ E) (hcap : E ≤ den*(z-1)) :
    0 ≤ ceilDiv E den ∧ ceilDiv E den ≤ z-1 ∧
    0 ≤ den*ceilDiv E den-E ∧ den*ceilDiv E den-E<den := by
  have rem0 := Int.emod_nonneg (-E) (ne_of_gt hd)
  have remlt := Int.emod_lt_of_pos (-E) hd
  have division := Int.emod_add_mul_ediv (-E) den
  have delta_eq : den*ceilDiv E den-E=(-E)%den := by
    dsimp [ceilDiv]
    nlinarith only [division]
  have delta0 : 0 ≤ den*ceilDiv E den-E := by rw [delta_eq]; exact rem0
  have deltalt : den*ceilDiv E den-E<den := by rw [delta_eq]; exact remlt
  have H0 : 0 ≤ ceilDiv E den := by
    by_contra h
    have hH : ceilDiv E den ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hH hd.le
    nlinarith
  have Hcap : ceilDiv E den ≤ z-1 := by
    by_contra h
    have hH : z ≤ ceilDiv E den := by omega
    have := mul_le_mul_of_nonneg_left hH hd.le
    nlinarith
  exact ⟨H0,Hcap,delta0,deltalt⟩

private structure SeamBounds (x y z t lam : ℤ) : Prop where
  H_nonneg : 0 ≤ chooseH x y z t lam
  H_upper : chooseH x y z t lam ≤ z-1
  delta_nonneg : 0 ≤ roundDelta x y z t lam
  delta_lt : roundDelta x y z t lam<2*lam*LL x z t
  first_old_nonneg : 0 ≤ BB x y t+MM y z t-2*AA x y z
  first_old_cap : BB x y t+MM y z t-2*AA x y z ≤ MM y z t-1
  first_new_nonneg : 0 ≤ 2*BB x y t-2*AA x y z+MMn y z t-1
  first_new_cap : 2*BB x y t-2*AA x y z+MMn y z t-1 ≤ MMn y z t-1
  second_old_cap : roundDelta x y z t lam ≤ AA x y z-1
  second_new_nonneg : 0 ≤ secondNew x y z t lam
  second_new_cap : secondNew x y z t lam ≤ AA x y z-1
  third_old_nonneg : 0 ≤ BB x y t-lam*LL x z t
  third_old_cap : 2*(BB x y t-lam*LL x z t) ≤ BB x y t-1
  third_new_nonneg : 0 ≤ BBn x y t-lam*LLn x z t
  third_new_cap : 2*(BBn x y t-lam*LLn x z t) ≤ BBn x y t-1
  fresh_cap : AA x y z ≤ NN x y z t
  rounding_identity : LL x z t*secondNew x y z t lam=
    LLn x z t*roundDelta x y z t lam+KK x y z t

set_option maxHeartbeats 2000000 in
private theorem selection_bounds (x R Z lam : ℤ)
    (hx : 4 ≤ x) (hR : 1 ≤ R) (hZ : 1 ≤ Z) (hlam : 1 ≤ lam) :
    SeamBounds x (dyadicY x R Z lam) (dyadicZ x R Z) (dyadicT x R) lam := by
  let t := dyadicT x R
  let z := dyadicZ x R Z
  let y := dyadicY x R Z lam
  let A := AA x y z
  let B := BB x y t
  let L := LL x z t
  let M := MM y z t
  let Bn := BBn x y t
  let Ln := LLn x z t
  let Mn := MMn y z t
  let E := EE x y z t
  let K := KK x y z t
  let J := JJ x y z t lam
  let H := chooseH x y z t lam
  let delta := roundDelta x y z t lam
  let T2 := secondNew x y z t lam
  have hx0 : 0<x := by omega
  have hR0 : 0<R := by omega
  have hZ0 : 0<Z := by omega
  have hlam0 : 0<lam := by omega
  have ht0 : 0<t := by dsimp [t,dyadicT]; positivity
  have hz0 : 0<z := by dsimp [z,dyadicZ,dyadicT]; positivity
  have L0 : 0<L := by dsimp [L,LL]; positivity
  have Ln0 : 0<Ln := by
    have eqn : Ln=2*x*z*t+2*z*t+z+1 := by dsimp [Ln,LLn,LL]; ring
    rw [eqn]
    positivity
  have den0 : 0<2*lam*L := by positivity
  have gs := all_gates x R Z lam hx hR hZ hlam
  have g0 := gs 0
  change 0 ≤ B+M-2*A at g0
  have g1 := gs 1
  change 0 ≤ 2*B-2*A+Mn-1 at g1
  have g2 := gs 2
  change 0 ≤ 2*A-B-1 at g2
  have g3 := gs 3
  change 0 ≤ 2*A-2*B at g3
  have g4 := gs 4
  change 0 ≤ E at g4
  have g5 := gs 5
  change 0 ≤ 2*lam*L*(z-1)-E at g5
  have g6 := gs 6
  change 0 ≤ A-1-2*lam*L at g6
  have g7 := gs 7
  change 0 ≤ K at g7
  have g8 := gs 8
  change 0 ≤ J at g8
  have g9 := gs 9
  change 0 ≤ B-lam*L at g9
  have g10 := gs 10
  change 0 ≤ Bn-lam*Ln at g10
  have g11 := gs 11
  change 0 ≤ 2*lam*L-B-1 at g11
  have g12 := gs 12
  change 0 ≤ 2*lam*Ln-Bn-1 at g12
  have g13 := gs 13
  change 0 ≤ NN x y z t-A at g13
  obtain ⟨H0,Hcap,delta0,deltalt⟩ := ceiling_range E (2*lam*L) z den0 g4 (by linarith only [g5])
  change 0 ≤ H at H0
  change H ≤ z-1 at Hcap
  change 0 ≤ delta at delta0
  change delta<2*lam*L at deltalt
  have exact_round : L*T2=Ln*delta+K := by
    have hdelta : 2*lam*L*H=E+delta := by dsimp [delta,roundDelta,H,E,L]; ring
    change L*(2*delta+A-DD y z-2*(lam*H)*(z+1)-2)=
      (2*L-z-1)*delta+(L*(A-DD y z-2)-E*(z+1))
    linear_combination -(z+1)*hdelta
  have t20 : 0 ≤ T2 := by
    have hp := mul_nonneg Ln0.le delta0
    by_contra hnot
    have negative := mul_neg_of_pos_of_neg L0 (show T2<0 by omega)
    nlinarith only [exact_round,hp,g7,negative]
  have t2cap : T2 ≤ A-1 := by
    have hp := mul_le_mul_of_nonneg_left deltalt.le Ln0.le
    have jgate : 0 ≤ L*(A-1)-2*lam*L*Ln-K := g8
    by_contra hnot
    have strict := mul_lt_mul_of_pos_left (show A-1<T2 by omega) L0
    nlinarith only [exact_round,hp,jgate,strict]
  change SeamBounds x y z t lam
  exact {
    H_nonneg := H0
    H_upper := Hcap
    delta_nonneg := delta0
    delta_lt := deltalt
    first_old_nonneg := g0
    first_old_cap := by linarith only [g2]
    first_new_nonneg := g1
    first_new_cap := by linarith only [g3]
    second_old_cap := by linarith only [deltalt,g6]
    second_new_nonneg := t20
    second_new_cap := t2cap
    third_old_nonneg := g9
    third_old_cap := by linarith only [g11]
    third_new_nonneg := g10
    third_new_cap := by linarith only [g12]
    fresh_cap := by linarith only [g13]
    rounding_identity := exact_round }

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
