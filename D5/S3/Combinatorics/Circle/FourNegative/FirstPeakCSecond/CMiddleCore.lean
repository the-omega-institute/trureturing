/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/CMiddleCore
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: CMiddle integer gates, physical masks, packet inventory, masses and native seam identities. -/
/- SOURCE_ONLY_UNCOMPILED. Full FirstPeakCSecond consumed implementation.
Repository API pin: 1add3bcde3f5768e7c5b7c84867d9758df1e6e6b.
Caller construction and ordinary proof; no Pro or kernel validation.
Full unrestricted physical J / Circle C3.1 remain OPEN. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddlePolynomials
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.FinRange
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open MaxPlusTwo.Chambers
open scoped BigOperators
open private size seed sourceMod base newBase charge chainLength chainStart
  nextBase nextNewBase oldValue newValue negatives actual_values chain_values
  new_base_bounds source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private strip_append_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

/- Integer choices are made before any toNat conversion. -/
private def ceil (B Mn : ℤ) : ℤ := (B+Mn-1)/Mn

private theorem ceil_bounds (B M Mn D g : ℤ)
    (hB : 0<B) (hM : 0<M) (hMn : 0<Mn) (hD : 1≤D)
    (hrel : Mn=2*M-D) (hF : 0≤B*(Mn-M)-M*Mn)
    (hcap : B≤g*Mn) :
    let r := ceil B Mn
    1≤r ∧ r≤g ∧ B≤r*Mn ∧ r*Mn<B+Mn ∧ r*M<B ∧ r*Mn≤2*B-1 := by
  let r := ceil B Mn
  have h0 := Int.emod_nonneg (B+Mn-1) (ne_of_gt hMn)
  have h1 := Int.emod_lt_of_pos (B+Mn-1) hMn
  have he := Int.ediv_mul_add_emod (B+Mn-1) Mn
  change r*Mn+(B+Mn-1)%Mn=B+Mn-1 at he
  have hlow : B≤r*Mn := by omega
  have hhigh : r*Mn<B+Mn := by omega
  have hr : 1≤r := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (show r≤0 by omega) hMn.le
    omega
  have hrg : r≤g := by
    by_contra h
    have := mul_le_mul_of_nonneg_right (show g+1≤r by omega) hMn.le
    nlinarith
  have hrM : r*M<B := by
    have hi := mul_lt_mul_of_pos_right hhigh hM
    have hj : M*(B+Mn)≤B*Mn := by nlinarith only [hF]
    nlinarith only [hi,hj,hMn]
  have hrd := mul_le_mul_of_nonneg_left hD (show 0≤r by omega)
  refine ⟨hr,hrg,hlow,hhigh,hrM,?_⟩
  have hrM' : r*M≤B-1 := by omega
  calc
    r*Mn = r*(2*M-D) := by rw [hrel]
    _ ≤ 2*B-1 := by nlinarith only [hrM',hrd,hr]

private theorem floor_bounds (L B M r z : ℤ)
    (hB : 0<B) (hr : 0≤r) (hM : 0≤M) (hnum : 0≤L-r*M)
    (hwidth : 2*L<z*B) :
    let w := (L-r*M)/B
    0≤w ∧ 0≤L-r*M-w*B ∧ L-r*M-w*B≤B-1 ∧ 2*w<z := by
  let w := (L-r*M)/B
  have hw : 0≤w := Int.ediv_nonneg hnum hB.le
  have h0 := Int.emod_nonneg (L-r*M) (ne_of_gt hB)
  have h1 := Int.emod_lt_of_pos (L-r*M) hB
  have he := Int.ediv_mul_add_emod (L-r*M) B
  change w*B+(L-r*M)%B=L-r*M at he
  have hrM := mul_nonneg hr hM
  have hwz : 2*w<z := by
    by_contra hh
    have := mul_le_mul_of_nonneg_right (show z≤2*w by omega) hB.le
    nlinarith
  have hrem : 0≤(L-r*M)%B ∧ (L-r*M)%B≤B-1 := by omega
  have hremEq : L-r*M-w*B=(L-r*M)%B := by
    omega
  exact ⟨hw,by rw [hremEq]; exact hrem.1,
    by rw [hremEq]; exact hrem.2,hwz⟩

private def XGates (v : Row) (s r w : ℤ) : Prop :=
  (0≤v.t*v.A-2*s*v.M ∧ v.t*v.A-2*s*v.M≤v.A-1) ∧
  (0≤2*((v.t-1)*v.A-s*v.Mn) ∧ 2*((v.t-1)*v.A-s*v.Mn)≤v.A-1) ∧
  (0≤2*(v.B-r*v.M) ∧ 2*(v.B-r*v.M)≤v.B-1) ∧
  (0≤2*(v.Bn-r*v.Mn) ∧ 2*(v.Bn-r*v.Mn)≤v.Bn-1) ∧
  (0≤2*(v.L-r*v.M-w*v.B) ∧ 2*(v.L-r*v.M-w*v.B)≤v.L-1) ∧
  (0≤2*(v.Ln-r*v.Mn-w*v.Bn) ∧ 2*(v.Ln-r*v.Mn-w*v.Bn)≤v.Ln-1)

private theorem model_positive (y t e h : ℤ)
    (hy : 4≤y) (ht : 4≤t) (he : 2≤e) (hh : 2≤h) :
    let v := model y t e h
    1≤v.A ∧ 1≤v.B ∧ 1≤v.L ∧ 1≤v.M ∧ 1≤v.Mn ∧
      v.z+1≤v.D ∧ v.Mn-v.M=v.t*v.y*v.z ∧ 1≤v.Bn ∧ 1≤v.Ln := by
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have he0 : 0≤e := by omega
  have hh0 : 0≤h := by omega
  have hy1 : 1≤y := by omega
  have ht1 : 1≤t := by omega
  have hD1 : (1 : ℤ) ≤ y*(e*t)+y+1 := by
    have hz0 : (0 : ℤ) ≤ y*(e*t) := by positivity
    nlinarith
  have hterm : (0 : ℤ) ≤ t*y*(e*t) := by positivity
  dsimp [model]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hp : (0 : ℤ) ≤ e*h*t*(y*e*t+y+1) := by positivity
    nlinarith [hp]
  · have hp : (0 : ℤ) ≤ e*h*t*t*(y+1) := by positivity
    nlinarith [hp]
  · have hp : (0 : ℤ) ≤ e*h*t*(e*t)*t + (e*t)*t + e*t := by positivity
    nlinarith [hp]
  · have hp : (0 : ℤ) ≤ t*y*(e*t) + (y*(e*t)+y+1) := by positivity
    nlinarith [hp,hD1,hterm]
  · have hp : (0 : ℤ) ≤ y*(e*t)+y+1 + 2*(t*y*(e*t)) := by positivity
    nlinarith [hp,hD1,hterm]
  · have hp : (0 : ℤ) ≤ (y-1)*(e*t)+y := by positivity
    nlinarith [hp]
  · ring
  · have hp : (0 : ℤ) ≤ 2*(e*h*t*t*(y+1)+t) := by positivity
    nlinarith [hp]
  · have hp : (0 : ℤ) ≤ 2*(e*h*t*(e*t)*t+(e*t)*t)+e*t := by positivity
    nlinarith [hp]

/- The six later gates share the same integer rounding proof. The first four
polynomial margins are kept separate, including the actual pre-ear first seam. -/
set_option maxHeartbeats 2000000 in
private theorem x_floor_gates (y t e h s g : ℤ)
    (hy : 4≤y) (ht : 4≤t) (he : 2≤e) (hh : 2≤h)
    (hfirst : let v:=model y t e h
      (0≤v.t*v.A-2*s*v.M ∧ v.t*v.A-2*s*v.M≤v.A-1) ∧
      (0≤2*((v.t-1)*v.A-s*v.Mn) ∧ 2*((v.t-1)*v.A-s*v.Mn)≤v.A-1))
    (hF : let v:=model y t e h; 0≤v.B*v.t*v.y*v.z-v.M*v.Mn)
    (hg : let v:=model y t e h; 0≤g*v.Mn-v.B)
    (hL : let v:=model y t e h; 0≤v.L-2*v.B-g*v.D)
    (hz : let v:=model y t e h; 0≤v.z*v.B-2*v.L-1) :
    let v:=model y t e h
    let r:=ceil v.B v.Mn
    let w:=(v.L-r*v.M)/v.B
    1≤r ∧ r≤g ∧ r*v.M<v.B ∧ 0≤w ∧ 2*w<v.z ∧ XGates v s r w := by
  let v:=model y t e h
  let r:=ceil v.B v.Mn
  let w:=(v.L-r*v.M)/v.B
  obtain ⟨hA,hB,hLL,hM,hMn,hD,hrel,hBn,hLn⟩ := model_positive y t e h hy ht he hh
  have hDsmall : v.z+1≤v.D := by simpa [v] using hD
  have hB' : 1≤v.B := by simpa [v] using hB
  have hM' : 1≤v.M := by simpa [v] using hM
  have hMn' : 1≤v.Mn := by simpa [v] using hMn
  have hD' : 1≤v.D := by
    have hz : 0≤v.z := by
      dsimp [v,model]
      positivity
    omega
  have hvB : 0<v.B := by omega
  have hvM : 0<v.M := by omega
  have hvMn : 0<v.Mn := by omega
  have hvD : 1≤v.D := hD'
  have hc := ceil_bounds v.B v.M v.Mn v.D g hvB hvM hvMn hvD
    (by dsimp [v,model]) (by simpa only [hrel, mul_assoc] using hF) (by linarith only [hg])
  change 1≤r ∧ r≤g ∧ v.B≤r*v.Mn ∧ r*v.Mn<v.B+v.Mn ∧
    r*v.M<v.B ∧ r*v.Mn≤2*v.B-1 at hc
  have hg0 : 0≤g := by omega
  have hgd := mul_nonneg hg0 (show 0≤v.D by omega)
  have hnum : 0≤v.L-r*v.M := by
    have hgd' : 0≤g*v.D := hgd
    nlinarith [hc.2.2.2.2.1,hL]
  have hwidth : 2*v.L < v.z*v.B := by
    have hz' : 0≤v.z*v.B-2*v.L-1 := by simpa [v] using hz
    omega
  have hf := floor_bounds v.L v.B v.M r v.z (by omega) (by omega) (by omega)
    hnum hwidth
  change 0≤w ∧ 0≤v.L-r*v.M-w*v.B ∧ v.L-r*v.M-w*v.B≤v.B-1 ∧ 2*w<v.z at hf
  have hrD : 1≤r*v.D := by
    have := mul_le_mul_of_nonneg_left (show 1≤v.D by omega) (show 0≤r by omega)
    omega
  have hrDg := mul_le_mul_of_nonneg_right hc.2.1 (show 0≤v.D by omega)
  have hrDz : v.z+1≤r*v.D := by
    have := mul_le_mul_of_nonneg_right hc.1 (show 0≤v.D by omega)
    nlinarith [hDsmall]
  have hbrel : v.Bn=2*v.B-1 := by rfl
  have hlrel : v.Ln=2*v.L-v.z-1 := by rfl
  have hmrel : v.Mn=2*v.M-v.D := by rfl
  have hk1 : v.Bn-r*v.Mn=2*(v.B-r*v.M)+r*v.D-1 := by rw [hbrel,hmrel]; ring
  have hk2 : v.Ln-r*v.Mn-w*v.Bn=
      2*(v.L-r*v.M-w*v.B)+r*v.D+w-v.z-1 := by rw [hlrel,hmrel,hbrel]; ring
  refine ⟨hc.1,hc.2.1,hc.2.2.2.2.1,hf.1,hf.2.2.2,?_,?_,?_,?_,?_,?_⟩
  · exact hfirst.1
  · exact hfirst.2
  · constructor <;> nlinarith [hc.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2]
  · constructor <;> nlinarith [hc.2.2.1,hc.2.2.2.2.2]
  · constructor <;> nlinarith [hf.2.1,hf.2.2.1,hL]
  · constructor <;> nlinarith [hf.2.1,hf.2.2.1,hf.2.2.2,hL]

set_option maxHeartbeats 10000000 in
private theorem x_one_gates (t h s : ℤ) (ht : 4≤t) (hh : 4≤h)
    (hmargins : let v:=model t t 2 h
      0≤v.t*v.A-2*s*v.M ∧ 0≤v.A-1-(v.t*v.A-2*s*v.M) ∧
      0≤2*((v.t-1)*v.A-s*v.Mn) ∧ 0≤v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
      0≤v.B*v.t*v.y*v.z-v.M*v.Mn ∧ 0≤h*v.Mn-v.B ∧
      0≤(v.L-v.B-v.M)*v.Mn-v.B*v.M ∧ 0≤2*v.B-v.L-1) :
    let v:=model t t 2 h
    let r:=ceil v.B v.Mn
    1≤r ∧ r≤h ∧ r*v.M<v.B ∧ 2<v.z ∧ XGates v s r 1 := by
  let v:=model t t 2 h
  let r:=ceil v.B v.Mn
  obtain ⟨hA,hB,hL,hM,hMn,hD,hrel,hBn,hLn⟩ := model_positive t t 2 h ht ht (by omega) (by omega)
  rcases hmargins with ⟨f0,f1,f2,f3,F,G,P,W⟩
  have hDsmall : v.z+1≤v.D := by simpa [v] using hD
  have hB' : 1≤v.B := by simpa [v] using hB
  have hM' : 1≤v.M := by simpa [v] using hM
  have hMn' : 1≤v.Mn := by simpa [v] using hMn
  have hD' : 1≤v.D := by
    have hz : 0≤v.z := by
      dsimp [v,model]
      positivity
    omega
  have hvB : 0<v.B := by omega
  have hvM : 0<v.M := by omega
  have hvMn : 0<v.Mn := by omega
  have hvD : 1≤v.D := hD'
  have hc := ceil_bounds v.B v.M v.Mn v.D h hvB hvM hvMn
    (by
      have hz : 4≤v.z := by dsimp [v,model]; omega
      omega)
    (by rfl) (by simpa only [hrel, mul_assoc] using F) (by linarith)
  change 1≤r ∧ r≤h ∧ v.B≤r*v.Mn ∧ r*v.Mn<v.B+v.Mn ∧
    r*v.M<v.B ∧ r*v.Mn≤2*v.B-1 at hc
  have hrD : v.z+1≤r*v.D := by
    have := mul_le_mul_of_nonneg_right hc.1 (show 0≤v.D by omega)
    nlinarith [hDsmall]
  have hs2 : 0≤v.L-v.B-r*v.M := by
    have hi := mul_lt_mul_of_pos_right hc.2.2.2.1 (show 0<v.M by omega)
    have hj : v.B*v.M+v.Mn*v.M≤(v.L-v.B)*v.Mn := by nlinarith only [P]
    nlinarith only [hi,hj,hMn]
  have hb : v.Bn=2*v.B-1 := rfl
  have hl : v.Ln=2*v.L-v.z-1 := rfl
  have hm : v.Mn=2*v.M-v.D := rfl
  have k1 : v.Bn-r*v.Mn=2*(v.B-r*v.M)+r*v.D-1 := by rw [hb,hm]; ring
  have k2 : v.Ln-r*v.Mn-v.Bn=2*(v.L-r*v.M-v.B)+r*v.D-v.z := by rw [hl,hm,hb]; ring
  have hrm : 0≤r*v.Mn := mul_nonneg (by omega) (by omega)
  have hrm' : 0≤r*v.M := mul_nonneg (by omega) (by omega)
  refine ⟨hc.1,hc.2.1,hc.2.2.2.2.1,by dsimp [v,model]; omega,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨f0,by omega⟩
  · exact ⟨f2,by omega⟩
  · constructor <;> nlinarith [hc.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2]
  · constructor <;> nlinarith [hc.2.2.1,hc.2.2.2.2.2]
  · constructor <;> nlinarith [hs2,W]
  · constructor <;> nlinarith [hs2,W]

/- The dynamic first bank retains its actual ceil-dependent s=5h+r. -/
set_option maxHeartbeats 10000000 in
private theorem dynamic_first (h : ℤ) (hh : 8≤h)
    (hmargins : let v:=model 4 4 4 h
      0≤2*(2*v.A-5*h*v.M-v.B) ∧
      0≤(10*h*v.M-3*v.A-1)*v.Mn+2*v.B*v.M ∧
      0≤2*(3*v.A-5*h*v.Mn-v.B-v.Mn) ∧
      0≤10*h*v.Mn+2*v.B-5*v.A-1 ∧
      0≤v.B*v.t*v.y*v.z-v.M*v.Mn ∧ 0≤h*v.Mn-v.B) :
    let v:=model 4 4 4 h
    let r:=ceil v.B v.Mn
    (0≤v.t*v.A-2*(5*h+r)*v.M ∧ v.t*v.A-2*(5*h+r)*v.M≤v.A-1) ∧
    (0≤2*((v.t-1)*v.A-(5*h+r)*v.Mn) ∧
      2*((v.t-1)*v.A-(5*h+r)*v.Mn)≤v.A-1) := by
  let v:=model 4 4 4 h
  let r:=ceil v.B v.Mn
  rcases hmargins with ⟨f0,f1,f2,f3,F,G⟩
  obtain ⟨hA,hB,hL,hM,hMn,hD,hrel,hBn,hLn⟩ := model_positive 4 4 4 h (by norm_num) (by norm_num) (by norm_num) (by omega)
  have hDsmall : v.z+1≤v.D := by simpa [v] using hD
  have hB' : 1≤v.B := by simpa [v] using hB
  have hM' : 1≤v.M := by simpa [v] using hM
  have hMn' : 1≤v.Mn := by simpa [v] using hMn
  have hD' : 1≤v.D := by
    have hz : 0≤v.z := by
      dsimp [v,model]
      positivity
    omega
  have hvB : 0<v.B := by omega
  have hvM : 0<v.M := by omega
  have hvMn : 0<v.Mn := by omega
  have hvD : 1≤v.D := hD'
  have hc := ceil_bounds v.B v.M v.Mn v.D h hvB hvM hvMn
    (by norm_num [v,model]) (by rfl) (by simpa only [hrel, mul_assoc] using F) (by linarith)
  change 1≤r ∧ r≤h ∧ v.B≤r*v.Mn ∧ r*v.Mn<v.B+v.Mn ∧
    r*v.M<v.B ∧ r*v.Mn≤2*v.B-1 at hc
  have hrLo := mul_le_mul_of_nonneg_right hc.2.2.1 (show 0≤v.M by omega)
  have hrHi := mul_lt_mul_of_pos_right hc.2.2.2.1 (show 0<v.M by omega)
  have ht : v.t=4 := rfl
  change (0≤v.t*v.A-2*(5*h+r)*v.M ∧ v.t*v.A-2*(5*h+r)*v.M≤v.A-1) ∧
    (0≤2*((v.t-1)*v.A-(5*h+r)*v.Mn) ∧
      2*((v.t-1)*v.A-(5*h+r)*v.Mn)≤v.A-1)
  rw [ht]
  constructor
  · constructor
    · nlinarith [hc.2.2.2.2.1]
    · have heq : (v.A-1-(4*v.A-2*(5*h+r)*v.M))*v.Mn =
          (10*h*v.M-3*v.A-1)*v.Mn+2*r*v.Mn*v.M := by ring
      nlinarith only [heq,hrLo,f1,hMn]
  · constructor <;> nlinarith [hc.2.2.1,hc.2.2.2.1]


/- The required pinned tree has no UpperGap.Rounding module. This one consumed
bit lemma is ported from that module at immutable prior pin
51bcfb627895955906cf7299b5bc67b74189dfc5; its proof body is retained here. -/
private theorem multiple_predecessor_bits (k q : ℕ) (hq : 1 ≤ q)
    (i : ℕ) (hi : i < k) : (2^k*q-1).testBit i = true := by
  have hp : 0 < (2:ℕ)^k := by positivity
  have he : 2^k*q-1 = 2^k*(q-1)+(2^k-1) := by
    have hq' : q-1+1=q := by omega
    have hm : 2^k*q=2^k*(q-1)+2^k := by
      calc
        _ = 2^k*((q-1)+1) := by rw [hq']
        _ = _ := by ring
    rw [hm]
    omega
  have hm : (2^k*q-1) % 2^k = 2^k-1 := by
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 2^k-1 < 2^k)]
  have ht := Nat.testBit_mod_two_pow (2^k*q-1) k i
  rw [hm] at ht
  simpa [Nat.testBit_two_pow_sub_one,hi] using ht.symm


private theorem bit_below (q k i : ℕ) (hq : q<2^k) (hi : q.testBit i=true) : i<k := by
  by_contra hn
  have hp : 2^k≤(2:ℕ)^i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq hp)
  simp [hf] at hi

private theorem predecessor_submask (k u q : ℕ) (hu : 1≤u) (hq : q<2^k) :
    ∀ i, q.testBit i=true → (2^k*u-1).testBit i=true := by
  intro i hi
  exact multiple_predecessor_bits k u hu i (bit_below q k i hq hi)

private theorem dynamic_submask (k q : ℕ) (hq : q<2^k) :
    ∀ i, q.testBit i=true → (5*2^k+q).testBit i=true := by
  intro i hi
  have hik := bit_below q k i hq hi
  have hm : (5*2^k+q) % 2^k=q := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hq]
  have ht := Nat.testBit_mod_two_pow (5*2^k+q) k i
  rw [hm] at ht
  simpa [hik,hi] using ht.symm

private theorem odd_submask (R : ℕ) (hR : R%2=1) :
    ∀ i, (1:ℕ).testBit i=true → R.testBit i=true := by
  intro i hi
  have hi0 : i=0 := by
    have he := bit_below 1 1 i (by norm_num) hi
    omega
  subst i
  simp [Nat.testBit_eq_decide_div_mod_eq,hR]

private def mask (a b c d : ℕ) (r : Fin 4) (m : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) m
private def full (a b c d : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c d r-1)-1
private def terminal (a b c d : ℕ) (r : Fin 4) : ℕ :=
  chainStart b c d r+chainLength a b c d r-1

private theorem full_split (a b c d : ℕ) (r : Fin 4) (m : ℕ) :
    (mask a b c d r (full a b c d r ^^^ m) ++ mask a b c d r m).Perm
      (mask a b c d r (full a b c d r)) := by
  apply chamberLabels_split
  intro i hi _
  simp [full,Nat.testBit_two_pow_sub_one,hi]

private theorem sub_split (a b c d : ℕ) (r : Fin 4) (m q : ℕ)
    (hsub : ∀ i, q.testBit i=true → m.testBit i=true) :
    (mask a b c d r (m ^^^ q) ++ mask a b c d r q).Perm (mask a b c d r m) := by
  exact chamberLabels_split _ _ _ _ (fun i _ hi => hsub i hi)

private theorem chain_inventory (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    (mask a b c d 0 (full a b c d 0) ++ [terminal a b c d 0] ++
     mask a b c d 1 (full a b c d 1) ++ [terminal a b c d 1] ++
     mask a b c d 2 (full a b c d 2) ++ [terminal a b c d 2] ++
     mask a b c d 3 (full a b c d 3) ++ [terminal a b c d 3]) =
      List.range (size a b c d) := by
  have merge (off len : ℕ) (hlen : 1≤len) :
      chamberLabels (len-1) off (2^(len-1)-1) ++ [off+len-1] = List.range' off len := by
    rw [chamberLabels_full]
    simpa [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega] using
      (List.range'_1_concat (s:=off) (n:=len-1)).symm
  suffices h :
      ((chamberLabels (d-1) 0 (2^(d-1)-1) ++ [d-1]) ++
      (chamberLabels (c-1) d (2^(c-1)-1) ++ [d+c-1])) ++
      (chamberLabels (b-1) (d+c) (2^(b-1)-1) ++ [d+c+b-1]) ++
      (chamberLabels (a-1) (d+c+b) (2^(a-1)-1) ++ [d+c+b+a-1]) =
      List.range (size a b c d) by
    simpa [mask,full,terminal,chainLength,chainStart,size,List.append_assoc] using h
  have hu : chamberLabels (d-1) 0 (2^(d-1)-1) ++ [d-1] = List.range' 0 d := by
    simpa only [Nat.zero_add] using merge 0 d (by omega)
  rw [hu,merge d c (by omega),merge (d+c) b (by omega),merge (d+c+b) a (by omega)]
  have h1 := List.range'_append_1 (s:=0) (m:=d) (n:=c)
  have h2 := List.range'_append_1 (s:=0) (m:=d+c) (n:=b)
  have h3 := List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a)
  simp only [Nat.zero_add] at h1 h2 h3
  rw [h1,h2,h3,←List.range_eq_range']
  congr 1
  dsimp [size]
  omega

private def xPackets (a b c d m q w : ℕ) : List (List ℕ × ℕ) :=
  let U := mask a b c d 0
  let V := mask a b c d 1
  let W := mask a b c d 2
  let X := mask a b c d 3
  [(X (full a b c d 3 ^^^ m) ++ U (full a b c d 0),terminal a b c d 3),
   (X (m-q),terminal a b c d 0),
   (V (full a b c d 1 ^^^ w),terminal a b c d 1),
   (W (full a b c d 2) ++ X q ++ V w,terminal a b c d 2)]

private def vPackets (a b c d q R : ℕ) : List (List ℕ × ℕ) :=
  let U := mask a b c d 0
  let V := mask a b c d 1
  let W := mask a b c d 2
  let X := mask a b c d 3
  [(V (full a b c d 1 ^^^ q),terminal a b c d 1),
   (U (full a b c d 0) ++ V q ++ X 1,terminal a b c d 0),
   (X (full a b c d 3 ^^^ R),terminal a b c d 3),
   (W (full a b c d 2) ++ X (R-1),terminal a b c d 2)]

/- Prefix the fresh physical label to the bank following the chosen terminal.
Unlike packet normalisation, this deliberately keeps the literal cut unchanged. -/
private def freshAfter (k : ℕ) : ℕ → List (List ℕ × ℕ) → List (List ℕ × ℕ)
  | _, [] => []
  | 0, (P,n)::bs => (k::P,n)::bs
  | i+1, b::bs => b::freshAfter k i bs

private theorem mask_numeric_split (len m q : ℕ)
    (hm : m<2^len) (hq : q<2^len)
    (hsub : ∀ i, q.testBit i=true → m.testBit i=true) : m ^^^ q=m-q := by
  have hxor : m ^^^ q<2^len := Nat.xor_lt_two_pow hm hq
  let f : ℕ→ℤ:=fun i => (2:ℤ)^i
  have so:=chamberLabels_sum len 0 m hm f 1 (by intro i hi; simp [f])
  have si:=chamberLabels_sum len 0 q hq f 1 (by intro i hi; simp [f])
  have sx:=chamberLabels_sum len 0 (m ^^^ q) hxor f 1 (by intro i hi; simp [f])
  have hp:=((chamberLabels_split len 0 m q (fun i _ hi => hsub i hi)).map f).sum_eq
  simp only [List.map_append,List.sum_append,so,si,sx,mul_one] at hp
  have hn : (m ^^^ q)+q=m := by exact_mod_cast hp
  omega

private theorem x_inventory (a b c d m q w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hm : m<2^(a-1)) (hq : q<2^(a-1))
    (hsub : ∀ i, q.testBit i=true → m.testBit i=true) :
    (blocksWord (xPackets a b c d m q w)).Perm (List.range (size a b c d)) := by
  let U:=mask a b c d 0
  let V:=mask a b c d 1
  let W:=mask a b c d 2
  let X:=mask a b c d 3
  have hnum:=mask_numeric_split (a-1) m q hm hq hsub
  have hX:=full_split a b c d 3 m
  have hQ:=sub_split a b c d 3 m q hsub
  have hV:=full_split a b c d 1 w
  have hx:=Multiset.coe_eq_coe.mpr
    ((hQ.append_left (X (full a b c d 3 ^^^ m))).trans hX)
  have hv:=Multiset.coe_eq_coe.mpr hV
  apply Multiset.coe_eq_coe.mp
  calc
    _ = (↑(X (full a b c d 3 ^^^ m) ++ X (m ^^^ q) ++ X q) : Multiset ℕ) +
      ↑(V (full a b c d 1 ^^^ w) ++ V w) + ↑(U (full a b c d 0)) +
      ↑(W (full a b c d 2)) + {terminal a b c d 0} + {terminal a b c d 1} +
      {terminal a b c d 2} + {terminal a b c d 3} := by
        simp [xPackets,←hnum,blocksWord,←Multiset.coe_add,←Multiset.cons_coe,
          ←Multiset.singleton_add,List.append_assoc] <;> ac_rfl
    _ = ↑(X (full a b c d 3)) + ↑(V (full a b c d 1)) + ↑(U (full a b c d 0)) +
      ↑(W (full a b c d 2)) + {terminal a b c d 0} + {terminal a b c d 1} +
      {terminal a b c d 2} + {terminal a b c d 3} := by
        have hx' : (↑(X (full a b c d 3 ^^^ m) ++ X (m ^^^ q) ++ X q) : Multiset ℕ)=↑(X (full a b c d 3)) := by
          simpa only [List.append_assoc] using hx
        rw [hx',hv]
    _ = ↑(mask a b c d 0 (full a b c d 0) ++ [terminal a b c d 0] ++
      mask a b c d 1 (full a b c d 1) ++ [terminal a b c d 1] ++
      mask a b c d 2 (full a b c d 2) ++ [terminal a b c d 2] ++
      mask a b c d 3 (full a b c d 3) ++ [terminal a b c d 3]) := by
        simp only [←Multiset.coe_add,Multiset.coe_singleton]; ac_rfl
    _ = _ := by rw [chain_inventory a b c d ha hb hc hd]

private theorem v_inventory (a b c d q R : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (hR : R%2=1)
    (hRc : R<2^(a-1)) (h1c : 1<2^(a-1)) :
    (blocksWord (vPackets a b c d q R)).Perm (List.range (size a b c d)) := by
  let U:=mask a b c d 0
  let V:=mask a b c d 1
  let W:=mask a b c d 2
  let X:=mask a b c d 3
  have hnum:=mask_numeric_split (a-1) R 1 hRc h1c (odd_submask R hR)
  have hX:=full_split a b c d 3 R
  have hQ:=sub_split a b c d 3 R 1 (odd_submask R hR)
  have hV:=full_split a b c d 1 q
  have hx:=Multiset.coe_eq_coe.mpr
    ((hQ.append_left (X (full a b c d 3 ^^^ R))).trans hX)
  have hv:=Multiset.coe_eq_coe.mpr hV
  apply Multiset.coe_eq_coe.mp
  calc
    _ = (↑(X (full a b c d 3 ^^^ R) ++ X (R ^^^ 1) ++ X 1) : Multiset ℕ) +
      ↑(V (full a b c d 1 ^^^ q) ++ V q) + ↑(U (full a b c d 0)) +
      ↑(W (full a b c d 2)) + {terminal a b c d 0} + {terminal a b c d 1} +
      {terminal a b c d 2} + {terminal a b c d 3} := by
        simp [vPackets,←hnum,blocksWord,←Multiset.coe_add,←Multiset.cons_coe,
          ←Multiset.singleton_add,List.append_assoc] <;> ac_rfl
    _ = ↑(X (full a b c d 3)) + ↑(V (full a b c d 1)) + ↑(U (full a b c d 0)) +
      ↑(W (full a b c d 2)) + {terminal a b c d 0} + {terminal a b c d 1} +
      {terminal a b c d 2} + {terminal a b c d 3} := by
        have hx' : (↑(X (full a b c d 3 ^^^ R) ++ X (R ^^^ 1) ++ X 1) : Multiset ℕ)=↑(X (full a b c d 3)) := by
          simpa only [List.append_assoc] using hx
        rw [hx',hv]
    _ = ↑(mask a b c d 0 (full a b c d 0) ++ [terminal a b c d 0] ++
      mask a b c d 1 (full a b c d 1) ++ [terminal a b c d 1] ++
      mask a b c d 2 (full a b c d 2) ++ [terminal a b c d 2] ++
      mask a b c d 3 (full a b c d 3) ++ [terminal a b c d 3]) := by
        simp only [←Multiset.coe_add,Multiset.coe_singleton]; ac_rfl
    _ = _ := by rw [chain_inventory a b c d ha hb hc hd]

private theorem mask_mass (a b c d m : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hm : m<2^(chainLength a b c d r-1)) :
    ((mask a b c d r m).map (oldValue a b c d)).sum = (m:ℤ)*base a b c d r ∧
    ((mask a b c d r m).map (newValue a b c d)).sum = (m:ℤ)*newBase a b c d r := by
  have h:=chain_values a b c d ha hb hc hd
  constructor
  · apply chamberLabels_sum _ _ m hm
    intro i hi
    rw [h.2.1 r i (by omega),if_pos (by omega)]
  · apply chamberLabels_sum _ _ m hm
    intro i hi
    rw [h.2.2.1 r i (by omega),if_pos (by omega)]

private theorem mask_positive (a b c d m : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    ∀ i ∈ mask a b c d r m, 0≤oldValue a b c d i ∧ 0≤newValue a b c d i := by
  have h:=chain_values a b c d ha hb hc hd
  have hn:=new_base_bounds a b c d ha hb hc hd r
  intro i hi
  obtain ⟨j,hj,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
  rw [h.2.1 r j (by omega),h.2.2.1 r j (by omega)]
  have hcond : j+1 < chainLength a b c d r := by omega
  simp [hcond]
  exact ⟨mul_nonneg (by positivity) (by have := (h.1 r).1; omega),
    mul_nonneg (by positivity) (by have := hn.1; omega)⟩

private theorem complement_mass (a b c d m : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hm : m<2^(chainLength a b c d r-1)) :
    ((mask a b c d r (full a b c d r ^^^ m)).map (oldValue a b c d)).sum =
      ((full a b c d r:ℕ):ℤ)*base a b c d r-(m:ℤ)*base a b c d r ∧
    ((mask a b c d r (full a b c d r ^^^ m)).map (newValue a b c d)).sum =
      ((full a b c d r:ℕ):ℤ)*newBase a b c d r-(m:ℤ)*newBase a b c d r := by
  have hp:=full_split a b c d r m
  have hfull : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have hf:=mask_mass a b c d (full a b c d r) r ha hb hc hd hfull
  have hm':=mask_mass a b c d m r ha hb hc hd hm
  have ho:=(hp.map (oldValue a b c d)).sum_eq
  have hn:=(hp.map (newValue a b c d)).sum_eq
  simp only [List.map_append,List.sum_append] at ho hn
  exact ⟨by linarith only [ho,hf.1,hm'.1],by linarith only [hn,hf.2,hm'.2]⟩

private theorem split_mass (a b c d m q : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hm : m<2^(chainLength a b c d r-1))
    (hq : q<2^(chainLength a b c d r-1))
    (hsub : ∀ i, q.testBit i=true → m.testBit i=true) :
    ((mask a b c d r (m-q)).map (oldValue a b c d)).sum =
      ((m:ℤ)-(q:ℤ))*base a b c d r ∧
    ((mask a b c d r (m-q)).map (newValue a b c d)).sum =
      ((m:ℤ)-(q:ℤ))*newBase a b c d r := by
  have hnum:=mask_numeric_split (chainLength a b c d r-1) m q hm hq hsub
  have hp:=sub_split a b c d r m q hsub
  have hf:=mask_mass a b c d m r ha hb hc hd hm
  have hq':=mask_mass a b c d q r ha hb hc hd hq
  have ho:=(hp.map (oldValue a b c d)).sum_eq
  have hn:=(hp.map (newValue a b c d)).sum_eq
  simp only [List.map_append,List.sum_append,hnum] at ho hn
  constructor <;> nlinarith [ho,hn,hf.1,hf.2,hq'.1,hq'.2]

private theorem power_split (a c : ℕ) (hac : c≤a) :
    (2:ℤ)^a=2^(a-c)*2^c := by
  rw [←pow_add,Nat.sub_add_cancel hac]

private def actualRow (a b c d : ℕ) : Row :=
  model (2^b) (2^d) (2^(c-d)) (2^(a-c))

private theorem row_source (a b c d : ℕ) (hac : c≤a) (hcd : d≤c) :
    let v:=actualRow a b c d
    v.x=2^a ∧ v.y=2^b ∧ v.z=2^c ∧ v.t=2^d ∧
    v.A=base a b c d 0 ∧ v.B=base a b c d 1 ∧
    v.L=base a b c d 2 ∧ v.M=base a b c d 3 ∧
    v.Bn=newBase a b c d 1 ∧ v.Ln=newBase a b c d 2 ∧
    v.Mn=newBase a b c d 3 ∧ newBase a b c d 0=2*v.A := by
  have he:=power_split c d hcd
  have hh:=power_split a c hac
  have hx : (2:ℤ)^(c-d)*2^(a-c)*2^d=2^a := by rw [hh,he]; ring
  dsimp [actualRow,model,base,newBase,charge]
  simp only [hx,←he]
  repeat' constructor <;> try trivial <;> ring

private theorem power_pred (j : ℕ) (hj : 1≤j) :
    (2:ℤ)^j=2*2^(j-1) := by
  calc
    (2 : ℤ)^j = (2 : ℤ)^(j - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
    _ = (2 : ℤ)^(j - 1) * 2 := by rw [pow_succ]
    _ = 2 * (2 : ℤ)^(j - 1) := by ring

private theorem terminal_double (a b c d : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    2*oldValue a b c d (terminal a b c d r)=nextBase a b c d r-sourceMod a b c d ∧
    2*newValue a b c d (terminal a b c d r)=
      nextNewBase a b c d r-(2*sourceMod a b c d+1) := by
  have h:=chain_values a b c d ha hb hc hd
  have hl : 1≤chainLength a b c d r := by fin_cases r <;> simp [chainLength] <;> omega
  have ho:=h.2.1 r (chainLength a b c d r-1) (by omega)
  have hn:=h.2.2.1 r (chainLength a b c d r-1) (by omega)
  have hidx : chainStart b c d r+(chainLength a b c d r-1)=terminal a b c d r := by
    dsimp [terminal]; omega
  rw [hidx,if_neg (by omega)] at ho hn
  have hrec : (2:ℤ)^(chainLength a b c d r)*base a b c d r=
      sourceMod a b c d+nextBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,sourceMod,nextBase] <;> ring
  have hrecn : (2:ℤ)^(chainLength a b c d r)*newBase a b c d r=
      2*sourceMod a b c d+1+nextNewBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,newBase,charge,sourceMod,nextNewBase] <;> ring
  rw [power_pred _ hl] at hrec hrecn
  have heo : sourceMod a b c d-nextBase a b c d r=
      2*(2^(chainLength a b c d r-1)*base a b c d r-nextBase a b c d r) := by
    nlinarith only [hrec]
  have hen : 2*sourceMod a b c d+1-nextNewBase a b c d r=
      2*(2^(chainLength a b c d r-1)*newBase a b c d r-nextNewBase a b c d r) := by
    nlinarith only [hrecn]
  rw [ho,hn,heo,hen]
  omega

private theorem source_odd (a b c d : ℕ) (hd : 1≤d) : sourceMod a b c d%2=1 := by
  have ht:=power_pred d hd
  have h : sourceMod a b c d =
      2*((2:ℤ)^a*2^b*2^c*2^(d-1)-1)+1 := by dsimp [sourceMod]; rw [ht]; ring
  rw [h]
  omega

/- Four doubled seam/peak pairs imply the recursive packet checks. This lemma
uses the exact zero total, including the final terminal, instead of discarding it. -/
private theorem four_checks (f : ℕ→ℤ) (C : ℤ)
    (P0 P1 P2 P3 : List ℕ) (n0 n1 n2 n3 : ℕ)
    (S0 S1 S2 J0 J1 J2 J3 : ℤ)
    (h0 : 2*((P0.map f).sum+f n0)=S0)
    (h1 : 2*((P0.map f).sum+f n0+(P1.map f).sum+f n1)=S1)
    (h2 : 2*((P0.map f).sum+f n0+(P1.map f).sum+f n1+(P2.map f).sum+f n2)=S2)
    (hz : ((blocksWord [(P0,n0),(P1,n1),(P2,n2),(P3,n3)]).map f).sum=0)
    (hn0 : 2*f n0=J0-(2*C+1)) (hn1 : 2*f n1=J1-(2*C+1))
    (hn2 : 2*f n2=J2-(2*C+1)) (hn3 : 2*f n3=J3-(2*C+1))
    (hg0 : 0≤S0 ∧ S0≤J0-1) (hg1 : 0≤S1 ∧ S1≤J1-1)
    (hg2 : 0≤S2 ∧ S2≤J2-1) (hg3 : 1≤J3) :
    packetChecks f C 0 [(P0,n0),(P1,n1),(P2,n2),(P3,n3)] := by
  simp only [blocksWord,List.map_append,List.sum_append,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hz
  simp only [packetChecks,zero_add]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,True.intro⟩

private theorem terminal_nonpositive (a b c d : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    oldValue a b c d (terminal a b c d r)≤0 ∧
    newValue a b c d (terminal a b c d r)≤0 := by
  have hv:=chain_values a b c d ha hb hc hd
  have hn:=new_base_bounds a b c d ha hb hc hd
  have ht:=terminal_double a b c d r ha hb hc hd
  have hb0 : nextBase a b c d r<sourceMod a b c d := by
    fin_cases r <;> simpa [nextBase] using (hv.1 _).2
  have hb1 : nextNewBase a b c d r<2*sourceMod a b c d+1 := by
    fin_cases r
    · simpa [nextNewBase] using (hn 1).2
    · simpa [nextNewBase] using (hn 2).2
    · simpa [nextNewBase] using (hn 3).2
    · have hh := hv.1 0
      have hN : 0 < sourceMod a b c d := lt_of_lt_of_le (by omega) hh.2.le
      change base a b c d 0 < 2 * sourceMod a b c d + 1
      omega
  exact ⟨by omega,by omega⟩

private theorem packet_positive (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (m q w R : ℕ) :
    (∀ P∈xPackets a b c d m q w, ∀ i∈P.1,
      0≤oldValue a b c d i ∧ 0≤newValue a b c d i) ∧
    (∀ P∈vPackets a b c d q R, ∀ i∈P.1,
      0≤oldValue a b c d i ∧ 0≤newValue a b c d i) := by
  constructor
  · intro P hP i hi
    simp only [xPackets,List.mem_cons,List.mem_singleton] at hP
    rcases hP with rfl|rfl|rfl|hP
    · simp only [List.mem_append] at hi
      rcases hi with hi|hi
      · exact mask_positive a b c d (full a b c d 3 ^^^ m) 3 ha hb hc hd i hi
      · exact mask_positive a b c d (full a b c d 0) 0 ha hb hc hd i hi
    · exact mask_positive a b c d (m-q) 3 ha hb hc hd i hi
    · exact mask_positive a b c d (full a b c d 1 ^^^ w) 1 ha hb hc hd i hi
    · rcases hP with hP|hP
      · subst P
        simp only [List.mem_append] at hi
        rcases hi with hi|hi
        · rcases hi with hi|hi
          · exact mask_positive a b c d (full a b c d 2) 2 ha hb hc hd i hi
          · exact mask_positive a b c d q 3 ha hb hc hd i hi
        · exact mask_positive a b c d w 1 ha hb hc hd i hi
      · simp at hP
  · intro P hP i hi
    simp only [vPackets,List.mem_cons,List.mem_singleton] at hP
    rcases hP with rfl|rfl|rfl|hP
    · exact mask_positive a b c d (full a b c d 1 ^^^ q) 1 ha hb hc hd i hi
    · simp only [List.mem_append] at hi
      rcases hi with hi|hi
      · rcases hi with hi|hi
        · exact mask_positive a b c d (full a b c d 0) 0 ha hb hc hd i hi
        · exact mask_positive a b c d q 1 ha hb hc hd i hi
      · exact mask_positive a b c d 1 3 ha hb hc hd i hi
    · exact mask_positive a b c d (full a b c d 3 ^^^ R) 3 ha hb hc hd i hi
    · rcases hP with hP|hP
      · subst P
        simp only [List.mem_append] at hi
        rcases hi with hi|hi
        · exact mask_positive a b c d (full a b c d 2) 2 ha hb hc hd i hi
        · exact mask_positive a b c d (R-1) 3 ha hb hc hd i hi
      · simp at hP

private theorem fresh_positive (a b c d : ℕ) (e : ℕ) (bs : List (List ℕ×ℕ))
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hp : ∀ P∈bs, ∀ i∈P.1, 0≤newValue a b c d i) :
    ∀ P∈freshAfter (size a b c d) e bs, ∀ i∈P.1, 0≤newValue a b c d i := by
  have h:=chain_values a b c d ha hb hc hd
  have he : 0≤newValue a b c d (size a b c d) := by rw [h.2.2.2]; have := (h.1 0).1; omega
  induction bs generalizing e with
  | nil => simp [freshAfter]
  | cons b bs ih =>
    cases e <;> simp only [freshAfter,List.mem_cons] <;>
      aesop

private theorem fresh_word (k e : ℕ) (bs : List (List ℕ×ℕ)) (he : e<bs.length) :
    blocksWord (freshAfter k e bs)=
      insertAt k (blocksWord bs) (blocksWord (bs.take e)).length := by
  induction bs generalizing e with
  | nil => simp [freshAfter,blocksWord,insertAt] at *
  | cons b bs ih =>
    rcases b with ⟨P,n⟩
    cases e with
    | zero => simp [freshAfter,blocksWord,insertAt]
    | succ e =>
      have hh : e<bs.length := by simpa using he
      rw [freshAfter,blocksWord,ih e hh]
      simp only [List.take_succ_cons,blocksWord,List.length_append,List.length_cons]
      unfold insertAt
      rw [List.take_length_add_append,List.drop_length_add_append]
      simp [List.append_assoc]

private theorem fresh_total (a b c d : ℕ) (l : List ℕ) (j : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hp : l.Perm (List.range (size a b c d))) :
    ((insertAt (size a b c d) l j).map (newValue a b c d)).sum=0 := by
  have h:=source_totals a b c d ha hb hc hd
  have hm := (hp.map (newValue a b c d)).sum_eq
  have ht : ((l.take j).map (newValue a b c d)).sum+
      ((l.drop j).map (newValue a b c d)).sum=(l.map (newValue a b c d)).sum := by
    rw [←List.sum_append,←List.map_append,List.take_append_drop]
  simp only [insertAt,List.map_append,List.sum_append,List.map_cons]
  simp only [List.sum_cons,List.sum_nil,zero_add,add_zero]
  rw [h.2.2]
  linarith [h.2.1]

private theorem full_double (a b c d : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    2*((full a b c d r:ℕ):ℤ)+2=(2:ℤ)^(chainLength a b c d r) := by
  have hl : 1≤chainLength a b c d r := by fin_cases r <;> simp [chainLength] <;> omega
  dsimp [full]
  rw [Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
    power_pred _ hl]
  ring

private theorem native_balance (a b c d : ℕ) (r : Fin 4)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    ((full a b c d r:ℕ):ℤ)*base a b c d r+oldValue a b c d (terminal a b c d r)=
      nextBase a b c d r-base a b c d r ∧
    ((full a b c d r:ℕ):ℤ)*newBase a b c d r+newValue a b c d (terminal a b c d r)=
      nextNewBase a b c d r-newBase a b c d r := by
  have fd:=full_double a b c d r ha hb hc hd
  have td:=terminal_double a b c d r ha hb hc hd
  have hrec : (2:ℤ)^(chainLength a b c d r)*base a b c d r=
      sourceMod a b c d+nextBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,nextBase,sourceMod] <;> ring
  have hrecn : (2:ℤ)^(chainLength a b c d r)*newBase a b c d r=
      2*sourceMod a b c d+1+nextNewBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,newBase,charge,nextNewBase,sourceMod] <;> ring
  have fo:=congrArg (fun z : ℤ => z*base a b c d r) fd
  have fn:=congrArg (fun z : ℤ => z*newBase a b c d r) fd
  exact ⟨by nlinarith only [fo,hrec,td.1],by nlinarith only [fn,hrecn,td.2]⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
