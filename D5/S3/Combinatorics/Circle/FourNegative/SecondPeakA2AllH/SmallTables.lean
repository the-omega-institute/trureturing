/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallTables
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Twenty affine families and twenty finite boundary rows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH.SmallWindows

/-! Twenty affine families and twenty finite boundary rows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakHighD

structure AffineSmallRow where
  p : ℕ
  q : ℕ
  block : ℕ
  v : ℕ
  j : ℕ
  before : Bool
  atOne : Fin 4 → ℤ
  slope : Fin 4 → ℤ

def affineSmallRows : Fin 20 → AffineSmallRow :=
  ![⟨4,2,8,7,6,true,![2224,16212,13558,4878],![2156,16276,13420,5012]⟩,
    ⟨4,4,21,15,5,true,![8510,61126,51668,17968],![8362,61270,51370,18262]⟩,
    ⟨4,8,46,31,4,true,![12860,257480,160626,109714],![12552,257784,160008,110328]⟩,
    ⟨4,16,97,63,4,true,![91260,973704,714482,350482],![90632,974328,713224,351736]⟩,
    ⟨4,32,200,127,4,true,![444668,3782408,3001842,1225234],![443400,3783672,2999304,1227768]⟩,
    ⟨8,2,14,14,7,true,![1288,35580,20884,15984],![1150,35714,20606,16258]⟩,
    ⟨8,4,40,30,5,true,![468,138800,70400,68868],![170,139094,69802,69462]⟩,
    ⟨8,8,91,62,5,true,![74676,466000,419360,121316],![74058,466614,418122,122550]⟩,
    ⟨8,16,193,126,4,true,![116466,2013458,1297374,832550],![115208,2014712,1294856,835064]⟩,
    ⟨8,32,398,254,4,true,![757234,7696914,5740510,2713638],![754696,7699448,5735432,2718712]⟩,
    ⟨16,2,27,29,1,false,![55602,18130,586,73146],![55314,18414,18,73710]⟩,
    ⟨16,4,78,60,7,true,![17220,261312,173468,105064],![16622,261906,172270,106258]⟩,
    ⟨16,8,181,124,5,true,![17952,1063396,576248,505100],![16714,1064630,573770,507574]⟩,
    ⟨16,16,385,252,5,true,![625760,3634084,3380792,879052],![623242,3636598,3375754,884086]⟩,
    ⟨16,32,795,508,4,true,![989150,15919142,10431414,6476878],![984072,15924216,10421256,6487032]⟩,
    ⟨32,2,53,57,2,true,![604,146856,74902,72558],![36,147420,73764,73692]⟩,
    ⟨32,4,155,121,2,false,![476412,80648,117164,439896],![475204,81852,114756,442300]⟩,
    ⟨32,8,360,248,7,true,![166780,1995912,1414444,748248],![164302,1998386,1409486,753202]⟩,
    ⟨32,16,769,504,5,true,![202296,8317388,4663784,3855900],![197258,8322422,4653706,3865974]⟩,
    ⟨32,32,1589,1016,5,true,![5123256,28693324,27153512,6663068],![5113098,28703478,27133194,6683382]⟩]

/-- Each of the eighty equalities is a polynomial identity in an unrestricted integer. -/
theorem affine_first_identity (i : Fin 20) (u : ℤ) (r : Fin 4) :
    let w := affineSmallRows i
    smallFirstSlacks w.p w.q (8*u) w.v (w.j*u) (8*u*w.block-1) w.before r=
      w.atOne r+(u-1)*w.slope r := by
  fin_cases i <;> fin_cases r <;>
    norm_num [affineSmallRows,smallFirstSlacks,oldEnds,newEnds,A,B,L,K,SU,SV,SW,Y,Z,T] <;>
    ring

/-- The finite checks concern coefficients and stocks, not an exponent cutoff. -/
theorem affine_small_data (i : Fin 20) :
    let w := affineSmallRows i
    4≤w.p ∧ 2≤w.q ∧ 2≤w.block ∧ w.j<8 ∧
    1≤w.v ∧ 2*w.v≤4*w.p*w.q ∧
    5≤(5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1) ∧
    (5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1)≤9 ∧
    ∀ r : Fin 4, 0≤w.atOne r ∧ 0≤w.slope r := by
  fin_cases i <;> norm_num [affineSmallRows]
  all_goals intro r; fin_cases r <;> norm_num

/-- Actual charged windows for every integer u>=1, strictly stronger than dyadic u. -/
theorem affine_small_bounds (i : Fin 20) (u : ℤ) (hu : 1≤u) :
    let w := affineSmallRows i
    rowBounds 4 w.p w.q (8*u) w.v (w.j*u) (8*u*w.block-1) w.before := by
  let w := affineSmallRows i
  have data := affine_small_data i
  change 4≤w.p ∧ 2≤w.q ∧ 2≤w.block ∧ w.j<8 ∧
    1≤w.v ∧ 2*w.v≤4*w.p*w.q ∧
    5≤(5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1) ∧
    (5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1)≤9 ∧
    ∀ r : Fin 4, 0≤w.atOne r ∧ 0≤w.slope r at data
  rcases data with ⟨hp,hq,hC,hj,hv0,hv,hd0,hd1,hcoef⟩
  have hpZ : (4:ℤ)≤w.p := by exact_mod_cast hp
  have hqZ : (2:ℤ)≤w.q := by exact_mod_cast hq
  have hv0Z : (1:ℤ)≤w.v := by exact_mod_cast hv0
  have hvZ : 2*(w.v:ℤ)≤T (4:ℤ) w.p w.q := by
    dsimp [T]
    exact_mod_cast hv
  have hdid : smallDelta w.p w.q (8*u) (8*u*w.block-1)=
      8*u*((5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1))-5 := by
    dsimp [smallDelta,Y,T]; ring
  have hdl := mul_nonneg (show 0≤8*u by omega)
    (show 0≤(5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1)-5 by omega)
  have hdu := mul_nonneg (show 0≤8*u by omega)
    (show 0≤9-((5:ℤ)*(w.block:ℤ)-8*(w.p:ℤ)*((w.q:ℤ)-1)) by omega)
  have hdp := mul_nonneg (show 0≤8*u by omega) (show 0≤4*(w.p:ℤ)-9 by omega)
  apply finish_small_bounds w.p w.q (8*u) w.v (w.j*u) (8*u*w.block-1) w.before
    hpZ hqZ (by omega) hv0Z hvZ
  · rw [hdid]; nlinarith only [hdl,hu]
  · rw [hdid]; nlinarith only [hdu,hdp]
  · intro r
    rw [affine_first_identity]
    exact add_nonneg (hcoef r).1 (mul_nonneg (by omega) (hcoef r).2)

/-- Bits require dyadic h; the affine inequalities above do not. -/
theorem affine_small_selection (i : Fin 20) (H : ℕ) (hH : 3≤H) :
    let w := affineSmallRows i
    ∃ v m M : ℕ, ∃ before : Bool,
      Submask m M ∧ m<M ∧ rowBounds 4 w.p w.q (2^H) v m M before := by
  let w := affineSmallRows i
  let u : ℕ := 2^(H-3)
  have hpower : (2:ℕ)^H=8*u := by
    calc
      (2:ℕ)^H=2^(3+(H-3)) := by congr 1; omega
      _=8*u := by rw [pow_add]; norm_num [u]
  have hu : 1≤u := by dsimp [u]; have := Nat.two_pow_pos (H-3); omega
  have data := affine_small_data i
  have hC : 2≤w.block := data.2.2.1
  have hj : w.j<8 := data.2.2.2.1
  have hm : w.j*u<2^H := by
    rw [hpower]
    exact mul_lt_mul_of_pos_right hj (by omega)
  have hs := small_proper_predecessor H w.block (w.j*u) hC hm
  have hprod : 1≤2^H*w.block :=
    mul_pos (Nat.two_pow_pos H) (by omega)
  have hcastM : ((2^H*w.block-1:ℕ):ℤ)=(2:ℤ)^H*w.block-1 := by
    rw [Nat.cast_sub hprod]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hpowerZ : (2:ℤ)^H=8*(u:ℤ) := by exact_mod_cast hpower
  have hb := affine_small_bounds i u (by exact_mod_cast hu)
  refine ⟨w.v,w.j*u,2^H*w.block-1,w.before,hs.1,hs.2,?_⟩
  simpa only [Nat.cast_mul,hcastM,hpowerZ] using hb

def h4SmallRows : Fin 20 → FixedRow :=
  ![⟨4,4,2,4,5,20,29,false⟩,
    ⟨4,4,4,4,6,64,80,true⟩,
    ⟨4,4,8,4,4,180,183,true⟩,
    ⟨4,4,16,4,43,132,388,true⟩,
    ⟨4,4,32,4,5,789,797,true⟩,
    ⟨4,8,2,4,7,54,55,true⟩,
    ⟨4,8,4,4,8,152,157,true⟩,
    ⟨4,8,8,4,9,352,362,true⟩,
    ⟨4,8,16,4,47,516,772,true⟩,
    ⟨4,8,32,4,8,1589,1591,true⟩,
    ⟨4,16,2,4,20,66,106,false⟩,
    ⟨4,16,4,4,15,310,311,true⟩,
    ⟨4,16,8,4,25,656,720,true⟩,
    ⟨4,16,16,4,16,1536,1540,true⟩,
    ⟨4,16,32,4,27,3104,3178,true⟩,
    ⟨4,32,2,4,55,16,208,true⟩,
    ⟨4,32,4,4,31,610,618,true⟩,
    ⟨4,32,8,4,31,1436,1437,true⟩,
    ⟨4,32,16,4,32,3073,3077,false⟩,
    ⟨4,32,32,4,34,6336,6352,true⟩]

theorem h4_small_bounds (i : Fin 20) :
    let w := h4SmallRows i
    rowBounds 4 w.p w.q 4 w.v w.m w.M w.before := by
  constructor
  · intro r
    fin_cases i <;> fin_cases r <;>
      norm_num [h4SmallRows,oldEnds,newEnds,oldHeads,newHeads,A,B,L,K,SU,SV,SW,Y,Z,T]
  · fin_cases i <;> norm_num [h4SmallRows,T,Y]

theorem h4_small_bits (i : Fin 20) :
    let w := h4SmallRows i
    Submask w.m w.M ∧ w.m<w.M := by
  constructor
  · apply submask_of_land
    fin_cases i <;> decide
  · fin_cases i <;> decide

theorem small_row_pairs (p q : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32)
    (hq : q=2 ∨ q=4 ∨ q=8 ∨ q=16 ∨ q=32) :
    ∃ i : Fin 20, (affineSmallRows i).p=p ∧ (affineSmallRows i).q=q := by
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,by norm_num [affineSmallRows]⟩
  · exact ⟨1,by norm_num [affineSmallRows]⟩
  · exact ⟨2,by norm_num [affineSmallRows]⟩
  · exact ⟨3,by norm_num [affineSmallRows]⟩
  · exact ⟨4,by norm_num [affineSmallRows]⟩
  · exact ⟨5,by norm_num [affineSmallRows]⟩
  · exact ⟨6,by norm_num [affineSmallRows]⟩
  · exact ⟨7,by norm_num [affineSmallRows]⟩
  · exact ⟨8,by norm_num [affineSmallRows]⟩
  · exact ⟨9,by norm_num [affineSmallRows]⟩
  · exact ⟨10,by norm_num [affineSmallRows]⟩
  · exact ⟨11,by norm_num [affineSmallRows]⟩
  · exact ⟨12,by norm_num [affineSmallRows]⟩
  · exact ⟨13,by norm_num [affineSmallRows]⟩
  · exact ⟨14,by norm_num [affineSmallRows]⟩
  · exact ⟨15,by norm_num [affineSmallRows]⟩
  · exact ⟨16,by norm_num [affineSmallRows]⟩
  · exact ⟨17,by norm_num [affineSmallRows]⟩
  · exact ⟨18,by norm_num [affineSmallRows]⟩
  · exact ⟨19,by norm_num [affineSmallRows]⟩

theorem h4_pairs (i : Fin 20) :
    (h4SmallRows i).p=(affineSmallRows i).p ∧
    (h4SmallRows i).q=(affineSmallRows i).q := by
  fin_cases i <;> norm_num [h4SmallRows,affineSmallRows]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
