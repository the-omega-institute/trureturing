/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Hard
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-last-u-schedule)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: An actual floor mask and interior ear throughout the hard small-d window. -/
import Mathlib.Data.Int.DivMod
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Lower
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.HardArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private seed eta vcoef wcoef xcoef Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn
  Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private rank amplitude oldRow newRow source_data coeff_positive old_total inserted_perm new_total finish
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private Pair Pair.left Pair.right Pair.fl Pair.fr Pair.gl Pair.gr Pair.plf Pair.prf Pair.plg Pair.prg
  split_pair pair_inventory from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Masked
open private bounds_strip from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Lower
open private Bounds from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic
open private hard_bounds from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.HardArithmetic
open private hard_floor from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Arithmetic

-- The residual charge bounds the ear peak after all unselected X positives.
set_option maxHeartbeats 2000000 in
private theorem hard (s d : ℕ) (hd : 2≤d) (hhard : 2*d≤s) :
    ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut≤rank s d ∧
      OriginalOrder (rank s d) (amplitude s) sigma ∧
      OriginalOrder (rank s d+1) (2*amplitude s) (earWord (rank s d) sigma cut) := by
  classical
  have hs : 2≤s := by omega
  let R : ℤ := 2^s
  let D : ℤ := 2^d
  let H : ℤ := 2^(s-d)
  let r : ℤ := 2^(s-1)
  let e : ℤ := 2^(d-1)
  let u : ℕ := 2^(d-1)-1
  let n : ℕ := 2^(s-d)-1
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := modulus (rank s d)
  let HU := (N-V)/2
  let xi := (HU-(r-H)*W)/X
  let x := xi.toNat
  let f := oldRow s d
  let g := newRow s d
  obtain ⟨tab,⟨hR,hD⟩,hamp,hN,hM,hA,hAN,hear⟩ := source_data s d hs hd
  change Table s d R D N f g at tab
  change N=D*R*R*R-1 at hN
  change g (rank s d)=A at hear
  change 0<A at hA
  change A<N at hAN
  have cp := coeff_positive R D hR hD
  change 0≤A ∧ 0≤2*A ∧ 0≤V ∧ 0≤2*V-1 ∧ 0≤W ∧ 0≤2*W-R-1 ∧ 0≤X ∧ 0≤2*X-C at cp
  have hr : 2*r=R := by
    dsimp [r,R]
    conv_rhs => rw [show s=s-1+1 by omega,pow_succ]
    ring
  have he : 2*e=D := by
    dsimp [e,D]
    conv_rhs => rw [show d=d-1+1 by omega,pow_succ]
    ring
  have hRH : D*H=R := by dsimp [D,H,R];rw [←pow_add,show d+(s-d)=s by omega]
  have hH : 2≤H := by
    simpa [H] using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤s-d by omega)
  have hRD : 2*D≤R := by nlinarith only [hH,hRH,hD]
  have huc : (u:ℤ)=e-1 := by
    have hp : 0<2^(d-1) := by positivity
    have hh : u+1=2^(d-1) := by dsimp [u];omega
    have hz : (u:ℤ)+1=(2:ℤ)^(d-1) := by exact_mod_cast hh
    omega
  have hnc : (n:ℤ)=H-1 := by
    have hp : 0<2^(s-d) := by positivity
    have hh : n+1=2^(s-d) := by dsimp [n];omega
    have hz : (n:ℤ)+1=(2:ℤ)^(s-d) := by exact_mod_cast hh
    omega
  have hu : u<2^(d-1) := by
    dsimp [u]
    have hp : 0<2^(d-1) := by positivity
    omega
  have hn : n<2^(s-1) := by
    have hh : (n:ℤ)<r := by nlinarith only [hnc,hH,hD,hRH,hr]
    change (n : ℤ) < (2 : ℤ)^(s-1) at hh
    exact_mod_cast hh
  have floor := hard_floor s d hd hhard
  dsimp only at floor
  rw [←hN] at floor
  change 0≤xi ∧ xi<r ∧ 0≤HU-(r-H)*W-xi*X ∧
    1≤2*(HU-(r-H)*W-xi*X)+(1+(R+1)*(r-H)+C*xi) ∧
    2*(HU-(r-H)*W-xi*X)+(1+(R+1)*(r-H)+C*xi)≤(A-1)/2 at floor
  have hxc : (x:ℤ)=xi := Int.toNat_of_nonneg floor.1
  have hx : x<2^(s-1) := by
    have hh : (x : ℤ) < (2 : ℤ)^(s-1) := by
      change (x : ℤ) < r
      rw [hxc]
      exact floor.2.1
    exact_mod_cast hh
  let U := split_pair f g 0 (d-1) u A (2*A) hu cp.1 cp.2.1
    (by simpa only [Nat.zero_add] using Table.u tab) (by simpa only [Nat.zero_add] using Table.un tab)
  let P := split_pair f g d (s-1) n V (2*V-1) hn cp.2.2.1 cp.2.2.2.1 (Table.v tab) (Table.vn tab)
  let Q := split_pair f g (d+s) (s-1) n W (2*W-R-1) hn cp.2.2.2.2.1 cp.2.2.2.2.2.1 (Table.w tab) (Table.wn tab)
  let T := split_pair f g (d+s+s) (s-1) x X (2*X-C) hx cp.2.2.2.2.2.2.1 cp.2.2.2.2.2.2.2 (Table.x tab) (Table.xn tab)
  let F := Pair.left U++Pair.left P
  let K := Pair.right P++Pair.left Q
  let S := Pair.right T
  let G := Pair.right U++Pair.right Q++Pair.left T
  let nu := d-1
  let nv := d+s-1
  let nw := d+s+s-1
  let nx := d+s+s+s-1
  let word := F++nw::K++nv::S++nx::G++[nu]
  have hp : word.Perm (List.range (rank s d)) := by
    apply List.Perm.trans (l₂ := (Pair.left U++Pair.right U)++nu::(Pair.left P++Pair.right P)++nv::
      (Pair.left Q++Pair.right Q)++nw::(Pair.left T++Pair.right T)++[nx])
    · apply Multiset.coe_eq_coe.mp
      simp only [word,F,K,S,G,←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
      ac_rfl
    · exact pair_inventory s d hs hd f g A (2*A) V (2*V-1) W (2*W-R-1) X (2*X-C) u n n x U P Q T
  have fF : (F.map f).sum=(e-1)*A+(H-1)*V := by
    simp only [F,List.map_append,List.sum_append,Pair.fl,huc,hnc]
  have fK : (K.map f).sum=(r-H)*V+(H-1)*W := by
    simp only [K,List.map_append,List.sum_append,Pair.fr,Pair.fl,hnc]
    dsimp only [r];ring
  have fS : (S.map f).sum=(r-1-xi)*X := by rw [Pair.fr,hxc]
  have gF : (F.map g).sum=(e-1)*(2*A)+(H-1)*(2*V-1) := by
    simp only [F,List.map_append,List.sum_append,Pair.gl,huc,hnc]
  have gK : (K.map g).sum=(r-H)*(2*V-1)+(H-1)*(2*W-R-1) := by
    simp only [K,List.map_append,List.sum_append,Pair.gr,Pair.gl,hnc]
    dsimp only [r];ring
  have gS : ((S++[rank s d]).map g).sum=(r-1-xi)*(2*X-C)+A := by
    simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hear]
    rw [Pair.gr,hxc]
  have pff : ∀ i∈F,0≤f i := by intro i hi;rcases List.mem_append.mp hi with hi|hi;exact Pair.plf U i hi;exact Pair.plf P i hi
  have pfg : ∀ i∈F,0≤g i := by intro i hi;rcases List.mem_append.mp hi with hi|hi;exact Pair.plg U i hi;exact Pair.plg P i hi
  have pkf : ∀ i∈K,0≤f i := by intro i hi;rcases List.mem_append.mp hi with hi|hi;exact Pair.prf P i hi;exact Pair.plf Q i hi
  have pkg : ∀ i∈K,0≤g i := by intro i hi;rcases List.mem_append.mp hi with hi|hi;exact Pair.prg P i hi;exact Pair.plg Q i hi
  have pgf : ∀ i∈G,0≤f i := by
    intro i hi;simp only [G,List.mem_append] at hi
    rcases hi with (hi|hi)|hi
    · exact Pair.prf U i hi
    · exact Pair.prf Q i hi
    · exact Pair.plf T i hi
  have pgg : ∀ i∈G,0≤g i := by
    intro i hi;simp only [G,List.mem_append] at hi
    rcases hi with (hi|hi)|hi
    · exact Pair.prg U i hi
    · exact Pair.prg Q i hi
    · exact Pair.plg T i hi
  have pse : ∀ i∈S++[rank s d],0≤g i := by
    intro i hi;rcases List.mem_append.mp hi with hi|hi
    · exact Pair.prg T i hi
    · have hi : i=rank s d := by simpa using hi
      subst i;rw [hear];exact hA.le
  have hB : 2*(N/2)=D*R*R*R-2 := by
    have hh : N=2*(e*R*R*R-1)+1 := by rw [hN,←he];ring
    clear * - hh hN
    omega
  have hHU : 2*HU=D*R*R*R-1-V := by
    have hnu := Table.nu tab
    change 2*f (d-1)=V-N at hnu
    rw [←hN]
    clear * - hnu
    dsimp only [HU]
    omega
  have hL : 2*((A-1)/2)=A-1 := by
    have hh : A-1=2*(r*C) := by dsimp [A,C,seed,eta];rw [←hr];ring
    clear * - hh
    omega
  have cert := hard_bounds R D H r e (N/2) HU xi ((A-1)/2)
    hD hH hRD hRH hr he hB hHU hL floor.1
    ⟨floor.2.2.1,by simpa only [add_assoc] using floor.2.2.2.1,
      by simpa only [add_assoc] using floor.2.2.2.2⟩
  dsimp only at cert
  rw [←hN] at cert
  have hold : InStrip f (N/2) 0 word := by
    apply bounds_strip f F K S G nw nv nx nu (N/2) 0 pff pkf (Pair.prf T) pgf le_rfl
    · rw [fF,fK,fS,Table.nw tab,Table.nv tab,Table.nx tab,Table.nu tab];exact cert.1
    · simpa only [zero_add] using old_total s d hs hd word hp
  let left := F++nw::K++nv::S
  let right := nx::G++[nu]
  have hsplit : left++right=word := by simp only [left,right,word,List.append_assoc,List.cons_append,List.nil_append]
  have hpnew : (left++rank s d::right).Perm (List.range (rank s d+1)) := inserted_perm _ _ _ (by rw [hsplit];exact hp)
  have htotal : ((F++nw::K++nv::(S++[rank s d])++nx::G++[nu]).map g).sum=0 := by
    have hh := new_total s d hs hd _ hpnew
    simpa only [left,right,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using hh
  have hnew : InStrip g N 0 (F++nw::K++nv::(S++[rank s d])++nx::G++[nu]) := by
    apply bounds_strip g F K (S++[rank s d]) G nw nv nx nu N 0 pfg pkg pse pgg le_rfl
    · rw [gF,gK,gS,Table.nwn tab,Table.nvn tab,Table.nxn tab,Table.nun tab];exact cert.2
    · simpa only [zero_add] using htotal
  apply finish s d hs hd left right (by rw [hsplit];exact hp)
  · rw [hsplit];exact hold
  · change InStrip g (modulus (rank s d+1)/2) 0 _
    have hh : modulus (rank s d+1)/2=N := by
      clear * - hM
      change modulus (rank s d+1)=2*N+1 at hM
      omega
    rw [hh]
    simpa only [left,right,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using hnew
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
