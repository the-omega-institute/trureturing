/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Large
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-large-d-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A reserved physical bit and first ear throughout the large-d cone. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Lower
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LargeArithmetic
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
open private large_bounds from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LargeArithmetic

-- Four complete packets and one reserved occurrence suffice for every d >= s+2.
set_option maxHeartbeats 2000000 in
private theorem large (s d : ℕ) (hs : 2≤s) (hds : s+2≤d) :
    ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut≤rank s d ∧
      OriginalOrder (rank s d) (amplitude s) sigma ∧
      OriginalOrder (rank s d+1) (2*amplitude s) (earWord (rank s d) sigma cut) := by
  classical
  have hd : 2≤d := by omega
  let R : ℤ := 2^s
  let D : ℤ := 2^d
  let r : ℤ := 2^(s-1)
  let e : ℤ := 2^(d-1)
  let u : ℕ := 2^(d-s-1)
  let v : ℕ := 2^(s-1)-1
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := modulus (rank s d)
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
  have hu2 : 2≤(u:ℤ) := by
    have hp : (2:ℤ)≤2^(d-s-1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤d-s-1 by omega)
    simpa only [u,Nat.cast_pow,Nat.cast_ofNat] using hp
  have hDu : D=2*R*(u:ℤ) := by
    simp only [D,R,u,Nat.cast_pow,Nat.cast_ofNat]
    calc
      (2 : ℤ)^d = 2^(s+(d-s-1)+1) := by congr 1; omega
      _ = 2*2^s*2^(d-s-1) := by rw [pow_succ,pow_add]; ring
  have hu : u<2^(d-1) := by
    have hz : (u:ℤ)<e := by nlinarith only [hR,hu2,hDu,he]
    change (u : ℤ) < (2 : ℤ)^(d-1) at hz
    exact_mod_cast hz
  have hv : v<2^(s-1) := by
    dsimp [v]
    have hp : 0<2^(s-1) := by positivity
    omega
  have hvc : (v:ℤ)=r-1 := by
    have hp : 0<2^(s-1) := by positivity
    have heq : v+1=2^(s-1) := by dsimp [v];omega
    have hz : (v:ℤ)+1=(2:ℤ)^(s-1) := by exact_mod_cast heq
    omega
  let U := split_pair f g 0 (d-1) u A (2*A) hu cp.1 cp.2.1
    (by simpa only [Nat.zero_add] using (Table.u tab)) (by simpa only [Nat.zero_add] using (Table.un tab))
  let P := split_pair f g d (s-1) v V (2*V-1) hv cp.2.2.1 cp.2.2.2.1 (Table.v tab) (Table.vn tab)
  let Q := split_pair f g (d+s) (s-1) v W (2*W-R-1) hv cp.2.2.2.2.1 cp.2.2.2.2.2.1 (Table.w tab) (Table.wn tab)
  let T := split_pair f g (d+s+s) (s-1) v X (2*X-C) hv cp.2.2.2.2.2.2.1 cp.2.2.2.2.2.2.2 (Table.x tab) (Table.xn tab)
  let F := (Pair.right U)
  let K := (Pair.left P)
  let S := (Pair.left Q)
  let G := (Pair.left U)++(Pair.right P)++(Pair.right Q)++(Pair.left T)++(Pair.right T)
  let nu := d-1
  let nv := d+s-1
  let nw := d+s+s-1
  let nx := d+s+s+s-1
  let word := F++nw::K++nv::S++nu::G++[nx]
  have hp : word.Perm (List.range (rank s d)) := by
    apply List.Perm.trans (l₂ := ((Pair.left U)++(Pair.right U))++nu::((Pair.left P)++(Pair.right P))++nv::
      ((Pair.left Q)++(Pair.right Q))++nw::((Pair.left T)++(Pair.right T))++[nx])
    · apply Multiset.coe_eq_coe.mp
      simp only [word,F,K,S,G,←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
      ac_rfl
    · exact pair_inventory s d hs hd f g A (2*A) V (2*V-1) W (2*W-R-1) X (2*X-C) u v v v U P Q T
  have fF : (F.map f).sum=(e-1-u)*A := (Pair.fr U)
  have fK : (K.map f).sum=(r-1)*V := by rw [(Pair.fl P),hvc]
  have fS : (S.map f).sum=(r-1)*W := by rw [(Pair.fl Q),hvc]
  have gF : (F.map g).sum=(e-1-u)*(2*A) := (Pair.gr U)
  have gK : (K.map g).sum=(r-1)*(2*V-1) := by rw [(Pair.gl P),hvc]
  have gS : (S.map g).sum=(r-1)*(2*W-R-1) := by rw [(Pair.gl Q),hvc]
  have pgf : ∀ i∈G,0≤f i := by
    intro i hi
    simp only [G,List.mem_append] at hi
    rcases hi with (((hi|hi)|hi)|hi)|hi
    · exact (Pair.plf U) i hi
    · exact (Pair.prf P) i hi
    · exact (Pair.prf Q) i hi
    · exact (Pair.plf T) i hi
    · exact (Pair.prf T) i hi
  have pgg : ∀ i∈G,0≤g i := by
    intro i hi
    simp only [G,List.mem_append] at hi
    rcases hi with (((hi|hi)|hi)|hi)|hi
    · exact (Pair.plg U) i hi
    · exact (Pair.prg P) i hi
    · exact (Pair.prg Q) i hi
    · exact (Pair.plg T) i hi
    · exact (Pair.prg T) i hi
  have hB : 2*(N/2)=D*R*R*R-2 := by
    have hh : N=2*(e*R*R*R-1)+1 := by rw [hN,←he];ring
    clear * - hh hN
    omega
  have cert := large_bounds R D (u:ℤ) r e (N/2) hR hu2 hDu hr he hB
  dsimp only at cert
  change Bounds _ _ _ _ _ _ _ (N/2) 0 ∧ Bounds _ _ _ _ _ _ _ (D*R*R*R-1) A at cert
  rw [←hN] at cert
  have hold : InStrip f (N/2) 0 word := by
    apply bounds_strip f F K S G nw nv nu nx (N/2) 0 (Pair.prf U) (Pair.plf P) (Pair.plf Q) pgf le_rfl
    · rw [fF,fK,fS,(Table.nw tab),(Table.nv tab),(Table.nu tab),(Table.nx tab)];exact cert.1
    · simpa only [zero_add] using old_total s d hs hd word hp
  have hzg : A+(word.map g).sum=0 := by
    have hh := new_total s d hs hd (rank s d::word)
      (by simpa only [List.nil_append] using inserted_perm (rank s d) [] word hp)
    change g (rank s d)+(word.map g).sum=0 at hh
    rwa [hear] at hh
  have hgs : InStrip g N A word := by
    apply bounds_strip g F K S G nw nv nu nx N A (Pair.prg U) (Pair.plg P) (Pair.plg Q) pgg hA.le
    · rw [gF,gK,gS,(Table.nwn tab),(Table.nvn tab),(Table.nun tab),(Table.nxn tab)];exact cert.2
    · exact hzg
  apply finish s d hs hd [] word
    (by simpa only [List.nil_append] using hp)
    (by simpa only [List.nil_append] using hold)
  change InStrip g (modulus (rank s d+1)/2) 0 (rank s d::word)
  have hh : modulus (rank s d+1)/2=N := by
    clear * - hM
    change modulus (rank s d+1)=2*N+1 at hM
    omega
  rw [hh]
  change 0≤(0:ℤ) ∧ 0≤N ∧ InStrip g N (0+g (rank s d)) word
  rw [hear,zero_add]
  exact ⟨le_rfl,le_trans hA.le hAN.le,hgs⟩
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
