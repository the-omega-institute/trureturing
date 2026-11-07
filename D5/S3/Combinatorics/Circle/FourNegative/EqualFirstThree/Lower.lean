/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Lower
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-delayed-ear-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A physical delayed ear throughout the complete lower small-d window. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Masked
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic

/-! Four negative labels appear in V,W,U,X order; the ear precedes the last one. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private seed eta vcoef wcoef xcoef Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private rank amplitude oldRow newRow source_data coeff_positive old_total inserted_perm
  new_total finish from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private Pair Pair.left Pair.right Pair.fl Pair.fr Pair.gl Pair.gr
  Pair.plf Pair.prf Pair.plg Pair.prg split_pair pair_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Masked
open private Bounds lower_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

private theorem bounds_strip (f : ℕ → ℤ) (P Q S G : List ℕ)
    (n1 n2 n3 n4 : ℕ) (B h : ℤ)
    (pp : ∀ i ∈ P, 0 ≤ f i) (pq : ∀ i ∈ Q, 0 ≤ f i)
    (ps : ∀ i ∈ S, 0 ≤ f i) (pg : ∀ i ∈ G, 0 ≤ f i) (hh : 0 ≤ h)
    (hb : Bounds (P.map f).sum (Q.map f).sum (S.map f).sum
      (2*f n1) (2*f n2) (2*f n3) (2*f n4) B h)
    (ht : h + ((P ++ n1 :: Q ++ n2 :: S ++ n3 :: G ++ [n4]).map f).sum = 0) :
    InStrip f B h (P ++ n1 :: Q ++ n2 :: S ++ n3 :: G ++ [n4]) := by
  dsimp only [Bounds] at hb
  apply four_strip f P Q S G n1 n2 n3 n4 B h pp pq ps pg hh
  all_goals first | exact ht | constructor <;> omega

set_option maxHeartbeats 2000000 in
private theorem lower (s d : ℕ) (hd : 2 ≤ d) (hds : d < s) (hsd : s ≤ 2*d-1) :
    ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut ≤ rank s d ∧
      OriginalOrder (rank s d) (amplitude s) sigma ∧
      OriginalOrder (rank s d+1) (2*amplitude s) (earWord (rank s d) sigma cut) := by
  classical
  have hs : 2 ≤ s := by omega
  let R : ℤ := 2 ^ s
  let D : ℤ := 2 ^ d
  let H : ℤ := 2 ^ (s-d)
  let r : ℤ := 2 ^ (s-1)
  let e : ℤ := 2 ^ (d-1)
  let u : ℕ := 2 ^ (d-1)-1
  let v : ℕ := 2 ^ (s-1)-1
  let n : ℕ := 2 ^ (s-d)-1
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
  change (amplitude s : ℤ)=A at hamp
  change g (rank s d)=A at hear
  change 0<A at hA
  change A<N at hAN
  have cp := coeff_positive R D hR hD
  change 0≤A ∧ 0≤2*A ∧ 0≤V ∧ 0≤2*V-1 ∧ 0≤W ∧
    0≤2*W-R-1 ∧ 0≤X ∧ 0≤2*X-C at cp
  have hr : 2*r=R := by
    dsimp [r,R]
    conv_rhs => rw [show s=s-1+1 by omega,pow_succ]
    ring
  have he : 2*e=D := by
    dsimp [e,D]
    conv_rhs => rw [show d=d-1+1 by omega,pow_succ]
    ring
  have hH : 2≤H := by
    simpa [H] using pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2) (show 1≤s-d by omega)
  have hRH : D*H=R := by dsimp [D,H,R]; rw [←pow_add,show d+(s-d)=s by omega]
  have hHD : 2*H≤D := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ)≤2) (show s-d+1≤d by omega)
    simpa only [pow_succ,mul_comm] using h
  have huc : (u : ℤ)=e-1 := by
    have hp : 0 < 2^(d-1) := by positivity
    have hh : u+1=2^(d-1) := by dsimp [u]; omega
    have hz : (u : ℤ)+1=(2 : ℤ)^(d-1) := by exact_mod_cast hh
    omega
  have hvc : (v : ℤ)=r-1 := by
    have hp : 0 < 2^(s-1) := by positivity
    have hh : v+1=2^(s-1) := by dsimp [v]; omega
    have hz : (v : ℤ)+1=(2 : ℤ)^(s-1) := by exact_mod_cast hh
    omega
  have hnc : (n : ℤ)=H-1 := by
    have hp : 0 < 2^(s-d) := by positivity
    have hh : n+1=2^(s-d) := by dsimp [n]; omega
    have hz : (n : ℤ)+1=(2 : ℤ)^(s-d) := by exact_mod_cast hh
    omega
  have hu : u<2^(d-1) := by
    dsimp [u]
    have hp : 0<2^(d-1) := by positivity
    omega
  have hv : v<2^(s-1) := by
    dsimp [v]
    have hp : 0<2^(s-1) := by positivity
    omega
  have hn : n<2^(s-1) := by
    have hnr : (n : ℤ)<r := by nlinarith only [hnc,hH,hD,hRH,hr]
    change (n : ℤ) < (2 : ℤ)^(s-1) at hnr
    exact_mod_cast hnr
  let U := split_pair f g 0 (d-1) u A (2*A) hu cp.1 cp.2.1
    (by simpa only [Nat.zero_add] using (Table.u tab)) (by simpa only [Nat.zero_add] using (Table.un tab))
  let P := split_pair f g d (s-1) v V (2*V-1) hv cp.2.2.1 cp.2.2.2.1 (Table.v tab) (Table.vn tab)
  let Q := split_pair f g (d+s) (s-1) v W (2*W-R-1) hv cp.2.2.2.2.1 cp.2.2.2.2.2.1 (Table.w tab) (Table.wn tab)
  let T := split_pair f g (d+s+s) (s-1) n X (2*X-C) hn cp.2.2.2.2.2.2.1 cp.2.2.2.2.2.2.2 (Table.x tab) (Table.xn tab)
  let F := (Pair.left P)
  let K := (Pair.left Q)
  let S := (Pair.left U) ++ (Pair.left T)
  let G := (Pair.right U) ++ (Pair.right P) ++ (Pair.right Q) ++ (Pair.right T)
  let nu := d-1
  let nv := d+s-1
  let nw := d+s+s-1
  let nx := d+s+s+s-1
  let word := F ++ nv :: K ++ nw :: S ++ nu :: G ++ [nx]
  have hp : word.Perm (List.range (rank s d)) := by
    apply List.Perm.trans (l₂ := ((Pair.left U)++(Pair.right U)) ++ nu ::
      ((Pair.left P)++(Pair.right P)) ++ nv :: ((Pair.left Q)++(Pair.right Q)) ++ nw :: ((Pair.left T)++(Pair.right T)) ++ [nx])
    · apply Multiset.coe_eq_coe.mp
      simp only [word,F,K,S,G,←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
      ac_rfl
    · exact pair_inventory s d hs hd f g A (2*A) V (2*V-1) W (2*W-R-1) X (2*X-C) u v v n U P Q T
  have fF : (F.map f).sum=(r-1)*V := by rw [(Pair.fl P),hvc]
  have fK : (K.map f).sum=(r-1)*W := by rw [(Pair.fl Q),hvc]
  have fS : (S.map f).sum=(e-1)*A+(H-1)*X := by
    simp only [S,List.map_append,List.sum_append,(Pair.fl U),(Pair.fl T),huc,hnc]
  have gF : (F.map g).sum=(r-1)*(2*V-1) := by rw [(Pair.gl P),hvc]
  have gK : (K.map g).sum=(r-1)*(2*W-R-1) := by rw [(Pair.gl Q),hvc]
  have gS : (S.map g).sum=(e-1)*(2*A)+(H-1)*(2*X-C) := by
    simp only [S,List.map_append,List.sum_append,(Pair.gl U),(Pair.gl T),huc,hnc]
  have hB : 2*(N/2)=D*R*R*R-2 := by
    have hh : N=2*(e*R*R*R-1)+1 := by rw [hN,←he]; ring
    clear * - hh hN
    omega
  have cert := lower_bounds R D H r e (N/2) hD hH hHD hRH hr he hB
  change Bounds ((r-1)*V) ((r-1)*W) ((e-1)*A+(H-1)*X)
      (W-(D*R*R*R-1)) (X-(D*R*R*R-1)) (V-(D*R*R*R-1)) (A-(D*R*R*R-1)) (N/2) 0 ∧
    Bounds ((r-1)*(2*V-1)) ((r-1)*(2*W-R-1)) ((e-1)*(2*A)+(H-1)*(2*X-C))
      (2*W-R-1-(2*(D*R*R*R-1)+1)) (2*X-C-(2*(D*R*R*R-1)+1))
      (2*V-1-(2*(D*R*R*R-1)+1)) (A-(2*(D*R*R*R-1)+1)) (D*R*R*R-1) 0 at cert
  rw [←hN] at cert
  have psf : ∀ i∈S,0≤f i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi; exact (Pair.plf U) i hi; exact (Pair.plf T) i hi
  have psg : ∀ i∈S,0≤g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi; exact (Pair.plg U) i hi; exact (Pair.plg T) i hi
  have pgf : ∀ i∈G,0≤f i := by
    intro i hi
    simp only [G,List.mem_append] at hi
    rcases hi with ((hi|hi)|hi)|hi
    · exact (Pair.prf U) i hi
    · exact (Pair.prf P) i hi
    · exact (Pair.prf Q) i hi
    · exact (Pair.prf T) i hi
  have pgg : ∀ i∈G,0≤g i := by
    intro i hi
    simp only [G,List.mem_append] at hi
    rcases hi with ((hi|hi)|hi)|hi
    · exact (Pair.prg U) i hi
    · exact (Pair.prg P) i hi
    · exact (Pair.prg Q) i hi
    · exact (Pair.prg T) i hi
  have hold : InStrip f (N/2) 0 word := by
    apply bounds_strip f F K S G nv nw nu nx (N/2) 0 (Pair.plf P) (Pair.plf Q) psf pgf le_rfl
    · rw [fF,fK,fS,(Table.nv tab),(Table.nw tab),(Table.nu tab),(Table.nx tab)]
      exact cert.1
    · simpa only [zero_add] using old_total s d hs hd word hp
  let left := F ++ nv :: K ++ nw :: S ++ nu :: G
  have hsplit : left ++ [nx]=word := by
    simp only [left,word,List.append_assoc,List.cons_append,List.nil_append]
  have hew : (left ++ rank s d :: [nx]).Perm (List.range (rank s d+1)) :=
    inserted_perm _ _ _ (by rw [hsplit]; exact hp)
  have htotal : ((F ++ nv :: K ++ nw :: S ++ nu :: (G++[rank s d]) ++ [nx]).map g).sum=0 := by
    have h := new_total s d hs hd _ hew
    simpa only [left,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using h
  have pge : ∀ i∈G++[rank s d],0≤g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact pgg i hi
    · have hi : i=rank s d := by simpa using hi
      subst i; rw [hear]; exact hA.le
  have hnew : InStrip g N 0 (F ++ nv :: K ++ nw :: S ++ nu :: (G++[rank s d]) ++ [nx]) := by
    apply bounds_strip g F K S (G++[rank s d]) nv nw nu nx N 0 (Pair.plg P) (Pair.plg Q) psg pge le_rfl
    · rw [gF,gK,gS,(Table.nvn tab),(Table.nwn tab),(Table.nun tab),(Table.nxn tab)]
      exact cert.2
    · simpa only [zero_add] using htotal
  apply finish s d hs hd left [nx] (by rw [hsplit]; exact hp)
  · rw [hsplit]; exact hold
  · change InStrip g (modulus (rank s d+1)/2) 0 _
    have hh : modulus (rank s d+1)/2=N := by
      clear * - hM
      change modulus (rank s d+1)=2*N+1 at hM
      omega
    rw [hh]
    simpa only [left,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using hnew

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
