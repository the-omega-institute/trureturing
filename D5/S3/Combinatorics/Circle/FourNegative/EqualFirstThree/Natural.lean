/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Natural
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-natural-schedules)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Natural physical schedules for the diagonal and the critical interior-ear slice. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

/-! The critical slice inserts its literal ear after three complete physical chains. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private seed eta vcoef wcoef xcoef Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private rank amplitude oldRow newRow source_data coeff_positive range_positive
  old_total inserted_perm new_total finish
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private ladder_sum from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

private theorem packet_laws (f : ℕ → ℤ) (off len : ℕ) (F N Y : ℤ)
    (hlen : 1 ≤ len) (hF : 0 ≤ F) (hrec : (2 : ℤ) ^ len * F = N + Y)
    (hf : ∀ i < len - 1, f (off + i) = (2 : ℤ) ^ i * F) :
    2 * ((List.range' off (len - 1)).map f).sum = N + Y - 2 * F ∧
      ∀ i ∈ List.range' off (len - 1), 0 ≤ f i := by
  refine ⟨?_, range_positive f off (len - 1) F hF hf⟩
  rw [ladder_sum f off (len - 1) F hf]
  have he : (2 : ℤ) ^ len = 2 * 2 ^ (len - 1) := by
    conv_lhs => rw [show len = len - 1 + 1 by omega, pow_succ]
    ring
  rw [he] at hrec
  nlinarith only [hrec]

private theorem natural_inventory (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d) :
    (List.range' 0 (d - 1) ++ (d - 1) :: List.range' d (s - 1) ++
      (d + s - 1) :: List.range' (d + s) (s - 1) ++
      (d + s + s - 1) :: List.range' (d + s + s) (s - 1) ++
      [d + s + s + s - 1]).Perm (List.range (rank s d)) := by
  have block (off len : ℕ) (hlen : 1 ≤ len) :
      List.range' off (len - 1) ++ [off + len - 1] = List.range' off len := by
    simpa only [show off + len - 1 = off + (len - 1) by omega,
      show len - 1 + 1 = len by omega] using
      (List.range'_1_concat (s := off) (n := len - 1)).symm
  have h1 := block 0 d (by omega)
  have h2 := block d s (by omega)
  have h3 := block (d + s) s (by omega)
  have h4 := block (d + s + s) s (by omega)
  simp only [Nat.zero_add] at h1
  have he : List.range' 0 (d - 1) ++ (d - 1) :: List.range' d (s - 1) ++
      (d + s - 1) :: List.range' (d + s) (s - 1) ++
      (d + s + s - 1) :: List.range' (d + s + s) (s - 1) ++
      [d + s + s + s - 1] =
      (List.range' 0 (d - 1) ++ [d - 1]) ++
      (List.range' d (s - 1) ++ [d + s - 1]) ++
      (List.range' (d + s) (s - 1) ++ [d + s + s - 1]) ++
      (List.range' (d + s + s) (s - 1) ++ [d + s + s + s - 1]) := by
    simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  rw [he, h1, h2, h3, h4]
  have h12 := List.range'_append_1 (s := 0) (m := d) (n := s)
  have h123 := List.range'_append_1 (s := 0) (m := d + s) (n := s)
  have h1234 := List.range'_append_1 (s := 0) (m := d + s + s) (n := s)
  simp only [Nat.zero_add] at h12 h123 h1234
  rw [h12, h123, h1234]
  simpa only [← List.range_eq_range', rank, show d + s + s + s = 3 * s + d by omega] using
    (List.Perm.refl (List.range (rank s d)))

private theorem three_peak_strip (f : ℕ → ℤ) (P Q S G : List ℕ)
    (nu nv nw nx : ℕ) (N B h a b c e : ℤ)
    (hNB : N = 2 * B + 1) (hh : 0 ≤ h)
    (p1 : 2 * (P.map f).sum = N + b - 2 * a)
    (p2 : 2 * (Q.map f).sum = N + c - 2 * b)
    (p3 : 2 * (S.map f).sum = N + e - 2 * c)
    (n1 : 2 * f nu = b - N) (n2 : 2 * f nv = c - N)
    (n3 : 2 * f nw = e - N)
    (posP : ∀ i ∈ P, 0 ≤ f i) (posQ : ∀ i ∈ Q, 0 ≤ f i)
    (posS : ∀ i ∈ S, 0 ≤ f i) (posG : ∀ i ∈ G, 0 ≤ f i)
    (hb : a - h ≤ b ∧ b ≤ 2 * (a - h) - 1)
    (hc : a - h ≤ c ∧ c ≤ 2 * (a - h) - 1)
    (he : a - h ≤ e ∧ e ≤ 2 * (a - h) - 1)
    (last : 0 ≤ -f nx ∧ -f nx ≤ B)
    (total : h + ((P ++ nu :: Q ++ nv :: S ++ nw :: G ++ [nx]).map f).sum = 0) :
    InStrip f B h (P ++ nu :: Q ++ nv :: S ++ nw :: G ++ [nx]) := by
  apply four_strip f P Q S G nu nv nw nx B h posP posQ posS posG hh
  · constructor <;> omega
  · constructor <;> omega
  · constructor <;> omega
  · exact last
  · exact total

private theorem diagonal_coefficients (R : ℤ) (hR : 4≤R) :
    (seed R≤vcoef R R ∧ vcoef R R≤2*seed R-1) ∧
    (seed R≤wcoef R R ∧ wcoef R R≤2*seed R-1) ∧
    (seed R≤xcoef R R ∧ xcoef R R≤2*seed R-1) ∧
    (seed R≤2*vcoef R R-1 ∧ 2*vcoef R R-1≤2*seed R-1) ∧
    (seed R≤2*wcoef R R-R-1 ∧ 2*wcoef R R-R-1≤2*seed R-1) ∧
    (seed R≤2*xcoef R R-eta R ∧ 2*xcoef R R-eta R≤2*seed R-1) := by
  obtain ⟨z,hz,rfl⟩ : ∃ z : ℤ,0≤z ∧ R=z+4 := ⟨R-4,by omega,by omega⟩
  dsimp [seed,vcoef,wcoef,xcoef,eta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

private theorem critical_coefficients (R : ℤ) (hR : 4≤R) :
    (seed R≤vcoef R (2*R) ∧ vcoef R (2*R)≤2*seed R-1) ∧
    (seed R≤wcoef R (2*R) ∧ wcoef R (2*R)≤2*seed R-1) ∧
    (seed R≤xcoef R (2*R) ∧ xcoef R (2*R)≤2*seed R-1) ∧
    (2*seed R≤2*vcoef R (2*R)-1 ∧ 2*vcoef R (2*R)-1≤4*seed R-1) ∧
    (2*seed R≤2*wcoef R (2*R)-R-1 ∧ 2*wcoef R (2*R)-R-1≤4*seed R-1) ∧
    (2*seed R≤2*xcoef R (2*R)-eta R ∧ 2*xcoef R (2*R)-eta R≤4*seed R-1) := by
  obtain ⟨z,hz,rfl⟩ : ∃ z : ℤ,0≤z ∧ R=z+4 := ⟨R-4,by omega,by omega⟩
  dsimp [seed,vcoef,wcoef,xcoef,eta]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

-- The two actual physical rows share packets but have different initial heights.
set_option maxHeartbeats 1600000 in
private theorem natural_slices (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d)
    (hcase : d = s ∨ d = s + 1) :
    ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut ≤ rank s d ∧
      OriginalOrder (rank s d) (amplitude s) sigma ∧
      OriginalOrder (rank s d + 1) (2 * amplitude s) (earWord (rank s d) sigma cut) := by
  let R : ℤ := 2 ^ s
  let D : ℤ := 2 ^ d
  let N := modulus (rank s d)
  let M := modulus (rank s d + 1)
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let Vn := 2 * V - 1
  let Wn := 2 * W - R - 1
  let Xn := 2 * X - C
  let f := oldRow s d
  let g := newRow s d
  let U := List.range' 0 (d - 1)
  let P := List.range' d (s - 1)
  let Q := List.range' (d + s) (s - 1)
  let T := List.range' (d + s + s) (s - 1)
  let nu := d - 1
  let nv := d + s - 1
  let nw := d + s + s - 1
  let nx := d + s + s + s - 1
  let word := U ++ nu :: P ++ nv :: Q ++ nw :: T ++ [nx]
  obtain ⟨tab, ⟨hR, hD⟩, hamp, hN, hM, hA0, hAN, hear⟩ := source_data s d hs hd
  change Table s d R D N f g at tab
  change (amplitude s : ℤ) = A at hamp
  change N = D * R * R * R - 1 at hN
  change M = 2 * N + 1 at hM
  change 0 < A at hA0
  change A < N at hAN
  change g (rank s d) = A at hear
  have cp := coeff_positive R D hR hD
  change 0 ≤ A ∧ 0 ≤ 2 * A ∧ 0 ≤ V ∧ 0 ≤ Vn ∧ 0 ≤ W ∧ 0 ≤ Wn ∧ 0 ≤ X ∧ 0 ≤ Xn at cp
  have r1 : (2 : ℤ) ^ d * A = N + V := by change D * A = N + V; rw [hN]; dsimp [A,V,seed,vcoef]; ring
  have r2 : (2 : ℤ) ^ s * V = N + W := by change R * V = N + W; rw [hN]; dsimp [V,W,vcoef,wcoef]; ring
  have r3 : (2 : ℤ) ^ s * W = N + X := by change R * W = N + X; rw [hN]; dsimp [W,X,wcoef,xcoef]; ring
  have j1 : (2 : ℤ) ^ d * (2 * A) = M + Vn := by change D * (2 * A) = M + Vn; rw [hM]; dsimp [Vn]; nlinarith only [r1]
  have j2 : (2 : ℤ) ^ s * Vn = M + Wn := by change R * Vn = M + Wn; rw [hM,hN]; dsimp [Vn,Wn,V,W,vcoef,wcoef]; ring
  have j3 : (2 : ℤ) ^ s * Wn = M + Xn := by change R * Wn = M + Xn; rw [hM,hN]; dsimp [Wn,Xn,W,X,C,wcoef,xcoef,eta]; ring
  have pu := packet_laws f 0 d A N V (le_trans (by decide) hd) cp.1 r1 (by simpa only [Nat.zero_add] using (Table.u tab))
  have pv := packet_laws f d s V N W (le_trans (by decide) hs) cp.2.2.1 r2 (Table.v tab)
  have pw := packet_laws f (d + s) s W N X (le_trans (by decide) hs) cp.2.2.2.2.1 r3 (Table.w tab)
  have gu := packet_laws g 0 d (2 * A) M Vn (le_trans (by decide) hd) cp.2.1 j1 (by simpa only [Nat.zero_add] using (Table.un tab))
  have gv := packet_laws g d s Vn M Wn (le_trans (by decide) hs) cp.2.2.2.1 j2 (Table.vn tab)
  have gw := packet_laws g (d + s) s Wn M Xn (le_trans (by decide) hs) cp.2.2.2.2.2.1 j3 (Table.wn tab)
  have pt := range_positive f (d+s+s) (s-1) X cp.2.2.2.2.2.2.1 (Table.x tab)
  have gt := range_positive g (d+s+s) (s-1) Xn cp.2.2.2.2.2.2.2 (Table.xn tab)
  have n1 := (Table.nu tab)
  have n2 := (Table.nv tab)
  have n3 := (Table.nw tab)
  have n4 := (Table.nx tab)
  change 2*f nx=A-N at n4
  have m1 := (Table.nun tab)
  have m2 := (Table.nvn tab)
  have m3 := (Table.nwn tab)
  have m4 := (Table.nxn tab)
  rw [←hM] at m1 m2 m3 m4
  change 2*g nx=A-M at m4
  have hp : word.Perm (List.range (rank s d)) := natural_inventory s d hs hd
  have hz : (word.map f).sum = 0 := old_total s d hs hd word hp
  have hhalfD : 2 * (2 : ℤ) ^ (d - 1) = D := by
    dsimp [D]
    conv_rhs => rw [show d = d - 1 + 1 by omega, pow_succ]
    ring
  have heN : N = 2 * ((2 : ℤ) ^ (d-1) * R * R * R - 1) + 1 := by rw [hN, ←hhalfD]; ring
  have hhalf : N = 2 * (N/2) + 1 := by
    clear * - heN
    omega
  have hmhalf : M/2 = N := by
    clear * - hM
    omega
  have oldbounds : (A≤V ∧ V≤2*A-1) ∧ (A≤W ∧ W≤2*A-1) ∧ (A≤X ∧ X≤2*A-1) := by
    rcases hcase with he | he
    · have hDR : D=R := by dsimp [D,R];rw [he]
      have hb := diagonal_coefficients R hR
      simpa only [A,V,W,X,hDR] using ⟨hb.1,hb.2.1,hb.2.2.1⟩
    · have hDR : D=2*R := by dsimp [D,R];rw [he,pow_succ];ring
      have hb := critical_coefficients R hR
      simpa only [A,V,W,X,hDR] using ⟨hb.1,hb.2.1,hb.2.2.1⟩
  have hold : InStrip f (N/2) 0 word := by
    apply three_peak_strip f U P Q T nu nv nw nx N (N/2) 0 A V W X hhalf le_rfl
      pu.1 pv.1 pw.1 n1 n2 n3 pu.2 pv.2 pw.2 pt
    · simpa only [sub_zero] using oldbounds.1
    · simpa only [sub_zero] using oldbounds.2.1
    · simpa only [sub_zero] using oldbounds.2.2
    · clear * - n4 hA0 hAN hhalf
      constructor <;> omega
    · simpa only [zero_add] using hz
  rcases hcase with he | he
  · have hDR : D = R := by dsimp [D,R]; rw [he]
    have hb := diagonal_coefficients R hR
    have bv : A≤Vn ∧ Vn≤2*A-1 := by simpa only [A,Vn,V,hDR] using hb.2.2.2.1
    have bw : A≤Wn ∧ Wn≤2*A-1 := by simpa only [A,Wn,W,hDR] using hb.2.2.2.2.1
    have bx : A≤Xn ∧ Xn≤2*A-1 := by simpa only [A,Xn,X,C,hDR] using hb.2.2.2.2.2
    have hzg : A + (word.map g).sum = 0 := by
      have h := new_total s d hs hd (rank s d :: word)
        (by simpa only [List.nil_append] using inserted_perm (rank s d) [] word hp)
      change g (rank s d)+(word.map g).sum=0 at h
      rwa [hear] at h
    have hgs : InStrip g N A word := by
      apply three_peak_strip g U P Q T nu nv nw nx M N A (2*A) Vn Wn Xn hM hA0.le
        gu.1 gv.1 gw.1 m1 m2 m3 gu.2 gv.2 gw.2 gt
      · simpa only [show 2*A-A=A by ring] using bv
      · simpa only [show 2*A-A=A by ring] using bw
      · simpa only [show 2*A-A=A by ring] using bx
      · clear * - m4 hA0 hAN hM
        constructor <;> omega
      · exact hzg
    apply finish s d hs hd [] word
      (by simpa only [List.nil_append] using hp)
      (by simpa only [List.nil_append] using hold)
    change InStrip g (M/2) 0 (rank s d :: word)
    rw [hmhalf]
    change 0 ≤ (0 : ℤ) ∧ 0 ≤ N ∧ InStrip g N (0 + g (rank s d)) word
    rw [hear,zero_add]
    exact ⟨le_rfl,le_trans hA0.le hAN.le,hgs⟩
  · have hDR : D = 2 * R := by dsimp [D,R]; rw [he,pow_succ]; ring
    have hb := critical_coefficients R hR
    have bv : 2*A≤Vn ∧ Vn≤4*A-1 := by simpa only [A,Vn,V,hDR] using hb.2.2.2.1
    have bw : 2*A≤Wn ∧ Wn≤4*A-1 := by simpa only [A,Wn,W,hDR] using hb.2.2.2.2.1
    have bx : 2*A≤Xn ∧ Xn≤4*A-1 := by simpa only [A,Xn,X,C,hDR] using hb.2.2.2.2.2
    let left := U ++ nu :: P ++ nv :: Q ++ [nw]
    let right := T ++ [nx]
    have hsplit : left ++ right = word := by
      simp only [left,right,word,List.append_assoc,List.cons_append,List.nil_append]
    have hpe : (left ++ rank s d :: right).Perm (List.range (rank s d+1)) :=
      inserted_perm _ _ _ (by rw [hsplit]; exact hp)
    have htotal : ((U ++ nu :: P ++ nv :: Q ++ nw :: (rank s d :: T) ++ [nx]).map g).sum = 0 := by
      have h := new_total s d hs hd _ hpe
      simpa only [left,right,List.append_assoc,List.cons_append,List.nil_append] using h
    have hgt : ∀ i ∈ rank s d :: T, 0 ≤ g i := by
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hear]; exact hA0.le
      · exact gt i hi
    have hgs : InStrip g N 0 (U ++ nu :: P ++ nv :: Q ++ nw :: (rank s d :: T) ++ [nx]) := by
      apply three_peak_strip g U P Q (rank s d :: T) nu nv nw nx M N 0
        (2*A) Vn Wn Xn hM le_rfl gu.1 gv.1 gw.1 m1 m2 m3 gu.2 gv.2 gw.2 hgt
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bv
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bw
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bx
      · clear * - m4 hA0 hAN hM
        constructor <;> omega
      · simpa only [zero_add] using htotal
    apply finish s d hs hd left right (by rw [hsplit]; exact hp)
    · rw [hsplit]; exact hold
    · change InStrip g (M/2) 0 _
      rw [hmhalf]
      simpa only [left,right,List.append_assoc,List.cons_append,List.nil_append] using hgs

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
