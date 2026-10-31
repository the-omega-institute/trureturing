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
  simpa only [← List.range_eq_range', rank, show d + s + s + s = 3 * s + d by omega]

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
  have pu := packet_laws f 0 d A N V (by omega) cp.1 r1 (by simpa only [Nat.zero_add] using tab.u)
  have pv := packet_laws f d s V N W (by omega) cp.2.2.1 r2 tab.v
  have pw := packet_laws f (d + s) s W N X (by omega) cp.2.2.2.2.1 r3 tab.w
  have gu := packet_laws g 0 d (2 * A) M Vn (by omega) cp.2.1 j1 (by simpa only [Nat.zero_add] using tab.un)
  have gv := packet_laws g d s Vn M Wn (by omega) cp.2.2.2.1 j2 tab.vn
  have gw := packet_laws g (d + s) s Wn M Xn (by omega) cp.2.2.2.2.2.1 j3 tab.wn
  have pt := range_positive f (d+s+s) (s-1) X cp.2.2.2.2.2.2.1 tab.x
  have gt := range_positive g (d+s+s) (s-1) Xn cp.2.2.2.2.2.2.2 tab.xn
  have n1 := tab.nu
  have n2 := tab.nv
  have n3 := tab.nw
  have n4 := tab.nx
  have m1 := tab.nun
  have m2 := tab.nvn
  have m3 := tab.nwn
  have m4 := tab.nxn
  have hp : word.Perm (List.range (rank s d)) := natural_inventory s d hs hd
  have hz : (word.map f).sum = 0 := old_total s d hs hd word hp
  have hhalfD : 2 * (2 : ℤ) ^ (d - 1) = D := by
    dsimp [D]
    conv_rhs => rw [show d = d - 1 + 1 by omega, pow_succ]
    ring
  have heN : N = 2 * ((2 : ℤ) ^ (d-1) * R * R * R - 1) + 1 := by rw [hN, ←hhalfD]; ring
  have hhalf : N = 2 * (N/2) + 1 := by omega
  have hmhalf : M/2 = N := by omega
  have hC0 : 0 < C := by dsimp [C,eta]; positivity
  have hCA : C + 1 ≤ A ∧ R + 2 ≤ A ∧ 3 * C ≤ 2 * A := by
    have hRR : 0 ≤ R * R := mul_self_nonneg R
    have hRR1 : R + 1 ≤ R * R := by nlinarith
    have hcube : 4 * (R * R) ≤ R * R * R :=
      mul_le_mul_of_nonneg_right hR hRR
    dsimp [C,A,eta,seed]
    constructor
    · nlinarith
    constructor <;> nlinarith
  have oldbounds : (A ≤ V ∧ V ≤ 2 * A - 1) ∧
      (A ≤ W ∧ W ≤ 2 * A - 1) ∧ (A ≤ X ∧ X ≤ 2 * A - 1) := by
    rcases hcase with he | he
    · have hDR : D = R := by dsimp [D,R]; rw [he]
      have ev : V = A := by rw [show V = vcoef R D from rfl,hDR]; dsimp [A,vcoef,seed]; ring
      have ew : W = A := by rw [show W = wcoef R D from rfl,hDR]; dsimp [A,wcoef,seed]; ring
      have ex : X = A := by rw [show X = xcoef R D from rfl,hDR]; dsimp [A,xcoef,seed]; ring
      rw [ev,ew,ex]; omega
    · have hDR : D = 2 * R := by dsimp [D,R]; rw [he,pow_succ]; ring
      have ev : V = 2 * A - 1 := by dsimp [V]; rw [hDR]; dsimp [A,vcoef,seed]; ring
      have ew : W = 2 * A - R - 1 := by dsimp [W]; rw [hDR]; dsimp [A,wcoef,seed]; ring
      have ex : X = 2 * A - C := by dsimp [X]; rw [hDR]; dsimp [A,C,xcoef,seed,eta]; ring
      rw [ev,ew,ex]; omega
  have hold : InStrip f (N/2) 0 word := by
    apply three_peak_strip f U P Q T nu nv nw nx N (N/2) 0 A V W X hhalf (by omega)
      pu.1 pv.1 pw.1 n1 n2 n3 pu.2 pv.2 pw.2 pt
    · simpa only [sub_zero] using oldbounds.1
    · simpa only [sub_zero] using oldbounds.2.1
    · simpa only [sub_zero] using oldbounds.2.2
    · constructor <;> omega
    · simpa only [zero_add] using hz
  rcases hcase with he | he
  · have hDR : D = R := by dsimp [D,R]; rw [he]
    have ev : V = A := by dsimp [V]; rw [hDR]; dsimp [A,vcoef,seed]; ring
    have ew : W = A := by dsimp [W]; rw [hDR]; dsimp [A,wcoef,seed]; ring
    have ex : X = A := by dsimp [X]; rw [hDR]; dsimp [A,xcoef,seed]; ring
    have bv : A ≤ Vn ∧ Vn ≤ 2*A-1 := by dsimp [Vn]; rw [ev]; omega
    have bw : A ≤ Wn ∧ Wn ≤ 2*A-1 := by dsimp [Wn]; rw [ew]; omega
    have bx : A ≤ Xn ∧ Xn ≤ 2*A-1 := by dsimp [Xn]; rw [ex]; omega
    have hzg : A + (word.map g).sum = 0 := by
      have h := new_total s d hs hd (rank s d :: word)
        (by simpa only [List.nil_append] using inserted_perm (rank s d) [] word hp)
      simpa only [List.map_cons,List.sum_cons,hear] using h
    have hgs : InStrip g N A word := by
      apply three_peak_strip g U P Q T nu nv nw nx M N A (2*A) Vn Wn Xn hM (by omega)
        gu.1 gv.1 gw.1 m1 m2 m3 gu.2 gv.2 gw.2 gt
      · simpa only [show 2*A-A=A by ring] using bv
      · simpa only [show 2*A-A=A by ring] using bw
      · simpa only [show 2*A-A=A by ring] using bx
      · constructor <;> omega
      · exact hzg
    apply finish s d hs hd [] word (by simpa using hp) (by simpa using hold)
    change InStrip g (M/2) 0 (rank s d :: word)
    rw [hmhalf]
    change 0 ≤ (0 : ℤ) ∧ 0 ≤ N ∧ InStrip g N (0 + g (rank s d)) word
    rw [hear,zero_add]
    exact ⟨le_rfl,by omega,hgs⟩
  · have hDR : D = 2 * R := by dsimp [D,R]; rw [he,pow_succ]; ring
    have ev : V = 2*A-1 := by dsimp [V]; rw [hDR]; dsimp [A,vcoef,seed]; ring
    have ew : W = 2*A-R-1 := by dsimp [W]; rw [hDR]; dsimp [A,wcoef,seed]; ring
    have ex : X = 2*A-C := by dsimp [X]; rw [hDR]; dsimp [A,C,xcoef,seed,eta]; ring
    have bv : 2*A ≤ Vn ∧ Vn ≤ 4*A-1 := by dsimp [Vn]; rw [ev]; omega
    have bw : 2*A ≤ Wn ∧ Wn ≤ 4*A-1 := by dsimp [Wn]; rw [ew]; omega
    have bx : 2*A ≤ Xn ∧ Xn ≤ 4*A-1 := by dsimp [Xn]; rw [ex]; omega
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
      · rw [hear]; omega
      · exact gt i hi
    have hgs : InStrip g N 0 (U ++ nu :: P ++ nv :: Q ++ nw :: (rank s d :: T) ++ [nx]) := by
      apply three_peak_strip g U P Q (rank s d :: T) nu nv nw nx M N 0
        (2*A) Vn Wn Xn hM (by omega) gu.1 gv.1 gw.1 m1 m2 m3 gu.2 gv.2 gw.2 hgt
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bv
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bw
      · simpa only [sub_zero,show 2*(2*A)-1=4*A-1 by ring] using bx
      · constructor <;> omega
      · simpa only [zero_add] using htotal
    apply finish s d hs hd left right (by rw [hsplit]; exact hp)
    · rw [hsplit]; exact hold
    · change InStrip g (M/2) 0 _
      rw [hmhalf]
      simpa only [left,right,List.append_assoc,List.cons_append,List.nil_append] using hgs

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
