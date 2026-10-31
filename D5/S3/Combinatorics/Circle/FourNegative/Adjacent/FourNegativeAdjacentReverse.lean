/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentReverse
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentReverse
   mirror-E: none(waiver:no-public-declarations)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: The reverse adjacent dyadic ratio has a literal first-ear joint order. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource

/-! The branch s=r+1, including its exceptional physical boundary. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentReverse
open SourceWidth PeriodicShortening RunFirstEarTransport
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private Gates four_strip from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private chains from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource

set_option maxHeartbeats 800000 in
-- The coupled peak inequalities expand quartic polynomial expressions.
private theorem arithmetic (q : ℤ) (hq : 4 ≤ q) :
    let z := 2 * q
    let N := 4 * z ^ 4 - 1
    let A := 2 * z ^ 3 + z ^ 2 + z + 1
    let B := 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1
    let L := 4 * z ^ 3 + 4 * z ^ 2 + 2 * z + 1
    let M := 4 * z ^ 3 + 2 * z ^ 2 + z + 1
    let GV := 2 * B - 1
    let GW := 2 * L - 1 - 2 * z
    let GX := 2 * M - 1 - z - 2 * z ^ 2
    Gates (N/2) (A + (q - 1) * M) (-(N - A)/2) (B + (q - 1) * L) (-(N - M)/2)
      ((z - 2) * A) (-(N - B)/2) ((z - 2) * B) (-(N - L)/2) ∧
    Gates N (3 * A + (q - 1) * GX) (-((2 * N + 1) - A)/2)
      (GV + (q - 1) * GW) (-((2 * N + 1) - GX)/2)
      ((z - 2) * (2 * A)) (-((2 * N + 1) - GV)/2)
      ((z - 2) * GV) (-((2 * N + 1) - GW)/2) := by
  dsimp only [Gates]
  have hq2 : 4 * q ≤ q ^ 2 := by nlinarith
  have hq3 : 4 * q ^ 2 ≤ q ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 4 by omega) (sq_nonneg q)]
  have hq4 : 4 * q ^ 3 ≤ q ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 4 by omega) (show 0 ≤ q ^ 3 by positivity)]
  ring_nf
  omega

private theorem inventory (n : ℕ) (hn : 3 ≤ n) :
    ([0] ++ List.range' (3 * n + 2) (n - 1) ++ [4 * n + 1] ++ [n + 1] ++
      List.range' (2 * n + 2) (n - 1) ++ [3 * n + 1] ++ List.range' 1 (n - 1) ++ [n] ++
      List.range' (n + 2) (n - 1) ++ [2 * n + 1]).Perm (List.range (2 * n + 2 * (n + 1))) := by
  have hU : [0] ++ List.range' 1 (n - 1) ++ [n] = List.range (n + 1) := by
    have h := List.range'_append_1 (s:=0) (m:=1) (n:=n - 1)
    simp only [List.range'_one,Nat.zero_add,show 1 + (n - 1) = n by omega,←List.range_eq_range'] at h
    rw [h]
    exact (List.range_succ (n:=n)).symm
  have hV : [n + 1] ++ List.range' (n + 2) (n - 1) ++ [2 * n + 1] = List.range' (n + 1) (n + 1) := by
    have h := List.range'_append_1 (s:=n + 1) (m:=1) (n:=n - 1)
    simp only [List.range'_one,show n + 1 + 1 = n + 2 by omega,show 1 + (n - 1) = n by omega] at h
    rw [h]
    simpa only [show n + 1 + n = 2 * n + 1 by omega] using (List.range'_1_concat (s:=n + 1) (n:=n)).symm
  have hW : List.range' (2 * n + 2) (n - 1) ++ [3 * n + 1] = List.range' (2 * n + 2) n := by
    simpa only [show 2 * n + 2 + (n - 1) = 3 * n + 1 by omega,show n - 1 + 1 = n by omega] using
      (List.range'_1_concat (s:=2 * n + 2) (n:=n - 1)).symm
  have hX : List.range' (3 * n + 2) (n - 1) ++ [4 * n + 1] = List.range' (3 * n + 2) n := by
    simpa only [show 3 * n + 2 + (n - 1) = 4 * n + 1 by omega,show n - 1 + 1 = n by omega] using
      (List.range'_1_concat (s:=3 * n + 2) (n:=n - 1)).symm
  have hall : ([0] ++ List.range' 1 (n - 1) ++ [n]) ++
      ([n + 1] ++ List.range' (n + 2) (n - 1) ++ [2 * n + 1]) ++
      (List.range' (2 * n + 2) (n - 1) ++ [3 * n + 1]) ++
      (List.range' (3 * n + 2) (n - 1) ++ [4 * n + 1]) = List.range (2 * n + 2 * (n + 1)) := by
    rw [hU,hV,hW,hX,List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=n + 1) (n:=n + 1)
    have h2 := List.range'_append_1 (s:=0) (m:=2 * n + 2) (n:=n)
    have h3 := List.range'_append_1 (s:=0) (m:=3 * n + 2) (n:=n)
    simp only [Nat.zero_add,show n + 1 + (n + 1) = 2 * n + 2 by omega] at h1 h2 h3
    rw [show 2 * n + 2 + n = 3 * n + 2 by omega] at h2
    calc
      _ = ((List.range' 0 (n + 1) ++ List.range' (n + 1) (n + 1)) ++ List.range' (2 * n + 2) n) ++ List.range' (3 * n + 2) n := by simp only [List.append_assoc]
      _ = List.range' 0 (3 * n + 2 + n) := by rw [h1,h2,h3]
      _ = _ := by rw [show 3 * n + 2 + n = 2 * n + 2 * (n + 1) by omega,←List.range_eq_range']
  rw [←hall]
  apply Multiset.coe_eq_coe.mp
  simp only [←Multiset.coe_add]
  ac_rfl

set_option maxHeartbeats 1600000 in
-- Physical source identities, inventories and both prefix strips are elaborated together.
private theorem symbolic (n : ℕ) (hn : 3 ≤ n) :
    ∃ sigma : List (Fin (2 * n + 2 * (n + 1))),
      OriginalOrder (2 * n + 2 * (n + 1)) (1 + 2 ^ n + 2 ^ (2 * n) + 2 ^ (2 * n + (n + 1))) sigma ∧
      OriginalOrder (2 * n + 2 * (n + 1) + 1) (2 * (1 + 2 ^ n + 2 ^ (2 * n) + 2 ^ (2 * n + (n + 1))))
        (earWord (2 * n + 2 * (n + 1)) sigma 0) := by
  let k := 2 * n + 2 * (n + 1)
  let z : ℤ := 2 ^ n
  let q : ℤ := 2 ^ (n - 1)
  let N := modulus k
  let A := 2 * z ^ 3 + z ^ 2 + z + 1
  let B := 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1
  let L := 4 * z ^ 3 + 4 * z ^ 2 + 2 * z + 1
  let M := 4 * z ^ 3 + 2 * z ^ 2 + z + 1
  let GV := 2 * B - 1
  let GW := 2 * L - 1 - 2 * z
  let GX := 2 * M - 1 - z - 2 * z ^ 2
  let t : ℕ := 1 + 2 ^ n + 2 ^ (2 * n) + 2 ^ (2 * n + (n + 1))
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
  let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * A))
  have hq : 4 ≤ q := by simpa [q] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 2 ≤ n - 1 by omega)
  have hzq : z = 2 * q := by
    dsimp [z,q]
    conv_lhs => rw [show n = (n - 1) + 1 by omega,pow_succ]
    ring
  have hN : N = 4 * z ^ 4 - 1 := by
    dsimp [N,k,modulus,z]
    rw [show 2 * n + 2 * (n + 1) = n + n + n + n + 2 by omega]
    simp only [pow_add]; ring
  have hNN : modulus (k + 1) = 2 * N + 1 := by dsimp [N,modulus]; rw [pow_succ]; ring
  have ht : (t : ℤ) = A := by
    dsimp [t,A,z]
    push_cast
    rw [show 2 * n = n + n by omega,show n + n + (n + 1) = n + n + n + 1 by omega]
    simp only [pow_add,pow_succ]; ring
  have hpw : (2 : ℤ) ^ (n + 1) = 2 * z := by dsimp [z]; rw [pow_succ]; ring
  have hA : 1 + z + z ^ 2 + z ^ 2 * (2 * z) = A := by dsimp [A]; ring
  have hB : 1 + 2 * z + z * (2 * z) + z ^ 2 * (2 * z) = B := by dsimp [B]; ring
  have hL : 1 + 2 * z + (2 * z) ^ 2 + z * (2 * z) ^ 2 = L := by dsimp [L]; ring
  have hM : 1 + z + z * (2 * z) + z * (2 * z) ^ 2 = M := by dsimp [M]; ring
  have hE : 2 * M - (1 + z + z * (2 * z)) = GX := by dsimp [GX]; ring
  obtain ⟨hU,hV,hW,hX,hU',hV',hW',hX',hear⟩ := chains n (n + 1) (by omega) (by omega)
  simp only [show (2 : ℤ) ^ n = z from rfl,hpw,hA,hB,hL,hM,hE] at hU hV hW hX hU' hV' hW' hX' hear
  change ∀ i < n + 1, f i = if i + 1 < n + 1 then 2 ^ i * A else - (N - B)/2 at hU
  change ∀ i < n + 1, f (n + 1 + i) = if i + 1 < n + 1 then 2 ^ i * B else - (N - L)/2 at hV
  change ∀ i < n, f (2 * (n + 1) + i) = if i + 1 < n then 2 ^ i * L else - (N - M)/2 at hW
  change ∀ i < n, f (2 * (n + 1) + n + i) = if i + 1 < n then 2 ^ i * M else - (N - A)/2 at hX
  change ∀ i < n + 1, g i = if i + 1 < n + 1 then 2 ^ i * (2 * A) else - (modulus (k + 1) - GV)/2 at hU'
  change ∀ i < n + 1, g (n + 1 + i) = if i + 1 < n + 1 then 2 ^ i * GV else - (modulus (k + 1) - GW)/2 at hV'
  change ∀ i < n, g (2 * (n + 1) + i) = if i + 1 < n then 2 ^ i * GW else - (modulus (k + 1) - GX)/2 at hW'
  change ∀ i < n, g (2 * (n + 1) + n + i) = if i + 1 < n then 2 ^ i * GX else - (modulus (k + 1) - A)/2 at hX'
  change g k = A at hear
  let U := List.range' 1 (n - 1)
  let V := List.range' (n + 2) (n - 1)
  let W := List.range' (2 * n + 2) (n - 1)
  let X := List.range' (3 * n + 2) (n - 1)
  let u := n
  let v := 2 * n + 1
  let w := 3 * n + 1
  let x := 4 * n + 1
  have posU (i : ℕ) (hi : i < n - 1) : f (1 + i) = 2 ^ i * (2 * A) ∧ g (1 + i) = 2 ^ i * (4 * A) := by
    rw [show 1 + i = i + 1 by omega,hU (i + 1) (by omega),hU' (i + 1) (by omega),ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    constructor <;> ring
  have posV (i : ℕ) (hi : i < n - 1) : f (n + 2 + i) = 2 ^ i * (2 * B) ∧ g (n + 2 + i) = 2 ^ i * (2 * GV) := by
    rw [show n + 2 + i = n + 1 + (i + 1) by omega,hV (i + 1) (by omega),hV' (i + 1) (by omega),ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    constructor <;> ring
  have posW (i : ℕ) (hi : i < n - 1) : f (2 * n + 2 + i) = 2 ^ i * L ∧ g (2 * n + 2 + i) = 2 ^ i * GW := by
    rw [show 2 * n + 2 + i = 2 * (n + 1) + i by omega]
    exact ⟨(hW i (by omega)).trans (ite_eq_left (by omega)),(hW' i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i < n - 1) : f (3 * n + 2 + i) = 2 ^ i * M ∧ g (3 * n + 2 + i) = 2 ^ i * GX := by
    rw [show 3 * n + 2 + i = 2 * (n + 1) + n + i by omega]
    exact ⟨(hX i (by omega)).trans (ite_eq_left (by omega)),(hX' i (by omega)).trans (ite_eq_left (by omega))⟩
  have h0 : f 0 = A ∧ g 0 = 2 * A := by
    simpa only [pow_zero,one_mul,ite_eq_left (by omega : 0 + 1 < n + 1)] using And.intro (hU 0 (by omega)) (hU' 0 (by omega))
  have h1 : f (n + 1) = B ∧ g (n + 1) = GV := by
    simpa only [Nat.add_zero,pow_zero,one_mul,ite_eq_left (by omega : 0 + 1 < n + 1)] using And.intro (hV 0 (by omega)) (hV' 0 (by omega))
  have negU : f u = -(N - B)/2 ∧ g u = -(modulus (k + 1) - GV)/2 := by
    simpa only [u,ite_eq_right (by omega : ¬n + 1 < n + 1)] using And.intro (hU n (by omega)) (hU' n (by omega))
  have negV : f v = -(N - L)/2 ∧ g v = -(modulus (k + 1) - GW)/2 := by
    simpa only [show n + 1 + n = v by dsimp [v]; omega,ite_eq_right (by omega : ¬n + 1 < n + 1)] using And.intro (hV n (by omega)) (hV' n (by omega))
  have negW : f w = -(N - M)/2 ∧ g w = -(modulus (k + 1) - GX)/2 := by
    simpa only [show 2 * (n + 1) + (n - 1) = w by dsimp [w]; omega,ite_eq_right (by omega : ¬n - 1 + 1 < n)] using And.intro (hW (n - 1) (by omega)) (hW' (n - 1) (by omega))
  have negX : f x = -(N - A)/2 ∧ g x = -(modulus (k + 1) - A)/2 := by
    simpa only [show 2 * (n + 1) + n + (n - 1) = x by dsimp [x]; omega,ite_eq_right (by omega : ¬n - 1 + 1 < n)] using And.intro (hX (n - 1) (by omega)) (hX' (n - 1) (by omega))
  have sumU : (U.map f).sum = (z - 2) * A ∧ (U.map g).sum = (z - 2) * (2 * A) := by
    have a := ladder_sum f 1 (n - 1) (2 * A) (fun i hi => (posU i hi).1)
    have b := ladder_sum g 1 (n - 1) (4 * A) (fun i hi => (posU i hi).2)
    change (U.map f).sum = (q - 1) * (2 * A) at a
    change (U.map g).sum = (q - 1) * (4 * A) at b
    rw [a,b,hzq]; constructor <;> ring
  have sumV : (V.map f).sum = (z - 2) * B ∧ (V.map g).sum = (z - 2) * GV := by
    have a := ladder_sum f (n + 2) (n - 1) (2 * B) (fun i hi => (posV i hi).1)
    have b := ladder_sum g (n + 2) (n - 1) (2 * GV) (fun i hi => (posV i hi).2)
    change (V.map f).sum = (q - 1) * (2 * B) at a
    change (V.map g).sum = (q - 1) * (2 * GV) at b
    rw [a,b,hzq]; constructor <;> ring
  have sumW : (W.map f).sum = (q - 1) * L ∧ (W.map g).sum = (q - 1) * GW :=
    ⟨ladder_sum f (2 * n + 2) (n - 1) L (fun i hi => (posW i hi).1),ladder_sum g (2 * n + 2) (n - 1) GW (fun i hi => (posW i hi).2)⟩
  have sumX : (X.map f).sum = (q - 1) * M ∧ (X.map g).sum = (q - 1) * GX :=
    ⟨ladder_sum f (3 * n + 2) (n - 1) M (fun i hi => (posX i hi).1),ladder_sum g (3 * n + 2) (n - 1) GX (fun i hi => (posX i hi).2)⟩
  have hzpos : 0 ≤ z := by omega
  have coeff : 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ M ∧ 0 ≤ GV ∧ 0 ≤ GW ∧ 0 ≤ GX := by
    dsimp [A,B,L,M,GV,GW,GX]
    ring_nf
    refine ⟨by positivity,by positivity,by positivity,by positivity,by positivity,by positivity,?_⟩
    positivity
  obtain ⟨hAp,hBp,hLp,hMp,hGVp,hGWp,hGXp⟩ := coeff
  have up : ∀ i∈U, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]; rw [(posU j hj).1,(posU j hj).2]; constructor <;> positivity
  have vp : ∀ i∈V, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]; rw [(posV j hj).1,(posV j hj).2]; constructor <;> positivity
  have wp : ∀ i∈W, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]; rw [(posW j hj).1,(posW j hj).2]; constructor <;> positivity
  have xp : ∀ i∈X, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]; rw [(posX j hj).1,(posX j hj).2]; constructor <;> positivity
  let F1 := [0] ++ X
  let F2 := [n + 1] ++ W
  let word := F1 ++ [x] ++ F2 ++ [w] ++ U ++ [u] ++ V ++ [v]
  have hp : word.Perm (List.range k) := by simpa only [word,F1,F2,U,V,W,X,u,v,w,x,k,List.append_assoc] using inventory n hn
  have hold : Gates (N/2) (F1.map f).sum (f x) (F2.map f).sum (f w) (U.map f).sum (f u) (V.map f).sum (f v) := by
    simp only [F1,F2,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,h0.1,h1.1,sumU.1,sumV.1,sumW.1,sumX.1,negU.1,negV.1,negW.1,negX.1]
    simpa only [←hzq,←hN,A,B,L,M] using (arithmetic q hq).1
  have hnew : Gates N (([k] ++ F1).map g).sum (g x) (F2.map g).sum (g w) (U.map g).sum (g u) (V.map g).sum (g v) := by
    simp only [F1,F2,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,hear,h0.2,h1.2,sumU.2,sumV.2,sumW.2,sumX.2,negU.2,negV.2,negW.2,negX.2,hNN]
    have he : A + (2 * A + (q - 1) * GX) = 3 * A + (q - 1) * GX := by ring
    rw [he]
    simpa only [←hzq,←hN,A,B,L,M,GV,GW,GX] using (arithmetic q hq).2
  have p1 : ∀ i∈F1, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · rw [List.mem_singleton.mp hi,h0.1,h0.2]; constructor <;> positivity
    · exact xp i hi
  have p2 : ∀ i∈F2, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · rw [List.mem_singleton.mp hi,h1.1,h1.2]; exact ⟨hBp,hGVp⟩
    · exact wp i hi
  have oldstrip : InStrip f (N/2) 0 word :=
    four_strip f (N/2) F1 F2 U V x w u v (fun i hi => (p1 i hi).1)
      (fun i hi => (p2 i hi).1) (fun i hi => (up i hi).1) (fun i hi => (vp i hi).1) hold
  have newstrip : InStrip g N 0 (k::word) := by
    simpa only [word,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
      four_strip g N ([k] ++ F1) F2 U V x w u v
        (by intro i hi; rcases List.mem_append.mp hi with hi|hi
            · rw [List.mem_singleton.mp hi,hear]; exact hAp
            · exact (p1 i hi).2)
        (fun i hi => (p2 i hi).2) (fun i hi => (up i hi).2) (fun i hi => (vp i hi).2) hnew
  have hp' : (k::word).Perm (List.range (k + 1)) := by
    rw [List.range_succ]
    exact (List.perm_append_comm : ([k] ++ word).Perm (word ++ [k])).trans (hp.append_right [k])
  have hz : ((List.range k).map f).sum = 0 := by
    simpa only [f,N,←ht] using ThreeNegativeEqualOuterSourceBridge.source_zero k t (by dsimp [k]; omega)
  have hz' : ((List.range (k + 1)).map g).sum = 0 := by
    have he : ((2 * t : ℕ) : ℤ) = 2 * A := by push_cast; rw [ht]
    simpa only [g,←he] using ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * t) (by dsimp [k]; omega)
  refine ⟨word.map (label k (by dsimp [k]; omega)),?_,?_⟩
  · exact lift_order k t (by dsimp [k]; omega) word hp (by simpa only [f,N,←ht] using oldstrip) (by simpa only [f,N,←ht] using hz)
  · rw [show word = List.nil ++ word from rfl,marked_word k 0 (by dsimp [k]; omega) [] word rfl (by simpa using hp)]
    have he : ((2 * t : ℕ) : ℤ) = 2 * A := by push_cast; rw [ht]
    exact lift_order (k + 1) (2 * t) (by dsimp [k]; omega) (k::word) hp'
      (by have hh : modulus (k + 1)/2 = N := by omega
          simpa only [g,he,hh] using newstrip)
      (by simpa only [g,he] using hz')

/-- All physical labels in the branch s=r+1 admit the same old/new order,
including the boundary (r,s) = (2,3). -/
private theorem actualSource_four_negative_adjacent_reverse_joint_lift (r s : ℕ)
    (hr : 2 ≤ r) (hs : s = r + 1) :
    ∃ sigma : List (Fin (2 * r + 2 * s)),
      OriginalOrder (2 * r + 2 * s) (1 + 2 ^ r + 2 ^ (2 * r) + 2 ^ (2 * r + s)) sigma ∧
      OriginalOrder (2 * r + 2 * s + 1) (2 * (1 + 2 ^ r + 2 ^ (2 * r) + 2 ^ (2 * r + s)))
        (earWord (2 * r + 2 * s) sigma 0) := by
  subst s
  by_cases h : r = 2
  · subst r
    refine ⟨[0,8,9,3,1,7,6,2,4,5],⟨by decide,by decide,?_⟩,⟨by decide,by decide,?_⟩⟩
    all_goals
      intro h
      by_cases hh : h ≤ 11
      · interval_cases h <;> norm_num [earWord,actualSource,centered,modulus]
      · rw [List.take_of_length_le (by simp [earWord]; omega)]
        norm_num [earWord,actualSource,centered,modulus]
  · exact symbolic r (by omega)

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentReverse
