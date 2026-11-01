/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ActualBlocks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ActualBlocks
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual physical mask inventories, source masses and coupled prefix seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Physical occurrence inventories, exact chain masses and reserve-based prefix bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers

open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private mass_margin ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge two_power_pred from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ modZ old enlarged charge shadow natural_lift_strips natural_lift_totals
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong strong_strips strong_append strong_of_shadow from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem power_two_ge (n : ℕ) (hn : 2 ≤ n) : (4 : ℤ) ≤ 2^n := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn
  norm_num at h ⊢
  omega

private theorem list_sum_sub (xs : List ℕ) (f q : ℕ → ℤ) :
    (xs.map (fun i => f i-q i)).sum = (xs.map f).sum-(xs.map q).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private theorem strong_block
    (f q : ℕ → ℤ) (B h Q : ℤ) (xs : List ℕ)
    (hf : ∀ i ∈ xs, 0 ≤ f i)
    (hq : ∀ i ∈ xs, 0 ≤ q i)
    (hz : ∀ i ∈ xs, 0 ≤ f i-q i)
    (h0 : 0 ≤ h) (hQ : 1 ≤ Q)
    (hendh : h + (xs.map f).sum ≤ B)
    (hendr : h + Q + (xs.map (fun i => f i-q i)).sum ≤ B)
    (hQend : 1 ≤ Q-(xs.map q).sum) :
    Strong f q B h Q xs := by
  induction xs generalizing h Q with
  | nil =>
    simp only [List.map_nil, List.sum_nil, sub_zero, add_zero] at hendh hendr hQend ⊢
    exact strong_of_shadow B h Q h0 hQ hendr
  | cons i xs ih =>
    have hfi := hf i (by simp)
    have hqi := hq i (by simp)
    have hzi := hz i (by simp)
    have hft : ∀ j ∈ xs, 0 ≤ f j := by intro j hj; exact hf j (by simp [hj])
    have hqt : ∀ j ∈ xs, 0 ≤ q j := by intro j hj; exact hq j (by simp [hj])
    have hzt : ∀ j ∈ xs, 0 ≤ f j-q j := by intro j hj; exact hz j (by simp [hj])
    have hsF : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
      intro v hv
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      exact hft j hj)
    have hsQ : 0 ≤ (xs.map q).sum := List.sum_nonneg (by
      intro v hv
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      exact hqt j hj)
    have hsZ : 0 ≤ (xs.map (fun j => f j-q j)).sum := List.sum_nonneg (by
      intro v hv
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      exact hzt j hj)
    simp only [List.map_cons, List.sum_cons] at hendh hendr hQend
    have hQ' : 1 ≤ Q-q i := by omega
    have hstate : 0 ≤ h ∧ h ≤ B-1 ∧ 0 ≤ h+Q ∧ h+Q ≤ B := by
      have : h+Q ≤ B := by linarith
      exact strong_of_shadow B h Q h0 hQ this
    refine ⟨hstate.1,hstate.2.1,hstate.2.2.1,hstate.2.2.2,?_⟩
    apply ih (h+f i) (Q-q i) hft hqt hzt
    · linarith
    · linarith
    · linarith
    · linarith [hendr]
    · linarith

private theorem labels_v_partition (len off full v0 v2 v3 : ℕ)
    (h01 : ∀ e < len, (v0 ||| v2).testBit e = true → full.testBit e = true)
    (h12 : ∀ e < len, v2.testBit e = true → (v0 ||| v2).testBit e = true)
    (h23 : ∀ e < len, v3.testBit e = true → v2.testBit e = true)
    (hxor : (v0 ||| v2) ^^^ v2 = v0)
    (hfull : full = 2^len-1) :
    (chamberLabels len off v0 ++ chamberLabels len off (full ^^^ (v0 ||| v2)) ++
      chamberLabels len off (v2 ^^^ v3) ++ chamberLabels len off v3).Perm (List.range' off len) := by
  have hA := chamberLabels_split len off full (v0 ||| v2)
    (by intro e he _; simpa [hfull, Nat.testBit_two_pow_sub_one, he])
  have hB := chamberLabels_split len off (v0 ||| v2) v2 h12
  have hC := chamberLabels_split len off v2 v3 h23
  have hA' : (chamberLabels len off (full ^^^ (v0 ||| v2)) ++
      chamberLabels len off (v0 ||| v2)).Perm (chamberLabels len off full) := by
    exact hA
  have hB' : (chamberLabels len off v0 ++ chamberLabels len off v2).Perm
      (chamberLabels len off (v0 ||| v2)) := by
    simpa [hxor] using hB
  have hC' : (chamberLabels len off (v2 ^^^ v3) ++ chamberLabels len off v3).Perm
      (chamberLabels len off v2) := hC
  have htail : (chamberLabels len off v0 ++ chamberLabels len off (v2 ^^^ v3) ++
      chamberLabels len off v3).Perm (chamberLabels len off (v0 ||| v2)) := by
    have hp := (hC'.append_left (chamberLabels len off v0)).trans hB'
    simpa [List.append_assoc] using hp
  have hall := (htail.append_left (chamberLabels len off (full ^^^ (v0 ||| v2)))).trans hA'
  have horder :
      (chamberLabels len off v0 ++ chamberLabels len off (full ^^^ (v0 ||| v2)) ++
        chamberLabels len off (v2 ^^^ v3) ++ chamberLabels len off v3).Perm
      (chamberLabels len off (full ^^^ (v0 ||| v2)) ++
        (chamberLabels len off v0 ++ chamberLabels len off (v2 ^^^ v3) ++
          chamberLabels len off v3)) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hfull' := horder.trans hall
  rw [hfull] at hfull'
  simpa only [hfull] using
    hfull'.trans (List.Perm.of_eq (chamberLabels_full len off))

set_option maxHeartbeats 1000000 in
-- The physical partition rearranges four binary chains and their negative endpoints.
private theorem masked_inventory
    (a b c d u1 u2 u3 v0 v2 v3 w : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hU12 : ∀ e < d-1, u2.testBit e = true → u1.testBit e = true)
    (hU23 : ∀ e < d-1, u3.testBit e = true → u2.testBit e = true)
    (hV01 : ∀ e < c-1, (v0 ||| v2).testBit e = true →
      (2^(c-1)-1).testBit e = true)
    (hV12 : ∀ e < c-1, v2.testBit e = true → (v0 ||| v2).testBit e = true)
    (hV23 : ∀ e < c-1, v3.testBit e = true → v2.testBit e = true)
    (hVxor : (v0 ||| v2) ^^^ v2 = v0) :
    (chamberMaskedWord a b c d u1 u2 u3 v0 v2 v3 w).Perm
      (List.range (a+b+c+d)) := by
  let U := chamberLabels (d-1) 0
  let V := chamberLabels (c-1) d
  let W := chamberLabels (b-1) (d+c)
  let X := chamberLabels (a-1) (d+c+b)
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  have hu := chamberLabels_nested_four (d-1) 0 u1 u2 u3 hU12 hU23
  have hv := labels_v_partition (c-1) d vf v0 v2 v3 hV01 hV12 hV23 hVxor rfl
  have hw := chamberLabels_split (b-1) (d+c) wf w
    (by intro e he _; dsimp [wf]; simp [Nat.testBit_two_pow_sub_one, he])
  have hx := chamberLabels_full (a-1) (d+c+b)
  let U1 := chamberLabels (d-1) 0 (2^(d-1)-1 ^^^ u1)
  let U2 := chamberLabels (d-1) 0 (u1 ^^^ u2)
  let U3 := chamberLabels (d-1) 0 (u2 ^^^ u3)
  let U4 := chamberLabels (d-1) 0 u3
  let V1 := chamberLabels (c-1) d v0
  let V2 := chamberLabels (c-1) d (2^(c-1)-1 ^^^ (v0 ||| v2))
  let V3 := chamberLabels (c-1) d (v2 ^^^ v3)
  let V4 := chamberLabels (c-1) d v3
  let W1 := chamberLabels (b-1) (d+c) (2^(b-1)-1 ^^^ w)
  let W2 := chamberLabels (b-1) (d+c) w
  let X1 := chamberLabels (a-1) (d+c+b) (2^(a-1)-1)
  have hu' : (chamberLabels (d-1) 0 (2^(d-1)-1 ^^^ u1) ++
      chamberLabels (d-1) 0 (u1 ^^^ u2) ++ chamberLabels (d-1) 0 (u2 ^^^ u3) ++
      chamberLabels (d-1) 0 u3).Perm (List.range' 0 (d-1)) := hu
  have hw0 := hw.trans (List.Perm.of_eq (chamberLabels_full (b-1) (d+c)))
  have hw' : (W1 ++ W2).Perm (List.range' (d+c) (b-1)) := by
    simpa [W1,W2] using hw0
  have hUeq : (U1 ++ U2 ++ U3 ++ U4 : List ℕ).Perm
      (List.range' 0 (d-1)) := by simpa [U1,U2,U3,U4] using hu'
  have hVeq : (V1 ++ V2 ++ V3 ++ V4 : List ℕ).Perm
      (List.range' d (c-1)) := by simpa [V1,V2,V3,V4] using hv
  have hWeq : (W1 ++ W2 : List ℕ).Perm
      (List.range' (d+c) (b-1)) := by simpa [W1,W2] using hw'
  have hXeq : X1 = List.range' (d+c+b) (a-1) := by simpa [X1] using hx
  have merge (o n : ℕ) (hn : 1 ≤ n) :
      List.range' o (n-1) ++ [o+n-1] = List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega, show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hall :
      (List.range' 0 (d-1) ++ [d-1]) ++
      (List.range' d (c-1) ++ [d+c-1]) ++
      (List.range' (d+c) (b-1) ++ [d+c+b-1]) ++
      (List.range' (d+c+b) (a-1) ++ [d+c+b+a-1]) =
        List.range (a+b+c+d) := by
    have hd0 := merge 0 d hd
    simp only [Nat.zero_add] at hd0
    rw [hd0, merge d c hc,
      merge (d+c) b hb, merge (d+c+b) a ha]
    have h1 := List.range'_append_1 (s:=0) (m:=d) (n:=c)
    have h2 := List.range'_append_1 (s:=0) (m:=d+c) (n:=b)
    have h3 := List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a)
    simp only [Nat.zero_add] at h1 h2 h3
    rw [h1,h2,h3,←List.range_eq_range']
    congr 1
    omega
  change ((U1++V1)++[d-1]++(U2++V2)++[d+c-1]++
    (U3++V3++W1)++[d+c+b-1]++(U4++V4++W2++X1)++[d+c+b+a-1]).Perm _
  apply Multiset.coe_eq_coe.mp
  calc
    (↑((U1 ++ V1) ++ [d-1] ++ (U2 ++ V2) ++ [d+c-1] ++
      (U3 ++ V3 ++ W1) ++ [d+c+b-1] ++ (U4 ++ V4 ++ W2 ++ X1) ++
      [d+c+b+a-1]) : Multiset ℕ) =
      (↑(U1 ++ U2 ++ U3 ++ U4) : Multiset ℕ) +
        ↑(V1 ++ V2 ++ V3 ++ V4) + ↑(W1 ++ W2) + ↑X1 +
        ({d-1} : Multiset ℕ) + {d+c-1} + {d+c+b-1} + {d+c+b+a-1} := by
          simp only [← Multiset.coe_add]
          ac_rfl

    _ = (↑(List.range' 0 (d-1)) : Multiset ℕ) +
        ↑(List.range' d (c-1)) + ↑(List.range' (d+c) (b-1)) +
        ↑(List.range' (d+c+b) (a-1)) +
        ({d-1} : Multiset ℕ) + {d+c-1} + {d+c+b-1} + {d+c+b+a-1} := by
          rw [Multiset.coe_eq_coe.mpr hUeq, Multiset.coe_eq_coe.mpr hVeq,
            Multiset.coe_eq_coe.mpr hWeq, hXeq]
    _ = (List.range (a+b+c+d) : Multiset ℕ) := by
          rw [←hall]
          simp only [←Multiset.coe_add,Multiset.coe_singleton]
          ac_rfl


/-- Split permutations compute weighted masses without arithmetic XOR identities. -/
private theorem masked_weighted_masses
    (a b c d u1 u2 u3 v0 v2 v3 w : ℕ) (z : ℕ → ℤ)
    (A Vbase Wbase Ut Vt Wt Xt : ℤ)
    (hu1 : u1 < 2^(d-1)) (hu2 : u2 < 2^(d-1)) (hu3 : u3 < 2^(d-1))
    (hv0 : v0 < 2^(c-1)) (hv2 : v2 < 2^(c-1)) (hv3 : v3 < 2^(c-1))
    (hw : w < 2^(b-1))
    (hU12 : ∀ e < d-1, u2.testBit e = true → u1.testBit e = true)
    (hU23 : ∀ e < d-1, u3.testBit e = true → u2.testBit e = true)
    (hV23 : ∀ e < c-1, v3.testBit e = true → v2.testBit e = true)
    (hVxor : (v0 ||| v2) ^^^ v2 = v0)
    (hzU : ∀ e < d-1, z (0+e)=2^e*A)
    (hzV : ∀ e < c-1, z (d+e)=2^e*(Vbase))
    (hzW : ∀ e < b-1, z (d+c+e)=2^e*(Wbase))
    (hUt : ((chamberLabels (d-1) 0 (2^(d-1)-1)).map z).sum=Ut)
    (hVt : ((chamberLabels (c-1) d (2^(c-1)-1)).map z).sum=Vt)
    (hWt : ((chamberLabels (b-1) (d+c) (2^(b-1)-1)).map z).sum=Wt)
    (hXt : ((chamberLabels (a-1) (d+c+b) (2^(a-1)-1)).map z).sum=Xt) :
    let P := maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
    let S1 := A*u1-Vbase*v0
    let S2 := A*u2+Vbase*v2
    let S3 := A*u3+Vbase*v3+Wbase*w
    (P.first.map z).sum=Ut-S1 ∧
    (P.second.map z).sum=Vt+S1-S2 ∧
    (P.third.map z).sum=Wt+S2-S3 ∧
    (P.fourth.map z).sum=Xt+S3 := by
  let U := chamberLabels (d-1) 0
  let V := chamberLabels (c-1) d
  let W := chamberLabels (b-1) (d+c)
  let X := chamberLabels (a-1) (d+c+b)
  let uf := 2^(d-1)-1
  let vf := 2^(c-1)-1
  let wf := 2^(b-1)-1
  let xf := 2^(a-1)-1
  have su1 := chamberLabels_sum (d-1) 0 u1 hu1 z A hzU
  have su2 := chamberLabels_sum (d-1) 0 u2 hu2 z A hzU
  have su3 := chamberLabels_sum (d-1) 0 u3 hu3 z A hzU
  have sv0 := chamberLabels_sum (c-1) d v0 hv0 z (Vbase) hzV
  have sv2 := chamberLabels_sum (c-1) d v2 hv2 z (Vbase) hzV
  have sv3 := chamberLabels_sum (c-1) d v3 hv3 z (Vbase) hzV
  have sw := chamberLabels_sum (b-1) (d+c) w hw z (Wbase) hzW
  have split_mass (len off outer inner : ℕ)
      (hsub : ∀ e<len, inner.testBit e=true → outer.testBit e=true) :
      ((chamberLabels len off (outer ^^^ inner)).map z).sum +
        ((chamberLabels len off inner).map z).sum =
        ((chamberLabels len off outer).map z).sum := by
    have h := ((chamberLabels_split len off outer inner hsub).map z).sum_eq
    simpa only [List.map_append,List.sum_append] using h
  have huf := split_mass (d-1) 0 uf u1
    (by intro e he _; simp [uf,Nat.testBit_two_pow_sub_one,he])
  have hu12 := split_mass (d-1) 0 u1 u2 hU12
  have hu23 := split_mass (d-1) 0 u2 u3 hU23
  have hvf := split_mass (c-1) d vf (v0 ||| v2)
    (by intro e he _; simp [vf,Nat.testBit_two_pow_sub_one,he])
  have hv02 := split_mass (c-1) d (v0 ||| v2) v2
    (by intro e _ he; simp [Nat.testBit_or,he])
  rw [hVxor] at hv02
  have hv23 := split_mass (c-1) d v2 v3 hV23
  have hwf := split_mass (b-1) (d+c) wf w
    (by intro e he _; simp [wf,Nat.testBit_two_pow_sub_one,he])
  change ((U (uf ^^^ u1)++V v0).map z).sum = _ ∧
    ((U (u1 ^^^ u2)++V (vf ^^^ (v0 ||| v2))).map z).sum = _ ∧
    ((U (u2 ^^^ u3)++V (v2 ^^^ v3)++W (wf ^^^ w)).map z).sum = _ ∧
    ((U u3++V v3++W w++X xf).map z).sum = _
  simp only [List.map_append,List.sum_append]
  dsimp only [U,V,W,X,uf,vf,wf,xf] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [su1,su2,su3,sv0,sv2,sv3,sw,
    hUt,hVt,hWt,hXt,huf,hu12,hu23,hvf,hv02,hv23,hwf]

private theorem actual_word_totals (a b c d : ℕ) (xs : List ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 3 ≤ d)
    (hx : xs.Perm (List.range (a+b+c+d))) :
    (xs.map (old a b c d)).sum = 0 ∧
      (xs.map (charge a b c d)).sum = seedZ a b c := by
  let k := a+b+c+d
  let seed : ℕ := 1+2^a+2^(a+b)+2^(a+b+c)
  have hseed : (seed : ℤ) = seedZ a b c := by
    simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [seedZ]
    simp only [pow_add]
    ring
  have hmod : modulus k = modZ a b c d := by
    dsimp [modulus,modZ,k]
    simp only [pow_add]
  have hmod' : modulus (k+1) = 2*modZ a b c d+1 := by
    dsimp [modulus]
    rw [pow_succ]
    have hm : (2:ℤ)^k=modZ a b c d+1 := by
      have := hmod
      dsimp [modulus] at this
      linarith
    rw [hm]
    ring
  have hf : ((List.range k).map (old a b c d)).sum = 0 := by
    unfold old
    simpa only [hmod,hseed] using
      ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k]; omega)
  have hg : ((List.range (k+1)).map (enlarged a b c d)).sum = 0 := by
    unfold enlarged
    simpa only [hmod',Nat.cast_mul,Nat.cast_ofNat,hseed] using
      ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed)
        (by dsimp [k]; omega)
  have hear := (source_shadow_charge a b c d ha hb hc hd).2.2.2.2
  change enlarged a b c d (d+c+b+a) = seedZ a b c at hear
  have hk : d+c+b+a=k := by dsimp [k]; omega
  rw [hk] at hear
  rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,
    List.sum_singleton,hear] at hg
  have hq : ((List.range k).map (charge a b c d)).sum = seedZ a b c := by
    unfold charge
    rw [list_sum_sub, List.sum_map_mul_left, hf]
    linarith
  exact ⟨((hx.map (old a b c d)).sum_eq).trans hf,
    ((hx.map (charge a b c d)).sum_eq).trans hq⟩


/-- Complete positive-chain masses are summed from the existing actual centered source. -/
private theorem actual_chain_masses (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d) :
    let R : ℤ:=2^a
    let T : ℤ:=2^b
    let Z : ℤ:=2^c
    let H : ℤ:=2^(d-1)
    let C:=1+R+R*T
    let A:=R*T*Z+C
    let B:=H*R*T*Z
    let e1:=H*C
    let e2:=H*(R+1)*Z
    let e3:=H*T*Z
    let z:=shadow a b c d
    ((chamberLabels (d-1) 0 (2^(d-1)-1)).map z).sum=B+e1-A ∧
    ((chamberLabels (c-1) d (2^(c-1)-1)).map z).sum=B+e2-2*e1 ∧
    ((chamberLabels (b-1) (d+c) (2^(b-1)-1)).map z).sum=B+e3-2*e2 ∧
    ((chamberLabels (a-1) (d+c+b) (2^(a-1)-1)).map z).sum=B-2*e3 := by
  let R : ℤ:=2^a
  let T : ℤ:=2^b
  let Z : ℤ:=2^c
  let H : ℤ:=2^(d-1)
  let C:=1+R+R*T
  let A:=R*T*Z+C
  let B:=H*R*T*Z
  let e1:=H*C
  let e2:=H*(R+1)*Z
  let e3:=H*T*Z
  obtain ⟨u,v,w,x,_⟩:=source_shadow_charge a b c d ha hb hc hd
  dsimp only at u v w x
  have hzU (e : ℕ) (he : e<d-1) : shadow a b c d (0+e)=2^e*A := by
    have h:=(u e (by omega)).2
    change shadow a b c d e = if e+1<d then 2^e*A else -B+e1 at h
    simpa only [if_pos (show e+1<d by omega),Nat.zero_add] using h
  have hzV (e : ℕ) (he : e<c-1) : shadow a b c d (d+e)=2^e*(2*e1) := by
    have h:=(v e (by omega)).2
    change shadow a b c d (d+e) = if e+1<c then 2^e*(2*e1) else -B+e2 at h
    simpa only [if_pos (show e+1<c by omega)] using h
  have hzW (e : ℕ) (he : e<b-1) : shadow a b c d (d+c+e)=2^e*(2*e2) := by
    have h:=(w e (by omega)).2
    change shadow a b c d (d+c+e) = if e+1<b then 2^e*(2*e2) else -B+e3 at h
    simpa only [if_pos (show e+1<b by omega)] using h
  have hzX (e : ℕ) (he : e<a-1) : shadow a b c d (d+c+b+e)=2^e*(2*e3) := by
    have h:=(x e (by omega)).2
    change shadow a b c d (d+c+b+e) = if e+1<a then 2^e*(2*e3) else -B at h
    simpa only [if_pos (show e+1<a by omega)] using h
  have cap (n : ℕ) : 2^n-1<2^n := Nat.sub_lt (Nat.two_pow_pos n) (by decide)
  have castfull (n : ℕ) : ((2^n-1:ℕ):ℤ)=(2:ℤ)^n-1 := by
    rw [Nat.cast_sub (show 1≤2^n from Nat.one_le_two_pow)]
    norm_cast
  have hR : R=2*(2:ℤ)^(a-1) := two_power_pred a (by omega)
  have hT : T=2*(2:ℤ)^(b-1) := two_power_pred b (by omega)
  have hZ : Z=2*(2:ℤ)^(c-1) := two_power_pred c (by omega)
  change _ = B+e1-A ∧ _ = B+e2-2*e1 ∧ _ = B+e3-2*e2 ∧ _ = B-2*e3
  refine ⟨?_,?_,?_,?_⟩
  · rw [chamberLabels_sum (d-1) 0 _ (cap _) _ A hzU,castfull]
    change (H-1)*A=B+e1-A
    dsimp only [A,B,e1,C]
    ring
  · rw [chamberLabels_sum (c-1) d _ (cap _) _ (2*e1) hzV,castfull]
    dsimp only [B,e1,e2]
    rw [hZ]
    dsimp only [C]
    ring
  · rw [chamberLabels_sum (b-1) (d+c) _ (cap _) _ (2*e2) hzW,castfull]
    dsimp only [B,e2,e3]
    rw [hT]
    ring
  · rw [chamberLabels_sum (a-1) (d+c+b) _ (cap _) _ (2*e3) hzX,castfull]
    dsimp only [B,e3]
    rw [hR]
    ring

private theorem block_from_r
    (f q : ℕ → ℤ) (B h Q : ℤ) (xs : List ℕ)
    (hf : ∀ i ∈ xs, 0 ≤ f i)
    (hq : ∀ i ∈ xs, 0 ≤ q i)
    (hz : ∀ i ∈ xs, 0 ≤ f i-q i)
    (h0 : 0 ≤ h) (hQ : 1 ≤ Q)
    (hendr : h + Q + (xs.map (fun i => f i-q i)).sum ≤ B)
    (hQend : 1 ≤ Q-(xs.map q).sum) :
    Strong f q B h Q xs := by
  apply strong_block f q B h Q xs hf hq hz h0 hQ
  · have hzsum := list_sum_sub xs f q
    rw [hzsum] at hendr
    linarith
  · exact hendr
  · exact hQend

private theorem strong_chunk
    (f q : ℕ → ℤ) (B h Q : ℤ) (xs : List ℕ) (n : ℕ)
    (hB : 1 ≤ B)
    (hf : ∀ i ∈ xs, 0 ≤ f i)
    (hq : ∀ i ∈ xs, 0 ≤ q i)
    (hz : ∀ i ∈ xs, 0 ≤ f i-q i)
    (h0 : 0 ≤ h) (hQ : 1 ≤ Q) (hqn : 1 ≤ q n)
    (hn : f n-q n ≤ 0)
    (hpeak : h+Q+(xs.map (fun i => f i-q i)).sum ≤ B)
    (hpost : 0 ≤ h+(xs.map f).sum+f n)
    (hproper : 1 ≤ Q-(xs.map q).sum-q n ∨
      h+(xs.map f).sum+f n=0 ∧ Q-(xs.map q).sum-q n=0) :
    Strong f q B h Q (xs++[n]) := by
  have hmass := list_sum_sub xs f q
  have hQafter : 0 ≤ Q-(xs.map q).sum-q n := by
    rcases hproper with h | h <;> omega
  have hQbefore : 1 ≤ Q-(xs.map q).sum := by omega
  have hblock := block_from_r f q B h Q xs hf hq hz h0 hQ hpeak hQbefore
  have hsum : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    exact hf i hi)
  have hpre := strong_of_shadow B (h+(xs.map f).sum)
    (Q-(xs.map q).sum) (by linarith) hQbefore (by linarith)
  have hpostpeak : h+(xs.map f).sum+f n+(Q-(xs.map q).sum-q n) ≤ B := by
    linarith
  have hpostupper : h+(xs.map f).sum+f n ≤ B-1 := by
    rcases hproper with h | h
    · linarith
    · omega
  apply strong_append f q B h Q xs [n] hblock
  simp only [Strong]
  exact ⟨hpre.1,hpre.2.1,hpre.2.2.1,hpre.2.2.2,
    hpost,hpostupper,by linarith, hpostpeak⟩

set_option maxHeartbeats 800000 in
-- Four successive block states share the exact remaining charge and final totals.
private theorem four_reserve_strong
    (f q : ℕ → ℤ) (B A e1 e2 e3 S1 S2 S3 : ℤ)
    (P1 P2 P3 P4 : List ℕ) (n1 n2 n3 n4 : ℕ)
    (hB : 1 ≤ B) (hA : 1 ≤ A)
    (hp1 : ∀ i ∈ P1, 0 ≤ f i ∧ 0 ≤ q i ∧ 0 ≤ f i-q i)
    (hp2 : ∀ i ∈ P2, 0 ≤ f i ∧ 0 ≤ q i ∧ 0 ≤ f i-q i)
    (hp3 : ∀ i ∈ P3, 0 ≤ f i ∧ 0 ≤ q i ∧ 0 ≤ f i-q i)
    (hp4 : ∀ i ∈ P4, 0 ≤ f i ∧ 0 ≤ q i ∧ 0 ≤ f i-q i)
    (hn1 : 1 ≤ q n1) (hn2 : 1 ≤ q n2) (hn3 : 1 ≤ q n3) (hn4 : 1 ≤ q n4)
    (he1 : e1 ≤ B) (he2 : e2 ≤ B) (he3 : e3 ≤ B)
    (hz1 : f n1-q n1 = -B+e1) (hz2 : f n2-q n2 = -B+e2)
    (hz3 : f n3-q n3 = -B+e3) (hz4 : f n4-q n4 = -B)
    (hm1 : (P1.map (fun i => f i-q i)).sum = B+e1-A-S1)
    (hm2 : (P2.map (fun i => f i-q i)).sum = B+e2-2*e1+S1-S2)
    (hm3 : (P3.map (fun i => f i-q i)).sum = B+e3-2*e2+S2-S3)
    (hm4 : (P4.map (fun i => f i-q i)).sum = B-2*e3+S3)
    (hs1 : e1 ≤ S1 ∧ S1 ≤ 2*e1-(A-(P1.map q).sum-q n1))
    (hs2 : e2 ≤ S2 ∧ S2 ≤ 2*e2-(A-(P1.map q).sum-q n1-(P2.map q).sum-q n2))
    (hs3 : e3 ≤ S3 ∧ S3 ≤ 2*e3-
      (A-(P1.map q).sum-q n1-(P2.map q).sum-q n2-(P3.map q).sum-q n3))
    (hftot : ((P1++[n1]++P2++[n2]++P3++[n3]++P4++[n4]).map f).sum=0)
    (hqtot : ((P1++[n1]++P2++[n2]++P3++[n3]++P4++[n4]).map q).sum=A) :
    Strong f q B 0 A (P1++[n1]++P2++[n2]++P3++[n3]++P4++[n4]) := by
  let F1 := (P1.map f).sum
  let F2 := (P2.map f).sum
  let F3 := (P3.map f).sum
  let F4 := (P4.map f).sum
  let Q1 := (P1.map q).sum
  let Q2 := (P2.map q).sum
  let Q3 := (P3.map q).sum
  let Q4 := (P4.map q).sum
  have qnonneg (P : List ℕ) (hp : ∀ i ∈ P, 0 ≤ q i) :
      0 ≤ (P.map q).sum := List.sum_nonneg (by
    intro v hv; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv; exact hp i hi)
  have hQ1 : 0 ≤ Q1 := qnonneg P1 (fun i hi => (hp1 i hi).2.1)
  have hQ2 : 0 ≤ Q2 := qnonneg P2 (fun i hi => (hp2 i hi).2.1)
  have hQ3 : 0 ≤ Q3 := qnonneg P3 (fun i hi => (hp3 i hi).2.1)
  have hQ4 : 0 ≤ Q4 := qnonneg P4 (fun i hi => (hp4 i hi).2.1)
  have m1 := list_sum_sub P1 f q
  have m2 := list_sum_sub P2 f q
  have m3 := list_sum_sub P3 f q
  have m4 := list_sum_sub P4 f q
  change (P1.map (fun i => f i-q i)).sum = F1-Q1 at m1
  change (P2.map (fun i => f i-q i)).sum = F2-Q2 at m2
  change (P3.map (fun i => f i-q i)).sum = F3-Q3 at m3
  change (P4.map (fun i => f i-q i)).sum = F4-Q4 at m4
  simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    at hftot hqtot
  change F1+f n1+F2+f n2+F3+f n3+F4+f n4=0 at hftot
  change Q1+q n1+Q2+q n2+Q3+q n3+Q4+q n4=A at hqtot
  let H1 := F1+f n1
  let H2 := H1+F2+f n2
  let H3 := H2+F3+f n3
  let C1 := A-Q1-q n1
  let C2 := C1-Q2-q n2
  let C3 := C2-Q3-q n3
  change e1 ≤ S1 ∧ S1 ≤ 2*e1-C1 at hs1
  change e2 ≤ S2 ∧ S2 ≤ 2*e2-C2 at hs2
  change e3 ≤ S3 ∧ S3 ≤ 2*e3-C3 at hs3
  have r1 : H1+C1=2*e1-S1 := by dsimp [H1,C1]; linarith only [m1,hm1,hz1]
  have r2 : H2+C2=2*e2-S2 := by dsimp [H2,C2]; linarith only [r1,m2,hm2,hz2]
  have r3 : H3+C3=2*e3-S3 := by dsimp [H3,C3]; linarith only [r2,m3,hm3,hz3]
  have c1 : 1 ≤ C1 ∧ C1 ≤ A := by dsimp [C1]; constructor <;> linarith
  have c2 : 1 ≤ C2 ∧ C2 ≤ A := by dsimp [C2,C1]; constructor <;> linarith
  have c3 : 1 ≤ C3 ∧ C3 ≤ A := by dsimp [C3,C2,C1]; constructor <;> linarith
  have h1 : 0 ≤ H1 := by linarith only [r1,hs1.2]
  have h2 : 0 ≤ H2 := by linarith only [r2,hs2.2]
  have h3 : 0 ≤ H3 := by linarith only [r3,hs3.2]
  have h4 : H3+F4+f n4=0 := by dsimp [H3,H2,H1]; exact hftot
  have c4 : C3-Q4-q n4=0 := by dsimp [C3,C2,C1]; linarith only [hqtot]
  have s1 : Strong f q B 0 A (P1++[n1]) := by
    apply strong_chunk f q B 0 A P1 n1 hB
      (fun i hi => (hp1 i hi).1) (fun i hi => (hp1 i hi).2.1)
      (fun i hi => (hp1 i hi).2.2) (by omega) hA hn1
    · linarith only [hz1,he1]
    · linarith only [hm1,hs1.1]
    · change 0 ≤ 0+F1+f n1
      dsimp [H1] at h1
      linarith only [h1]
    · exact Or.inl c1.1
  have s2 : Strong f q B H1 C1 (P2++[n2]) := by
    apply strong_chunk f q B H1 C1 P2 n2 hB
      (fun i hi => (hp2 i hi).1) (fun i hi => (hp2 i hi).2.1)
      (fun i hi => (hp2 i hi).2.2) h1 c1.1 hn2
    · linarith only [hz2,he2]
    · linarith only [r1,hm2,hs2.1]
    · exact h2
    · exact Or.inl c2.1
  have s3 : Strong f q B H2 C2 (P3++[n3]) := by
    apply strong_chunk f q B H2 C2 P3 n3 hB
      (fun i hi => (hp3 i hi).1) (fun i hi => (hp3 i hi).2.1)
      (fun i hi => (hp3 i hi).2.2) h2 c2.1 hn3
    · linarith only [hz3,he3]
    · linarith only [r2,hm3,hs3.1]
    · exact h3
    · exact Or.inl c3.1
  have s4 : Strong f q B H3 C3 (P4++[n4]) := by
    apply strong_chunk f q B H3 C3 P4 n4 hB
      (fun i hi => (hp4 i hi).1) (fun i hi => (hp4 i hi).2.1)
      (fun i hi => (hp4 i hi).2.2) h3 c3.1 hn4
    · linarith only [hz4,hB]
    · linarith only [r3,hm4]
    · change 0 ≤ H3+F4+f n4
      omega
    · exact Or.inr ⟨h4,c4⟩
  have s12 := strong_append f q B 0 A (P1++[n1]) (P2++[n2]) s1 (by
    convert s2 using 1 <;>
      simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    · dsimp [H1,F1]; ring
    · dsimp [C1,Q1]; ring)
  have s123 := strong_append f q B 0 A ((P1++[n1])++(P2++[n2])) (P3++[n3]) s12 (by
    convert s3 using 1 <;>
      simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    · dsimp [H2,H1,F1,F2]; ring
    · dsimp [C2,C1,Q1,Q2]; ring)
  have s1234 := strong_append f q B 0 A
    (((P1++[n1])++(P2++[n2]))++(P3++[n3])) (P4++[n4]) s123 (by
    convert s4 using 1 <;>
      simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    · dsimp [H3,H2,H1,F1,F2,F3]; ring
    · dsimp [C3,C2,C1,Q1,Q2,Q3]; ring)
  simpa only [List.append_assoc] using s1234




end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
