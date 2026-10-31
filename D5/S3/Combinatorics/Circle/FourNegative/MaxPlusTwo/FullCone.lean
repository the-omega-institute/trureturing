/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete physical max-plus-two cone with all chamber masks and literal first ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Peak
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone

open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ old enlarged charge shadow natural_lift_strips natural_lift_totals
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

private theorem strong_single
    (f q : ℕ → ℤ) (B h Q : ℤ) (i : ℕ)
    (h0 : 0 ≤ h) (hB : h ≤ B-1) (hQ : 0 ≤ Q) (hQB : h+Q ≤ B)
    (hi0 : 0 ≤ f i) (hqi : 0 ≤ q i) (hzi : 0 ≤ f i-q i)
    (h1 : 0 ≤ h+f i) (h1B : h+f i ≤ B-1)
    (h1Q : 0 ≤ Q-q i) (h1QB : h+f i+Q-q i ≤ B) :
    Strong f q B h Q [i] := by
  simp only [Strong]
  exact ⟨h0,hB,by omega,hQB,h1,h1B,by omega,by linarith [h1QB]⟩

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
  exact hfull'.trans (List.Perm.of_eq (chamberLabels_full len off))

private theorem masked_inventory
    (a b c d u1 u2 u3 v0 v2 v3 w : ℕ)
    (hfullU : u1 < 2^(d-1)) (hfullV : v0 ||| v2 < 2^(c-1))
    (hfullW : w < 2^(b-1))
    (hU12 : ∀ e < d-1, u2.testBit e = true → u1.testBit e = true)
    (hU23 : ∀ e < d-1, u3.testBit e = true → u2.testBit e = true)
    (hV01 : ∀ e < c-1, (v0 ||| v2).testBit e = true →
      (2^(c-1)-1).testBit e = true)
    (hV12 : ∀ e < c-1, v2.testBit e = true → (v0 ||| v2).testBit e = true)
    (hV23 : ∀ e < c-1, v3.testBit e = true → v2.testBit e = true)
    (hVxor : (v0 ||| v2) ^^^ v2 = v0)
    (hW : w < 2^(b-1)) :
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
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one, he])
  have hx := chamberLabels_full (a-1) (d+c+b)
  dsimp [chamberMaskedWord, U, V, W, X, uf, vf, wf, xf]
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
  apply Multiset.coe_eq_coe.mp
  calc
    (↑(U1 ++ V1 ++ [d-1] ++ U2 ++ V2 ++ [d+c-1] ++
      U3 ++ V3 ++ W1 ++ [d+c+b-1] ++ U4 ++ V4 ++ W2 ++ X1 ++
      [d+c+b+a-1]) : Multiset ℕ) =
      (↑(U1 ++ U2 ++ U3 ++ U4) : Multiset ℕ) +
        ↑(V1 ++ V2 ++ V3 ++ V4) + ↑(W1 ++ W2) + ↑X1 +
        ({d-1} : Multiset ℕ) + {d+c-1} + {d+c+b-1} + {d+c+b+a-1} := by
          simp only [← Multiset.coe_add]
          ac_rfl

private theorem base_charge_shadow_values (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 3 ≤ d) :
    let f := old a b c d
    let q := charge a b c d
    let z := fun i => f i-q i
    (∀ i<d, q i = (if i+1<d then 0 else 1) ∧
      z i = (if i+1<d then 2^i*seedZ a b c else -(2^(d-1)*2^a*2^b*2^c)+2^(d-1)*(1+2^a+2^a*2^b))) ∧
    (∀ i<c, q (d+i) = (if i+1<c then 2^i else 2^(c-1)+1) ∧
      z (d+i) = (if i+1<c then 2^i*(2*(2^(d-1)*(1+2^a+2^a*2^b)) )
        else -(2^(d-1)*2^a*2^b*2^c)+2^(d-1)*(2^a+1)*2^c)) := by
  obtain ⟨hu,hv,hw,hx,hfresh⟩ :=
    source_shadow_charge a b c d ha hb hc hd
  dsimp only
  dsimp [old, charge, seedZ, modZ]
  change (∀ i<d, _ ∧ _) ∧ (∀ i<c, _ ∧ _)
  constructor
  · intro i hi
    have h := hu i hi
    dsimp only at h
    constructor
    · exact h.1
    · have hz := h.2
      dsimp [shadow] at hz
      linarith
  · intro i hi
    have h := hv i hi
    dsimp only at h
    constructor
    · exact h.1
    · have hz := h.2
      dsimp [shadow] at hz
      linarith
    _ = (↑(List.range' 0 (d-1)) : Multiset ℕ) +
        ↑(List.range' d (c-1)) + ↑(List.range' (d+c) (b-1)) +
        ↑(List.range' (d+c+b) (a-1)) +
        ({d-1} : Multiset ℕ) + {d+c-1} + {d+c+b-1} + {d+c+b+a-1} := by
          rw [Multiset.coe_eq_coe.mpr hUeq, Multiset.coe_eq_coe.mpr hVeq,
            Multiset.coe_eq_coe.mpr hWeq, hXeq]
    _ = (List.range (a+b+c+d) : Multiset ℕ) := by
          simp only [List.range'_eq_map]
          rw [← List.range_succ]
          simp only [Nat.succ_eq_add_one]
          ac_rfl

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
