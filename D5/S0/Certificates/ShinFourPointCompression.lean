/- GID: D5/S0/Certificates/ShinFourPointCompression
   generality: I
   mirror-B: D5/B/S0/Certificates/ShinFourPointCompression
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Pointwise.Finset.Basic, mathlib/module/Mathlib.Data.Nat.BitIndices, mathlib/module/Mathlib.Data.Finset.Sort]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/ShinFourPointCompression.claim; result=D5/S0/Certificates/ShinFourPointCompression.result; claim=D5/S0/Certificates/ShinFourPointCompression.claim
   digest: A four-point integer set whose eleven-fold sumset cardinality cannot occur in diameter seventy-nine. -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

namespace D5.S0.Certificates.ShinFourPointCompression

open scoped Pointwise

/-- The affirmative answer to the unnumbered question following Corollary 10.5
and (193) of arXiv:2609.01690v1. The operation `nsmulRec` uses repeated
pointwise addition, with zero-fold sumset `{0}`. Only cardinality is preserved. -/
def claim : Prop :=
  ∀ h : ℕ, 2 ≤ h → ∀ A : Finset ℤ, A.card = 4 →
    ∃ B : Finset ℤ, B.card = 4 ∧
      B ⊆ Finset.Icc 0 (↑(Nat.choose (h+2) 2 + if h % 2 = 1 then 1 else 0)) ∧
      (nsmulRec h B).card = (nsmulRec h A).card

private def sumBits (a b c : ℕ) : ℕ → ℕ
  | 0 => 1
  | h+1 => let x := sumBits a b c h; x ||| (x <<< a) ||| (x <<< b) ||| (x <<< c)

private def countBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | w+1, n => n % 2 + countBits w (n / 2)

private def byteCount (n : ℕ) : ℕ := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4 * (n % 256))) % 16

private def countBytes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | w+1, n => byteCount n + countBytes w (n / 256)

private def decode (n : ℕ) : Finset ℤ := n.bitIndices.toFinset.image Int.ofNat

private def checkA (a : ℕ) : Bool := (List.range 80).all fun b =>
  decide (b ≤ a) || (List.range 80).all (fun c =>
    decide (c ≤ b) || (countBytes 111 (sumBits a b c 11) != 347))

set_option maxHeartbeats 0 in
/-- At h=11, the cardinality 347 of the sumset of {0,7,17,80} is absent
from all four-element subsets of [0,79]. This negates the full source question's
affirmative proposition; it does not assert that the optimal diameter is 80. -/
theorem result : ¬ claim := by
  have count_bits_length (w n : ℕ) (hn : n < 2^w) :
      countBits w n = n.bitIndices.length := by
    induction w generalizing n with
    | zero =>
      have : n = 0 := by simpa using hn
      simp_all [countBits]
    | succ w ih =>
      induction n using Nat.bitCasesOn with
      | bit b n =>
        have hn' : n < 2^w := Nat.bit_lt_two_pow_succ_iff.mp hn
        cases b <;> simp [countBits, ih n hn', Nat.mul_add_div]
        omega
  have count_bits_split (u v n : ℕ) :
      countBits (u+v) n = countBits u n + countBits v (n / 2^u) := by
    induction u generalizing n with
    | zero => simp [countBits]
    | succ u ih =>
      simp only [Nat.succ_add, countBits]
      rw [ih]
      simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm, Nat.add_assoc]
  have count_bits_mod (w n : ℕ) : countBits w (n % 2^w) = countBits w n := by
    induction w generalizing n with
    | zero => rfl
    | succ w ih =>
      simp only [countBits]
      rw [Nat.mod_mod_of_dvd _ (by simp [pow_succ]), pow_succ',
        Nat.mod_mul_right_div_self, ih]
  have count_bytes_bits (w n : ℕ) : countBytes w n = countBits (8*w) n := by
    have table : ∀ n : Fin 256, byteCount n = countBits 8 n := by decide +kernel
    have byte (n : ℕ) : byteCount n = countBits 8 n := by
      have h := table ⟨n%256, Nat.mod_lt _ (by decide)⟩
      change byteCount (n%256) = countBits 8 (n%256) at h
      rw [show byteCount (n%256) = byteCount n by simp [byteCount]] at h
      exact h.trans (count_bits_mod 8 n)
    induction w generalizing n with
    | zero => rfl
    | succ w ih =>
      rw [countBytes, byte, ih, Nat.mul_succ, Nat.add_comm (8*w), count_bits_split]
      rfl
  have decode_or (x y : ℕ) : decode (x ||| y) = decode x ∪ decode y := by
    ext z
    simp only [decode, Finset.mem_image, List.mem_toFinset, Nat.mem_bitIndices,
      Nat.testBit_or, Bool.or_eq_true, Finset.mem_union]
    aesop
  have decode_shift (x a : ℕ) : decode (x <<< a) = {↑a} + decode x := by
    ext z
    simp only [decode, Finset.mem_image, List.mem_toFinset, Nat.mem_bitIndices,
      Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_add,
      Finset.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨k, ⟨hak, hk⟩, rfl⟩
      exact ⟨↑(k-a), ⟨k-a, hk, rfl⟩, by
        change (a:ℤ) + ((k-a:ℕ):ℤ) = (k:ℤ)
        rw [Int.natCast_sub hak]
        omega⟩
    · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨a+k, ⟨by omega, by simpa using hk⟩, by simp⟩
  have sum_bits_decode (h a b c : ℕ) :
      decode (sumBits a b c h) = nsmulRec h ({0, ↑a, ↑b, ↑c} : Finset ℤ) := by
    induction h with
    | zero => simp [sumBits, decode, nsmulRec]; rfl
    | succ h ih =>
      simp only [sumBits, decode_or, decode_shift, ih, nsmulRec]
      ext z
      simp only [Finset.mem_union, Finset.mem_add, Finset.mem_insert,
        Finset.mem_singleton, exists_eq_left]
      aesop (add simp [add_comm])
  have coefficients (h a b c : ℕ) (z : ℤ) :
      z ∈ nsmulRec h ({0, ↑a, ↑b, ↑c} : Finset ℤ) ↔
        ∃ i j k : ℕ, i+j+k ≤ h ∧ z = ↑(i*a+j*b+k*c) := by
    induction h generalizing z with
    | zero =>
      change z ∈ ({0}:Finset ℤ) ↔ _
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨0,0,0, by omega, by simp⟩
      · rintro ⟨i,j,k,h,rfl⟩
        have : i=0 ∧ j=0 ∧ k=0 := by omega
        simp [this.1, this.2.1, this.2.2]
    | succ h ih =>
      rw [nsmulRec, add_comm]
      rw [Finset.mem_add]
      constructor
      · rintro ⟨x,hx,y,hy,rfl⟩
        obtain ⟨i,j,k,hijk,rfl⟩ := (ih y).mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨i,j,k,by omega,by simp⟩
        · refine ⟨i+1,j,k,by omega,?_⟩; push_cast; ring
        · refine ⟨i,j+1,k,by omega,?_⟩; push_cast; ring
        · refine ⟨i,j,k+1,by omega,?_⟩; push_cast; ring
      · rintro ⟨i,j,k,hijk,rfl⟩
        by_cases hi : i=0
        · subst i
          by_cases hj : j=0
          · subst j
            cases k with
            | zero =>
              refine ⟨0,by simp,0,(ih 0).mpr ⟨0,0,0,by omega,by simp⟩,by simp⟩
            | succ k =>
              refine ⟨↑c,by simp,↑(k*c),(ih _).mpr ⟨0,0,k,by omega,by simp⟩,?_⟩
              push_cast; ring
          · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
            refine ⟨↑b,by simp,↑(j*b+k*c),(ih _).mpr ⟨0,j,k,by omega,by simp⟩,?_⟩
            push_cast; ring
        · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
          refine ⟨↑a,by simp,↑(i*a+j*b+k*c),(ih _).mpr ⟨i,j,k,by omega,rfl⟩,?_⟩
          push_cast; ring
  have sum_bits_bound (h a b c m : ℕ) (ha : a≤m) (hb : b≤m) (hc : c≤m) :
      sumBits a b c h < 2^(h*m+1) := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hit
    have hz : (i:ℤ) ∈ nsmulRec h ({0, ↑a, ↑b, ↑c} : Finset ℤ) := by
      rw [← sum_bits_decode]
      exact Finset.mem_image.mpr ⟨i, by simpa using hit, rfl⟩
    obtain ⟨j,k,l,hjkl,heq⟩ := (coefficients h a b c (i:ℤ)).mp hz
    have heq' : i = j*a+k*b+l*c := by exact_mod_cast heq
    have hle : i ≤ h*m := calc
      i = j*a+k*b+l*c := heq'
      _ ≤ j*m+k*m+l*m := by gcongr
      _ = (j+k+l)*m := by ring
      _ ≤ h*m := Nat.mul_le_mul_right _ hjkl
    omega
  have sum_card_count (a b c : ℕ) (ha : a≤80) (hb : b≤80) (hc : c≤80) :
      (nsmulRec 11 ({0, ↑a, ↑b, ↑c} : Finset ℤ)).card =
        countBytes 111 (sumBits a b c 11) := by
    rw [← sum_bits_decode, decode, Finset.card_image_of_injective _ Int.ofNat_injective,
      List.toFinset_card_of_nodup Nat.bitIndices_nodup, count_bytes_bits,
      count_bits_length]
    exact (sum_bits_bound 11 a b c 80 ha hb hc).trans_le
      (Nat.pow_le_pow_right (show 1 ≤ (2:ℕ) by decide) (show 11*80+1 ≤ 8*111 by decide))
  have translate_card (h : ℕ) (A : Finset ℤ) (t : ℤ) :
      (nsmulRec h ({t} + A)).card = (nsmulRec h A).card := by
    change (h • ({t} + A)).card = (h • A).card
    rw [nsmul_add, Finset.nsmul_singleton, Finset.card_singleton_add]
  have normalize_four (B : Finset ℤ) (hB : B.card = 4)
      (hbound : B ⊆ Finset.Icc 0 79) :
      ∃ a b c : ℕ, 0<a ∧ a<b ∧ b<c ∧ c≤79 ∧
        ∀ h, (nsmulRec h B).card =
          (nsmulRec h ({0, ↑a, ↑b, ↑c} : Finset ℤ)).card := by
    let f := B.orderEmbOfFin hB
    have hf (i : Fin 4) : f i ∈ B := B.orderEmbOfFin_mem hB i
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have h23 : f 2 < f 3 := f.strictMono (by decide)
    have hb0 := Finset.mem_Icc.mp (hbound (hf 0))
    have hb3 := Finset.mem_Icc.mp (hbound (hf 3))
    let a := (f 1 - f 0).toNat
    let b := (f 2 - f 0).toNat
    let c := (f 3 - f 0).toNat
    have ha : (a:ℤ) = f 1 - f 0 := Int.toNat_of_nonneg (by omega)
    have hb : (b:ℤ) = f 2 - f 0 := Int.toNat_of_nonneg (by omega)
    have hc : (c:ℤ) = f 3 - f 0 := Int.toNat_of_nonneg (by omega)
    have hset : B = {f 0, f 1, f 2, f 3} := by
      rw [← B.image_orderEmbOfFin_univ hB]
      rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]
      simp [f]
    have htranslate : B = {f 0} + {0, (a:ℤ), (b:ℤ), (c:ℤ)} := by
      rw [hset]
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_add, exists_eq_left]
      rw [ha,hb,hc]
      constructor
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨0, Or.inl rfl, by omega⟩
        · exact ⟨f 1-f 0, Or.inr (Or.inl rfl), by omega⟩
        · exact ⟨f 2-f 0, Or.inr (Or.inr (Or.inl rfl)), by omega⟩
        · exact ⟨f 3-f 0, Or.inr (Or.inr (Or.inr rfl)), by omega⟩
      · rintro ⟨y, (rfl | rfl | rfl | rfl), hy⟩
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (by omega)))
    refine ⟨a,b,c,by omega,by omega,by omega,by omega,?_⟩
    intro h
    rw [htranslate]
    exact translate_card h _ _
  have witness : (nsmulRec 11 ({0,7,17,80} : Finset ℤ)).card = 347 := by
    have heq := sum_card_count 7 17 80 (by decide) (by decide) (by decide)
    calc
      _ = countBytes 111 (sumBits 7 17 80 11) := by simpa only [Nat.cast_ofNat] using heq
      _ = 347 := by decide +kernel
  have exclusion : ∀ a : Fin 78, checkA (a.val + 1) = true := by
    intro a
    fin_cases a <;> decide +kernel
  intro H
  obtain ⟨B,hB,hbound,hcard⟩ := H 11 (by decide) {0,7,17,80} (by decide +kernel)
  change B ⊆ Finset.Icc 0 79 at hbound
  obtain ⟨a,b,c,ha,hab,hbc,hc,hnorm⟩ := normalize_four B hB hbound
  have hex := exclusion ⟨a-1, by omega⟩
  have hrow : checkA a = true := by simpa [Nat.sub_add_cancel ha] using hex
  have hb80 : b < 80 := by omega
  have hc80 : c < 80 := by omega
  have hbcases := (List.all_eq_true.mp hrow) b (List.mem_range.mpr hb80)
  simp only [decide_eq_false (show ¬ b≤a by omega), Bool.false_or] at hbcases
  have hccase := (List.all_eq_true.mp hbcases) c (List.mem_range.mpr hc80)
  have hne : countBytes 111 (sumBits a b c 11) ≠ 347 := by
    simpa only [decide_eq_false (show ¬ c≤b by omega), Bool.false_or,
      bne_iff_ne] using hccase
  apply hne
  rw [← sum_card_count a b c (by omega) (by omega) (by omega), ← hnorm 11,
    hcard, witness]
end D5.S0.Certificates.ShinFourPointCompression
