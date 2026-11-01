/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical binary supports, disjoint complete inventory, bank masses and literal-cut cardinality. -/
/- SOURCE_ONLY_UNCOMPILED. Physical occurrence inventory; equal values stay distinct.
Caller construction and proof. The terminal bits are never selected. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic
import D5.S3.Combinatorics.Circle.ThreeBitSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
open private mask_labels mask_labels_mem mask_labels_sum mask_labels_disjoint
  from D5.S3.Combinatorics.Circle.ThreeBitSource

private def shift (off : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (off+·)
private def support (off m : ℕ) : Finset ℕ := shift off m.bitIndices.toFinset

private theorem mem_shift (off i : ℕ) (S : Finset ℕ) :
    i∈shift off S ↔ ∃ e∈S,off+e=i := by simp [shift]

private theorem bit_bound (len m e : ℕ) (hm : m<2^len)
    (he : e∈m.bitIndices.toFinset) : e<len := by
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp he)
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0<2) (show len≤e by omega)
  omega

private theorem support_eq_mask (len off m : ℕ) (hm : m<2^len) :
    support off m=mask_labels len off m hm := by
  ext i
  simp only [support,mem_shift,mask_labels_mem,List.mem_toFinset,Nat.mem_bitIndices]
  constructor
  · rintro ⟨e,he,rfl⟩
    exact ⟨e,bit_bound len m e hm (by simpa using Nat.mem_bitIndices.mpr he),he,rfl⟩
  · rintro ⟨e,_,he,rfl⟩; exact ⟨e,he,rfl⟩

private theorem support_bound (len off m i : ℕ) (hm : m<2^len)
    (hi : i∈support off m) : off ≤ i ∧ i < off+len := by
  obtain ⟨e,he,rfl⟩ := (mem_shift off i m.bitIndices.toFinset).mp hi
  have hh := bit_bound len m e hm he
  omega

private theorem support_sum (len off m : ℕ) (hm : m<2^len)
    (f : ℕ→ℤ) (B : ℤ) (hf : ∀ e<len,f (off+e)=(2:ℤ)^e*B) :
    (∑ i∈support off m,f i)=(m:ℤ)*B := by
  rw [support_eq_mask len off m hm]
  exact mask_labels_sum len off m hm f B hf

-- The low grain bits of s-1 are all ones. This proves disjointness without
-- any search over masks or a favorable-mask premise at the public endpoint.
private theorem reserve_bits (e s r : ℕ) (hs : 1≤s) (hdiv : 2^e∣s)
    (hr : 1≤r ∧ r≤2^e) :
    Disjoint (s-r).bitIndices.toFinset (r-1).bitIndices.toFinset ∧
    (s-r).bitIndices.toFinset ∪ (r-1).bitIndices.toFinset=(s-1).bitIndices.toFinset := by
  classical
  obtain ⟨k,hk⟩ := hdiv
  have hG : 1≤(2:ℕ)^e := Nat.one_le_two_pow
  have hkpos : 1≤k := by
    by_contra hn
    have hk0 : k=0 := by omega
    have hs0 : s=0 := by simpa only [hk0,Nat.mul_zero] using hk
    omega
  have hsplit : s-1=2^e*(k-1)+(2^e-1) := by
    have he : 2^e*(k-1)+2^e=s := by
      calc
        2^e*(k-1)+2^e=2^e*(k-1+1) := by rw [Nat.mul_add,Nat.mul_one]
        _ = s := by rw [Nat.sub_add_cancel hkpos]; exact hk.symm
    omega
  have hrG : r-1<2^e := by omega
  have hsub : (r-1).bitIndices.toFinset ⊆ (s-1).bitIndices.toFinset := by
    intro i hi
    have hie := bit_bound e (r-1) i hrG hi
    apply List.mem_toFinset.mpr
    apply Nat.mem_bitIndices.mpr
    rw [hsplit,Nat.testBit_two_pow_mul_add (k-1) (by omega : 2^e-1<2^e) i]
    simp [hie,Nat.testBit_two_pow_sub_one]
  let C := (s-1).bitIndices.toFinset \ (r-1).bitIndices.toFinset
  have hdis : Disjoint C (r-1).bitIndices.toFinset := Finset.disjoint_left.mpr
    (fun i hi hj => (Finset.mem_sdiff.mp hi).2 hj)
  have hfull : C∪(r-1).bitIndices.toFinset=(s-1).bitIndices.toFinset :=
    Finset.sdiff_union_of_subset hsub
  have hsum := Finset.sum_union hdis (f := fun i : ℕ => 2^i)
  rw [hfull,Finset.sum_toFinset_bitIndices_two_pow,Finset.sum_toFinset_bitIndices_two_pow] at hsum
  have hsr : r≤s := by
    have hh : 2^e≤s := by
      rw [hk]
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((2:ℕ)^e) hkpos
    omega
  have hC : (s-r).bitIndices.toFinset=C := by
    apply Finset.geomSum_injective (by decide : 2≤(2:ℕ))
    dsimp only
    rw [Finset.sum_toFinset_bitIndices_two_pow]
    omega
  rw [hC]
  exact ⟨hdis,hfull⟩

private def positives (a b c d : ℕ) : Fin 4 → Finset ℕ :=
  ![Finset.range (d-1),shift d (Finset.range (c-1)),
    shift (d+c) (Finset.range (b-1)),shift (d+c+b) (Finset.range (a-1))]

private def banks (a b c d p q w : ℕ) : Fin 3 → Finset ℕ :=
  ![(positives a b c d 3 \ (support (d+c+b) p ∪ support (d+c+b) q)) ∪ positives a b c d 0,
    support (d+c+b) p,
    positives a b c d 1 \ support d w]

private theorem positive_mem (a b c d : ℕ) (r : Fin 4) (i : ℕ) :
    i∈positives a b c d r ↔
      if r=0 then i<d-1 else if r=1 then d ≤ i ∧ i < d+(c-1)
      else if r=2 then d+c ≤ i ∧ i < d+c+(b-1)
      else d+c+b ≤ i ∧ i < d+c+b+(a-1) := by
  have hshift (off len : ℕ) :
      i∈shift off (Finset.range len) ↔ off ≤ i ∧ i < off+len := by
    rw [mem_shift]
    simp only [Finset.mem_range]
    constructor
    · rintro ⟨e,he,rfl⟩; omega
    · rintro ⟨hlo,hhi⟩
      exact ⟨i-off,by omega,by omega⟩
  fin_cases r <;> simp [positives,hshift,Finset.mem_range]

private theorem banks_inventory (a b c d p q w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hp : p<2^(a-1)) (hq : q<2^(a-1)) (hw : w<2^(c-1))
    (hpq : Disjoint p.bitIndices.toFinset q.bitIndices.toFinset) :
    (∀ r : Fin 3, ∀ i∈banks a b c d p q w r,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d-1 ∧ i≠d+c-1 ∧ i≠d+c+b-1) ∧
    (∀ r s : Fin 3, r≠s → Disjoint (banks a b c d p q w r) (banks a b c d p q w s)) ∧
    (Finset.range (a+b+c+d) \ (banks a b c d p q w 0 ∪ banks a b c d p q w 1 ∪
      banks a b c d p q w 2 ∪ {a+b+c+d-1,d-1,d+c-1,d+c+b-1}) =
      positives a b c d 2 ∪ support (d+c+b) q ∪ support d w) := by
  classical
  have bp (i : ℕ) (hi : i∈support (d+c+b) p) := support_bound (a-1) (d+c+b) p i hp hi
  have bq (i : ℕ) (hi : i∈support (d+c+b) q) := support_bound (a-1) (d+c+b) q i hq hi
  have bw (i : ℕ) (hi : i∈support d w) := support_bound (c-1) d w i hw hi
  have hdis : Disjoint (support (d+c+b) p) (support (d+c+b) q) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨u,hu,heu⟩ := (mem_shift (d+c+b) i _).mp hi
    obtain ⟨v,hv,hev⟩ := (mem_shift (d+c+b) i _).mp hj
    have he : u=v := by omega
    exact Finset.disjoint_left.mp hpq hu (he.symm ▸ hv)
  have good : ∀ r : Fin 3, ∀ i∈banks a b c d p q w r,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d-1 ∧ i≠d+c-1 ∧ i≠d+c+b-1 := by
    intro r i hi
    fin_cases r
    all_goals simp only [banks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
      Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi
    · rcases hi with hi|hi
      · have hh := (positive_mem a b c d 3 i).mp hi.1; simp at hh; omega
      · have hh := (positive_mem a b c d 0 i).mp hi; simp at hh; omega
    · have hh := bp i hi; omega
    · have hh := (positive_mem a b c d 1 i).mp hi.1; simp at hh; omega
  have dis : ∀ r s : Fin 3, r≠s → Disjoint (banks a b c d p q w r) (banks a b c d p q w s) := by
    intro r s hrs
    apply Finset.disjoint_left.mpr
    intro i hi hj
    fin_cases r <;> fin_cases s
    all_goals try exact (hrs rfl).elim
    all_goals simp only [banks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
      Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi hj
    all_goals by_cases hpi : i∈support (d+c+b) p
    all_goals try have hpb := bp i hpi
    all_goals simp [positive_mem,hpi] at hi hj
    all_goals omega
  refine ⟨good,dis,?_⟩
  ext i
  have hnot : ¬(i∈support (d+c+b) p ∧ i∈support (d+c+b) q) :=
    fun hh => Finset.disjoint_left.mp hdis hh.1 hh.2
  by_cases hpi : i∈support (d+c+b) p <;>
    by_cases hqi : i∈support (d+c+b) q <;> by_cases hwi : i∈support d w
  all_goals try exact (hnot ⟨hpi,hqi⟩).elim
  all_goals try have hpb := bp i hpi
  all_goals try have hqb := bq i hqi
  all_goals try have hwb := bw i hwi
  all_goals simp [banks,positive_mem,hpi,hqi,hwi]
  all_goals omega

private theorem shift_sum (off n : ℕ) (f : ℕ→ℤ) (B : ℤ)
    (hf : ∀ e<n,f (off+e)=(2:ℤ)^e*B) :
    (∑ i∈shift off (Finset.range n),f i)=(2^n-1)*B := by
  rw [shift,Finset.sum_image (by intro i hi j hj he; exact Nat.add_left_cancel he)]
  have he : (∑ e∈Finset.range n,f (off+e))=(∑ e∈Finset.range n,(2:ℤ)^e)*B := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun e he => hf e (Finset.mem_range.mp he))
  rw [he]
  have hs : ∑ i∈Finset.range n,(2:ℤ)^i=2^n-1 := by simpa using geom_sum_mul (2:ℤ) n
  rw [hs]

private theorem bank_masses (a b c d p q w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hp : p<2^(a-1)) (hq : q<2^(a-1)) (hw : w<2^(c-1))
    (hpq : Disjoint p.bitIndices.toFinset q.bitIndices.toFinset)
    (f : ℕ→ℤ) (U V X : ℤ)
    (hU : ∀ e<d-1,f e=(2:ℤ)^e*U)
    (hV : ∀ e<c-1,f (d+e)=(2:ℤ)^e*V)
    (hX : ∀ e<a-1,f (d+c+b+e)=(2:ℤ)^e*X) :
    (∑ i∈banks a b c d p q w 0,f i)=(2^(a-1)-1-(p:ℤ)-q)*X+(2^(d-1)-1)*U ∧
    (∑ i∈banks a b c d p q w 1,f i)=(p:ℤ)*X ∧
    (∑ i∈banks a b c d p q w 2,f i)=(2^(c-1)-1-(w:ℤ))*V := by
  classical
  have sp := support_sum (a-1) (d+c+b) p hp f X hX
  have sq := support_sum (a-1) (d+c+b) q hq f X hX
  have sw := support_sum (c-1) d w hw f V hV
  have hxp : support (d+c+b) p ⊆ positives a b c d 3 := by
    intro i hi; have hh := support_bound (a-1) (d+c+b) p i hp hi
    simpa [positive_mem] using hh
  have hxq : support (d+c+b) q ⊆ positives a b c d 3 := by
    intro i hi; have hh := support_bound (a-1) (d+c+b) q i hq hi
    simpa [positive_mem] using hh
  have hvw : support d w ⊆ positives a b c d 1 := by
    intro i hi; have hh := support_bound (c-1) d w i hw hi
    simpa [positive_mem] using hh
  have hdis : Disjoint (support (d+c+b) p) (support (d+c+b) q) := by
    rw [support_eq_mask (a-1) (d+c+b) p hp,support_eq_mask (a-1) (d+c+b) q hq]
    exact mask_labels_disjoint hpq
  have hfullX : (∑ i∈positives a b c d 3,f i)=(2^(a-1)-1)*X := by
    simpa [positives] using shift_sum (d+c+b) (a-1) f X hX
  have hfullV : (∑ i∈positives a b c d 1,f i)=(2^(c-1)-1)*V := by
    simpa [positives] using shift_sum d (c-1) f V hV
  have hfullU : (∑ i∈positives a b c d 0,f i)=(2^(d-1)-1)*U := by
    have hh := shift_sum 0 (d-1) f U (by simpa using hU)
    simpa [positives,shift] using hh
  have hsub : support (d+c+b) p ∪ support (d+c+b) q ⊆ positives a b c d 3 :=
    Finset.union_subset hxp hxq
  have hxs := Finset.sum_sdiff (f := f) hsub
  rw [Finset.sum_union hdis,sp,sq,hfullX] at hxs
  have hvs := Finset.sum_sdiff (f := f) hvw
  rw [sw,hfullV] at hvs
  have hUdis : Disjoint (positives a b c d 3 \ (support (d+c+b) p ∪ support (d+c+b) q))
      (positives a b c d 0) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hx := (positive_mem a b c d 3 i).mp (Finset.mem_sdiff.mp hi).1
    have hu := (positive_mem a b c d 0 i).mp hj
    simp at hx hu; omega
  simp only [banks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply]
  rw [Finset.sum_union hUdis,hfullU]
  exact ⟨by nlinarith only [hxs],sp,by nlinarith only [hvs]⟩

private theorem first_length (a b c d p q m : ℕ)
    (ha : 2≤a) (hd : 2≤d) (hm : m<2^(a-1))
    (hunion : p.bitIndices.toFinset ∪ q.bitIndices.toFinset=m.bitIndices.toFinset) :
    (banks a b c d p q 0 0).card+1=a+d-1-m.bitIndices.toFinset.card := by
  classical
  have hs : support (d+c+b) p ∪ support (d+c+b) q=support (d+c+b) m := by
    simp only [support,shift,←Finset.image_union,hunion]
  have hsub : support (d+c+b) m ⊆ positives a b c d 3 := by
    intro i hi; have hh := support_bound (a-1) (d+c+b) m i hm hi
    simpa [positive_mem] using hh
  have hdis : Disjoint (positives a b c d 3 \ support (d+c+b) m) (positives a b c d 0) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hx := (positive_mem a b c d 3 i).mp (Finset.mem_sdiff.mp hi).1
    have hu := (positive_mem a b c d 0 i).mp hj
    simp at hx hu; omega
  have hcX : (positives a b c d 3).card=a-1 := by
    change (shift (d+c+b) (Finset.range (a-1))).card=a-1
    rw [shift,Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
    simp
  have hcU : (positives a b c d 0).card=d-1 := by simp [positives]
  have hcm : (support (d+c+b) m).card=m.bitIndices.toFinset.card := by
    exact Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
  have hcard := Finset.card_le_card hsub
  change ((positives a b c d 3 \ (support (d+c+b) p ∪ support (d+c+b) q)) ∪ positives a b c d 0).card+1=_
  rw [hs,Finset.card_union_of_disjoint hdis,Finset.card_sdiff_of_subset hsub,hcX,hcU,hcm]
  rw [hcX,hcm] at hcard
  omega

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
