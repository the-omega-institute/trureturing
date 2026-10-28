/- GID: D5/S3/Arith/Lattices/Golay/LeechMinimalCount
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/LeechMinimalCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact classification and count of the unbounded integer Leech minimum sphere. -/

import D5.S3.Arith.Lattices.Golay.GolayOctadCount
import D5.S3.Arith.Lattices.Golay.LeechSignedSupport

/-! # The actual integer Leech minimum sphere -/

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

open scoped BigOperators
noncomputable section
namespace D5.S3.Arith.Lattices.Golay.LeechMinimalCount
open GolayEncoder IntegerLeech GolayOctadCount LeechSignedSupport
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

abbrev Sphere := {x : IntVector // Admissible code x ∧ squareSum x = 32}
abbrev TwoSupport := {S : Finset I // S.card = 2}
abbrev ZeroFamily := (S : TwoSupport) × (S.val → F2)
abbrev OctadFamily := (c : Octad) × EvenSigns (wordSupport (c.val : Word))
abbrev OddFamily := I × code
abbrev Families := ZeroFamily ⊕ (OctadFamily ⊕ OddFamily)

def zeroVector (p : ZeroFamily) : IntVector := signed 4 p.1.val p.2

def octadVector (p : OctadFamily) : IntVector :=
  signed 2 (wordSupport (p.1.val : Word)) p.2.val

/-- At j, replace the ordinary sign by minus three times that sign. -/
def oddVector (p : OddFamily) : IntVector := fun i =>
  sign ((p.2 : Word) i) + if i = p.1 then -4 * sign ((p.2 : Word) i) else 0

def familyVector : Families → IntVector
  | .inl p => zeroVector p
  | .inr (.inl p) => octadVector p
  | .inr (.inr p) => oddVector p

private theorem scale_square (k : ℤ) (a : IntVector) :
    squareSum (fun i => k * a i) = k ^ 2 * squareSum a := by
  simp only [squareSum, mul_pow, Finset.mul_sum]

private theorem support_square_one {b : IntVector}
    (h : ∀ i, b i = 0 ∨ b i = 1 ∨ b i = -1) :
    squareSum b = (nzSupport b).card := by
  calc
    squareSum b = ∑ i : I, if b i ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases h i with h | h | h <;> simp [h]
    _ = ((nzSupport b).card : ℤ) := by
      simp only [nzSupport, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : b i = 0 <;> simp [hi]

private theorem red_zero_div_two {a : IntVector} (h : red a = 0) :
    ∀ i, a i = 2 * (a i / 2) := by
  intro i
  have he : (a i : F2) = 0 := congrFun h i
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) 2).mp he
  omega

private theorem square_eq_one_values {z : ℤ} (h : z ^ 2 = 1) : z = 1 ∨ z = -1 := by
  exact sq_eq_one_iff.mp h

/-- Equality in the sum-of-squares bound with value two forces two signed units. -/
private theorem norm_two_shape {b : IntVector} (h : squareSum b = 2) :
    (nzSupport b).card = 2 ∧
      (∀ i ∈ nzSupport b, b i = 1 ∨ b i = -1) := by
  have hb : ∀ i, b i = 0 ∨ b i = 1 ∨ b i = -1 := by
    intro i
    have hi : b i ^ 2 ≤ 2 := by
      have := Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
      change b i ^ 2 ≤ squareSum b at this
      omega
    have hlo : -1 ≤ b i := by nlinarith [sq_nonneg (b i + 1)]
    have hhi : b i ≤ 1 := by nlinarith [sq_nonneg (b i - 1)]
    omega
  refine ⟨?_, ?_⟩
  · have hc := support_square_one hb
    omega
  · intro i hi
    exact (hb i).resolve_left (mem_nzSupport b i |>.mp hi)

/-- Equality in the actual Golay minimum-weight bound forces an octad with unit entries. -/
private theorem norm_eight_shape {a : IntVector}
    (hc : red a ∈ code) (hn : red a ≠ 0) (ha : squareSum a = 8) :
    weight (red a) = 8 ∧
      (∀ i, if red a i = 0 then a i = 0 else a i = 1 ∨ a i = -1) := by
  have hlo := minimum_weight (red a) hc hn
  have hhi := weight_le_squares a
  have hw : weight (red a) = 8 := by omega
  have hd : ∀ i, 0 ≤ a i ^ 2 - (if red a i = 0 then 0 else 1) := by
    intro i
    split_ifs with hi
    · simpa using sq_nonneg (a i)
    · have hnz : a i ≠ 0 := by intro hz; simp [red, hz] at hi
      have hp := sq_pos_of_ne_zero hnz
      omega
  have hs : (∑ i, (a i ^ 2 - (if red a i = 0 then 0 else 1))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have he : (∑ i, if red a i = 0 then (0 : ℤ) else 1) = weight (red a) := by
      unfold weight
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : red a i = 0 <;>
        simp only [hi, ite_true, ite_false, Nat.cast_zero, Nat.cast_one]
    rw [he]
    change squareSum a - (weight (red a) : ℤ) = 0
    rw [ha, hw]; norm_num
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd i)).mp hs
  refine ⟨hw, ?_⟩
  intro i
  have hi := he i (Finset.mem_univ i)
  split_ifs with hz
  · rw [if_pos hz] at hi
    have hh : a i ^ 2 = 0 := by omega
    exact (sq_eq_zero_iff).mp hh
  · rw [if_neg hz] at hi
    apply square_eq_one_values
    omega

private theorem zeroVector_mem (p : ZeroFamily) : Admissible code (zeroVector p) := by
  apply (representation code (zeroVector p)).2
  refine ⟨0, Or.inl rfl, signed 2 p.1.val p.2, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ p.1.val <;> simp [zeroVector, signed, hi] <;> ring
  · have hr : red (signed 2 p.1.val p.2) = 0 := by
      ext i
      change ((signed 2 p.1.val p.2 i : ℤ) : F2) = 0
      by_cases hi : i ∈ p.1.val
      · rw [signed_at 2 p.1.val p.2 ⟨i, hi⟩]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨_, rfl⟩
      · simp [signed, hi]
    rw [hr]
    exact code.zero_mem
  · have hs := signed_sum 4 p.1.val p.2
    change (∑ i, signed 4 p.1.val p.2 i) % 8 = 0
    rw [hs, p.1.property]
    omega

private theorem zeroVector_square (p : ZeroFamily) : squareSum (zeroVector p) = 32 := by
  rw [zeroVector, signed_squareSum, p.1.property]
  norm_num

private theorem zeroVector_even (p : ZeroFamily) : ∀ i, zeroVector p i % 2 = 0 := by
  intro i
  by_cases hi : i ∈ p.1.val <;> simp [zeroVector, signed, hi] <;> omega

private theorem zeroVector_quotient (p : ZeroFamily) :
    red (fun i => zeroVector p i / 2) = 0 := by
  ext i
  by_cases hi : i ∈ p.1.val
  · change ((zeroVector p i / 2 : ℤ) : F2) = 0
    have hx : zeroVector p i = 4 * sign (p.2 ⟨i, hi⟩) := by
      simp [zeroVector, signed, hi]
    rw [hx]
    have he : 4 * sign (p.2 ⟨i, hi⟩) / 2 = 2 * sign (p.2 ⟨i, hi⟩) := by omega
    rw [he]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨_, rfl⟩
  · simp [red, zeroVector, signed, hi]

private theorem octadVector_mem (p : OctadFamily) : Admissible code (octadVector p) := by
  let S := wordSupport (p.1.val : Word)
  have hS : S.card = 8 := by simpa [S] using p.1.property
  apply (representation code (octadVector p)).2
  refine ⟨0, Or.inl rfl, signed 1 S p.2.val, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ S <;> simp [octadVector, S, signed, hi] <;> ring
  · have hr : red (signed 1 S p.2.val) = (p.1.val : Word) := by
      ext i
      by_cases hi : (p.1.val : Word) i = 0
      · simp [red, signed, S, hi]
      · have hc : (p.1.val : Word) i = 1 := by
          have hv := ZMod.val_lt ((p.1.val : Word) i)
          have hv0 : ((p.1.val : Word) i).val ≠ 0 := by
            intro h; apply hi; apply ZMod.val_injective 2; simpa using h
          apply ZMod.val_injective 2
          change ((p.1.val : Word) i).val = 1
          omega
        simp [red, signed, S, hi, hc]
    rw [hr]; exact p.1.val.property
  · have hs := signed_sum 2 S p.2.val
    obtain ⟨t, ht⟩ := evenSigns_sum_div_two S p.2
    change (∑ i, signed 2 S p.2.val i) % 8 = 0
    rw [hs, hS, ht]
    omega

private theorem octadVector_square (p : OctadFamily) : squareSum (octadVector p) = 32 := by
  rw [octadVector, signed_squareSum, wordSupport_card, p.1.property]
  norm_num

private theorem octadVector_even (p : OctadFamily) : ∀ i, octadVector p i % 2 = 0 := by
  intro i
  by_cases hi : i ∈ wordSupport (p.1.val : Word) <;> simp [octadVector, signed, hi] <;> omega

private theorem octadVector_quotient (p : OctadFamily) :
    red (fun i => octadVector p i / 2) = (p.1.val : Word) :=
  signed_two_red _ _

private theorem oddVector_at (p : OddFamily) :
    oddVector p p.1 = -3 * sign ((p.2 : Word) p.1) := by simp [oddVector]; ring

private theorem oddVector_off (p : OddFamily) {i : I} (hi : i ≠ p.1) :
    oddVector p i = sign ((p.2 : Word) i) := by simp [oddVector, hi]

private theorem oddVector_parity (p : OddFamily) : ∀ i, oddVector p i % 2 = 1 := by
  intro i
  by_cases hi : i = p.1
  · subst i
    rw [oddVector_at]
    rcases sign_values ((p.2 : Word) p.1) with h | h <;> rw [h] <;> norm_num
  · rw [oddVector_off p hi]
    exact sign_mod_two _

private theorem oddVector_quotient (p : OddFamily) :
    red (fun i => (oddVector p i - 1) / 2) = (p.2 : Word) := by
  ext i
  have hb : (p.2 : Word) i = 0 ∨ (p.2 : Word) i = 1 := by
    have hv := ZMod.val_lt ((p.2 : Word) i)
    have hh : ((p.2 : Word) i).val = 0 ∨ ((p.2 : Word) i).val = 1 := by omega
    rcases hh with h | h
    · left; apply ZMod.val_injective 2; simpa using h
    · right; apply ZMod.val_injective 2; change ((p.2 : Word) i).val = 1; exact h
  by_cases hi : i = p.1
  · subst i
    rw [red, oddVector_at]
    rcases hb with hb | hb <;> rw [hb] <;> decide +kernel
  · rw [red, oddVector_off p hi]
    rcases hb with hb | hb <;> rw [hb] <;> decide +kernel

private theorem lift_sum (c : Word) : (∑ i, liftBit (c i)) = (weight c : ℤ) := by
  simp only [weight, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hv := ZMod.val_lt (c i)
  by_cases hi : c i = 0
  · simp [hi]
  · have hval : (c i).val = 1 := by
      have hn : (c i).val ≠ 0 := by
        intro h; apply hi; apply ZMod.val_injective 2; simpa using h
      omega
    simp [hi, liftBit, hval]

private theorem oddVector_sum (p : OddFamily) :
    (∑ i, oddVector p i) = 24 - 2 * weight (p.2 : Word) -
      4 * sign ((p.2 : Word) p.1) := by
  have hsign : (∑ i : I, sign ((p.2 : Word) i)) =
      24 - 2 * (weight (p.2 : Word) : ℤ) := by
    unfold sign
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, lift_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (24 : ℤ) * 1 - 2 * (weight (p.2 : Word) : ℤ) =
      24 - 2 * (weight (p.2 : Word) : ℤ)
    rw [mul_one]
  calc
    _ = (∑ i : I, sign ((p.2 : Word) i)) +
        (-4 * sign ((p.2 : Word) p.1)) := by
      simp [oddVector, Finset.sum_add_distrib]
    _ = _ := by rw [hsign]; ring

private theorem oddVector_mem (p : OddFamily) : Admissible code (oddVector p) := by
  refine ⟨1, Or.inr rfl, oddVector_parity p, ?_, ?_⟩
  · rw [oddVector_quotient]
    exact p.2.property
  · rw [oddVector_sum]
    obtain ⟨t, ht⟩ := doubly_even (p.2 : Word) p.2.property
    have ht' : (weight (p.2 : Word) : ℤ) = 4 * t := by exact_mod_cast ht
    rw [ht']
    rcases sign_values ((p.2 : Word) p.1) with h | h <;> rw [h] <;> omega

private theorem oddVector_square (p : OddFamily) : squareSum (oddVector p) = 32 := by
  have he : ∀ i, oddVector p i ^ 2 = 1 + if i = p.1 then 8 else 0 := by
    intro i
    by_cases hi : i = p.1
    · subst i; rw [oddVector_at]; norm_num [mul_pow]
    · rw [oddVector_off p hi]; simp [hi]
  unfold squareSum
  simp_rw [he]
  simp [Finset.sum_add_distrib]

private theorem zeroVector_injective : Function.Injective zeroVector := by
  rintro ⟨S, σ⟩ ⟨T, τ⟩ h
  have hs : S = T := by
    apply Subtype.ext
    have hh := congrArg nzSupport h
    simpa [zeroVector, signed_support (by norm_num : (4 : ℤ) ≠ 0)] using hh
  subst T
  have ht : σ = τ := signed_injective (by norm_num : (4 : ℤ) ≠ 0) S.val h
  subst τ
  rfl

private theorem octadVector_injective : Function.Injective octadVector := by
  rintro ⟨c, σ⟩ ⟨d, τ⟩ h
  have hc : c = d := by
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun x : IntVector => red (fun i => x i / 2)) h
    simpa only [octadVector_quotient] using hh
  subst d
  have hs : σ = τ := by
    apply Subtype.ext
    exact signed_injective (by norm_num : (2 : ℤ) ≠ 0) _ h
  subst τ
  rfl

private theorem oddVector_injective : Function.Injective oddVector := by
  intro p q h
  have hc : p.2 = q.2 := by
    apply Subtype.ext
    have hh := congrArg (fun x : IntVector => red (fun i => (x i - 1) / 2)) h
    simpa only [oddVector_quotient] using hh
  have hj : p.1 = q.1 := by
    by_contra hn
    have he := congrArg (fun x : IntVector => x p.1 ^ 2) h
    rw [oddVector_at, oddVector_off q hn] at he
    norm_num [mul_pow] at he
  exact Prod.ext hj hc

/-- The two even shapes have different actual quotient residue words. -/
private theorem zero_ne_octad (p : ZeroFamily) (q : OctadFamily) :
    zeroVector p ≠ octadVector q := by
  intro h
  have hh := congrArg (fun x : IntVector => red (fun i => x i / 2)) h
  rw [zeroVector_quotient, octadVector_quotient] at hh
  have hw := q.1.property
  rw [← hh] at hw
  simp [weight] at hw

private theorem even_ne_odd {x : IntVector} (hx : ∀ i, x i % 2 = 0) (p : OddFamily) :
    x ≠ oddVector p := by
  intro h
  have h0 := hx 0
  have h1 := oddVector_parity p 0
  rw [h] at h0
  omega

/-- Every norm-32 odd vector has one exceptional coordinate and 23 unit coordinates. -/
private theorem odd_shape {x : IntVector} (hp : ∀ i, x i % 2 = 1)
    (hs : squareSum x = 32) :
    ∃ j : I, (x j = 3 ∨ x j = -3) ∧
      ∀ i, i ≠ j → (x i = 1 ∨ x i = -1) := by
  let e : I → ℤ := fun i => x i ^ 2 - 1
  have hnonneg : ∀ i, 0 ≤ e i := by
    intro i
    have hn : x i ≠ 0 := by have := hp i; omega
    have := sq_pos_of_ne_zero hn
    dsimp [e]; omega
  have hsum : (∑ i, e i) = 8 := by
    simp only [e, Finset.sum_sub_distrib]
    change squareSum x - _ = 8
    rw [hs]; norm_num
  have hv : ∀ i, x i = 1 ∨ x i = -1 ∨ x i = 3 ∨ x i = -3 := by
    intro i
    have hie : e i ≤ 8 := by
      have := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ i)
      omega
    have hbound : x i ^ 2 ≤ 9 := by dsimp [e] at hie; omega
    have hlow : -3 ≤ x i := by nlinarith [sq_nonneg (x i + 3)]
    have hupp : x i ≤ 3 := by nlinarith [sq_nonneg (x i - 3)]
    have hi := hp i
    omega
  have hj : ∃ j, x j = 3 ∨ x j = -3 := by
    by_contra hn
    have hnot : ∀ i, x i ≠ 3 ∧ x i ≠ -3 := by
      intro i
      constructor
      · intro h; exact hn ⟨i, Or.inl h⟩
      · intro h; exact hn ⟨i, Or.inr h⟩
    have hz : ∀ i, e i = 0 := by
      intro i
      rcases hv i with h | h | h | h
      · simp [e, h]
      · simp [e, h]
      · exact False.elim ((hnot i).1 h)
      · exact False.elim ((hnot i).2 h)
    simp_rw [hz] at hsum
    norm_num at hsum
  obtain ⟨j, hj⟩ := hj
  refine ⟨j, hj, ?_⟩
  have hej : e j = 8 := by rcases hj with h | h <;> simp [e, h]
  have hrest : (∑ i ∈ Finset.univ.erase j, e i) = 0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hsum, hej]
    norm_num
  intro i hi
  have hei := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp hrest
    i (by simp [hi])
  apply square_eq_one_values
  dsimp [e] at hei
  omega

private theorem quotient_unit {z : ℤ} (h : z = 1 ∨ z = -1) :
    z = sign (((z - 1) / 2 : ℤ) : F2) := by
  rcases h with rfl | rfl <;> decide +kernel

private theorem quotient_triple {z : ℤ} (h : z = 3 ∨ z = -3) :
    z = -3 * sign (((z - 1) / 2 : ℤ) : F2) := by
  rcases h with rfl | rfl <;> decide +kernel

private theorem classify_odd {x : IntVector}
    (hp : ∀ i, x i % 2 = 1)
    (hc : red (fun i => (x i - 1) / 2) ∈ code)
    (hs : squareSum x = 32) : ∃ p : OddFamily, oddVector p = x := by
  obtain ⟨j, hj, hother⟩ := odd_shape hp hs
  let c : code := ⟨red (fun i => (x i - 1) / 2), hc⟩
  refine ⟨(j, c), ?_⟩
  funext i
  by_cases hi : i = j
  · subst i
    rw [oddVector_at]
    exact (quotient_triple hj).symm
  · rw [oddVector_off (j, c) hi]
    exact (quotient_unit (hother i hi)).symm

private theorem classify_even_zero {x a : IntVector}
    (hx : ∀ i, x i = 2 * a i) (hr : red a = 0)
    (hs : squareSum x = 32) : ∃ p : ZeroFamily, zeroVector p = x := by
  let b : IntVector := fun i => a i / 2
  have hab : ∀ i, a i = 2 * b i := red_zero_div_two hr
  have hxb : x = fun i => 4 * b i := by
    funext i
    rw [hx i, hab i]
    ring
  have hbs : squareSum b = 2 := by
    rw [hxb, scale_square] at hs
    norm_num at hs
    omega
  obtain ⟨hcard, hon⟩ := norm_two_shape hbs
  obtain ⟨σ, hσ⟩ := exists_signed (k := 1) (nzSupport b) b hon (by
    intro i hi
    simpa only [mem_nzSupport, not_not] using hi)
  refine ⟨⟨⟨nzSupport b, hcard⟩, σ⟩, ?_⟩
  funext i
  have he := congrFun hσ i
  have hx' := congrFun hxb i
  by_cases hi : i ∈ nzSupport b <;>
    simp [zeroVector, signed, hi] at he ⊢ <;> omega

private theorem classify_even_octad {x a : IntVector}
    (hx : ∀ i, x i = 2 * a i) (hc : red a ∈ code) (hn : red a ≠ 0)
    (hcong : (∑ i, x i) % 8 = 0) (hs : squareSum x = 32) :
    ∃ p : OctadFamily, octadVector p = x := by
  have hxa : x = fun i => 2 * a i := funext hx
  have has : squareSum a = 8 := by
    rw [hxa, scale_square] at hs
    norm_num at hs
    omega
  obtain ⟨hw, hshape⟩ := norm_eight_shape hc hn has
  let c : Octad := ⟨⟨red a, hc⟩, hw⟩
  let S := wordSupport (red a)
  have hS : S.card = 8 := by simp [S, hw]
  obtain ⟨σ, hσ⟩ := exists_signed (k := 1) S a (by
    intro i hi
    have hn : red a i ≠ 0 := (mem_wordSupport _ i).mp hi
    simpa [hn] using hshape i) (by
    intro i hi
    have hz : red a i = 0 := by simpa [S] using hi
    simpa [hz] using hshape i)
  have hvec : signed 2 S σ = x := by
    funext i
    have he := congrFun hσ i
    rw [hx i]
    by_cases hi : i ∈ S <;> simp [signed, hi] at he ⊢ <;> omega
  have hpar : ∑ i : S, σ i = 0 := by
    have hsum := signed_sum 2 S σ
    rw [hvec, hS] at hsum
    apply evenSigns_of_sum_div_two S σ
    have hdiv : 2 ∣ ∑ i : S, liftBit (σ i) := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      omega
    exact hdiv
  exact ⟨⟨c, ⟨σ, hpar⟩⟩, hvec⟩

/-- Exhaustive classification in the literal integer coordinates of the existing construction. -/
theorem familyVector_surjective_on_sphere (x : Sphere) :
    ∃ p : Families, familyVector p = x.val := by
  obtain ⟨m, hm, a, ha, hc, hsum⟩ := (representation code x.val).1 x.property.1
  rcases hm with rfl | rfl
  · have hx : ∀ i, x.val i = 2 * a i := by simpa using ha
    by_cases hn : red a = 0
    · obtain ⟨p, hp⟩ := classify_even_zero hx hn x.property.2
      exact ⟨.inl p, hp⟩
    · have hs : (∑ i, x.val i) % 8 = 0 := by simpa using hsum
      obtain ⟨p, hp⟩ := classify_even_octad hx hc hn hs x.property.2
      exact ⟨.inr (.inl p), hp⟩
  · have hp : ∀ i, x.val i % 2 = 1 := by intro i; have := ha i; omega
    have hq : red (fun i => (x.val i - 1) / 2) ∈ code := by
      have he : (fun i => (x.val i - 1) / 2) = a := by
        funext i; have := ha i; omega
      rwa [he]
    obtain ⟨p, hp⟩ := classify_odd hp hq x.property.2
    exact ⟨.inr (.inr p), hp⟩

private theorem familyVector_mem (p : Families) :
    Admissible code (familyVector p) ∧ squareSum (familyVector p) = 32 := by
  rcases p with p | p
  · exact ⟨zeroVector_mem p, zeroVector_square p⟩
  · rcases p with p | p
    · exact ⟨octadVector_mem p, octadVector_square p⟩
    · exact ⟨oddVector_mem p, oddVector_square p⟩

private theorem familyVector_injective : Function.Injective familyVector := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q
  · exact congrArg Sum.inl (zeroVector_injective h)
  · rcases q with q | q
    · exact False.elim (zero_ne_octad p q h)
    · exact False.elim (even_ne_odd (zeroVector_even p) q h)
  · rcases p with p | p
    · exact False.elim (zero_ne_octad q p h.symm)
    · exact False.elim (even_ne_odd (zeroVector_even q) p h.symm)
  · rcases p with p | p <;> rcases q with q | q
    · exact congrArg (fun v => Sum.inr (Sum.inl v)) (octadVector_injective h)
    · exact False.elim (even_ne_odd (octadVector_even p) q h)
    · exact False.elim (even_ne_odd (octadVector_even q) p h.symm)
    · exact congrArg (fun v => Sum.inr (Sum.inr v)) (oddVector_injective h)

/-- A finite, nonredundant parametrization, not a bounded surrogate sphere. -/
def sphereEquiv : Families ≃ Sphere := Equiv.ofBijective
  (fun p => ⟨familyVector p, familyVector_mem p⟩) (by
    constructor
    · intro p q h
      exact familyVector_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨p, hp⟩ := familyVector_surjective_on_sphere x
      exact ⟨p, Subtype.ext hp⟩)

private def twoSupportEquiv : TwoSupport ≃ ↥(Finset.univ.powersetCard 2 : Finset (Finset I)) where
  toFun S := ⟨S.val, by simp [S.property]⟩
  invFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv S := rfl
  right_inv S := rfl

private theorem zeroFamily_card : Fintype.card ZeroFamily = 1104 := by
  have hc : Fintype.card TwoSupport = 276 := by
    rw [Fintype.card_congr twoSupportEquiv, Fintype.card_coe, Finset.card_powersetCard]
    norm_num [Nat.choose_two_right]
  have hs : ∀ S : TwoSupport, Fintype.card (S.val → F2) = 4 := by
    intro S
    simp [Fintype.card_fun, S.property, ZMod.card]
  rw [Fintype.card_sigma]
  simp_rw [hs]
  simp [hc]

private theorem octadFamily_card : Fintype.card OctadFamily = 97152 := by
  have ho : Fintype.card Octad = 759 := by
    simpa using octad_card
  have hs : ∀ c : Octad, Fintype.card (EvenSigns (wordSupport (c.val : Word))) = 128 := by
    intro c
    apply evenSigns_card
    simpa using c.property
  rw [Fintype.card_sigma]
  simp_rw [hs]
  simp [ho]

private theorem oddFamily_card : Fintype.card OddFamily = 98304 := by
  have hc : Fintype.card code = 4096 := by simpa using code_card
  simp [OddFamily, hc]

/-- Finiteness is obtained from the explicit classification before using Nat.card. -/
theorem shortest_vectors_finite :
    Finite {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32} :=
  Finite.of_injective sphereEquiv.symm sphereEquiv.symm.injective

/-- The actual integer Golay Leech construction has exactly 196560 norm-32 vectors. -/
theorem shortest_vectors_card :
    Nat.card {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32} = 196560 := by
  rw [← Nat.card_congr sphereEquiv, Nat.card_eq_fintype_card]
  simp only [Families, Fintype.card_sum]
  rw [zeroFamily_card, octadFamily_card, oddFamily_card]

/-- The original rational scaling has squared length four exactly on this sphere. -/
def scaledSphereEquiv : Sphere ≃ {x : IntVector // Admissible code x ∧ scaledSquare x = 4} where
  toFun x := ⟨x.val, x.property.1, by norm_num [scaledSquare, x.property.2]⟩
  invFun x := ⟨x.val, x.property.1, by
    have h := x.property.2
    unfold scaledSquare at h
    have he : (squareSum x.val : ℚ) = 32 := by linarith
    exact_mod_cast he⟩
  left_inv x := rfl
  right_inv x := rfl

/-- Count at the existing squared-length-four scale, consuming the integer classification. -/
theorem scaled_shortest_vectors_finite_card :
    Finite {x : IntVector // Admissible code x ∧ scaledSquare x = 4} ∧
    Nat.card {x : IntVector // Admissible code x ∧ scaledSquare x = 4} = 196560 := by
  constructor
  · letI : Finite Sphere := shortest_vectors_finite
    exact Finite.of_injective scaledSphereEquiv.symm scaledSphereEquiv.symm.injective
  · rw [← Nat.card_congr scaledSphereEquiv]
    exact shortest_vectors_card

#print axioms shortest_vectors_card
#print axioms shortest_vectors_finite
#print axioms scaled_shortest_vectors_finite_card
end D5.S3.Arith.Lattices.Golay.LeechMinimalCount
