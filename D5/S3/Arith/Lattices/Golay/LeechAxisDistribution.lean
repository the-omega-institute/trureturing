/- GID: D5/S3/Arith/Lattices/Golay/LeechAxisDistribution
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/Golay/LeechAxisDistribution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate axis distribution on the actual unbounded integer Leech minimum sphere. -/

import D5.S3.Arith.Lattices.Golay.LeechMinimalCount
import D5.S3.Arith.Lattices.Golay.GolayOctadIncidence

/-! # Distribution at every two-coordinate Leech axis -/

set_option Elab.async false
set_option maxRecDepth 65536

open scoped BigOperators
noncomputable section
namespace D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
open GolayEncoder IntegerLeech GolayOctadCount LeechSignedSupport LeechMinimalCount
attribute [local instance] Classical.propDecidable
attribute [local instance 10] Fintype.ofFinite

private theorem bit_cases (a : F2) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have hh : a.val = 0 ∨ a.val = 1 := by omega
  rcases hh with h | h
  · left; apply ZMod.val_injective 2; simpa using h
  · right; apply ZMod.val_injective 2; change a.val = 1; exact h

private theorem sum_bits (f : F2 → ℕ) : ∑ b, f b = f 0 + f 1 := by
  have hu : (Finset.univ : Finset F2) = {0, 1} := by
    ext b; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact bit_cases b
  rw [hu]; simp

private theorem sum_fibers {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (g : B → ℕ) :
    (∑ a, g (f a)) = ∑ b, Nat.card {a // f a = b} * g b := by
  simpa only [Nat.card_eq_fintype_card, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
    (Fintype.sum_fiberwise' f g).symm

private theorem sum_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : A → ℕ) : (∑ a, f a) = ∑ b, f (e.symm b) := by
  exact (e.symm.sum_comp f).symm

private theorem code_pair_card (i j : I) (hij : i ≠ j) (a b : F2) :
    Nat.card {c : code // (c.val i, c.val j) = (a, b)} = 1024 := by
  have hf := pairProjection_surjective code all_ones_mem self_dual minimum_weight i j hij
  have he := AddMonoidHom.card_fiber_eq_of_mem_range (pairProjection code i j)
    (hf (a,b)) (hf (1,1))
  have hc := pair_fiber_card code code_card all_ones_mem self_dual minimum_weight i j hij
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter fun c : code => pairProjection code i j c = (a,b)).card = _
  rw [he]
  simpa only [pairProjection, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] using hc

private theorem fun_one_card {A : Type*} [Fintype A] (i : A) (a : F2) :
    Nat.card {f : A → F2 // f i = a} = 2 ^ (Fintype.card A - 1) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset F2) i (Finset.mem_univ a)

private theorem fun_pair_card {A : Type*} [Fintype A] (i j : A) (hij : i ≠ j) (a b : F2) :
    Nat.card {f : A → F2 // (f i, f j) = (a,b)} = 2 ^ (Fintype.card A - 2) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have he : (Finset.univ.filter fun f : A → F2 => (f i, f j) = (a,b)) =
      (Fintype.piFinset (Function.update (fun _ : A => (Finset.univ : Finset F2)) i {a})).filter
        (fun f => f j = b) := by
    rw [Fintype.piFinset_update_singleton_eq_filter_piFinset_eq (fun _ : A => (Finset.univ : Finset F2)) i (Finset.mem_univ a)]
    simp only [Fintype.piFinset_univ, Finset.filter_filter, Prod.mk.injEq]
  rw [he, Fintype.card_filter_piFinset_eq_of_mem
    (Function.update (fun _ : A => (Finset.univ : Finset F2)) i {a}) j (by simp [hij.symm])]
  have hp : (∏ k ∈ (Finset.univ : Finset A).erase j,
      (Function.update (fun _ : A => (Finset.univ : Finset F2)) i {a} k).card) =
      ∏ k ∈ ((Finset.univ : Finset A).erase j).erase i, (2 : ℕ) := by
    rw [← Finset.mul_prod_erase _ _ (show i ∈ (Finset.univ : Finset A).erase j by simp [hij])]
    simp only [Function.update_self, Finset.card_singleton, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [Function.update_of_ne hki, ZMod.card]
  rw [hp]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_erase_of_mem (show i ∈ (Finset.univ : Finset A).erase j by simp [hij]), Finset.card_univ]
  congr 1

private theorem pivot_away (S : Finset I) (hS : S.card = 8) (i j : S) :
    ∃ p : S, p ≠ i ∧ p ≠ j := by
  by_contra h
  push Not at h
  have hs : (Finset.univ : Finset S) ⊆ {i,j} := by
    intro k _
    have hk := h k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hc := Finset.card_le_card hs
  have hb : ({i,j} : Finset S).card ≤ 2 := Finset.card_le_two
  simp only [Finset.card_univ, Fintype.card_coe, hS] at hc
  omega

private theorem deleted_card (S : Finset I) (hS : S.card = 8) (p : S) :
    Fintype.card {i : S // i ≠ p} = 7 := by
  rw [Fintype.card_subtype_compl (fun i : S => i = p)]
  simp [hS]

private theorem even_one_card (S : Finset I) (hS : S.card = 8) (i : S) (a : F2) :
    Nat.card {σ : EvenSigns S // σ.val i = a} = 64 := by
  obtain ⟨p, hpi, _⟩ := pivot_away S hS i i
  let e := Equiv.subtypeEquiv (evenSignsEquiv S p)
    (p := fun σ => σ.val i = a)
    (q := fun τ => τ ⟨i, hpi.symm⟩ = a) (fun _ => Iff.rfl)
  rw [Nat.card_congr e, fun_one_card, deleted_card S hS p]
  norm_num

private theorem even_pair_card (S : Finset I) (hS : S.card = 8)
    (i j : S) (hij : i ≠ j) (a b : F2) :
    Nat.card {σ : EvenSigns S // (σ.val i, σ.val j) = (a,b)} = 32 := by
  obtain ⟨p, hpi, hpj⟩ := pivot_away S hS i j
  let e := Equiv.subtypeEquiv (evenSignsEquiv S p)
    (p := fun σ => (σ.val i, σ.val j) = (a,b))
    (q := fun τ => (τ ⟨i, hpi.symm⟩, τ ⟨j, hpj.symm⟩) = (a,b)) (fun _ => Iff.rfl)
  rw [Nat.card_congr e,
    fun_pair_card ⟨i, hpi.symm⟩ ⟨j, hpj.symm⟩
      (fun h => hij (congrArg Subtype.val h)), deleted_card S hS p]
  norm_num

private theorem signed_local {A : Type*} [Fintype A]
    (S : Finset I) (σ : A → S → F2) (k : ℤ) (n m l : ℕ)
    (hn : Fintype.card A = n)
    (hm : ∀ i a, Nat.card {x : A // σ x i = a} = m)
    (hl : ∀ i j, i ≠ j → ∀ a b, Nat.card {x : A // (σ x i, σ x j) = (a,b)} = l)
    (i j : I) (hij : i ≠ j) (t : ℤ) :
    (∑ x : A, if signed k S (σ x) i + signed k S (σ x) j = 2*t then 1 else 0) =
      if i ∈ S ∧ j ∈ S then
        l * ((if t = k then 1 else 0) + (if t = 0 then 2 else 0) + (if t = -k then 1 else 0))
      else if (i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S) then
        m * ((if 2*t = k then 1 else 0) + (if 2*t = -k then 1 else 0))
      else if t = 0 then n else 0 := by
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · let u : S := ⟨i,hi⟩
      let v : S := ⟨j,hj⟩
      have huv : u ≠ v := fun h => hij (congrArg Subtype.val h)
      simp only [hi, hj, and_self, ite_true]
      have he : (∑ x : A, if signed k S (σ x) i + signed k S (σ x) j = 2*t then 1 else 0) =
          ∑ x : A, (fun p : F2 × F2 => if k * sign p.1 + k * sign p.2 = 2*t then 1 else 0)
            (σ x u, σ x v) := by simp only [signed, hi, hj, dite_true]; rfl
      rw [he, sum_fibers (fun x : A => (σ x u, σ x v))
        (fun p : F2 × F2 => if k * sign p.1 + k * sign p.2 = 2*t then 1 else 0)]
      simp only [Fintype.sum_prod_type, hl u v huv, sum_bits, sign_zero, sign_one]
      split_ifs <;> omega
    · simp only [hi, hj, and_false, and_true, not_false_eq_true, not_true_eq_false,
        false_and, or_false, ite_false, ite_true, true_and]
      have he : (∑ x : A, if signed k S (σ x) i + signed k S (σ x) j = 2*t then 1 else 0) =
          ∑ x : A, (fun b : F2 => if k * sign b = 2*t then 1 else 0) (σ x ⟨i,hi⟩) := by
        simp only [signed, hi, hj, dite_true, dite_false, add_zero]
      rw [he, sum_fibers (fun x : A => σ x ⟨i,hi⟩)
        (fun b : F2 => if k * sign b = 2*t then 1 else 0)]
      simp only [hm, sum_bits, sign_zero, sign_one]
      split_ifs <;> omega
  · by_cases hj : j ∈ S
    · simp only [hi, hj, and_false, and_true, not_false_eq_true, not_true_eq_false,
        false_and, or_true, ite_false, ite_true, true_and]
      have he : (∑ x : A, if signed k S (σ x) i + signed k S (σ x) j = 2*t then 1 else 0) =
          ∑ x : A, (fun b : F2 => if k * sign b = 2*t then 1 else 0) (σ x ⟨j,hj⟩) := by
        simp only [signed, hi, hj, dite_true, dite_false, zero_add]
      rw [he, sum_fibers (fun x : A => σ x ⟨j,hj⟩)
        (fun b : F2 => if k * sign b = 2*t then 1 else 0)]
      simp only [hm, sum_bits, sign_zero, sign_one]
      split_ifs <;> omega
    · simp only [signed, hi, hj, dite_false, add_zero, not_false_eq_true,
        false_and, and_false, or_false, ite_false]
      by_cases ht : t = 0
      · simp [ht, hn]
      · have ht' : ¬ (0 : ℤ) = 2*t := by omega
        simp [ht, ht']

private theorem occupancy_sum {A : Type*} [Fintype A] (S : A → Finset I)
    (i j : I) (b c d : ℕ) :
    (∑ x, if i ∈ S x ∧ j ∈ S x then b
      else if (i ∈ S x ∧ j ∉ S x) ∨ (i ∉ S x ∧ j ∈ S x) then c else d) =
    (Finset.univ.filter fun x => i ∈ S x ∧ j ∈ S x).card * b +
    (Finset.univ.filter fun x =>
      (i ∈ S x ∧ j ∉ S x) ∨ (i ∉ S x ∧ j ∈ S x)).card * c +
    (Finset.univ.filter fun x => i ∉ S x ∧ j ∉ S x).card * d := by
  have he (x : A) :
      (if i ∈ S x ∧ j ∈ S x then b
        else if (i ∈ S x ∧ j ∉ S x) ∨ (i ∉ S x ∧ j ∈ S x) then c else d) =
      (if i ∈ S x ∧ j ∈ S x then b else 0) +
      (if (i ∈ S x ∧ j ∉ S x) ∨ (i ∉ S x ∧ j ∈ S x) then c else 0) +
      (if i ∉ S x ∧ j ∉ S x then d else 0) := by
    by_cases hi : i ∈ S x <;> by_cases hj : j ∈ S x <;> simp [hi,hj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

private def supportEquiv : TwoSupport ≃ ↥(Finset.univ.powersetCard 2 : Finset (Finset I)) where
  toFun S := ⟨S.val, by simp [S.property]⟩
  invFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem two_support_incidence (i j : I) (hij : i ≠ j) :
    (Finset.univ.filter fun S : TwoSupport => i ∈ S.val ∧ j ∈ S.val).card = 1 ∧
    (Finset.univ.filter fun S : TwoSupport =>
      (i ∈ S.val ∧ j ∉ S.val) ∨ (i ∉ S.val ∧ j ∈ S.val)).card = 44 ∧
    (Finset.univ.filter fun S : TwoSupport => i ∉ S.val ∧ j ∉ S.val).card = 231 := by
  have hc : Fintype.card TwoSupport = 276 := by
    rw [Fintype.card_congr supportEquiv, Fintype.card_coe, Finset.card_powersetCard]
    norm_num [Nat.choose_two_right]
  have count (T : Finset I) (hT : T.card ≤ 2) :
      (Finset.univ.filter fun S : TwoSupport => T ⊆ S.val).card =
        Nat.choose (24 - T.card) (2 - T.card) := by
    have he := supportEquiv.sum_comp
      (fun S => if T ⊆ S.val then (1 : ℕ) else 0)
    change (∑ S : TwoSupport, if T ⊆ S.val then (1 : ℕ) else 0) =
      ∑ S : ↥(Finset.univ.powersetCard 2 : Finset (Finset I)),
        if T ⊆ S.val then (1 : ℕ) else 0 at he
    rw [← Finset.card_filter] at he
    rw [← he]
    rw [← Finset.sum_subtype (Finset.univ.powersetCard 2 : Finset (Finset I))
      (fun _ => Iff.rfl) (fun S => if T ⊆ S then (1 : ℕ) else 0), ← Finset.card_filter,
      Finset.card_filter_powersetCard_subset T _ 2 (Finset.subset_univ _) hT]
    simp
  have hi := count {i} (by simp)
  have hj := count {j} (by simp)
  have hp := count {i,j} (by simp [hij])
  norm_num [hij, Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.choose] at hi hj hp
  have part (S : TwoSupport) :
      (if i ∈ S.val then (1 : ℕ) else 0) + (if j ∈ S.val then 1 else 0) =
      2 * (if i ∈ S.val ∧ j ∈ S.val then 1 else 0) +
      (if (i ∈ S.val ∧ j ∉ S.val) ∨ (i ∉ S.val ∧ j ∈ S.val) then 1 else 0) := by
    by_cases h : i ∈ S.val <;> by_cases k : j ∈ S.val <;> simp [h,k]
  have part' (S : TwoSupport) : (1 : ℕ) =
      (if i ∈ S.val ∧ j ∈ S.val then 1 else 0) +
      (if (i ∈ S.val ∧ j ∉ S.val) ∨ (i ∉ S.val ∧ j ∈ S.val) then 1 else 0) +
      (if i ∉ S.val ∧ j ∉ S.val then 1 else 0) := by
    by_cases h : i ∈ S.val <;> by_cases k : j ∈ S.val <;> simp [h,k]
  have hx := Finset.sum_congr (s₁ := (Finset.univ : Finset TwoSupport)) rfl (fun S _ => part S)
  have hn := Finset.sum_congr (s₁ := (Finset.univ : Finset TwoSupport)) rfl (fun S _ => part' S)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter, hi, hj, hp] at hx
  simp only [Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, hc, hp] at hn
  exact ⟨hp, by omega, by omega⟩

private theorem zero_count (i j : I) (hij : i ≠ j) (t : ℤ) :
    (∑ p : ZeroFamily, if zeroVector p i + zeroVector p j = 2*t then 1 else 0) =
    (if t = 4 ∨ t = -4 then 1 else 0) +
    (if t = 2 ∨ t = -2 then 88 else 0) + (if t = 0 then 926 else 0) := by
  have hs (S : TwoSupport) := signed_local S.val (fun σ : S.val → F2 => σ) 4 4 2 1
    (by simp [Fintype.card_fun, S.property, ZMod.card])
    (fun u a => by rw [fun_one_card]; simp [S.property])
    (fun u v huv a b => by rw [fun_pair_card u v huv]; simp [S.property]) i j hij t
  change (∑ p : (S : TwoSupport) × (S.val → F2), _) = _
  rw [Fintype.sum_sigma]
  simp only [zeroVector] at *
  simp_rw [hs]
  rw [occupancy_sum]
  obtain ⟨hb,ho,hn⟩ := two_support_incidence i j hij
  rw [hb,ho,hn]
  split_ifs <;> omega

private theorem octad_count (i j : I) (hij : i ≠ j) (t : ℤ) :
    (∑ p : OctadFamily, if octadVector p i + octadVector p j = 2*t then 1 else 0) =
    (if t = 2 ∨ t = -2 then 2464 else 0) +
    (if t = 1 ∨ t = -1 then 22528 else 0) + (if t = 0 then 47168 else 0) := by
  have hs (c : Octad) := signed_local (wordSupport (c.val : Word))
    (fun σ : EvenSigns (wordSupport (c.val : Word)) => σ.val) 2 128 64 32
    (evenSigns_card _ (by simpa using c.property))
    (even_one_card _ (by simpa using c.property))
    (even_pair_card _ (by simpa using c.property)) i j hij t
  change (∑ p : (c : Octad) × EvenSigns (wordSupport (c.val : Word)), _) = _
  rw [Fintype.sum_sigma]
  simp only [octadVector] at *
  simp_rw [hs]
  rw [occupancy_sum]
  obtain ⟨_,_,hb,ho,hn⟩ := GolayOctadIncidence.coordinate_incidence i j hij
  rw [hb,ho,hn]
  split_ifs <;> omega

private theorem odd_local (i j k : I) (hij : i ≠ j) (t : ℤ) :
    (∑ c : code, if oddVector (k,c) i + oddVector (k,c) j = 2*t then 1 else 0) =
      if k = i ∨ k = j then
        (if t = 2 ∨ t = -2 then 1024 else 0) + (if t = 1 ∨ t = -1 then 1024 else 0)
      else (if t = 1 ∨ t = -1 then 1024 else 0) + (if t = 0 then 2048 else 0) := by
  have hs := sum_fibers (fun c : code => (c.val i, c.val j))
    (fun p : F2 × F2 => if
      (sign p.1 + if i = k then -4 * sign p.1 else 0) +
      (sign p.2 + if j = k then -4 * sign p.2 else 0) = 2*t then 1 else 0)
  change (∑ c : code, if oddVector (k,c) i + oddVector (k,c) j = 2*t then 1 else 0) = _ at hs
  rw [hs]
  simp only [Fintype.sum_prod_type, code_pair_card i j hij, sum_bits, sign_zero, sign_one]
  by_cases hki : k = i
  · subst k
    simp only [hij, Ne.symm hij, ite_true, ite_false, true_or]
    split_ifs <;> omega
  · by_cases hkj : k = j
    · subst k
      simp only [hij, Ne.symm hij, ite_true, ite_false, or_true]
      split_ifs <;> omega
    · simp only [Ne.symm hki, Ne.symm hkj, hki, hkj, false_or, ite_false]
      split_ifs <;> omega

end D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
