/- GID: D5/S3/ObserverMemory/NonlinearSelectorProfile
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/NonlinearSelectorProfile
   mirror-E: none(waiver:exact-finite-word-profile)
   anchors: []
   utility: none
   digest: Preparation prefixes in the literal binary selector relation have distinct completion residuals. -/

import D5.S3.ObserverMemory.StrictAnchoredBoundary
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ObserverMemory.NonlinearSelectorProfile
open StrictAnchoredBoundary

def selectorRelation (m : Nat) : Set (List Bool) :=
  {w | ∃ i j : List Bool, i.length = m ∧ j.length = m ∧
    (w = i ++ j ++ [false] ++ i ∨ w = i ++ j ++ [true] ++ j)}

private theorem fixed_length (m : Nat) :
    ∀ w ∈ selectorRelation m, w.length = 3 * m + 1 := by
  rintro w ⟨i,j,hi,hj,h | h⟩ <;> subst w <;>
    simp only [List.length_append, List.length_singleton, hi, hj] <;> omega

private theorem relation_nonempty (m : Nat) : (selectorRelation m).Nonempty := by
  let i := List.replicate m false
  exact ⟨i ++ i ++ [false] ++ i, i, i, by simp [i], by simp [i], Or.inl rfl⟩

private theorem selector_test (m : Nat) (p x : List Bool) (b : Bool)
    (hp : p.length = 2 * m) :
    p ++ [b] ++ x ∈ selectorRelation m ↔
      x = if b then p.drop m else p.take m := by
  constructor
  · rintro ⟨i,j,hi,hj,h | h⟩
    · have hlen : p.length = (i ++ j).length := by simp [hp, hi, hj]; omega
      have he := List.append_inj (by simpa only [List.append_assoc] using h :
        p ++ ([b] ++ x) = (i ++ j) ++ ([false] ++ i)) hlen
      have ht : b = false ∧ x = i := by simpa using he.2
      rw [ht.1, he.1]
      simpa [hi] using ht.2
    · have hlen : p.length = (i ++ j).length := by simp [hp, hi, hj]; omega
      have he := List.append_inj (by simpa only [List.append_assoc] using h :
        p ++ ([b] ++ x) = (i ++ j) ++ ([true] ++ j)) hlen
      have ht : b = true ∧ x = j := by simpa using he.2
      rw [ht.1, he.1]
      simpa [hi] using ht.2
  · intro hx
    have hi : (p.take m).length = m := by simp [hp]; omega
    have hj : (p.drop m).length = m := by simp [hp]; omega
    refine ⟨p.take m, p.drop m, hi, hj, ?_⟩
    rw [List.take_append_drop]
    cases b <;> simp_all

/-- Unequal preparation prefixes admit a common supplied completion that is
accepted from the first prefix and rejected from the second. -/
private theorem preparation_separation (m k : Nat) (hk : k ≤ 2 * m)
    (u v : List Bool) (hu : u.length = k) (hv : v.length = k) (hne : u ≠ v) :
    ∃ f : List Bool, u ++ f ∈ selectorRelation m ∧ v ++ f ∉ selectorRelation m := by
  let z := List.replicate (2 * m - k) false
  let p := u ++ z
  let q := v ++ z
  have hp : p.length = 2 * m := by simp [p, z, hu]; omega
  have hq : q.length = 2 * m := by simp [q, z, hv]; omega
  have hpq : p ≠ q := by
    intro he
    exact hne (List.append_cancel_right he)
  by_cases ht : p.take m = q.take m
  · have hd : p.drop m ≠ q.drop m := by
      intro he
      apply hpq
      rw [← List.take_append_drop m p, ← List.take_append_drop m q, ht, he]
    refine ⟨z ++ [true] ++ p.drop m, ?_, ?_⟩
    · simpa [p, List.append_assoc] using
        (selector_test m p (p.drop m) true hp).mpr (by simp)
    · intro he
      have he' : q ++ [true] ++ p.drop m ∈ selectorRelation m := by
        simpa [q, List.append_assoc] using he
      exact hd (by simpa using (selector_test m q (p.drop m) true hq).mp he')
  · refine ⟨z ++ [false] ++ p.take m, ?_, ?_⟩
    · simpa [p, List.append_assoc] using
        (selector_test m p (p.take m) false hp).mpr (by simp)
    · intro he
      have he' : q ++ [false] ++ p.take m ∈ selectorRelation m := by
        simpa [q, List.append_assoc] using he
      exact ht (by simpa using (selector_test m q (p.take m) false hq).mp he')

private theorem preparation_actual (m k : Nat) (hk : k ≤ 2 * m)
    (u : List Bool) (hu : u.length = k) :
    ∃ f, u ++ f ∈ selectorRelation m := by
  let z := List.replicate (2 * m - k) false
  have hp : (u ++ z).length = 2 * m := by simp [z, hu]; omega
  refine ⟨z ++ [false] ++ (u ++ z).take m, ?_⟩
  simpa [List.append_assoc] using
    (selector_test m (u ++ z) ((u ++ z).take m) false hp).mpr (by simp)

/-- Every preparation cut has exactly one distinct actual residual per binary
word of its length, including the empty cut and both complete blocks. -/
private theorem preparation_profile (m k : Nat) (hk : k ≤ 2 * m) :
    (residualSet (selectorRelation m) k).Finite ∧
    Nat.card (residualSet (selectorRelation m) k) = 2 ^ k := by
  classical
  let f : List.Vector Bool k → residualSet (selectorRelation m) k :=
    fun u => ⟨residual (selectorRelation m) u.val,
      u.val, u.property, preparation_actual m k hk u.val u.property, rfl⟩
  have hinj : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    by_contra hne
    obtain ⟨w, hw, hn⟩ := preparation_separation m k hk u.val v.val u.property v.property hne
    have hr : residual (selectorRelation m) u.val = residual (selectorRelation m) v.val :=
      congrArg Subtype.val he
    have hm : w ∈ residual (selectorRelation m) u.val := hw
    rw [hr] at hm
    exact hn hm
  have hsurj : Function.Surjective f := by
    rintro ⟨S,u,hu,ha,he⟩
    exact ⟨⟨u,hu⟩, Subtype.ext he⟩
  let e := Equiv.ofBijective f ⟨hinj,hsurj⟩
  have hf : Finite (residualSet (selectorRelation m) k) := Finite.of_equiv _ e
  letI := hf
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_vector]
  simp

private theorem words_card (k : Nat) :
    Nat.card {u : List Bool // u.length = k} = 2 ^ k := by
  change Nat.card (List.Vector Bool k) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  simp

private theorem preparation_tails (m k : Nat) (hk : k ≤ 2 * m) (hpos : 1 ≤ k)
    (S : residualSet (selectorRelation m) (k-1)) :
    pref S.val 1 = {t : List Bool | t.length = 1} := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    change t.length = 1 at ht
    obtain ⟨v,hv,_,he⟩ := S.property
    have hvt : (v ++ t).length = k := by simp [hv,ht]; omega
    obtain ⟨f,hf⟩ := preparation_actual m k hk (v ++ t) hvt
    refine ⟨ht,f,?_⟩
    rw [← he]
    simpa [StrictAnchoredBoundary.residual,List.append_assoc] using hf

/-- The preparation one-credit count is the full prefix count. -/
private theorem preparation_one_credit (m k : Nat) (hpos : 1 ≤ k) (hk : k ≤ 2 * m) :
    (image (selectorRelation m) (k,1)).Finite ∧
    Nat.card (image (selectorRelation m) (k,1)) = 2 ^ k := by
  classical
  have hs := strict_anchored_specialization (3*m+1) (selectorRelation m)
    (fixed_length m) (relation_nonempty m) k 1 hpos (by omega)
  obtain ⟨inst,hcount⟩ := hs.2.2.2.1
  letI := inst
  have htail : ∀ S : residualSet (selectorRelation m) (k-1),
      Nat.card (pref S.val 1) = 2 := by
    intro S
    rw [preparation_tails m k hk hpos S]
    change Nat.card {t : List Bool // t.length = 1} = 2
    norm_num [words_card]
  have himfinite : (image (selectorRelation m) (k,1)).Finite := by
    rw [hs.2.2.1]
    apply ((preparation_profile m (k-1) (by omega)).1.prod
      (List.finite_length_eq Bool 1)).subset
    exact fun b hb => ⟨hb.1,hb.2.1⟩
  refine ⟨himfinite,?_⟩
  rw [hcount]
  simp only [htail,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, (preparation_profile m (k-1) (by omega)).2]
  have he : k = (k-1)+1 := by omega
  conv_rhs => rw [he, pow_succ]

private theorem preceding_residual (m : Nat) (i j : List Bool)
    (hi : i.length = m) (hj : j.length = m) :
    residual (selectorRelation m) (i ++ j) = {false :: i, true :: j} := by
  ext f
  constructor
  · rintro ⟨i',j',hi',hj',h | h⟩
    · have he := List.append_inj (by simpa only [List.append_assoc] using h :
        (i ++ j) ++ f = (i' ++ j') ++ ([false] ++ i')) (by simp [hi,hj,hi',hj'])
      have hij := List.append_inj he.1 (hi.trans hi'.symm)
      simpa [hij.1,he.2]
    · have he := List.append_inj (by simpa only [List.append_assoc] using h :
        (i ++ j) ++ f = (i' ++ j') ++ ([true] ++ j')) (by simp [hi,hj,hi',hj'])
      have hij := List.append_inj he.1 (hi.trans hi'.symm)
      simpa [hij.2,he.2]
  · intro hf
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hf
    rcases hf with hf | hf
    · exact ⟨i,j,hi,hj,Or.inl (by simp [hf,List.append_assoc])⟩
    · exact ⟨i,j,hi,hj,Or.inr (by simp [hf,List.append_assoc])⟩

private theorem preceding_residuals (m : Nat) :
    residualSet (selectorRelation m) (2*m) =
    Set.range (fun ij : List.Vector Bool m × List.Vector Bool m =>
      ({false :: ij.1.val, true :: ij.2.val} : Set (List Bool))) := by
  ext S
  constructor
  · rintro ⟨u,hu,_,he⟩
    have hi : (u.take m).length = m := by simp [hu]; omega
    have hj : (u.drop m).length = m := by simp [hu]; omega
    refine ⟨(⟨u.take m,hi⟩,⟨u.drop m,hj⟩),?_⟩
    change {false :: u.take m, true :: u.drop m} = S
    rw [← preceding_residual m _ _ hi hj, List.take_append_drop,he]
  · rintro ⟨⟨i,j⟩,rfl⟩
    refine ⟨i.val ++ j.val,by simp [i.property,j.property]; omega,
      preparation_actual m (2*m) le_rfl _ (by simp [i.property,j.property]; omega),
      preceding_residual m _ _ i.property j.property⟩

/-- At the selector the actual image consists precisely of both supplied bits
paired with each realized two-branch predecessor residual. -/
private theorem selector_image (m : Nat) :
    image (selectorRelation m) (2*m+1,1) =
      Set.range (fun p : (List.Vector Bool m × List.Vector Bool m) × Bool =>
        (({false :: p.1.1.val, true :: p.1.2.val} : Set (List Bool)),[p.2])) := by
  classical
  have hs := strict_anchored_specialization (3*m+1) (selectorRelation m)
    (fixed_length m) (relation_nonempty m) (2*m+1) 1 (by omega) (by omega)
  rw [hs.2.2.1]
  have hsub : 2*m+1-1 = 2*m := by omega
  rw [hsub, preceding_residuals]
  ext b
  constructor
  · rintro ⟨⟨⟨i,j⟩,he⟩,ht,ha⟩
    obtain ⟨a,ha'⟩ := List.length_eq_one_iff.mp ht
    exact ⟨((i,j),a),Prod.ext he ha'.symm⟩
  · rintro ⟨⟨⟨i,j⟩,a⟩,rfl⟩
    refine ⟨⟨(i,j),rfl⟩,by simp,?_⟩
    cases a
    · exact ⟨i.val,by simp⟩
    · exact ⟨j.val,by simp⟩

private theorem selector_pair_injective (m : Nat) :
    Function.Injective (fun p : (List.Vector Bool m × List.Vector Bool m) × Bool =>
      (({false :: p.1.1.val, true :: p.1.2.val} : Set (List Bool)),[p.2])) := by
  intro p q he
  have hs : ({false :: p.1.1.val,true :: p.1.2.val} : Set (List Bool)) =
      {false :: q.1.1.val,true :: q.1.2.val} := congrArg Prod.fst he
  have hb : [p.2] = [q.2] := congrArg Prod.snd he
  have hi : p.1.1.val = q.1.1.val := by
    have h : false :: p.1.1.val ∈ ({false :: q.1.1.val,true :: q.1.2.val} : Set (List Bool)) := by
      rw [← hs]; simp
    simpa using h
  have hj : p.1.2.val = q.1.2.val := by
    have h : true :: p.1.2.val ∈ ({false :: q.1.1.val,true :: q.1.2.val} : Set (List Bool)) := by
      rw [← hs]; simp
    simpa using h
  exact Prod.ext (Prod.ext (Subtype.ext hi) (Subtype.ext hj)) (by simpa using hb)

private theorem selector_count (m : Nat) :
    (image (selectorRelation m) (2*m+1,1)).Finite ∧
    Nat.card (image (selectorRelation m) (2*m+1,1)) = 2 * (2^m)^2 := by
  rw [selector_image]
  refine ⟨Set.finite_range _,?_⟩
  rw [Nat.card_range_of_injective (selector_pair_injective m)]
  simp [Nat.card_prod, Nat.card_eq_fintype_card, card_vector, pow_two]
  <;> ring

private theorem postcopy_singleton (m ell : Nat)
    (u f : List Bool) (hu : u.length = 2*m+1+ell)
    (hf : u ++ f ∈ selectorRelation m) :
    residual (selectorRelation m) u = {f} := by
  let p := u.take (2*m)
  have hp : p.length = 2*m := by simp [p,hu]; omega
  have hz : 0 < (u.drop (2*m)).length := by simp [hu]; omega
  obtain ⟨b,t,ht⟩ := List.exists_cons_of_length_pos hz
  have hu' : u = p ++ [b] ++ t := by
    simpa [p,ht,List.append_assoc] using (List.take_append_drop (2*m) u).symm
  have hft : t ++ f = if b then p.drop m else p.take m := by
    apply (selector_test m p (t ++ f) b hp).mp
    simpa [hu',List.append_assoc] using hf
  ext g
  constructor
  · intro hg
    have hgt : t ++ g = if b then p.drop m else p.take m := by
      apply (selector_test m p (t ++ g) b hp).mp
      simpa [StrictAnchoredBoundary.residual,hu',List.append_assoc] using hg
    exact List.append_cancel_left (hgt.trans hft.symm)
  · intro hg
    change g = f at hg
    subst g
    exact hf

private theorem postcopy_residuals (m ell : Nat) (hell : ell ≤ m) :
    residualSet (selectorRelation m) (2*m+1+ell) =
      Set.range (fun r : List.Vector Bool (m-ell) => ({r.val} : Set (List Bool))) := by
  ext S
  constructor
  · rintro ⟨u,hu,⟨f,hf⟩,he⟩
    have hn := fixed_length m (u ++ f) hf
    have hlen : f.length = m-ell := by simp only [List.length_append,hu] at hn; omega
    refine ⟨⟨f,hlen⟩,?_⟩
    change {f} = S
    rw [← postcopy_singleton m ell u f hu hf,he]
  · rintro ⟨r,rfl⟩
    let t := List.replicate ell false
    let i := t ++ r.val
    let j := List.replicate m false
    let u := i ++ j ++ [false] ++ t
    have hi : i.length = m := by simp [i,t,r.property]; omega
    have hj : j.length = m := by simp [j]
    have hu : u.length = 2*m+1+ell := by simp [u,hi,hj,t]; omega
    have hf : u ++ r.val ∈ selectorRelation m := by
      refine ⟨i,j,hi,hj,Or.inl ?_⟩
      simp [u,i,List.append_assoc]
    exact ⟨u,hu,⟨r.val,hf⟩,postcopy_singleton m ell u r.val hu hf⟩

private theorem singleton_word_injective (k : Nat) :
    Function.Injective (fun r : List.Vector Bool k => ({r.val} : Set (List Bool))) := by
  intro r s he
  apply Subtype.ext
  have hm : r.val ∈ ({s.val} : Set (List Bool)) := by
    change ({r.val} : Set (List Bool)) = {s.val} at he
    rw [← he]; simp
  simpa using hm

private theorem postcopy_count (m ell : Nat) (hell : ell ≤ m) :
    (residualSet (selectorRelation m) (2*m+1+ell)).Finite ∧
    Nat.card (residualSet (selectorRelation m) (2*m+1+ell)) = 2^(m-ell) := by
  rw [postcopy_residuals m ell hell]
  refine ⟨Set.finite_range _,?_⟩
  rw [Nat.card_range_of_injective (singleton_word_injective _),
    Nat.card_eq_fintype_card,card_vector]
  simp

private theorem postcopy_image (m ell : Nat) (hpos : 1 ≤ ell) (hell : ell ≤ m) :
    image (selectorRelation m) (2*m+1+ell,1) =
      Set.range (fun ar : Bool × List.Vector Bool (m-ell) =>
        (({ar.1 :: ar.2.val} : Set (List Bool)),[ar.1])) := by
  classical
  have hs := strict_anchored_specialization (3*m+1) (selectorRelation m)
    (fixed_length m) (relation_nonempty m) (2*m+1+ell) 1 (by omega) (by omega)
  have hcut : 2*m+1+ell-1 = 2*m+1+(ell-1) := by omega
  have hlen : m-(ell-1) = (m-ell)+1 := by omega
  rw [hs.2.2.1,hcut,postcopy_residuals m (ell-1) (by omega)]
  ext b
  constructor
  · rintro ⟨⟨w,hw⟩,ht,⟨f,hf⟩⟩
    obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp ht
    have he : b.2 ++ f = w.val := by simpa [← hw] using hf
    have hflen : f.length = m-ell := by
      have hh := congrArg List.length he
      simp only [List.length_append,ht,w.property,hlen] at hh
      omega
    refine ⟨(a,⟨f,hflen⟩),?_⟩
    change ({a :: f},[a]) = b
    apply Prod.ext
    · change {a :: f} = b.1
      change ({w.val} : Set (List Bool)) = b.1 at hw
      rw [← hw,← he,ha]
      rfl
    · exact ha.symm
  · rintro ⟨⟨a,r⟩,rfl⟩
    refine ⟨⟨⟨a :: r.val,by simp [r.property,hlen]⟩,rfl⟩,by simp,?_⟩
    exact ⟨r.val,by simp⟩

private theorem copy_pair_injective (k : Nat) :
    Function.Injective (fun ar : Bool × List.Vector Bool k =>
      (({ar.1 :: ar.2.val} : Set (List Bool)),[ar.1])) := by
  intro p q he
  have hb : p.1 = q.1 := by simpa using congrArg Prod.snd he
  have hs : ({p.1 :: p.2.val} : Set (List Bool)) = {q.1 :: q.2.val} :=
    congrArg Prod.fst he
  have hr : p.2.val = q.2.val := by
    have hm : p.1 :: p.2.val ∈ ({q.1 :: q.2.val} : Set (List Bool)) := by
      rw [← hs]; simp
    simpa [hb] using hm
  exact Prod.ext hb (Subtype.ext hr)

private theorem postcopy_one_count (m ell : Nat) (hpos : 1 ≤ ell) (hell : ell ≤ m) :
    (image (selectorRelation m) (2*m+1+ell,1)).Finite ∧
    Nat.card (image (selectorRelation m) (2*m+1+ell,1)) = 2^(m-ell+1) := by
  rw [postcopy_image m ell hpos hell]
  refine ⟨Set.finite_range _,?_⟩
  rw [Nat.card_range_of_injective (copy_pair_injective _)]
  simp [Nat.card_eq_fintype_card,card_vector,pow_succ,Nat.mul_comm]

private theorem zero_credit_count (m k : Nat) (hk : k ≤ 3*m+1) :
    (image (selectorRelation m) (k,0)).Finite ∧
    Nat.card (image (selectorRelation m) (k,0)) =
      Nat.card (residualSet (selectorRelation m) k) := by
  classical
  have hs := strict_anchored_specialization (3*m+1) (selectorRelation m)
    (fixed_length m) (relation_nonempty m) k 0 (by omega) hk
  obtain ⟨inst,hcount⟩ := hs.2.2.2.1
  simp only [Nat.sub_zero] at inst hcount
  letI := inst
  have htail : ∀ S : residualSet (selectorRelation m) k, pref S.val 0 = {[]} := by
    intro S
    ext t
    constructor
    · intro ht
      exact List.length_eq_zero_iff.mp ht.1
    · intro ht
      change t = [] at ht
      subst t
      obtain ⟨v,hv,⟨f,hf⟩,he⟩ := S.property
      refine ⟨rfl,f,?_⟩
      rw [← he]
      exact hf
  have himfinite : (image (selectorRelation m) (k,0)).Finite := by
    rw [hs.2.2.1]
    simp only [Nat.sub_zero]
    apply ((Set.toFinite (residualSet (selectorRelation m) k)).prod
      (List.finite_length_eq Bool 0)).subset
    exact fun b hb => ⟨hb.1,hb.2.1⟩
  refine ⟨himfinite,?_⟩
  rw [hcount]
  simp only [htail,Nat.card_unique,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,Nat.mul_one,Nat.card_eq_fintype_card]

noncomputable def forwardPeak (m : Nat) : Nat :=
  (Finset.range (3*m+2)).sup (fun k => Nat.card (residualSet (selectorRelation m) k))

noncomputable def oneCreditPeak (m : Nat) : Nat :=
  (Finset.range (3*m+2)).sup (fun k =>
    (Finset.range (min 1 k + 1)).sup (fun d => Nat.card (image (selectorRelation m) (k,d))))

private theorem forward_bound (m k : Nat) (hk : k ≤ 3*m+1) :
    Nat.card (residualSet (selectorRelation m) k) ≤ (2^m)^2 := by
  have hpow : (2^m)^2 = 2^(2*m) := by rw [← pow_mul]; congr 1; omega
  rw [hpow]
  by_cases hp : k ≤ 2*m
  · rw [(preparation_profile m k hp).2]
    exact Nat.pow_le_pow_right (by decide) hp
  · have he : k = 2*m+1+(k-(2*m+1)) := by omega
    rw [he,(postcopy_count m (k-(2*m+1)) (by omega)).2]
    apply Nat.pow_le_pow_right (by decide)
    omega

private theorem peaks (m : Nat) :
    forwardPeak m = (2^m)^2 ∧ oneCreditPeak m = 2*(2^m)^2 := by
  classical
  have hforward : forwardPeak m = (2^m)^2 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro k hk
      exact forward_bound m k (by have ht := Finset.mem_range.mp hk; omega)
    · have h := Finset.le_sup (f := fun k => Nat.card (residualSet (selectorRelation m) k))
        (show 2*m ∈ Finset.range (3*m+2) by simp; omega)
      rw [(preparation_profile m (2*m) le_rfl).2] at h
      simpa [forwardPeak,pow_mul,Nat.mul_comm] using h
  refine ⟨hforward,?_⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    have hk' : k ≤ 3*m+1 := by have ht := Finset.mem_range.mp hk; omega
    apply Finset.sup_le
    intro d hd
    have hd' : d ≤ min 1 k := by have ht := Finset.mem_range.mp hd; omega
    have hd1 : d ≤ 1 := le_trans hd' (Nat.min_le_left _ _)
    have hdk : d ≤ k := le_trans hd' (Nat.min_le_right _ _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with rfl | rfl
    · rw [(zero_credit_count m k hk').2]
      exact (forward_bound m k hk').trans (by omega)
    · by_cases hp : k ≤ 2*m
      · rw [(preparation_one_credit m k hdk hp).2]
        have h := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
        have he : 2^(2*m) = (2^m)^2 := by rw [← pow_mul]; congr 1; omega
        rw [he] at h
        omega
      · by_cases he : k = 2*m+1
        · subst k
          exact le_of_eq (selector_count m).2
        · have hcut : k = 2*m+1+(k-(2*m+1)) := by omega
          rw [hcut,(postcopy_one_count m (k-(2*m+1)) (by omega) (by omega)).2]
          have hp := Nat.pow_le_pow_right (show 0 < 2 by decide)
            (show m-(k-(2*m+1))+1 ≤ 2*m+1 by omega)
          have he : 2^(2*m+1) = 2*(2^m)^2 := by rw [pow_succ,← pow_mul]; ring
          rw [he] at hp
          exact hp
  · have hk : 2*m+1 ∈ Finset.range (3*m+2) := by simp; omega
    have hd : 1 ∈ Finset.range (min 1 (2*m+1)+1) := by simp
    have h1 := Finset.le_sup (f := fun d => Nat.card (image (selectorRelation m) (2*m+1,d))) hd
    have h2 := Finset.le_sup (f := fun k =>
      (Finset.range (min 1 k+1)).sup (fun d => Nat.card (image (selectorRelation m) (k,d)))) hk
    rw [(selector_count m).2] at h1
    exact h1.trans h2

/-- The complete full-carrier selector-family profile, conditional on the
supplied public type, includes zero credit and every endpoint. -/
theorem exact_selector_family_profile (m : Nat) (hm : 1 ≤ m) :
    (∀ w ∈ selectorRelation m, w.length = 3*m+1) ∧
    (selectorRelation m).Nonempty ∧ (selectorRelation m).Finite ∧
    (∀ k, k ≤ 2*m →
      (residualSet (selectorRelation m) k).Finite ∧
      Nat.card (residualSet (selectorRelation m) k) = 2^k) ∧
    (∀ ell, ell ≤ m →
      residualSet (selectorRelation m) (2*m+1+ell) =
        Set.range (fun r : List.Vector Bool (m-ell) => ({r.val} : Set (List Bool))) ∧
      (residualSet (selectorRelation m) (2*m+1+ell)).Finite ∧
      Nat.card (residualSet (selectorRelation m) (2*m+1+ell)) = 2^(m-ell)) ∧
    (∀ k, 1 ≤ k → k ≤ 2*m →
      (image (selectorRelation m) (k,1)).Finite ∧
      Nat.card (image (selectorRelation m) (k,1)) = 2^k) ∧
    (image (selectorRelation m) (2*m+1,1) =
      Set.range (fun p : (List.Vector Bool m × List.Vector Bool m) × Bool =>
        (({false :: p.1.1.val,true :: p.1.2.val} : Set (List Bool)),[p.2]))) ∧
    (image (selectorRelation m) (2*m+1,1)).Finite ∧
    Nat.card (image (selectorRelation m) (2*m+1,1)) = 2*(2^m)^2 ∧
    (∀ ell, 1 ≤ ell → ell ≤ m →
      image (selectorRelation m) (2*m+1+ell,1) =
        Set.range (fun ar : Bool × List.Vector Bool (m-ell) =>
          (({ar.1 :: ar.2.val} : Set (List Bool)),[ar.1])) ∧
      (image (selectorRelation m) (2*m+1+ell,1)).Finite ∧
      Nat.card (image (selectorRelation m) (2*m+1+ell,1)) = 2^(m-ell+1)) ∧
    (∀ k, k ≤ 3*m+1 →
      (image (selectorRelation m) (k,0)).Finite ∧
      Nat.card (image (selectorRelation m) (k,0)) =
        Nat.card (residualSet (selectorRelation m) k)) ∧
    forwardPeak m = (2^m)^2 ∧ oneCreditPeak m = 2*(2^m)^2 ∧
    Nat.clog 2 (forwardPeak m) = 2*m ∧
    Nat.clog 2 (oneCreditPeak m) = 2*m+1 ∧
    Nat.clog 2 (oneCreditPeak m) - Nat.clog 2 (forwardPeak m) = 1 ∧
    Nat.clog 2 (Nat.card (residualSet (selectorRelation m) (2*m+1))) = m ∧
    Nat.clog 2 (Nat.card (image (selectorRelation m) (2*m+1,1))) = 2*m+1 ∧
    Nat.clog 2 (Nat.card (image (selectorRelation m) (2*m+1,1))) -
      Nat.clog 2 (Nat.card (residualSet (selectorRelation m) (2*m+1))) = m+1 := by
  have hp := peaks m
  have hpow : (2^m)^2 = 2^(2*m) := by rw [← pow_mul]; congr 1; omega
  have hpow' : 2*(2^m)^2 = 2^(2*m+1) := by rw [hpow,pow_succ]; omega
  have hw0 : Nat.clog 2 (forwardPeak m) = 2*m := by
    rw [hp.1,hpow,Nat.clog_pow 2 (2*m) (by decide)]
  have hw1 : Nat.clog 2 (oneCreditPeak m) = 2*m+1 := by
    rw [hp.2,hpow',Nat.clog_pow 2 (2*m+1) (by decide)]
  have hs0 : Nat.clog 2 (Nat.card (residualSet (selectorRelation m) (2*m+1))) = m := by
    have h := (postcopy_count m 0 (by omega)).2
    simp only [Nat.add_zero,Nat.sub_zero] at h
    rw [h,Nat.clog_pow 2 m (by decide)]
  have hs1 : Nat.clog 2 (Nat.card (image (selectorRelation m) (2*m+1,1))) = 2*m+1 := by
    rw [(selector_count m).2,hpow',Nat.clog_pow 2 (2*m+1) (by decide)]
  refine ⟨fixed_length m, relation_nonempty m,
    (List.finite_length_eq Bool (3*m+1)).subset (fixed_length m),
    preparation_profile m,?_,preparation_one_credit m,selector_image m,
    (selector_count m).1,(selector_count m).2,?_,zero_credit_count m,
    hp.1,hp.2,hw0,hw1,by omega,hs0,hs1,by omega⟩
  · intro ell hell
    exact ⟨postcopy_residuals m ell hell,postcopy_count m ell hell⟩
  · intro ell hpos hell
    exact ⟨postcopy_image m ell hpos hell,postcopy_one_count m ell hpos hell⟩

#print axioms exact_selector_family_profile

end D5.S3.ObserverMemory.NonlinearSelectorProfile
