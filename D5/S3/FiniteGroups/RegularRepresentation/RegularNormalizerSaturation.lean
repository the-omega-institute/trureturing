/- GID: D5/S3/FiniteGroups/RegularRepresentation/RegularNormalizerSaturation
   generality: G
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: For any group H and nonempty K, the actual diagonal regular normalizer equals the full partition automorphism subgroup iff Finite H and (Nat.card H ≤ 2 or (Subsingleton K and (Nat.card H = 3 or (Nat.card H = 4 and every h in H has h*h = 1)))). -/

import D5.S3.FiniteGroups.Partitions.UniformPartitionAutomorphisms
import D5.S3.FiniteGroups.RegularRepresentation.DiagonalRegularNormalizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic.Push

/-!
# Saturation of the diagonal regular normalizer

For arbitrary `K : Type u` and `H : Type v` with `[Group H]` and `[Nonempty K]`,
the actual normalizer of the diagonal left-translation range in
`Equiv.Perm (K × H)` equals the full first-coordinate partition automorphism
subgroup exactly when `H` is finite and either has at most two elements, or
`K` is subsingleton and `H` has order three or order four with every square one.
The explicit `Finite H` conclusion matters because `Nat.card` is zero on
infinite types. The universes of `K` and `H` are independent.

The proof reuses the existing diagonal-normalizer and partition-coordinate
extractions. Its finite-cover transposition obstructions and common-automorphism
condition compare the actual ambient subgroups without additional finiteness
hypotheses. The order-four sufficiency step uses Mathlib's
`IsKleinFour.mulEquiv` from `Mathlib.GroupTheory.SpecificGroups.KleinFour`:
squares one give exponent dividing two, and cardinality four excludes exponent one.

The identity-fixing bijection classification is prior mathematical work:
Mikko Korhonen, answer 491536 to Mathematics Stack Exchange question 452596;
Pete L. Clark, answer 452657, excludes infinite groups; Tobias Kildetoft,
answer 452609, treats the finite case. See the original discussion:
https://math.stackexchange.com/questions/452596/is-a-bijection-from-a-group-to-itself-automatically-an-isomorphism-if-it-maps-th
The local formal contribution is the finite-cover obstruction and its use with
the common automorphism of the already-proved diagonal coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FiniteGroups.RegularNormalizerSaturation
open Equiv
universe u v
variable {K : Type u} {H : Type v} [Group H]

private theorem common_of_equality [Nonempty K]
    (he : DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H)
    (f : K → Perm H) (hf : ∀ i, f i 1 = 1) :
    ∃ alpha : MulAut H, ∀ i x, f i x = alpha x := by
  let p := UniformPartitionAutomorphisms.assemble f (1 : Perm K)
  have hp : (p : Perm (K × H)) ∈ DiagonalRegularNormalizer.diagonalNormalizer K H := by
    rw [he]
    exact p.property
  obtain ⟨t, ht, _⟩ := (DiagonalRegularNormalizer.mem_normalizer_iff_existsUnique_coordinates K H _).mp hp
  refine ⟨t.2.1, ?_⟩
  intro i x
  have hb := congrArg Prod.snd (ht i 1)
  change f i 1 = t.2.1 1 * t.2.2 i at hb
  have hb' : t.2.2 i = 1 := by simpa [hf i] using hb.symm
  have hx := congrArg Prod.snd (ht i x)
  change f i x = t.2.1 x * t.2.2 i at hx
  simpa [hb'] using hx

private theorem fixes_one_mul [Nonempty K]
    (he : DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H) :
    ∀ f : Perm H, f 1 = 1 → ∀ x y, f (x * y) = f x * f y := by
  intro f hf x y
  obtain ⟨alpha, ha⟩ := common_of_equality he (fun _ => f) (fun _ => hf)
  let i : K := Classical.choice inferInstance
  rw [ha i (x*y), ha i x, ha i y, map_mul]

private theorem finite_classification
    (hm : ∀ f : Perm H, f 1 = 1 → ∀ x y, f (x*y) = f x * f y) :
    Finite H ∧ (Nat.card H ≤ 2 ∨ Nat.card H = 3 ∨
      (Nat.card H = 4 ∧ ∀ h : H, h*h = 1)) := by
  classical
  by_cases hn : ∃ a : H, a*a ≠ 1
  · obtain ⟨a, ha⟩ := hn
    have ha1 : a ≠ 1 := by intro h; simpa [h] using ha
    have haa : a*a ≠ a := by
      intro h
      have : a = 1 := mul_left_cancel (show a*a = a*1 by simpa using h)
      exact ha1 this
    have hc (x : H) : x = 1 ∨ x = a ∨ x = a*a := by
      by_contra hh
      push Not at hh
      let f : Perm H := swap (a*a) x
      have hf : f 1 = 1 := swap_apply_of_ne_of_ne ha.symm hh.1.symm
      have hfa : f a = a := swap_apply_of_ne_of_ne haa.symm hh.2.1.symm
      have hx := hm f hf a a
      rw [hfa] at hx
      exact hh.2.2 (by simpa [f] using hx)
    letI : Fintype H := ⟨{1,a,a*a}, by intro x; simpa using hc x⟩
    have hc3 : Nat.card H = 3 := by
      rw [Nat.card_eq_fintype_card]
      change ({1,a,a*a} : Finset H).card = 3
      simp [ha1, ha, haa, Ne.symm ha1, Ne.symm ha, Ne.symm haa]
    exact ⟨inferInstance, Or.inr (Or.inl hc3)⟩
  · have hs : ∀ h : H, h*h = 1 := by simpa using hn
    by_cases hab : ∃ a b : H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
    · obtain ⟨a,b,ha,hb,hab⟩ := hab
      have hp1 : a*b ≠ 1 := by
        intro hp
        have : a*b = a*a := hp.trans (hs a).symm
        exact hab (mul_left_cancel this).symm
      have hpa : a*b ≠ a := by
        intro hp
        exact hb (mul_left_cancel (show a*b = a*1 by simpa using hp))
      have hpb : a*b ≠ b := by
        intro hp
        exact ha (mul_right_cancel (show a*b = 1*b by simpa using hp))
      have hc (x : H) : x = 1 ∨ x = a ∨ x = b ∨ x = a*b := by
        by_contra hh
        push Not at hh
        let f : Perm H := swap (a*b) x
        have hf : f 1 = 1 := swap_apply_of_ne_of_ne hp1.symm hh.1.symm
        have hfa : f a = a := swap_apply_of_ne_of_ne hpa.symm hh.2.1.symm
        have hfb : f b = b := swap_apply_of_ne_of_ne hpb.symm hh.2.2.1.symm
        have hx := hm f hf a b
        rw [hfa,hfb] at hx
        exact hh.2.2.2 (by simpa [f] using hx)
      letI : Fintype H := ⟨{1,a,b,a*b}, by intro x; simpa using hc x⟩
      have hc4 : Nat.card H = 4 := by
        rw [Nat.card_eq_fintype_card]
        change ({1,a,b,a*b} : Finset H).card = 4
        simp [ha,hb,hab,hp1,hpa,hpb,Ne.symm ha,Ne.symm hb,Ne.symm hab,
          Ne.symm hp1,Ne.symm hpa,Ne.symm hpb]
      exact ⟨inferInstance, Or.inr (Or.inr ⟨hc4, hs⟩)⟩
    · by_cases ha : ∃ a : H, a ≠ 1
      · obtain ⟨a,ha⟩ := ha
        have hc (x : H) : x = 1 ∨ x = a := by
          by_cases hx : x = 1
          · exact Or.inl hx
          · exact Or.inr (by by_contra h; exact hab ⟨x,a,hx,ha,h⟩)
        letI : Fintype H := ⟨{1,a}, by intro x; simpa using hc x⟩
        refine ⟨inferInstance, Or.inl ?_⟩
        rw [Nat.card_eq_fintype_card]
        change ({1,a} : Finset H).card ≤ 2
        simp [ha,Ne.symm ha]
      · have hc (x : H) : x = 1 := by by_contra hx; exact ha ⟨x,hx⟩
        letI : Fintype H := ⟨{1}, by intro x; simpa using hc x⟩
        refine ⟨inferInstance, Or.inl ?_⟩
        rw [Nat.card_eq_fintype_card]
        change ({1} : Finset H).card ≤ 2
        simp

private theorem labels_subsingleton [Nonempty K]
    (he : DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H)
    (a b : H) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) : Subsingleton K := by
  classical
  refine ⟨?_⟩
  intro i j
  by_contra hij
  let f : K → Perm H := fun k => if k = i then swap a b else 1
  have hf (k : K) : f k 1 = 1 := by
    dsimp [f]
    split_ifs
    · exact swap_apply_of_ne_of_ne ha.symm hb.symm
    · rfl
  obtain ⟨alpha, hh⟩ := common_of_equality he f hf
  have hi := hh i a
  have hj := hh j a
  have : b = a := by simpa [f, Ne.symm hij] using hi.trans hj.symm
  exact hab this.symm

private theorem small_perm [Finite H] (hc : Nat.card H ≤ 2)
    (f : Perm H) (hf : f 1 = 1) (x : H) : f x = x := by
  classical
  letI := Fintype.ofFinite H
  by_contra hx
  have hx1 : x ≠ 1 := by intro h; simpa [h,hf] using hx
  have hf1 : f x ≠ 1 := by intro h; exact hx1 (f.injective (h.trans hf.symm))
  have h := Finset.card_le_univ ({1,x,f x} : Finset H)
  have hc' : Fintype.card H ≤ 2 := by simpa only [Nat.card_eq_fintype_card] using hc
  simp [hx1,hf1,hx,Ne.symm hx1,Ne.symm hf1,Ne.symm hx] at h
  omega

private theorem three_perm [Finite H] (hc : Nat.card H = 3)
    (f : Perm H) (hf : f 1 = 1) : ∀ x y, f (x*y) = f x * f y := by
  classical
  letI := Fintype.ofFinite H
  have cube (x : H) : x*x*x = 1 := by
    have h := pow_card_eq_one' (x := x)
    rw [hc] at h
    simpa only [pow_succ, pow_zero, one_mul] using h
  have sq (x : H) (hx : x ≠ 1) : x*x ≠ 1 := by
    intro h
    have hh := cube x
    rw [h,one_mul] at hh
    exact hx hh
  have cover (a b : H) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
      (z : H) : z = 1 ∨ z = a ∨ z = b := by
    by_contra hz
    push Not at hz
    have h := Finset.card_le_univ ({1,a,b,z} : Finset H)
    have hcard : Fintype.card H = 3 := by simpa only [Nat.card_eq_fintype_card] using hc
    simp [ha,hb,hab,hz.1,hz.2.1,hz.2.2,Ne.symm ha,Ne.symm hb,
      Ne.symm hab,Ne.symm hz.1,Ne.symm hz.2.1,Ne.symm hz.2.2,hcard] at h
  have prod (a b : H) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) : a*b = 1 := by
    rcases cover a b ha hb hab (a*b) with h|h|h
    · exact h
    · exact (hb (mul_left_cancel (show a*b = a*1 by simpa using h))).elim
    · exact (ha (mul_right_cancel (show a*b = 1*b by simpa using h))).elim
  intro x y
  by_cases hx : x = 1
  · simp [hx,hf]
  by_cases hy : y = 1
  · simp [hy,hf]
  have hfx : f x ≠ 1 := fun h => hx (f.injective (h.trans hf.symm))
  have hfy : f y ≠ 1 := fun h => hy (f.injective (h.trans hf.symm))
  by_cases hxy : x = y
  · subst y
    have hsx : x*x ≠ x := fun h => hx (mul_left_cancel (show x*x = x*1 by simpa using h))
    have hsfx : f x*f x ≠ f x := fun h => hfx (mul_left_cancel (show f x*f x = f x*1 by simpa using h))
    rcases cover (f x) (f (x*x)) hfx
      (fun h => sq x hx (f.injective (h.trans hf.symm)))
      (fun h => hsx (f.injective h).symm) (f x*f x) with h|h|h
    · exact (sq (f x) hfx h).elim
    · exact (hsfx h).elim
    · exact h.symm
  · rw [prod x y hx hy hxy, hf, prod (f x) (f y) hfx hfy (fun h => hxy (f.injective h))]

private theorem four_perm [Finite H] (hc : Nat.card H = 4)
    (hs : ∀ h : H, h*h = 1) (f : Perm H) (hf : f 1 = 1) :
    ∀ x y, f (x*y) = f x * f y := by
  classical
  have hd : Monoid.exponent H ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun h => by
      simpa only [pow_two] using hs h
  have he : Monoid.exponent H = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · letI : Subsingleton H := Monoid.exp_eq_one_iff.mp h1
      have hcard : Nat.card H = 1 := Nat.card_unique
      omega
    · exact h2
  letI : IsKleinFour H := ⟨hc, he⟩
  exact fun x y => (IsKleinFour.mulEquiv f hf).map_mul x y

private theorem equality_of_coordinates [Nonempty K] [Finite H]
    (hc : Nat.card H ≤ 2 ∨ (Subsingleton K ∧
      (Nat.card H = 3 ∨ (Nat.card H = 4 ∧ ∀ h : H, h*h = 1)))) :
    DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H := by
  classical
  apply le_antisymm
  · intro p hp
    obtain ⟨t, ht, _⟩ := (DiagonalRegularNormalizer.mem_normalizer_iff_existsUnique_coordinates K H p).mp hp
    intro x y
    change (p x).1 = (p y).1 ↔ x.1 = y.1
    rw [ht x.1 x.2, ht y.1 y.2]
    exact t.1.injective.eq_iff
  · intro p hp
    let q : UniformPartitionAutomorphisms.Aut K H := ⟨p,hp⟩
    let c := UniformPartitionAutomorphisms.coordinates q
    have ev (i : K) (x : H) : p (i,x) = (c.right i,c.left (c.right i) x) := by
      have hh := congrArg (fun a : UniformPartitionAutomorphisms.Aut K H => (a : Perm (K × H)) (i,x))
        (UniformPartitionAutomorphisms.coordinates.symm_apply_apply q)
      exact hh.symm
    let f : K → Perm H := fun i => c.left (c.right i)
    let b : K → H := fun i => f i 1
    let g : K → Perm H := fun i => (f i).trans (Equiv.mulRight (b i)⁻¹)
    have g1 (i : K) : g i 1 = 1 := by simp [g,b]
    have fg (i : K) (x : H) : f i x = g i x * b i := by simp [g,mul_assoc]
    let i0 : K := Classical.choice inferInstance
    have gm : ∀ x y, g i0 (x*y) = g i0 x * g i0 y := by
      rcases hc with hsmall | ⟨hK,h3|⟨h4,hs⟩⟩
      · intro x y; rw [small_perm hsmall _ (g1 i0),small_perm hsmall _ (g1 i0),small_perm hsmall _ (g1 i0)]
      · exact three_perm h3 _ (g1 i0)
      · exact four_perm h4 hs _ (g1 i0)
    let alpha : MulAut H := { g i0 with map_mul' := gm }
    have gg (i : K) (x : H) : g i x = alpha x := by
      rcases hc with hsmall | ⟨hK,_⟩
      · change g i x = g i0 x
        rw [small_perm hsmall _ (g1 i), small_perm hsmall _ (g1 i0)]
      · have hi : i = i0 := hK.elim i i0
        subst i
        rfl
    have ht (i : K) (x : H) : p (i,x) = (c.right i,alpha x*b i) := by
      rw [ev]
      change (c.right i,f i x) = _
      rw [fg,gg]
    let pn := (DiagonalRegularNormalizer.normalizerEquiv K H).symm (c.right,alpha,b)
    have heqp : p = (pn : Perm (K × H)) := by
      apply Equiv.ext
      rintro ⟨i,x⟩
      rw [ht, DiagonalRegularNormalizer.normalizerEquiv_eval K H pn]
      simp [pn]
    rw [heqp]
    exact pn.property

private theorem labels_of_large [Nonempty K] [Finite H]
    (he : DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H) (hc : 2 < Nat.card H) :
    Subsingleton K := by
  classical
  letI := Fintype.ofFinite H
  have hc' : 2 < Fintype.card H := by simpa only [Nat.card_eq_fintype_card] using hc
  obtain ⟨a,ha⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card H) (1:H)
  have hb : ∃ b : H, b ≠ 1 ∧ b ≠ a := by
    by_contra hn
    have hcover (x : H) : x = 1 ∨ x = a := by
      by_contra hh
      push Not at hh
      exact hn ⟨x,hh⟩
    have hsub : (Finset.univ : Finset H) ⊆ {1,a} := by intro x _; simpa using hcover x
    have h := Finset.card_le_card hsub
    simp [ha,Ne.symm ha] at h
    omega
  obtain ⟨b,hb1,hba⟩ := hb
  exact labels_subsingleton he a b ha hb1 hba.symm

/-- Exact saturation classification in the actual ambient permutation group. -/
theorem diagonalNormalizer_eq_partitionAut_iff (K : Type u) (H : Type v)
    [Group H] [Nonempty K] :
    DiagonalRegularNormalizer.diagonalNormalizer K H = UniformPartitionAutomorphisms.Aut K H ↔
      Finite H ∧ (Nat.card H ≤ 2 ∨ (Subsingleton K ∧
        (Nat.card H = 3 ∨ (Nat.card H = 4 ∧ ∀ h : H, h*h = 1)))) := by
  classical
  constructor
  · intro he
    obtain ⟨hfin,hc⟩ := finite_classification (fixes_one_mul he)
    letI := hfin
    refine ⟨hfin, ?_⟩
    rcases hc with h2 | h3 | ⟨h4,hs⟩
    · exact Or.inl h2
    · exact Or.inr ⟨labels_of_large he (by omega),Or.inl h3⟩
    · exact Or.inr ⟨labels_of_large he (by omega),Or.inr ⟨h4,hs⟩⟩
  · rintro ⟨hfin,hc⟩
    letI := hfin
    exact equality_of_coordinates hc

end D5.S3.FiniteGroups.RegularNormalizerSaturation
