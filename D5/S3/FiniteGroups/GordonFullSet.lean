/- GID: D5/S3/FiniteGroups/GordonFullSet
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GordonFullSet
   mirror-E: none(waiver:pure-mathematical-gordon-construction)
   anchors: []
   utility: none
   digest: Gordon full-set sequencing for every finite additive abelian group of nonzero total. -/

import D5.S3.FiniteGroups.GordonProduct
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Prime-power decomposition and transport of Gordon's original-label sequencing. -/

open scoped BigOperators DirectSum

namespace D5.S3.FiniteGroups.Gordon

private def total (G : Type*) [AddCommGroup G] [Fintype G] : G := ∑ x : G, x

private theorem total_map {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [Fintype H] (e : G ≃+ H) : e (total G) = total H := by
  simp only [total, map_sum]
  exact e.toEquiv.sum_comp (fun x => x)

private theorem two_total (G : Type*) [AddCommGroup G] [Fintype G] :
    total G + total G = 0 := by
  have hn : -total G = total G := by
    rw [total, ← Finset.sum_neg_distrib]
    exact Equiv.sum_comp (Equiv.neg G) (fun x => x)
  exact neg_eq_iff_add_eq_zero.mp hn

private theorem even_nsmul_total (G : Type*) [AddCommGroup G] [Fintype G]
    (n : ℕ) (hn : Even n) : n • total G = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, ← nsmul_add, two_total, nsmul_zero]

private theorem total_prod (G H : Type*) [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [Fintype H] :
    total (G × H) = (Fintype.card H • total G, Fintype.card G • total H) := by
  apply Prod.ext
  · simp only [total, Prod.fst_sum, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ]
    exact (Finset.smul_sum (r := Fintype.card H) (s := Finset.univ)
      (f := fun x : G => x)).symm
  · simp [total, Fintype.sum_prod_type, Finset.sum_const, Prod.snd_sum]

private theorem total_zero_of_two_injective (G : Type*) [AddCommGroup G] [Fintype G]
    (hi : Function.Injective (fun x : G => x + x)) : total G = 0 := by
  exact hi (by simpa only [zero_add] using two_total G)

/-- A cyclic prime-power coordinate with its prime witness retained. -/
structure CyclicFactor where
  prime : ℕ
  isPrime : Nat.Prime prime
  exponent : ℕ

private def CyclicFactor.modulus (c : CyclicFactor) : ℕ := c.prime ^ c.exponent

instance (c : CyclicFactor) : NeZero c.modulus :=
  ⟨pow_ne_zero _ c.isPrime.ne_zero⟩

@[reducible] private def Chain : List CyclicFactor → Type
  | [] => PUnit
  | c :: cs => ZMod c.modulus × Chain cs

private instance chainGroup : (cs : List CyclicFactor) → AddCommGroup (Chain cs)
  | [] => inferInstanceAs (AddCommGroup PUnit)
  | c :: cs => letI := chainGroup cs
               inferInstanceAs (AddCommGroup (ZMod c.modulus × Chain cs))

private instance chainFintype : (cs : List CyclicFactor) → Fintype (Chain cs)
  | [] => inferInstanceAs (Fintype PUnit)
  | c :: cs => letI := chainFintype cs
               inferInstanceAs (Fintype (ZMod c.modulus × Chain cs))

private def piSplit {n : ℕ} (f : Fin (n + 1) → CyclicFactor) :
    ((i : Fin (n + 1)) → ZMod (f i).modulus) ≃+
      ZMod (f 0).modulus × ((i : Fin n) → ZMod (f i.succ).modulus) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl

private def piChain : (n : ℕ) → (f : Fin n → CyclicFactor) →
    ((i : Fin n) → ZMod (f i).modulus) ≃+ Chain (List.ofFn f)
  | 0, f =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ i => Fin.elim0 i
      left_inv := fun _ => funext fun i => Fin.elim0 i
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  | n + 1, f => by
    rw [List.ofFn_succ]
    exact (piSplit f).trans ((AddEquiv.refl _).prodCongr (piChain n (fun i => f i.succ)))

/-- The three cases distinguish no even factor, one even factor, and vanishing total. -/
private def DecompositionCase (G : Type*) [AddCommGroup G] [Fintype G] : Prop :=
  (Odd (Fintype.card G) ∧ ∃ ds : List OddRadix, Nonempty (G ≃+ Box ds)) ∨
  (∃ a : ℕ, 0 < a ∧ ∃ ds : List OddRadix,
    Nonempty (G ≃+ ZMod (2 ^ a) × Box ds)) ∨
  (Even (Fintype.card G) ∧ total G = 0)

private theorem case_transport {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [Fintype H] (e : G ≃+ H) (hh : DecompositionCase H) :
    DecompositionCase G := by
  have hc := Fintype.card_congr e.toEquiv
  rcases hh with ⟨ho, ds, ⟨f⟩⟩ | ⟨a, ha, ds, ⟨f⟩⟩ | ⟨he, hz⟩
  · exact Or.inl ⟨hc ▸ ho, ds, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨a, ha, ds, ⟨e.trans f⟩⟩)
  · refine Or.inr (Or.inr ⟨hc ▸ he, e.injective ?_⟩)
    rw [total_map, hz, map_zero]

private theorem card_even_of_power_box {G : Type*} [AddCommGroup G] [Fintype G]
    (a : ℕ) (ha : 0 < a) (ds : List OddRadix)
    (e : G ≃+ ZMod (2 ^ a) × Box ds) : Even (Fintype.card G) := by
  rw [Fintype.card_congr e.toEquiv, Fintype.card_prod, ZMod.card]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  refine ⟨2 ^ a * Fintype.card (Box ds), ?_⟩
  rw [pow_succ]
  ring

private theorem total_prod_zero_even (G H : Type*) [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [Fintype H] (hg : Even (Fintype.card G))
    (hh : Even (Fintype.card H)) : total (G × H) = 0 := by
  rw [total_prod, even_nsmul_total G _ hh, even_nsmul_total H _ hg]
  rfl

private theorem chain_classification (cs : List CyclicFactor) :
    DecompositionCase (Chain cs) := by
  induction cs with
  | nil =>
    exact Or.inl ⟨by decide, [], ⟨AddEquiv.refl _⟩⟩
  | cons c cs ih =>
    by_cases he : c.exponent = 0
    · have hm : c.modulus = 1 := by simp [CyclicFactor.modulus, he]
      letI : Unique (ZMod c.modulus) := by rw [hm]; infer_instance
      exact case_transport (AddEquiv.uniqueProd) ih
    · have hep : 0 < c.exponent := by omega
      have hmod : 1 < c.modulus := one_lt_pow₀ c.isPrime.one_lt he
      by_cases hp : c.prime = 2
      · have hm : c.modulus = 2 ^ c.exponent := by simp [CyclicFactor.modulus, hp]
        let ec : ZMod c.modulus ≃+ ZMod (2 ^ c.exponent) :=
          (ZMod.ringEquivCongr hm).toAddEquiv
        have hce : Even (Fintype.card (ZMod c.modulus)) := by
          rw [ZMod.card, hm]
          obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero he
          rw [ha, pow_succ]
          exact ⟨2 ^ a, by ring⟩
        rcases ih with ⟨ho, ds, ⟨f⟩⟩ | ⟨a, ha, ds, ⟨f⟩⟩ | ⟨ht, hz⟩
        · exact Or.inr (Or.inl ⟨c.exponent, hep, ds, ⟨ec.prodCongr f⟩⟩)
        · have ht := card_even_of_power_box a ha ds f
          refine Or.inr (Or.inr ⟨?_, total_prod_zero_even _ _ hce ht⟩)
          simpa only [Chain, Fintype.card_prod] using hce.mul_right (Fintype.card (Chain cs))
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · simpa [Chain, Fintype.card_prod] using hce.mul_right (Fintype.card (Chain cs))
          · change total (ZMod c.modulus × Chain cs) = 0
            rw [total_prod, even_nsmul_total _ _ ht, hz, nsmul_zero]
            rfl
      · have hodd : Odd c.modulus := (c.isPrime.odd_of_ne_two hp).pow
        let d : OddRadix := ⟨c.modulus, hmod, hodd⟩
        have hct : total (ZMod c.modulus) = 0 := by
          apply total_zero_of_two_injective
          have hunit : IsUnit (2 : ZMod c.modulus) :=
            (ZMod.isUnit_iff_coprime 2 c.modulus).mpr (Nat.coprime_two_left.mpr hodd)
          intro x y hxy
          exact hunit.mul_left_injective (by simpa only [mul_two] using hxy)
        rcases ih with ⟨ho, ds, ⟨f⟩⟩ | ⟨a, ha, ds, ⟨f⟩⟩ | ⟨ht, hz⟩
        · refine Or.inl ⟨?_, d :: ds, ⟨(AddEquiv.refl _).prodCongr f⟩⟩
          simpa [Chain, Fintype.card_prod, ZMod.card] using hodd.mul ho
        · refine Or.inr (Or.inl ⟨a, ha, d :: ds, ⟨?_⟩⟩)
          exact ((AddEquiv.refl _).prodCongr f).trans
            ((AddEquiv.prodAssoc).symm.trans
              (((AddEquiv.prodComm).prodCongr (AddEquiv.refl _)).trans
                (AddEquiv.prodAssoc)))
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · simpa [Chain, Fintype.card_prod] using ht.mul_left (Fintype.card (ZMod c.modulus))
          · change total (ZMod c.modulus × Chain cs) = 0
            rw [total_prod, hct, hz, nsmul_zero, nsmul_zero]
            rfl

private theorem finite_abelian_presentation (G : Type*) [AddCommGroup G] [Fintype G] :
    ∃ cs : List CyclicFactor, Nonempty (G ≃+ Chain cs) := by
  classical
  obtain ⟨ι, _, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  let f : ι → CyclicFactor := fun i => ⟨p i, hp i, n i⟩
  let r := (Fintype.equivFin ι).symm
  refine ⟨List.ofFn (fun i => f (r i)), ⟨?_⟩⟩
  exact e.trans ((DirectSum.addEquivProd _).trans
    (((RingEquiv.piCongrLeft (fun i => ZMod (p i ^ n i)) r).toAddEquiv).symm.trans
      (piChain _ (fun i => f (r i)))))

/-- Nonzero total excludes no even factor and more than one even factor. -/
private theorem decomposition_of_total_ne_zero (G : Type*) [AddCommGroup G] [Fintype G]
    (hs : total G ≠ 0) : ∃ a : ℕ, 0 < a ∧ ∃ ds : List OddRadix,
      Nonempty (G ≃+ ZMod (2 ^ a) × Box ds) := by
  obtain ⟨cs, ⟨e⟩⟩ := finite_abelian_presentation G
  have hm := case_transport e (chain_classification cs)
  rcases hm with ⟨_, ds, ⟨f⟩⟩ | h | ⟨_, hz⟩
  · have hb : total (Box ds) = 0 := total_zero_of_two_injective _ (box_two_injective ds)
    exact (hs (f.injective (by rw [total_map, hb, map_zero]))).elim
  · exact h
  · exact (hs hz).elim

private theorem total_eq_of_unique_involution {G : Type*} [AddCommGroup G] [Fintype G]
    (t : G) (ht : t ≠ 0 ∧ t + t = 0)
    (hu : ∀ x : G, x ≠ 0 ∧ x + x = 0 → x = t) : total G = t := by
  classical
  have hneg : -t = t := neg_eq_iff_add_eq_zero.mpr ht.2
  have hz : ∑ x ∈ (Finset.univ.erase t), x = 0 := by
    apply Finset.sum_involution (fun x _ => -x)
    · intro x hx
      exact add_neg_cancel x
    · intro x hx hxn he
      have hxt := hu x ⟨hxn, neg_eq_iff_add_eq_zero.mp he⟩
      exact (Finset.mem_erase.mp hx).1 hxt
    · intro x hx
      exact neg_neg x
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
      intro he
      exact hx (neg_injective (he.trans hneg.symm))
  have hsum := Finset.add_sum_erase Finset.univ (fun x : G => x) (Finset.mem_univ t)
  simpa only [hz, add_zero, total] using hsum.symm

private theorem product_unique_involution (h : ℕ) (hh : 0 < h) (ds : List OddRadix) :
    ∃! t : ZMod (2 * h) × Box ds, t ≠ 0 ∧ t + t = 0 := by
  letI : NeZero (2 * h) := ⟨by omega⟩
  refine ⟨(word h ds).sum, ?_, ?_⟩
  · rw [word_endpoint h hh ds]
    constructor
    · intro he
      have he' := congrArg Prod.fst he
      change (h : ZMod (2 * h)) = 0 at he'
      have hd := (ZMod.natCast_eq_zero_iff h (2 * h)).mp he'
      have := Nat.le_of_dvd hh hd
      omega
    · apply Prod.ext
      · change (h : ZMod (2 * h)) + h = 0
        rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
      · exact zero_add _
  · rintro ⟨x, y⟩ ⟨hne, hadd⟩
    have hy : y = 0 := box_two_injective ds (by
      have he := congrArg Prod.snd hadd
      change y + y = 0 at he
      simpa only [zero_add] using he)
    subst y
    have hxne : x ≠ 0 := by intro hx; exact hne (by simp [hx])
    have hxadd : x + x = 0 := congrArg Prod.fst hadd
    have hv := (ZMod.neg_eq_self_iff x).mp (neg_eq_iff_add_eq_zero.mpr hxadd)
    rcases hv with hx | hv
    · exact (hxne hx).elim
    have hx : x = (h : ZMod (2 * h)) := by
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by omega : h < 2 * h)]
      omega
    rw [word_endpoint h hh ds]
    exact Prod.ext hx rfl

/-- The full-group sum is nonzero exactly when the nonzero two-torsion is a singleton. -/
theorem sum_ne_zero_iff_unique_involution (G : Type*) [AddCommGroup G] [Fintype G] :
    (∑ x : G, x) ≠ 0 ↔ ∃! t : G, t ≠ 0 ∧ t + t = 0 := by
  constructor
  · intro hs
    obtain ⟨a, ha, ds, ⟨e⟩⟩ := decomposition_of_total_ne_zero G hs
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hm : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    let ep : ZMod (2 ^ (b + 1)) × Box ds ≃+ ZMod (2 * 2 ^ b) × Box ds :=
      (ZMod.ringEquivCongr hm).toAddEquiv.prodCongr (AddEquiv.refl _)
    let f := e.trans ep
    obtain ⟨t, ht, hu⟩ := product_unique_involution (2 ^ b) (pow_pos (by decide) _) ds
    refine ⟨f.symm t, ⟨?_, ?_⟩, ?_⟩
    · intro hz
      exact ht.1 (f.symm.injective (hz.trans (map_zero f.symm).symm))
    · rw [← map_add, ht.2, map_zero]
    · intro x hx
      apply f.injective
      rw [f.apply_symm_apply]
      apply hu
      constructor
      · intro hz
        exact hx.1 (f.injective (hz.trans (map_zero f).symm))
      · rw [← map_add, hx.2, map_zero]
  · rintro ⟨t, ht, hu⟩
    change total G ≠ 0
    rw [total_eq_of_unique_involution t ht hu]
    exact ht.1

private theorem sequencing_map {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (w : List G) (hw : FullSequencing w) : FullSequencing (w.map e) := by
  refine ⟨hw.1.map e.injective, ?_, ?_⟩
  · intro y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      intro he
      exact ((hw.2.1 x).mp hx) (e.injective (he.trans (map_zero e).symm))
    · intro hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact List.mem_map.mpr ⟨x, (hw.2.1 x).mpr (by simpa using hy), rfl⟩
  · intro k l he
    have hk : k.val < w.length + 1 := by simpa only [List.length_map] using k.isLt
    have hl : l.val < w.length + 1 := by simpa only [List.length_map] using l.isLt
    have he' : e ((w.take k.val).sum) = e ((w.take l.val).sum) := by
      simpa only [← List.map_take, List.sum_hom] using he
    apply Fin.ext
    exact congrArg (fun z : Fin (w.length + 1) => z.val)
      (hw.2.2 (a₁ := ⟨k.val, hk⟩) (a₂ := ⟨l.val, hl⟩) (e.injective he'))

private theorem interval_ne_zero {G : Type*} [AddCommGroup G] (w : List G)
    (hi : Function.Injective (fun k : Fin (w.length + 1) => (w.take k.val).sum))
    (i j : ℕ) (hij : i < j) (hj : j ≤ w.length) : ((w.drop i).take (j - i)).sum ≠ 0 := by
  intro hz
  have he : (w.take j).sum = (w.take i).sum := by
    have hsplit := congrArg List.sum (List.take_add (l := w) (i := i) (j := j - i))
    simpa only [Nat.add_sub_of_le hij.le, List.sum_append, hz, add_zero] using hsplit
  have he' := hi (a₁ := ⟨j, by omega⟩) (a₂ := ⟨i, by omega⟩) he
  have hh : j = i := congrArg (fun z : Fin (w.length + 1) => z.val) he'
  omega

/-- Gordon's full-set theorem in the original additive group and original labels.
Every nonempty interval, including the whole word, has nonzero sum. -/
theorem exists_full_set_sequencing (G : Type*) [AddCommGroup G] [Fintype G]
    (hs : (∑ x : G, x) ≠ 0) :
    ∃ w : List G, w.Nodup ∧ (∀ x : G, x ∈ w ↔ x ≠ 0) ∧
      Function.Injective (fun k : Fin (w.length + 1) => (w.take k.val).sum) ∧
      (∀ i j : ℕ, i < j → j ≤ w.length → ((w.drop i).take (j - i)).sum ≠ 0) := by
  obtain ⟨t, ht, hu⟩ := (sum_ne_zero_iff_unique_involution G).mp hs
  have htotal : total G ≠ 0 := by
    rw [total_eq_of_unique_involution t ht hu]
    exact ht.1
  obtain ⟨a, ha, ds, ⟨e⟩⟩ := decomposition_of_total_ne_zero G htotal
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hmod : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  let ep : ZMod (2 ^ (b + 1)) × Box ds ≃+ ZMod (2 * 2 ^ b) × Box ds :=
    (ZMod.ringEquivCongr hmod).toAddEquiv.prodCongr (AddEquiv.refl _)
  have hc : (2 ^ b).Coprime (volume ds) :=
    (Nat.coprime_two_left.mpr (volume_odd ds)).pow_left b
  have hp := product_sequencing (2 ^ b) (pow_pos (by decide) _) ds hc
  let w := (word (2 ^ b) ds).map (e.trans ep).symm
  have hw : FullSequencing w := sequencing_map (e.trans ep).symm _ hp
  exact ⟨w, hw.1, hw.2.1, hw.2.2, interval_ne_zero w hw.2.2⟩

end D5.S3.FiniteGroups.Gordon
