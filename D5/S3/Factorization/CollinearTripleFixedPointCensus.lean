/- GID: D5/S3/Factorization/CollinearTripleFixedPointCensus
   generality: I
   mirror-B: D5/B/S3/Factorization/CollinearTripleFixedPointCensus
   mirror-E: none(waiver:universal-counting-theorem)
   anchors: []
   utility: none
   digest: Fixed collinear triples are exactly the cosets of an admissible three-cycle. -/

import D5.S3.Factorization.CollinearTripleTranslationOrbits
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Tactic.Ring

namespace D5.S3.Factorization.CollinearTripleFixedPointCensus

open CollinearTripleTranslationOrbits
open scoped Pointwise

/-- Nonidentity translations have the exact three-cycle census, and for a modulus
three times a positive integer the eligible translations form an explicit quartet. -/
theorem fixed_point_census (n : ℕ) (hn : 0 < n) :
    (∀ t : Point n, 3 • t = 0 → t.1 ≠ 0 → t.2 ≠ 0 →
      ∃ c : Triple n, c.val = {0, t, 2 • t} ∧
        (∀ s : Triple n, t +ᵥ s = s ↔ ∃ p : Point n, p +ᵥ c = s) ∧
        (∀ p q : Point n, p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val) ∧
        Nat.card (AddAction.fixedBy (Triple n) t) = n ^ 2 / 3) ∧
    (∀ t : Point n, t ≠ 0 → ¬(3 • t = 0 ∧ t.1 ≠ 0 ∧ t.2 ≠ 0) →
      Nat.card (AddAction.fixedBy (Triple n) t) = 0) ∧
    (∀ m : ℕ, 0 < m → n = 3 * m → ∀ t : Point n, t ≠ 0 →
      Nat.card (AddAction.fixedBy (Triple n) t) =
        if t ∈ ({((m : ZMod n), (m : ZMod n)),
          ((m : ZMod n), ((2 * m : ℕ) : ZMod n)),
          (((2 * m : ℕ) : ZMod n), (m : ZMod n)),
          (((2 * m : ℕ) : ZMod n), ((2 * m : ℕ) : ZMod n))} : Finset (Point n))
        then n ^ 2 / 3 else 0) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have eligible (t : Point n) (h3 : 3 • t = 0) (hx : t.1 ≠ 0) (hy : t.2 ≠ 0) :
      ∃ c : Triple n, c.val = {0, t, 2 • t} ∧
        (∀ s : Triple n, t +ᵥ s = s ↔ ∃ p : Point n, p +ᵥ c = s) ∧
        (∀ p q : Point n, p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val) ∧
        Nat.card (AddAction.fixedBy (Triple n) t) = n ^ 2 / 3 := by
    have ht : t ≠ 0 := fun h ↦ hx (congrArg Prod.fst h)
    have ho : addOrderOf t = 3 := addOrderOf_eq_prime h3 ht
    have hox : addOrderOf t.1 = 3 :=
      addOrderOf_eq_prime (congrArg Prod.fst h3) hx
    have hoy : addOrderOf t.2 = 3 :=
      addOrderOf_eq_prime (congrArg Prod.snd h3) hy
    have hi : Set.InjOn (fun k : ℕ ↦ k • t) (↑(Finset.range 3)) := by
      simpa only [Finset.coe_range, ho] using nsmul_injOn_Iio_addOrderOf (x := t)
    let C : Finset (Point n) := (Finset.range 3).image (fun k ↦ k • t)
    have hcard : C.card = 3 := by
      change ((Finset.range 3).image (fun k ↦ k • t)).card = 3
      rw [Finset.card_image_of_injOn hi, Finset.card_range]
    have hC : IsCollinearTriple C := by
      refine ⟨hcard, ?_, ?_, ?_⟩
      · intro p hp q hq heq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
        have hij : i = j := nsmul_injOn_Iio_addOrderOf (x := t.1)
          (by simpa only [hox, Set.mem_Iio] using Finset.mem_range.mp hi)
          (by simpa only [hox, Set.mem_Iio] using Finset.mem_range.mp hj) heq
        rw [hij]
      · intro p hp q hq heq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
        have hij : i = j := nsmul_injOn_Iio_addOrderOf (x := t.2)
          (by simpa only [hoy, Set.mem_Iio] using Finset.mem_range.mp hi)
          (by simpa only [hoy, Set.mem_Iio] using Finset.mem_range.mp hj) heq
        rw [hij]
      · intro p hp q hq r hr
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
        change ((j • t.1) - (i • t.1)) * ((k • t.2) - (i • t.2)) =
          ((k • t.1) - (i • t.1)) * ((j • t.2) - (i • t.2))
        simp only [nsmul_eq_mul]
        ring
    let c : Triple n := ⟨C, hC⟩
    have hzero : (0 : Point n) ∈ C := Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    have hfix : t +ᵥ c = c := by
      apply Subtype.ext
      apply AddAction.mem_stabilizer_iff.mp
      apply AddAction.mem_stabilizer_finset'.mpr
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hir : i < 3 := Finset.mem_range.mp hi
      by_cases hi2 : i = 2
      · subst i
        exact Finset.mem_image.mpr ⟨0, by simp, by
          simpa only [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul,
            one_nsmul, zero_nsmul, vadd_eq_add, add_comm] using h3.symm⟩
      · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega),
          by change (i + 1) • t = t + i • t
             rw [add_nsmul, one_nsmul, add_comm]⟩
    have hstab (u : Point n) : u ∈ AddAction.stabilizer (Point n) c ↔ u ∈ C := by
      constructor
      · intro hu
        have hset : u +ᵥ C = C := congrArg Subtype.val hu
        have hmem : u +ᵥ (0 : Point n) ∈ u +ᵥ C :=
          Finset.mem_vadd_finset.mpr ⟨0, hzero, rfl⟩
        simpa only [vadd_eq_add, add_zero, hset] using hmem
      · intro hu
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
        exact (AddAction.stabilizer (Point n) c).nsmul_mem hfix i
    have hclass (s : Triple n) : t +ᵥ s = s ↔ ∃ p : Point n, p +ᵥ c = s := by
      constructor
      · intro hs
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [s.property.1]; decide)
        have hsub : p +ᵥ C ⊆ s.val := by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := Finset.mem_vadd_finset.mp hq
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
          have hmem : i • t ∈ AddAction.stabilizer (Point n) s.val :=
            (AddAction.stabilizer (Point n) s.val).nsmul_mem (congrArg Subtype.val hs) i
          simpa only [vadd_eq_add, add_comm] using
            AddAction.mem_stabilizer_finset'.mp hmem hp
        have heq : p +ᵥ C = s.val := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_vadd_finset, hcard, s.property.1])
        exact ⟨p, Subtype.ext heq⟩
      · rintro ⟨p, rfl⟩
        rw [← add_vadd, add_comm t p, add_vadd, hfix]
    have hfiber (p q : Point n) : p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val := by
      rw [← hstab]
      change _ ↔ (p - q) +ᵥ c = c
      constructor
      · intro h
        rw [sub_eq_neg_add, add_vadd, h, neg_vadd_vadd]
      · intro h
        have hh := congrArg (fun s : Triple n ↦ q +ᵥ s) h
        have hq : q + (p - q) = p := by rw [add_comm, sub_add_cancel]
        simpa only [← add_vadd, hq] using hh
    have hstabc : Nat.card (AddAction.stabilizer (Point n) c) = 3 := by
      calc
        _ = Nat.card C := Nat.card_congr (Equiv.subtypeEquivRight hstab)
        _ = 3 := (Nat.card_eq_finsetCard C).trans hcard
    have hset : AddAction.fixedBy (Triple n) t = AddAction.orbit (Point n) c := by
      ext s
      exact (hclass s).trans AddAction.mem_orbit_iff.symm
    have hcount := Nat.card_congr (AddAction.orbitProdStabilizerEquivAddGroup (Point n) c)
    rw [Nat.card_prod, hstabc, Nat.card_prod, Nat.card_zmod] at hcount
    have hnum : Nat.card (AddAction.fixedBy (Triple n) t) = n ^ 2 / 3 := by
      rw [← pow_two] at hcount
      rw [hset, ← hcount, Nat.mul_div_cancel]
      decide
    have hCexplicit : C = {0, t, 2 • t} := by
      simp only [C, show (Finset.range 3) = {0, 1, 2} from by decide,
        Finset.image_insert, Finset.image_singleton, zero_nsmul, one_nsmul]
    exact ⟨c, hCexplicit, hclass, hfiber, hnum⟩
  have necessary (t : Point n) (ht : t ≠ 0) (s : Triple n) (hs : t +ᵥ s = s) :
      3 • t = 0 ∧ t.1 ≠ 0 ∧ t.2 ≠ 0 := by
    have h3 := stabilizing_translation_three_torsion s t hs
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [s.property.1]; decide)
    have hset : t +ᵥ s.val = s.val := congrArg Subtype.val hs
    have htp : t + p ∈ s.val := by
      rw [← hset]
      exact Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
    refine ⟨h3, ?_, ?_⟩
    · intro hx
      have heq := s.property.2.1 htp hp (by simp only [Prod.fst_add, hx, zero_add])
      exact ht (add_right_cancel (heq.trans (zero_add p).symm))
    · intro hy
      have heq := s.property.2.2.1 htp hp (by simp only [Prod.snd_add, hy, zero_add])
      exact ht (add_right_cancel (heq.trans (zero_add p).symm))
  have zero_count (t : Point n) (ht : t ≠ 0)
      (hbad : ¬(3 • t = 0 ∧ t.1 ≠ 0 ∧ t.2 ≠ 0)) :
      Nat.card (AddAction.fixedBy (Triple n) t) = 0 := by
    let : IsEmpty (AddAction.fixedBy (Triple n) t) :=
      ⟨fun s ↦ hbad (necessary t ht s.val s.property)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
  refine ⟨eligible, zero_count, ?_⟩
  intro m hm hnm t ht
  subst n
  have coord (x : ZMod (3 * m)) :
      3 • x = 0 ↔ x = 0 ∨ x = (m : ZMod (3 * m)) ∨
        x = ((2 * m : ℕ) : ZMod (3 * m)) := by
    constructor
    · intro hx
      have hcast : ((3 * x.val : ℕ) : ZMod (3 * m)) = 0 := by
        simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hx
      have hd : m ∣ x.val := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp
        ((ZMod.natCast_eq_zero_iff _ _).mp hcast)
      obtain ⟨k, hk⟩ := hd
      have hv := ZMod.val_lt x
      have hk3 : k < 3 := by
        have hh : m * k < m * 3 := by simpa only [hk, Nat.mul_comm] using hv
        exact Nat.lt_of_mul_lt_mul_left hh
      have he : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases he with rfl | rfl | rfl
      · left
        rw [← ZMod.natCast_zmod_val x, hk]
        simp
      · right; left
        rw [← ZMod.natCast_zmod_val x, hk]
        simp
      · right; right
        rw [← ZMod.natCast_zmod_val x, hk]
        simp [Nat.mul_comm]
    · rintro (rfl | rfl | rfl)
      · simp
      · rw [nsmul_eq_mul, ← Nat.cast_mul]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl _)
      · rw [nsmul_eq_mul, ← Nat.cast_mul]
        apply (ZMod.natCast_eq_zero_iff _ _).mpr
        exact ⟨2, by omega⟩
  have hm0 : (m : ZMod (3 * m)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hle := Nat.le_of_dvd hm hd
    omega
  have hm20 : ((2 * m : ℕ) : ZMod (3 * m)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * m) hd
    omega
  have hequiv : t ∈ ({((m : ZMod (3 * m)), (m : ZMod (3 * m))),
        ((m : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m))),
        (((2 * m : ℕ) : ZMod (3 * m)), (m : ZMod (3 * m))),
        (((2 * m : ℕ) : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m)))} :
          Finset (Point (3 * m))) ↔ 3 • t = 0 ∧ t.1 ≠ 0 ∧ t.2 ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl) <;>
        exact ⟨Prod.ext (coord _ |>.mpr (by simp)) (coord _ |>.mpr (by simp)),
          by assumption, by assumption⟩
    · rintro ⟨h3, hx, hy⟩
      have hx' := (coord t.1).mp (congrArg Prod.fst h3)
      have hy' := (coord t.2).mp (congrArg Prod.snd h3)
      rcases hx' with h0 | hx' | hx'
      · exact (hx h0).elim
      · rcases hy' with h0 | hy' | hy'
        · exact (hy h0).elim
        · exact Or.inl (Prod.ext hx' hy')
        · exact Or.inr (Or.inl (Prod.ext hx' hy'))
      · rcases hy' with h0 | hy' | hy'
        · exact (hy h0).elim
        · exact Or.inr (Or.inr (Or.inl (Prod.ext hx' hy')))
        · exact Or.inr (Or.inr (Or.inr (Prod.ext hx' hy')))
  split_ifs with hq
  · obtain ⟨h3, hx, hy⟩ := hequiv.mp hq
    obtain ⟨c, _, _, _, hc⟩ := eligible t h3 hx hy
    exact hc
  · exact zero_count t ht (fun h ↦ hq (hequiv.mpr h))


#print axioms stabilizing_translation_three_torsion
#print axioms fixed_point_census

end D5.S3.Factorization.CollinearTripleFixedPointCensus
