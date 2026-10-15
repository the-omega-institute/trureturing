/- GID: D5/S3/Factorization/HomomorphismFilteredTripleCensus
   generality: G
   mirror-B: D5/B/S3/Factorization/HomomorphismFilteredTripleCensus
   mirror-E: none(waiver:universal-structural-counting-theorem)
   anchors: []
   utility: none
   digest: Homomorphism-injective triples have exact cyclic fixed families and census. -/

import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

namespace D5.S3.Factorization.HomomorphismFilteredTripleCensus

open scoped Pointwise

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- The literal family of unordered three-element sets on which the homomorphism is injective. -/
def IsFilteredTriple (f : G →+ A) (s : Finset G) : Prop :=
  s.card = 3 ∧ Set.InjOn f (s : Set G)

/-- Members retain their actual finite point sets, not a classification or count oracle. -/
def Triple (f : G →+ A) := {s : Finset G // IsFilteredTriple f s}

/-- The first three multiples of a direction, without an order assumption. -/
noncomputable def cycle (t : G) : Finset G := by
  classical
  exact (Finset.range 3).image (fun k ↦ k • t)

private theorem translate_preserves [DecidableEq G] (f : G →+ A)
    {s : Finset G} (hs : IsFilteredTriple f s) (t : G) :
    IsFilteredTriple f (t +ᵥ s) := by
  refine ⟨(Finset.card_vadd_finset t s).trans hs.1, ?_⟩
  intro p hp q hq heq
  obtain ⟨p, hsp, rfl⟩ := Finset.mem_vadd_finset.mp hp
  obtain ⟨q, hsq, rfl⟩ := Finset.mem_vadd_finset.mp hq
  have h : f p = f q := add_left_cancel (by simpa only [vadd_eq_add, map_add] using heq)
  exact congrArg (t + ·) (hs.2 hsp hsq h)

noncomputable instance (f : G →+ A) : AddAction G (Triple f) where
  vadd t s := by
    classical
    exact ⟨t +ᵥ s.val, translate_preserves f s.property t⟩
  zero_vadd s := by classical exact Subtype.ext (zero_vadd _ s.val)
  add_vadd t u s := by classical exact Subtype.ext (add_vadd t u s.val)

instance (f : G →+ A) [Finite G] : Finite (Triple f) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  unfold Triple
  infer_instance

private theorem necessary (f : G →+ A) (t : G) (ht : t ≠ 0)
    (s : Triple f) (hs : t +ᵥ s = s) : 3 • t = 0 ∧ f t ≠ 0 := by
  classical
  have hset : t +ᵥ s.val = s.val := congrArg Subtype.val hs
  have hsum := congrArg (fun u : Finset G ↦ ∑ p ∈ u, p) hset
  rw [Finset.vadd_finset_def, Finset.sum_image] at hsum
  · change (∑ p ∈ s.val, (t + p)) = (∑ p ∈ s.val, p) at hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, s.property.1] at hsum
    refine ⟨add_right_cancel (hsum.trans (zero_add _).symm), ?_⟩
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [s.property.1]; decide)
    have htp : t + p ∈ s.val := by
      rw [← hset]
      exact Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
    intro hft
    have heq := s.property.2 htp hp (by simp only [map_add, hft, zero_add])
    exact ht (add_right_cancel (heq.trans (zero_add p).symm))
  · intro p _ q _ h
    exact add_left_cancel h

/-- For arbitrary abelian domain and codomain, nonidentity fixed triples are exactly
the cosets of the three-cycle, with its exact stabilizer and translation fibers.
The excluded cases give an empty actual fixed family. -/
theorem fixed_family_structure (f : G →+ A) (t : G) (ht : t ≠ 0) :
    (∀ s : Triple f, t +ᵥ s = s → 3 • t = 0 ∧ f t ≠ 0) ∧
    (¬(3 • t = 0 ∧ f t ≠ 0) → AddAction.fixedBy (Triple f) t = ∅) ∧
    (3 • t = 0 → f t ≠ 0 →
      ∃ c : Triple f, c.val = cycle t ∧
        (∀ s : Triple f, t +ᵥ s = s ↔ ∃ p : G, p +ᵥ c = s) ∧
        (∀ u : G, u ∈ AddAction.stabilizer G c ↔ u ∈ c.val) ∧
        (∀ p q : G, p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val) ∧
        Nat.card (AddAction.stabilizer G c) = 3) := by
  classical
  refine ⟨necessary f t ht, ?_, ?_⟩
  · intro hbad
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact hbad (necessary f t ht s hs)
  intro h3 hft
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : addOrderOf t = 3 := addOrderOf_eq_prime h3 ht
  have hof : addOrderOf (f t) = 3 :=
    addOrderOf_eq_prime (by simp only [← map_nsmul, h3, map_zero]) hft
  have hi : Set.InjOn (fun k : ℕ ↦ k • t) (↑(Finset.range 3)) := by
    simpa only [Finset.coe_range, ho] using nsmul_injOn_Iio_addOrderOf (x := t)
  have hcard : (cycle t).card = 3 := by
    rw [cycle, Finset.card_image_of_injOn hi, Finset.card_range]
  have hC : IsFilteredTriple f (cycle t) := by
    refine ⟨hcard, ?_⟩
    intro p hp q hq heq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hij : i = j := nsmul_injOn_Iio_addOrderOf (x := f t)
      (by simpa only [hof, Set.mem_Iio] using Finset.mem_range.mp hi)
      (by simpa only [hof, Set.mem_Iio] using Finset.mem_range.mp hj)
      (by simpa only [map_nsmul] using heq)
    rw [hij]
  let c : Triple f := ⟨cycle t, hC⟩
  have hzero : (0 : G) ∈ cycle t := Finset.mem_image.mpr ⟨0, by simp, by simp⟩
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
  have hstab (u : G) : u ∈ AddAction.stabilizer G c ↔ u ∈ cycle t := by
    constructor
    · intro hu
      have hset : u +ᵥ cycle t = cycle t := congrArg Subtype.val hu
      have hmem : u +ᵥ (0 : G) ∈ u +ᵥ cycle t :=
        Finset.mem_vadd_finset.mpr ⟨0, hzero, rfl⟩
      simpa only [vadd_eq_add, add_zero, hset] using hmem
    · intro hu
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      exact (AddAction.stabilizer G c).nsmul_mem hfix i
  have hclass (s : Triple f) : t +ᵥ s = s ↔ ∃ p : G, p +ᵥ c = s := by
    constructor
    · intro hs
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [s.property.1]; decide)
      have hsub : p +ᵥ cycle t ⊆ s.val := by
        intro q hq
        obtain ⟨r, hr, rfl⟩ := Finset.mem_vadd_finset.mp hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
        have hmem : i • t ∈ AddAction.stabilizer G s.val :=
          (AddAction.stabilizer G s.val).nsmul_mem (congrArg Subtype.val hs) i
        simpa only [vadd_eq_add, add_comm] using
          AddAction.mem_stabilizer_finset'.mp hmem hp
      have heq : p +ᵥ cycle t = s.val := Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_vadd_finset, hcard, s.property.1])
      exact ⟨p, Subtype.ext heq⟩
    · rintro ⟨p, rfl⟩
      rw [← add_vadd, add_comm t p, add_vadd, hfix]
  have hfiber (p q : G) : p +ᵥ c = q +ᵥ c ↔ p - q ∈ c.val := by
    rw [← hstab]
    change _ ↔ (p - q) +ᵥ c = c
    constructor
    · intro h
      rw [sub_eq_neg_add, add_vadd, h, neg_vadd_vadd]
    · intro h
      have hh := congrArg (fun s : Triple f ↦ q +ᵥ s) h
      have hq : q + (p - q) = p := by rw [add_comm, sub_add_cancel]
      simpa only [← add_vadd, hq] using hh
  have hstabc : Nat.card (AddAction.stabilizer G c) = 3 := by
    calc
      _ = Nat.card (cycle t) := Nat.card_congr (Equiv.subtypeEquivRight hstab)
      _ = 3 := (Nat.card_eq_finsetCard (cycle t)).trans hcard
  exact ⟨c, rfl, hclass, hstab, hfiber, hstabc⟩

/-- Exact cardinality of the same actual fixed family. Only the domain is finite;
the codomain and the homomorphism's global kernel remain unrestricted. -/
theorem fixed_point_census [Finite G] (f : G →+ A) (t : G) (ht : t ≠ 0) :
    Nat.card (AddAction.fixedBy (Triple f) t) =
      @ite ℕ (3 • t = 0 ∧ f t ≠ 0) (Classical.propDecidable _)
        (Nat.card G / 3) 0 := by
  classical
  obtain ⟨_, hempty, heligible⟩ := fixed_family_structure f t ht
  split_ifs with he
  · obtain ⟨c, _, hclass, _, _, hstabc⟩ := heligible he.1 he.2
    have hset : AddAction.fixedBy (Triple f) t = AddAction.orbit G c := by
      ext s
      exact (hclass s).trans AddAction.mem_orbit_iff.symm
    let : Fintype G := Fintype.ofFinite G
    let : Fintype (AddAction.orbit G c) := Fintype.ofFinite _
    let : Fintype (AddAction.stabilizer G c) := Fintype.ofFinite _
    have hcount := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup G c
    have hcount' : Nat.card (AddAction.orbit G c) * 3 = Nat.card G := by
      simpa only [← Nat.card_eq_fintype_card, hstabc] using hcount
    rw [hset, ← hcount', Nat.mul_div_cancel]
    decide
  · rw [hempty he]
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

#print axioms fixed_family_structure
#print axioms fixed_point_census

end D5.S3.Factorization.HomomorphismFilteredTripleCensus
