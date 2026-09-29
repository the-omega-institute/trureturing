/- GID: D5/S3/Factorization/CollinearTripleFixedPointCensus
   generality: I
   mirror-B: D5/B/S3/Factorization/CollinearTripleFixedPointCensus
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Nonzero order-three translations fix exactly one orbit of collinear triples. -/

import D5.S3.Factorization.CollinearTripleThreeTorsion
import Mathlib.Tactic

namespace D5.S3.Factorization.CollinearTripleFixedPointCensus

open scoped Pointwise
open D5.S3.Factorization.CollinearTripleTranslationOrbits
open D5.S3.Factorization.CollinearTripleThreeTorsion
open D5.S3.Factorization.FiniteTranslationStabilizer

private def cycle {n : ℕ} (t : Point n)
    (hfirst : 3 • t.1 = 0) (hsecond : 3 • t.2 = 0)
    (hnz1 : t.1 ≠ 0) (hnz2 : t.2 ≠ 0) : Triple n :=
  ⟨{0, t, (2 : ℕ) • t}, three_cycle_collinear t hfirst hsecond hnz1 hnz2⟩

private theorem cycle_fixed {n : ℕ} (t : Point n)
    (hfirst : 3 • t.1 = 0) (hsecond : 3 • t.2 = 0)
    (hnz1 : t.1 ≠ 0) (hnz2 : t.2 ≠ 0) :
    t +ᵥ cycle t hfirst hsecond hnz1 hnz2 =
      cycle t hfirst hsecond hnz1 hnz2 := by
  classical
  apply Subtype.ext
  have h3 : 3 • t = 0 := Prod.ext hfirst hsecond
  change t +ᵥ ({0, t, (2 : ℕ) • t} : Finset (Point n)) = _
  rw [Finset.vadd_finset_def]
  simp only [Finset.image_insert, Finset.image_singleton]
  have htwice : t + t = (2 : ℕ) • t := (two_nsmul t).symm
  have hthrice : t + (2 : ℕ) • t = 0 := by
    calc
      t + (2 : ℕ) • t = 3 • t := by abel
      _ = 0 := h3
  simp only [vadd_eq_add, add_zero, cycle]
  change ({t, t + t, t + (2 : ℕ) • t} : Finset (Point n)) =
    {0, t, (2 : ℕ) • t}
  rw [htwice, hthrice]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem fixed_eq_orbit {n : ℕ} [NeZero n] (t : Point n)
    (hfirst : 3 • t.1 = 0) (hsecond : 3 • t.2 = 0)
    (hnz1 : t.1 ≠ 0) (hnz2 : t.2 ≠ 0) :
    AddAction.fixedBy (Triple n) t =
      AddAction.orbit (Point n) (cycle t hfirst hsecond hnz1 hnz2) := by
  classical
  let c := cycle t hfirst hsecond hnz1 hnz2
  have ht0 : t ≠ 0 := by intro h; exact hnz1 (congrArg Prod.fst h)
  ext s
  constructor
  · intro hs
    have hfixed : t +ᵥ s = s := hs
    have hset : t +ᵥ s.val = s.val := congrArg Subtype.val hfixed
    obtain ⟨p, hp⟩ : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property.1]; omega)
    have hcycle := three_point_eq_translation_cycle s.val s.property.1 t hset ht0 p hp
    apply AddAction.mem_orbit_iff.mpr
    refine ⟨p, Subtype.ext ?_⟩
    change p +ᵥ ({0, t, (2 : ℕ) • t} : Finset (Point n)) = s.val
    rw [hcycle]
    ext x
    simp only [Finset.mem_vadd_finset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨y, (rfl | rfl | rfl), rfl⟩ <;> simp [add_comm, add_left_comm, add_assoc]
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨t, by simp, by simp [add_comm]⟩
      · exact ⟨(2 : ℕ) • t, by simp, by simp [add_comm]⟩
  · rintro ⟨p, rfl⟩
    change t +ᵥ (p +ᵥ c) = p +ᵥ c
    rw [← add_vadd, add_comm t p, add_vadd, cycle_fixed t hfirst hsecond hnz1 hnz2]

/-- A nonzero three-torsion vector with both coordinates nonzero fixes exactly
one translation orbit of admissible triples, of size one third of the grid. -/
theorem card_fixedBy_three_torsion {n : ℕ} [NeZero n] (t : Point n)
    (hfirst : 3 • t.1 = 0) (hsecond : 3 • t.2 = 0)
    (hnz1 : t.1 ≠ 0) (hnz2 : t.2 ≠ 0) :
    Nat.card (AddAction.fixedBy (Triple n) t) = n ^ 2 / 3 := by
  classical
  let c := cycle t hfirst hsecond hnz1 hnz2
  have ht0 : t ≠ 0 := by intro h; exact hnz1 (congrArg Prod.fst h)
  have hstab_eq : AddAction.stabilizer (Point n) c =
      AddAction.stabilizer (Point n) c.val := by
    ext u
    constructor
    · intro hu
      exact congrArg Subtype.val hu
    · intro hu
      exact Subtype.ext hu
  have hstab : Nat.card (AddAction.stabilizer (Point n) c) = 3 := by
    have hdiv : Nat.card (AddAction.stabilizer (Point n) c) ∣ 3 := by
      rw [hstab_eq]
      simpa only [c, cycle, (three_cycle_collinear t hfirst hsecond hnz1 hnz2).1]
        using stabilizer_card_dvd_card c.val
    have hne : Nat.card (AddAction.stabilizer (Point n) c) ≠ 1 := by
      intro h
      have hsub : Subsingleton (AddAction.stabilizer (Point n) c) :=
        (Finite.card_le_one_iff_subsingleton).mp (le_of_eq h)
      have hz : (⟨t, cycle_fixed t hfirst hsecond hnz1 hnz2⟩ :
        AddAction.stabilizer (Point n) c) = 0 := Subsingleton.elim _ _
      exact ht0 (congrArg Subtype.val hz)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact False.elim (hne h)
    · exact h
  letI : Fintype (Triple n) := Fintype.ofFinite _
  letI : Fintype (AddAction.orbit (Point n) c) := Fintype.ofFinite _
  have horbit := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup
    (Point n) c
  have hstab' : Fintype.card (AddAction.stabilizer (Point n) c) = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hstab
  have hgroup : Fintype.card (Point n) = n ^ 2 := by
    change Fintype.card (ZMod n × ZMod n) = n ^ 2
    rw [Fintype.card_prod, ZMod.card]
    exact (pow_two n).symm
  have hcard : Nat.card (AddAction.orbit (Point n) c) * 3 = n ^ 2 := by
    rw [hstab', hgroup] at horbit
    simpa only [Nat.card_eq_fintype_card] using horbit
  rw [fixed_eq_orbit t hfirst hsecond hnz1 hnz2]
  calc
    Nat.card (AddAction.orbit (Point n) c) =
        (Nat.card (AddAction.orbit (Point n) c) * 3) / 3 := by omega
    _ = n ^ 2 / 3 := congrArg (· / 3) hcard

private def exceptional (m : ℕ) : Finset (Point (3 * m)) :=
  ({(m : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m))} :
    Finset (ZMod (3 * m))) ×ˢ
  ({(m : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m))} :
    Finset (ZMod (3 * m)))

private theorem exceptional_data (m : ℕ) (hm : 0 < m) :
    (exceptional m).card = 4 ∧
    (0 : Point (3 * m)) ∉ exceptional m ∧
    ∀ t : Point (3 * m), t ∈ exceptional m ↔
      (3 • t.1 = 0 ∧ t.1 ≠ 0) ∧ (3 • t.2 = 0 ∧ t.2 ≠ 0) := by
  classical
  letI : NeZero (3 * m) := ⟨by omega⟩
  let u : ZMod (3 * m) := m
  let v : ZMod (3 * m) := (2 * m : ℕ)
  have hu0 : u ≠ 0 := by
    intro hz
    have hd : 3 * m ∣ m := (ZMod.natCast_eq_zero_iff m (3 * m)).mp hz
    exact (by omega : ¬3 * m ≤ m) (Nat.le_of_dvd hm hd)
  have hv0 : v ≠ 0 := by
    intro hz
    have hd : 3 * m ∣ 2 * m := (ZMod.natCast_eq_zero_iff (2 * m) (3 * m)).mp hz
    exact (by omega : ¬3 * m ≤ 2 * m) (Nat.le_of_dvd (by omega) hd)
  have huv : u ≠ v := by
    intro h
    have hh := congrArg ZMod.val h
    simp only [u, v, ZMod.val_natCast_of_lt (by omega : m < 3 * m),
      ZMod.val_natCast_of_lt (by omega : 2 * m < 3 * m)] at hh
    omega
  have h3u : 3 • u = 0 :=
    (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm u).mpr
      (Or.inr (Or.inl rfl))
  have h3v : 3 • v = 0 :=
    (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm v).mpr
      (Or.inr (Or.inr rfl))
  have htwo : ({u, v} : Finset (ZMod (3 * m))).card = 2 := by
    simp [huv]
  refine ⟨?_, ?_, ?_⟩
  · simp only [exceptional, Finset.card_product]
    change ({u, v} : Finset (ZMod (3 * m))).card * ({u, v} :
      Finset (ZMod (3 * m))).card = 4
    rw [htwo]
  · have h0 : (0 : ZMod (3 * m)) ∉ ({u, v} : Finset (ZMod (3 * m))) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        (show (0 : ZMod (3 * m)) ≠ u ∧ (0 : ZMod (3 * m)) ≠ v from
          ⟨Ne.symm hu0, Ne.symm hv0⟩)
    intro h
    exact h0 (Finset.mem_product.mp h).1
  · intro t
    simp only [exceptional, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rcases h1 with h1 | h1
        · simpa only [h1] using And.intro h3u hu0
        · simpa only [h1] using And.intro h3v hv0
      · rcases h2 with h2 | h2
        · simpa only [h2] using And.intro h3u hu0
        · simpa only [h2] using And.intro h3v hv0
    · rintro ⟨⟨h1, hn1⟩, ⟨h2, hn2⟩⟩
      have hc1 := (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff
        m hm t.1).mp h1
      have hc2 := (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff
        m hm t.2).mp h2
      exact ⟨hc1.resolve_left hn1, hc2.resolve_left hn2⟩

private theorem card_fixedBy_exceptional (m : ℕ) (hm : 0 < m)
    (t : Point (3 * m)) (ht : t ∈ exceptional m) :
    Nat.card (AddAction.fixedBy (Triple (3 * m)) t) = (3 * m) ^ 2 / 3 := by
  letI : NeZero (3 * m) := ⟨by omega⟩
  obtain ⟨⟨h1, hn1⟩, ⟨h2, hn2⟩⟩ := ((exceptional_data m hm).2.2 t).mp ht
  exact card_fixedBy_three_torsion t h1 h2 hn1 hn2

private theorem card_fixedBy_outside (m : ℕ) (hm : 0 < m)
    (t : Point (3 * m)) (ht0 : t ≠ 0) (ht : t ∉ exceptional m) :
    Nat.card (AddAction.fixedBy (Triple (3 * m)) t) = 0 := by
  classical
  letI : NeZero (3 * m) := ⟨by omega⟩
  apply Finite.card_eq_zero_iff.mpr
  refine ⟨fun s => ?_⟩
  have hfixed : t +ᵥ s.val = s.val := s.property
  have hdir := stabilizer_direction_four m hm s.val t hfixed ht0
  apply ht
  rcases hdir with h | h | h | h <;> simp [exceptional, h]

private theorem sum_card_fixedBy (m : ℕ) [NeZero (3 * m)] (hm : 0 < m) :
    (∑ t : Point (3 * m), Nat.card (AddAction.fixedBy (Triple (3 * m)) t)) =
      Nat.card (Triple (3 * m)) + 4 * ((3 * m) ^ 2 / 3) := by
  classical
  let e := exceptional m
  have hecard : e.card = 4 := (exceptional_data m hm).1
  have hzero_not : (0 : Point (3 * m)) ∉ e := (exceptional_data m hm).2.1
  have hzero : Nat.card (AddAction.fixedBy (Triple (3 * m))
      (0 : Point (3 * m))) = Nat.card (Triple (3 * m)) := by
    have heq : AddAction.fixedBy (Triple (3 * m)) (0 : Point (3 * m)) =
        Set.univ := by
      ext s
      simp [AddAction.mem_fixedBy]
    rw [heq]
    simp
  have he : (∑ t ∈ e, Nat.card (AddAction.fixedBy (Triple (3 * m)) t)) =
      e.card * ((3 * m) ^ 2 / 3) :=
    Finset.sum_const_nat (fun t ht => card_fixedBy_exceptional m hm t ht)
  have hsmall :
      (∑ t ∈ insert (0 : Point (3 * m)) e,
        Nat.card (AddAction.fixedBy (Triple (3 * m)) t)) =
      ∑ t : Point (3 * m), Nat.card (AddAction.fixedBy (Triple (3 * m)) t) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have ht0 : t ≠ 0 := by
      intro h
      exact ht (by simp [h])
    have hte : t ∉ e := by
      intro h
      exact ht (Finset.mem_insert.mpr (Or.inr h))
    exact card_fixedBy_outside m hm t ht0 hte
  calc
    (∑ t : Point (3 * m), Nat.card (AddAction.fixedBy (Triple (3 * m)) t)) =
        ∑ t ∈ insert (0 : Point (3 * m)) e,
          Nat.card (AddAction.fixedBy (Triple (3 * m)) t) := hsmall.symm
    _ = Nat.card (Triple (3 * m)) + 4 * ((3 * m) ^ 2 / 3) := by
      rw [Finset.sum_insert hzero_not, hzero, he, hecard]

/-- Exact three-torsion residue for unordered admissible collinear triples. -/
theorem exact_three_torsion_residue (m : ℕ) (hm : 0 < m) :
    ∃ q : ℕ, Nat.card (Triple (3 * m)) =
      (3 * m) ^ 2 * q + 2 * ((3 * m) ^ 2 / 3) := by
  classical
  letI : NeZero (3 * m) := ⟨by omega⟩
  letI : Fintype (Triple (3 * m)) := Fintype.ofFinite _
  letI : Fintype (AddAction.orbitRel.Quotient (Point (3 * m)) (Triple (3 * m))) :=
    Fintype.ofFinite _
  letI : ∀ t : Point (3 * m), Fintype (AddAction.fixedBy (Triple (3 * m)) t) :=
    fun _ => Fintype.ofFinite _
  let O := Nat.card (AddAction.orbitRel.Quotient (Point (3 * m)) (Triple (3 * m)))
  have hpoint : Fintype.card (Point (3 * m)) = (3 * m) ^ 2 := by
    change Fintype.card (ZMod (3 * m) × ZMod (3 * m)) = (3 * m) ^ 2
    rw [Fintype.card_prod, ZMod.card]
    exact (pow_two (3 * m)).symm
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (Point (3 * m)) (Triple (3 * m))
  have hburnNat :
      (∑ t : Point (3 * m), Nat.card (AddAction.fixedBy (Triple (3 * m)) t)) =
      O * (3 * m) ^ 2 := by
    simpa only [O, Nat.card_eq_fintype_card, hpoint] using hburn
  rw [sum_card_fixedBy m hm] at hburnNat
  have hr : (3 * m) ^ 2 = 3 * (3 * m * m) := by ring
  have hd : (3 * m) ^ 2 / 3 = 3 * m * m := by
    rw [hr]
    omega
  have hsq : (3 * m) ^ 2 = 3 * ((3 * m) ^ 2 / 3) := by
    calc
      (3 * m) ^ 2 = 3 * (3 * m * m) := hr
      _ = 3 * ((3 * m) ^ 2 / 3) := by rw [hd]
  have hdpos : 0 < (3 * m) ^ 2 / 3 := by
    rw [hd]
    positivity
  have hO : 2 ≤ O := by
    by_contra h
    have hcases : O = 0 ∨ O = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0, zero_mul] at hburnNat
      omega
    · rw [h1, one_mul, hsq] at hburnNat
      omega
  let q := O - 2
  have hOeq : O = q + 2 := by dsimp [q]; omega
  refine ⟨q, ?_⟩
  rw [hOeq] at hburnNat
  nlinarith [hsq, hburnNat]

#print axioms card_fixedBy_three_torsion
#print axioms exact_three_torsion_residue

end D5.S3.Factorization.CollinearTripleFixedPointCensus
