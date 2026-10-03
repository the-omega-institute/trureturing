/- GID: D5/S3/Factorization/CollinearTripleThreeTorsion
   generality: I
   mirror-B: D5/B/S3/Factorization/CollinearTripleThreeTorsion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Nontrivial translation symmetries of collinear triples have two diagonal directions. -/

import D5.S3.Factorization.CollinearTripleTranslationOrbits
import D5.S3.Factorization.FiniteTranslationStabilizer
import D5.S3.Factorization.ThreeTorsionZMod
import Mathlib.Tactic.Ring

namespace D5.S3.Factorization.CollinearTripleThreeTorsion

open scoped Pointwise
open D5.S3.Factorization.CollinearTripleTranslationOrbits

/-- A nonzero stabilizing translation of an admissible triple cannot vanish in
either coordinate. -/
private theorem stabilizer_coordinates_nonzero {n : ℕ} (s : Triple n)
    (t : Point n) (ht : t +ᵥ s = s) (ht0 : t ≠ 0) :
    t.1 ≠ 0 ∧ t.2 ≠ 0 := by
  classical
  have hset : t +ᵥ s.val = s.val := congrArg Subtype.val ht
  have hnonempty : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property.1]; omega)
  obtain ⟨p, hp⟩ := hnonempty
  have htp : t + p ∈ s.val := by
    have h : t + p ∈ t +ᵥ s.val :=
      Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
    simpa only [hset] using h
  constructor
  · intro hz
    have heq : (t + p).1 = p.1 := by simp [hz]
    have hpoint : t + p = p := s.property.2.1 htp hp heq
    have htzero : t = 0 := add_right_cancel
      (hpoint.trans (zero_add p).symm)
    exact ht0 htzero
  · intro hz
    have heq : (t + p).2 = p.2 := by simp [hz]
    have hpoint : t + p = p := s.property.2.2.1 htp hp heq
    have htzero : t = 0 := add_right_cancel
      (hpoint.trans (zero_add p).symm)
    exact ht0 htzero

/-- Every nontrivial translation symmetry is one of four signed diagonal
three-torsion vectors, leaving exactly two cyclic directions. -/
theorem stabilizer_direction_four (m : ℕ) (hm : 0 < m)
    (s : Triple (3 * m)) (t : Point (3 * m))
    (ht : t +ᵥ s = s) (ht0 : t ≠ 0) :
    t = ((m : ZMod (3 * m)), (m : ZMod (3 * m))) ∨
    t = ((m : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m))) ∨
    t = (((2 * m : ℕ) : ZMod (3 * m)), (m : ZMod (3 * m))) ∨
    t = (((2 * m : ℕ) : ZMod (3 * m)),
      ((2 * m : ℕ) : ZMod (3 * m))) := by
  classical
  have hset : t +ᵥ s.val = s.val := congrArg Subtype.val ht
  have hthree : 3 • t = 0 := by
    simpa only [s.property.1] using
      D5.S3.Factorization.FiniteTranslationStabilizer.card_nsmul_eq_zero_of_vadd_finset_eq
        s.val t hset
  have hfirst : 3 • t.1 = 0 := congrArg Prod.fst hthree
  have hsecond : 3 • t.2 = 0 := congrArg Prod.snd hthree
  obtain ⟨hnz1, hnz2⟩ := stabilizer_coordinates_nonzero s t ht ht0
  rcases (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm t.1).mp
      hfirst with h1 | h1 | h1
  · exact False.elim (hnz1 h1)
  · rcases (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm t.2).mp
        hsecond with h2 | h2 | h2
    · exact False.elim (hnz2 h2)
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Or.inl (Prod.ext h1 h2))
  · rcases (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm t.2).mp
        hsecond with h2 | h2 | h2
    · exact False.elim (hnz2 h2)
    · exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))
    · exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))

/-- A three-torsion direction whose two coordinates are nonzero determines
an admissible collinear triple through the origin. -/
theorem three_cycle_collinear {n : ℕ} (t : Point n)
    (hfirst : 3 • t.1 = 0) (hsecond : 3 • t.2 = 0)
    (hnz1 : t.1 ≠ 0) (hnz2 : t.2 ≠ 0) :
    IsCollinearTriple ({0, t, (2 : ℕ) • t} : Finset (Point n)) := by
  classical
  have h2nz (x : ZMod n) (h3 : 3 • x = 0) (hx : x ≠ 0) :
      (2 : ℕ) • x ≠ 0 := by
    intro h2
    have heq : x = 3 • x - 2 • x := by
      simp only [succ_nsmul]
      abel
    rw [h3, h2, sub_self] at heq
    exact hx heq
  have hdiff (x : ZMod n) (hx : x ≠ 0) : x ≠ (2 : ℕ) • x := by
    intro h
    have : x = x + x := by simpa only [two_nsmul] using h
    exact hx (add_left_cancel (by simpa only [add_zero] using this.symm))
  have h2nz1 := h2nz t.1 hfirst hnz1
  have h2nz2 := h2nz t.2 hsecond hnz2
  have hdiff1 := hdiff t.1 hnz1
  have hdiff2 := hdiff t.2 hnz2
  have ht0 : t ≠ 0 := by intro h; exact hnz1 (congrArg Prod.fst h)
  have h20 : (2 : ℕ) • t ≠ 0 := by
    intro h
    exact h2nz1 (congrArg Prod.fst h)
  have ht2 : t ≠ (2 : ℕ) • t := by
    intro h
    exact hdiff1 (congrArg Prod.fst h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0mem : (0 : Point n) ∉ ({t, (2 : ℕ) • t} : Finset (Point n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ht0, Ne.symm h20⟩
    have htmem : t ∉ ({(2 : ℕ) • t} : Finset (Point n)) := by
      simpa only [Finset.mem_singleton] using ht2
    rw [Finset.card_insert_of_notMem h0mem,
      Finset.card_insert_of_notMem htmem, Finset.card_singleton]
  · intro p hp q hq heq
    change p ∈ ({0, t, (2 : ℕ) • t} : Finset (Point n)) at hp
    change q ∈ ({0, t, (2 : ℕ) • t} : Finset (Point n)) at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim (hnz1 heq)
      | exact False.elim (hnz1 heq.symm)
      | exact False.elim (h2nz1 (by simpa [nsmul_eq_mul, Prod.fst_mul] using heq))
      | exact False.elim (h2nz1 (by simpa [nsmul_eq_mul, Prod.fst_mul] using heq.symm))
      | exact False.elim (hdiff1 (by simpa [nsmul_eq_mul, Prod.fst_mul] using heq))
      | exact False.elim (hdiff1 (by simpa [nsmul_eq_mul, Prod.fst_mul] using heq.symm))
  · intro p hp q hq heq
    change p ∈ ({0, t, (2 : ℕ) • t} : Finset (Point n)) at hp
    change q ∈ ({0, t, (2 : ℕ) • t} : Finset (Point n)) at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim (hnz2 heq)
      | exact False.elim (hnz2 heq.symm)
      | exact False.elim (h2nz2 (by simpa [nsmul_eq_mul, Prod.snd_mul] using heq))
      | exact False.elim (h2nz2 (by simpa [nsmul_eq_mul, Prod.snd_mul] using heq.symm))
      | exact False.elim (hdiff2 (by simpa [nsmul_eq_mul, Prod.snd_mul] using heq))
      | exact False.elim (hdiff2 (by simpa [nsmul_eq_mul, Prod.snd_mul] using heq.symm))
  · intro p hp q hq r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl <;>
      simp [two_nsmul, Prod.fst_add, Prod.snd_add] <;> ring

/-- Both diagonal order-three directions actually produce admissible triples. -/
theorem two_canonical_cycles_collinear (m : ℕ) (hm : 0 < m) :
    IsCollinearTriple
      ({0, ((m : ZMod (3 * m)), (m : ZMod (3 * m))),
        (2 : ℕ) • ((m : ZMod (3 * m)), (m : ZMod (3 * m)))} :
        Finset (Point (3 * m))) ∧
    IsCollinearTriple
      ({0, ((m : ZMod (3 * m)), ((2 * m : ℕ) : ZMod (3 * m))),
        (2 : ℕ) • ((m : ZMod (3 * m)),
          ((2 * m : ℕ) : ZMod (3 * m)))} :
        Finset (Point (3 * m))) := by
  letI : NeZero (3 * m) := ⟨by omega⟩
  have hnonzero (a : ℕ) (ha : 0 < a) (hlt : a < 3 * m) :
      (a : ZMod (3 * m)) ≠ 0 := by
    intro hz
    have hd : 3 * m ∣ a := (ZMod.natCast_eq_zero_iff a (3 * m)).mp hz
    have hle : 3 * m ≤ a := Nat.le_of_dvd ha hd
    omega
  have hm0 : (m : ZMod (3 * m)) ≠ 0 :=
    hnonzero m hm (by omega)
  have h2m0 : (((2 * m : ℕ) : ZMod (3 * m))) ≠ 0 :=
    hnonzero (2 * m) (by omega) (by omega)
  have hm3 : 3 • (m : ZMod (3 * m)) = 0 :=
    (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm _).mpr
      (Or.inr (Or.inl rfl))
  have h2m3 : 3 • (((2 * m : ℕ) : ZMod (3 * m))) = 0 :=
    (D5.S3.Factorization.ThreeTorsionZMod.three_nsmul_eq_zero_iff m hm _).mpr
      (Or.inr (Or.inr rfl))
  exact ⟨three_cycle_collinear _ hm3 hm3 hm0 hm0,
    three_cycle_collinear _ hm3 h2m3 hm0 h2m0⟩

#print axioms stabilizer_direction_four
#print axioms three_cycle_collinear
#print axioms two_canonical_cycles_collinear

end D5.S3.Factorization.CollinearTripleThreeTorsion
