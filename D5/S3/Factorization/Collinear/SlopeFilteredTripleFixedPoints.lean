/- GID: D5/S3/Factorization/Collinear/SlopeFilteredTripleFixedPoints
   generality: I
   mirror-B: D5/B/S3/Factorization/Collinear/SlopeFilteredTripleFixedPoints
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A slope filters three-cycle fixed points by its effect on their direction. -/

import D5.S3.Factorization.FiniteTranslationStabilizer
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints

open scoped Pointwise
open D5.S3.Factorization.FiniteTranslationStabilizer

/-- Three abscissae whose images under multiplication by the slope remain distinct. -/
def SlopeTriple (n : ℕ) (a : ZMod n) :=
  {X : Finset (ZMod n) // X.card = 3 ∧ Set.InjOn (a * ·) (X : Set (ZMod n))}

instance (n : ℕ) [NeZero n] (a : ZMod n) : Finite (SlopeTriple n a) := by
  unfold SlopeTriple
  infer_instance

noncomputable instance (n : ℕ) (a : ZMod n) : AddAction (ZMod n) (SlopeTriple n a) where
  vadd t X := ⟨t +ᵥ X.val, by
    classical
    constructor
    · exact (Finset.card_vadd_finset t X.val).trans X.property.1
    · intro x hx y hy heq
      obtain ⟨x, hx', rfl⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨y, hy', rfl⟩ := Finset.mem_vadd_finset.mp hy
      have heq' : a * (t + x) = a * (t + y) := by
        simpa only [vadd_eq_add] using heq
      have hxy : a * x = a * y := by
        linear_combination heq'
      simpa only [vadd_eq_add] using
        congrArg (t + ·) (X.property.2 hx' hy' hxy)⟩
  zero_vadd X := Subtype.ext (zero_vadd _ X.val)
  add_vadd t u X := Subtype.ext (add_vadd t u X.val)

/-- A nonzero translation fixes either no slope-admissible triples, or one
three-cycle orbit. The latter occurs exactly when it has order three and its
image under multiplication by the slope is nonzero. -/
theorem card_fixedBy_nonzero (n : ℕ) [NeZero n] (a t : ZMod n) (ht0 : t ≠ 0) :
    Nat.card (AddAction.fixedBy (SlopeTriple n a) t) =
      if 3 • t = 0 ∧ a * t ≠ 0 then n / 3 else 0 := by
  classical
  have hcard3 (z : ZMod n) (hz3 : 3 • z = 0) (hz0 : z ≠ 0) :
      ({0, z, (2 : ℕ) • z} : Finset (ZMod n)).card = 3 := by
    have hz2 : (2 : ℕ) • z ≠ 0 := by
      intro h2
      have h : z = 3 • z - 2 • z := by abel
      rw [hz3, h2, sub_self] at h
      exact hz0 h
    have hz12 : z ≠ (2 : ℕ) • z := by
      intro h
      have h' : z = z + z := by simpa only [two_nsmul] using h
      exact hz0 (add_left_cancel (by simpa only [add_zero] using h'.symm))
    have h0mem : (0 : ZMod n) ∉ ({z, (2 : ℕ) • z} : Finset (ZMod n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hz0, Ne.symm hz2⟩
    have hzmem : z ∉ ({(2 : ℕ) • z} : Finset (ZMod n)) := by
      simpa only [Finset.mem_singleton] using hz12
    rw [Finset.card_insert_of_notMem h0mem,
      Finset.card_insert_of_notMem hzmem, Finset.card_singleton]
  by_cases ht3 : 3 • t = 0
  · by_cases hat0 : a * t = 0
    · have hzero : Nat.card (AddAction.fixedBy (SlopeTriple n a) t) = 0 := by
        apply Finite.card_eq_zero_iff.mpr
        refine ⟨fun X => ?_⟩
        have hfixed : t +ᵥ X.val.val = X.val.val :=
          congrArg (fun Y : SlopeTriple n a => Y.val) X.property
        obtain ⟨p, hp⟩ : X.val.val.Nonempty :=
          Finset.card_pos.mp (by rw [X.val.property.1]; omega)
        have htp : t + p ∈ X.val.val := by
          have h : t + p ∈ t +ᵥ X.val.val :=
            Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
          simpa only [hfixed] using h
        have heq : t + p = p := X.val.property.2 htp hp (by
          calc
            a * (t + p) = a * t + a * p := by ring
            _ = a * p := by rw [hat0, zero_add])
        exact ht0 (add_right_cancel (heq.trans (zero_add p).symm))
      simpa [ht3, hat0] using hzero
    · have hat3 : 3 • (a * t) = 0 := by
        simpa [nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
          congrArg (a * ·) ht3
      have hXcard := hcard3 t ht3 ht0
      have hYcard := hcard3 (a * t) hat3 hat0
      have hXinj : Set.InjOn (a * ·)
          (({0, t, (2 : ℕ) • t} : Finset (ZMod n)) : Set (ZMod n)) := by
        apply Finset.card_image_iff.mp
        have himage : ({0, t, (2 : ℕ) • t} : Finset (ZMod n)).image (a * ·) =
            {0, a * t, (2 : ℕ) • (a * t)} := by
          simp [Finset.image_insert, Finset.image_singleton, nsmul_eq_mul,
            mul_assoc, mul_left_comm, mul_comm]
        rw [himage, hXcard, hYcard]
      let c : SlopeTriple n a := ⟨{0, t, (2 : ℕ) • t}, hXcard, hXinj⟩
      have hcycle : t +ᵥ c = c := by
        apply Subtype.ext
        have ht2 : t + t = (2 : ℕ) • t := (two_nsmul t).symm
        have ht3' : t + (2 : ℕ) • t = 0 := by
          calc
            t + (2 : ℕ) • t = 3 • t := by abel
            _ = 0 := ht3
        change t +ᵥ ({0, t, (2 : ℕ) • t} : Finset (ZMod n)) = _
        rw [Finset.vadd_finset_def]
        simp only [Finset.image_insert, Finset.image_singleton, vadd_eq_add,
          add_zero, ht2, ht3']
        change ({t, (2 : ℕ) • t, 0} : Finset (ZMod n)) = {0, t, (2 : ℕ) • t}
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hfixed_eq : AddAction.fixedBy (SlopeTriple n a) t =
          AddAction.orbit (ZMod n) c := by
        ext X
        constructor
        · intro hX
          have hset : t +ᵥ X.val = X.val := congrArg Subtype.val hX
          obtain ⟨p, hp⟩ : X.val.Nonempty :=
            Finset.card_pos.mp (by rw [X.property.1]; omega)
          have hthree := three_point_eq_translation_cycle X.val X.property.1
            t hset ht0 p hp
          apply AddAction.mem_orbit_iff.mpr
          refine ⟨p, Subtype.ext ?_⟩
          change p +ᵥ ({0, t, (2 : ℕ) • t} : Finset (ZMod n)) = X.val
          rw [hthree, Finset.vadd_finset_def]
          ext x
          simp only [Finset.image_insert, Finset.image_singleton,
            Finset.mem_insert, Finset.mem_singleton, vadd_eq_add, add_zero]
          simp [add_comm]
        · rintro ⟨p, rfl⟩
          change t +ᵥ (p +ᵥ c) = p +ᵥ c
          rw [← add_vadd, add_comm t p, add_vadd, hcycle]
      have hstab : Nat.card (AddAction.stabilizer (ZMod n) c) = 3 := by
        have hstab_eq : AddAction.stabilizer (ZMod n) c =
            AddAction.stabilizer (ZMod n) c.val := by
          ext u
          constructor
          · intro hu
            exact congrArg Subtype.val hu
          · intro hu
            exact Subtype.ext hu
        have hdiv : Nat.card (AddAction.stabilizer (ZMod n) c) ∣ 3 := by
          rw [hstab_eq]
          simpa only [c, hXcard] using stabilizer_card_dvd_card c.val
        have hne : Nat.card (AddAction.stabilizer (ZMod n) c) ≠ 1 := by
          intro h
          have hsub : Subsingleton (AddAction.stabilizer (ZMod n) c) :=
            (Finite.card_le_one_iff_subsingleton).mp (le_of_eq h)
          have hz : (⟨t, hcycle⟩ : AddAction.stabilizer (ZMod n) c) = 0 :=
            Subsingleton.elim _ _
          exact ht0 (congrArg Subtype.val hz)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
        · exact False.elim (hne h)
        · exact h
      letI : Fintype (AddAction.orbit (ZMod n) c) := Fintype.ofFinite _
      have horbit := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup
        (ZMod n) c
      have hcard : Nat.card (AddAction.orbit (ZMod n) c) * 3 = n := by
        rw [show Fintype.card (AddAction.stabilizer (ZMod n) c) = 3 by
          simpa only [Nat.card_eq_fintype_card] using hstab,
          ZMod.card] at horbit
        simpa only [Nat.card_eq_fintype_card] using horbit
      rw [hfixed_eq]
      have hresult : Nat.card (AddAction.orbit (ZMod n) c) = n / 3 := by
        omega
      simpa [ht3, hat0] using hresult
  · have hzero : Nat.card (AddAction.fixedBy (SlopeTriple n a) t) = 0 := by
      apply Finite.card_eq_zero_iff.mpr
      refine ⟨fun X => ?_⟩
      have hset : t +ᵥ X.val.val = X.val.val :=
        congrArg (fun Y : SlopeTriple n a => Y.val) X.property
      have hthree : 3 • t = 0 := by
        simpa only [X.val.property.1] using
          card_nsmul_eq_zero_of_vadd_finset_eq X.val.val t hset
      exact ht3 hthree
    rw [if_neg (by intro h; exact ht3 h.1)]
    exact hzero

#print axioms card_fixedBy_nonzero

end D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints
