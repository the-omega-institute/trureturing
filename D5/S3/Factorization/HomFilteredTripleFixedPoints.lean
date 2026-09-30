/- GID: D5/S3/Factorization/HomFilteredTripleFixedPoints
   generality: I
   mirror-B: D5/B/S3/Factorization/HomFilteredTripleFixedPoints
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A homomorphism filters three-cycle fixed points by its kernel. -/

import D5.S3.Factorization.FiniteTranslationStabilizer
import Mathlib.Tactic

namespace D5.S3.Factorization.HomFilteredTripleFixedPoints

open scoped Pointwise
open D5.S3.Factorization.FiniteTranslationStabilizer

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]
  [DecidableEq G] [DecidableEq A]

/-- Three points whose images under an additive homomorphism are distinct. -/
def HomTriple (f : G →+ A) :=
  {X : Finset G // X.card = 3 ∧ Set.InjOn f (X : Set G)}

instance [Finite G] (f : G →+ A) : Finite (HomTriple f) := by
  unfold HomTriple
  infer_instance

noncomputable instance (f : G →+ A) : AddAction G (HomTriple f) where
  vadd t X := ⟨t +ᵥ X.val, by
    classical
    constructor
    · exact (Finset.card_vadd_finset t X.val).trans X.property.1
    · intro x hx y hy heq
      obtain ⟨x, hx', rfl⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨y, hy', rfl⟩ := Finset.mem_vadd_finset.mp hy
      have heq' : f (t + x) = f (t + y) := by
        simpa only [vadd_eq_add] using heq
      have hxy : f x = f y := by
        apply add_left_cancel (a := f t)
        simpa only [map_add] using heq'
      simpa only [vadd_eq_add] using
        congrArg (t + ·) (X.property.2 hx' hy' hxy)⟩
  zero_vadd X := Subtype.ext (zero_vadd _ X.val)
  add_vadd t u X := Subtype.ext (add_vadd t u X.val)

/-- A nonzero translation fixes either no homomorphism-admissible triples or
one three-cycle orbit, according to whether its order-three direction survives
the homomorphism. -/
theorem card_fixedBy_nonzero [Finite G] (f : G →+ A) (t : G) (ht0 : t ≠ 0) :
    Nat.card (AddAction.fixedBy (HomTriple f) t) =
      if 3 • t = 0 ∧ f t ≠ 0 then Nat.card G / 3 else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  by_cases ht3 : 3 • t = 0
  · by_cases hft0 : f t = 0
    · have hzero : Nat.card (AddAction.fixedBy (HomTriple f) t) = 0 := by
        apply Finite.card_eq_zero_iff.mpr
        refine ⟨fun X => ?_⟩
        have hfixed : t +ᵥ X.val.val = X.val.val :=
          congrArg (fun Y : HomTriple f => Y.val) X.property
        obtain ⟨p, hp⟩ : X.val.val.Nonempty :=
          Finset.card_pos.mp (by rw [X.val.property.1]; omega)
        have htp : t + p ∈ X.val.val := by
          have h : t + p ∈ t +ᵥ X.val.val :=
            Finset.mem_vadd_finset.mpr ⟨p, hp, rfl⟩
          simpa only [hfixed] using h
        have heq : t + p = p := X.val.property.2 htp hp (by
          calc
            f (t + p) = f t + f p := map_add f t p
            _ = f p := by rw [hft0, zero_add])
        exact ht0 (add_right_cancel (heq.trans (zero_add p).symm))
      simpa [ht3, hft0] using hzero
    · have hft3 : 3 • f t = 0 := by
        simpa only [map_nsmul, map_zero] using congrArg f ht3
      have hXcard : ({0, t, (2 : ℕ) • t} : Finset G).card = 3 := by
        have ht2 : (2 : ℕ) • t ≠ 0 := by
          intro h2
          have h : t = 3 • t - 2 • t := by abel
          rw [ht3, h2, sub_self] at h
          exact ht0 h
        have ht12 : t ≠ (2 : ℕ) • t := by
          intro h
          have h' : t = t + t := by simpa only [two_nsmul] using h
          exact ht0 (add_left_cancel (by simpa only [add_zero] using h'.symm))
        have h0mem : (0 : G) ∉ ({t, (2 : ℕ) • t} : Finset G) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm ht0, Ne.symm ht2⟩
        have htmem : t ∉ ({(2 : ℕ) • t} : Finset G) := by
          simpa only [Finset.mem_singleton] using ht12
        rw [Finset.card_insert_of_notMem h0mem,
          Finset.card_insert_of_notMem htmem, Finset.card_singleton]
      have hYcard : ({0, f t, (2 : ℕ) • f t} : Finset A).card = 3 := by
        have hf2 : (2 : ℕ) • f t ≠ 0 := by
          intro h2
          have h : f t = 3 • f t - 2 • f t := by abel
          rw [hft3, h2, sub_self] at h
          exact hft0 h
        have hf12 : f t ≠ (2 : ℕ) • f t := by
          intro h
          have h' : f t = f t + f t := by simpa only [two_nsmul] using h
          exact hft0 (add_left_cancel (by simpa only [add_zero] using h'.symm))
        have h0mem : (0 : A) ∉ ({f t, (2 : ℕ) • f t} : Finset A) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hft0, Ne.symm hf2⟩
        have hfmem : f t ∉ ({(2 : ℕ) • f t} : Finset A) := by
          simpa only [Finset.mem_singleton] using hf12
        rw [Finset.card_insert_of_notMem h0mem,
          Finset.card_insert_of_notMem hfmem, Finset.card_singleton]
      have hXinj : Set.InjOn f
          (({0, t, (2 : ℕ) • t} : Finset G) : Set G) := by
        apply Finset.card_image_iff.mp
        have himage : ({0, t, (2 : ℕ) • t} : Finset G).image f =
            ({0, f t, (2 : ℕ) • (f t)} : Finset A) := by
          simp [Finset.image_insert, Finset.image_singleton, map_nsmul]
        rw [himage, hXcard, hYcard]
      let c : HomTriple f := ⟨{0, t, (2 : ℕ) • t}, hXcard, hXinj⟩
      have hcycle : t +ᵥ c = c := by
        apply Subtype.ext
        have ht2 : t + t = (2 : ℕ) • t := (two_nsmul t).symm
        have ht3' : t + (2 : ℕ) • t = 0 := by
          calc
            t + (2 : ℕ) • t = 3 • t := by abel
            _ = 0 := ht3
        change t +ᵥ ({0, t, (2 : ℕ) • t} : Finset G) = _
        rw [Finset.vadd_finset_def]
        simp only [Finset.image_insert, Finset.image_singleton, vadd_eq_add,
          add_zero, ht2, ht3']
        change ({t, (2 : ℕ) • t, 0} : Finset G) = {0, t, (2 : ℕ) • t}
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hfixed_eq : AddAction.fixedBy (HomTriple f) t =
          AddAction.orbit G c := by
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
          change p +ᵥ ({0, t, (2 : ℕ) • t} : Finset G) = X.val
          rw [hthree, Finset.vadd_finset_def]
          ext x
          simp only [Finset.image_insert, Finset.image_singleton,
            Finset.mem_insert, Finset.mem_singleton, vadd_eq_add, add_zero]
          simp [add_comm]
        · rintro ⟨p, rfl⟩
          change t +ᵥ (p +ᵥ c) = p +ᵥ c
          rw [← add_vadd, add_comm t p, add_vadd, hcycle]
      have hstab : Nat.card (AddAction.stabilizer G c) = 3 := by
        have hstab_eq : AddAction.stabilizer G c =
            AddAction.stabilizer G c.val := by
          ext u
          constructor
          · intro hu
            exact congrArg Subtype.val hu
          · intro hu
            exact Subtype.ext hu
        have hdiv : Nat.card (AddAction.stabilizer G c) ∣ 3 := by
          rw [hstab_eq]
          simpa only [c, hXcard] using stabilizer_card_dvd_card c.val
        have hne : Nat.card (AddAction.stabilizer G c) ≠ 1 := by
          intro h
          have hsub : Subsingleton (AddAction.stabilizer G c) :=
            (Finite.card_le_one_iff_subsingleton).mp (le_of_eq h)
          have hz : (⟨t, hcycle⟩ : AddAction.stabilizer G c) = 0 :=
            Subsingleton.elim _ _
          exact ht0 (congrArg Subtype.val hz)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
        · exact False.elim (hne h)
        · exact h
      letI : Fintype (AddAction.orbit G c) := Fintype.ofFinite _
      have horbit := AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup G c
      have hcard : Nat.card (AddAction.orbit G c) * 3 = Nat.card G := by
        rw [show Fintype.card (AddAction.stabilizer G c) = 3 by
          simpa only [Nat.card_eq_fintype_card] using hstab] at horbit
        simpa only [Nat.card_eq_fintype_card] using horbit
      rw [hfixed_eq]
      have hresult : Nat.card (AddAction.orbit G c) = Nat.card G / 3 := by
        omega
      simpa [ht3, hft0] using hresult
  · have hzero : Nat.card (AddAction.fixedBy (HomTriple f) t) = 0 := by
      apply Finite.card_eq_zero_iff.mpr
      refine ⟨fun X => ?_⟩
      have hset : t +ᵥ X.val.val = X.val.val :=
        congrArg (fun Y : HomTriple f => Y.val) X.property
      have hthree : 3 • t = 0 := by
        simpa only [X.val.property.1] using
          card_nsmul_eq_zero_of_vadd_finset_eq X.val.val t hset
      exact ht3 hthree
    rw [if_neg (by intro h; exact ht3 h.1)]
    exact hzero

#print axioms card_fixedBy_nonzero

end D5.S3.Factorization.HomFilteredTripleFixedPoints
