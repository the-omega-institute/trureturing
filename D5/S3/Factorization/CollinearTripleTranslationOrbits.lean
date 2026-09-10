/- GID: D5/S3/Factorization/CollinearTripleTranslationOrbits
   generality: I
   mirror-B: D5/B/S3/Factorization/CollinearTripleTranslationOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Translation orbits prove square divisibility for collinear triples. -/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

namespace D5.S3.Factorization.CollinearTripleTranslationOrbits

open scoped Pointwise

/-- Points in the square grid modulo n. -/
abbrev Point (n : ℕ) := ZMod n × ZMod n

/-- An unordered three-element set with distinct coordinates and zero determinants. -/
def IsCollinearTriple {n : ℕ} (s : Finset (Point n)) : Prop :=
  s.card = 3 ∧
    Set.InjOn Prod.fst (s : Set (Point n)) ∧
    Set.InjOn Prod.snd (s : Set (Point n)) ∧
    ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s,
      (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- The configurations counted by OEIS A146557, with no ordering of the three points. -/
def Triple (n : ℕ) := {s : Finset (Point n) // IsCollinearTriple s}

instance (n : ℕ) [NeZero n] : Finite (Triple n) := by
  unfold Triple
  infer_instance

private theorem translate_preserves {n : ℕ} {s : Finset (Point n)}
    (hs : IsCollinearTriple s) (t : Point n) : IsCollinearTriple (t +ᵥ s) := by
  classical
  refine ⟨(Finset.card_vadd_finset t s).trans hs.1, ?_, ?_, ?_⟩
  · intro p hp q hq heq
    obtain ⟨p, hsp, rfl⟩ := Finset.mem_vadd_finset.mp hp
    obtain ⟨q, hsq, rfl⟩ := Finset.mem_vadd_finset.mp hq
    have h : p.1 = q.1 := add_left_cancel heq
    exact congrArg (t + ·) (hs.2.1 hsp hsq h)
  · intro p hp q hq heq
    obtain ⟨p, hsp, rfl⟩ := Finset.mem_vadd_finset.mp hp
    obtain ⟨q, hsq, rfl⟩ := Finset.mem_vadd_finset.mp hq
    have h : p.2 = q.2 := add_left_cancel heq
    exact congrArg (t + ·) (hs.2.2.1 hsp hsq h)
  · intro p hp q hq r hr
    obtain ⟨p, hsp, rfl⟩ := Finset.mem_vadd_finset.mp hp
    obtain ⟨q, hsq, rfl⟩ := Finset.mem_vadd_finset.mp hq
    obtain ⟨r, hsr, rfl⟩ := Finset.mem_vadd_finset.mp hr
    simpa only [vadd_eq_add, Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub]
      using hs.2.2.2 p hsp q hsq r hsr

noncomputable instance (n : ℕ) : AddAction (Point n) (Triple n) where
  vadd t s := ⟨t +ᵥ s.val, translate_preserves s.property t⟩
  zero_vadd s := Subtype.ext (zero_vadd _ s.val)
  add_vadd t u s := Subtype.ext (add_vadd t u s.val)

-- Summing the translated set avoids choosing or ordering its three elements.
private theorem stabilizing_translation_three_torsion {n : ℕ}
    (s : Triple n) (t : Point n) (ht : t +ᵥ s = s) : 3 • t = 0 := by
  classical
  have hset : t +ᵥ s.val = s.val := congrArg Subtype.val ht
  have hsum := congrArg (fun u : Finset (Point n) => ∑ p ∈ u, p) hset
  rw [Finset.vadd_finset_def, Finset.sum_image] at hsum
  · change (∑ p ∈ s.val, (t + p)) = (∑ p ∈ s.val, p) at hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, s.property.1] at hsum
    exact add_right_cancel (hsum.trans (zero_add _).symm)
  · intro p _ q _ h
    exact add_left_cancel h

private theorem three_torsion_trivial {n : ℕ} (hn : ¬3 ∣ n) (t : Point n)
    (ht : 3 • t = 0) : t = 0 := by
  have hc : Nat.Coprime 3 n := Nat.prime_three.coprime_iff_not_dvd.mpr hn
  have hz (x : ZMod n) (hx : 3 • x = 0) : x = 0 := by
    have hx' : (ZMod.unitOfCoprime 3 hc : ZMod n) * x = 0 := by
      simpa only [ZMod.coe_unitOfCoprime, nsmul_eq_mul] using hx
    exact (Units.mul_right_eq_zero _).mp hx'
  exact Prod.ext (hz t.1 (congrArg Prod.fst ht)) (hz t.2 (congrArg Prod.snd ht))

/-- If three does not divide the positive modulus, its square divides the number
of unordered collinear triples with pairwise distinct first and second coordinates. -/
theorem square_dvd_card_collinear_triples (n : ℕ) (hn : 0 < n) (hthree : ¬3 ∣ n) :
    n ^ 2 ∣ Nat.card (Triple n) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hfree (s : Triple n) : AddAction.stabilizer (Point n) s = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro t ht
    exact three_torsion_trivial hthree t
      (stabilizing_translation_three_torsion s t ht)
  have hcard := Nat.card_congr (AddAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod] at hcard
  rw [hcard, pow_two]
  exact dvd_mul_left _ _

#print axioms square_dvd_card_collinear_triples
#print axioms instFiniteTripleOfNeZeroNat

end D5.S3.Factorization.CollinearTripleTranslationOrbits
