/- GID: D5/S3/Arith/ResidueRings/MesyanQuantaleUnit
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueRings/MesyanQuantaleUnit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The prime-residue direct sum is nonzero, has no ring identity, and has top as its additive-submonoid product identity. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Submonoid.Pointwise
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.NonUnitalSubring.Defs
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The direct sum of the prime residue rings is nonzero and has no multiplicative
identity. Its top additive submonoid is a two-sided identity for the product
of additive submonoids, identified with the positive finite sums in Definition 4
of Mesyan, *Quantales Arising From Rings*.
-/

open scoped BigOperators Pointwise

namespace D5.S3.Arith.ResidueRings.MesyanQuantaleUnit

noncomputable section

/-- Membership in the product from Definition 4, including the condition that the
number of summands is positive. The subtypes enforce membership of each factor. -/
private theorem mem_product_iff {A : Type*} [NonUnitalNonAssocSemiring A]
    (S T : AddSubmonoid A) (x : A) :
    x ∈ S * T ↔
      ∃ n : ℕ, 0 < n ∧
        ∃ (s : Fin n → S) (t : Fin n → T),
          (∑ i, (s i : A) * (t i : A)) = x := by
  constructor
  · intro hx
    refine AddSubmonoid.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      refine ⟨1, Nat.one_pos, fun _ => ⟨a, ha⟩, fun _ => ⟨b, hb⟩, ?_⟩
      simp
    · rintro a b ⟨n, hn, s, t, ha⟩ ⟨m, _, s', t', hb⟩
      refine ⟨n + m, Nat.add_pos_left hn m, Fin.addCases s s', Fin.addCases t t', ?_⟩
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, ha, hb]
  · rintro ⟨n, _, s, t, rfl⟩
    exact AddSubmonoid.sum_mem _ fun i _ =>
      AddSubmonoid.mul_mem_mul (s i).property (t i).property

private def support (a : (p : Nat.Primes) → ZMod (p : ℕ)) : Set Nat.Primes := {p | a p ≠ 0}

/-- The direct sum inside the product with coordinatewise ring operations. -/
def finiteSupportSubring : NonUnitalSubring ((p : Nat.Primes) → ZMod (p : ℕ)) where
  carrier := {a | (support a).Finite}
  zero_mem' := by
    change (support 0).Finite
    have h : support 0 = ∅ := by ext p; simp [support]
    rw [h]
    exact Set.finite_empty
  add_mem' {a b} ha hb := by
    change (support a).Finite at ha
    change (support b).Finite at hb
    exact (ha.union hb).subset fun p hp => by
      change a p + b p ≠ 0 at hp
      change a p ≠ 0 ∨ b p ≠ 0
      by_cases ha0 : a p = 0
      · exact Or.inr fun hb0 => hp (by rw [ha0, hb0, zero_add])
      · exact Or.inl ha0
  mul_mem' {a b} ha _ := by
    change (support a).Finite at ha
    exact ha.subset fun p hp ha0 =>
      hp (show a p * b p = 0 by rw [ha0, zero_mul])
  neg_mem' {a} ha := by
    change (support a).Finite at ha
    exact ha.subset fun p hp ha0 =>
      hp (show -a p = 0 by rw [ha0, neg_zero])

private instance (p : Nat.Primes) : NeZero (p : ℕ) := ⟨p.property.ne_zero⟩

private instance (p : Nat.Primes) : Fact (1 < (p : ℕ)) := ⟨p.property.one_lt⟩

private theorem finite_support (a : ↥finiteSupportSubring) : (support a.val).Finite := a.property

/-- The natural CRT representative on the support of the element being multiplied. -/
private theorem exists_nsmul_eq_mul (r a : ↥finiteSupportSubring) : ∃ n : ℕ, n • a = r * a := by
  classical
  let s := (finite_support a).toFinset
  let modulus (p : Nat.Primes) := (p : ℕ)
  let residue (p : Nat.Primes) := (r.val p).val
  have nonzeroModuli : ∀ p ∈ s, modulus p ≠ 0 := fun p _ => p.property.ne_zero
  have coprimeModuli : Set.Pairwise (s : Set Nat.Primes) (Function.onFun Nat.Coprime modulus) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes p.property q.property).2 (fun h => hpq (Subtype.ext h))
  let n := Nat.chineseRemainderOfFinset residue modulus s nonzeroModuli coprimeModuli
  refine ⟨n.val, Subtype.ext (funext fun p => ?_)⟩
  change n.val • a.val p = r.val p * a.val p
  by_cases hp : p ∈ s
  · have hcast : (n.val : ZMod (p : ℕ)) = r.val p := by
      rw [← ZMod.natCast_zmod_val (r.val p)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (n.property p hp)
    rw [nsmul_eq_mul, hcast]
  · have ha : a.val p = 0 :=
      not_not.mp (fun h => hp ((finite_support a).mem_toFinset.2 h))
    rw [ha, smul_zero, mul_zero]

/-- The element with coordinate one on a finite set of primes and zero elsewhere. -/
private def supportIdempotent (s : Finset Nat.Primes) : ↥finiteSupportSubring :=
  ⟨fun p => if p ∈ s then 1 else 0, by
    apply s.finite_toSet.subset
    intro p hp
    by_contra h
    exact hp (ite_eq_right h)⟩

private theorem supportIdempotent_mul (a : ↥finiteSupportSubring) :
    supportIdempotent (finite_support a).toFinset * a = a := by
  apply Subtype.ext
  funext p
  change (if p ∈ (finite_support a).toFinset then 1 else 0) * a.val p = a.val p
  by_cases h : p ∈ (finite_support a).toFinset
  · rw [ite_eq_left h, one_mul]
  · have ha : a.val p = 0 :=
      not_not.mp (fun h' => h ((finite_support a).mem_toFinset.2 h'))
    rw [ha, mul_zero]

private theorem singleton_coordinate (p : Nat.Primes) :
    (supportIdempotent {p}).val p = 1 := by simp [supportIdempotent]

private theorem nonzero : ∃ a : ↥finiteSupportSubring, a ≠ 0 := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  refine ⟨supportIdempotent {p}, fun h => ?_⟩
  have hcoord := congrArg (fun a : ↥finiteSupportSubring => a.val p) h
  change (supportIdempotent {p}).val p = 0 at hcoord
  rw [singleton_coordinate] at hcoord
  exact one_ne_zero hcoord

private theorem no_two_sided_unit :
    ∀ e : ↥finiteSupportSubring, ∃ a : ↥finiteSupportSubring, e * a ≠ a ∨ a * e ≠ a := by
  intro e
  obtain ⟨p, hp⟩ := (finite_support e).exists_notMem
  have he : e.val p = 0 := not_not.mp hp
  refine ⟨supportIdempotent {p}, Or.inl (fun h => ?_)⟩
  have hcoord := congrArg (fun a : ↥finiteSupportSubring => a.val p) h
  change e.val p * (supportIdempotent {p}).val p = (supportIdempotent {p}).val p at hcoord
  rw [he, singleton_coordinate, zero_mul] at hcoord
  exact zero_ne_one hcoord

/-- Every additive submonoid is preserved by multiplication by every element. -/
private theorem mul_mem_of_mem (M : AddSubmonoid ↥finiteSupportSubring)
    (r a : ↥finiteSupportSubring) (ha : a ∈ M) : r * a ∈ M := by
  obtain ⟨n, hn⟩ := exists_nsmul_eq_mul r a
  exact hn ▸ M.nsmul_mem ha n

private theorem top_is_product_unit (M : AddSubmonoid ↥finiteSupportSubring) :
    (⊤ : AddSubmonoid ↥finiteSupportSubring) * M = M ∧
      M * (⊤ : AddSubmonoid ↥finiteSupportSubring) = M := by
  have hleft : (⊤ : AddSubmonoid ↥finiteSupportSubring) * M = M := by
    ext x
    rw [mem_product_iff]
    constructor
    · rintro ⟨n, _, s, t, rfl⟩
      exact M.sum_mem fun i _ => mul_mem_of_mem M (s i) (t i) (t i).property
    · intro hx
      refine ⟨1, Nat.one_pos, fun _ => ⟨supportIdempotent (finite_support x).toFinset, by simp⟩,
        fun _ => ⟨x, hx⟩, ?_⟩
      simpa only [Fin.sum_univ_one] using supportIdempotent_mul x
  exact ⟨hleft, (AddSubmonoid.mul_comm_of_commute fun a _ b _ => Commute.all a b).trans hleft⟩

/-- The prime-residue direct sum is nonzero and has no ring identity, but its top
additive submonoid is a two-sided identity for the product of submonoids. -/
theorem finiteSupportSubring_properties :
    (∃ a : ↥finiteSupportSubring, a ≠ 0) ∧
    (∀ e : ↥finiteSupportSubring, ∃ a : ↥finiteSupportSubring, e * a ≠ a ∨ a * e ≠ a) ∧
    (∀ M : AddSubmonoid ↥finiteSupportSubring,
      (⊤ : AddSubmonoid ↥finiteSupportSubring) * M = M ∧
        M * (⊤ : AddSubmonoid ↥finiteSupportSubring) = M) :=
  ⟨nonzero, no_two_sided_unit, top_is_product_unit⟩

end

end D5.S3.Arith.ResidueRings.MesyanQuantaleUnit
