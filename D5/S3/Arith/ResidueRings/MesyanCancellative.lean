/- GID: D5/S3/Arith/ResidueRings/MesyanCancellative
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueRings/MesyanCancellative
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cancellative semiring product units and the cyclic multiplier criterion. -/

import D5.S3.Arith.ResidueRings.MesyanQuantaleClassification

/-!
For Mesyan's Question 36, we classify the additively cancellative associative
semirings with a unit on their additive submonoids. For arbitrary associative
semirings we identify the only candidate and give its elementwise unit criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

namespace D5.S3.Arith.ResidueRings.MesyanCancellative

variable {S : Type*} [NonUnitalSemiring S]

/-- A two-sided identity for the product of all additive submonoids. -/
private def IsProductUnit (E : AddSubmonoid S) : Prop :=
  ∀ M : AddSubmonoid S, E * M = M ∧ M * E = M

/-- A multiplicative identity on a type with possibly nonunital multiplication. -/
private def HasMultiplicativeIdentity (S : Type*) [Mul S] : Prop :=
  ∃ u : S, ∀ x : S, u * x = x ∧ x * u = x

private theorem left_product_iff (E : AddSubmonoid S) :
    (∀ M : AddSubmonoid S, E * M = M) ↔
      (∀ e ∈ E, ∀ a : S, ∃ n : ℕ, n • a = e * a) ∧
      (∀ a : S, ∃ e ∈ E, e * a = a) := by
  constructor
  · intro h
    have memSelf (a : S) : a ∈ AddSubmonoid.multiples a := ⟨1, one_nsmul a⟩
    refine ⟨fun e he a => ?_, fun a => ?_⟩
    · have hm := AddSubmonoid.mul_mem_mul he (memSelf a)
      rw [h] at hm
      exact hm
    · have hm : a ∈ E * AddSubmonoid.multiples a :=
        (h _).symm ▸ memSelf a
      refine AddSubmonoid.mul_induction_on (C := fun x => ∃ e ∈ E, e * a = x) hm ?_ ?_
      · rintro e he _ ⟨n, rfl⟩
        exact ⟨n • e, E.nsmul_mem he n, by rw [smul_mul_assoc, mul_smul_comm]⟩
      · rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
        exact ⟨e + f, E.add_mem he hf, add_mul e f a⟩
  · rintro ⟨hpres, hfix⟩ M
    apply le_antisymm
    · exact AddSubmonoid.mul_le.2 fun e he a ha =>
        let ⟨n, hn⟩ := hpres e he a
        hn ▸ M.nsmul_mem ha n
    · intro a ha
      obtain ⟨e, he, hfixa⟩ := hfix a
      exact hfixa ▸ AddSubmonoid.mul_mem_mul he ha

private theorem right_product_iff (E : AddSubmonoid S) :
    (∀ M : AddSubmonoid S, M * E = M) ↔
      (∀ e ∈ E, ∀ a : S, ∃ n : ℕ, n • a = a * e) ∧
      (∀ a : S, ∃ e ∈ E, a * e = a) := by
  constructor
  · intro h
    have memSelf (a : S) : a ∈ AddSubmonoid.multiples a := ⟨1, one_nsmul a⟩
    refine ⟨fun e he a => ?_, fun a => ?_⟩
    · have hm := AddSubmonoid.mul_mem_mul (memSelf a) he
      rw [h] at hm
      exact hm
    · have hm : a ∈ AddSubmonoid.multiples a * E :=
        (h _).symm ▸ memSelf a
      refine AddSubmonoid.mul_induction_on (C := fun x => ∃ e ∈ E, a * e = x) hm ?_ ?_
      · rintro _ ⟨n, rfl⟩ e he
        exact ⟨n • e, E.nsmul_mem he n, by rw [smul_mul_assoc, mul_smul_comm]⟩
      · rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
        exact ⟨e + f, E.add_mem he hf, mul_add a e f⟩
  · rintro ⟨hpres, hfix⟩ M
    apply le_antisymm
    · exact AddSubmonoid.mul_le.2 fun a ha e he =>
        let ⟨n, hn⟩ := hpres e he a
        hn ▸ M.nsmul_mem ha n
    · intro a ha
      obtain ⟨e, he, hfixa⟩ := hfix a
      exact hfixa ▸ AddSubmonoid.mul_mem_mul ha he

/-- Natural multiples of an element without an additive inverse are distinct
when addition is cancellative. -/
private theorem nsmul_injective_of_no_add_inverse {A : Type*} [AddCommMonoid A] [IsLeftCancelAdd A]
    {a : A} (ha : ¬ ∃ b : A, a + b = 0) : Function.Injective (fun n : ℕ => n • a) := by
  let _ : AddLeftCancelMonoid A := { ‹AddCommMonoid A›, ‹IsLeftCancelAdd A› with }
  exact injective_nsmul_iff_not_isOfFinAddOrder.mpr fun h =>
    ha (isAddUnit_iff_exists_and_exists.mp h.isAddUnit).1

private theorem fixed_everywhere_of_cyclic_idempotent {A : Type*} [AddCommMonoid A]
    [IsLeftCancelAdd A] (F : A →+ A) (hF : ∀ x : A, ∃ n : ℕ, n • x = F x)
    (hFF : ∀ x : A, F (F x) = F x) {a : A}
    (ha : ¬ ∃ b : A, a + b = 0) (hFa : F a = a) :
    ∀ x : A, F x = x := by
  intro x
  have hnoInverse : ¬ ∃ b : A, F (a + x) + b = 0 := by
    rintro ⟨b, hb⟩
    exact ha ⟨F x + b, by simpa only [map_add, hFa, add_assoc] using hb⟩
  obtain ⟨k, hk⟩ := hF (a + x)
  have hmultiple : k • F (a + x) = F (a + x) := by
    rw [← map_nsmul, hk, hFF]
  have hk1 : k = 1 :=
    nsmul_injective_of_no_add_inverse hnoInverse (hmultiple.trans (one_nsmul _).symm)
  have hfix : F (a + x) = a + x := by
    simpa only [hk1, one_nsmul] using hk.symm
  exact add_left_cancel (by simpa only [map_add, hFa] using hfix)

private theorem product_unit_of_multiplicative_identity
    (h : HasMultiplicativeIdentity S) : ∃ E : AddSubmonoid S, IsProductUnit E := by
  obtain ⟨u, hu⟩ := h
  let E := AddSubmonoid.multiples u
  have hleft := (left_product_iff E).2
    ⟨by rintro _ ⟨n, rfl⟩ x; exact ⟨n, by rw [smul_mul_assoc, (hu x).1]⟩,
      fun x => ⟨u, ⟨1, one_nsmul u⟩, (hu x).1⟩⟩
  have hright := (right_product_iff E).2
    ⟨by rintro _ ⟨n, rfl⟩ x; exact ⟨n, by rw [mul_smul_comm, (hu x).2]⟩,
      fun x => ⟨u, ⟨1, one_nsmul u⟩, (hu x).2⟩⟩
  exact ⟨E, fun M => ⟨hleft M, hright M⟩⟩

/-- Equip the original carrier with a nonunital ring by choosing an additive
inverse for each element. The supplied semiring fields include its natural scalar action. -/
@[instance_reducible]
private noncomputable def ringOfAdditiveInverses (h : ∀ a : S, ∃ b : S, a + b = 0) :
    NonUnitalRing S := by
  letI : Neg S := ⟨fun a => Classical.choose (h a)⟩
  exact { ‹NonUnitalSemiring S› with
    neg := Neg.neg
    neg_add_cancel := fun a => (add_comm _ _).trans (Classical.choose_spec (h a))
    zsmul := zsmulRec (fun n a => n • a)
    zsmul_zero' := by
      intro a
      change (0 : ℕ) • a = 0
      exact zero_nsmul a
    zsmul_succ' := by
      intro n a
      change (n + 1) • a = n • a + a
      exact AddMonoid.nsmul_succ n a }

/-- Multipliers preserving each cyclic additive submonoid on both sides.
The left and right natural multiples may be chosen independently. -/
def cyclicPreservingMultipliers (S : Type*) [NonUnitalSemiring S] : AddSubmonoid S where
  carrier := {c | ∀ x : S, c * x ∈ AddSubmonoid.multiples x ∧
    x * c ∈ AddSubmonoid.multiples x}
  zero_mem' := fun x => ⟨by rw [zero_mul]; exact (AddSubmonoid.multiples x).zero_mem,
    by rw [mul_zero]; exact (AddSubmonoid.multiples x).zero_mem⟩
  add_mem' := fun {c d} hc hd x =>
    ⟨by rw [add_mul]; exact (AddSubmonoid.multiples x).add_mem (hc x).1 (hd x).1,
      by rw [mul_add]; exact (AddSubmonoid.multiples x).add_mem (hc x).2 (hd x).2⟩

/-- The only possible product unit is the submonoid of cyclic-preserving
multipliers. It is a unit exactly when every element has a local fixer on
each side from that submonoid. -/
theorem product_unit_iff_eq_cyclicPreservingMultipliers (E : AddSubmonoid S) :
    (∀ M : AddSubmonoid S, E * M = M ∧ M * E = M) ↔
      E = cyclicPreservingMultipliers S ∧ ∀ x : S,
        (∃ l ∈ cyclicPreservingMultipliers S, l * x = x) ∧
        (∃ r ∈ cyclicPreservingMultipliers S, x * r = x) := by
  constructor
  · intro h
    obtain ⟨hLeft, hLeftFix⟩ := (left_product_iff E).1 fun M => (h M).1
    obtain ⟨hRight, hRightFix⟩ := (right_product_iff E).1 fun M => (h M).2
    have hEq : E = cyclicPreservingMultipliers S := by
      apply le_antisymm
      · exact fun c hc x => ⟨hLeft c hc x, hRight c hc x⟩
      · intro c hc
        obtain ⟨e, he, hec⟩ := hLeftFix c
        obtain ⟨n, hn⟩ := (hc e).2
        exact (hn.trans hec) ▸ E.nsmul_mem he n
    exact ⟨hEq, hEq ▸ fun x => ⟨hLeftFix x, hRightFix x⟩⟩
  · rintro ⟨rfl, h⟩ M
    exact ⟨(left_product_iff _).2 ⟨fun c hc x => (hc x).1, fun x => (h x).1⟩ M,
      (right_product_iff _).2 ⟨fun c hc x => (hc x).2, fun x => (h x).2⟩ M⟩

private theorem multiplicative_identity_of_product_unit [IsLeftCancelAdd S]
    {a : S} (ha : ¬ ∃ b : S, a + b = 0) {E : AddSubmonoid S}
    (hE : IsProductUnit E) : HasMultiplicativeIdentity S := by
  obtain ⟨_, hfix⟩ := (product_unit_iff_eq_cyclicPreservingMultipliers E).1 hE
  obtain ⟨⟨l, hl, hla⟩, ⟨r, hr, har⟩⟩ := hfix a
  obtain ⟨m, hm⟩ := (hl l).1
  obtain ⟨n, hn⟩ := (hr r).2
  change m • l = l * l at hm
  change n • r = r * r at hn
  have hm1 : m = 1 := nsmul_injective_of_no_add_inverse ha (calc
    m • a = (m • l) * a := by rw [smul_mul_assoc, hla]
    _ = a := by rw [hm, mul_assoc, hla, hla]
    _ = 1 • a := (one_nsmul a).symm)
  have hn1 : n = 1 := nsmul_injective_of_no_add_inverse ha (calc
    n • a = a * (n • r) := by rw [mul_smul_comm, har]
    _ = a := by rw [hn, ← mul_assoc, har, har]
    _ = 1 • a := (one_nsmul a).symm)
  have hll : l * l = l := by simpa only [hm1, one_nsmul] using hm.symm
  have hrr : r * r = r := by simpa only [hn1, one_nsmul] using hn.symm
  have hlGlobal : ∀ x : S, l * x = x :=
    fixed_everywhere_of_cyclic_idempotent (AddMonoidHom.mulLeft l) (fun x => (hl x).1)
      (fun x => show l * (l * x) = l * x by rw [← mul_assoc, hll]) ha hla
  have hrGlobal : ∀ x : S, x * r = x :=
    fixed_everywhere_of_cyclic_idempotent (AddMonoidHom.mulRight r) (fun x => (hr x).2)
      (fun x => show (x * r) * r = x * r by rw [mul_assoc, hrr]) ha har
  have hlr : l = r := (hrGlobal l).symm.trans (hlGlobal r)
  exact ⟨l, fun x => ⟨hlGlobal x, hlr.symm ▸ hrGlobal x⟩⟩

/-- Complete classification for associative semirings with cancellative addition.
If all elements have additive inverses, the ring theorem applies on exactly
the supplied semiring reduct. The torsion branch itself supplies these inverses. -/
theorem product_unit_iff_cancellative [IsLeftCancelAdd S] :
    (∃ E : AddSubmonoid S, ∀ M : AddSubmonoid S, E * M = M ∧ M * E = M) ↔
      (∃ u : S, ∀ x : S, u * x = x ∧ x * u = x) ∨
      ((∀ a : S, 0 < addOrderOf a) ∧
        ∀ p : Nat.Primes, ∃ u : S, (∃ j : ℕ, (p : ℕ) ^ j • u = 0) ∧
          ∀ x : S, (∃ j : ℕ, (p : ℕ) ^ j • x = 0) → u * x = x ∧ x * u = x) := by
  classical
  constructor
  · rintro ⟨E, hE⟩
    by_cases hall : ∀ a : S, ∃ b : S, a + b = 0
    · exact (@MesyanQuantaleClassification.product_unit_iff
        S (ringOfAdditiveInverses hall)).1 ⟨E, hE⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hall
      exact Or.inl (multiplicative_identity_of_product_unit ha hE)
  · rintro (hu | ht)
    · exact product_unit_of_multiplicative_identity hu
    · have hall (a : S) : ∃ b : S, a + b = 0 :=
        (isAddUnit_iff_exists_and_exists.mp (addOrderOf_pos_iff.mp (ht.1 a)).isAddUnit).1
      exact (@MesyanQuantaleClassification.product_unit_iff
        S (ringOfAdditiveInverses hall)).2 (Or.inr ht)

end D5.S3.Arith.ResidueRings.MesyanCancellative
