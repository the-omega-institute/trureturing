/- GID: D5/S3/Arith/ResidueRings/MesyanQuantaleClassification
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueRings/MesyanQuantaleClassification
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A ring has a quantale unit on its additive submonoids exactly when it has a ring unit or is a torsion ring with unital primary components. -/

import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Ring.Submonoid.Pointwise
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.NatInt
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The associative-ring classification in Mesyan's *Quantales Arising From Rings*,
Question 36 (arXiv:2611.31109v1). The product of additive submonoids is the
positive finite-sum product of Definition 4.
-/

open scoped Pointwise

namespace D5.S3.Arith.ResidueRings.MesyanQuantaleClassification

variable {R : Type*} [NonUnitalRing R]

/-- The left action on additive submonoids, reduced to cyclic submonoids
and a local left identity at every element. -/
private theorem left_product_iff (E : AddSubmonoid R) :
    (∀ M : AddSubmonoid R, E * M = M) ↔
      (∀ e ∈ E, ∀ a : R, ∃ n : ℕ, n • a = e * a) ∧
      (∀ a : R, ∃ e ∈ E, e * a = a) := by
  constructor
  · intro h
    have memSelf (a : R) : a ∈ AddSubmonoid.multiples a := ⟨1, one_nsmul a⟩
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

private theorem right_product_iff (E : AddSubmonoid R) :
    (∀ M : AddSubmonoid R, M * E = M) ↔
      (∀ e ∈ E, ∀ a : R, ∃ n : ℕ, n • a = a * e) ∧
      (∀ a : R, ∃ e ∈ E, a * e = a) := by
  constructor
  · intro h
    have memSelf (a : R) : a ∈ AddSubmonoid.multiples a := ⟨1, one_nsmul a⟩
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

/-- A cyclic-preserving endomorphism cannot kill a nonzero element whose
additive order divides the order of a fixed point. -/
private theorem ker_eq_zero_of_order_dvd {A : Type*} [AddCommGroup A]
    (F : A →+ A) (hF : ∀ x, ∃ n : ℕ, n • x = F x)
    {a b : A} (hfa : F a = a) (hb : F b = 0) (hd : addOrderOf b ∣ addOrderOf a) :
    b = 0 := by
  obtain ⟨n, hn⟩ := hF (a + b)
  rw [map_add, hfa, hb, add_zero] at hn
  have hna : n • a = a := by
    simpa only [map_nsmul, map_add, hfa, hb, add_zero] using congrArg F hn
  have hmod := (nsmul_eq_nsmul_iff_modEq (x := a)).1 (hna.trans (one_nsmul a).symm)
  have hnb : n • b = b :=
    ((nsmul_eq_nsmul_iff_modEq (x := b)).2 (hmod.of_dvd hd)).trans (one_nsmul b)
  rwa [nsmul_add, hna, hnb, add_eq_left] at hn

/-- A cyclic-preserving additive endomorphism with a fixed point of order p
is injective on the elements killed by powers of p. -/
private theorem ker_eq_zero_of_prime_order {A : Type*} [AddCommGroup A]
    (F : A →+ A) (hF : ∀ x, ∃ n : ℕ, n • x = F x)
    (p : Nat.Primes) {a : A} (ha : addOrderOf a = (p : ℕ)) (hfa : F a = a)
    (b : A) (hb : F b = 0) (hbp : ∃ j : ℕ, (p : ℕ)^j • b = 0) :
    b = 0 := by
  have orderP (c : A) (hc : (p : ℕ) • c = 0) (hfc : F c = 0) : c = 0 :=
    ker_eq_zero_of_order_dvd F hF hfa hfc (ha ▸ addOrderOf_dvd_of_nsmul_eq_zero hc)
  obtain ⟨j, hj⟩ := hbp
  induction j with
  | zero => simpa using hj
  | succ j ih =>
    apply ih
    apply orderP
    · simpa [pow_succ, mul_nsmul] using hj
    · rw [map_nsmul, hb, nsmul_zero]

/-- A left product identity forces a ring left identity when there is an
element of infinite additive order. -/
private theorem left_identity_of_infinite_order {E : AddSubmonoid R}
    (h : ∀ M : AddSubmonoid R, E * M = M) {a : R} (ha : addOrderOf a = 0) :
    ∃ e : R, ∀ b, e * b = b := by
  obtain ⟨hpres, hfix⟩ := (left_product_iff E).1 h
  obtain ⟨e, he, hfa⟩ := hfix a
  let F : R →+ R := AddMonoidHom.mulLeft e
  have inj := (injective_iff_map_eq_zero F).2 fun b hb =>
    ker_eq_zero_of_order_dvd F (hpres e he) hfa hb (ha ▸ dvd_zero (addOrderOf b))
  obtain ⟨k, hk⟩ := hpres e he e
  have hiter (x : R) : e * (e * x) = e * (k • x) := by
    rw [← mul_assoc, ← hk, smul_mul_assoc, mul_smul_comm]
  refine ⟨e, fun b => ?_⟩
  have hka : a = k • a := by simpa only [mul_smul_comm, hfa] using hiter a
  have hk1 : k = 1 := by
    have hmod := (nsmul_eq_nsmul_iff_modEq (x := a)).1 (hka.symm.trans (one_nsmul a).symm)
    simpa [ha, Nat.ModEq] using hmod
  apply inj
  change e * (e * b) = e * b
  simpa only [hk1, one_nsmul] using hiter b

/-- The additive primary component, as a submodule over the integers. -/
private def Primary (A : Type*) [AddCommGroup A] (p : Nat.Primes) : Submodule ℤ A :=
  Ideal.primaryComponent A (Ideal.span {((p : ℕ) : ℤ)})

private theorem mem_primary_iff {A : Type*} [AddCommGroup A] {p : Nat.Primes} {x : A} :
    x ∈ Primary A p ↔ ∃ j : ℕ, (p : ℕ)^j • x = 0 := by
  unfold Primary
  rw [Ideal.primaryComponent_mem]
  simp only [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq,
    Submodule.mem_torsionBy_iff, ← Nat.cast_pow, natCast_zsmul]

/-- Every element of a torsion additive group is a finite sum of
prime-primary components, indexed by distinct primes. -/
private theorem exists_primary_sum {A : Type*} [AddCommGroup A]
    (ht : ∀ a : A, 0 < addOrderOf a) (a : A) :
    ∃ f : Nat.Primes →₀ A, (∀ p, f p ∈ Primary A p) ∧ f.sum (fun _ x => x) = a := by
  have ht' : Module.IsTorsion ℤ A :=
    isAddTorsion_iff_isTorsion_int.1 fun a => addOrderOf_pos_iff.1 (ht a)
  have htop : (⨆ p : Nat.Primes, Primary A p) = ⊤ := by
    apply top_unique
    rw [← Ideal.iSup_primaryComponent_eq_top ht']
    apply iSup_le
    intro P
    obtain ⟨p, hp, hP⟩ :=
      (Ideal.isPrime_int_iff.1 P.isPrime).resolve_left P.ne_bot
    rw [hP]
    exact le_iSup (Primary A) ⟨p, hp⟩
  apply (Submodule.mem_iSup_iff_exists_finsupp (Primary A) a).1
  rw [htop]
  exact Submodule.mem_top

private theorem eq_zero_of_coprime_annihilators {A : Type*} [AddCommGroup A]
    {x : A} {m n : ℕ} (hc : m.Coprime n) (hm : m • x = 0) (hn : n • x = 0) :
    x = 0 := by
  have hd := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm)
    (addOrderOf_dvd_of_nsmul_eq_zero hn)
  rw [hc.gcd_eq_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.mp hd)

private theorem primary_mul_eq_zero {p q : Nat.Primes} (hpq : p ≠ q)
    {x y : R} (hx : x ∈ Primary R p) (hy : y ∈ Primary R q) : x * y = 0 := by
  obtain ⟨i, hi⟩ := mem_primary_iff.1 hx
  obtain ⟨j, hj⟩ := mem_primary_iff.1 hy
  have hc : Nat.Coprime (p : ℕ) (q : ℕ) :=
    (Nat.coprime_primes p.property q.property).2 (fun h => hpq (Subtype.ext h))
  apply eq_zero_of_coprime_annihilators (hc.pow i j)
  · rw [← smul_mul_assoc, hi, zero_mul]
  · rw [← mul_smul_comm, hj, mul_zero]

private theorem mul_mem_primary {p : Nat.Primes} (e : R) {x : R}
    (hx : x ∈ Primary R p) : e * x ∈ Primary R p := by
  obtain ⟨j, hj⟩ := mem_primary_iff.1 hx
  exact mem_primary_iff.2 ⟨j, by rw [← mul_smul_comm, hj, mul_zero]⟩

private theorem exists_primary_left_action (ht : ∀ a : R, 0 < addOrderOf a)
    (p : Nat.Primes) (e : R) : ∃ eₚ ∈ Primary R p, ∀ x ∈ Primary R p, e * x = eₚ * x := by
  classical
  obtain ⟨f, hf, hsum⟩ := exists_primary_sum ht e
  refine ⟨f p, hf p, fun x hx => ?_⟩
  conv_lhs => rw [← hsum]
  change (∑ q ∈ f.support, f q) * x = f p * x
  rw [Finset.sum_mul]
  exact Finset.sum_eq_single p (fun q _ hqp => primary_mul_eq_zero hqp (hf q) hx)
    (fun h => by rw [Finsupp.notMem_support_iff.1 h, zero_mul])

private theorem exists_order_p_of_ne_zero {A : Type*} [AddCommGroup A]
    (p : Nat.Primes) {x : A} (hx : x ≠ 0) (hxp : x ∈ Primary A p) :
    ∃ a : A, addOrderOf a = (p : ℕ) := by
  obtain ⟨j, hj⟩ := mem_primary_iff.1 hxp
  have : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  induction j with
  | zero => exact (hx (by simpa using hj)).elim
  | succ j ih =>
    by_cases h : (p : ℕ)^j • x = 0
    · exact ih h
    · exact ⟨_, addOrderOf_eq_prime (by simpa [pow_succ, mul_nsmul] using hj) h⟩

private theorem eq_zero_of_coprime_primary_nsmul {A : Type*} [AddCommGroup A]
    {p : Nat.Primes} {k : ℕ} (hk : k.Coprime (p : ℕ)) {x : A}
    (hx : x ∈ Primary A p) (h : k • x = 0) : x = 0 := by
  obtain ⟨j, hj⟩ := mem_primary_iff.1 hx
  exact eq_zero_of_coprime_annihilators (hk.pow_right j) h hj

/-- In a torsion ring, a left product unit induces an internal left identity
on each primary component. -/
private theorem primary_left_identity_of_product {E : AddSubmonoid R}
    (h : ∀ M : AddSubmonoid R, E * M = M) (ht : ∀ a : R, 0 < addOrderOf a)
    (p : Nat.Primes) : ∃ u ∈ Primary R p, ∀ x ∈ Primary R p, u * x = x := by
  classical
  by_cases hp : ∃ x ∈ Primary R p, x ≠ 0
  swap
  · refine ⟨0, (Primary R p).zero_mem, fun x hx => ?_⟩
    rw [zero_mul]
    exact (not_ne_iff.1 fun hn => hp ⟨x, hx, hn⟩).symm
  obtain ⟨x, hx, hx0⟩ := hp
  obtain ⟨a, ha⟩ := exists_order_p_of_ne_zero p hx0 hx
  have ha0 : a ≠ 0 := by
    intro hzero
    exact p.property.ne_one (ha.symm.trans (by simp [hzero]))
  have hpa : (p : ℕ) • a = 0 := by rw [← ha, addOrderOf_nsmul_eq_zero]
  obtain ⟨hpres, hfix⟩ := (left_product_iff E).1 h
  obtain ⟨e, he, hea⟩ := hfix a
  obtain ⟨k, hk⟩ := hpres e he e
  let F : R →+ R := AddMonoidHom.mulLeft e
  have hinj : Set.InjOn F (Primary R p : Set R) := by
    intro x hx y hy hxy
    apply sub_eq_zero.mp
    exact ker_eq_zero_of_prime_order F (hpres e he) p ha hea (x - y)
      (by rw [map_sub, hxy, sub_self]) (mem_primary_iff.1 ((Primary R p).sub_mem hx hy))
  have hiter (x : R) : e * (e * x) = e * (k • x) := by
    rw [← mul_assoc, ← hk, smul_mul_assoc, mul_smul_comm]
  have hka : k • a = a := by simpa only [mul_smul_comm, hea] using (hiter a).symm
  have hkp : k.Coprime (p : ℕ) := by
    apply Nat.Coprime.symm
    apply p.property.coprime_iff_not_dvd.2
    rintro ⟨r, hr⟩
    apply ha0
    rw [hr, mul_nsmul, hpa, nsmul_zero] at hka
    exact hka.symm
  have heacts (x : R) (hx : x ∈ Primary R p) : e * x = k • x := by
    apply hinj (mul_mem_primary e hx) ((Primary R p).toAddSubmonoid.nsmul_mem hx k)
    exact hiter x
  obtain ⟨eₚ, heₚ, hacts⟩ := exists_primary_left_action ht p e
  obtain ⟨j, hj⟩ := mem_primary_iff.1 heₚ
  have hcop : k.Coprime (addOrderOf eₚ) :=
    (hkp.pow_right j).coprime_dvd_right (addOrderOf_dvd_of_nsmul_eq_zero hj)
  obtain ⟨n, hn⟩ := exists_nsmul_eq_self_of_coprime hcop
  let u := n • eₚ
  have hu : u ∈ Primary R p := (Primary R p).toAddSubmonoid.nsmul_mem heₚ n
  have hku : k • u = eₚ := by
    dsimp [u]
    rw [← mul_nsmul, Nat.mul_comm, mul_nsmul]
    exact hn
  refine ⟨u, hu, fun x hx => ?_⟩
  apply sub_eq_zero.mp
  apply eq_zero_of_coprime_primary_nsmul hkp ((Primary R p).sub_mem (mul_mem_primary u hx) hx)
  rw [nsmul_sub, ← smul_mul_assoc, hku, ← hacts x hx, heacts x hx, sub_self]

/-- Elements whose left and right actions give the same natural multiple
of each argument. -/
private def cyclicMultipliers (R : Type*) [NonUnitalRing R] : AddSubmonoid R where
  carrier := {e | ∀ a : R, ∃ n : ℕ, n • a = e * a ∧ n • a = a * e}
  zero_mem' := fun a => ⟨0, by simp⟩
  add_mem' {e f} he hf := by
    intro a
    obtain ⟨m, hml, hmr⟩ := he a
    obtain ⟨n, hnl, hnr⟩ := hf a
    exact ⟨m + n, by rw [add_nsmul, hml, hnl, add_mul],
      by rw [add_nsmul, hmr, hnr, mul_add]⟩

private theorem primary_unit_mem_cyclicMultipliers (ht : ∀ a : R, 0 < addOrderOf a)
    (p : Nat.Primes) {u : R} (hu : u ∈ Primary R p)
    (hunit : ∀ x ∈ Primary R p, u * x = x ∧ x * u = x) :
    u ∈ cyclicMultipliers R := by
  classical
  intro a
  obtain ⟨f, hf, hsum⟩ := exists_primary_sum ht a
  choose j hj using fun q => mem_primary_iff.1 (hf q)
  let modulus (q : Nat.Primes) : ℕ := (q : ℕ) ^ j q
  let residue (q : Nat.Primes) : ℕ := if q = p then 1 else 0
  have hnonzero (q : Nat.Primes) (_ : q ∈ f.support) : modulus q ≠ 0 :=
    pow_ne_zero _ q.property.ne_zero
  have hcop : Set.Pairwise (f.support : Set Nat.Primes)
      (Function.onFun Nat.Coprime modulus) := by
    intro q _ r _ hqr
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes q.property r.property).2 (fun h => hqr (Subtype.ext h))
  let c := Nat.chineseRemainderOfFinset residue modulus f.support hnonzero hcop
  have hcoeff (q : Nat.Primes) (hq : q ∈ f.support) :
      (c : ℕ) • f q = residue q • f q :=
    nsmul_eq_nsmul_of_modEq (c.property q hq) (hj q)
  have hactions (q : Nat.Primes) :
      residue q • f q = u * f q ∧ residue q • f q = f q * u := by
    by_cases hqp : q = p
    · subst q
      obtain ⟨hl, hr⟩ := hunit (f p) (hf p)
      simp [residue, hl, hr]
    · simp [residue, hqp, primary_mul_eq_zero (Ne.symm hqp) hu (hf q),
        primary_mul_eq_zero hqp (hf q) hu]
  refine ⟨c.val, ?_, ?_⟩
  · rw [← hsum]
    change c.val • (∑ q ∈ f.support, f q) = u * ∑ q ∈ f.support, f q
    rw [Finset.smul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q hq => (hcoeff q hq).trans (hactions q).1
  · rw [← hsum]
    change c.val • (∑ q ∈ f.support, f q) = (∑ q ∈ f.support, f q) * u
    rw [Finset.smul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q hq => (hcoeff q hq).trans (hactions q).2

/-- Primary units in a torsion ring give a product unit of its additive submonoids. -/
private theorem product_unit_of_primary_units (ht : ∀ a : R, 0 < addOrderOf a)
    (hp : ∀ p : Nat.Primes, ∃ u ∈ Primary R p,
      ∀ x ∈ Primary R p, u * x = x ∧ x * u = x) :
    ∃ E : AddSubmonoid R, ∀ M : AddSubmonoid R, E * M = M ∧ M * E = M := by
  classical
  choose u hu hunit using hp
  let E := cyclicMultipliers R
  have hfix (a : R) : ∃ e ∈ E, e * a = a ∧ a * e = a := by
    obtain ⟨f, hf, hsum⟩ := exists_primary_sum ht a
    let e := ∑ p ∈ f.support, u p
    refine ⟨e, E.sum_mem (fun p _ => primary_unit_mem_cyclicMultipliers ht p (hu p) (hunit p)),
      ?_, ?_⟩
    · rw [← hsum]
      change e * (∑ p ∈ f.support, f p) = ∑ p ∈ f.support, f p
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [e]
      rw [Finset.sum_mul, Finset.sum_eq_single_of_mem p hp
        (fun q _ hqp => primary_mul_eq_zero hqp (hu q) (hf p))]
      exact (hunit p (f p) (hf p)).1
    · rw [← hsum]
      change (∑ p ∈ f.support, f p) * e = ∑ p ∈ f.support, f p
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [e]
      rw [Finset.mul_sum, Finset.sum_eq_single_of_mem p hp
        (fun q _ hqp => primary_mul_eq_zero (Ne.symm hqp) (hf p) (hu q))]
      exact (hunit p (f p) (hf p)).2
  have hleft : ∀ M : AddSubmonoid R, E * M = M :=
    (left_product_iff E).2
      ⟨fun e he x => let ⟨n, hl, _⟩ := he x; ⟨n, hl⟩,
        fun x => let ⟨e, he, hl, _⟩ := hfix x; ⟨e, he, hl⟩⟩
  have hright : ∀ M : AddSubmonoid R, M * E = M :=
    (right_product_iff E).2
      ⟨fun e he x => let ⟨n, _, hr⟩ := he x; ⟨n, hr⟩,
        fun x => let ⟨e, he, _, hr⟩ := hfix x; ⟨e, he, hr⟩⟩
  exact ⟨E, fun M => ⟨hleft M, hright M⟩⟩

private theorem product_unit_of_ring_unit {u : R} (hu : ∀ x : R, u * x = x ∧ x * u = x) :
    ∃ E : AddSubmonoid R, ∀ M : AddSubmonoid R, E * M = M ∧ M * E = M := by
  let E := AddSubmonoid.multiples u
  have hleft : ∀ M : AddSubmonoid R, E * M = M := (left_product_iff E).2
    ⟨by rintro _ ⟨n, rfl⟩ x; exact ⟨n, by rw [smul_mul_assoc, (hu x).1]⟩,
     fun x => ⟨u, ⟨1, one_nsmul u⟩, (hu x).1⟩⟩
  have hright : ∀ M : AddSubmonoid R, M * E = M := (right_product_iff E).2
    ⟨by rintro _ ⟨n, rfl⟩ x; exact ⟨n, by rw [mul_smul_comm, (hu x).2]⟩,
     fun x => ⟨u, ⟨1, one_nsmul u⟩, (hu x).2⟩⟩
  exact ⟨E, fun M => ⟨hleft M, hright M⟩⟩

private theorem opposite_left_product {E : AddSubmonoid R}
    (h : ∀ M : AddSubmonoid R, M * E = M) :
    ∀ M : AddSubmonoid Rᵐᵒᵖ, E.map MulOpposite.opAddEquiv * M = M := by
  obtain ⟨hpres, hfix⟩ := (right_product_iff E).1 h
  apply (left_product_iff _).2
  constructor
  · intro e he a
    obtain ⟨e', he', rfl⟩ := AddSubmonoid.mem_map.1 he
    obtain ⟨n, hn⟩ := hpres e' he' (MulOpposite.unop a)
    refine ⟨n, MulOpposite.unop_injective ?_⟩
    change n • MulOpposite.unop a = MulOpposite.unop a * e'
    exact hn
  · intro a
    obtain ⟨e, he, hn⟩ := hfix (MulOpposite.unop a)
    refine ⟨MulOpposite.op e, AddSubmonoid.mem_map.2 ⟨e, he, rfl⟩,
      MulOpposite.unop_injective ?_⟩
    exact hn

/-- Mesyan Q36: the additive-submonoid product has a two-sided unit exactly
when the ring has a two-sided identity or its additive group is torsion and every
primary component has a two-sided identity belonging to that component.
Zero is the identity of a zero component. -/
theorem product_unit_iff :
    (∃ E : AddSubmonoid R, ∀ M : AddSubmonoid R, E * M = M ∧ M * E = M) ↔
      (∃ u : R, ∀ x : R, u * x = x ∧ x * u = x) ∨
      ((∀ a : R, 0 < addOrderOf a) ∧
        ∀ p : Nat.Primes, ∃ u : R, (∃ j : ℕ, (p : ℕ)^j • u = 0) ∧
          ∀ x : R, (∃ j : ℕ, (p : ℕ)^j • x = 0) → u * x = x ∧ x * u = x) := by
  constructor
  · rintro ⟨E, h⟩
    have hleft (M : AddSubmonoid R) := (h M).1
    have hop := opposite_left_product (fun M => (h M).2)
    by_cases ht : ∀ a : R, 0 < addOrderOf a
    · refine Or.inr ⟨ht, fun p => ?_⟩
      have htop (a : Rᵐᵒᵖ) : 0 < addOrderOf a := by
        rw [← MulOpposite.opAddEquiv.symm.addOrderOf_eq a]
        exact ht (MulOpposite.unop a)
      obtain ⟨l, hlp, hl⟩ := primary_left_identity_of_product hleft ht p
      obtain ⟨r, hrp, hr⟩ := primary_left_identity_of_product hop htop p
      have hrp' : MulOpposite.unop r ∈ Primary R p :=
        mem_primary_iff.2 (by
          obtain ⟨j, hj⟩ := mem_primary_iff.1 hrp
          exact ⟨j, congrArg MulOpposite.unop hj⟩)
      have hr' (x : R) (hx : x ∈ Primary R p) : x * MulOpposite.unop r = x := by
        have hopx : MulOpposite.op x ∈ Primary Rᵐᵒᵖ p :=
          mem_primary_iff.2 (by
            obtain ⟨j, hj⟩ := mem_primary_iff.1 hx
            exact ⟨j, congrArg MulOpposite.op hj⟩)
        exact congrArg MulOpposite.unop (hr _ hopx)
      have heq : l = MulOpposite.unop r := (hr' l hlp).symm.trans (hl _ hrp')
      exact ⟨l, mem_primary_iff.1 hlp, fun x hx =>
        ⟨hl x (mem_primary_iff.2 hx), heq ▸ hr' x (mem_primary_iff.2 hx)⟩⟩
    · push Not at ht
      obtain ⟨a, ha⟩ := ht
      have ha0 : addOrderOf a = 0 := Nat.le_zero.mp ha
      have haop : addOrderOf (MulOpposite.op a) = 0 :=
        (MulOpposite.opAddEquiv.addOrderOf_eq a).trans ha0
      obtain ⟨l, hl⟩ := left_identity_of_infinite_order hleft ha0
      obtain ⟨r, hr⟩ := left_identity_of_infinite_order hop haop
      have hr' (x : R) : x * MulOpposite.unop r = x :=
        congrArg MulOpposite.unop (hr (MulOpposite.op x))
      have heq : l = MulOpposite.unop r := (hr' l).symm.trans (hl _)
      exact Or.inl ⟨l, fun x => ⟨hl x, heq ▸ hr' x⟩⟩
  · rintro (⟨u, hu⟩ | ⟨ht, hp⟩)
    · exact product_unit_of_ring_unit hu
    · apply product_unit_of_primary_units ht
      intro p
      obtain ⟨u, hu, hunit⟩ := hp p
      exact ⟨u, mem_primary_iff.2 hu, fun x hx => hunit x (mem_primary_iff.1 hx)⟩

end D5.S3.Arith.ResidueRings.MesyanQuantaleClassification
