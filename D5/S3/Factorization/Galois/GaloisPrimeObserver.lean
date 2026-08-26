/- GID: D5/S3/Factorization/Galois/GaloisPrimeObserver
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GaloisPrimeObserver
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tagged Frobenius observers have an infinite fiber; boundary cases are audited. -/
/- Library-search audit trail (2026-08-25):
   * Current-tree searches found no number-theoretic Frobenius declaration in D5.
   * Lean LSP search commands were unavailable; the scripted search returned no exact hit.
   * Pinned source searches covered `Frobenius`, `IsUnramified`, `Ideal.map`, `Gal`,
     decomposition groups, and inertia. `arithFrobAt`, `isConj_arithFrobAt`, and the
     inertia-difference interface are supplied by `Mathlib.RingTheory.Frobenius`.
   * Exact pigeonhole and prime hits are `Finite.exists_infinite_fiber` and
     `Nat.infinite_setOf_prime`; both are applied below.
   * No packaged finite-ramification theorem for a fixed number-field extension was found,
     so finiteness of the ramified prime set remains an explicit hypothesis.
   * No direct quadratic split/inert Frobenius bridge was found; that instance is omitted. -/

import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Frobenius

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.GaloisPrimeObserver

/-- A prime observer with an explicit ramification boundary. `none` records a ramified
prime; an unramified prime records the conjugacy class of its supplied Frobenius element. -/
def galoisPrimeObserver {G : Type*} [Monoid G]
    (unramified : Nat.Primes -> Prop)
    (frobenius : forall p, unramified p -> G) :
    Nat.Primes -> Option (ConjClasses G) := by
  classical
  intro p
  exact if hp : unramified p then some (ConjClasses.mk (frobenius p hp)) else none

/-- The tagged local bridge to Mathlib's chosen arithmetic Frobenius element. It deliberately
returns no conjugacy class at a ramified ideal. -/
def mathlibFrobeniusAt
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : Option (ConjClasses G) := by
  classical
  exact if Algebra.IsUnramifiedAt R Q then
    some (ConjClasses.mk (arithFrobAt R G Q))
  else none

/-- A finite conjugacy-class output merges infinitely many unramified rational primes,
provided that only finitely many primes carry the ramified tag. -/
theorem frobenius_observation_has_infinite_fiber
    {G : Type*} [Monoid G] [Finite (ConjClasses G)]
    (unramified : Nat.Primes -> Prop)
    (frobenius : forall p, unramified p -> G)
    (finiteRamification : {p : Nat.Primes | ¬unramified p}.Finite) :
    ∃ c : ConjClasses G,
      {p : Nat.Primes | galoisPrimeObserver unramified frobenius p = some c}.Infinite := by
  classical
  letI : Infinite Nat.Primes := Nat.infinite_setOf_prime.to_subtype
  obtain ⟨value, hvalue⟩ :=
    Finite.exists_infinite_fiber (galoisPrimeObserver unramified frobenius)
  rcases value with _ | c
  · have hfinite :
        {p : Nat.Primes | galoisPrimeObserver unramified frobenius p = none}.Finite := by
      apply finiteRamification.subset
      intro p hp
      simpa [galoisPrimeObserver] using hp
    have hinfinite :
        {p : Nat.Primes | galoisPrimeObserver unramified frobenius p = none}.Infinite := by
      have hpreimage := Set.infinite_coe_iff.mp hvalue
      rw [show galoisPrimeObserver unramified frobenius ⁻¹' {none} =
        {p | galoisPrimeObserver unramified frobenius p = none} by ext; simp] at hpreimage
      exact hpreimage
    exact (hfinite.not_infinite hinfinite).elim
  · refine ⟨c, ?_⟩
    have hpreimage := Set.infinite_coe_iff.mp hvalue
    rw [show galoisPrimeObserver unramified frobenius ⁻¹' {some c} =
      {p | galoisPrimeObserver unramified frobenius p = some c} by ext; simp] at hpreimage
    exact hpreimage

#print axioms frobenius_observation_has_infinite_fiber

/-- If every prime is tagged ramified, every genuine Frobenius-class fiber is empty.
This concrete observer shows why finite ramification is required by the main theorem. -/
theorem finite_ramification_is_necessary :
    {_p : Nat.Primes | ¬False}.Infinite ∧
      ¬∃ c : ConjClasses Unit,
        {p : Nat.Primes |
          galoisPrimeObserver (G := Unit) (fun _ => False) (fun _ h => h.elim) p =
            some c}.Infinite := by
  constructor
  · simpa using (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)
  · rintro ⟨c, hc⟩
    have hfinite :
        {p : Nat.Primes |
          galoisPrimeObserver (G := Unit) (fun _ => False) (fun _ h => h.elim) p =
            some c}.Finite := by
      simp [galoisPrimeObserver]
    exact hfinite.not_infinite hc

#print axioms finite_ramification_is_necessary

/-- With infinitely many conjugacy classes, the unramified observer can be injective.
This concrete observer shows why finite conjugacy-class output is required. -/
theorem finite_conjugacy_output_is_necessary :
    Infinite (ConjClasses (Multiplicative Nat)) ∧
      ¬∃ c : ConjClasses (Multiplicative Nat),
        {p : Nat.Primes |
          some (ConjClasses.mk (Multiplicative.ofAdd p.1)) = some c}.Infinite := by
  constructor
  · apply Infinite.of_injective
      (fun n : Nat => ConjClasses.mk (Multiplicative.ofAdd n))
    intro m n hmn
    exact ConjClasses.mk_injective (α := Multiplicative Nat) hmn
  · rintro ⟨c, hc⟩
    apply hc
    apply Set.Subsingleton.finite
    intro p hp q hq
    apply Subtype.ext
    have hclasses :
        ConjClasses.mk (Multiplicative.ofAdd p.1) =
          ConjClasses.mk (Multiplicative.ofAdd q.1) :=
      Option.some_injective _ (hp.trans hq.symm)
    exact ConjClasses.mk_injective (α := Multiplicative Nat) hclasses

#print axioms finite_conjugacy_output_is_necessary

-- Empty-output audit: a conjugacy-class output is inhabited because a monoid contains `1`.
example {G : Type*} [Monoid G] : Nonempty (ConjClasses G) :=
  ⟨ConjClasses.mk 1⟩

-- Trivial-extension audit: the trivial group gives one constant class on all unramified primes.
example :
    {p : Nat.Primes |
      galoisPrimeObserver (G := Unit) (fun _ => True) (fun _ _ => ()) p =
        some (ConjClasses.mk ())}.Infinite := by
  simpa [galoisPrimeObserver] using
    (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)

-- All primes cannot be ramified under the finite-ramification hypothesis.
example : ¬({_p : Nat.Primes | True}).Finite := by
  simpa using (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)

end D5.S3.Factorization.Galois.GaloisPrimeObserver
