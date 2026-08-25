/- GID: D5/S3/Factorization/Galois/QuadraticObservationBound
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/QuadraticObservationBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary observers factor through the square quotient; C2 and C4 are audited. -/
/- Library-search audit trail (2026-08-25):
   * Lean LSP search commands were unavailable; two scripted searches found no exact hit.
   * Pinned source searches covered `commutator`, `Abelianization`, `MonoidHom.ker`,
     `ZMod 2`, `IsElementaryAbelian`, `Subgroup.closure`, squares, and exponent.
   * `Subgroup.square` exists only for commutative groups, so it cannot define this `G²`.
   * `Subgroup.normalClosure`, `normalClosure_le_normal`, and `normalClosure_normal`
     supply the least normal subgroup containing all squares and the required quotient.
   * `Monoid.exponent_dvd_of_forall_pow_eq_one` and `Commute.of_orderOf_dvd_two`
     give the exponent-dividing-two and commutativity conclusions for the quotient.
   * No general `IsElementaryAbelian` interface was found, so those two properties are
     stated directly. `Abelianization` is not needed because the square quotient commutes. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.QuadraticObservationBound

/-- The multiplicative two-element target used for split/inert observations. -/
abbrev QuadraticBit := Multiplicative (ZMod 2)

/-- A quadratic observer is any group homomorphism to the split/inert target.
Surjectivity is deliberately not required. -/
abbrev QuadraticObserver (G : Type*) [Group G] := G →* QuadraticBit

/-- The subgroup denoted by `G²`: the normal closure of all square elements.
`normalClosure` is used instead of `closure` so the quotient is available for every group. -/
def squareSubgroup (G : Type*) [Group G] : Subgroup G :=
  Subgroup.normalClosure (Set.range fun g : G => g ^ 2)

instance squareSubgroup_normal (G : Type*) [Group G] : (squareSubgroup G).Normal := by
  rw [squareSubgroup]
  infer_instance

/-- The intersection of the kernels of all split/inert observers. -/
def quadraticJointKernel (G : Type*) [Group G] : Subgroup G :=
  ⨅ φ : QuadraticObserver G, MonoidHom.ker φ

/-- The joint readout that records the value of every split/inert observer. -/
def quadraticReadout (G : Type*) [Group G] : G → (QuadraticObserver G → QuadraticBit) :=
  fun g φ => φ g

private theorem quadraticBit_sq (z : QuadraticBit) : z ^ 2 = 1 := by
  fin_cases z <;> decide

/-- Every square, and hence its normal closure, lies in every quadratic-observer kernel. -/
theorem square_subgroup_le_quadratic_joint_kernel {G : Type*} [Group G] :
    squareSubgroup G ≤ quadraticJointKernel G := by
  rw [squareSubgroup, quadraticJointKernel]
  refine le_iInf fun φ => Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨g, rfl⟩
  change φ (g ^ 2) = 1
  rw [map_pow]
  exact quadraticBit_sq (φ g)

#print axioms square_subgroup_le_quadratic_joint_kernel

/-- The quotient by `G²` has exponent dividing two and is commutative. These are the
available Mathlib-level properties of the maximal elementary abelian two-quotient. -/
theorem square_quotient_exponent_divides_two_and_commutative
    {G : Type*} [Group G] :
    Monoid.exponent (G ⧸ squareSubgroup G) ∣ 2 ∧
      ∀ x y : G ⧸ squareSubgroup G, x * y = y * x := by
  have hpow : ∀ q : G ⧸ squareSubgroup G, q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure (Set.mem_range_self g))
  constructor
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  · intro x y
    exact (Commute.of_orderOf_dvd_two
      (fun q => orderOf_dvd_of_pow_eq_one (hpow q)) x y).eq

#print axioms square_quotient_exponent_divides_two_and_commutative

/-- If `G²` is nontrivial, two distinct elements have identical values under every
quadratic observer, so the joint readout cannot recover a group element. -/
theorem quadratic_readout_has_collision {G : Type*} [Group G]
    (h : squareSubgroup G ≠ ⊥) :
    ∃ x y : G, x ≠ y ∧ quadraticReadout G x = quadraticReadout G y := by
  obtain ⟨x, hx, hxne⟩ := (Subgroup.bot_or_exists_ne_one (squareSubgroup G)).resolve_left h
  refine ⟨x, 1, hxne, ?_⟩
  funext φ
  have hxjoint : x ∈ quadraticJointKernel G :=
    square_subgroup_le_quadratic_joint_kernel hx
  have hxker : x ∈ MonoidHom.ker φ := (Subgroup.mem_iInf.mp hxjoint) φ
  simpa [quadraticReadout, MonoidHom.mem_ker] using hxker

#print axioms quadratic_readout_has_collision

/-- On `C₂`, the square subgroup is trivial and the identity observer separates all
elements. This concrete case shows that the nontrivial-square hypothesis is necessary. -/
theorem nontrivial_square_subgroup_is_necessary :
    squareSubgroup QuadraticBit = ⊥ ∧
      Function.Injective (quadraticReadout QuadraticBit) := by
  constructor
  · rw [squareSubgroup, Subgroup.normalClosure_eq_bot_iff]
    rintro _ ⟨g, rfl⟩
    exact quadraticBit_sq g
  · intro x y hxy
    have hid := congrFun hxy (MonoidHom.id QuadraticBit)
    simpa [quadraticReadout] using hid

#print axioms nontrivial_square_subgroup_is_necessary

/-- `C₄` is a named cyclic two-group strict example: it is commutative, its square subgroup
contains the nonidentity element two, and its joint quadratic readout has a collision. -/
theorem zmod_four_strictness_example :
    (∀ x y : Multiplicative (ZMod 4), x * y = y * x) ∧
      squareSubgroup (Multiplicative (ZMod 4)) ≠ ⊥ ∧
        ∃ x y : Multiplicative (ZMod 4),
          x ≠ y ∧ quadraticReadout _ x = quadraticReadout _ y := by
  have hsquare : squareSubgroup (Multiplicative (ZMod 4)) ≠ ⊥ := by
    intro hbot
    have hmem : Multiplicative.ofAdd (2 : ZMod 4) ∈
        squareSubgroup (Multiplicative (ZMod 4)) := by
      apply Subgroup.subset_normalClosure
      refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
      decide
    have htwo : Multiplicative.ofAdd (2 : ZMod 4) = 1 :=
      Subgroup.mem_bot.mp (hbot ▸ hmem)
    exact (by decide : Multiplicative.ofAdd (2 : ZMod 4) ≠ 1) htwo
  exact ⟨mul_comm, hsquare, quadratic_readout_has_collision hsquare⟩

#print axioms zmod_four_strictness_example

-- Empty-domain audit: a group cannot have an empty carrier because it contains one.
example {G : Type*} [Group G] : Nonempty G := ⟨1⟩

-- Trivial-group audit: its square subgroup is trivial and every readout is injective.
example : squareSubgroup Unit = ⊥ ∧ Function.Injective (quadraticReadout Unit) := by
  constructor
  · exact Subsingleton.elim _ _
  · intro x y _
    exact Subsingleton.elim x y

-- Trivial-observer audit: the constant homomorphism never adds separating power.
example {G : Type*} [Group G] (x y : G) :
    (1 : QuadraticObserver G) x = (1 : QuadraticObserver G) y := by
  simp

-- Noncommutative audit: the same strictness applies to the permutation group on three points.
example :
    (¬∀ a b : Equiv.Perm (Fin 3), a * b = b * a) ∧
      ∃ x y : Equiv.Perm (Fin 3),
        x ≠ y ∧ quadraticReadout _ x = quadraticReadout _ y := by
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let b : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hnoncomm : ¬∀ x y : Equiv.Perm (Fin 3), x * y = y * x := by
    intro hcomm
    exact (by decide : a * b ≠ b * a) (hcomm a b)
  have hsquare : squareSubgroup (Equiv.Perm (Fin 3)) ≠ ⊥ := by
    intro hbot
    have hmem : (a * b) ^ 2 ∈ squareSubgroup (Equiv.Perm (Fin 3)) :=
      Subgroup.subset_normalClosure (Set.mem_range_self (a * b))
    have hone : (a * b) ^ 2 = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
    exact (by decide : (a * b) ^ 2 ≠ 1) hone
  exact ⟨hnoncomm, quadratic_readout_has_collision hsquare⟩

-- There is no numeric depth parameter in these definitions, so an `n = 0` audit is inapplicable.

end D5.S3.Factorization.Galois.QuadraticObservationBound
