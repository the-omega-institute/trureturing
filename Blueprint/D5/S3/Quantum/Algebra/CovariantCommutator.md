# Covariant Commutator Factorization

## Abstract

Covariance factors commutators independently of any particular representation.

**Theorem 1.1 (Semiconjugacy factors the commutator).**

$$\forall U,f,t \in B,\  U f = t U \Rightarrow U f - f U = (t - f) U.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_commutator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For elements U, f, and t in any associative ring, the covariance equation U f = t U rewrites the oriented commutator as U f - f U = (t - f) U. In Lean, SemiconjBy carries exactly this covariance equation, and sub_mul supplies the entire factorization after rewriting.

No topology, norm, star operation, completion, concrete representation, or universal property enters this declaration. It is only the representation-independent algebraic consequence of covariance.

**Theorem 1.2 (The opposite commutator has the opposite difference).**

$$\forall U,f,t \in B,\  U f = t U \Rightarrow f U - U f = (f - t) U.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_opposite_commutator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the commutator orientation reverses the translated difference while leaving the common right factor U unchanged. This corollary records the sign convention explicitly instead of requiring downstream users to negate the first formula.

**Theorem 1.3 (Every covariant group pair obeys the factorization).**

$$\forall g \in Gamma,a \in A,\  U_{g} \operatorname{embed}(a) = \operatorname{embed}(action_{g}(a)) U_{g} \Rightarrow U_{g} \operatorname{embed}(a) - \operatorname{embed}(a) U_{g} = (\operatorname{embed}(action_{g}(a)) - \operatorname{embed}(a)) U_{g}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_pair_commutator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on a source semiring by ring equivalences, let embed map the source into an arbitrary target ring, and let U assign a target-ring unit to every group element. Pointwise covariance is a SemiconjBy hypothesis, so the generic factorization applies to every group element and source observable.

The companion declaration covariant_pair_opposite_commutator_formula records the reversed orientation for the same covariant pair. These declarations do not construct a crossed product or assert that a given observer interface uniquely forces one.

**Theorem 1.4 (The two-address window is a noncommuting covariant pair).**

$$C = \operatorname{clock}(2), S = \operatorname{shift}(2), r = \operatorname{root}(2),\  C S = (r S) C \land C S - S C \neq 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CovariantCommutator.window_two_covariant_commutator_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the existing two-address finite window, the clock semiconjugates the cyclic shift to the primitive phase times that shift. This is the finite Weyl relation rewritten with the scalar on the shift before multiplication by the clock.

The commutator is explicitly nonzero. If it vanished, the Weyl relation would force the primitive phase to fix the shift-clock product. At matrix entry (0,1), that product equals the primitive phase itself; cancellation would make the order-two primitive root equal to one, contradicting primitivity. Thus both the covariance premise and a genuinely noncommuting instance are inhabited.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_commutator_formula`
- Truth anchor: `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_opposite_commutator_formula`
- Truth anchor: `D5/S3/Quantum/Algebra/CovariantCommutator.covariant_pair_commutator_formula`
- Truth anchor: `D5/S3/Quantum/Algebra/CovariantCommutator.window_two_covariant_commutator_witness`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
