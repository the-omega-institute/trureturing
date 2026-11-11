# Circuit balance and least confirmation

## Abstract

On the original finite dimensional real carrier, balance of every pure circuit constructs linear proper confirming effects and forces reciprocity, least confirmation on the whole cone and every finite pure mixture law, under an explicit pure conic generation hypothesis.

Let A be a finite dimensional real vector space, C a cone closed under addition and nonnegative scaling, and u a real linear functional nonnegative on C. The real span of C is all of A. All effects below act on this same A. The result additionally assumes that C is exactly the nonnegative conic hull of all extreme points of its entire normalized base. This is a mathematical generation hypothesis, not a supplier of relation preservation, reciprocity or least confirmation.

**Definition 1.1 (The entire normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the specified C and u, base(C,u) consists of all x in C with u(x)=1. No selected preparations replace this base.

**Definition 1.2 (All pure points).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pure set P is exactly the set of extreme points of base(C,u), with extremality over the real scalars. It is not an independently chosen list and need not be finite or consist of exposed points.

**Definition 1.3 (The full proper interval).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real linear functional f on A is proper precisely when 0 <= f(x) <= u(x) for every x in the original C. Every such f is available in this mathematical interval.

**Definition 1.4 (All confirming proper effects).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate confirms(C,u,p,f) requires f to be proper on all of C and f(p)=1. In particular the original u confirms each pure point.

**Definition 1.5 (The original comparison lower envelope).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a pure reference p, the value T_p(x) is the real infimum of f(x) over all original proper effects f confirming p. For each x in C this set of readings is nonempty and bounded below by zero. The theorem proves that its infimum is attained by the constructed effect; it does not assume attainment.

**Definition 1.6 (Actual minimal signed relations).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite subset s of P, a coefficient function c on s is a circuit when c is nonzero, its weighted sum of the original pure vectors is zero, and any nonzero signed relation w supported inside the support of c has exactly that support. The finite ambient subset may contain unused labels; the actual support is the circuit. Subtype labels are distinct original pure points. No preservation of signs is imposed on competitors.

**Definition 1.7 (Balance on every circuit).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar assignment v on P is balanced when, for every finite subset s and every circuit c on s, the sum of c(i)v(i) is zero. Applied at reference p, the assignment is v(q)=T_q(p); reciprocity is absent from this definition.

**Theorem 1.8 (Reciprocal least confirmation and every finite mixture).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every C and u satisfying nonnegativity of u on C, real spanning of C, and the exact equality C=cone(P), suppose q maps to T_q(p) is balanced for every pure reference p. Then there exists a family of real linear functionals e_p on the original A with all six properties: each e_p is proper and confirms p; e_p(q)=T_q(p) for every pure q; T_p(q)=T_q(p) for every pair of pure references; e_p(x)<=f(x) for every x in C and every original proper f confirming p; T_p(x)=e_p(x) for every x in C; and for every finite n, pure list q indexed by Fin n, and nonnegative real weights summing to one, T_p(sum_i w_i q_i)=sum_i w_i T_{q_i}(p). Zero weights, unequal positive weights and duplicate pure labels are all included. The construction also works with degenerate carriers; no inner product, matrix algebra or chosen second carrier occurs.

Choose real coordinates only to apply NonnegativeKernelCircuit.OrderedField.signConformalGlobalKernelCircuitDecomposition to each finite relation. Its summands are minimal signed relations within the original support, so circuit balance annihilates each summand and hence every relation. The existing linear quotient construction then descends the assignment to a functional on A. Bounds on pure points extend by nonnegative conic generation to the entire C, putting e_p inside the full proper confirming interval. Thus T_p(q)<=e_p(q)=T_q(p). Constructing e_q and exchanging the references supplies the opposite inequality. Reciprocity follows, and the same bounds show e_p is least on the entire original cone. Since it is itself a confirmer, the lower envelope equals it, and its linearity yields every finite mixture formula.

Application boundary for Quantum Origin V Lemmas 77.15 and Theorem 77.16. The support-contained signed decomposition is an existing result, directly reused here. The explicit equality C=cone(ext(base(C,u))) remains to be derived for the original nonzero finite dimensional closed pointed generating cone with a unit strictly positive away from zero. This module neither replaces those original hypotheses nor claims that equality from the name of a carrier. The converse from full S to circuit balance, the dimension bound on circuit size, and the at-least-two-points assertion for each sign remain separate obligations. Consequently the complete original equivalence and its original PRE, Jordan, reset, H13/C13 and static consumers are not established here. Mathematical effects and finite sums do not supply preparation programs, actual menus, histories or operations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit](../Entanglement/AbsolutePPT/NonnegativeKernelCircuit.md)
