# Quadratic companion defect

## Abstract

Integral elimination of an identity-plus-square companion using two initial coordinates.

A is any additive commutative group and J:A->A any additive homomorphism. Rows have n+2 coordinates indexed by Fin(n+2). first(v)=v(0), second(v)=v((0:Fin(n+1)).succ), and skipSum(v,j)=v(j.succ.succ)+v(j.castSucc.castSucc). All shears and recurrences use only addition and subtraction. No field, division by two, finite state-space or torsion-free hypothesis is imposed.

**Definition 1.1 (A two-coordinate integral recurrence).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), n \in Nat, a \in A, b \in A, t \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), A\right),\; \operatorname{hasType}\left(\operatorname{reconstruct}\left(n, a, b, t\right), \operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right)\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At n=0 the row is (a,b). At n+1 it is Fin.cons a applied to reconstruct n with initial values b and t(0)-a and remaining input t(j.succ). Therefore every tail satisfies v(j+2)+v(j)=t(j), including all boundary cases.

**Definition 1.2 (Two free values and all two-step sums).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), n \in Nat,\; \operatorname{hasType}\left(\operatorname{domainEquiv}\left(n\right), \operatorname{AddEquiv}\left(\operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right), \operatorname{Prod}\left(\operatorname{Prod}\left(A, A\right), \operatorname{Function}\left(\operatorname{Fin}\left(n\right), A\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.domainEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is v -> ((first(v),second(v)), j -> skipSum(v,j)); its inverse is reconstruct. The reconstruction identities prove both inverse equations on the entire additive group.

**Definition 1.3 (Sum omitting the rightmost coordinate).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), n \in Nat, v \in \operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right),\; \operatorname{hasType}\left(\operatorname{prefixSum}\left(n, v\right), A\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.prefixSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

prefixSum n v is the sum over j:Fin(n+1) of v(j.castSucc). It is the sum of the coordinates that remain after one companion shift.

**Definition 1.4 (The actual two-step boundary and tail equations).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), J \in \operatorname{AddMonoidHom}\left(A, A\right), n \in Nat,\; \operatorname{hasType}\left(\operatorname{companion}\left(J, n\right), \operatorname{AddMonoidHom}\left(\operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right), \operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.companion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write S=sum v and P=prefixSum n v. The output is (a+J(J(S)+P), b+J(S), j -> skipSum(v,j)). This is identity plus the square of the reset companion whose first transition coordinate is J(sum v). J need not be invertible for the definition or general elimination.

**Definition 1.5 (Remove inhomogeneous tail contributions).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), J \in \operatorname{AddMonoidHom}\left(A, A\right), n \in Nat,\; \operatorname{hasType}\left(\operatorname{codomainEquiv}\left(J, n\right), \operatorname{AddEquiv}\left(\operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right), \operatorname{Prod}\left(\operatorname{Prod}\left(A, A\right), \operatorname{Function}\left(\operatorname{Fin}\left(n\right), A\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.codomainEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given y, let t(j)=y(j.succ.succ), and p=reconstruct n 0 0 t. Subtract the first two coordinates of companion J n p from (first(y),second(y)); retain t. The inverse adds this same correction and uses Fin.cons twice. The shear is independent of the two free domain values.

**Definition 1.6 (The homogeneous two-dimensional boundary map).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), J \in \operatorname{AddMonoidHom}\left(A, A\right), n \in Nat, a \in A, b \in A,\; \operatorname{hasType}\left(\operatorname{boundary}\left(J, n, a, b\right), \operatorname{Prod}\left(A, A\right)\right)$$

*Formalization.* `D5/S1/Recurrence/QuadraticCompanionDefect.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the first two companion coordinates on reconstruct n a b 0. The homogeneous row follows the actual period-four recurrence a,b,-a,-b. No rational eigenspace replaces its integer coordinates.

**Theorem 1.7 (Exact additive normal form of the quadratic defect).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), J \in \operatorname{AddMonoidHom}\left(A, A\right), n \in Nat, v \in \operatorname{Function}\left(\operatorname{Fin}\left(\operatorname{add}\left(n, 2\right)\right), A\right),\; \operatorname{apply}\left(\operatorname{codomainEquiv}\left(J, n\right), \operatorname{apply}\left(\operatorname{companion}\left(J, n\right), v\right)\right) = \operatorname{pair}\left(\operatorname{boundary}\left(J, n, \operatorname{first}\left(v\right), \operatorname{second}\left(v\right)\right), \operatorname{secondProjection}\left(\operatorname{apply}\left(\operatorname{domainEquiv}\left(n\right), v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/QuadraticCompanionDefect.eliminate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Separate v into its homogeneous reconstruction and its zero-head inhomogeneous reconstruction. Additivity shows that the codomain correction cancels exactly the latter's boundary contribution, while the remaining tails are identity. The domain and codomain equivalences were constructed separately.

**Theorem 1.8 (Two copies of identity plus an involution).**

$$\forall A \in Type, inst \in \operatorname{AddCommGroup}\left(A\right), J \in \operatorname{AddMonoidHom}\left(A, A\right), hJ \in \left(\forall x \in A,\; \operatorname{apply}\left(J, \operatorname{apply}\left(J, x\right)\right) = x\right), m \in Nat, a \in A, b \in A,\; \operatorname{boundary}\left(J, \operatorname{add}\left(\operatorname{mul}\left(4, m\right), 1\right), a, b\right) = \operatorname{pair}\left(\operatorname{add}\left(\operatorname{add}\left(a, b\right), \operatorname{apply}\left(J, \operatorname{add}\left(a, b\right)\right)\right), \operatorname{add}\left(b, \operatorname{apply}\left(J, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/QuadraticCompanionDefect.boundary_three_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier length is (4m+1)+2=4m+3. Its homogeneous row has total sum b and prefix sum a+b, proved by a four-step recurrence and induction on m. If J(J(x))=x for every x, the boundary is ((id+J)(a+b),(id+J)(b)). The integral shear (a,b)->(a+b,b) is invertible, so these are two independent copies of id+J. This includes m=0, carrier length three.

Escape audit status. The original generic theorems eliminate and boundary_three_mod_four and their mirrored Reg proofs compile. Their source bindings remain declared_unresolved: IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.params for eliminate and rule=source.state_binder for boundary_three_mod_four. The missing classified source bindings and certificates are tracked at https://github.com/the-omega-institute/trureturing/issues/15897. Their escape audits are unfinished; this issue supplies neither proof nor declared_validated status.

## References

- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.boundary`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.boundary_three_mod_four`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.codomainEquiv`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.companion`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.domainEquiv`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.eliminate`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.prefixSum`
- Truth anchor: `D5/S1/Recurrence/QuadraticCompanionDefect.reconstruct`
