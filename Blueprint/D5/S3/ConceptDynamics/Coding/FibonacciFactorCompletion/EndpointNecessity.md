# Fixed-tail endpoint-budget necessity

## Abstract

The same full actual tails across every finite history force the original six-group endpoint budget in Q(t).

**Theorem 1.1 (Every fixed actual tail obeys the complete endpoint budget).**

$$\forall s1 \in Guard, s2 \in Guard, P \in \operatorname{List}\left(Label\right), Q \in \operatorname{List}\left(Label\right), h \in \operatorname{List}\left(Color\right), U \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Label\right)\right), V \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Label\right)\right), W \in \operatorname{Function}\left(Bool, \operatorname{List}\left(Color\right)\right), L \in Nat, xi \in \operatorname{Function}\left(Nat, Label\right), eta \in \operatorname{Function}\left(Nat, Label\right), x \in \operatorname{Function}\left(Nat, Real\right), y \in \operatorname{Function}\left(Nat, Real\right), path1 \in \operatorname{Function}\left(Nat, Guard\right), path2 \in \operatorname{Function}\left(Nat, Guard\right), b \in Real,\; \left(\operatorname{length}\left(P\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{length}\left(Q\right) = \operatorname{length}\left(h\right) \land \left(\operatorname{lt}\left(0, L\right) \land \left(\left(\forall i \in Bool,\; \operatorname{length}\left(\operatorname{apply}\left(U, i\right)\right) = L \land \left(\operatorname{length}\left(\operatorname{apply}\left(V, i\right)\right) = L \land \left(\operatorname{length}\left(\operatorname{apply}\left(W, i\right)\right) = L \land \left(\operatorname{LegalWord}\left(s1, s1, \operatorname{apply}\left(U, i\right)\right) \land \operatorname{LegalWord}\left(s2, s2, \operatorname{apply}\left(V, i\right)\right)\right)\right)\right)\right) \land \left(\operatorname{le}\left(0, b\right) \land \left(\forall zs \in \operatorname{List}\left(Bool\right),\; \operatorname{ClosedOriginalTailExtension}\left(b, \operatorname{append}\left(P, \operatorname{choiceBlocks}\left(U, zs\right)\right), \operatorname{append}\left(h, \operatorname{choiceBlocks}\left(W, zs\right)\right), xi, x, path1\right) \land \operatorname{ClosedOriginalTailExtension}\left(b, \operatorname{append}\left(Q, \operatorname{choiceBlocks}\left(V, zs\right)\right), \operatorname{append}\left(h, \operatorname{choiceBlocks}\left(W, zs\right)\right), eta, y, path2\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{familyEndpointBudget}\left(P, Q, h, U, V, W, L\right), b\right) \land \operatorname{member}\left(\operatorname{familyEndpointBudget}\left(P, Q, h, U, V, W, L\right), coefficientField\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity.original_fixed_tail_endpoint_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ClosedOriginalTailExtension(b,A,cs,xi,x,path) means there exist full literal, scalar and guard sequences a,X,q starting at guard G0, following every original nextGuard edge, supported at every position, and satisfying X(p)=branch(a(p),X(p+1)). The first length(A) labels equal A. At length(A)+p all three future sequences equal respectively xi(p),x(p),path(p), for every p. Only departures r<length(cs) satisfy ClosedExpanded(b,cs[r],X(r)). The theorem makes the observed source and color lengths equal. ClosedExpanded(b,c,z) is the original closed relaxation z in [-1,phi], cut(c)-b<=z<=cut(c+1)+b.

The same two full futures are fixed before every finite Boolean choice word, including the empty word. Their starting scalars need not belong to either canonical hull. For each component, the existing canonical periodic endpoint supplies one repeated extremal return when (-g)^L is positive, or two alternating extremal returns when it is negative. Finite repetitions act on the original fixed scalar. The existing signed orbit criterion, applied to the closed affine preimage of one slot constraint, forces that endpoint to satisfy the slot. Stem slots use the extremal choice history directly; each return slot uses its chosen first return followed by that history. Both endpoints of every one of the six indexed groups are included. Different endpoint tests may use different histories under the universal premise.

familyEndpointBudget is the existing foldr max 0 of familyEndpointCosts, with exactly two stem groups and all four return groups. Equal-valued entries are retained. Original suffix evaluations, all cut values and canonical endpoints belong to coefficientField=Q(t); every finite maximum selects one of its arguments. Each endpoint cost is at most the supplied nonnegative b, so the whole maximum is at most b and belongs to that field. Empty stems, singleton hulls, equal returns, either slope sign and b=0 are included. This necessary bound does not require U(false)!=U(true); the original source-separation requirements remain in the separate original goal.

This is necessity for the closed relaxation. It asserts neither ownership-sensitive color attainment at equality, nor a new decoder-capacity or optional-piece result. No terminal color is tested. The high and low futures may differ. No budget infimum over a changing family of tails replaces the original fixed-tail quantifiers.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity.original_fixed_tail_endpoint_budget`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion](../FibonacciFactorCompletion.md)
