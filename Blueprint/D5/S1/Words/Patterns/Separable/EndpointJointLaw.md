# Coupled endpoint count and terminal type

## Abstract

The actual marked-cycle law gives the coupled distribution of low-value suffix removals and the terminal endpoint type.

A marked cycle retains its initial direct or skew sign, all actual removed permutation shapes, and its actual terminal indecomposable shape. Its probability mass function is the normalized actual shape law from the finite-prefix limit model. The two observations below are taken from the same cycle; they are not sampled independently.

**Definition 1.1 (Low-value suffix removals).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.lowRemovalCount`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointJointLaw.lowRemovalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an actual UnboundedCycle, a terminal node has count zero. A discard node adds one exactly when its current sign is true, and then continues on the tail whose sign is reversed. True denotes a skew cut: its removed right block has lower values than the retained left block. False denotes a direct cut and contributes zero to this count. Thus N counts low-value right suffix removals, not all discard steps.

**Definition 1.2 (The terminal endpoint type).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.finiteTerminal`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointJointLaw.finiteTerminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a terminal node with sign s, finiteTerminal is the Boolean negation of s; a discard node passes on the terminal type of its tail. A direct terminal cut therefore gives true. This is the finite-value emission convention of the endpoint-history word in the limit model. Both direct and skew terminal shapes are finite combinatorial objects; the Boolean distinguishes their endpoint emission types, not whether a Lean shape itself is infinite.

**Definition 1.3 (The joint observation).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.observation`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointJointLaw.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a marked cycle c, observation(c) is the ordered pair (lowRemovalCount(c),finiteTerminal(c)). Write this pair as (N,chi), with chi=true represented by 1 and chi=false by 0 in probability notation.

**Definition 1.4 (Pushforward of the actual cycle law).**

Lean statement: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.endpointPMF`

*Formalization.* `D5/S1/Words/Patterns/Separable/EndpointJointLaw.endpointPMF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

endpointPMF is cyclePMF.map(observation), a probability mass function on natural numbers times Bool. In particular its value at (r,s) is the total actual marked-cycle mass of precisely the cycles with joint observation (r,s). It is not an independently chosen primitive distribution.

Put t=sqrt(2)-1 and a=1-1/sqrt(2), as real numbers. The critical shape-law parameter b equals t, and its terminal-shape mass ceiling equals a; the separately named parameter a in the shape-count construction is twice this terminal mass. In the displayed formula p(r,s) abbreviates endpointPMF((r,s)), and ofReal maps a real number to the extended nonnegative reals.

**Theorem 1.5 (The complete coupled endpoint law).**

$$\forall r \in \mathbb{N},\; \operatorname{p}\left(0, true\right) = \operatorname{ofReal}\left(a\right) \land \left(\operatorname{p}\left(0, false\right) = \operatorname{ofReal}\left(a \cdot \left(1 + t\right)\right) \land \left(1 \le r \Rightarrow \left(\operatorname{p}\left(r, true\right) = \operatorname{ofReal}\left(a \cdot t \cdot \left(1 + t\right) \cdot t^{2 \cdot r - 2}\right) \land \operatorname{p}\left(r, false\right) = \operatorname{ofReal}\left(t \cdot a \cdot t \cdot \left(1 + t\right) \cdot t^{2 \cdot r - 2}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointJointLaw.whole_endpoint_joint_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural parameter r is unrestricted. The first two equations give the two exceptional masses at zero. The implication gives both masses at every positive r; its exponent 2r-2 is natural-number subtraction, which is ordinary subtraction under r at least one. Consequently u(r)=p(r,true) and v(r)=p(r,false) satisfy u(0)=a, v(0)=a(1+t), u(r)=a*t*(1+t)*t^(2r-2), and v(r)=t*u(r) for all positive r.

Enumerate a cycle by its initial sign s and its total number k of discard steps, retaining every actual shape. Structural recursion on the alternating cycle identifies all observation fibers. The observation (0,true) occurs exactly for (s,k)=(false,0). For every natural j, (j+1,true) occurs exactly for (true,2j+1) or (false,2j+2), while (j,false) occurs exactly for (true,2j) or (false,2j+1). These are complete classifications of the actual observations, including zero removals.

The total actual shape mass at fixed s,k is ofReal(a*t^k). Reindexing the pushforward sum by the size-preserving cycle enumeration and the classified fibers therefore leaves one term for (0,true) and two terms for every other fiber above. Adding these masses and simplifying yields the four equations. No independence between the count and the terminal type is used.

This law concerns the endpoint observations of the existing actual finite-prefix limit model. It does not assert convergence of the entire finite-size endpoint event after an infinite aggregation, nor a reconstructed infinite permutation, a predictable conditional hazard, an occupied-mass lower bound, or discrepancy marginal estimates.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.endpointPMF`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.finiteTerminal`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.lowRemovalCount`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.observation`
- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointJointLaw.whole_endpoint_joint_law`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCycleLaw](ActualCycleLaw.md)
