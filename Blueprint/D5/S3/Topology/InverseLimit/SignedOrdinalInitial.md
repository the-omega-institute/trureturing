# Actual initial cubes

## Abstract

Full Boolean cubes and the first ordinal predecessor

**Definition 1.1 (Finite and omega cubes).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.H0`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.H0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H0 is a Prefix(succ omega) whose carrier at every ordinal a<succ omega is the entire function space Coord(a) to Bool. Each carrier is closed and contains the constant-false point. Every transition is SignedProperLimit.restrict on the literal coordinates. Surjectivity extends a Boolean function by false outside its original coordinate domain; it is proved for every lower-stage pair, including the finite stages and omega.

**Definition 1.2 (Empty-history omega predecessor).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.predecessor`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.predecessor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

predecessor constructs SignedOrdinalSuccessor.Predecessor H0 (le_refl omega) without any predecessor assumption or CH. Properness is omega<omega-one. The current full omega cube maps onto Cube(omega) by reflexive coordinate restriction, which is the identity. A row r in Rows(omega) satisfies omega<=r<=omega, so it equals newRow. Every old-row U, V, nu, I, J, A, B, C, E and F field is obtained by eliminating its impossible inequality r!=newRow.

A historical birth would have b<omega, omega<=r and max(r,d)=b, contradicting omega<=b. The births field eliminates this contradiction on its exact dependent domain; it supplies no placeholder reservoir, support family or measure. Under CH this actual prefix and predecessor are inputs to SignedOrdinalSuccessor.exists_successor with its original launch and treatment telescope. The initial construction supplies no ordinal schedule, delayed execution, successor F transport, well-founded history, final omega-one limit, CH theorem or official solution.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.H0`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalInitial.predecessor`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalSuccessor](SignedOrdinalSuccessor.md)
