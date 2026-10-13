# Noncommutative edge return orbits

## Abstract

For the original paired-edge relation, the six edge slots split into a low family
`{0,5,3}` and a high family `{1,2,4}`. After the displayed normalization, every
actual edge chain is exactly an orbit of the corresponding return word.

**Definition 1.1 (Original edge equivalence closure).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.edgeClass`

*Formalization.* `D5/S3/Geometry/Hyperideal/ReturnCycleWords.edgeClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

`edgeClass u v` is the equivalence closure of the original `edgeRel (pairing u v)`;
all later orbit statements refer to this unchanged relation.

**Definition 1.2 (Edge family).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.family`

*Formalization.* `D5/S3/Geometry/Hyperideal/ReturnCycleWords.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

`family j` is false on slots 0, 3 and 5 and true on slots 1, 2 and 4. It records
the low/high edge family without identifying the two families.

**Definition 1.3 (Representative edge slot).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.baseEdge`

*Formalization.* `D5/S3/Geometry/Hyperideal/ReturnCycleWords.baseEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low family uses representative slot 0 and the high family representative slot 1.

**Definition 1.4 (Normalized edge coordinate).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.normalizeEdge`

*Formalization.* `D5/S3/Geometry/Hyperideal/ReturnCycleWords.normalizeEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six slot multipliers are `[1, 1, v*u, u², u, u]`, in slot order 0 through 5.
The normalized coordinate is in representative slot 0 for the low family and
slot 1 for the high family.

**Definition 1.5 (Edge return word and subgroup).**

Lean statements: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.returnWord`,
`D5/S3/Geometry/Hyperideal/ReturnCycleWords.returnGroup`

*Formalization.* Both declarations are machine-checked in the target module (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low return word is `v⁻¹*u²`; the high return word is `v²*u`. `returnGroup`
is the subgroup closure of the selected word, so inverse and product powers remain
inside the same actual family.

**Theorem 1.6 (Actual edge equivalence is exactly a return orbit).**

Lean statement: `D5/S3/Geometry/Hyperideal/ReturnCycleWords.actual_edge_orbit_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/ReturnCycleWords.actual_edge_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group `G`, every type `Ω` with the opposite-group action, all `u,v : G`,
and occurrences `a,b : Ω × Fin 6`, the equivalence closure of the original
`edgeRel (pairing u v)` relates `a` and `b` exactly when they have the same low/high
family and some element of the corresponding `returnGroup` sends the normalized
coordinate of `a` to that of `b`. The forward proof checks every actual face-slot
generator and propagates the invariant through reflexive, symmetric and transitive
chains. The reverse proof expands a subgroup word into actual three-step cycles and
connects every occurrence to its normalized representative. No finiteness,
faithfulness, transitivity or freeness assumption is used. This characterizes the
edge relation only; it does not assert endpoint orientation, link topology, metric
geometry, Euler characteristic or a polygon-manifold realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.facePair`
- Truth anchor: `D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.slotMap`
- Truth anchor: `D5/S3/Geometry/Hyperideal/NoncommutativeCornerOrbits.act_mul`
- Dependency: `D5/S3/Geometry/Hyperideal/ActualCornerTransport`
