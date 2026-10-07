# A finite non-tree Big-3 state

`finite-state.json` supplies 35 E-coset representatives at n=6. Start with all
full-length and next-to-full-length prefix-reversal edges. In every selected
E coset, replace the next-to-full edges by the n−2 reversal edges. The result
has all 360 full-length matching edges and forms one 720-vertex closed cycle.

Run from the repository root:

```sh
python3 docs/reports/big3-necklace-transitions/verify_finite_state.py
```

The reader independently generates all permutations, uses actual tuple prefix
reversals, reconstructs E orbits, rejects repeated selected cosets, and verifies
degree two, symmetric adjacency, every full-length matching edge, all permitted
edge lengths, all n! distinct vertices, and the closing edge. Its counts are
360 length-6, 185 length-5 and 175 length-4 edges. It consumes neither a SAT
solver nor a saved cycle or coset integer IDs.

The producer found this state through deterministic connectivity cuts without
a tree constraint. A separate raw-cycle reader checked it before publication.
This reconstruction is the portable evidence. It shows that the impossible
tree count 4t=59 does not imply failure of the broader E-only route. It proves
one finite state and supplies no all-n construction, unique credit, new Lean
instance or official acceptance.

The mathematical interpretation and remaining uniform obligation are in
[the theory volume](../../develop/theory/BIG3_NECKLACE_TRANSITION_INTERFACE.md).
