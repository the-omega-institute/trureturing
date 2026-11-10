# An unbounded obstruction forces mixed SMALL/LARGE insertion

## Abstract

An unbounded obstruction forces mixed SMALL/LARGE insertion.

**Theorem 1.1 (An unbounded obstruction forces mixed SMALL/LARGE insertion).**

Lean statement: `D5/S3/Combinatorics/Circle/ForcedMixedDyadic.forced_mixed_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ForcedMixedDyadic.forced_mixed_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=3, at the actual source k=4*r and d=(2^(4*r)-1)/15, there is a native Legal word W with G(W)=3. A strict native Legal competitor introducing at most two originally fresh labels exists. Every such competitor V, with arbitrary old returns and arbitrary order, has V.toFinset minus W.toFinset exactly {e,z}, where e and z are distinct existential physical labels with actual values +2*d and -7*d. The conclusion does not single out a fixed displayed pair: alternative equal-valued outsiders remain possible.

The old word concatenates r-2 physical rows with values [4,2,1,-7], then appends [4,1,1] using the last two rows. It uses all r unit labels, r-2 labels of value 2, r-1 top labels and r-2 reset labels. Its scaled endpoint is 6, and U(W)=5. The physical indices are proved distinct. Each complete row has heights 0,4,6,7,0, while the tail has heights 0,4,5,6. Source scaling transports all natural prefixes to the original half-modulus strip.

For an arbitrary competitor, take the actual fresh and returned set differences and their exact physical permutation. Its fresh +4 count is at most one, there are no fresh unit labels, and the total fresh count is at most two. Its endpoint lies in [0,7]; reset_top_bound constrains its consumed +4 and -7 counts for every possible ordering. Exact endpoint, G, H and U balances then force fresh counts (top,reset,small)=(0,1,1). The strict energy comparison uses 3^(4*d)<3^(7*d), with d>0 derived from the native source.

forced_mixed_of_counts proves this universal necessity for every old native inventory with the stated residue multiplicities. obstructing_inventory_exists realizes that inventory for every r>=3. The arbitrary-word augmentation supplies a real competitor, so the obstruction is non-vacuous. It excludes both one-fresh improvement and every two-fresh LARGE-only strategy in this family. It is not a counterexample to the two-fresh theorem or a solution of full arbitrary-source C3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ForcedMixedDyadic.forced_mixed_obstruction`
- Dependency: [D5/S3/Combinatorics/Circle/DyadicResetDenominations](DyadicResetDenominations.md)
- Dependency: [D5/S3/Combinatorics/Circle/MixedDyadicAugmentation](MixedDyadicAugmentation.md)
