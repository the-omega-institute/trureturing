# Fresh Completion of a Complete Prime Chain

## Abstract

The complete residual of a saturated prime chain limits how many unused cofactor heights can remain. A hypothetical injection of its actual residue projection into those heights constructs a smaller whole cover.

**Theorem 1.1 (Every residual point satisfies every chain cofactor).**

Lean statement: `D5/S3/Arith/Covering/SingleChainFreshCompletion.single_chain_pfree_residual_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/SingleChainFreshCompletion.single_chain_pfree_residual_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a finite whole cover by pairwise distinct odd moduli greater than one. Let p and ell be distinct primes. Suppose the complete list of original moduli divisible by p consists of p ell^j for j from zero through p minus one, with the actual first p-roots pairwise distinct. A point avoiding every original whose modulus is not divisible by p is congruent to each chain member's actual residue modulo ell^j.

Factor the actual common period into a power of p and a coprime remainder. For each chain member, CRT changes only the first p-root to that member's root and preserves the remainder coordinates. An original covering the resulting point must belong to the chain; distinct roots identify it. Its cofactor congruence therefore holds at the original residual point. This argument assumes neither minimality nor an already aligned common cofactor phase.

This consequence of the existing CRT and actual-period interfaces is used inside the fresh-completion construction.

**Theorem 1.2 (Unused heights are fewer than actual surviving roots).**

Lean statement: `D5/S3/Arith/Covering/SingleChainFreshCompletion.fresh_ladder_projection_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/SingleChainFreshCompletion.fresh_ladder_projection_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same complete chain and assume F has globally minimum class count among odd distinct whole covers. Let s be any odd integer greater than one, coprime to ell. Let U be the exponents j below p for which s ell^j is absent from the entire original numerical palette. Let S be the set of residues modulo s attained by points avoiding all p-free originals. Assume the cardinality of S is strictly less than p.

Let c be the actual residue of the top chain member, and let A contain the distinct s-roots of retained p-free originals of modulus s ell^j, j below p, whose cofactor residue is c modulo ell^j. Then the cardinality of U is strictly less than that of S, and the sum of the cardinalities of S and A is at most s.

If the first inequality failed, embed the actual roots S into the unused heights U. For each root, insert the CRT class with that s-root and cofactor residue c at its assigned height. Retain all p-free originals and delete the complete p-chain. A point already having a retained owner stays covered. Every other point belongs to the complete residual, satisfies the top cofactor congruence, and is covered by its assigned fresh class.

The assigned heights are distinct, every new numerical label is absent from F, and all new moduli are odd and greater than one. The proof constructs the new whole cover and verifies these properties internally. Its class count replaces p originals by fewer than p new ones, contradicting the stated minimum. The second inequality follows because a residual root in A would already have a retained owner on the terminal cylinder.

All roots, blockers, heights and phases refer to the same original F. The integer s need not be prime, smaller than p, or an original modulus. The actual projection bound is a hypothesis; s less than p is one sufficient way to obtain it. No modulus-sum minimum or bound on other prime heights is assumed. These are necessary conditions on this complete-chain branch, and do not establish unrestricted noncoverage.

## References

- Truth anchor: `D5/S3/Arith/Covering/SingleChainFreshCompletion.fresh_ladder_projection_bounds`
- Truth anchor: `D5/S3/Arith/Covering/SingleChainFreshCompletion.single_chain_pfree_residual_subset`
