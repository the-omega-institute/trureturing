# Near invariance forces an exact proper subgroup

## Abstract

Rounded displacement packing and proper-stabilizer localization.

**Theorem 1.1 (Original-label retention in a proper stabilizer).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration.near_invariant_localization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration.near_invariant_localization` (`✓ std3`). ∎

*Citation.* Benjamin Bedert, Matija Bucić, Noah Kravitz, Richard Montgomery, Alp Müyesser (2025). *On Graham's rearrangement conjecture over F₂ⁿ*. DOI: [10.48550/arXiv.2508.18254](https://doi.org/10.48550/arXiv.2508.18254).

*Commentary.*

For every finite possibly nonabelian group K and nonempty set T, let tau=|T|/|K|. A real mean-zero Euclidean unit vector with regular-action correlation at least (1-beta)|T|, where 0<=beta<=tau^2/1000, yields an actual proper subgroup L retaining at least (1-50 beta/tau^2)|T| original labels. The retained finset is precisely the elements of L whose original values lie in T.

The action is U_g v(x)=v(xg), with its Euclidean isometry proved by coordinate permutation and its orbit sum zero by finite reindexing. The second moment of D(g)=norm(U_g v-v) is at most 2 beta |T|. The closed ball of radius tau/5 contains most labels. Only its positive squared radius is divided out, so beta=0 is included.

Put M=floor(4/tau) and q=(M+2)/3 in the natural numbers. If every successive ball grows, the q shells with indices 3i+1 give disjoint translates of the small ball. Their exact integer cardinalities contradict its density. The resulting plateau at k<=4/tau gives X=B((k-1)tau/5) and the actual left stabilizer L=stabilizer K X. It contains the small ball. Since 1 lies in X and X is contained in B(4/5), the zero orbit sum and triangle inequality force L to be proper.

This is the localization part of the finite-group structural core adapted from Section 4 of the cited paper. Quantitative retained-label descent, the all-real-vector numerical gap, centered-indicator directed cuts, complex eigenvalue readout and full original-colour coset/index consequences remain outside this checkpoint. The intended descent must stop at the numerical condition: eigenvalue real parts alone do not control a nonnormal operator's quadratic forms.

Identity labels and loops are allowed in this structural lemma. This permission does not transfer to rainbow-path consumers. No connector, matching, coupling or absorption proof is certified, and original proper-interval Good and unrestricted AM remain open. The construction is literature-adapted, with no novelty claim.

The faithful dependent-family Reg proof compiles, but its source binding remains declared_unresolved with diagnostic source.residual_requires_open. An accepted binding certificate is missing; no declared_validated audit is claimed. The source-owner disclosure is https://github.com/the-omega-institute/trureturing/issues/21342.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration.near_invariant_localization`
