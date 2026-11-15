# The corrected criterion on the original W modules

## Abstract

The binomial and complete no-carry criteria hold on actual dual symmetric powers with the original relative ideal.

Let K and W be types in universe zero, K a field of prime characteristic p, and W a finite-dimensional K-vector space of finrank two. Let E, in an independent universe, be a finite nontrivial additive commutative group of exponent p, and let rho be a faithful representation of Multiplicative E on W. Set q=card E. Faithful means that rho is injective.

For every positive i, V_i is the ordinary dual of the actual quotient SymmetricPower K (Fin (i-1)) W, with its induced contragredient action. Set i=pa+u, j=pb+v, t=min(u,v), with i,j positive, u,v<p, u+v<=p and i+j<=q. M is the literal direct sum over r in Fin(q/p) of V_(p(r+1)), S is the literal direct sum over ell in Fin t of V_(i+j-(2ell+1)), and T is V_i tensor V_j. All these indices are proved positive; when t=0 the sum S is literally empty.

RelativeStableIso is the imported original relative relation. Its error maps factor through an actual equivariant retract P of X tensor M; P and X are unrestricted objects of the original representation category. They are not assumed finite-dimensional. No alternative PHom ideal, coordinate hypothesis or desired transport premise is introduced.

**Theorem 1.1 (The exact high-binomial condition).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all parameters and actions with exactly the assumptions above, RelativeStableIso M S T holds if and only if u=0 or v=0 or choose(a+b,a), cast into K, is nonzero. The relation on the left is expressed entirely in the original W modules and contains no alpha. K need not be finite. The positivity and total-index bound imply i<q and j<q without additional hypotheses.

The full normal-form and genuine symmetric-power construction supplies one injective alpha for all degrees. Componentwise equivalences on the literal direct sums give M and S, and the actual tensor product of the coordinate changes gives T. Generator transport retains exactly the same P and X, conjugating the retract maps by id_X tensor the generator equivalence. Conjugating the two stable inverse errors yields the original relative relation on either side. The already proved arbitrary-embedding polynomial criterion then supplies the displayed arithmetic condition.

**Theorem 1.2 (The complete no-carry union).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion_no_carry`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion_no_carry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same parameters and the same actual M,S,T, RelativeStableIso M S T holds if and only if u=0 or v=0 or, for every k in Finset.Ico 1 (Nat.log p (a+b)+1), a mod p^k+b mod p^k<p^k. The interval tests the integers from 1 through Nat.log p (a+b); this checks every base-p carry in adding a and b. It is equivalent to the high-binomial condition, not a separate classification.

Both zero-residue branches, p=2, u+v=p and equality i+j=q are retained. There is no factorial exclusion, low-degree restriction, assumed triangular basis or assumed representation equivalence. Sym^0 appears at V_1 only; no identification with V_0 is used.

Elmer--Kadr arXiv:2510.07939v1, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(a), is already refuted by the earlier finite-field counterexample. This delivery transports the corrected binomial classification to the actual original W setting. It does not claim a proof of the false unconditional assertion, novelty, priority, or completion of the separate reflection assertion 3.7(b). The three modules together carry the constructed normal form, actual quotient coordinates and their consumed relative transport.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification.originalW_relative_criterion_no_carry`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification](EmbeddedOriginalClassification.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation](SymmetricPowerTranslation.md)
