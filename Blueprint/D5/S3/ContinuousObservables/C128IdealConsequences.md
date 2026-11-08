# Whole-Ideal Local Sections and Nonunitality

## Abstract

Local sections of the whole ideal prove nonunitality and detect ambient Jordan annihilation.

**Theorem 1.1 (The algebra is nonzero and genuinely nonunital).**

$$(\exists r: I, r\neq 0) \land (\exists f: A, f\neq 0) \land (\neg \exists e: A, \forall (f: A), (ef=f) \land (fe=f))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/C128IdealConsequences.nonzero_nonunital` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is the whole complex C0 algebra on U=(0,1/4) minus every 1/n for n at least 5, with the genuine two by two matrix operator norm. The whole selfadjoint ideal I has a nonzero element, A has a nonzero element, and no element is a left and right multiplicative identity on all of A.

Compactly supported local unit sections exist at every point of U. Symmetrizing one gives a selfadjoint section whose value there is the full matrix identity. A two-sided unit would therefore equal the identity at every point of U. The points 1/4-1/(40(n+1)) all lie in U and approach 1/4. Continuity of the whole zero extension then forces its value at 1/4 to be both zero and the matrix identity, a contradiction.

**Theorem 1.2 (Whole-ideal annihilation is pointwise vanishing).**

$$\forall (a: X), (\forall (r: I), \operatorname{S}(a, r)=0)\iff \forall (t: U), \operatorname{a}(\operatorname{inc}(t))=0$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/C128IdealConsequences.annihilator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is the whole selfadjoint continuous matrix field space on [0,1], I is its entire zero-off-U selfadjoint ideal, S(a,r)=(ar+ra)/2, and inc includes U in [0,1]. For every a in X, annihilating every element of I under S is equivalent to vanishing at every point of U.

The inverse of the onto real linear isometry j carries each selfadjoint local identity section into the whole ideal I. Evaluating S(a,r)=0 at that point gives a=0 there. Conversely the product is zero on U because a vanishes there, and off U because every ideal field vanishes there. This establishes the ambient pointwise criterion; identifying the closure of U with [0,1/4] and the original polynomial-domain annihilator requires further arguments.

## References

- Truth anchor: `D5/S3/ContinuousObservables/C128IdealConsequences.annihilator_iff`
- Truth anchor: `D5/S3/ContinuousObservables/C128IdealConsequences.nonzero_nonunital`
- Dependency: [D5/S3/ContinuousObservables/C128IdealJordan](C128IdealJordan.md)
