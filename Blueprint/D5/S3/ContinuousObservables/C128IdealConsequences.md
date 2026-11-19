# The Whole Selfadjoint Ideal, Local Sections and Nonunitality

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

Use Y=[0,1], U=(0,1/4) minus all 1/n for natural n at least 5, M=CStarMatrix (Fin 2) (Fin 2) Complex with its operator norm, A=the whole C0(U,M), and X=the whole selfadjoint part of C(Y,M). I is the real submodule of every selfadjoint field vanishing off U. The real linear isometry equivalence j restricts I onto the whole selfadjoint part of A; its inverse is zero extension.

I is closed: it is the inverse image of the closed whole complex ideal under the continuous subtype map. S(a,b)=(ab+ba)/2 is the original real Jordan product. Define the original oriented operation D(a,b)=i(ab-ba)/2. Star reverses products and conjugates i to -i, so both S and D are selfadjoint. At every point outside U an ideal factor is zero, so S(X,I) is contained in I and D(I,I) is contained in I.

$$
(\operatorname{IsClosed}(I)) \land (\forall (a: X), \forall (r: I), \operatorname{S}(a, r)\in I) \land (\forall (r: I), \forall (s: I), \operatorname{D}(r, s)\in I) \land (\forall (r: I), \forall (t: U), \operatorname{j}(r, t)=\operatorname{r}(\operatorname{inc}(t))) \land (\forall (r: I), \forall (s: I), \operatorname{j}(\operatorname{S}(r, s))=\operatorname{Jordan}(\operatorname{j}(r), \operatorname{j}(s))) \land (\forall (r: I), \forall (s: I), \operatorname{j}(\operatorname{D}(r, s))=\operatorname{Oriented}(\operatorname{j}(r), \operatorname{j}(s)))
$$

Here Jordan(p,q)=(pq+qp)/2 and Oriented(p,q)=i(pq-qp)/2 in A, with exactly this commutator orientation. For r in I and t in U, j(r)(t)=r(inc(t)). Applying this evaluation identity to each summand and product gives both displayed correspondence identities by extensionality on every point of U. The closure laws make both restricted operations well-defined on I. For every r in I and selfadjoint p in A, j inverse(j(r))=r and j(j inverse(p))=p; both j and its inverse preserve the norm.

Applying j inverse to genuine selfadjoint local identity sections gives the ambient Jordan annihilator criterion and a nonzero element of I. This does not prove polynomial-plus-ideal completeness, its all-input S/D closure, noncommuting seeds, the full original model, or physical realization.

## References

- Truth anchor: `D5/S3/ContinuousObservables/C128IdealConsequences.annihilator_iff`
- Truth anchor: `D5/S3/ContinuousObservables/C128IdealConsequences.nonzero_nonunital`
- Dependency: [D5/S3/ContinuousObservables/C128ZeroExtension](C128ZeroExtension.md)
