# Dedekind Family Split

## Abstract

The oriented Dedekind ledger splits into its alternating walk and endpoint translation.

**Theorem 1.1 (The oriented ledger splits into walk and translation).**

$$\forall a\in \operatorname{List}(\mathbb{Z}),\ \forall phi, psi\in \mathbb{Q},\ \forall u, v, c, t\in \mathbb{Z},\ c\neq 0, phi=3+[\operatorname{alt}(a)]_{\mathbb{Q}}+\frac{[u-v]_{\mathbb{Q}}}{[c]_{\mathbb{Q}}}, psi=phi-3, u-v=ct \Rightarrow psi=[\operatorname{alt}(a)]_{\mathbb{Q}}+[t]_{\mathbb{Q}}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindFamilySplit.dedekind_family_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here alt(a) is the alternating integer walk of the coefficient list. The endpoint hypothesis identifies the rational correction with the integer translation, and psi = phi - 3 removes the constant term.

This is a deeper-clause continuation for the oriented family-split identity only; the empirical enumeration and asymptotic clauses remain open.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindFamilySplit.dedekind_family_split`
- Dependency: [D5/S1/Phase/WalkFormula](../WalkFormula.md)
