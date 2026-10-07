---
bibkey: gohlke2023measure
authors: "P. Gohlke; A. Mitchell; D. Rust; T. Samuel"
year: 2023
title: "Measure Theoretic Entropy of Random Substitution Subshifts"
doi: "10.1007/s00023-022-01212-x"
url: "https://link.springer.com/article/10.1007/s00023-022-01212-x"
claim: "Example 5.3 gives the scalar entropy -(p log p + (1-p) log(1-p))/(2-p), maximised at the inverse golden ratio with value log of the golden ratio, for a different constant-length random substitution."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Scalar entropy extremum supplier

The primary publisher article is in Annales Henri Poincaré 24, 277–323.
Example 5.3 in §5 defines the random substitution

$$
a\mapsto\begin{cases}aa&\text{with probability }p,\\ab&\text{with probability }1-p,\end{cases}
\qquad b\mapsto ba,\qquad 0<p<1.
$$

For its frequency measure $\mu_p$, the example uses Theorem 3.5 to give

$$
h(\mu_p)=-\frac{p\log p+(1-p)\log(1-p)}{2-p}.
$$

It states that the maximum occurs at $p=\tau^{-1}$, where $\tau$ is the golden
ratio, and the value is $\log\tau\approx0.481212$. This numerical value fixes
the natural-log unit. In bits the scalar function is $h_2(p)/(2-p)$ and the
maximum is $\log_2\tau$; the conversion divides the displayed entropy by
$\ln2$. The scalar extremum is `literature-attested`.

[The single-lineage partition volume](../../docs/develop/theory/AURIC_FIB_SINGLE_LINEAGE_PARTITION_GEOMETRY.md)
§7.4 consumes precisely this scalar precedent and proves its connection to
the FIB geometry, including the strict equality condition. The deterministic
rule $\alpha\mapsto\beta$, $\beta\mapsto\langle\beta,\alpha\rangle$ is not the
random substitution of Example 5.3. Its uniform-root-position reference is
not identified with the example's frequency measure.

The example further gives a larger topological entropy and states that the
golden frequency measure is not a measure of maximal entropy for that
subshift. Neither its topological entropy nor a maximal-measure assertion
is transferred to the partition model. The source is not Example 5.4's
random Fibonacci substitution.
