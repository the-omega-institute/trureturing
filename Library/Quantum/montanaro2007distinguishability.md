---
bibkey: montanaro2007distinguishability
authors: Ashley Montanaro
year: 2007
title: On the Distinguishability of Random Quantum States
doi: 10.1007/s00220-007-0221-7
claim: The coordinatewise square-root Gram bound in Section 2.2, equation (8), bounds each pure-state square-root-measurement error by its squared-overlap row sum divided by one plus that row sum.
strata_touched: []
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Quantum/montanaro2007distinguishability -->

# On the Distinguishability of Random Quantum States

The published article appears in *Communications in Mathematical Physics* 273,
619–636. Its [public preprint](https://arxiv.org/abs/quant-ph/0607011), Section 2.2,
equation (8), PDF page 5, gives the coordinatewise inequality

$$
\bigl((\sqrt G)_{ii}\bigr)^2
\ge \frac{G_{ii}^3}{\sum_j|G_{ij}|^2}.
$$

This inequality precedes the paper's sum over ensemble labels. For a family of
$d$ normalized pure record states with unit-diagonal Gram matrix $H$, take the
uniformly weighted Gram matrix $G=H/d$. If
$r_i=\sum_{j\ne i}|H_{ij}|^2$, the square-root measurement has conditional
success probability $((\sqrt H)_{ii})^2\ge(1+r_i)^{-1}$, hence conditional
error at most $r_i/(1+r_i)$. This is a bound for every label; it does not require
the actual input labels to have a uniform prior.

The formula is used on the support of the signal ensemble and does not require
an invertible Gram matrix. Completing the measurement outside that support has
no effect on its probabilities on the record states.

The source anchors this decoding inequality. It is not an attribution of an
adaptive quantum-history comparison, a product bound for instrument errors, or
a record-storage budget to this paper. No Lean declaration is attributed to the
note.
