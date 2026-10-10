# Three-outcome permutationally invariant Bell inequalities

## Abstract

Five three-outcome PI Bell inequalities hold for every party count.

**Definition 1.1 (One-party PI observable).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \forall (a : \operatorname{Fin}(3)), \forall (x : \operatorname{Fin}(2)), \operatorname{P1}(w, p, a, x) = \sum_{l : L} (w(l) \cdot \sum_{i : \operatorname{Fin}(N)} (p(l, i, x, a)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.P1` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Section II, Eq. (3), p. 2: the one-party observable sums the marginal probability over all parties. There are N parties, two inputs and three outcomes. L is the finite hidden-variable type; w is its weight and p(l,i,x,a) is the local response. Outcome indices precede input indices in P1. All quantities are real.

**Definition 1.2 (Two-party PI observable).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \forall (a : \operatorname{Fin}(3)), \forall (b : \operatorname{Fin}(3)), \forall (x : \operatorname{Fin}(2)), \forall (y : \operatorname{Fin}(2)), \operatorname{P2}(w, p, a, b, x, y) = \sum_{l : L} (w(l) \cdot \sum_{i : \operatorname{Fin}(N)} (\sum_{(j : \operatorname{Fin}(N)) \in \operatorname{Finset}.\operatorname{erase}(\operatorname{Finset}.\operatorname{univ}, i)} (p(l, i, x, a) \cdot p(l, j, y, b))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.P2` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Section II, Eq. (3), p. 2: the two-party observable sums over ordered pairs of distinct parties. The erased univ excludes i from the inner sum; no factor of one half is present. The response product belongs to the same hidden variable l. P2 takes its two outcomes before its two inputs.

**Definition 1.3 (First symmetrized observable).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \operatorname{Pt0}(w, p) = \operatorname{P1}(w, p, 0, 0) + \operatorname{P1}(w, p, 0, 1) + \operatorname{P1}(w, p, 1, 0) + \operatorname{P1}(w, p, 1, 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt0` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (19), p. 5: Pt0 is the source's tilde P0.

**Definition 1.4 (Equal outcomes at equal inputs).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \operatorname{Pt00}(w, p) = \operatorname{P2}(w, p, 0, 0, 0, 0) + \operatorname{P2}(w, p, 0, 0, 1, 1) + \operatorname{P2}(w, p, 1, 1, 0, 0) + \operatorname{P2}(w, p, 1, 1, 1, 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt00` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (19), p. 5: Pt00 is the source's tilde P00.

**Definition 1.5 (Different outcomes at different inputs).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \operatorname{Pt01}(w, p) = \operatorname{P2}(w, p, 0, 1, 0, 1) + \operatorname{P2}(w, p, 1, 0, 0, 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt01` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (19), p. 5: Pt01 is the source's tilde P01.

**Definition 1.6 (Equal outcomes at different inputs).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \operatorname{Pt10}(w, p) = \operatorname{P2}(w, p, 0, 0, 0, 1) + \operatorname{P2}(w, p, 1, 1, 0, 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt10` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (19), p. 5: Pt10 is the source's tilde P10.

**Definition 1.7 (Different outcomes at equal inputs).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \operatorname{Pt11}(w, p) = \operatorname{P2}(w, p, 0, 1, 0, 0) + \operatorname{P2}(w, p, 0, 1, 1, 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt11` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (19), p. 5: Pt11 is the source's tilde P11.

**Definition 1.8 (Bell expression).**

$$\forall (N : \mathbb{N}), \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), \forall (c : \operatorname{Fin}(6) \to \mathbb{R}), \operatorname{bell}(w, p, c) = c(0) \cdot \operatorname{Pt0}(w, p) + c(1) \cdot \operatorname{Pt00}(w, p) + c(2) \cdot \operatorname{Pt01}(w, p) + c(3) \cdot \operatorname{Pt10}(w, p) + c(4) \cdot \operatorname{Pt11}(w, p) + c(5)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.bell` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Equation (20), p. 5: the five coefficients multiply the five symmetrized observables, and the sixth entry is the additive classical-bound constant. The coefficient function c is indexed from zero.

**Definition 1.9 (The five Table III rows).**

$$\operatorname{table} = ![![1, 1, 0, -2, 0, 0], ![1, 1, -2, -2, 2, 0], ![-2, 1, 2, 2, 0, 4], ![-6, 1, 4, 4, 2, 12], ![-6, 1, 4, 0, 0, 24]]$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.table` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Table III, p. 6, lists (alpha1, alpha2, alpha3, alpha4, alpha5, beta_c). Fin 5 numbers the source's rows 1 through 5 as 0 through 4. Each displayed vector is a function Fin 6 to Real, in exactly that coefficient order.

**Definition 1.10 (Validity for arbitrary party number).**

$$\operatorname{claim} \Leftrightarrow \forall (k : \operatorname{Fin}(5)), \forall (N : \mathbb{N}), (3 < N) \Rightarrow \forall (L : \operatorname{Type}), [\operatorname{Fintype}(L)] \forall (w : L \to \mathbb{R}), \forall (p : L \to \operatorname{Fin}(N) \to \operatorname{Fin}(2) \to \operatorname{Fin}(3) \to \mathbb{R}), (\forall (l : L), 0 \le w(l)) \Rightarrow (\sum_{l : L} (w(l)) = 1) \Rightarrow (\forall (l : L), \forall (i : \operatorname{Fin}(N)), \forall (x : \operatorname{Fin}(2)), \forall (a : \operatorname{Fin}(3)), 0 \le p(l, i, x, a)) \Rightarrow (\forall (l : L), \forall (i : \operatorname{Fin}(N)), \forall (x : \operatorname{Fin}(2)), \sum_{a : \operatorname{Fin}(3)} (p(l, i, x, a)) = 1) \Rightarrow 0 \le \operatorname{bell}(w, p, \operatorname{table}(k))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.claim` (`✓ std3`).

*Citation.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Section III.A, p. 5, verbatim: To give a concrete example, we propose for any N > 3 the five 3PIBIs shown in Tab. III. At this point, for each conjectured inequality we have to prove that it is indeed valid for arbitrary number of parties N, or at least for all N larger than a minimum number. The encoding quantifies over each row k and every N > 3, then over every finite hidden-variable type L and every normalized nonnegative w and p. Inputs are Fin 2, outcomes Fin 3 and parties Fin N. The finite-hidden-variable formulation is the finite convex-hull formulation of the local model; no integral representation theorem is asserted. The conclusion is nonnegativity of the literal Table III Bell expression.

**Theorem 1.11 (All five Bell inequalities are valid).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Aloy; G. Müller-Rigat; J. Tura; M. Fadel (2024). *Deriving three-outcome permutationally invariant Bell inequalities*. DOI: [10.3390/e26100816](https://doi.org/10.3390/e26100816). URL: <https://arxiv.org/abs/2406.11792v1>.

*Commentary.*

Every normalized finite local hidden-variable model satisfies all five inequalities. Independent local choices at both inputs give a distribution on deterministic strategies. The one-party and distinct-party two-party moments reproduce the responses, so the Bell expression is their weighted average. At a deterministic strategy, the nine outcome-pair counts give the Table II formulas. Row 2 is a square plus twice the joint count K. Row 3 separates the small marginal-count cases from a sum of squares and nonnegative products. Rows 4 and 5 reduce to a quadratic G on three natural numbers, nonnegative by the cases k = 0, k = 1 and k >= 2. The argument for the finite local model uses no lower bound on N; in particular it applies for every N >= 1. Validity alone asserts neither that these inequalities are facets nor that quantum correlations violate them.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.P1`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.P2`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt0`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt00`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt01`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt10`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.Pt11`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.bell`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell.table`
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](../../Entropy/NamingWindow/GreenClassWindowEntropy.md)
