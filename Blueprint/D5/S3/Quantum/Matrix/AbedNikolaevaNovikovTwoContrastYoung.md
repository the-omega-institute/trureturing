# The exact two-contrast Young envelope

## Abstract

The exact relative Young violation with prescribed density and modulus contrasts in every positive even dimension.

**Definition 1.1 (Operator Michelson contrast).**

$$\forall n: \mathbb{N}, \forall T: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{contrast}\left(T\right) = \frac{\operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, T\right)\right) - \operatorname{sInf}\left(\operatorname{spectrum}\left(\mathbb{R}, T\right)\right)}{\operatorname{sSup}\left(\operatorname{spectrum}\left(\mathbb{R}, T\right)\right) + \operatorname{sInf}\left(\operatorname{spectrum}\left(\mathbb{R}, T\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.contrast` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Section 3.2, page 8: “For a positive invertible operator T on a Hilbert space with m = min σ(T), M = max σ(T) let” followed by OMC(T) = tanh OLC(T) = (M − m)/(M + m). The real spectral extrema are sInf and sSup. Only nonzero positive semidefinite matrices enter the value set; the same fraction includes a zero minimum eigenvalue.

**Definition 1.2 (Relative violations for actual triples).**

$$\forall n: \mathbb{N}, \forall delta: \mathbb{R}, \forall eta: \mathbb{R}, \operatorname{values}\left(n, delta, eta\right) = \{v: \mathbb{R} \mid \exists rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \exists A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \exists B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{Matrix}.\operatorname{PosDef}(rho)) \land ((A \ne 0) \land ((B \ne 0) \land ((\operatorname{contrast}\left(rho\right) = delta) \land ((\operatorname{contrast}\left(\operatorname{CFC}.\operatorname{abs}(A)\right) = eta) \land ((\operatorname{contrast}\left(\operatorname{CFC}.\operatorname{abs}(B)\right) = eta) \land ((0 < \frac{\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(A) \cdot A))) + \operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(B) \cdot B)))}{2}) \land (v = \frac{\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot \operatorname{CFC}.\operatorname{abs}(A \cdot \operatorname{Matrix}.\operatorname{conjTranspose}(B)))) - \frac{\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(A) \cdot A))) + \operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(B) \cdot B)))}{2}}{\frac{\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(A) \cdot A))) + \operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(rho \cdot (\operatorname{Matrix}.\operatorname{conjTranspose}(B) \cdot B)))}{2}})))))))\}$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.values` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Section 3.8, page 12: “The envelope Vₙ(δ) lets the operator variables range over all operators. To see how the violation depends on the operators themselves, we also prescribe their contrast. For a positive variable A we use OMC(A), for an arbitrary or self-adjoint variable X the contrast OMC(|X|) of its modulus (for the Peierls–Bogoliubov inequality, item 16, the variables are positive, as in [14]), and we let every operator variable of an item have the same contrast δ′ ∈ [0, 1]:” The displayed set is the set inside that supremum for Table 3, item 8. Here delta is δ, eta is δ′, and rho is ρ. Matrices A and B are arbitrary, nonzero, and independently oriented. The modulus is CFC.abs X = CFC.sqrt (star X * X). The functional is (rho * X).trace; Complex.re selects its real value on positive semidefinite arguments. The normalizer is the positive average of the two weighted Gram traces. No trace-one condition is imposed on rho.

**Definition 1.3 (The conjectured envelope).**

$$claim = (\forall r: \mathbb{N}, (1 \le r) \Rightarrow (\forall delta: \mathbb{R}, (0 \le delta) \Rightarrow ((delta < 1) \Rightarrow (\forall eta: \mathbb{R}, (0 \le eta) \Rightarrow ((eta \le 1) \Rightarrow ((\operatorname{Set}.\operatorname{Nonempty}(\operatorname{values}\left(2 \cdot r, delta, eta\right))) \land ((\operatorname{BddAbove}\left(\operatorname{values}\left(2 \cdot r, delta, eta\right)\right)) \land (\operatorname{sSup}\left(\operatorname{values}\left(2 \cdot r, delta, eta\right)\right) = \frac{4 \cdot delta \cdot eta}{1 + eta^{2} - 2 \cdot delta \cdot eta}))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.claim` (`✓ std3`).

*Citation.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Conjecture 11.1, final clause, page 57: “and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.” Write n = 2r with r ≥ 1. The parameters delta and eta denote the source's δ and δ′. Nonemptiness and boundedness are conclusions, so the real supremum represents a nonempty bounded set. The endpoints delta = 0, eta = 0 and eta = 1 are included.

**Theorem 1.4 (The exact envelope in every positive even dimension).**

$$\forall r: \mathbb{N}, (1 \le r) \Rightarrow (\forall delta: \mathbb{R}, (0 \le delta) \Rightarrow ((delta < 1) \Rightarrow (\forall eta: \mathbb{R}, (0 \le eta) \Rightarrow ((eta \le 1) \Rightarrow ((\operatorname{Set}.\operatorname{Nonempty}(\operatorname{values}\left(2 \cdot r, delta, eta\right))) \land ((\operatorname{BddAbove}\left(\operatorname{values}\left(2 \cdot r, delta, eta\right)\right)) \land (\operatorname{sSup}\left(\operatorname{values}\left(2 \cdot r, delta, eta\right)\right) = \frac{4 \cdot delta \cdot eta}{1 + eta^{2} - 2 \cdot delta \cdot eta})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

Four nonnegative trace products of endpoint gaps give a sharp common-trace interval comparison. Applied to the actual Gram orbits, it bounds the weighted Young expression in every nonempty finite dimension. A unitary polar factor follows from singular value decomposition, including singular matrices. In dimension 2r the density with repeated eigenvalues k and 1 and the repeated off-diagonal input with entries 1 and ell attain the bound, where k = (1 + delta)/(1 - delta) and ell = (1 - eta)/(1 + eta). This is the direct-sum construction of Proposition 5.22. The denominator is (1 - eta)² + 2 eta (1 - delta), which is strictly positive on the stated domain. Evenness is needed only for attainment. No sharp interior odd-dimensional envelope or singular-density extension is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.contrast`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.result`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung.values`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](AlternativeMeanLinearization.md)
