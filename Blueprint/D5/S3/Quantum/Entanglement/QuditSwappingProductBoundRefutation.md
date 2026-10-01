# A four-dimensional counterexample to the improved swapping bound

## Abstract

The improved product bound for entanglement swapping conjectured by Starke, Basso, Celeri and Maziero fails for two identical partially entangled ququarts: the average is 723/625, whereas the proposed bound is 507/625.

**Definition 1.1 (Bell phase).**

$$\forall d : \mathbb{N}, \operatorname{omega}\left(d\right) = \operatorname{exp}\left((\frac{2 \cdot \pi}{(d : \mathbb{R})} : \mathbb{C}) \cdot i\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.omega` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

The generalized Bell basis uses omega = exp(2 pi i / d). The imaginary unit is i; the natural dimension is cast to a real number in the quotient.

**Definition 1.2 (Unnormalized conditional state).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall c : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall b : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall p : \operatorname{ZMod}\left(d\right), \forall q : \operatorname{ZMod}\left(d\right), \forall x : (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), \operatorname{phi}\left(d, c, b, p, q, x\right) = \frac{1}{(\sqrt{(d : \mathbb{R})} : \mathbb{C})} \cdot (\sum_{k \in \operatorname{ZMod}\left(d\right)} c\left(p + k\right) \cdot b\left(k\right) \cdot \operatorname{star}\left(\operatorname{omega}\left(d\right)\right)^{\operatorname{val}\left(q\right) \cdot \operatorname{val}\left(k\right)} \cdot \operatorname{ite}\left(x = (p + k, k), 1, 0\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.phi` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Page 5, Eq. (30): `\ket{\phi_{pq}^{AB}} = \frac{1}{\sqrt{d}}\sum_{k=0}^{d-1}c_{p\oplus k} d_k \bar{\omega}^{qk}|p\oplus k,k\rangle`. The paper's d_k is renamed b_k. Indices are ZMod d, p plus k is addition modulo d, and val selects the representative in 0,...,d-1 for the natural exponent. The ket is its computational-basis delta function: ite(P,a,b) is a if P holds and b otherwise. All real scalars in complex arithmetic are cast to C. Translation k to p+k is a bijection, so the post-measurement state is in Schmidt form with sigma(k)=p+k.

**Definition 1.3 (Hilbert norm).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall v : ((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)) \to \mathbb{C}), \operatorname{stateNorm}\left(d, v\right) = \sqrt{\sum_{x \in (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right))} \left\lVert v\left(x\right) \right\rVert^{2}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.stateNorm` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

In the orthonormal computational basis ZMod d times ZMod d, the Hilbert norm is the square root of the sum of squared coordinate moduli. This is the norm used to normalize each conditional state.

**Definition 1.4 (Bell-outcome probability).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall c : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall b : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall p : \operatorname{ZMod}\left(d\right), \forall q : \operatorname{ZMod}\left(d\right), \operatorname{prob}\left(d, c, b, p, q\right) = \operatorname{stateNorm}\left(d, \operatorname{phi}\left(d, c, b, p, q\right)\right)^{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.prob` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Page 5, Eq. (31): `\left\Vert\ket{\phi_{pq}^{AB}}\right\Vert^2 = \frac{1}{d}\sum_{k=0}^{d-1}|c_{p\oplus k}|^2 |d_k|^2 = \Pr\big(\Phi_{pq}^{CC'}\big)`. The definition is the squared Hilbert norm of the conditional state, with d_k renamed b_k.

**Definition 1.5 (Entanglement in Schmidt form).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall a : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \operatorname{El1}\left(d, a\right) = \sum_{j \in \operatorname{ZMod}\left(d\right)} \sum_{k \in \operatorname{ZMod}\left(d\right)} \operatorname{ite}\left(j = k, 0, \left\lVert a\left(j\right) \cdot a\left(k\right) \right\rVert\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.El1` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Page 4, Eq. (24): `E_{l_1}(|\xi\rangle_{AC}) = \sum_{j\ne k}|c_j c_k|`. For a normalized state in Schmidt form sum_k a_k |sigma(k),k>, with sigma a bijection, this is the sum over ordered pairs of distinct indices of the modulus of a_j a_k. No division by d-1 is included in El1.

**Definition 1.6 (Average post-measurement entanglement).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall c : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall b : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \operatorname{averageEl1}\left(d, c, b\right) = \sum_{p \in \operatorname{ZMod}\left(d\right)} \sum_{q \in \operatorname{ZMod}\left(d\right)} \operatorname{ite}\left(\operatorname{prob}\left(d, c, b, p, q\right) = 0, 0, \operatorname{prob}\left(d, c, b, p, q\right) \cdot \operatorname{El1}\left(d, (k : \operatorname{ZMod}\left(d\right) \mapsto \frac{\operatorname{phi}\left(d, c, b, p, q, (p + k, k)\right)}{(\operatorname{stateNorm}\left(d, \operatorname{phi}\left(d, c, b, p, q\right)\right) : \mathbb{C})})\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.averageEl1` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Page 5, Eq. (41): `\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle = \sum_{p,q = 0}^{d-1} \Pr\big(\Phi_{pq}^{CC'}\big) E_{l_1}\big( |\hat{\phi}_{pq}^{AB} \rangle \big)`. Each conditional state is divided by its Hilbert norm. Its Schmidt coefficients are the coordinates at (p+k,k); zero-probability outcomes contribute zero. The sum includes all d squared Bell outcomes.

**Definition 1.7 (The improved upper-bound conjecture).**

$$claim \Leftrightarrow (\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall c : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), \forall b : (\operatorname{ZMod}\left(d\right) \to \mathbb{C}), (2 \le d) \Rightarrow \left((\sum_{j \in \operatorname{ZMod}\left(d\right)} \left\lVert c\left(j\right) \right\rVert^{2} = 1) \Rightarrow \left((\sum_{k \in \operatorname{ZMod}\left(d\right)} \left\lVert b\left(k\right) \right\rVert^{2} = 1) \Rightarrow \operatorname{averageEl1}\left(d, c, b\right) \le \frac{\operatorname{El1}\left(d, c\right) \cdot \operatorname{El1}\left(d, b\right)}{(d : \mathbb{R}) - 1}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.claim` (`✓ std3`).

*Citation.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Page 8, Eq. (59), verbatim (the source formula is quoted in TeX): "Therefore, we conjecture that the improved upper bound has the form `\big\langle E_{l_1}\big(|\hat{\phi}_{pq}^{AB} \rangle\big) \big\rangle \le \frac{E_{l_1}(|\xi\rangle_{AC}) E_{l_1}(|\eta\rangle_{C'B})}{d-1}.`" The quantified encoding ranges over every dimension d at least 2 and every pair c,b of normalized complex coefficient vectors. NeZero d supplies the finite ZMod d index type and follows from d at least 2. The paper's second vector d_k is b_k. The denominator is real d minus 1.

**Theorem 1.8 (The bound fails in dimension four).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Diego S. Starke; Marcos L. W. Basso; Lucas C. Céleri; Jonas Maziero (2025). *Entanglement swapping for partially entangled qudits and the role of quantum complementarity*. DOI: [10.48550/arXiv.2508.00813](https://doi.org/10.48550/arXiv.2508.00813). URL: <https://arxiv.org/abs/2508.00813v2>.

*Commentary.*

Take d=4 and c=b=(7/10,1/10,7/10,1/10). Both sums of squared moduli are 1 and both El1 values are 39/25. For arbitrary positive dimension, the phase has modulus 1 and the weighted entanglement of an outcome is (1/d) times the ordered off-diagonal sum of |c_(p+j)c_(p+k)b_j b_k|. In the zero-probability case, every supported coefficient vanishes; otherwise the squared normalizing factor cancels the probability. Summing over q removes the factor 1/d. Evaluating the resulting correlation sum at these inputs gives 723/625, strictly greater than (39/25)^2/3=507/625.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.El1`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.averageEl1`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.omega`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.phi`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.prob`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.stateNorm`
