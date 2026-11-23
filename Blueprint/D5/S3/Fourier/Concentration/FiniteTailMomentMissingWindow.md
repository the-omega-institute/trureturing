# Missing Windows from Finite Tail Moments

## Abstract

Bounded-degree exclusion of exact relations controls a finite sine score on a closed window.

**Theorem 1.1 (A power-moment grid budget for the original time orbit).**

$$\begin{aligned}V=\sum_{j \in J} \operatorname{w}\left(j\right)^{2},\quad B=\sum_{j \in J} \operatorname{w}\left(j\right) \cdot \left|\operatorname{g}\left(j\right)\right|,\quad N=\left\lfloor\frac{H}{h}\right\rfloor_{+}+1\\\forall j \in J, \operatorname{w}\left(j\right)\ge0,\quad p>0,\quad h>0,\quad \delta>0\\\forall k: J\to\mathbb{Z},\quad \sum_{j \in J} \left|\operatorname{k}\left(j\right)\right|\le2 \cdot p\quad \land\quad \sum_{j \in J} \operatorname{k}\left(j\right) \cdot \operatorname{g}\left(j\right)=0\quad \longrightarrow\quad k=0\\(V=0\quad \lor\quad N \cdot (\frac{2 \cdot p \cdot V}{\delta^{2}})^{p}<1)\\\longrightarrow\quad \forall A \in \mathbb{R},\quad \exists a>A,\quad \forall t \in [a,a + H],\quad \sum_{j \in J} \operatorname{w}\left(j\right) \cdot \operatorname{sin}\left(\operatorname{g}\left(j\right) \cdot t\right)<\delta + h \cdot B\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow.exists_arbitrarily_late_tail_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Youness Lamzouri (2024). *An effective Linear Independence Conjecture for the zeros of the Riemann zeta function and applications*. DOI: [10.48550/arXiv.2311.04860](https://doi.org/10.48550/arXiv.2311.04860). URL: <https://arxiv.org/html/2311.04860v2>.

*Commentary.*

Let J be a finite index type, let g and w be real-valued, and let each weight be nonnegative. The frequencies need no nonzero lower bound on the size of their frequency combinations. Only combinations of coefficient length at most 2p must avoid zero unless all coefficients vanish. Both h and the threshold δ are positive, and p is a positive integer.

The imaginary part of Z(t) = Σ wⱼ exp(i gⱼ t) is the sine score. Expand the pth powers of Z and its conjugate by the multinomial theorem. Two degree-p count vectors produce an integer difference with length at most 2p. The normalized long-time integral of each nonzero character tends to zero by its explicit antiderivative. Thus only equal count vectors survive in the average of |Z|^(2p). A fixed offset of the averaging variable has the same limit. This is the real-time, finite-degree counterpart of the Fourier coefficient extraction in ExpSumCoeffEqZeroOfVanishing.lean in the comparison repository and the signed-frequency expansion in Lamzouri, Lemma 3.2.

Each diagonal term has the square of its multinomial coefficient. Bounding one of the factors by p! ≤ p^p and summing the remaining multinomial terms bounds the limit by (pV)^p. Sum the nonnegative moments over all grid offsets and take the average above A. If every candidate start had a bad grid point, its sum would be at least δ^(2p). The strict budget rules this out. The same start works at all grid nodes.

The floor mesh covers the closed interval, including its right endpoint. Moving by at most h changes the sine score by at most hB. At zero variance the score vanishes, and when H is negative the interval is empty. An arbitrary head can contribute no more than its total weight. The arithmetic relation hypothesis for a tail of actual ζ ordinates remains open.

`D5/S3/Fourier/Concentration/FiniteSineMissingWindow`

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteTailMomentMissingWindow.exists_arbitrarily_late_tail_window`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSineMissingWindow](FiniteSineMissingWindow.md)
- Narrative reference: [D5/S3/Fourier/Concentration/FiniteSineMissingWindow](FiniteSineMissingWindow.md)
