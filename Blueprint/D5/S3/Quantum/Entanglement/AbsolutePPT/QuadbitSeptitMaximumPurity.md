# Four-by-seven APPT maximum purity

## Abstract

The maximum purity of a literal four-by-seven APPT density matrix is 1/25.

**Definition 1.1 (Literal density-matrix extremum).**

$$claim\iff ((\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{1}{25})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{1}{25})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(7\right)))\mapsto if(i=(0,0))then\frac{3}{30}else\frac{1}{30})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{1}{25})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

The matrices are complex matrices on Fin 4 times Fin 7. Positive semidefiniteness and complex trace one define the density assumption. APPT quantifies over every global unitary, with partial transpose on the second local factor. The claim combines the universal purity upper bound, the supremum of all attainable real trace-squares, and the explicit diagonal attainer with entry 3/30 at (0,0) and entry 1/30 at every other coordinate. It includes all density matrices, including those with repeated or zero eigenvalues, and makes no assertion about all equality cases.

**Theorem 1.2 (Sharp four-by-seven APPT purity).**

$$(\forall (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),((((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right)))\Rightarrow (re\left(trace\left(rho\cdot rho\right)\right)\leq \frac{1}{25})))\land (sSup\left(\{p:\mathbb{R}\mid \exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),(((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=p))\}\right)=\frac{1}{25})\land (\exists (rho:Matrix\left((Fin\left(4\right)\times Fin\left(7\right)), (Fin\left(4\right)\times Fin\left(7\right)), \mathbb{C}\right)),((rho=diagonal\left((fun(i:(Fin\left(4\right)\times Fin\left(7\right)))\mapsto if(i=(0,0))then\frac{3}{30}else\frac{1}{30})\right))\land (((PosSemidef\left(rho\right))\land (trace\left(rho\right)=1))\land (APPT\left(rho\right))\land (re\left(trace\left(rho\cdot rho\right)\right)=\frac{1}{25}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

Every literal four-by-seven APPT density has Re trace(rho*rho)<=1/25. The set of all such purities has real supremum 1/25, attained by diagonal (3,1^27)/30. The upper bound uses QuadbitQuintitMaximumPurity.diagonal_spectral_reduction to obtain one antitone, nonnegative, mass-one spectrum l and APPT of its labelled diagonal. Both diagonal_necessary_both and UniformRankFourNecessary.uniform_rank_four_necessary take this exact same labelling e, spectrum l and APPT diagonal. Thus K1 and K2 at [l0,l1,l2,l22,l23,l24,l25,l26,l27] are positive semidefinite, while the sum of l0 through l5 is at most the sum of l18 through l27. The terminal sum minus the initial sum is exactly RankFourLength28Purity.L4 l. Applying RankFourLength28Purity.purity_bound bounds the spectral square sum; the retained trace-square equality returns the bound for the original physical matrix. The necessary mass inequality is used together with both pencils; the pencils alone are not substituted for this stronger hypothesis.

For attainment, the existing arbitrary-dimension normalized_ray gives (I+2|v><v|)/(mn+2) for every unit vector v. At m=4,n=7 and v=|00>, normalized_basis_diagonal identifies it with the prescribed diagonal. Its trace-square is (28+8)/(28+2)^2=1/25. Positivity, trace one and APPT come from that same ray theorem: every global unitary sends v to a unit vector, for which the numerator is separable. The attained value proves nonemptiness of the purity set and supplies the lower bound in the supremum equality.

The finite-complement Bell construction, normalized ray and length-28 rational identity are used at their existing interfaces. The new connection is that both necessary spectral tests apply to one actual diagonal of the physical state. Hildebrand's Positive partial transpose from spectra, Phys. Rev. A 76, 052325 (2007), provides the spectral-test setting. This result concerns local dimensions four and seven; it does not establish the full APPT purity conjecture or a result in local dimensions five and five.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSeptitMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity](QuadbitQuintitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity](RankFourLength28Purity.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary](UniformRankFourNecessary.md)
