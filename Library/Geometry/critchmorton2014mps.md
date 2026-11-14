---
bibkey: critchmorton2014mps
authors: Critch, Andrew; Morton, Jason
year: 2014
title: "Algebraic geometry of matrix product states"
doi: 10.3842/SIGMA.2014.095
url: "https://arxiv.org/abs/1210.2812v4"
claim: "The paper studies the varieties of translation-invariant matrix product states with periodic and open boundary conditions, gives defining equations in small cases (among them the quartic hypersurface of open-boundary binary bond-dimension-two MPS on three sites), and states identifiability conjectures, including that each improper marginalization of open-boundary 2x2 binary MPS to three consecutive sites is a birational equivalence (Conjecture 8), and the corresponding three-site reduced-density phase recovery with a no-fewer clause (Conjecture 9)."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality
license: citation-only
triage: anchor
---

# Critch and Morton, Algebraic geometry of matrix product states

A. Critch and J. Morton, SIGMA 10 (2014), 095, DOI 10.3842/SIGMA.2014.095; arXiv:1210.2812v4 (10 September 2014). Quotations are from the arXiv v4 TeX source `sigma14-095.tex`; the author list is from the arXiv metadata.

With open boundary conditions the state is $\Psi=\sum_{i_1,\dots,i_N}b_0^TA_{i_1}\cdots A_{i_N}b_1|i_1\dots i_N\rangle$ for boundary vectors $b_0,b_1\in\mathbb C^D$ and $D\times D$ matrices $A_0,\dots,A_{d-1}$; $\mathrm{OB}(D,d,N)$ is the set of such states and $\overline{\mathrm{OB}}(D,d,N)$ its Zariski closure in $\mathbb C^{d^N}$ (Section 3, l. 344–364). Theorem 7 (l. 378–403) shows that $\overline{\mathrm{OB}}(2,2,3)$ is a quartic hypersurface in $\mathbb C^8$. The improper marginalization maps sum all indices outside three consecutive sites (l. 420–428), and the paper conjectures (l. 430–434):

> For $N\geq 4$, a~generic~$N$-qubit state can be recovered from its improper margina\-li\-zation to any three consecutive states.
> That is, each improper marginalization map $\overline\OB(2,2,N)\to\overline\OB(2,2,3)$ is
> a~birational equivalence of varieties.

Conjecture 9 concerns an actual Hermitian reduced density operator, rather than the coherent sum above:

> A generic N-qubit (D=d=2) translation invariant matrix product state Ψ with open boundary conditions is determined up to phase by a reduced density operator which traces out all but a chain of three adjacent states, but no fewer.

The displayed map immediately following it uses the prefix entries
$Q_k(\psi)_{u,v}=\sum_b\psi_{ub}\overline{\psi_{vb}}$.
On the unnormalized affine cone this is the raw partial trace, retaining the squared-norm scale. A normalized reading must normalize both states. The prefix interpretation does not itself establish a theorem for every interior window.

`OpenBoundaryMPSDensityRecovery.observable_chart_phase_recovery` supplies the conditional bridge: if some $t=Q_3(\psi)v$ lies in the existing coherent chart and the corresponding reconstructed complex linear transfer is injective, every actual free-boundary competitor with the same raw prefix density is a unit phase multiple of $\psi$. Its proof reuses the original three-site gauge reconstruction, without regularity assumptions on the competitor.

`OpenBoundaryMPSDensityGenericity.intrinsic_recovery_genericity` proves the recovery-genericity portion in the literal actual image. Fix the all-zero three-bit word $e$ and $t=Q_3(\psi)e$. Let $N_s(t)$ be the original Cramer matrix numerators, and form the four-entry transfer numerator matrix with entries $\sum_s N_s(t)_{ik}\overline{N_s(t)_{jl}}$. The product of its determinant and the original `chartPoly` is polynomial in independent $t,\overline t$ variables. The existing Cartesian substitution, followed by coefficientwise real and imaginary projections and their sum of squares, gives a polynomial with **real coefficients** whose nonvanishing is exactly the coherent chart condition and injectivity of the canonical transfer. Renaming into the fixed column gives `observedPolynomial` in the real and imaginary entries of $Q_3$; the explicit quadratic `statePolynomial` is its raw-density pullback.

For every natural $m$, `goodStates m` is the nonempty open dense subset of the subtype `openBoundaryMPS(3+m)` on which this observed polynomial does not vanish. Thus for every original length $N\ge4$, every target in this intrinsic principal relative real-algebraic open locus is determined, against **every actual competitor**, by the raw prefix $Q_3$ up to $U(1)$. The density proof pulls the real polynomial back through the original twelve-complex-parameter map and uses a nonzero actual witness, real analytic uniqueness, and continuity of the MPS map. It does not infer openness from a continuous image, replace the actual image by its Zariski closure, or assume genericity of the competitor.

The uniform recovery witness uses the original matrices and boundaries displayed below. Its fixed-density effective boundary is $E^m(rr^\dagger)(37,54)^T$, rather than the coherent sum-tail. Writing the real symmetric tail as $\left(\begin{smallmatrix}a&b\\b&c\end{smallmatrix}\right)$, its entries remain strictly positive under $(a,b,c)\mapsto(26a+64b+40c,38a+92b+56c,58a+136b+80c)$. The effective boundary has the positive entries $37a+54b,37b+54c$, so the original positive-boundary chart theorem applies. The original transfer is injective, and the original three-site gauge preserves transfer injectivity through invertible conjugate sandwiches and a nonzero scalar.

`OpenBoundaryMPSQuotient` supplies a rational observable boundary-Gram inverse. With the same fixed column $t$, write $d=\operatorname{eval}_t(\mathrm{minorPoly})$, $v=\operatorname{eval}_t(\det\mathrm{basisNumerator})$, $b_i=\operatorname{eval}_t(\mathrm{leftNumerator}_i)$, $N_i=\operatorname{eval}_t(\mathrm{matrixNumerator}_i)$ and $M=\mathrm{transferMatrix}(N)$. The original normalized rows $lA_i=e_i$ give the contraction $L_{kw}=l_{w_0}l_{w_1}\mathbf1_{w_2=k}$, with $L\,\mathrm{prefixMap}=I$. Its cleared version is $L_0=d^2L$. For $B=L_0Q_3L_0^\dagger$ and $h(z)=z\bar z$, the exact full-length canonical boundary Gram is

$$
qq^\dagger=\frac{h(v)^m}{h(d)^{m+2}\det(M)^m}
\operatorname{unvec}\!\left(\operatorname{adj}(M)^m\operatorname{vec}(B)\right).
$$

The denominator's exponent uses the actual complement length $m$ and adds no new selector determinant. Multiplying the numerator by $\overline{\det M}^{m}$ gives the positive real denominator $|d|^{2(m+2)}|\det M|^{2m}$. Literal polynomial expressions in arbitrary observed entries and independent conjugates, and real Cartesian numerator/denominator expressions for all thirteen quotient coordinates, accompany this identity. The five core coordinates remain the original Ma--Zhang canonical reconstruction. On the explicit refinement where the cleared 00 boundary numerator is nonzero, $\sigma=G_{00}=|q_0|^2>0$ and $\eta=G_{10}/G_{00}=q_1/q_0$. The positive representative $(\sqrt\sigma,\sqrt\sigma\eta)$ is unit-phase equivalent to the actual full state; the square-root realization is not called rational. The quotient observation uses boundary $(1,\eta)$ followed by real scale $\sigma$, and its coordinate inverse is an exact retraction. The original fixed-density witness and full-length gauge prove the refined chart nonempty for every $m$, without assuming the refinement to prove its witness. This inverse unit does not prove the subsequent generic-point rank/fiber descent or increase the solved-open-problem count.

Generic-point two-site nonidentifiability in a dense intrinsic locus of the full actual state image remains unproved. The recovery-genericity theorem and the separate parameter-open collision theorem below do not together resolve Conjecture 9. No solved-open-problem credit, positive or physically implementable recovery inverse, stability, dynamics or thermodynamic consequence is asserted.


`OpenBoundaryMPSTwoSiteMinimality` proves a local no-fewer result for every source length $N=3+m$ with $m\ge1$. Its canonical source has thirteen real coordinates, fixes the right boundary's first coordinate to be positive real, and retains the raw affine amplitude scale. The set `canonicalChart m` additionally requires the coherent triple chart, invertibility of $S=A_0+A_1$, and invertibility of the fixed leading $00,01$ principal block of $Q_2$. `canonicalChart_nonempty` proves this set nonempty uniformly in $m$; `isOpen_canonicalChart` proves it open. `open_subchart_collision` states that every nonempty subset of this canonical chart which is open in the induced subtype topology has two actual free-boundary matrix-and-boundary states in its image with identical **entire** raw $Q_2$ and no unit phase relating them; chart openness promotes the relative-open subset to an ambient-open set before the dimension obstruction. Its Q2 complement has length $1+m$, while the coherent triple complement has length $m$.

The proof combines the real C1 dimension obstruction with the actual amplitude-column factorization through a two-dimensional bond. The Gram is Hermitian of rank at most two, and fixed-block Schur completion upgrades twelve-real-coordinate record equality to full density equality; under the combined rank-at-most-two and invertible-leading-block hypotheses, the rank is exactly two. `phase_rigidity` uses the existing coherent inverse and invertible $S^m$ to identify all canonical parameters from phase-equal full states. The canonical-core inverse argument is attributed to Haobo Ma and Wenlin Zhang, *Proof of Critch–Morton Conjecture 8* (3 November 2026), licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); it is reused C8 mathematics, rather than claimed as new C9 content.

The uniform witness starts from $A_0=\left(\begin{smallmatrix}1&2\\3&4\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}5&6\\7&8\end{smallmatrix}\right)$, $l=(1,0)$ and $r=(1,2)^T$. An exact full-length gauge gives canonical $l=(-3,1)$, $A_0=\left(\begin{smallmatrix}1&1/2\\4&3/2\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}-1/2&2\\-3/2&7\end{smallmatrix}\right)$, and $r_N=2^{N-1}(5,17)^T$. The original positive sum matrix preserves positive coherent boundaries, on which the exact chart factors do not vanish. The tail COLUMN MATRIX $\left(\begin{smallmatrix}5&17\\11&23\end{smallmatrix}\right)$ has determinant $-72$ and its Gram determinant is $5184$. The original tail Gram is positive definite after every positive iterate, and the fixed prefix row pair has determinant $-36$, so the fixed density block stays invertible. The canonical $\det S=-2$ is distinct from a transfer-operator determinant.

This parameter-open result does not establish a dense intrinsic real-algebraic open locus in the actual state image, its descent to phase classes, or phase saturation of arbitrary open state loci. Those are separate obligations for full C9 PREFIX generic minimality. No interior-window, normalized-state, dynamical or thermodynamic conclusion is inferred.

## Verified locator

- DOI: https://doi.org/10.3842/SIGMA.2014.095
- Source: https://arxiv.org/abs/1210.2812v4

`OpenBoundaryMPSQ2PolynomialFiber.exists_generic_fiber` strengthens this parameter-domain result to fibers through every certified parameter. Its new coordinates are five complex core entries c, a positive real sigma and a complex eta, with old representative (c,sqrt(sigma),sqrt(sigma)*eta). The actual raw Q2 record is a literal Fin 13 to Fin 12 real polynomial: lift the canonical matrices and left row, start the two by two transfer at sigma times [[1,conjugate eta],[eta,eta times conjugate eta]], and extract the existing twelve real record components. For each k, O={sigma positive, representative in canonicalChart k} is open and nonempty; one nonzero real polynomial D gives a nonempty open locus O intersect {D nonzero}, dense relative to O. Through each point of this locus and in every specified open neighborhood contained in O, there is a positive-dimensional real C1 same-Q2 fiber with a continuous linear left inverse and the exact dimension equation. Every nonzero fiber parameter gives an actual length 3+k state not unit-phase equivalent to the original state. Q2 has complement 1+k, and the coherent Q3 complement is k. The conclusion is genericity in the canonical parameter domain only; intrinsic density in the actual MPS image still needs a separate observable rational inverse and denominator descent. This supplies no additional solved-open-problem credit and no arbitrary interior-window, normalized-state, dynamics or thermodynamic assertion.
