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
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorCommonCore
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorGenericity
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality
  - D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential
  - D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery
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

`OpenBoundaryMPSInteriorCommonCore.interior_common_core` supplies a separate arbitrary-interior common-core theorem. Let $p,q\ge1$, $N=(p+3)+q$, and let the target be the actual state $\psi(w)=lA_wr$. Assume `TwoSiteSpanning A`: the four products $A_iA_j$ span $M_2(\mathbb C)$. With $E_A(Z)=\sum_i A_iZA_i^\dagger$ and $E_A^*(Z)=\sum_i A_i^\dagger ZA_i$, require the **actual** environments $P=(E_A^*)^p(l^\dagger l)$ and $H=E_A^q(rr^\dagger)$ to be positive definite. For any actual competitor $\phi(w)=l'B_wr'$ of the same length, equality of the complete unnormalized `rawInterior p 3 q` matrices implies

$$
\exists X\in M_2(\mathbb C),\qquad
\phi(w)=\operatorname{tr}(X A_w)\quad\text{for every word }w\text{ of length }N.
$$

The competitor matrices and both free boundaries are arbitrary; no spanning, environment or transfer-invertibility hypothesis is imposed on them. The conclusion gives one unrestricted complex coefficient $X$ in the same target core. The observation sums $\psi( a u b )\overline{\psi( a v b )}$ over both actual exterior words $a,b$, retaining their order and the squared-norm scale.

The exact dictionary is $C=FK$ and $KK^\dagger=H\otimes P^T$, where $F(u,(i,j))=(A_u)_{ji}$ and $K((i,j),(a,b))=(A_b r)_i(lA_a)_j$. Positive definiteness gives context rank four; the original trace-separation theorem makes the target three-site feature injective. Equality of raw Grams therefore gives a rank-four observed competitor range. This saturates its entire coefficient image, whose dimension is at most four, so **every** $\operatorname{tr}(YB_u)$ belongs to the target three-site parent space. `all_coefficient_parent_induction` propagates this inclusion to every length $m+3$, generalizing the coefficient at each step: snoc uses $B_jY$, cons uses $YB_i$, and the original unrestricted parent intersection glues the two slices of the same function. Taking $m=p+q$ and $Y=r'l'$ gives the full actual competitor above.

`OpenBoundaryMPSInteriorCommonCore.common_core_rank_one` now closes the coefficient-rank step for an already established actual common-core representation. For $N\ge4$, write $N=2+(s+2)$. The weighted flattening
$$F_X((i,j),w)=\operatorname{tr}\!\bigl(XA_iA_jA_w\bigr)$$
is a row submatrix of the competitor's two-prefix amplitude matrix, so `columns_factor` and the two-dimensional virtual boundary give $\operatorname{rank}F_X\le2$. If $\det X\ne0$, the left map $Y\mapsto\gamma_A(s+2)(XY)$ is injective by `trace_separates`; the original two-site span argument then gives $\operatorname{rank}F_X=4$, a contradiction. Full rank for a $2\times2$ matrix is equivalent to surjectivity of `mulVec` and to `IsUnit`, so the converse needed to exclude rank two is explicit. Thus $\operatorname{rank}X\le1$, including the zero case. The existing rank-one factorization writes $X=r_A l_A$ and the private state-gamma identity rewrites the same competitor state through $A$ with boundaries $(l_A,r_A)$. This is conditional on the common-core representation, introduces no phase or genericity claim, and does not settle Conjecture 9.

`OpenBoundaryMPSInteriorCommonCore.interior_phase_recovery` completes conditional interior phase uniqueness against arbitrary actual competitors. For $p,q\ge1$ and $N=(p+3)+q$, retain target-only `TwoSiteSpanning A`, the actual positive definite $P,H$ above, and additionally require injectivity of $E_A$ on all complex $2\times2$ matrices. Complete unnormalized `rawInterior p 3 q` equality then implies

$$
\exists z\in\mathbb C,\qquad |z|=1,\qquad
\phi=z\psi.
$$

The competitor $B,l',r'$ remains arbitrary. The proof consumes the common-core theorem and its actual rank-one refactorization, then cancels the four-column feature sandwich to obtain $\widehat H\otimes\widehat P^T=H\otimes P^T$. For fixed $t,j$, this is $\widehat P_{tj}\widehat H=P_{tj}H$; linearity and injectivity cancel $E_A^q$. The bilinear trace pairing $\operatorname{tr}(Y E_A(X))=\operatorname{tr}(E_A^*(Y)X)$ and finite-dimensional surjectivity of $E_A$ imply injectivity of $E_A^*$, which cancels the other iterate. Thus the flattened coefficients $x_{ij}=r_i l_j$ and $\widehat x_{ij}=\widehat r_i\widehat l_j$ have identical outer Grams. The dimension-generic, zero-safe form of the original boundary-phase argument gives $\widehat x=zx$, and trace linearity gives the full-state conclusion. The internal same-core argument works for arbitrary natural $p,q$ and uses neither positivity nor lower bounds on them; those assumptions belong to the arbitrary-competitor common-core reduction. This is an algebraic conditional result; transfer inversion is not asserted to be positive or physically implementable.

The conditional interior unit is consumed by the intrinsic genericity theorem below. Downstream `InteriorSpectralAmbiguity.observed_interior_ambiguity` proves interior two-site insufficiency for every fixed $N\ge4$: one common nonempty relatively open dense principal locus in the entire actual image serves every individual internal two-site window, with an actual nonzero nonphase competitor that may depend on the window. This raw-state result supplies no joint-marginal theorem; the $N=3$ boundary-only case, right reversal, one-site partial-trace adapters and full window composition remain obligations. Full Conjecture 9 remains open. This conditional interior unit carries **zero solved-open-problem credit** and adds no normalized-state recovery, physical recovery operation, dynamics, time group, energy, clock or thermodynamic cost. The prefix results and their C8 provenance retain their stated scopes.

`OpenBoundaryMPSInteriorGenericity.intrinsic_interior_recovery` proves the all-interior three-site sufficiency portion intrinsically for every fixed $N=3+m\ge5$. There is one nonzero real polynomial $R_m$ in the real and imaginary entries of the complete raw prefix $Q_3$ whose nonvanishing defines a nonempty relatively open dense, unit-phase-saturated subset of the **entire actual** free-boundary uniform bond-two image. At every target in that same locus, every interior split $p,q\ge1$ with $p+q=m$ has the following property: equality of the complete raw three-site interior density with any actual competitor is equivalent to equality of the full states up to a unit complex phase. The competitor has no chart, spanning, transfer, environment, minimality or normalization premise. A polynomial may depend on the length; no common locus across different lengths is claimed.

The sufficient factors use the existing thirteen real quotient coordinates. With canonical $A,l$, $v=(1,\eta)^T$, define $S_{(a,b),(i,j)}=(A_iA_j)_{ab}$ and $V_{a,i}=(A_iv)_a$. Both product indices are ordered $00,01,10,11$; the feature matrix in CommonCore uses the transposed entry convention for a different purpose. Let

$$
K(x)=|\det S_x|^2|\det A_0(x)|^2|\det V_x|^2.
$$

Each squared modulus is the sum of squares of coefficientwise real and imaginary polynomial parts. Existing coordinate-specific clearing gives $K(x(Q))=H(y)/B(y)$ with $B(y)\ne0$ on the quotient locus. The observed polynomial is $R_m=\rho_m H$; $B$ needs no additional factor. The all-length canonical witness has $c=(-3,1,1/2,-1/2,2)$, $\eta=17/5$ and $\sigma=25(2^{2+m})^2$. Its exact determinants are $64,-1/2,72/25$, respectively, giving $K=5308416/625$. The existing witness gauge and local quotient retraction put **this same full state** on every factor. The existing actual_principal_genericity then proves density in the entire actual image.

The canonical identities $lA_i=e_i$ give $P_1=I$. Writing the actual right boundary as $r=\sqrt\sigma v$, the first right environment is $WW^\dagger$ for the invertible column matrix $W=(A_0r,A_1r)$. An invertible $A_0$ congruence plus the positive semidefinite $A_1$ term propagates strict positivity of both environments through every positive iterate. The factor $\det A_0$ is a sufficient locus restriction only and is not added to interior_phase_recovery. Actual observed_coherent, the original canonical_shape and the positive-representative alignment transport canonical transfer injectivity from the recovery polynomial; no separate transfer determinant is reproved. The accepted conditional phase theorem is then applied at every split, and its phase is composed with the exact actual quotient representative. Raw Gram scaling gives the reverse implication and phase saturation.

This establishes interior three-site sufficiency, retains the C8 Ma--Zhang and Q2 LeanPool attributions, and carries **zero solved-open-problem credit**. Interior two-site insufficiency is supplied by `InteriorSpectralAmbiguity.observed_interior_ambiguity` with the scope stated above for each fixed length, its common locus and competitors that may differ by window. Full C9 remains open. It supplies no normalized-state theorem, physical recovery operation, dynamics, clock, energy or thermodynamic conclusion.

`OpenBoundaryMPSQuotient` supplies a rational observable boundary-Gram inverse. With the same fixed column $t$, write $d=\operatorname{eval}_t(\mathrm{minorPoly})$, $v=\operatorname{eval}_t(\det\mathrm{basisNumerator})$, $b_i=\operatorname{eval}_t(\mathrm{leftNumerator}_i)$, $N_i=\operatorname{eval}_t(\mathrm{matrixNumerator}_i)$ and $M=\mathrm{transferMatrix}(N)$. The original normalized rows $lA_i=e_i$ give the contraction $L_{kw}=l_{w_0}l_{w_1}\mathbf1_{w_2=k}$, with $L\,\mathrm{prefixMap}=I$. Its cleared version is $L_0=d^2L$. For $B=L_0Q_3L_0^\dagger$ and $h(z)=z\bar z$, the exact full-length canonical boundary Gram is

$$
qq^\dagger=\frac{h(v)^m}{h(d)^{m+2}\det(M)^m}
\operatorname{unvec}\!\left(\operatorname{adj}(M)^m\operatorname{vec}(B)\right).
$$

The denominator's exponent uses the actual complement length $m$ and adds no new selector determinant. Multiplying the numerator by $\overline{\det M}^{m}$ gives the positive real denominator $|d|^{2(m+2)}|\det M|^{2m}$. Literal polynomial expressions in arbitrary observed entries and independent conjugates, and real Cartesian numerator/denominator expressions for all thirteen quotient coordinates, accompany this identity. The five core coordinates remain the original Ma--Zhang canonical reconstruction. On the explicit refinement where the cleared 00 boundary numerator is nonzero, $\sigma=G_{00}=|q_0|^2>0$ and $\eta=G_{10}/G_{00}=q_1/q_0$. The positive representative $(\sqrt\sigma,\sqrt\sigma\eta)$ is unit-phase equivalent to the actual full state; the square-root realization is not called rational. The quotient observation uses boundary $(1,\eta)$ followed by real scale $\sigma$, and its coordinate inverse is an exact retraction. The original fixed-density witness and full-length gauge prove the refined chart nonempty for every $m$, without assuming the refinement to prove its witness. This inverse unit does not prove the subsequent generic-point rank/fiber descent or increase the solved-open-problem count.

`OpenBoundaryMPSIntrinsicQ2Fiber.intrinsic_actual_q2_fiber` now proves the intrinsic actual-image endpoint for every $m\ge0$: a single nonzero real polynomial in the complete raw $Q_3$ entries defines a nonempty relatively open dense locus of the literal length-$N=3+m$ image. Through every state in that locus and every relative neighborhood, the proof constructs an actual state with equal complete raw prefix $Q_2$ and rules out every unit-complex phase relation. The construction descends the twelve-component polynomial Q2 record through the quotient rational retraction, clears its coordinate-specific denominators, and uses the rank-fiber theorem together with the existing Hermitian rank-two Schur-completion result. The leading-block and quotient-locus factors are retained in the defining polynomial, so the fiber theorem is applied only where the retraction and completion hypotheses remain valid.

This endpoint is for the displayed prefix reading of C9 on the full actual image. It does not settle arbitrary interior windows, normalized readings, or the full source quantifier of the paper's conjecture, and it supplies no solved-open-problem credit until that scope is separately assessed. No positive or physically implementable recovery inverse, stability, dynamics or thermodynamic consequence is asserted.


`OpenBoundaryMPSTwoSiteMinimality` proves a local no-fewer result for every source length $N=3+m$ with $m\ge1$. Its canonical source has thirteen real coordinates, fixes the right boundary's first coordinate to be positive real, and retains the raw affine amplitude scale. The set `canonicalChart m` additionally requires the coherent triple chart, invertibility of $S=A_0+A_1$, and invertibility of the fixed leading $00,01$ principal block of $Q_2$. `canonicalChart_nonempty` proves this set nonempty uniformly in $m$; `isOpen_canonicalChart` proves it open. `open_subchart_collision` states that every nonempty subset of this canonical chart which is open in the induced subtype topology has two actual free-boundary matrix-and-boundary states in its image with identical **entire** raw $Q_2$ and no unit phase relating them; chart openness promotes the relative-open subset to an ambient-open set before the dimension obstruction. Its Q2 complement has length $1+m$, while the coherent triple complement has length $m$.

The proof combines the real C1 dimension obstruction with the actual amplitude-column factorization through a two-dimensional bond. The Gram is Hermitian of rank at most two, and fixed-block Schur completion upgrades twelve-real-coordinate record equality to full density equality; under the combined rank-at-most-two and invertible-leading-block hypotheses, the rank is exactly two. `phase_rigidity` uses the existing coherent inverse and invertible $S^m$ to identify all canonical parameters from phase-equal full states. The canonical-core inverse argument is attributed to Haobo Ma and Wenlin Zhang, *Proof of Critch–Morton Conjecture 8* (3 November 2026), licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); it is reused C8 mathematics, rather than claimed as new C9 content.

The uniform witness starts from $A_0=\left(\begin{smallmatrix}1&2\\3&4\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}5&6\\7&8\end{smallmatrix}\right)$, $l=(1,0)$ and $r=(1,2)^T$. An exact full-length gauge gives canonical $l=(-3,1)$, $A_0=\left(\begin{smallmatrix}1&1/2\\4&3/2\end{smallmatrix}\right)$, $A_1=\left(\begin{smallmatrix}-1/2&2\\-3/2&7\end{smallmatrix}\right)$, and $r_N=2^{N-1}(5,17)^T$. The original positive sum matrix preserves positive coherent boundaries, on which the exact chart factors do not vanish. The tail COLUMN MATRIX $\left(\begin{smallmatrix}5&17\\11&23\end{smallmatrix}\right)$ has determinant $-72$ and its Gram determinant is $5184$. The original tail Gram is positive definite after every positive iterate, and the fixed prefix row pair has determinant $-36$, so the fixed density block stays invertible. The canonical $\det S=-2$ is distinct from a transfer-operator determinant.

This parameter-open result does not establish a dense intrinsic real-algebraic open locus in the actual state image, its descent to phase classes, or phase saturation of arbitrary open state loci. Those are separate obligations for full C9 PREFIX generic minimality. No interior-window, normalized-state, dynamical or thermodynamic conclusion is inferred.

## Periodic two-site differential identifiability

Conjecture 10 in Section 2 concerns a generic periodic binary, bond-dimension-two matrix product state. It asks for determination up to phase from the reduced density matrix on four adjacent sites, with a no-fewer clause. The observation is a Hermitian partial trace of the actual periodic trace-word state. The parameter-space differential of its two-site version is a separate question from generic uniqueness among all states in the actual image.

`PeriodicMPSTwoSiteDifferential.projective_rank_eight` supplies a chart point for each ring length $N\geq 4$. Fix the entry $a$ in $A_0=\operatorname{diag}(a,b)$ and take the first and second rows of $A_1$ to be $(c,1)$ and $(d,e)$. The raw two-site density, together with its eight real coordinate derivatives in $b,c,d,e$, has a nonsingular nine-row minor in the complex entries of the Hermitian observation. The derivative modulo the real radial line has rank eight at the witness. The proof transports the actual trace-word marginal to a Kronecker transfer contraction, reduces Gaussian integer coefficients modulo 13, and checks the minors over the 162 complement lengths supplied by a dual transfer recurrence. Generic global phase recovery from two sites remains open in this result.

`PeriodicMPSTwoSiteLocalRecovery.normalized_local_recovery` integrates the rank witness for every ring length $N\geq 4$. The trace of the raw two-site Gram is the total squared amplitude mass. On a nonempty positive-mass open neighborhood in the fixed-$a$ chart, the trace-normalized two-site density admits a decoder for all four remaining complex coordinates. Differentiating the mass rescaling identifies any kernel direction with a raw radial tangent, which the nine-column minor excludes. A real linear projection followed by the local inverse supplies the decoder, with a two-point Lipschitz estimate for recovery on the certified neighborhood. Generic finite phase-class fibers in the full periodic state space and the sharp threshold in Conjecture 10 remain open.

## Verified locator

- DOI: https://doi.org/10.3842/SIGMA.2014.095
- Source: https://arxiv.org/abs/1210.2812v4

`OpenBoundaryMPSQ2PolynomialFiber.exists_generic_fiber` strengthens this parameter-domain result to fibers through every certified parameter. Its new coordinates are five complex core entries c, a positive real sigma and a complex eta, with old representative (c,sqrt(sigma),sqrt(sigma)*eta). The actual raw Q2 record is a literal Fin 13 to Fin 12 real polynomial: lift the canonical matrices and left row, start the two by two transfer at sigma times [[1,conjugate eta],[eta,eta times conjugate eta]], and extract the existing twelve real record components. For each k, O={sigma positive, representative in canonicalChart k} is open and nonempty; one nonzero real polynomial D gives a nonempty open locus O intersect {D nonzero}, dense relative to O. Through each point of this locus and in every specified open neighborhood contained in O, there is a positive-dimensional real C1 same-Q2 fiber with a continuous linear left inverse and the exact dimension equation. Every nonzero fiber parameter gives an actual length 3+k state not unit-phase equivalent to the original state. Q2 has complement 1+k, and the coherent Q3 complement is k. The conclusion is genericity in the canonical parameter domain only; intrinsic density in the actual MPS image still needs a separate observable rational inverse and denominator descent. This supplies no additional solved-open-problem credit and no arbitrary interior-window, normalized-state, dynamics or thermodynamic assertion.

The fiber theorem's C1 supplier credits BochaoKong's Apache-2.0 LeanPool constant-rank argument at commit `2b1ec889365345f19a45fa94b6457a4d92c96295`; the canonical inverse and phase argument retain Ma and Zhang's CC BY 4.0 attribution. These reused arguments are not claimed as new CommonCore or C9 mathematics.


`OpenBoundaryMPSInteriorRootRealization` gives a conditional root-to-actual
ambiguity theorem for every $p,q\ge1$, with $N=(p+2)+q$. Fix a regular complex
sector $(\lambda,\mu,a)$ and write
$\delta=\mu-\lambda$, $\alpha=\lambda-a$, $\beta=\mu-a$,
$c=-\alpha\beta$. Regularity is
$\delta\alpha\beta\ne0$ and
$|1+\overline\lambda\mu|^2>0$. Put

$$
B=\operatorname{diag}(\lambda,\mu),\quad
G(z)=\begin{pmatrix}1&z\\\alpha&\beta z\end{pmatrix},\quad
C=\begin{pmatrix}a&1\\c&\lambda+\mu-a\end{pmatrix},\quad
A(z)=(G(z),BG(z)).
$$

Then $CG=GB$ and $A_iA_j=K_{ij}G^2$, with
$(K_{00},K_{01},K_{10},K_{11})=(I,C,B,BC)$. For arbitrary original finite
boundaries $l,r$ and nonzero $z_0$, the fixed actual environments are

$$
P=(E_{z_0}^*)^p(l^\dagger l),\qquad
H=G(z_0)^2 E_{z_0}^q(rr^\dagger)(G(z_0)^2)^\dagger.
$$

Assume both are positive definite. Reusing the original CommonCore observation
and Gram dictionary, with prefix rows $L_u=lA_u$ and right columns
$S_v=G^2 A_vr$, gives $P=L^\dagger L$, $H=SS^\dagger$ and the entire raw
interior identity

$$
Q_2(w,w')=\operatorname{tr}(P K_w H K_{w'}^\dagger).
$$

The observation is still the actual sum over both exterior words, using
`append(append(left,block),right)`. It retains all sixteen complex entries and
the squared-norm scale. No prefix rank-at-most-two record replaces it.

For the diagonal maps $D_B(X)=X+BXB^\dagger$ and
$D_{B^*}(X)=X+B^\dagger XB$, the algebraic inverses have the exact orders

$$
(E_z^*)^{-1}(P)=D_{B^*}^{-1}(G(z)^{-\dagger}P G(z)^{-1}),\qquad
E_z^{-1}(H)=G(z)^{-1}D_B^{-1}(H)G(z)^{-\dagger}.
$$

The maps $D_B^{-1}$ and $D_{B^*}^{-1}$ divide each entry by the corresponding
nonzero diagonal Schur factor. They are not claimed positive. Define the trial
boundary matrices with fixed $P,H$ by

$$
X_p(z)=((E_z^*)^{-1})^p(P),\qquad
Y_q(z)=(E_z^{-1})^q\bigl((G(z)^2)^{-1}H((G(z)^2)^{-1})^\dagger\bigr).
$$

`distinct_residual_root_actual_ambiguity` proves that every nonzero
$z\ne z_0$ with $\det X_p(z)=\det Y_q(z)=0$ yields actual finite boundaries
$l',r'$ for $A(z)$ and hence an actual nonzero competitor $\phi$ with identical
**entire** raw interior $Q_2$, while no unit complex scalar relates the two
full states. Hermitian preservation and both inverse-composition identities
are proved. The existing rank-one factor supplier and Hermitian symmetry
express each trial matrix as a real multiple of an outer Gram. Forward CP
positivity and the positive definite target exclude a nonpositive multiplier;
its positive square root supplies actual boundaries. This does not assume
abstract root realizability or a positive inverse.

The phase proof uses the span of $I,C,B,BC$ and explicit inverses supplied by
the positive target Grams. A hypothetical full-state phase equality gives
$UMV=\eta M$ for every $M\in M_2(\mathbb C)$; the scalar-center theorem forces
$U=hI$ with $h\ne0$, hence proportional actual prefix rows. The two columns
on prefix words $0^{p-1}j$ have coefficient matrices
$R_\alpha=\left(\begin{smallmatrix}1&\alpha\\\lambda&\mu\alpha\end{smallmatrix}\right)$
and
$R_\beta=\left(\begin{smallmatrix}1&\beta\\\lambda&\mu\beta\end{smallmatrix}\right)$,
whose determinants are $\alpha\delta$ and $\beta\delta$. They force $z=z_0$.
No old canonical-chart condition or extra regularity on $l',r'$ is used.

`annular_regular_root_actual_ambiguity` uses the explicit real map
$f(z)=\operatorname{Re}\det X_p(z)+i\operatorname{Re}\det Y_q(z)$.
It proves continuity on every closed annulus excluding zero and proves
$f(z_0)=0$ from the inverse identities. Under explicit radii
$0<\epsilon<|z_0|<R$, strict negativity of $\operatorname{Re}f$ on both
boundary circles, and an ordinary invertible **real** Frechet derivative at
$z_0$, `AnnularSecondZero.annular_second_zero` supplies a nonzero distinct
common root and the deterministic theorem supplies the actual competitor.
No holomorphicity, strict derivative, regularity or finiteness of other zeros,
or nonzero boundary winding is assumed.

This is conditional ambiguity, not genericity or a solution of C9, and it
adds **zero** solved-open-problem credit. The endpoint signs and fixed-witness
all-length real transversality are supplied below. Finite canonical-chart coverage and
dominance, and genericity on the actual state and actual raw-density images
remain separate obligations. The C8 attribution to Ma and Zhang, CC BY 4.0,
is unchanged. The topology supplier reuses
`TauCeti.not_contractibleSpace_sphere` at revision
`5a01f5fe3621126cccf9ba22e700493cbc7b7156`, with the Apache-2.0 license retained
at `docs/reports/licenses/tauceti-sphere-port-LICENSE.txt` and source-port
attribution in the owning topology note. This static finite-state theorem
adds no normalization, physical positive inverse, stability, clock, dynamics,
energy or thermodynamic cost.


`OpenBoundaryMPSInteriorTransversality.interior_q2_fixed_target_witness`
closes the ordinary real derivative premise at one actual witness for every
$p,q\ge1$. Its only inputs are these lengths and their positivity proofs.
The native sector is $(\lambda,\mu,a)=(2,0,1)$, $z_0=1$,
$l=(1,1)$ and $r=(1,i)^T$. With the same native targets, inverse transfers
and residual defined above, the theorem proves $P_p,H_q$ positive definite,
$X_p(1)=l^\dagger l$, $Y_q(1)=rr^\dagger$, and $f(1)=0$.

The first positive environments are
$S(l^\dagger l)=\left(\begin{smallmatrix}8&4\\4&4\end{smallmatrix}\right)$
and $E(rr^\dagger)=\left(\begin{smallmatrix}10&2i\\-2i&2\end{smallmatrix}\right)$,
with determinant $16$ in both cases. Invertible $G(1)$ congruence plus a
positive semidefinite Kraus summand preserves strict positivity at every
subsequent step, and $G(1)^2=2I$ gives $H_q=4E^q(rr^\dagger)$.

The ordinary real derivative is a continuous linear equivalence with

$$
Df(1)[w]=L_p\operatorname{Re}w+
i\bigl(C_q\operatorname{Re}w+R_q\operatorname{Im}w\bigr),
\qquad
\det\begin{pmatrix}L_p&0\\C_q&R_q\end{pmatrix}=L_pR_q\ne0.
$$

Joint parameter/input derivatives are proved before differentiating the
parameter-dependent inverse iterates, with $P_p,H_q$ held fixed. Both
$G(z)^{-1}$ factors in the central inverse-square sandwich contribute.
Conjugation is real linear. Determinants are differentiated entrywise at
the rank-one boundary Grams, without a matrix-inverse premise there.

The nonvanishing proof uses division-free integer recurrences. Let
$a_0=(1,0,-1)$, $b_0=(1,0,1)$, $x_0=(0,1,0)$, $y_0=(1,0,0)$ and

$$
D=\begin{pmatrix}3&0&-2\\-2&0&3\\0&5&0\end{pmatrix},\quad
T=\begin{pmatrix}3&2&0\\0&0&1\\2&3&0\end{pmatrix},\quad M=T^T.
$$

Set $a_{n+1}=a_nD$, $b_{n+1}=Tb_n$, $x_{n+1}=D^Tx_n$,
$y_{n+1}=My_n$ and $t_n=a_{n,0}b_{n,1}+a_{n,1}b_{n,0}$. From $U_0=V_0=0$ use

$$
U_{n+1}=5U_n+2t_{n+1},\qquad
V_{n+1}=5V_n+2(-1)^{n+2}
\bigl(x_{n+1,0}+5^{n+1}y_{n+2,2}\bigr).
$$

Real coordinate and inverse-power inductions identify
$5^pL_p=U_p$ and $5^qR_q=V_q$ after integer-to-real casts.
Successor induction in $\mathbb Z/5\mathbb Z$ proves
$U_p=1$ and $V_q=2(-1)^{q+1}3^q$ for all positive lengths. Their nonzero
residues imply $L_pR_q\ne0$, and the integrated theorem retains
$5^{p+q}L_pR_q=U_pV_q$ and the product residue. No homomorphism from
$\mathbb Q$ to $\mathbb Z/5\mathbb Z$, finite-length sweep or assumed
invertibility certificate is used.

This supplies one fixed-target all-length interior zero and its invertible
real derivative. It supplies no general annular boundary signs, endpoint
operator limits, polynomial clearance, genericity, or full C9, and adds
zero solved-open-problem credit. Source attribution for the original MPS
problem and reused C8 mathematics is unchanged. There is no normalized-state,
positive physical inverse, clock, dynamics, energy or thermodynamic claim.


`OpenBoundaryMPSInteriorEndpointSigns` supplies the general regular-sector annular
boundary-sign premise, using exactly the existing native `inverseDualTransfer`,
`trialLeft` and `residual`. For a regular sector put
$d=|\mu-\lambda|^2$, $a_0=1+|\lambda|^2$, $a_1=1+|\mu|^2$,
$c=|1+\overline\lambda\mu|^2$, $T=D_{B^*}^{-1}$,
$u=(\beta,-1)$ and $v=(-\alpha,1)$. Let
$M_\infty=T(u^\dagger u)$ and $M_0=T(v^\dagger v)$. In the actual
complex continuous-linear operator norm on $M_2(\mathbb C)\to M_2(\mathbb C)$,
with the elementwise supremum norm on the matrices, the Lean proof establishes

$$
|z|^2(E_z^*)^{-1}\longrightarrow[X\mapsto X_{11}M_0/d]
\quad(z\to0,\ z\ne0),\qquad
(E_z^*)^{-1}\longrightarrow[X\mapsto X_{00}M_\infty/d]
\quad(z\to\infty).
$$

The second filter is the cobounded filter on the entire complex plane. The
proof constructs exact continuous extensions: with $U$ having rows
$(\beta,-1),(0,0)$ and $V$ having rows $(0,0),(-\alpha,1)$,
$G(z)^{-1}=\delta^{-1}(U+z^{-1}V)$ for $z\ne0$. At infinity use
$d^{-1}T((U+wV)^\dagger X(U+wV))$ at $w=z^{-1}\to0$. At zero use
$d^{-1}T(|z|^2U^\dagger XU+\bar z U^\dagger XV+zV^\dagger XU+V^\dagger XV)$.
Finite-dimensional `continuous_clm_apply` promotes application continuity to
operator-norm continuity; scalar casts are complex and the native inverse
order is retained. Powers of these same operators converge before applying
them to the fixed target. Thus for every fixed $p\ge1$ and every Bond $P$,

$$
|z|^{2p}X_p(z)\longrightarrow P_{11}d^{-p}a_1^{-(p-1)}M_0,\qquad
X_p(z)\longrightarrow P_{00}d^{-p}(|\beta|^2/a_0)^{p-1}M_\infty.
$$

The exact determinants are real:
$\det M_0=|\alpha|^2(1/(a_0a_1)-1/c)$ and
$\det M_\infty=|\beta|^2(1/(a_0a_1)-1/c)$. Since
$c=a_0a_1-d>0$ and regularity makes $d,|\alpha|^2,|\beta|^2$ positive,
both determinants are strictly negative. If $P$ is positive definite,
$P_{00},P_{11}$ are real and positive, so the two determinant limits are
strictly negative. The positive factor $|z|^{4p}$ removes the zero-endpoint
scale. At infinity the determinant tends to a negative constant.

`annular_residual_negative` constructs for every nonzero $z_0$ radii
$0<\epsilon<|z_0|<R$ for which $\operatorname{Re}f(z)<0$ on both whole
circles, simultaneously for every $q$ and $H$. Uniform filter convergence,
rather than a raywise assertion, supplies the circle-wide signs. This is a
new endpoint proof within the Critch--Morton C9 program, not a literature
claim or a full C9 solution. Real transversality, finite chart coverage,
polynomial clearance and actual-density genericity remain separate.
It earns zero resolved external open problems and supplies no dynamics,
energy, clock, normalization or physical inverse.

`OpenBoundaryMPSInteriorPolynomial` constructs literal real polynomials
$F^L_{p,q},F^R_{p,q}$ in two independent trial coordinates and sixteen actual
coordinates, ordered as the real and imaginary parts of
$(\lambda,\mu,a,l_0,l_1,r_0,r_1,z_0)$. The native sector and core are the
ones above; no fixed canonical thirteen-coordinate core is substituted.
The targets are formed at $z_0$ and held fixed as the trial $z=x+iy$ varies.
The right target retains the outer $G(z_0)^2$ congruence after the transfer
iterate, and the inverse trial seed retains both inverse-square factors.

Put $d=|\mu-\lambda|^2$, $a_0=1+|\lambda|^2$,
$a_1=1+|\mu|^2$, $\kappa=|1+\bar\lambda\mu|^2$,
$\Gamma=da_0a_1\kappa$ and $t=|z|^2$. The exact evaluation identities are

$$
F^L_{p,q}(x,y;\theta)=\Gamma^{2p}t^{2p}\operatorname{Re}f(z),\qquad
F^R_{p,q}(x,y;\theta)=\Gamma^{2q}d^4t^{2q+4}\operatorname{Im}f(z).
$$

Both factors are strictly positive for a regular sector and $z\ne0$.
Division-free adjugate and cleared Schur recurrences establish these
identities for all natural lengths. Paired polynomial variables, actual
Cartesian conversion and real coefficient extraction give the literal
polynomials; polynomiality is not an additional premise.

Differentiate only the independent trial coordinates and then substitute
$(x,y)=(\operatorname{Re}z_0,\operatorname{Im}z_0)$ to define

$$
b_{p,q}(\theta)=
\left[\partial_xF^L_{p,q}\partial_yF^R_{p,q}
-\partial_yF^L_{p,q}\partial_xF^R_{p,q}\right]_{z=z_0}.
$$

Polynomial induction identifies these formal partials with the ordinary
real Frechet derivative of each fixed-target slice. At the native common
root, $b_{p,q}(\theta)=c_L(z_0)c_R(z_0)\det_{\mathbb R}Df(z_0)$.
The real basis is $(1,i)$ with output rows real and imaginary. The diagonal
identity with changing targets is never differentiated. Consuming the
native all-positive-length fixed witness above proves nonzero evaluation
and $b_{p,q}\ne0$ for every $p,q\ge1$, without an additional transversality
or witness assumption.

For every real scalar $a$, replacing $r$ by $ar$ multiplies evaluation of
$b_{p,q}$ by exactly $a^4$. The right target scales by $a^2$ and its cleared
$2\times2$ determinant and derivative row scale by $a^4$; the left row and
clearing factors are unchanged. This supplies boundary amplitude transport
for finite spectral descent. The residual derivative has real rank two;
spectral coefficient rank four is a different notion.

These results concern the native parameter locus. Finite chart dominance,
actual full-state and actual raw-density image genericity, and official C9
scope acceptance remain separate obligations. The external open-problem
count remains zero.

`nonzero_locus_actual_ambiguity` connects this locus to the exact native
annular conclusion. For regular sectors and nonzero actual target, the
polynomial formulas divided by their nonzero factors prove ordinary real
differentiability. Nonzero evaluation of $b_{p,q}$ makes that derivative
invertible. The endpoint signs supply enclosing radii, and the native
annular root realization supplies an actual nonzero finite MPS with equal
entire raw interior $Q_2$ and no unit-phase relation to the target. Positive
definiteness of both actual target environments remains an explicit
hypothesis. This is a parameter-locus theorem, not actual-image genericity.


`OpenBoundaryMPSSpectralExtraction` supplies the finite algebraic bridge from
the existing Ma--Zhang five-complex canonical core to the native sector of
`OpenBoundaryMPSInteriorRootRealization`. For the canonical coordinates
$c=(c_0,\ldots,c_4)$ put $h=c_4-c_1$, $D=h^2+4c_2c_3$,
$t_0=c_1-c_0c_2$, $t_1=1+c_3-c_0c_4$ and
$U=ht_0t_1-c_2t_1^2+c_3t_0^2$. The exact exclusions are
$e^2=D$ and $c_2DU(U+D)\ne0$. With
$\lambda=(h+e)/(2c_2)$, $\mu=(h-e)/(2c_2)$,
$T=A_0[(1,\lambda)^T,(1,\mu)^T]$ and $K=T^{-1}A_0T$,
the identities are $\det T=e$, $LT=(1,1)$,
$(A_1A_0^{-1})T=T\operatorname{diag}(\lambda,\mu)$,
$\det K=-c_2$, $ut=c_2U/D$ and $vw=c_2(U+D)/D$.
All four entries $u,v,w,t$ and $\delta=-e/c_2$ are nonzero.

Set $\rho=-c_2/(\delta uv)$, $S=T\operatorname{diag}(1,\rho)$,
$z=-c_2/(\delta u^2)$, $\alpha=\delta vw/(-c_2)$,
$a=\lambda-\alpha$. The native sector is $(\lambda,\mu,a)$;
$\beta=\mu-a=\delta ut/(-c_2)$ and $\beta-\alpha=\delta$.
The bridge retains the existing native $G,B$ and proves
$A_iS=uS\,\mathrm{core}_{\mathrm{native},i}$. The Schur cross
factor $1+\bar\lambda\mu\ne0$ is a separate condition for native
regularity; distinct eigenvalues alone do not supply it.
For every natural length $N$ and arbitrary original right boundary $R$,
the complete raw state is unchanged under
$l=LS=(1,\rho)$ and $r=u^NS^{-1}R$.
The actual native normalizer with rows $lG,lBG$ is $S/u$;
$lK_l^{-1}=uL$, whose second entry recovers $u$. Canonicalization
at this scalar returns both original cores, $L$ and $R$ exactly.

The same supplier starts from the actual native matrices
$G=\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$,
$B=\operatorname{diag}(2,0)$, $l=(1,1)$, $r=(1,i)$.
Its normalizer is $\left(\begin{smallmatrix}2&0\\2&2\end{smallmatrix}\right)$,
with inverse $\left(\begin{smallmatrix}1/2&0\\-1/2&1/2\end{smallmatrix}\right)$.
Thus $lK_l^{-1}=(0,1/2)$ and its second entry recovers the canonical scalar
$1/2$. This is the numerical application of `canonicalization_inverse` to
the same witness. The general normalizer proof directly reuses the original
`OpenBoundaryMPSTwoSiteMinimality.normalized_rows` at $(c,0,0)$.
Canonicalization gives
$c_*=(0,0,1/2,0,1)$, $R=2^N(1,1+i)$, $\sigma=4^N$,
$\eta=1+i$. At $e=1$ extraction returns the same native sector
$(2,0,1)$, $z=1$, $l=(1,1)$ and $r=(1,i)$.
Using only the raw boundary $(1,\eta)$ instead gives $2^{-N}(1,i)$.
Here $D=1$, $U=-1/2$, $U+D=1/2$ and the cross factor equals one.
The canonical quotient's existing `positiveBoundary` restores exactly the
same full scalar boundary. The C8 attribution and CC BY 4.0 license are
unchanged. This is a reusable inverse supplier, with no dimension-fourteen
assumption, arbitrary polynomial restriction, norm-field argument, genericity
proof, positive-environment extension or actual-image density claim.
Full C9 remains open and this unit earns zero solved-open-problem credit.


## Lengthwise canonical spectral exclusion with actual ambiguity

For every fixed pair of positive lengths $p,q$, put $N=(p+2)+q$.
`InteriorSpectralCoordinates.native_coordinates` supplies sixteen literal
REAL15 numerator/denominator pairs for the actual native sector, left boundary,
right boundary $u^NS^{-1}(1,\eta)$ and $z$. The first two variables are
$\operatorname{Re}e,\operatorname{Im}e$; the remaining thirteen retain the
existing canonical order. Every inverse guard follows from $e^2=D$ and
$c_2DU(U+D)\ne0$, including in helpers at $N=0$. The existing
`Q2PolynomialFiber.clear_polynomial`, with arbitrary independent denominators,
gives real polynomials $H,B$ and the exact physical equality $b=H/B$, with
$B\ne0$ there. No complex rational-function clearing statement is assumed.

The division-free cross numerator is
$C_\times=4c_2\bar c_2+(\bar h+f)(h-e)$, where $h=c_4-c_1$,
$e=X+iY$ and $f=X-iY$. At physical points it equals
$4\lVert c_2\rVert^2(1+\bar\lambda\mu)$.
Reduce $H(\operatorname{ReCoeff}C_\times^2+
\operatorname{ImCoeff}C_\times^2)$, with the squares taken after each
coefficient projection, by the literal finite MX/MY monomial sum to
$g_0+g_1X+g_2Y+g_3r$. `g_evaluation` proves the actual REAL15 evaluation
identity with $r=\operatorname{normSq}(e)$.

For $A=\operatorname{ReCoeff}D$, $B=\operatorname{ImCoeff}D$ and
$Q=A^2+B^2$, define
$K_0=g_0^2+Qg_3^2-\tfrac12 A(g_1^2-g_2^2)-Bg_1g_2$,
$H_0=2g_0g_3-\tfrac12(g_1^2+g_2^2)$ and
$\mathrm{normg}=K_0^2-QH_0^2$. Polynomial halves are $C(1/2)$.
The consumed character identity pairs the simultaneous opposite signs:
$h(E,F)h(-E,-F)=K_0+H_0EF$ and
$h(-E,F)h(E,-F)=K_0-H_0EF$, with $E^2=A+iB$, $F^2=A-iB$.

`InteriorSpectralWitness.normg_nonzero` uses the free COMPLEX13 map with
$c_3=-c_2\lambda\mu$, $c_4=c_1+c_2(\lambda+\mu)$ and an independent
barred copy. Swapping $\lambda,\mu$ and independently swapping the barred
pair fixes every mapped canonical coordinate and flips the two roots
independently. The original physical witness proves one free character
nonzero using actual real clearing and `b_right_scale`. The polynomial-domain
orbit product proves the norm polynomial nonzero. Neither injectivity of the
base map nor nonvanishing of the norm at that physical witness is assumed.

Set $J_{\rm den}=\lVert c_2DU(U+D)\rVert^2$ and
$W=c_2\eta^2+(c_1-c_4)\eta-c_3$. The literal REAL13 certificate is
$P_{p,q}=\sigma J_{\rm den}\lVert W\rVert^2\mathrm{normg}$.
At the existing physical witness $J_{\rm den}=1/64$ and $W=-1$;
the free orbit supplies the independent norm factor.
`P_nonzero` proves $P_{p,q}\ne0$. `certificate_native` proves that
$P_{p,q}(x)\ne0$ and $\sigma(x)>0$ supply Admissible, Regular and actual
native $b\ne0$ for every root branch. The exact quartic scaling law restores
$\sqrt\sigma$; no first-entry nonzero condition on the native right is used.

`InteriorSpectralEnvironments.native_environment_transport` proves the left
transport $a^{-p}S^\dagger L_pS$ and the bare right transport
$(a^N/a^q)S^{-1}R_q(S^{-1})^\dagger$, where $a=\operatorname{normSq}(u)>0$.
The actual right target is its outside $G^2$ congruence. The original
`InteriorGenericity.positive_iterates` is exposed with its body unchanged
and consumed to prove BOTH true native target matrices PosDef.
`InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity` combines the
nonzero certificate and the genuine public `nonzero_locus_actual_ambiguity`
consumer. At each such canonical point it produces a nonzero actual MPS with
the same entire raw two-site interior and no unit-phase relation, retaining
the complete $u^N$ boundary factor through `raw_amplitude`.

This canonical supplier proves length-dependent parameter exclusion and pointwise
actual ambiguity. Downstream `InteriorSpectralAmbiguity.observed_interior_ambiguity`
supplies the observed descent and entire-actual-image density below. Full C9 remains
open and solved-open-problem KPI is zero.
The existing C8 attribution and license are unchanged. New and exposed Reg
attempts require native audit readout; compilation alone does not assert
`declared_validated`, and unfinished evidence remains under issue #30422.


`InteriorSpectralAmbiguity.observed_interior_ambiguity` descends the SAME
substantive spectral exclusion unit to the literal actual image. Fix $m\ge1$,
$N=3+m$, and $i\in\operatorname{Fin}(m)$. Put
$p_i=i+1$, $q_i=m-i$, and clear the nonzero canonical certificate
$P_{p_i,q_i}$ through the original quotient numerator and denominator families:
$P_{p_i,q_i}(x(Q))=H_i(y(Q))/B_i(y(Q))$ on $\rho_m(Q)\ne0$.
Here $y$ consists of the real and imaginary entries of the complete prefix $Q_3$,
so $\Omega=(\mathrm{Word}_3\times\mathrm{Word}_3)\sqcup
(\mathrm{Word}_3\times\mathrm{Word}_3)$ and the literal real polynomial is
$R_m=\rho_m\prod_i H_i\in\mathbb R[\Omega]$.

The nonzero product $\prod_i P_{p_i,q_i}$ has a real evaluation witness by
polynomial function extensionality. Its dense nonzero locus intersects the
EXISTING open nonempty `quotientValidityDomain m` at one common $x$.
The positive representative gives an actual state $\psi_x$ of length $N$;
quotient retraction recovers $x$, actual denominators and every $B_i$ are
nonzero, and clearing makes every $H_i(y(Q_3(\psi_x)))$ nonzero. Thus
$R_m(y(Q_3(\psi_x)))\ne0$, a genuine ACTUAL evaluation witness, before applying
`actual_principal_genericity` once. The resulting `actualPrincipalLocus m R`
is nonempty, relatively open, dense in the entire literal
`openBoundaryMPS (3+m)` subtype, and $U(1)$ saturated. No image-openness or
Zariski-closure substitute is used. The live `normg_nonzero` proof supplies
$P_{p_i,q_i}\ne0$ through `P_nonzero`; the finite product is organization of
that substantive exclusion result, not an independent novelty claim.

For every target $\psi$ in this locus, every $p,q\ge1$ with $p+q=m+1$, and
every exact length equality $h:((p+2)+q)=3+m$, there is a nonzero $\phi$ in the
SAME actual image with
$\mathrm{rawInterior}_{p,2,q}(\mathrm{castState}_h\phi)=
\mathrm{rawInterior}_{p,2,q}(\mathrm{castState}_h\psi)$ and no unit phase
$\phi=\eta\psi$. Only the target is restricted to the locus. The competitor
has no chart, `Regular`, or locus premise and may depend on the window.
The proof takes the target's positive quotient representative modulo unit
phase, uses clearing to recover the appropriate $P_{p,q}\ne0$, chooses a
complex root $e^2=D$ using `IsAlgClosed.exists_pow_nat_eq`, and invokes the
actual canonical ambiguity supplier. Exact length casts and the SAME unit
scalar transport its nonzero competitor and its complete raw observation;
nonzero scalar cancellation proves the nonphase assertion. The native right
still contains $u^N$ and the physical $\sqrt\sigma$.

This includes $m=1$, $N=4$, with $p=q=1$. It does not assert a common competitor
for all windows or one in every neighborhood. The $N=3$ boundary-only case,
right reversal, one-site partial-trace adapters, full window composition and
normalized readings remain separate obligations. Full C9 is open; the
solved-open-problem KPI remains zero. Scoped kernel verification does not
constitute freezing or independent acceptance.


## Raw all-window settlement candidate

`OpenBoundaryMPSAllWindowC9.result` composes the existing suppliers into one
raw actual-image statement for every $N=3+m\ge3$. A single nonzero real
polynomial in ALL real and imaginary full-state amplitudes defines a nonempty,
relatively open dense $U(1)$-saturated locus in the ENTIRE literal actual MPS
image. Every target there is nonzero. Every separate adjacent three-site raw
marginal determines that target up to unit phase against arbitrary actual
competitors. Each separate two-site and one-site window has a possibly
different actual nonzero nonphase competitor preserving its complete raw
marginal. Every exterior split and every exact length cast is quantified.

Ordinary transpose with swapped original boundaries makes word reversal an
actual-image homeomorphism. Intersect the prefix recovery and Q2 loci, the
interior loci only in their valid length ranges, and the two reversed prefix
loci. One common ACTUAL point of these dense open sets proves nonzero
evaluation of the literal full-amplitude polynomial, constructed by complete
Q3 quadratic substitution and reversal of amplitude indices. Boundary Q2
witnesses are chosen in the open nonzero neighborhood of the nonzero target;
partial traces retain the same pair witness for each site. No spectral,
root, norm or genericity supplier is re-proved.

This is a sufficient strengthening of the pre-probe raw $N\ge4$ prefix
recovery and no-fewer target in issue #30422. $N\ge3$ and the explicit
real-principal genericity convention are formal strengthening choices, not
quoted author wording. The candidate's conservative proof shape is bind-only;
its candidate admission basis is open-problem-resolution. The matching Scribe
and `Problems/critch-morton-2014-open-boundary-mps-raw-c9.md` describe only that
raw settlement candidate. The bounded literature check found no exact C9
settlement in its accessible searched scope; this is no priority or uniqueness
certificate. Independent caller fidelity review, required checks, freezing and
publication remain separate. Global C9 status stays OPEN and solved-open-problem
KPI stays zero until caller verification. No normalized-state, joint-marginal,
closure-only, dynamics or thermodynamic conclusion is asserted. Original
supplier attributions and licenses are unchanged; the new whole-source Reg
attempt has no source-selection certificate and claims no native validation.

`OpenBoundaryMPSNormalizedC9.result` supplies the physical-mass-one consequence of the raw all-window supplier. For every natural $m$, including zero, let $N=3+m$ and
$$
M(\psi)=\sum_{w\in\{0,1\}^N}|\psi_w|^2,
\qquad S_N=\{\psi\in\mathrm{OB}(2,2,N):M(\psi)=1\}.
$$
This uses the actual free-boundary image and its induced topology. It does not use the default Pi sup norm. If $P$ is the real polynomial on all real and imaginary amplitude coordinates supplied by `OpenBoundaryMPSAllWindowC9.result`, write $P_d$ for its degree-$d$ homogeneous component and set
$$
H=\sum_{d=0}^{\deg P}P_d^2.
$$
The theorem retains literal nonzero real polynomials $P,H$. The locus $G_N=\{\psi\in S_N:H(\operatorname{Re}\psi,\operatorname{Im}\psi)\ne0\}$ is nonempty, relatively open, dense and $U(1)$-saturated. For every target in this same locus, every $p,q\in\mathbb N$ with $p+q=m$, and every length equality $(p+3)+q=N$, equality of the individual three-site `rawInterior p 3 q` observation with an arbitrary actual mass-one competitor is equivalent to a unit-phase relation. For each $p+q=m+1$, every individual two-site window admits an actual mass-one competitor with the same observation and no phase relation; the corresponding assertion holds separately for each one-site window with $p+q=m+2$. Each competitor may depend on the window. All equality casts, zero-length exteriors and the case $N=3$ remain in scope.

The new normalization argument uses the finite coefficient polynomial $F_x(T)=\sum_d P_d(x)T^d=P(Tx)$. Homogeneous evaluation, coefficient extraction, the real sum-of-squares criterion and the univariate infinite-root theorem prove
$$
H(x)\ne0\quad\Longleftrightarrow\quad
\exists t>0,\ P(tx)\ne0.
$$
This algebraic statement includes $P=0$, constants, empty variable carriers and $x=0$; no homogeneity of $P$ or $H$ is assumed. Taking $t=1$ embeds the old dense locus in the positive-ray saturation. A continuous normalization retraction $\psi\mapsto\psi/\sqrt{M(\psi)}$ on the open positive-mass actual subtype transports density to $S_N$. The old raw phase saturation, together with the ray characterization and commuting scalar actions, gives phase saturation of $G_N$.

For every window and its exact length cast, the proof establishes scalar degree two and $\operatorname{tr}(Q_k(\psi))=M(\psi)$. Equal same-window observations therefore have equal physical mass. For a target in $G_N$, choose $t>0$ reaching the raw $P$ locus. Apply the raw theorem at $t\psi$, scale each ambiguity witness back by $t^{-1}$, and use trace equality to retain that same witness on $S_N$. Recovery scales every arbitrary mass-one competitor by the same $t$ and cancels it. This supplies no joint-window ambiguity witness, neighborhood upgrade, stability, dynamics, time group, energy, physical clock or thermodynamic statement. All upstream attribution, including the Ma–Zhang Conjecture 8 supplier under CC BY 4.0, remains in force. The normalized result completes the same preregistered physical C9 reading with both states normalized under #30422: it is an AdditionalMember of the single existing claim hosted by `OpenBoundaryMPSAllWindowC9.result` in the same Problems dossier. Its conservative proof shape is bind-only and candidate admission basis is open-problem-resolution; no escape witness, independent priority or second problem credit is asserted. Normalization alone establishes no global C9 novelty or official resolution: caller scope verification and publication remain outstanding, C9 is OPEN, and the solved-open-problem KPI increment is zero. The normalized result's full-telescope Reg attempt is `declared_unresolved`, IE-C050 ClosedTruthReadout, rule `source.selection_missing`. The newly public `OpenBoundaryMPSDensityGenericity.continuous_realCoordinates` separately lacks owner-mirror registration evidence under the same #30422 disclosure route. Neither unfinished audit claims `declared_validated`.
