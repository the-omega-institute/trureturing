---
bibkey: audenaert2008normcompression
authors: K. M. R. Audenaert
year: 2008
title: "On a norm compression inequality for 2×N partitioned block matrices"
doi: 10.1016/j.laa.2007.08.007
url: https://arxiv.org/abs/math/0702186v2
claim: "Conjecture 1, upper branch: Schatten norm compression for arbitrary 2×N compatible block matrices at p ≥ 2."
strata_touched:
  - D5/S3/Quantum/NormCompression/UpperBranchReduction
  - D5/S3/Quantum/NormCompression/FinitePowerTrace
  - D5/S3/Quantum/NormCompression/FinitePowerSpectral
  - D5/S3/Quantum/NormCompression/FinitePowerMetric
  - D5/S3/Quantum/NormCompression/FinitePowerConcavity
  - D5/S3/Quantum/NormCompression/FinitePowerKernel
  - D5/S3/Quantum/NormCompression/LocalOutputGluing
  - D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound
license: citation-only
triage: anchor
---

# Norm compression for two block rows

## Verified locator

DOI: 10.1016/j.laa.2007.08.007

Source: https://arxiv.org/abs/math/0702186v2

Linear Algebra and its Applications 428 (2008), 781–795. The arXiv preprint's
page 2 contains the Schatten norm, the compression matrix and Conjecture 1;
Section 4 is entitled "Proofs in Special Cases". The publisher's
DOI metadata matches the author, title, volume and pages.

On page 1, the source defines compression in words:

> The norm compression of a block-partitioned matrix T = [T₍ᵢⱼ₎] w.r.t. a given matrix norm ||.|| is a matrix obtained from T by replacing each of its blocks by their norm: [||T₍ᵢⱼ₎||].

On page 2, the Schatten norm is

$$\|A\|_p=(\operatorname{Tr}(|A|^p))^{1/p}.$$

The compression definition, on the same page, is introduced by:

> I denote by 𝒞ₚ(T) its Schatten p-norm compression,

$$\mathcal C_p(T)=\begin{pmatrix}\|A_1\|_p&\cdots&\|A_N\|_p\\
\|B_1\|_p&\cdots&\|B_N\|_p\end{pmatrix}.$$

Conjecture 1, page 2, verbatim:

> Let T be a general matrix partitioned in 2 × N blocks, and let 𝒞ₚ(T) be its norm compression using the Schatten p-norm, then the following norm compression inequalities hold:

$$\|T\|_p\ge\|\mathcal C_p(T)\|_p,\quad 1\le p\le2,$$
$$\|T\|_p\le\|\mathcal C_p(T)\|_p,\quad p\ge2.$$

The Lean encoding uses `Matrix.toEuclideanLin` and
`LinearMap.singularValues`: the trace power is the finite sum of the p-th
powers of singular values, and the Schatten norm is its real 1/p-th power.
The scalar compression entries are nonnegative real block norms cast to ℂ.
The two row spaces are arbitrary finite types; the finite column dimension
may depend on the column index.

The upper-branch three-column reduction preserves the compression Gram
matrix and increases the original Schatten norm after nonnegative
square-root rescaling. This is a reduction of the upper branch, not a proof
of Conjecture 1. AUD-UP on 2 < p < 4 remains open. The lower-branch reduction
requires trace-power concavity and is not established by this module.


## Covariance-metric application of existing results

This is an ordinary derivation from existing formal suppliers, explained in the
`geometricMean_riccati` entry of
`Blueprint/D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.scribe.cs`.
It introduces no new exported Lean declaration and makes no novelty claim.
Write $X^*$ for conjugate transpose and $X\succeq0$ for positive semidefiniteness.
All factors retain their displayed order; no commutativity or common spectral
basis is assumed.

Let $m,k$ be arbitrary finite dimensions, $D\in\mathbb C^{m\times m}$ positive
definite, and $A,C\in\mathbb C^{m\times k}$ arbitrary. In particular, $A$ and $C$
may be rank deficient or zero. The inverse of $D$ is its ordinary two-sided
inverse and is Hermitian. Set $E=A-D^{-1}C$. The full ordered square expansion is

$$
\begin{aligned}
E^*DE
 &=A^*DA-A^*D(D^{-1}C)-(D^{-1}C)^*DA
   +(D^{-1}C)^*D(D^{-1}C)\\
 &=A^*DA+C^*D^{-1}C-A^*C-C^*A\succeq0.
\end{aligned}
$$

Here $D(D^{-1}C)=C$ and $(D^{-1}C)^*D=C^*$.
`Matrix.PosSemidef.conjTranspose_mul_mul_same` gives positivity of this
$k\times k$ congruence. Taking its nonnegative real trace, using
`Matrix.PosSemidef.trace_nonneg`, `RCLike.nonneg_iff` and
`Matrix.trace_conjTranspose`, gives

$$
2\operatorname{Re}\operatorname{Tr}(A^*C)
\le\operatorname{Re}\operatorname{Tr}(A^*DA)
 +\operatorname{Re}\operatorname{Tr}(C^*D^{-1}C).
$$

The coefficient $2$ is sharp: $D=I$ and $A=C\ne0$ attains equality whenever
the dimensions permit a nonzero factor. This is the stated real cross-trace
bound; it asserts no absolute-value or Schatten bound.

For any $n\ge0$, let $D$ be positive definite and $G$ Hermitian, both complex
$n\times n$. Then the other ordered square is

$$
\begin{aligned}
K&=(D-G)D^{-1}(D-G)\\
 &=DD^{-1}D-DD^{-1}G-GD^{-1}D+GD^{-1}G\\
 &=D-G-G+GD^{-1}G\succeq0.
\end{aligned}
$$

Congruence of $D^{-1}$ with the Hermitian matrix $D-G$ supplies positivity;
$G$ need not be positive for this identity. To take a weighted trace, let $P$
be positive definite and $K\succeq0$. With $H=P^{1/2}$, the existing
`CFC.sqrt_mul_sqrt_self` and positive-square-root Hermitian facts give
$HH=P$ and $H=H^*$. Hence

$$
\operatorname{Re}\operatorname{Tr}(KP)
=\operatorname{Re}\operatorname{Tr}(KHH)
=\operatorname{Re}\operatorname{Tr}(HKH)\ge0.
$$

The middle equality is trace cyclicity (`Matrix.trace_mul_comm`), and
$HKH=H^*KH\succeq0$ is a congruence. The argument does not assert that $KP$
itself is Hermitian or positive semidefinite.

Now let $P,S\in\mathbb C^{n\times n}$ be positive definite and define

$$
G=\operatorname{geometricMean}(P^{-1},S),\qquad
J(D)=\operatorname{Re}\operatorname{Tr}(DP)
 +\operatorname{Re}\operatorname{Tr}(D^{-1}S)
\quad(D\text{ positive definite}).
$$

The existing `LinGProperty.geometricMean` uses
`AlternativeMeanLinearization.gmInv` with the inverse of its first argument.
Thus `LinGProperty.geometricMean_riccati`, supplied by
`AlternativeMeanLinearization.riccati`, applied to $P^{-1},S$ gives precisely
$G\succ0$ and $GPG=S$. The orientation is $P^{-1}\#S$. Equivalently,

$$
G=P^{-1/2}(P^{1/2}SP^{1/2})^{1/2}P^{-1/2},
$$

because the positive matrix $P^{1/2}GP^{1/2}$ squares to $P^{1/2}SP^{1/2}$.
For every positive definite competitor $D$, cyclicity and the Riccati identity
give

$$
\operatorname{Tr}((GD^{-1}G)P)
=\operatorname{Tr}(D^{-1}(GPG))
=\operatorname{Tr}(D^{-1}S).
$$

Multiplying the ordered square identity by the same actual $P$ and taking
its real trace therefore yields the exact gap

$$
J(D)-2\operatorname{Re}\operatorname{Tr}(GP)
=\operatorname{Re}\operatorname{Tr}\bigl((D-G)D^{-1}(D-G)P\bigr)\ge0.
$$

For attainment, $G^{-1}S=PG$ follows by cancellation in $GPG=S$, and hence

$$
J(G)=\operatorname{Re}\operatorname{Tr}(GP)
 +\operatorname{Re}\operatorname{Tr}(PG)
=2\operatorname{Re}\operatorname{Tr}(GP).
$$

Consequently $J(G)\le J(D)$ for **every** positive definite $D$, and

$$
\min_{D\succ0}J(D)=2\operatorname{Re}\operatorname{Tr}(GP).
$$

This is an attained global minimum on the stated positive definite domain;
no separate uniqueness theorem or equality characterization is asserted.

With $P=AA^*$ and $S=CC^*$, rectangular trace cyclicity rewrites the right
side of the rectangular bound as $J(D)$. This optimizer calculation applies
only when both covariances are positive definite. If $C=ZB$, the dimensions
are $B\in\mathbb C^{r\times k}$ and $Z\in\mathbb C^{m\times r}$, and $C$
is their actual product. The rectangular square and bound remain valid for
singular and zero factors, since only $D$ is inverted. Empty row or column
index types, including $m=0$, $k=0$, and the square case $n=0$, reduce the
relevant identities and traces to zero. There is no claim of an inverse or
an attained optimizer for arbitrary singular metrics or singular covariances.

This application uses existing PSD congruence, trace positivity, square-root
and Riccati facts together with ordered inverse and trace algebra. It does
not solve Conjecture 1, supply unrelated-spectrum witnesses, or establish
the missing joint Schatten comparison for arbitrary compatible blocks.


## Finite two-row trace powers and local output budgets

For every finite column type, including the empty type, and every real
$1<q<2$, let $W$ be entrywise nonnegative, set
$A_q(W)_{bj}=W_{bj}^{1/(2q)}$, and put
$F_q(W)=\operatorname{Tr}((A_q(W)A_q(W)^*)^q)$.
`FinitePowerConcavity.Fq_eq_trace_rpow` identifies this operator expression
with the actual finite singular-value power sum used by the repository.
`continuous_Fq` proves continuity on the full cone (in fact on the ambient
real table space for $q>0$), and `Fq_smul` proves
$F_q(cW)=cF_q(W)$ for every $c\ge0$ and $q>0$.
`FinitePowerConcavity.concaveOn_Fq` proves full-cone concavity in the stated
open interval. Singular Grams, zero entries, axial columns and empty column
types are included. This is the two-row finite-power functional discussed
in the paper's final section, at $p=2q\in(2,4)$; the source's two-by-two
lemma is not substituted for arbitrary finite column count.

The proof differentiates the actual two-eigenvalue trace formula, keeps
all three symmetric metric coordinates, proves the strict scalar metric
gap for arbitrary real $q-1\in(0,1)$, and passes to the boundary by two
independent appended columns. Those root columns are exactly
$\varepsilon^{1/(2q)}(1,1)^T$ and
$\varepsilon^{1/(2q)}(1,4^{1/(2q)})^T$.
The normalized velocity is $z=\dot W/(q x^{2q-1})$, so $\dot x=z/2$;
both first- and second-derivative coefficients retain this normalization.

`FinitePowerConcavity.radial_hessian_kernel` asserts an exact local statement:
if the row Gram is positive definite, some column overlaps both rows, and
$V$ vanishes at every zero coordinate of $W$, then
$D^2F_q(W)[V,V]=0$ if and only if $V=cW$ for a real scalar $c$.
Zero columns and axial nonzero columns are retained through their actual
support tangents. No radial converse is asserted for a rank-one Gram or
a purely axial table, and no global superadditivity equality classification
is inferred from this local theorem alone.

For arbitrary finite rectangular complex column maps, the theorem
`LocalOutputGluing.local_output_compression_budget` genuinely consumes
this concavity: the sum of the $2q$-th Schatten powers of the component
compression matrices is at most the $2q$-th Schatten power of the global
compression matrix, for complete orthogonal resolutions of both local
outputs. Every local output and original column dimension may be empty.
The row-piece bound uses the existing full-PSD positive-unital Jensen
supplier and the attributed Physlib operator-power convexity source.
The existing Carlen--Lieb fixed invertible congruence theorem has a different
SPD domain and is not used as a replacement for the finite-power theorem.

These are supplied-calculation and repository proof results, without a
worldwide priority or solved-status claim. The unrestricted common-majorant
optimization chain, its full $\kappa_r$ gluing consequence, and the original
arbitrary complex block norm-compression inequality remain separate
obligations. Auxiliary four-slot registration is unfinished and disclosed
in [issue 26283](https://github.com/the-omega-institute/trureturing/issues/26283).
