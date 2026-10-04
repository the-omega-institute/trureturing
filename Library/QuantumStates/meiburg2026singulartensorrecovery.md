---
bibkey: meiburg2026singulartensorrecovery
authors: Alex Meiburg
year: 2026
title: Singular tensor logarithms and marginal support in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HermitianMat/LogExp.lean
claim: Physlib supplies singular tensor-log and actual marginal-support mechanisms; their repository-derived composition yields the product-reference recovery identity without a novelty claim.
strata_touched:
  - D5/S3/Quantum/Divergence/CanonicalProductRecovery
license: Apache-2.0
triage: anchor
---

# Singular tensor logarithms and product recovery

## Locator

The declared source URL is:
https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HermitianMat/LogExp.lean

`HermitianMat.log_kron_diagonal_with_proj` and `HermitianMat.log_kron_with_proj`
give the singular tensor-log formula. The same revision's
`QuantumInfo/ForMathlib/Isometry.lean`,
`Matrix.IsHermitian.cfc_eq_any_isometry`, supplies the arbitrary-diagonalization
argument. `QuantumInfo/Entropy/Relative.lean`, private
`fixed_support_kron_right` and `qMutualInfo_as_qRelativeEnt`, supplies the actual
marginal-support argument and the weighted support cancellation.
`QuantumInfo/ForMathlib/Matrix.lean`, `trace_mul_kron_one_right` and
`trace_mul_one_kron_right`, gives the raw complex trace contractions.

Capel, Lucia and Pérez-García, *Quantum conditional relative entropy and
quasi-factorization of the relative entropy*,
https://arxiv.org/abs/1804.09525v2, §3.3, Case 2, identifies the product-reference
conditional relative entropy with relative entropy to product recovery.
Their subsystem subscript denotes the erased subsystem; exchange its labels
to retain A here. Their Remark 4 assumes full-rank states throughout the paper.
The whole recovery chain below is a repository-derived composition of these
known source mechanisms. Its singular step uses the explicit kernel and
zero-eigenvalue calculation, rather than attributing a singular-state statement
to that full-rank convention. These identities are known mathematics;
the receiving adaptation does not assert novelty.

The cited Physlib code is Apache-2.0, with the original Alex Meiburg copyright
headers retained in the adapted code and the full license in
`docs/reports/inoutbalance/physlib-LICENSE.txt`. The mathematical paper is citation-only.

## Actual matrices and support

Let A and B be finite complex Hilbert spaces, and let rho be any joint density
matrix. In formulas write

$$
R=\operatorname{Tr}_B\rho,\quad S=\operatorname{Tr}_A\rho,\quad
C=\gamma_A,\quad B=\gamma_B,\quad
\widehat\rho=R\otimes B,\quad\gamma=C\otimes B.
$$

Only the reference factors C and B are positive definite density matrices.
R and rho may be singular, correlated or entangled. The entries of R and S are

$$
R_{x,z}=\sum_y\rho_{(x,y),(z,y)},\qquad
S_{y,t}=\sum_x\rho_{(x,y),(x,t)}.
$$

These are the actual receiving `partialTraceRight` and `partialTraceLeft`.
The existing canonical/legacy state conversions preserve the underlying
matrix and its positivity and trace-one proofs. No independent density carrier
or divergence is introduced. Trace one excludes an empty ambient carrier:
an empty matrix has trace zero. Dimension one is allowed, without a rank-two
condition. Zero oscillator modes, by contrast, correspond to a one-dimensional
Hilbert space, not an empty matrix carrier.

For any finite Hermitian X set

$$
L(X)=\operatorname{cfc}(\log,X),\qquad
\chi(t)=\begin{cases}0&t=0,\\1&t\ne0,\end{cases}\qquad
P_X=\operatorname{cfc}(\chi,X).
$$

For positive semidefinite X, P_X is the orthogonal support projection. The
total real logarithm has log(0)=0; it is not an infinite relative-entropy branch.

## Spectral calculation without aligned enumerations

Write X=U diag(x_i) U* and Y=V diag(y_j) V* using any two independent
orthonormal eigenbases. U tensor V diagonalizes X tensor Y with diagonal
x_i y_j. There is no assertion equating this indexing with the functional
calculus implementation's chosen eigenvalue enumeration.

To justify functional calculus on this diagonalization, let Z also have a
chosen diagonalization V0 diag(z_k) V0*. Set W=U* V0. The equality of the
two representations gives

$$
x_iW_{ik}=W_{ik}z_k.
$$

If x_i differs from z_k, W_ik=0; otherwise f(x_i)W_ik=W_ik f(z_k) for
any function f. Thus diag(f(x)) W=W diag(f(z)). Multiplying by U and V0*
proves cfc(f,Z)=U diag(f(x_i)) U*. This argument handles repeated and zero
eigenvalues. Every function is continuous on the finite real spectrum, so
the discontinuity of chi at zero does not obstruct this finite CFC use.

For nonnegative x,y,

$$
\log(xy)=\log x\,\chi(y)+\chi(x)\log y,\qquad
\chi(xy)=\chi(x)\chi(y).
$$

If either factor is zero the first equality has both sides zero. If both
are positive it is the ordinary product logarithm. Applying the preceding
diagonalization gives

$$
L(X\otimes Y)=L(X)\otimes P_Y+P_X\otimes L(Y),\qquad
P_{X\otimes Y}=P_X\otimes P_Y.
$$

In particular,

$$
L(\widehat\rho)=L(R)\otimes I_B+P_R\otimes L(B),\qquad
L(\gamma)=L(C)\otimes I_B+I_A\otimes L(B).
$$

The projection in the first expression is essential. For
R=diag(1,0), B=I_2/2, the left-hand side has diagonal
(-log 2,-log 2,0,0). Replacing P_R by I incorrectly gives -(log 2)I_4.

## Marginal kernel contraction and zero weights

Take an eigenbasis u_i of R and any orthonormal basis w_j of the second
factor. Put e_ij=u_i tensor w_j and
t_ij=⟨e_ij,rho e_ij⟩. Positivity gives t_ij≥0. Expanding the actual marginal
entries and using completeness of w_j gives

$$
\sum_j t_{ij}=\langle u_i,Ru_i\rangle=r_i.
$$

If r_i=0, every t_ij=0. For a positive semidefinite operator,
⟨v,rho v⟩=0 implies rho v=0: writing rho=F*F, the quadratic form is
the squared norm of Fv. Hence rho annihilates every e_ij with r_i=0.
These vectors span ker(R) tensor H_B. Since B is invertible,

$$
\ker(R\otimes B)=\ker R\otimes\mathcal H_B\subseteq\ker\rho.
$$

Equivalently, with Q=P_R tensor I_B,

$$
\rho Q=\rho=Q\rho.
$$

The proof uses the rotated positive matrix
T=(U* tensor I) rho (U tensor I). Its right partial trace is diag(r_i).
A zero marginal diagonal is a sum of nonnegative diagonals T_(i,j),(i,j),
so each is zero. The positive-matrix zero-quadratic theorem then annihilates
the corresponding entire column of T. Thus T diag(chi(r_i))=T, which
conjugates back to rho Q=rho.

For a spectral rho=∑_k lambda_k |v_k⟩⟨v_k|, let
W_kij=|⟨v_k,e_ij⟩|². Then t_ij=∑_k lambda_k W_kij, and
r_i=0 implies lambda_k W_kij=0 for every k,j. This is the explicit zero-weight
cancellation; no logarithm of a positive argument is applied before those
zero terms are removed.

## Raw traces and the finite chain

For arbitrary complex matrices M,X,Y of the relevant sizes,

$$
\operatorname{Tr}(M(X\otimes I_B))=
\operatorname{Tr}((\operatorname{Tr}_B M)X),\qquad
\operatorname{Tr}(M(I_A\otimes Y))=
\operatorname{Tr}((\operatorname{Tr}_A M)Y).
$$

The first identity expands on both sides to
∑_(x,z,y) M_(x,y),(z,y) X_(z,x); the second expands to
∑_(x,y,t) M_(x,y),(x,t) Y_(t,y). These are equalities of complex traces,
before taking real parts, with no commutation hypothesis.

Use the exact singular tensor log and rho Q=rho. Tensor multiplication gives
(P_R tensor L(B))=Q(I_A tensor L(B)). Therefore

$$
\operatorname{Tr}\rho L(\widehat\rho)
=\operatorname{Tr}RL(R)+\operatorname{Tr}SL(B),\qquad
\operatorname{Tr}\rho L(\gamma)
=\operatorname{Tr}RL(C)+\operatorname{Tr}SL(B).
$$

Let T(X)=Re Tr(X L(X)). The receiving finite trace-log expressions are

$$
\begin{aligned}
D_{\mathrm{fin}}(\rho\Vert\gamma)
 &=T(\rho)-\operatorname{Re}\operatorname{Tr}RL(C)
                 -\operatorname{Re}\operatorname{Tr}SL(B),\\
D_{\mathrm{fin}}(R\Vert C)
 &=T(R)-\operatorname{Re}\operatorname{Tr}RL(C),\\
D_{\mathrm{fin}}(\rho\Vert\widehat\rho)
 &=T(\rho)-T(R)-\operatorname{Re}\operatorname{Tr}SL(B).
\end{aligned}
$$

Subtracting gives

$$
D_{\mathrm{fin}}(\rho\Vert\gamma)-D_{\mathrm{fin}}(R\Vert C)
=D_{\mathrm{fin}}(\rho\Vert\widehat\rho).
$$

C and C tensor B are positive definite. The marginal-kernel proof supplies
the remaining support condition for rho against the singular recovered state.
Consequently all three canonical WithTop-real divergences are finite, and
the safe extended statement is

$$
D(\rho\Vert\gamma)=D(\rho\Vert\widehat\rho)+D(R\Vert C).
$$

This justifies real subtraction. Unsupported pairs must retain the infinite
branch: for orthogonal pure diagonal states the totalized trace-log expression
is zero but the canonical divergence is top.

Applying the chain to the actual recovered state, whose A-marginal is R,
gives D(recovered || gamma)=D(R || C). Existing product entropy additivity
and the same trace expansions also give

$$
D(\rho\Vert\widehat\rho)=I(A:B)_\rho+D(S\Vert B).
$$

No simultaneous diagonalization of R and C is used: their cross term is
∑_(i,l) r_i |⟨u_i,g_l⟩|² log(c_l).

## Theorem 1. Finite canonical product recovery

For every pair of finite index types A and B, every canonical joint density
state rho on A times B, and every pair of canonical density states gammaA on
A and gammaB on B whose underlying matrices are positive definite, set R to
the actual right partial-trace marginal of rho, S to its actual left
partial-trace marginal, recovered to the product state of R and gammaB, and
reference to the product state of gammaA and gammaB. The existing
canonical-to-legacy and legacy-to-canonical conversions preserve these
matrices. No positive-definiteness hypothesis is imposed on rho, R or S.
Let Dfin denote finiteTraceLogRelativeEntropy and D denote the canonical
extendedQuantumRelativeEntropy with values in WithTop of the reals. Then

$$
\begin{gathered}
\operatorname{SupportContained}(\rho,\mathrm{recovered}),\\
D_{\mathrm{fin}}(\rho\Vert\mathrm{reference})-D_{\mathrm{fin}}(R\Vert\gamma_A)
 =D_{\mathrm{fin}}(\rho\Vert\mathrm{recovered}),\\
D(\rho\Vert\mathrm{reference})
 =D(\rho\Vert\mathrm{recovered})+D(R\Vert\gamma_A),\\
D(\rho\Vert\mathrm{reference})\ne\top,\quad
D(\rho\Vert\mathrm{recovered})\ne\top,\quad
D(R\Vert\gamma_A)\ne\top,\quad D(S\Vert\gamma_B)\ne\top,\\
D_{\mathrm{fin}}(\rho\Vert\mathrm{recovered})
 =I(A:B)_\rho+D_{\mathrm{fin}}(S\Vert\gamma_B).
\end{gathered}
$$

Here I(A:B) is the receiving quantumMutualInformation of the same rho.
Support containment is reverse inclusion of matrix nullspaces. Every support
and finiteness conclusion is derived from the stated density and faithful
reference hypotheses. Trace one excludes empty density carriers; dimension
one and singular marginals remain included.

## Actual Gibbs generators and the same Hamiltonian

For physical Hermitian H_A,H_B and beta>0 put K_A=-beta H_A,
K_B=-beta H_B and H0=H_A tensor I+I tensor H_B. The existing Gibbs owner
uses the exponential generator K, not the physical energy H without this sign.
The tensor embeddings are continuous algebra homomorphisms and their ranges
commute. Mapping the exponential through each embedding and applying the
commuting exponential sum identity gives

$$
e^{-\beta H0}=e^{-\beta H_A}\otimes e^{-\beta H_B},\quad
Z_0=Z_AZ_B,\quad\gamma_{H0}=\gamma_A\otimes\gamma_B.
$$

These are direct existing exponential applications and normalization.
For the original same-H splitting, with d=dim A, e=dim B,

$$
h_0=\operatorname{Tr}H/(de),\quad
H_A=e^{-1}\operatorname{Tr}_BH-h_0I_A,\quad
H_B=d^{-1}\operatorname{Tr}_AH,\quad V=H-H0,
$$

write f_H=-beta⁻¹ log Z_H, G_H(rho)=beta⁻¹ D(rho||gamma_H),
E(rho)=D(rho||recovered), and Delta_H=G_H(rho)-beta⁻¹D(R||gamma_A).
The existing Gibbs variational identity and the finite chain give

$$
\Delta_H-\beta^{-1}E(\rho)=\operatorname{Tr}(\rho V)-(f_H-f_{H0}),
$$

$$
G_H(\rho)-G_H(\widehat\rho)=\beta^{-1}E(\rho)
+\operatorname{Tr}((\rho-\widehat\rho)V).
$$

They compare gamma_H with the actual product gamma_H0. They do not replace
a correlated gamma_H by the product of its marginals. Given the original
perturbation bound |f_H-f_H0|≤||V||≤delta(H), positivity and trace one imply
|Delta_H-beta⁻¹E|≤2delta(H). With quantum Pinsker in nats and the unhalved
trace norm, ||rho-sigma||_1²≤2D(rho||sigma), the original recovery estimate is

$$
\|\rho-\widehat\rho\|_1\le
\min\{2,\sqrt{2\beta(\Delta_H+2\delta(H))}\}.
$$

Its radicand is nonnegative because Delta_H+2delta(H)≥E/beta≥0.
For V=0 the product unitary transports both rho and its recovered state;
the hidden local Gibbs state is fixed, so the defect is conserved. Zero defect
characterizes exact recovery once zero-separation is supplied. These last
implications use relative-entropy nonnegativity and quantum Pinsker; they are
not consequences of the chain rule alone.

Finite matrix calculus does not establish the infinite-dimensional oscillator
tensor domains, actual observable-compatible metaplectic splitting, selfadjoint
closures and cores, or trace-class Gibbs and partition-factorization results.
