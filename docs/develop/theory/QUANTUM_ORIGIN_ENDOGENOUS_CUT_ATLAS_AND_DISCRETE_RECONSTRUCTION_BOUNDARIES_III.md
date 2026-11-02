# Quantum origin: endogenous cut atlas and discrete reconstruction boundaries III

This continuation studies finite observable interfaces, purity and invisible response fibres. It follows [Part II](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_II.md); the algebra and effect interface for each result are stated in its own section.


## 1. A finite observable algebra with an explicitly complete effect interface

The following is a conditional application of standard finite-dimensional operator-algebra, Schmidt and trace-distance tools. The observable algebra, its represented blocks and its complete effect interval are supplied inputs. No uniqueness of an actual universal state, physical acquisition of that algebra or derivation of complex quantum structure is asserted.

<a id="statement-purity-1-1"></a>

**定义 1.1（Represented block interface）。** Fix finite-dimensional complex spaces and the represented unital complex $*$-algebra

<a id="eq-purity-1-1"></a>

$$
\begin{aligned}
H&=\bigoplus_{\alpha\in I}(V_\alpha\otimes W_\alpha),\\
\mathcal A&=\bigoplus_{\alpha\in I}
\bigl(B(V_\alpha)\otimes I_{W_\alpha}\bigr),\\
n_\alpha&=\dim V_\alpha\ge1,
\qquad m_\alpha=\dim W_\alpha\ge1.
\end{aligned}
\tag{1.1}
$$

This is the standard represented block form of a finite-dimensional unital complex $C^*$-algebra; the arguments use the displayed form directly. Applying the formulas to a native menu requires its algebra closure and represented block form first. A linear span of available effects need not be such an algebra, as §7 illustrates.

Operational states here are all positive normalized functionals on $\mathcal A$, tested by every effect $0\le a\le I$ in $\mathcal A$. Purity means extremality in this whole state space, rather than in a separately restricted preparation list. Physical access to the entire effect interval is an additional interface condition.

<a id="statement-purity-1-2"></a>

**定义 1.2（Subnormalized visible blocks）。** For a unit vector $\Psi=\bigoplus_\alpha\Psi_\alpha$, put

<a id="eq-purity-1-2"></a>

$$
\sigma_\alpha=\operatorname{Tr}_{W_\alpha}
|\Psi_\alpha\rangle\langle\Psi_\alpha|,
\qquad p_\alpha=\operatorname{Tr}\sigma_\alpha,
\qquad\rho_\alpha=\frac{\sigma_\alpha}{p_\alpha}
\quad(p_\alpha>0).
\tag{1.2}
$$

Thus $\sigma_\alpha\succeq0$, $\sum_\alpha p_\alpha=1$, and the restricted functional is

<a id="eq-purity-1-3"></a>

$$
\omega_\Psi(a)=
\sum_\alpha\operatorname{Tr}(\sigma_\alpha a_\alpha),
\qquad
 a=\bigoplus_\alpha(a_\alpha\otimes I_{W_\alpha}).
\tag{1.3}
$$

The blocks $\sigma_\alpha$ are subnormalized; their traces, rather than each block separately, sum to one. The matrix $\sigma=\bigoplus_\alpha\sigma_\alpha$ is a trace-one density on the abstract visible space $\bigoplus_\alpha V_\alpha$. Passing from this abstract visible density to a density in the represented algebra on $H$ requires the multiplicity factors.

For example, with the ordinary represented trace on $H$, the trace-preserving conditional expectation of $P_\Psi=|\Psi\rangle\langle\Psi|$ into $\mathcal A$ is instead

$$
\bigoplus_\alpha
\left(\sigma_\alpha\otimes\frac{I_{W_\alpha}}{m_\alpha}\right).
\tag{1.4}
$$

The multiplicity factors cannot be dropped when comparing these two matrix representations.

<a id="statement-purity-1-3"></a>

**命题 1.3（Classification of the functionals at the declared interface）。** Every state of $\mathcal A$ has one unique family $\sigma_\alpha\succeq0$ with $\sum_\alpha\operatorname{Tr}\sigma_\alpha=1$ representing it by (1.3). Conversely each such family defines a state.

**证明。** Restrict the functional to each central sector and apply finite matrix trace duality. Positivity gives positive blocks and normalization gives total trace one; trace duality also gives uniqueness. The converse follows directly from (1.3). This classifies functionals, while §3 separately determines which have vector lifts in the fixed $H$. $\square$

## 2. When a globally pure vector has a pure visible restriction

<a id="statement-purity-2-1"></a>

**定理 2.1（Central concentration and one Schmidt direction）。** The state $\omega_\Psi$ is pure on $\mathcal A$ if and only if exactly one sector $\alpha$ has $p_\alpha=1$ and its normalized density $\rho_\alpha$ has rank one. Equivalently,

<a id="eq-purity-2-1"></a>

$$
\Psi=u\otimes v
\quad\text{in one sector }V_\alpha\otimes W_\alpha,
\qquad\lVert u\rVert=\lVert v\rVert=1.
\tag{2.1}
$$

**证明。** If two central weights are positive, conditioning on one central projection gives a nontrivial decomposition into distinct states. If only one sector is populated but its density has at least two positive eigenvalues, the spectral decomposition again decomposes the functional nontrivially.

Conversely, a rank-one density in one sector is extreme. In a positive convex decomposition, each summand has zero expectation on the positive effects outside that sector and outside its one-dimensional support. Positivity therefore forces both summands into the same rank-one visible support, and trace one makes them identical. Finally, the Schmidt rank of $\Psi_\alpha$ equals $\operatorname{rank}\sigma_\alpha$, giving (2.1). $\square$

There are two independent sources of visible mixture: weights across distinguishable central sectors and Schmidt rank inside a sector. Both refer to one specified vector and one specified observation interface.

<a id="statement-purity-2-2"></a>

**推论 2.2（Interfaces preserving purity of every global vector）。** Every unit vector in $H$ restricts to a pure state of $\mathcal A$ if and only if

$$
\mathcal A=\mathbb C I_H
\quad\text{or}\quad
\mathcal A=B(H).
\tag{2.2}
$$

**证明。** Two central sectors admit a unit vector with half its squared norm in each, whose restriction is mixed. In a single sector with $n\ge2$ and $m\ge2$, a two-term equal Schmidt vector has mixed restriction. The remaining single-sector cases are $n=1$, giving $\mathbb C I_H$, and $m=1$, giving $B(H)$; each has the asserted property. In dimension one these algebras coincide. $\square$

Thus the purity of represented global vectors alone does not select a nontrivial intermediate observable algebra.

## 3. Pure lifts and their exact invisible response fibre

<a id="statement-purity-3-1"></a>

**定理 3.1（Pure-lift existence in the fixed carrier）。** A state family $\{\sigma_\alpha\}$ has a unit-vector realization in the particular represented $H$ of (1.1) if and only if

<a id="eq-purity-3-1"></a>

$$
r_\alpha:=\operatorname{rank}\sigma_\alpha\le m_\alpha
\quad\text{for every }\alpha.
\tag{3.1}
$$

**证明。** Necessity is the Schmidt-rank bound in each sector. For sufficiency, diagonalize each nonzero block as

$$
\sigma_\alpha=\sum_{j=1}^{r_\alpha}
\lambda_{\alpha j}|u_{\alpha j}\rangle\langle u_{\alpha j}|,
$$

choose $r_\alpha$ orthonormal vectors $v_{\alpha j}$ in $W_\alpha$, and set

<a id="eq-purity-3-2"></a>

$$
\Psi=\bigoplus_\alpha\sum_{j=1}^{r_\alpha}
\sqrt{\lambda_{\alpha j}}\,
 u_{\alpha j}\otimes v_{\alpha j}.
\tag{3.2}
$$

Its squared norm is the total block trace, hence one, and its restrictions are the prescribed blocks. This is ordinary purification in each central sector. $\square$

<a id="statement-purity-3-2"></a>

**定理 3.2（Equality of visible responses is a commutant-unitary fibre）。** For unit vectors $\Psi,\Phi$ in this same represented $H$,

<a id="eq-purity-3-3"></a>

$$
\begin{aligned}
\omega_\Psi|_{\mathcal A}=\omega_\Phi|_{\mathcal A}
&\quad\Longleftrightarrow\quad
\Phi=U'\Psi\ \text{for a unitary }U'\in\mathcal A',\\
\mathcal A'
&=\bigoplus_\alpha
\bigl(I_{V_\alpha}\otimes B(W_\alpha)\bigr).
\end{aligned}
\tag{3.3}
$$

**证明。** A commuting unitary preserves all expectations. Conversely, equality of all block-matrix expectations gives the same $\sigma_\alpha$. Choose a common eigenbasis for each of these blocks. Both vectors then have expansions (3.2) with identical nonzero coefficients and left vectors, but possibly different orthonormal right frames. In each $W_\alpha$, map one right frame to the other and extend to a unitary. Their block sum gives $U'$. Zero sectors impose no condition; independent central-sector phases are included in these unitaries. Commuting first with central projections and then with every left matrix unit gives the displayed formula for $\mathcal A'$. $\square$

This is equality of current response fibres. It neither supplies $U'$ as a native operation nor makes it invisible to an enlarged future interface. A future test outside $\mathcal A$ changes the observation task.

<a id="statement-purity-3-3"></a>

**命题 3.3（Dimension of the pure-completion ray fibre）。** Fix the left eigenvectors in (3.2), omit zero sectors and assume the lift condition (3.1). The vector-ray fibre is

<a id="eq-purity-3-4"></a>

$$
\left(\prod_{\alpha:p_\alpha>0}
\operatorname{St}_{\mathbb C}(r_\alpha,m_\alpha)\right)/U(1),
\qquad
\dim_{\mathbb R}=
\sum_{\alpha:p_\alpha>0}
(2m_\alpha r_\alpha-r_\alpha^2)-1.
\tag{3.4}
$$

Here $\operatorname{St}_{\mathbb C}(r,m)$ denotes ordered orthonormal complex $r$-frames in $\mathbb C^m$. The single quotiented phase multiplies all populated sectors together.

**证明。** With the left eigenbasis fixed, every lift is uniquely specified by its right orthonormal frames. Each right vector is recovered by contraction against its fixed left vector and division by the specified positive square root. Thus eigenvalue degeneracy creates no additional quotient.

A complex $r$-frame has $2mr$ real coordinates and $r^2$ independent real orthonormality constraints. At a frame $F$, the derivative of $F^*F$ sends the variation $FH/2$ to any given Hermitian matrix $H$, proving independence. The global $U(1)$ action is free, so its quotient subtracts one real dimension. This proves (3.4). $\square$

<a id="statement-purity-3-4"></a>

**推论 3.4（Uniqueness of a pure lift inside the fixed carrier）。** When a pure lift exists, its ray is unique exactly when one sector is populated, its visible rank is one and that sector has $m_\alpha=1$.

**证明。** In this case the only right-frame freedom is one common phase. In every other case, either a relative central-sector phase or a change of right frame produces a distinct ray with the same visible functional. This concerns the fixed represented $H$, rather than arbitrary larger completions. $\square$

<a id="statement-purity-3-5"></a>

**命题 3.5（Every density extension of a pure visible state）。** If the visible state is pure in sector $\alpha$ and direction $u$, every density operator on $H$ extending it has the exact form

<a id="eq-purity-3-5"></a>

$$
R=|u\rangle\langle u|\otimes\tau
\quad\text{in that sector},
\qquad\tau\succeq0,\quad\operatorname{Tr}\tau=1.
\tag{3.5}
$$

Its extension to all of $B(H)$ is unique if and only if $m_\alpha=1$.

**证明。** The visible projection $Q=P_u\otimes I_{W_\alpha}$, extended by zero to other sectors, has expectation one. If $R\succeq0$ has trace one, then

$$
\operatorname{Tr}(R(I-Q))=0
\quad\Longrightarrow\quad
(I-Q)R^{1/2}=0
\quad\Longrightarrow\quad R=QRQ.
$$

The support is therefore $u\otimes W_\alpha$, giving (3.5). Every such density has the stated visible response, and its invisible density is unique precisely in multiplicity dimension one. A pure visible response alone does not select an invisible record state when $m_\alpha>1$. $\square$

## 4. Cyclic dimension belongs to the specified state and algebra

<a id="statement-purity-4-1"></a>

**定理 4.1（Cyclic space and finite GNS dimension）。** For the vector in (3.2), let $S_\alpha$ be the span of its right Schmidt vectors. Then

<a id="eq-purity-4-1"></a>

$$
\begin{aligned}
K_\Psi
&=\operatorname{span}\{a\Psi:a\in\mathcal A\}
=\bigoplus_\alpha(V_\alpha\otimes S_\alpha),\\
\dim K_\Psi&=\sum_\alpha n_\alpha r_\alpha.
\end{aligned}
\tag{4.1}
$$

This is also the dimension of the cyclic GNS representation of this functional. In the fixed faithful block representation (1.1), $\Psi$ is cyclic for all of $H$ exactly when $r_\alpha=m_\alpha$ in every sector; in particular no sector of $H$ may be unpopulated.

**证明。** Every left action stays in the displayed space. Conversely, a central projection isolates each sector. For each positive Schmidt coefficient, the left matrix unit $|x\rangle\langle u_{\alpha j}|$ sends its component to

$$
\sqrt{\lambda_{\alpha j}}\,x\otimes v_{\alpha j}.
$$

Varying $x,j$ spans the summand, proving (4.1).

The map $[a]\mapsto a\Psi$ identifies the finite GNS quotient with $K_\Psi$: its inner product is $\omega_\Psi(a^*b)$ and its zero vectors are exactly the GNS null space. Hence the displayed dimension is the least dimension of a cyclic representation of this particular functional. The representation may act as zero on unpopulated central sectors; the dimension does not claim that the actual represented carrier $H$ is minimal. Finally, $S_\alpha=W_\alpha$ in every sector is exactly the stated full-carrier cyclicity condition. $\square$

<a id="statement-purity-4-2"></a>

**推论 4.2（Commutant criterion on the cyclic space）。** On $K_\Psi$, the represented commutant is

$$
\bigoplus_{\alpha:p_\alpha>0}
\bigl(I_{n_\alpha}\otimes M_{r_\alpha}(\mathbb C)\bigr).
\tag{4.2}
$$

It consists only of scalars exactly when one sector is populated and its visible rank is one.

**证明。** Apply the central-projection and left-matrix-unit argument of Theorem 3.2 to the representation on $\bigoplus_\alpha(V_\alpha\otimes S_\alpha)$. Multiple populated sectors give independent scalar central actions, and a populated block with $r_\alpha>1$ gives a non-scalar right matrix action. The remaining case has one multiplicity-one block. This is the standard purity/irreducibility criterion in the explicit finite setting. $\square$

Thus a cyclic GNS unit vector can encode a mixed functional: cyclicity does not replace extremality. The integer $\sum_\alpha n_\alpha r_\alpha$ counts mathematical Hilbert dimension of that cyclic representation. It is no bound on preparation cost, physical memory acquisition, operational control complexity or spacetime dimension.

## 5. Exact stability of visible purity and global vector approximation

<a id="statement-purity-5-1"></a>

**定义 5.1（Distance for the complete effect interface）。** For two states of $\mathcal A$, represented by their subnormalized visible blocks, set

<a id="eq-purity-5-1"></a>

$$
\begin{aligned}
D_{\mathcal A}(\sigma,\tau)
&=\frac12\sum_\alpha
\lVert\sigma_\alpha-\tau_\alpha\rVert_1\\
&=\sup_{\substack{0\le a\le I\\a\in\mathcal A}}
|\omega_\sigma(a)-\omega_\tau(a)|.
\end{aligned}
\tag{5.1}
$$

The equality follows by choosing the positive spectral projection of the block-diagonal trace-zero difference. It presupposes the complete effect interval in §1; an actually restricted menu can distinguish less.

<a id="statement-purity-5-2"></a>

**定理 5.2（Exact nearest-pure distances）。** Set

$$
\eta=\max_\alpha\lambda_{\max}(\sigma_\alpha),
\qquad
\mathcal F_{\mathcal A}
=\{\Phi\in H:\lVert\Phi\rVert=1,
\ \omega_\Phi|_{\mathcal A}\text{ is pure}\}.
$$

For the globally pure input $P_\Psi$ and this fixed block interface,

<a id="eq-purity-5-2"></a>

$$
\begin{aligned}
\min_{\nu\in\operatorname{Pure}(\mathcal A)}
D_{\mathcal A}(\omega_\Psi,\nu)&=1-\eta,\\
\min_{\Phi\in\mathcal F_{\mathcal A}}
D(P_\Psi,P_\Phi)&=\sqrt{1-\eta}.
\end{aligned}
\tag{5.2}
$$

**证明。** A pure visible state has density $P_u$ in one sector. Testing its represented effect $P_u\otimes I_{W_\alpha}$ bounds the visible distance below by

$$
1-\langle u,\sigma_\alpha u\rangle\ge1-\eta.
$$

Choose a top eigenvector in a maximizing sector. The two visible densities then commute, and the sum of absolute eigenvalue differences is $2(1-\eta)$, proving the first equality and its attainment.

For the second equality, Theorem 2.1 says that $\Phi$ must be a product vector in a single sector. The largest squared overlap with such vectors is $\eta$, by the largest Schmidt coefficient in each sector. Directly, for fixed unit $u\in V_\alpha$, maximization over the right unit vector gives

$$
\max_{\lVert v\rVert=1}
|\langle u\otimes v,\Psi_\alpha\rangle|^2
=\lVert(\langle u|\otimes I)\Psi_\alpha\rVert^2
=\langle u,\sigma_\alpha u\rangle.
$$

Maximization over $u$ and the sectors gives $\eta$. Two rank-one densities have half trace distance

$$
D(P_\Psi,P_\Phi)
=\sqrt{1-|\langle\Psi,\Phi\rangle|^2},
$$

as diagonalization on their two-dimensional span shows. This proves the second equality, including attainment. $\square$

Consequently, for $\varepsilon\ge0$, visible distance at most $\varepsilon$ from the pure-state set is equivalent to the existence of a vector with pure $\mathcal A$ restriction within global half trace distance $\sqrt\varepsilon$, for this globally pure input and fixed block interface. The square-root exponent and coefficient are exact. No noise estimate from an incomplete finite menu is substituted for (5.1).

## 6. One cyclic vector can represent a mixed functional

<a id="statement-purity-6-1"></a>

**例 6.1（Bell–Schmidt mechanism at three interfaces）。** Let

$$
H=\mathbb C^2\otimes\mathbb C^2,
\qquad\mathcal A=M_2(\mathbb C)\otimes I_2,
\qquad
\Psi=\sqrt t\,|00\rangle+\sqrt{1-t}\,|11\rangle,
\qquad0<t<1.
\tag{6.1}
$$

The complete visible state is $\operatorname{diag}(t,1-t)$, with rank two and cyclic dimension $2\cdot2=4$. The GNS cyclic vector is one ray in that representation, while the functional on $\mathcal A$ is mixed. Right-factor unitary changes preserve its visible state.

Here $\eta=\max(t,1-t)$, so the exact visible distance to pure states is $\min(t,1-t)$ and the global distance to $\mathcal F_{\mathcal A}$ is $\sqrt{\min(t,1-t)}$. At $t=1/2$ these are respectively $1/2$ and $1/\sqrt2$.

Reduce the interface to the diagonal left algebra. The same two visible weights remain, and the functional is again mixed, now through central-sector mixture with one-dimensional left blocks. Enlarge the interface to all of $B(H)$, and the vector state is pure. These are three declared interfaces on the same carrier, with different purity classifications.

This reuses the Bell/Schmidt mechanism, rather than supplying a new Bell counterexample. The block-fibre and exact distance formulas identify the data on which that mechanism depends.

## 7. Generating an algebra does not supply all its readouts

<a id="statement-purity-7-1"></a>

**例 7.1（The two-observable disk and its larger algebra closure）。** On one qubit, take the self-adjoint observable span of $I,X,Z$. The image of all qubit density states under the two means is exactly

<a id="eq-purity-7-1"></a>

$$
(x,z),\qquad x^2+z^2\le1.
\tag{7.1}
$$

Necessity follows from the Bloch ball, and $\rho=(I+xX+zZ)/2$ witnesses sufficiency. The orthogonal pure states $|+y\rangle$ and $|-y\rangle$ both give the disk centre. This response is not extreme: it is the midpoint of $(1,0)$ and $(-1,0)$. Nevertheless the mathematically generated $*$-algebra of $X$ and $Z$ is all of $M_2(\mathbb C)$, since their product supplies $Y$ up to a scalar factor.

The complete-algebra criterion of §2 applies only if the generated algebra's effects belong to the declared observation contract. Generating $Y$ in a calculation does not install a $Y$ measurement. This disk is the response image of the common qubit model, rather than the larger square obtained by separately normalizing arbitrary binary menus without a shared-state condition. Compatibility, algebra closure and actual control access are distinct conditions.

## 8. Relation to AURIC sources and the remaining operational interfaces

The source pin is `6b24b302e37ea2ead041655259d42ef4866d3249`. V78, *AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md*, Definition 3.4, Theorems 7.2–7.3 and §7.1 define visible states and classify pure states for a complete effect interface. Its Theorem 10.2 supplies finite purification with the minimum record rank; Theorem 14.1 supplies the record Gram-rank mechanism. These provide the factor-case foundation reused here.

V58, *AURIC_RELATIONAL_AXIOMS_COMMON_COMPLEX_PHASE_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V58.md*, §7 and Explanation 7.2 already distinguish GNS uniqueness for a specified functional from uniqueness of the actual state, and a global unit vector from purity on the original observable algebra. The explicit blocks, fibres and distances above retain these distinctions.

The existing declaration `bell_pure_state_has_maximally_mixed_marginal` in `D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal.lean` supplies the named Bell-marginal result. `D5/S3/Quantum/Foundation/FiniteDensityPurification.lean` supplies canonical finite density purification. These named interfaces are source references; this conditional paper application makes no claim of a current build or fresh Lean verification.

Finite represented algebra blocks, Schmidt purification, commuting-unitary freedom and cyclic GNS representations are standard mathematics. General purification and trace-distance background is J. Watrous, [*The Theory of Quantum Information*, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). The displayed block and distance calculations are conditional applications. No priority or originality claim is made for their packaging.

For the $\Omega/\omega$ distinction, $\Omega$ supplies the stipulated structures, legal tests and operations, while $\omega$ is a functional relative to that interface. Choosing a pure vector representation neither selects $\omega$ nor proves that the actual interface is all of $B(H)$. If future histories return and reveal a multiplicity degree of freedom, their tests enlarge the interface; its purity and fibre calculation must use that enlarged task.

Shared-source independence, source availability, native reference controls and clean reference return require their own relations. The N2 shared-history dimension budget concerns the rank of a residual cross-wing relation map; $r_\alpha$ here is a density support rank. Relating them requires a supplied bridge between those objects. The cyclic dimension in (4.1) is not identified with that budget and settles none of these physical acquisition questions. The displayed results remain conditional paper deductions, without Lean compilation or physical validation.

## 追加锚（本行以下为增补区）


## 9. Current observations and the future question have separate domains

The following is a conditional paper application of standard duality and algebra tools. Finite complex state spaces, declared completely positive operations, their effect menus and complete records are inputs. Their mathematical representation does not establish native availability, a physical reference service or a quantum-origin claim.

<a id="statement-future-9-1"></a>

**定义 9.1（Current response equivalence and future width）。** Let $H$ be a finite-dimensional nonzero complex Hilbert space. Let $W\subseteq\operatorname{Herm}(H)$ be a real linear subspace containing $I$. It can be the real span of a declared effect menu; multiplication closure is not assumed. Define

<a id="eq-future-9-1"></a>

$$
\rho\sim_W\sigma
\quad\Longleftrightarrow\quad
\operatorname{Tr}((\rho-\sigma)w)=0
\quad\text{for every }w\in W.
\tag{9.1}
$$

All state quantifiers refer to the full density cone unless a smaller domain is explicitly specified. Comparing all allowed realizations with identical current responses is stronger than following one actual state; one trajectory alone supplies no such uniform conclusion.

For a Hermitian future readout $B$, put

<a id="eq-future-9-2"></a>

$$
\begin{aligned}
\Delta_W(B)
&=\max_{\rho\sim_W\sigma}
|\operatorname{Tr}(B(\rho-\sigma))|,\\
d_W(B)&=\min_{b\in W}\lVert B-b\rVert_{\mathrm{op}}.
\end{aligned}
\tag{9.2}
$$

For an effect $B$, $\Delta_W(B)\in[0,1]$. It is a possible difference between future event probabilities in two density realizations sharing every current response. Existence of an extremal mathematical pair does not provide devices that prepare it or measure $B$.

## 10. Exact fibre width is twice the missing predictor norm

<a id="statement-future-10-1"></a>

**定理 10.1（Exact finite response-fibre width）。** For every $B\in\operatorname{Herm}(H)$,

<a id="eq-future-10-1"></a>

$$
\Delta_W(B)=2d_W(B).
\tag{10.1}
$$

If $d_W(B)>0$, an attaining pair can be chosen with orthogonal supports.

**证明。** For any $b\in W$ and $\rho\sim_W\sigma$, subtract $b$ from $B$ and use $\lVert\rho-\sigma\rVert_1\le2$. Then

$$
|\operatorname{Tr}(B(\rho-\sigma))|
\le2\lVert B-b\rVert_{\mathrm{op}},
$$

which proves the upper bound.

For the reverse bound, suppose $d_W(B)>0$. Finite-dimensional real Hahn–Banach duality on $\operatorname{Herm}(H)/W$ supplies a real norm-one functional annihilating $W$ and taking $B$ to $d_W(B)$. Its trace representative is a Hermitian $X$. The operator-norm dual on Hermitian matrices is trace norm: diagonalizing $X$ and testing its spectral sign gives the dual norm $\operatorname{Tr}|X|$. Consequently $\lVert X\rVert_1=1$. Since $I\in W$, $\operatorname{Tr}X=0$, so its positive and negative spectral parts each have trace $1/2$.

Set $\rho=2X_+$ and $\sigma=2X_-$. They are density matrices with orthogonal supports, their difference annihilates $W$, and

$$
\operatorname{Tr}(B(\rho-\sigma))=2d_W(B).
$$

If $d_W(B)=0$, the upper bound already gives the equality. The relevant extrema exist in finite dimension. $\square$

<a id="statement-future-10-2"></a>

**推论 10.2（Exact prediction criterion and scalar minimax interpretation）。** Current responses determine the expectation of $B$ for every density matrix exactly when $B\in W$. Moreover $d_W(B)$ is the optimal worst scalar error among affine current-response predictors $\operatorname{Tr}(\rho b)$ with $b\in W$:

$$
\sup_\rho
|\operatorname{Tr}(\rho(B-b))|
=\lVert B-b\rVert_{\mathrm{op}}.
\tag{10.2}
$$

**证明。** The first assertion follows from (10.1), since $W$ is closed in finite dimension. The second follows by testing the largest absolute eigenvalue of the Hermitian matrix $B-b$. Minimizing gives (9.2). Here $b$ is a mathematical predictor; the optimization does not make it an available effect or a complete-positive state update. $\square$

The witness in Theorem 10.1 is one common state pair. Independently optimized marginal extrema are not combined into a fictitious joint realization.

## 11. Pure fibres detect every closure failure of a complete observable algebra

Specialize to $W=\mathcal A_{\mathrm{sa}}$ for the represented unital $*$-algebra

<a id="eq-future-11-1"></a>

$$
H=\bigoplus_\alpha(V_\alpha\otimes W_\alpha),
\qquad
\mathcal A=\bigoplus_\alpha
\bigl(B(V_\alpha)\otimes I_{W_\alpha}\bigr).
\tag{11.1}
$$

Write $d_{\mathcal A}$ for distance to $\mathcal A_{\mathrm{sa}}$. For unit vectors, let $\delta_{\mathcal A}(B)$ be the largest expectation difference among pairs with the same restriction to $\mathcal A$.

<a id="statement-future-11-1"></a>

**命题 11.1（Pure-fibre commutant formula and bounds）。** For Hermitian $B$,

<a id="eq-future-11-2"></a>

$$
\begin{aligned}
\delta_{\mathcal A}(B)
&=\max_{U'\in\mathcal U(\mathcal A')}
\lVert B-U'^*BU'\rVert_{\mathrm{op}},\\
d_{\mathcal A}(B)
&\le\delta_{\mathcal A}(B)
\le2d_{\mathcal A}(B).
\end{aligned}
\tag{11.2}
$$

**证明。** Equality of the restrictions of $\Psi$ and $\Phi$ is equivalent to $\Phi=U'\Psi$ for a commutant unitary, as in Theorem 3.2. Explicitly, choose a common left eigenbasis for each reduced sector density. The right orthonormal Schmidt frames differ by a unitary on the corresponding $W_\alpha$, including central-sector phases. Maximizing a Hermitian expectation over $\Psi$ then gives the norm in (11.2).

Average $U'^*BU'$ over the compact unitary group of $\mathcal A'$. The resulting trace-preserving conditional expectation belongs to $\mathcal A$ and has block formula

<a id="eq-future-11-3"></a>

$$
E_{\mathcal A}(B)=
\bigoplus_\alpha
\left(
\operatorname{Tr}_{W_\alpha}(P_\alpha BP_\alpha)
\otimes\frac{I_{W_\alpha}}{m_\alpha}
\right).
\tag{11.3}
$$

This is unital completely positive as a mathematical average of unitary conjugations. The average gives

$$
d_{\mathcal A}(B)
\le\lVert B-E_{\mathcal A}(B)\rVert_{\mathrm{op}}
\le\delta_{\mathcal A}(B).
$$

For the other bound, subtract any $b\in\mathcal A_{\mathrm{sa}}$, which commutes with every $U'$, and apply the triangle inequality. $\square$

Thus pure pairs detect every nonzero failure, but no equality between $\delta_{\mathcal A}(B)$ and $2d_{\mathcal A}(B)$ is asserted in general.

<a id="statement-future-11-2"></a>

**命题 11.2（Exact pure witness with an unobserved purification carrier）。** Supply a carrier $R$ of dimension $\dim H$, excluded from current tests. On $H\otimes R$, pure vectors agreeing on $\mathcal A\otimes I_R$ can attain future expectation difference $2d_{\mathcal A}(B)$ for $B\otimes I_R$, and cannot exceed it.

**证明。** Purify the attaining mixed pair of Theorem 10.1 on $H\otimes R$. The purifications agree on $\mathcal A\otimes I_R$ and retain the same $B\otimes I_R$ expectations. Conversely, reducing any admissible pure pair to $H$ gives a pair in (9.2), so (10.1) bounds its difference. $\square$

Adding joint $\mathcal A$–$R$ tests changes the equivalence relation. This existence statement neither acquires those purifications nor supplies a clean-return reference protocol.

## 12. A channel descends precisely when its future observables remain closed

<a id="statement-future-12-1"></a>

**定理 12.1（Full-state autonomy and Heisenberg closure）。** Let $\Phi$ be a completely positive trace-preserving channel on $B(H)$, with unital completely positive Heisenberg dual $F$. Then

<a id="eq-future-12-1"></a>

$$
\begin{gathered}
\rho|_{\mathcal A}=\sigma|_{\mathcal A}
\ \Longrightarrow\
\Phi(\rho)|_{\mathcal A}=\Phi(\sigma)|_{\mathcal A}
\quad\text{for all density matrices }\rho,\sigma\\
\Longleftrightarrow\quad F(\mathcal A)\subseteq\mathcal A.
\end{gathered}
\tag{12.1}
$$

On closure, $T=F|_{\mathcal A}$ is unital completely positive in the inherited matrix orders and its dual defines an affine update on the restricted states. Testing constancy on every currently equivalent pure-vector pair already implies the same closure.

**证明。** A future expectation of $a\in\mathcal A$ is the current expectation of $F(a)$. Apply Theorem 10.1 to each self-adjoint $a$ for both directions of (12.1); complex linearity extends the inclusion to all of $\mathcal A$. Restricting a unital completely positive map to a preserved algebra retains its matrix-order positivity and unit. For the pure-pair version, Proposition 11.1 makes zero pure-fibre width equivalent to $F(a)\in\mathcal A_{\mathrm{sa}}$. $\square$

For a general real unital space $W$, the corresponding one-step expectation criterion is $F(W)\subseteq W$. It does not require replacing $W$ by the $*$-algebra it generates. The existing future-statistics closure result supplies the minimal linear predictor space for all finite iterates. Computing an algebraic completion may add tests and has a different operation contract.

<a id="statement-future-12-2"></a>

**定理 12.2（Exact hidden one-step distinguishability）。** For the complete $\mathcal A$ interface,

<a id="eq-future-12-2"></a>

$$
\begin{aligned}
L_{\mathcal A}(\Phi)
&:=\max_{\rho|_{\mathcal A}=\sigma|_{\mathcal A}}
D_{\mathcal A}(\Phi(\rho),\Phi(\sigma))\\
&=2\max_{\substack{a\in\mathcal A\\0\le a\le I}}
d_{\mathcal A}(F(a)).
\end{aligned}
\tag{12.2}
$$

Here $D_{\mathcal A}$ is the operational half trace distance of restricted states, namely their largest probability difference over $\mathcal A$ effects. The value lies in $[0,1]$ and is attained by one pair and one effect.

**证明。** Interchange the two compact maxima, over a current-equivalent pair and an $\mathcal A$ effect. Theorem 10.1 evaluates the pair maximum for the pulled-back Hermitian observable $F(a)$ as $2d_{\mathcal A}(F(a))$. $\square$

This is distinguishability under the stated measurement interface, rather than a diamond distance or implementation cost.

## 13. Complete recorded autonomy requires every branch, including failure

Let $\{\Phi_x\}$ be a finite complete completely positive instrument on $B(H)$, so $\sum_x\Phi_x$ is trace preserving. All failure and rejection outcomes are included among the labels $x$. Let $F_x$ be the Heisenberg branch maps. The complete recorded output contains $x$ and the restricted subnormalized state of $\Phi_x(\rho)$ on $\mathcal A$.

<a id="statement-future-13-1"></a>

**定理 13.1（Branchwise closure for the recorded state quotient）。** This complete recorded output is autonomous on current $\mathcal A$ states exactly when

<a id="eq-future-13-1"></a>

$$
F_x(\mathcal A)\subseteq\mathcal A
\quad\text{for every }x.
\tag{13.1}
$$

**证明。** Test each branch against every $\mathcal A$ effect and use Theorem 10.1. Testing $I$ retains its branch probability. Closure gives induced completely positive subunital maps on $\mathcal A$ whose sum is unital; their duals provide the subnormalized poststates. Normalization occurs only after retaining the appropriate nonzero branch probability. Conversely these restrictions make all recorded branch responses functions of the current restricted state. Invariance of the summed map alone is weaker. $\square$

<a id="statement-future-13-2"></a>

**定理 13.2（Exact recorded-fibre gap with a common witness pair）。** Let $L_{\mathrm{rec}}$ be the largest complete flag-and-$\mathcal A$ operational half trace distance over pairs satisfying $\rho|_{\mathcal A}=\sigma|_{\mathcal A}$. Then

<a id="eq-future-13-2"></a>

$$
L_{\mathrm{rec}}(\{\Phi_x\})
=2\max_{\substack{a_x\in\mathcal A\\0\le a_x\le I}}
d_{\mathcal A}\left(\sum_xF_x(a_x)\right).
\tag{13.2}
$$

**证明。** A complete flag-and-$\mathcal A$ effect chooses a separate effect $a_x$ in each classical block. Its probability difference is

$$
\left|\sum_x
\operatorname{Tr}\bigl(a_x(\Phi_x(\rho)-\Phi_x(\sigma))\bigr)\right|.
$$

The pulled-back effect is $B=\sum_xF_x(a_x)$, with $0\le B\le I$ by instrument completeness. Maximize its probability difference over one current fibre by (10.1), then maximize over the block effects. This gives (13.2). The witness is one common state pair for the whole sum $B$; optimizing branches separately on different pairs is a different objective. $\square$

Choosing all $a_x$ equal recovers the nonselective gap as a lower bound; independently chosen $a_x$ can reveal a strictly larger gap. These formulas use the full normalized output with complete flags. Equal normalized successful poststates, without equal success probabilities, do not establish (13.1) or a complete recorded-state quotient.

## 14. One pure pair exhibits two ways for a hidden phase to return

<a id="statement-future-14-1"></a>

**例 14.1（A reversible return and a recorded-only return）。** On two qubits $S,E$, take $\mathcal A=M_2(S)\otimes I_E$ and

<a id="eq-future-14-1"></a>

$$
|\Psi_\pm\rangle=
\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
\tag{14.1}
$$

Both marginals, on $S$ and on $E$, are $I/2$, while the global pure vectors are orthogonal. Thus both one-party marginals agree and the joint phase differs.

First declare a joint controlled-NOT with $S$ as control,

$$
U=P_0\otimes I+P_1\otimes X.
$$

It sends the pair to $|+\rangle_S\otimes|0\rangle_E$ and $|-\rangle_S\otimes|0\rangle_E$. A terminal $X_S$ test perfectly distinguishes them. Its positive effect pulls back to

<a id="eq-future-14-2"></a>

$$
B=U^*\left(\frac{I+X_S}{2}\otimes I_E\right)U
=\frac{I+X_S\otimes X_E}{2}.
\tag{14.2}
$$

The current predictor $I/2$ is within operator norm $1/2$ of $B$. The probability difference one on (14.1) and Theorem 10.1 give the reverse bound, so $d_{\mathcal A}(B)=1/2$ exactly. Global unitarity preserves each source spectrum and their distinguishability, while the chosen local summary fails autonomy.

Now declare a different operation: the projective parity instrument

$$
P_+=\frac{I+X_S\otimes X_E}{2},\qquad
P_-=I-P_+,\qquad
\Phi_\pm(\rho)=P_\pm\rho P_\pm.
$$

Its nonselective Heisenberg action is

<a id="eq-future-14-3"></a>

$$
\sum_{s=\pm}P_s(a\otimes I_E)P_s
=\frac12(a+X_SaX_S)\otimes I_E.
\tag{14.3}
$$

Consequently the nonselective $S$ update is the same dephasing channel for every joint input, and (12.2) is zero. But the plus-branch effect on $I$ is $P_+\notin\mathcal A$. The complete outcome is plus with probability one on $\Psi_+$ and minus with probability one on $\Psi_-$. Thus the recorded gap (13.2) is exactly one. On each source's probability-one branch, the normalized $S$ marginal remains $I/2$; in this operation the distinguishing response lies entirely in the outcome flag.

The pair, controlled-NOT and parity measurement are standard finite quantum examples. They distinguish (12.1) from (13.1) using the same common pair with identical marginals and an exact norm reading. The joint controls are declared premises, rather than operations obtained from a local $X$ menu.

## 15. A completely positive predictor can control a bounded future horizon

<a id="statement-future-15-1"></a>

**定理 15.1（Finite-horizon scalar observation budget）。** For a sequence of completely positive trace-preserving channels with Heisenberg maps $F_j$, use the mathematical conditional expectation (11.3) to define

<a id="eq-future-15-1"></a>

$$
T_j=E_{\mathcal A}F_j|_{\mathcal A},
\qquad
\varepsilon_j=
\max_{\substack{a\in\mathcal A\\0\le a\le I}}
\lVert F_j(a)-T_j(a)\rVert_{\mathrm{op}}.
\tag{15.1}
$$

Each $T_j$ is unital completely positive on $\mathcal A$. For an $\mathcal A$ effect $a$, in the physical Heisenberg order,

<a id="eq-future-15-2"></a>

$$
\lVert F_1\cdots F_L(a)-T_1\cdots T_L(a)\rVert_{\mathrm{op}}
\le\sum_{j=1}^L\varepsilon_j.
\tag{15.2}
$$

The terminal probability error is at most $\min(1,\sum_j\varepsilon_j)$ for every density input. Two current-equivalent states differ at that terminal test by at most $\min(1,2\sum_j\varepsilon_j)$.

**证明。** Replace factors from right to left. The telescoping summands are

$$
F_1\cdots F_{j-1}(F_j-T_j)
T_{j+1}\cdots T_L(a).
$$

The right suffix stays an $\mathcal A$ effect, and the left factors are unital positive operator-norm contractions. Each summand therefore has norm at most $\varepsilon_j$, proving (15.2). Evaluation in any density gives the scalar probability bound, truncated at one. The compressed terminal effect belongs to $\mathcal A$, so current-equivalent states have identical predicted expectations; applying the one-state error bound twice gives the second estimate. $\square$

These are finite-horizon scalar observation bounds. $E_{\mathcal A}$ constructs a predictor; no projection, physical reset or state reacquisition is applied to the actual source. Repeated ready preparation and an unbounded-horizon guarantee are outside this conclusion. A channel norm retaining an arbitrary extra reference requires its own matrix-amplified error budget.

## 16. Reversible closure of the full algebra has a rigid operation form

<a id="statement-future-16-1"></a>

**定理 16.1（Finite represented-algebra unitary normalizer）。** For a fixed unitary $U$ on $H$, the inclusion $U^*\mathcal AU\subseteq\mathcal A$ is equality. Such a $U$ permutes only central sectors with identical pairs $(n_\alpha,m_\alpha)$ and has product form $V_\alpha\otimes W_\alpha$ between matching sectors.

**证明。** Finite dimension turns the inclusion into equality, so conjugation restricts to a $*$-automorphism. It permutes minimal central projections. The dimensions of the corresponding simple matrix algebras force $n_\alpha=n_\beta$, and their represented Hilbert ranks then force $m_\alpha=m_\beta$.

Choose a left unitary implementing each matrix-algebra isomorphism. Its inverse times the corresponding block of $U$ commutes with every left matrix unit. This commutant is $I\otimes B(W)$, so the remaining unitary acts only on the multiplicity factor, giving the product form. The one-sector conclusion is V38 Theorem 8.1 and is reused here. $\square$

<a id="statement-future-16-2"></a>

**推论 16.2（Generators of continuous reversible closure）。** A continuous one-parameter group $U_t=e^{-itH_0}$ preserves $\mathcal A$ for every $t$ exactly when

<a id="eq-future-16-1"></a>

$$
H_0=\bigoplus_\alpha
\left(h_\alpha\otimes I+I\otimes k_\alpha\right),
\qquad h_\alpha=h_\alpha^*,\quad k_\alpha=k_\alpha^*.
\tag{16.1}
$$

**证明。** Along a continuous path from the identity, no central sector can be permuted. Differentiate the resulting finite matrix-algebra automorphisms. On a full matrix block, a derivation is a commutator with a matrix, as verified on matrix units. Subtract the self-adjoint left generator from $H_0$; the remainder commutes with every left matrix unit and hence has the right-factor form in (16.1). A scalar may be shifted between $h_\alpha$ and $k_\alpha$ without changing their sum. Conversely (16.1) preserves $\mathcal A$ for every $t$. $\square$

The essential quantifier is every joint density state, or every equivalent pure pair, at one fixed full-algebra interface. On a stipulated ready-input family, global unitary dilations can implement noisy local channels. The nonselective parity operation of §14 is itself a completely positive measurement channel; its unitary dilation uses an extra initialized record. No autonomy on all states of that further enlarged carrier has been asserted, so this does not contradict Theorem 16.1.

## 17. Sources, reused results and remaining native-interface obligations

The source pin is `6b24b302e37ea2ead041655259d42ef4866d3249`. V78 synthesis Definition 3.4 requires retaining memory that can return in future tests. Its §§7.1 and 10 distinguish complete mathematical effects from actual resources and event probabilities from recorded updates.

V38, *AURIC_COMPLETE_QUANTUM_PROCESSES_INTERNAL_MEMORY_AND_RANK_BOUNDARY_STABILITY_V38.md*, Theorem 8.1 already gives the product-unitary conclusion under all-joint-state autonomy. Its ready-input exception and §§8.2–8.3 retain reset and finite-memory costs. V40 §6 supplies finite-period completely positive rigidity with its separate reference-sensitive norm contract. None of these results is presented as a new AURIC theorem here.

The existing declaration `future_statistics_iff_annihilates_infinite_system` in `D5/S3/Quantum/Fibers/FutureStatisticsEquivalence.lean` supplies the linear Heisenberg prediction-closure relation. `LeastInvariantObservableAlgebra.lean` is a separate commutative function-algebra construction, not a theorem imported for noncommuting matrices. The former orbit-predictor application already distinguishes operator-system closure from adding algebraic products. These are source references, without a current build or fresh Lean verification.

Sections 1–8 provide the finite-algebra purity, Schmidt-frame and current pure-fibre interfaces used in §11. The needed frame argument is stated again there to keep the hypotheses explicit. These conditional paper dependencies provide no new Lean evidence.

Real Hahn–Banach, finite Schatten duality, Schmidt purification, conditional expectations and finite matrix-algebra automorphisms are standard tools. *AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md*, §§28–29, also uses real Hahn–Banach and Schatten duality for a different restricted-channel contract: Theorem 28.1 contains the norming-functional duality proof, while §29 consumes that dual and distinguishes pointwise choices from a single linear selection. Those source-specific domains are not identified with $W$ here. General finite-state, instrument and Choi background is J. Watrous, [*The Theory of Quantum Information*, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). No priority or originality claim is made for this application.

The exact widths compare alternative realizations under declared tests and operations. An assertion of one actual world or one $\omega$ alone does not supply these variations, common-source preparations, measurement access or legal operations. Placing controls and records inside one encompassing $\Omega$ likewise does not make their probabilities functions of the current local $\omega$. An adequate native future quotient requires the corresponding closure relations on its actual input and operation family.

No free controls, purification, reset or clean-return reference service is supplied. The scalar widths and finite-horizon bounds make no reference-amplified or unbounded-horizon claim and are not identified with the N2 shared-history rank budget. The formulas remain conditional paper deductions, without Lean compilation or physical validation.

## 追加锚（本行以下为增补区）


## 18. A phase reference is a state program only for one fixed processor

This continuation is a conditional paper application of standard trace-distance, classical-affinity and two-state discrimination tools. Finite complex states, a fixed completely positive instrument and independent fresh probe preparations are supplied premises. The results neither obtain a native phase reference nor establish a repeatable hardware service. The state-program contract below is separate from a granted family of queried operators.

<a id="statement-reference-18-1"></a>

**定义 18.1（Common processor and persistent memory）。** Let $R$ contain the reference and every persistent auxiliary memory that can interact on a later use. Fix one data density $\rho$, independent of $R$, and the same auxiliary initialization under both program hypotheses. One use of the device is a single fixed channel

<a id="eq-reference-18-1"></a>

$$
\begin{aligned}
\mathcal T:B(R)&\longrightarrow B(C\otimes R),\\
\mathcal T(\eta)
&=\sum_x|x\rangle\langle x|_C\otimes\mathcal T_x(\eta).
\end{aligned}
\tag{18.1}
$$

The branch maps $\mathcal T_x$ are completely positive and their sum is trace preserving on the full input matrix cone. The finite classical register $C$ records every outcome, including success, failure and rejection. Earlier records are retained and are not fed back into $\mathcal T$.

Each new use supplies the same fixed data state $\rho$ and explicitly initialized fresh auxiliary resources. It does not reset $R$. In particular, work or memory that can return on a later use belongs to $R$, rather than being discarded from the return obligation.

<a id="statement-reference-18-2"></a>

**定义 18.2（Decoupled complete-record return）。** For two possible initial states $\eta_0,\eta_1$ of this same $R$, fix target complete-record distributions $p_0,p_1$ and errors $\varepsilon_0,\varepsilon_1$ satisfying

<a id="eq-reference-18-2"></a>

$$
D\bigl(\mathcal T(\eta_j),p_j\otimes\eta_j\bigr)
\le\varepsilon_j,
\qquad
D(A,B)=\frac12\lVert A-B\rVert_1,
\qquad j\in\{0,1\}.
\tag{18.2}
$$

The classical distribution $p_j$ is identified with its diagonal density on $C$. The product in (18.2) requires return of the entire persistent system and decoupling from its new complete record. For mixed $\eta_j$, return of the $R$ marginal alone is a weaker condition. If ready work is included in $R$, its residual state is included in the same joint error.

The hypothesis index $j$ appears only in $\eta_j$. A family of query operators $Q_j$, different classically selected apparatus settings, or a $j$-dependent data preparation changes the processor or its common input. Such an interface becomes a state program only after a separate bridge establishes (18.1). In particular, the calibrated controlled-$Q$ services in the AURIC atlas are not automatically finite reference-state programs.

## 19. Retained complete records give a finite reuse budget

Put

<a id="eq-reference-19-1"></a>

$$
d=D(\eta_0,\eta_1),
\qquad
\beta=\sum_x\sqrt{p_0(x)p_1(x)}\in[0,1].
\tag{19.1}
$$

<a id="statement-reference-19-1"></a>

**命题 19.1（Finite repeated-use inequality）。** Under Definitions 18.1–18.2, for every positive integer $n$,

<a id="eq-reference-19-2"></a>

$$
\boxed{
1-\beta^n\le d+n(\varepsilon_0+\varepsilon_1).
}
\tag{19.2}
$$

**证明。** Let $\Omega_j^{(n)}$ be the actual joint state of the $n$ retained classical records and $R$, after applying the same $\mathcal T$ successively to $R$ alone. Induction gives

<a id="eq-reference-19-3"></a>

$$
D\bigl(\Omega_j^{(n)},p_j^{\otimes n}\otimes\eta_j\bigr)
\le n\varepsilon_j.
\tag{19.3}
$$

The case $n=1$ is (18.2). For the induction step, apply $\operatorname{id}_{\rm old\ records}\otimes\mathcal T$ to the previous actual and ideal states. Their trace distance contracts. On the ideal input, the old records are $p_j^{\otimes n}$ and the persistent input is $\eta_j$, so the extra one-use error is at most $\varepsilon_j$ by (18.2). Tensoring with a positive trace-one state preserves trace norm. The triangle inequality gives the next instance of (19.3).

The actual complete $n$-use process is one common completely positive trace-preserving map applied to the initial program state. Consequently,

$$
D\bigl(\Omega_0^{(n)},\Omega_1^{(n)}\bigr)\le d.
$$

Discard $R$, use (19.3), and apply the triangle inequality to obtain

$$
D\bigl(p_0^{\otimes n},p_1^{\otimes n}\bigr)
\le d+n(\varepsilon_0+\varepsilon_1).
$$

For classical distributions $P,Q$, total variation is $1-\sum_x\min\{P(x),Q(x)\}$. Since $\min\{P(x),Q(x)\}\le\sqrt{P(x)Q(x)}$, and affinity multiplies under tensor products, the left side is at least $1-\beta^n$. This proves (19.2). $\square$

The independent records in this proof are an ideal comparison family. The actual reused records need not be independent, and independence is not inferred from one-use accuracy or from return of a reference marginal. Every ideal and actual state belongs to the same repeated device and the same initial program hypothesis.

<a id="statement-reference-19-2"></a>

**推论 19.2（Return-error and record-contrast forms）。** Writing $[t]_+=\max\{t,0\}$, each positive integer $n$ gives

<a id="eq-reference-19-4"></a>

$$
\varepsilon_0+\varepsilon_1
\ge\frac{[1-d-\beta^n]_+}{n}.
\tag{19.4}
$$

If $v$ is the total variation distance between the two complete target-record distributions, then also

<a id="eq-reference-19-5"></a>

$$
\varepsilon_0+\varepsilon_1
\ge\frac{[1-d-(1-v^2)^{n/2}]_+}{n}.
\tag{19.5}
$$

**证明。** Rearranging (19.2) gives (19.4). For (19.5), write

$$
|p_0(x)-p_1(x)|
=|\sqrt{p_0(x)}-\sqrt{p_1(x)}|
\bigl(\sqrt{p_0(x)}+\sqrt{p_1(x)}\bigr).
$$

Cauchy–Schwarz yields $v\le\sqrt{1-\beta^2}$, hence $\beta^n\le(1-v^2)^{n/2}$. Substitute this into (19.4). $\square$

These are necessary finite-use budgets. No optimization over processors, attaining device or sharpness of these lower bounds is asserted.

## 20. Pure-reference marginal fidelity controls decoupled return

Suppose $\eta_j=P_{r_j}=|r_j\rangle\langle r_j|$ is pure, and let $p_j$ now be the actual complete-record distribution on this input. Write the classical–quantum output as

$$
\mathcal T(P_{r_j})
=\sum_xp_j(x)|x\rangle\langle x|\otimes\eta_{j,x},
$$

where zero-probability terms are omitted. Define the mean reference-fidelity defect

<a id="eq-reference-20-1"></a>

$$
\delta_j
=1-\langle r_j,
\operatorname{Tr}_C\mathcal T(P_{r_j})r_j\rangle.
\tag{20.1}
$$

<a id="statement-reference-20-1"></a>

**命题 20.1（Pure marginal to complete joint return）。** The complete-record product-return error satisfies

<a id="eq-reference-20-2"></a>

$$
\begin{aligned}
D\bigl(\mathcal T(P_{r_j}),p_j\otimes P_{r_j}\bigr)
&=\sum_xp_j(x)D(\eta_{j,x},P_{r_j})\\
&\le\sqrt{\delta_j}.
\end{aligned}
\tag{20.2}
$$

**证明。** Trace norm adds over the orthogonal classical blocks, giving the equality. Diagonalize each $\eta_{j,x}$. The pure-state trace-distance formula, convexity of trace distance and concavity of square root give

$$
D(\eta_{j,x},P_{r_j})
\le\sqrt{1-\langle r_j,\eta_{j,x}r_j\rangle}.
$$

Apply square-root concavity again over the complete classical flags. Their weighted fidelity defect is exactly (20.1), giving (20.2). $\square$

Combining (19.4) with (20.2) yields

<a id="eq-reference-20-3"></a>

$$
\sqrt{\delta_0}+\sqrt{\delta_1}
\ge\frac{[1-d-\beta^n]_+}{n}
\qquad(n\ge1).
\tag{20.3}
$$

In particular, if both defects are at most $\delta$, then

$$
\delta\ge
\left(\frac{[1-d-\beta^n]_+}{2n}\right)^2
\qquad(n\ge1).
$$

If a target distribution differs from the actual complete-record distribution by total variation $\alpha_j$, a further triangle inequality bounds its error in (18.2) by $\alpha_j+\sqrt{\delta_j}$.

Exact return of a pure marginal forces every positive-probability conditional reference state to equal that same pure state. It therefore supplies the decoupled return required in (18.2). Approximate marginal fidelity gives the displayed square-root bound. For an arbitrary mixed marginal, neither this pure-state implication nor an analogous joint-return conclusion is assumed.

## 21. Exact decoupled reuse cannot reveal nonorthogonal state programs

<a id="statement-reference-21-1"></a>

**命题 21.1（Exact-return information obstruction）。** For the same fixed device of §18, if $d<1$ and $\varepsilon_0=\varepsilon_1=0$, then $p_0=p_1$.

**证明。** If the two normalized complete-record laws differ, their affinity satisfies $\beta<1$. Taking $n$ large in (19.2) gives $1\le d<1$, a contradiction. $\square$

This is the standard information-without-disturbance obstruction under an explicit retained-record contract. It allows noisy readouts and mixed program states when exact product return holds.

For finite density states, $d=1$ exactly when their supports are orthogonal. Orthogonal supports give distance one directly. Conversely, a maximizing Helstrom projection at distance one has probability one on one state and zero on the other. Positivity places their supports in its orthogonal range and kernel. Thus $d<1$ covers every pair with nonorthogonal supports.

<a id="statement-reference-21-2"></a>

**推论 21.2（A connected phase orbit has a constant exact-return record law）。** Let

<a id="eq-reference-21-1"></a>

$$
\eta_\theta
=U_R(\theta)\eta_0U_R(\theta)^*
\tag{21.1}
$$

be a continuous finite-dimensional phase orbit. Suppose one common device returns each $\eta_\theta$ exactly decoupled from its complete record. For a fixed common data input, its record distribution is constant on the connected phase circle.

**证明。** Continuity makes the trace distance between sufficiently nearby program states less than one. Proposition 21.1 makes their record laws equal. The law is therefore locally constant, hence constant on the connected circle. $\square$

The conclusion excludes a phase-dependent record under the exact decoupled-return promise, including a desired unsharp readout. It does not apply to different granted query operations $Q_\theta$ solely because their carrier is finite dimensional. Such operations still require the common-processor state-program bridge of §18.

## 22. A covariant processor makes the phase-reference condition explicit

Let a fixed instrument $\mathcal M$ act on $R\otimes S$ and output $R\otimes C$, with the output factors written in this order. Let $C$ again be the complete classical record. Assume covariance:

<a id="eq-reference-22-1"></a>

$$
\begin{aligned}
&\mathcal M\bigl[
(U_R(\theta)\otimes U_S(\theta))
X(U_R(\theta)\otimes U_S(\theta))^*
\bigr]\\
&\qquad=(U_R(\theta)\otimes I_C)
\mathcal M(X)
(U_R(\theta)\otimes I_C)^*.
\end{aligned}
\tag{22.1}
$$

Suppose, for every data density $\rho$,

$$
\mathcal M(\eta_0\otimes\rho)
=\eta_0\otimes p_0(\rho).
$$

Covariance then gives

<a id="eq-reference-22-2"></a>

$$
\mathcal M(\eta_\theta\otimes\rho)
=\eta_\theta\otimes
p_0\bigl(U_S(\theta)^*\rho U_S(\theta)\bigr).
\tag{22.2}
$$

<a id="statement-reference-22-1"></a>

**命题 22.1（Exact decoupled return permits only invariant effects）。** Under the preceding covariance and return assumptions, the distributions in (22.2) are independent of $\theta$ for each fixed $\rho$. If

$$
p_0(x\mid\rho)=\operatorname{Tr}(E_x\rho),
$$

then

<a id="eq-reference-22-3"></a>

$$
U_S(\theta)E_xU_S(\theta)^*=E_x
\qquad\text{for every }x,\theta.
\tag{22.3}
$$

**证明。** For each fixed independent data input $\rho$, the same $\mathcal M$ is one fixed channel from the program to its returned reference and classical record. Apply Corollary 21.2. Equality of the resulting probabilities for every data density implies equality of the effects, giving (22.3). $\square$

If $\eta_0$ is pure, exact marginal return for every data density supplies the product premise by §20. Mixed marginal return is not promoted to this stronger premise.

For an explicit target, let $S$ be a qubit, take $U_S(\theta)=e^{-i\theta Z/2}$, and let $p_0$ be the sharp $X$ measurement. The supplied common coherent probe $\rho=P_{+x}$ gives complete target laws

<a id="eq-reference-22-4"></a>

$$
p_0=(1,0),
\qquad
p_\theta=
\bigl(\cos^2(\theta/2),\sin^2(\theta/2)\bigr),
\qquad
\beta=|\cos(\theta/2)|.
\tag{22.4}
$$

Any approximate product-return implementation of this same state-program task obeys

<a id="eq-reference-22-5"></a>

$$
\varepsilon_0+\varepsilon_\theta
\ge
\frac{
[1-D(\eta_0,\eta_\theta)-|\cos(\theta/2)|^n]_+
}{n}
\qquad(n\ge1).
\tag{22.5}
$$

Small nonzero $\theta$ gives different target records while the reference-state distance is below one. This excludes exact product return and leaves finite-error protocols within the displayed budget. The coherent probe, its independent preparation, covariance and the common processor are supplied premises. A common-history label supplies none of these operations or preparations.

## 23. Success-only return retains a complete failure budget

Specify success as a subset of the actual complete classical outcomes. Suppose that, on each program input, the whole successful block factors with the original persistent state:

<a id="eq-reference-23-1"></a>

$$
\sum_{x\in\mathrm{succ}}
|x\rangle\langle x|\otimes\mathcal T_x(\eta_j)
=
\sum_{x\in\mathrm{succ}}
p_j(x)|x\rangle\langle x|\otimes\eta_j.
\tag{23.1}
$$

Here $p_j$ is the actual complete outcome distribution, and $\mathrm{fail}$ denotes every outcome outside the success subset, including rejection. Put $f_j=\sum_{x\in\mathrm{fail}}p_j(x)$. Conditional reference outputs on failure are arbitrary.

<a id="statement-reference-23-1"></a>

**命题 23.1（Paid heralding with complete flags）。** Under (23.1), the actual product-return error obeys

<a id="eq-reference-23-2"></a>

$$
\begin{aligned}
\varepsilon_j
&:=D\bigl(\mathcal T(\eta_j),p_j\otimes\eta_j\bigr)\\
&=\sum_{x\in\mathrm{fail}}
p_j(x)D(\eta_{j,x},\eta_j)
\le f_j.
\end{aligned}
\tag{23.2}
$$

Consequently,

<a id="eq-reference-23-3"></a>

$$
f_0+f_1
\ge\frac{[1-d-\beta^n]_+}{n}
\qquad(n\ge1),
\tag{23.3}
$$

where $\beta$ is the affinity of the complete actual record laws.

**证明。** Trace norm adds over the classical blocks. The successful blocks vanish from the joint difference by (23.1); each failure-state distance is at most one, giving (23.2). Apply (19.4) with these actual errors to obtain (23.3). $\square$

Separately normalized successful distributions cannot replace the complete distributions in $\beta$. Both success probability and the failure reference state remain in the budget. Equation (23.3) is a necessary bound, not an optimal heralded-measurement frontier or a prohibition on paid postselection. For a mixed reference, return of the success marginal while it remains correlated with its detailed record does not establish (23.1).

## 24. Exact marginal restoration can leave only one sample

<a id="statement-reference-24-1"></a>

**例 24.1（Repeated classical copying preserves correlations）。** On a qubit reference, take the commuting family

$$
\eta_p=pP_0+(1-p)P_1.
$$

A blank classical record and a controlled copy of the reference basis give

<a id="eq-reference-24-1"></a>

$$
\mathcal T(\eta_p)
=pP_0^C\otimes P_0^R
+(1-p)P_1^C\otimes P_1^R.
\tag{24.1}
$$

The $R$ marginal returns exactly while the record depends on $p$. For $0<p<1$, the joint output is correlated and differs from $p_{\rm record}\otimes\eta_p$.

After $n$ copies all record bits agree. Only the strings $0^n$ and $1^n$ occur, with masses $p$ and $1-p$. They are not an independent Bernoulli sample of length $n$. For program hypotheses $p,q$, the complete-record total variation remains $|p-q|$ at every $n$, equal to the initial program trace distance. Repetition creates no additional distinguishability.

The exact one-use distance from the product of the two marginals is

<a id="eq-reference-24-2"></a>

$$
D\bigl(\mathcal T(\eta_p),p_{\rm record}\otimes\eta_p\bigr)
=2p(1-p).
\tag{24.2}
$$

Indeed, the four diagonal differences are $p(1-p),-p(1-p),-p(1-p),p(1-p)$, whose absolute values give (24.2) under the half trace-norm convention. This example fails the zero joint-error premise of (18.2). It is a classical mixed-program example, not an exception for a continuous covariant phase orbit.

## 25. A finite catalog permits exact heralded return on success

<a id="statement-reference-25-1"></a>

**例 25.1（Two known nonorthogonal programs with a paid failure flag）。** Let two normalized pure program vectors have overlap $c\in(0,1)$. Choose their irrelevant vector phases so that $\langle r_0,r_1\rangle=c$. Fix any unit reference vector $f$ and three orthogonal record flags $0,1,\mathrm{fail}$. Define

<a id="eq-reference-25-1"></a>

$$
\begin{aligned}
V|r_0\rangle
&=\sqrt{1-c}|r_0\rangle|0\rangle
+\sqrt c|f\rangle|\mathrm{fail}\rangle,\\
V|r_1\rangle
&=\sqrt{1-c}|r_1\rangle|1\rangle
+\sqrt c|f\rangle|\mathrm{fail}\rangle.
\end{aligned}
\tag{25.1}
$$

The rule preserves the Gram matrix of its two inputs. It therefore extends linearly to an isometry on their span and can be extended to the whole input space. Reading the flags unambiguously identifies the program on success and returns that same program vector. Each program has success probability $1-c$; the reference is generally changed on failure.

If the two target data measurements and their label-controlled application are supplied as additional operations, the successful flag can choose the desired measurement on arbitrary data while keeping the program unchanged on that branch.

<a id="statement-reference-25-2"></a>

**命题 25.2（Failure bound for unambiguous program identification）。** For this two-program unambiguous-label task, the failure probabilities obey

<a id="eq-reference-25-2"></a>

$$
f_0f_1\ge c^2.
\tag{25.2}
$$

Equal failure rates are therefore at least $c$, attained by (25.1).

**证明。** Retain a Stinespring isometry and complete outcome flags. Successful labels for the two programs are orthogonal and cannot contribute to the input inner product. That inner product comes only from the failure vectors, whose squared norms are $f_0,f_1$. Cauchy–Schwarz gives $c\le\sqrt{f_0f_1}$, which is (25.2). $\square$

This sharp statement belongs to unambiguous program identification. It is not a universal minimum failure probability for an arbitrary pair of measurements without the identification task. The known catalog, its discriminator and controlled target measurements are extra operations. The construction is not asserted to be covariant on a whole phase orbit, uniform on a continuous catalog, native, or clean on failure. A successful filter can therefore coexist with the complete-resource obstruction to deterministic catalytic reuse without contradicting §21.

## 26. AURIC interfaces and the remaining reference-service obligations

The source pin is `abb8ab300349682ec584fdc4750b13ca19ef253f`. Atlas II §§65–66 distinguish declared-readout return, full source return and logical accuracy. Its §76.2 grants calibrated controlled-query services and clean synthesis work separately. Those query-operator contracts retain their stated scope. Equations (18.2) and (22.1) add a state-reference return contract and covariance; neither follows from the earlier service contracts.

*AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md*, Theorem C-124.1 uses fresh batches for tensor channel uses. Proposition C-124.2 already shows why reusing one exact one-use calibration record can fail at two uses. The fresh-versus-reused distinction is retained here: fresh source cost and a shared random record are not renamed as independent replenishment. Equation (19.2) instead quantifies the joint-return promise of one repeated processor.

V71 already supplies the Nielsen–Chuang pure-program unitary obstruction with its explicit input/output program inner-product proof. The classical-record argument here uses a different return contract and is not presented as a new general no-programming theorem. The prior-information, reference-state and covariant-mode distinctions of the four-corner volume, C-143.2–143.3, also retain their original scope. Availability of a mode is not a theorem about reference updates or return.

Trace-norm contraction, classical Bhattacharyya affinity, pure-state trace distance and two-state unambiguous discrimination are standard ingredients. General finite-state and instrument background is J. Watrous, [*The Theory of Quantum Information*, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). No independent priority survey of this finite-budget application has been completed and no originality claim is made.

Every reuse conclusion above concerns the same processor, with the parameter appearing only in its initial program state, every persistent memory included, all outcome flags retained, no old-record feedback and the stipulated fresh independent inputs. Membership in one encompassing $\Omega$ does not supply independent ready states or a covariant apparatus. The results neither derive a Born law nor select a complex state space. They specify the extra joint-return relation required for a reusable-reference claim and the complete records and failure states its cost must include. The displayed results are conditional paper deductions, without new Lean statements, current Lean compilation or physical validation.

## 追加锚（本行以下为增补区）


## 27. The preparation family fixes the domain of a future comparison

This continuation applies finite-dimensional span, relative-interior and Gram reconstruction arguments to a declared preparation interface. The source family, common operations, state/effect interpretation and calibration are supplied premises. Finite tests do not establish those premises, a Born rule, a physical state dimension or native preparation access. No literature-priority claim is made.

<a id="statement-preparation-27-1"></a>

**定义 27.1（Restricted preparation fibres）。** Let $H$ be a nonzero complex Hilbert space of dimension $D$. Regard $\operatorname{Herm}(H)$ as a real inner-product space with

$$
\langle A,B\rangle=\operatorname{Tr}(AB),
\qquad\lVert A\rVert_2^2=\operatorname{Tr}(A^2).
$$

Let $W\subseteq\operatorname{Herm}(H)$ be a real subspace containing $I$, and let $Q$ be a nonempty set of density matrices admitted by the declared common source and operation contract. Put

<a id="eq-preparation-27-1"></a>

$$
\begin{aligned}
\rho\sim_W\sigma
&\quad\Longleftrightarrow\quad
\operatorname{Tr}((\rho-\sigma)w)=0
\quad\text{for every }w\in W,\\
\mathcal K_Q
&=\operatorname{span}_{\mathbb R}
\{\rho-\sigma:\rho,\sigma\in Q,\ \rho\sim_W\sigma\},\\
\Delta_{Q,W}(B)
&=\sup_{\substack{\rho,\sigma\in Q\\\rho\sim_W\sigma}}
|\operatorname{Tr}(B(\rho-\sigma))|.
\end{aligned}
\tag{27.1}
$$

The supremum is used even when $Q$ is not closed. Identical pairs are allowed, so the comparison set is nonempty. Since $I\in W$, every element of $\mathcal K_Q$ has trace zero, and

$$
\mathcal K_Q\subseteq W^\perp,
\qquad
k:=\dim\mathcal K_Q\le D^2-\dim W.
$$

<a id="statement-preparation-27-2"></a>

**命题 27.2（Exact restricted-source prediction criterion）。** For every Hermitian $B$,

<a id="eq-preparation-27-2"></a>

$$
\Delta_{Q,W}(B)=0
\quad\Longleftrightarrow\quad
B\perp\mathcal K_Q.
\tag{27.2}
$$

**证明。** The width vanishes exactly when $B$ annihilates every generating equal-response difference in (27.1). This is equivalent to annihilating their real span. $\square$

Replacing $Q$ by all density matrices changes the comparison unless the two equal-response difference spans agree. For an effect $B$, the width belongs to $[0,1]$; its interpretation as a probability difference still uses the stipulated state/effect and Born contract.

For an arbitrary preparation set, one has only

$$
\mathcal K_Q
\subseteq\operatorname{span}_{\mathbb R}(Q-Q)\cap W^\perp.
$$

Equality needs an additional premise or a direct calculation of the span. In particular, taking the intersection after spanning all preparation differences can introduce directions that no equal-response pair in the original $Q$ supplies. Section 30 gives an explicit example.

## 28. A fixed preparation family has a finite actual-pair certificate

Suppose $k>0$. Finite basis extraction from the generating set in (27.1) selects $k$ actual pairs $(\rho_a,\sigma_a)$ in $Q$ with equal current responses, whose differences

$$
d_a=\rho_a-\sigma_a
\qquad(1\le a\le k)
$$

are linearly independent and span $\mathcal K_Q$. The selected states are members of the original preparation set. Arbitrary linear combinations are not declared to be available preparations.

Define the positive-definite real Gram matrix, future gap coordinates and hidden residual by

<a id="eq-preparation-28-1"></a>

$$
G_{ab}=\operatorname{Tr}(d_ad_b),
\qquad
b_a(B)=\operatorname{Tr}(Bd_a),
\qquad
R_Q(B)=P_{\mathcal K_Q}B.
\tag{28.1}
$$

<a id="statement-preparation-28-1"></a>

**命题 28.1（Gram reconstruction and finite exact certificate）。** For these actual equal-response pairs,

<a id="eq-preparation-28-2"></a>

$$
\begin{aligned}
R_Q(B)&=\sum_a(G^{-1}b(B))_a d_a,\\
\lVert R_Q(B)\rVert_2^2
&=b(B)^{\mathsf T}G^{-1}b(B).
\end{aligned}
\tag{28.2}
$$

Consequently,

<a id="eq-preparation-28-3"></a>

$$
\Delta_{Q,W}(B)=0
\quad\Longleftrightarrow\quad
b_a(B)=0\quad(1\le a\le k).
\tag{28.3}
$$

**证明。** Taking the inner product of the first expression in (28.2) with $d_c$ gives $(GG^{-1}b)_c=b_c(B)$. The reconstructed vector belongs to $\mathcal K_Q$ and has the same inner products with its basis as $B$, so it is the orthogonal projection. Its squared norm gives the second formula. Apply (27.2) to obtain (28.3). $\square$

This is an existence statement and a conditional finite-test certificate. A description of $Q$ need not provide its dimension, a search algorithm, the selected preparations or their calibration. Mathematical basis extraction does not acquire a native preparation procedure. If $k=0$, all widths vanish and the certificate contains zero pairs. The Gram estimates below concern $k>0$.

Write

$$
\operatorname{diam}_2(Q)
=\sup_{\rho,\sigma\in Q}\lVert\rho-\sigma\rVert_2.
$$

Density matrices satisfy $\operatorname{Tr}(\rho^2)\le1$ and $\operatorname{Tr}(\rho\sigma)\ge0$, so $\operatorname{diam}_2(Q)\le\sqrt2$. Every permitted equal-response difference belongs to $\mathcal K_Q$. Cauchy–Schwarz and the actual selected pairs give

<a id="eq-preparation-28-4"></a>

$$
\max_a|b_a(B)|
\le\Delta_{Q,W}(B)
\le\operatorname{diam}_2(Q)
\sqrt{b(B)^{\mathsf T}G^{-1}b(B)}.
\tag{28.4}
$$

The lower bound tests actual individual witness pairs. The upper bound uses the residual of one common future observable $B$; it does not combine source realizations optimized separately.

If the estimated coordinates satisfy $|b_a(B)-\widetilde b_a|\le\nu_a$, then

<a id="eq-preparation-28-5"></a>

$$
\Delta_{Q,W}(B)
\le
\frac{\operatorname{diam}_2(Q)}{\sqrt{\lambda_{\min}(G)}}
\left(\sum_a(|\widetilde b_a|+\nu_a)^2\right)^{1/2}.
\tag{28.5}
$$

Indeed, (28.2) bounds the residual norm by $\lVert b(B)\rVert_2/\sqrt{\lambda_{\min}(G)}$, and the coordinate error bounds control $\lVert b(B)\rVert_2$. The positive smallest eigenvalue belongs to the calibrated target differences. Exact spanning without a quantitative Gram bound does not give a uniform stable certificate.

## 29. Convex preparation domains identify the hidden directions

Suppose $Q$ is convex and put $L=\operatorname{span}_{\mathbb R}(Q-Q)$. Choose a relative-interior point $\rho_0\in Q$ and $r>0$ with

<a id="eq-preparation-29-1"></a>

$$
\rho_0+\{h\in L:\lVert h\rVert_2\le r\}
\subseteq Q.
\tag{29.1}
$$

Such a point and radius exist in finite dimension. Choose an affinely independent finite subset of $Q$ spanning its affine hull. Convexity places its simplex inside $Q$. At the barycenter all barycentric coordinates are strictly positive; continuity gives an open relative ball inside the simplex. Choose $r$ smaller than that radius to obtain the closed ball (29.1). For a singleton $Q$, $L=\{0\}$ and the ensuing zero-space statements are immediate. This existence argument provides neither a known numerical radius nor a physical method for preparing the ball.

<a id="statement-preparation-29-1"></a>

**命题 29.1（Convex-domain hidden span）。** Under convexity,

<a id="eq-preparation-29-2"></a>

$$
\boxed{\mathcal K_Q=L\cap W^\perp.}
\tag{29.2}
$$

**证明。** The forward inclusion holds for every $Q$. For nonzero $h\in L\cap W^\perp$, the two states

$$
\rho_0\pm r\frac{h}{\lVert h\rVert_2}
$$

belong to $Q$ by (29.1) and have the same $W$ responses. Their difference is a nonzero multiple of $h$, so $h\in\mathcal K_Q$. The zero vector needs no additional pair. $\square$

The ball here belongs to the actual affine preparation domain. A neighborhood in a larger ambient state space cannot substitute for it.

Choose a Hilbert–Schmidt orthonormal basis $H_a$ of $\mathcal K_Q$. The $2k$ states

<a id="eq-preparation-29-3"></a>

$$
\rho_a^\pm=\rho_0\pm rH_a,
\qquad
g_a(B)
=\operatorname{Tr}\bigl(B(\rho_a^+-\rho_a^-)\bigr)
=2r\operatorname{Tr}(BH_a)
\tag{29.3}
$$

form a finite equal-response certificate. In this orthonormal basis,

<a id="eq-preparation-29-4"></a>

$$
\begin{aligned}
\lVert R_Q(B)\rVert_2
&=\frac{\lVert g(B)\rVert_2}{2r},\\
2r\lVert R_Q(B)\rVert_2
&\le\Delta_{Q,W}(B)
\le\operatorname{diam}_2(Q)\lVert R_Q(B)\rVert_2.
\end{aligned}
\tag{29.4}
$$

The residual coordinates give the first equality. For the lower bound when the residual is nonzero, use the single admissible pair

$$
\rho_0\pm r\frac{R_Q(B)}{\lVert R_Q(B)\rVert_2}
$$

in the same relative ball. Its future gap is $2r\lVert R_Q(B)\rVert_2$. The zero case is immediate, and Cauchy–Schwarz gives the upper bound. This uses one jointly admissible pair; it does not assert simultaneous use of independently optimal coordinate pairs.

For the full density set, $\rho_0=I/D$ and $r=1/(2D)$ satisfy (29.1) on the full trace-zero Hermitian space. Indeed,

$$
\lVert h\rVert_{\rm op}\le\lVert h\rVert_2\le\frac1{2D}
\quad\Longrightarrow\quad
I/D+h\succeq I/(2D).
$$

The full-source positive-perturbation mechanism is already present in the repository's tomography completeness result. The sharper all-density width identity is supplied by §10. Equation (29.4) is a convenient conditioned finite-test bound and makes no optimal-constant claim.

## 30. Convexification and calibrated sensitivity are separate assumptions

<a id="statement-preparation-30-1"></a>

**例 30.1（Three classical preparations change their hidden span under convexification）。** Take qutrit coordinate projections and

$$
Q=\{P_0,P_1,P_2\},
\qquad
W=\operatorname{span}_{\mathbb R}\{I,Z\},
\qquad
Z=\operatorname{diag}(0,1,2).
$$

Their current $Z$ readings are respectively $0,1,2$, so no distinct preparations have the same current responses. Hence $\mathcal K_Q=\{0\}$, whereas

<a id="eq-preparation-30-1"></a>

$$
L\cap W^\perp
=\operatorname{span}_{\mathbb R}
\{\operatorname{diag}(1,-2,1)\}
\ne\{0\}.
\tag{30.1}
$$

For $Q'=\operatorname{conv}Q$, the states $P_1$ and $(P_0+P_2)/2$ have the same $Z$ expectation $1$. The future effect $B=P_1$ has expectations $1$ and $0$ on that pair. Therefore

$$
\Delta_{Q,W}(P_1)=0,
\qquad
\Delta_{Q',W}(P_1)=1.
$$

When a randomized preparation choice is admitted and its label is unavailable to the subsequent device, a fixed quantum operation evaluates the corresponding mixture affinely. Admitting all such mixtures as source states still requires that randomization and label contract. If a preparation label or correlated memory is retained by the device, it must be included in $H$ and in its input state. The marginal mixture alone need not describe the full input. One actual $\omega$ trajectory does not supply the alternative preparations or a convex domain.

<a id="statement-preparation-30-2"></a>

**例 30.2（Small probe gaps can have poor sensitivity）。** On a qubit, take

$$
W=\operatorname{span}_{\mathbb R}\{I,Z\},
\qquad
B=\frac{I+X}{2}.
$$

The full-source width is $1$. For $0<\epsilon\le1$, the probes $I/2\pm\epsilon X/2$ have equal $W$ responses and future gap $\epsilon$. Letting $\epsilon$ decrease makes that gap arbitrarily small while the full-source width of the same $B$ remains $1$. The Gram eigenvalue of the shrinking difference records exactly the sensitivity loss appearing in (28.5). A small raw gap alone is not a dimension-free accuracy certificate.

## 31. A complete recorded instrument has a finite branchwise certificate

Let $\{\Lambda_x\}$ be one fixed finite instrument on the input $H$, with an output carrier. Each branch is completely positive and trace nonincreasing, and their sum is trace preserving. Let $\mathcal A_{\rm out}$ be a represented unital output observable algebra, and choose a finite real basis of effects $E_1,\ldots,E_m$ for $(\mathcal A_{\rm out})_{\rm sa}$. Such an effect basis is obtained by starting with $I$ and a Hermitian basis, then shifting and scaling the remaining basis elements into $[0,I]$.

Write $F_x=\Lambda_x^*$. For the selected actual pairs from §28, use $\rho_a^+=\rho_a$ and $\rho_a^-=\sigma_a$; the convex-ball pairs of §29 use their existing signs. In either case put $d_a=\rho_a^+-\rho_a^-$. The unnormalized recorded probabilities satisfy

<a id="eq-preparation-31-1"></a>

$$
\begin{aligned}
p_{a,x,\ell}^\pm
&=\operatorname{Tr}\bigl(E_\ell\Lambda_x(\rho_a^\pm)\bigr),\\
p_{a,x,\ell}^+-p_{a,x,\ell}^-
&=\operatorname{Tr}\bigl(F_x(E_\ell)d_a\bigr).
\end{aligned}
\tag{31.1}
$$

<a id="statement-preparation-31-1"></a>

**命题 31.1（Finite test of complete recorded autonomy on $Q$）。** The following are equivalent:

1. Every pair of preparations in $Q$ with the same $W$ responses gives the same complete recorded output state restricted to $\mathcal A_{\rm out}$.
2. $F_x(E_\ell)\perp\mathcal K_Q$ for every $x,\ell$.
3. Every selected finite gap in (31.1) is zero.

**证明。** If $k=0$, the equal-response difference span is zero, the selected list is empty and all three conditions hold. Otherwise Proposition 28.1 turns vanishing of the selected gaps into orthogonality to $\mathcal K_Q$. The effect span and linearity extend this equality to every output effect in each recorded branch. Conversely, equality of the complete restricted outputs applies to every selected pair and basis effect. $\square$

Every failure branch is included. Since $I$ belongs to the output span, the certificate also compares branch probabilities. Normalizing successful states first discards those probabilities. Summing the branches first tests a weaker nonselective contract and permits cancellation.

For a quantitative form, put

$$
\delta_x=\max_\ell\lVert R_Q(F_x(E_\ell))\rVert_2.
$$

For the fixed effect basis write $a=\sum_\ell c_\ell(a)E_\ell$, and define

<a id="eq-preparation-31-2"></a>

$$
\kappa
=\sup_{\substack{a\in\mathcal A_{\rm out}\\0\le a\le I}}
\sum_\ell|c_\ell(a)|
<\infty.
\tag{31.2}
$$

Basis coordinates are continuous on the compact effect interval, which proves finiteness. A complete recorded event chooses one effect $a_x$ in every branch. Its pulled-back input effect is $\sum_xF_x(a_x)$, and

<a id="eq-preparation-31-3"></a>

$$
\begin{aligned}
&\sup_{\substack{\rho,\sigma\in Q\\\rho\sim_W\sigma}}
\ \sup_{a_x\in\operatorname{Eff}(\mathcal A_{\rm out})}
\left|
\sum_x\operatorname{Tr}\bigl(a_x\Lambda_x(\rho-\sigma)\bigr)
\right|\\
&\qquad\le
\operatorname{diam}_2(Q)\,\kappa\sum_x\delta_x.
\end{aligned}
\tag{31.3}
$$

To prove this, project the one summed input effect onto $\mathcal K_Q$. Each basis expansion has residual norm at most $\kappa\delta_x$. Sum those bounds and apply Cauchy–Schwarz to the same admissible difference $\rho-\sigma$. This is a triangle upper bound; it does not claim that independently optimized branch extrema are simultaneously attained. Equations (28.2) and (28.5) bound the constituent residuals and hence $\delta_x$.

An arbitrary-horizon recursive certificate additionally requires admissible successor preparation domains and legal operations at every history. A test on one initial family does not establish this closure.

## 32. Actual product pairs span the full partial-trace kernel

Let $H=S\otimes E$ with $\dim S=d\ge1$ and $\dim E=e\ge2$. Take

$$
W=\operatorname{Herm}(S)\otimes I_E,
$$

so that equal current responses mean equality of the entire system marginal.

Choose $d^2$ pure system densities $\rho_i$: the $d$ coordinate projections and, for every $j<k$, the projections onto

$$
\frac{|j\rangle+|k\rangle}{\sqrt2},
\qquad
\frac{|j\rangle+i|k\rangle}{\sqrt2}.
$$

They span $\operatorname{Herm}(S)$ over $\mathbb R$. Subtracting half the two coordinate projections from each added density gives a real or imaginary off-diagonal matrix direction.

Choose a Hilbert–Schmidt orthonormal basis $H_a$, $1\le a\le e^2-1$, of the traceless Hermitian environmental space. Put

<a id="eq-preparation-32-1"></a>

$$
\tau_a^\pm
=I_E/e\pm H_a/(2e),
\qquad
\xi_{ia}^\pm=\rho_i\otimes\tau_a^\pm.
\tag{32.1}
$$

<a id="statement-preparation-32-1"></a>

**命题 32.1（Finite product-pair basis of hidden joint differences）。** Every $\tau_a^\pm$ is a faithful density with minimum eigenvalue at least $1/(2e)$. Each pair $\xi_{ia}^+,\xi_{ia}^-$ consists of product states with the same system marginal $\rho_i$. Their differences form a real basis of

<a id="eq-preparation-32-2"></a>

$$
\ker\operatorname{Tr}_E
=\operatorname{Herm}(S)\otimes\operatorname{Herm}_0(E)
=W^\perp.
\tag{32.2}
$$

There are exactly $d^2(e^2-1)$ selected pairs, requiring at most $2d^2(e^2-1)$ preparations.

**证明。** Each $H_a$ is traceless and $\lVert H_a\rVert_{\rm op}\le\lVert H_a\rVert_2=1$, so (32.1) has trace one and is bounded below by $I_E/(2e)$. Tensoring with $\rho_i$ gives the stated product states and equal system marginals. Their differences are

$$
\xi_{ia}^+-\xi_{ia}^-
=\rho_i\otimes H_a/e.
$$

The $d^2$ spanning system densities form a real basis, as do the environmental $H_a$. Their tensor products form a basis of the middle space in (32.2). Expanding the environmental factor in its normalized identity and traceless basis shows that partial trace kills exactly the traceless-factor terms. This gives (32.2) and the exact pair count. $\square$

No entangled preparation is required by this particular certificate. The finite-dimensional complex tensor factorization and the ability to vary the environment remain supplied premises.

For any one fixed channel $\Lambda$ on the joint input and any specified output effect span, equality of output responses on every selected pair is therefore equivalent to equality on every pair of joint density matrices with the same system marginal. This uses the same linear channel and the exact span (32.2); it does not assert physical preparability of the untested states. A list of $d^2$ spanning system output effects suffices to compare complete system output matrices. For recorded instruments, use that list separately in every branch, as in §31.

<a id="statement-preparation-32-2"></a>

**应用 32.2（Finite input certificate for the existing product-unitary theorem）。** Let

$$
\Lambda(\rho)=\operatorname{Tr}_E(U\rho U^*)
$$

for one fixed global unitary $U$ on $S\otimes E$. If its system output matrices agree on every selected pair in (32.1), then (32.2) supplies the all-joint-state autonomy premise of V38 Theorem 8.1. Directly reusing that theorem gives

<a id="eq-preparation-32-3"></a>

$$
U=W_S\otimes V_E.
\tag{32.3}
$$

The product-unitary result is an existing supplier, not a new proof or novelty claim here. The finite actual product-pair test supplies its conditional input certificate. A single fixed environmental ready state does not supply (32.2) and cannot replace these tests. For $e=1$, the hidden kernel and test list are empty and the product decomposition is automatic.

## 33. Calibration and acquisition remain part of the source contract

### 33.1. Calibration belongs to the declared preparation domain

For a target pair $d_a=\rho_a-\sigma_a$, suppose the two actual preparations are at trace distances at most $\zeta_a^+,\zeta_a^-$ from their targets. For a common input effect $0\le B\le I$, the resulting probability-gap bias is at most $\zeta_a^++\zeta_a^-$: each effect expectation changes by at most the corresponding trace distance. Add the specified readout-estimation errors to obtain $\nu_a$ in (28.5). A simultaneous confidence guarantee requires its own sampling assumptions and is not supplied here.

Current $W$ responses can supply full trace-distance calibration when they determine the state on the declared domain with a controlled inverse error bound. An incomplete interface on that domain need not do so. Completeness on a restricted domain differs from completeness on all density matrices.

For an explicit finite-dimensional calibration contract, let $F_1,\ldots,F_m$ be the measured effects and write

<a id="eq-preparation-33-1"></a>

$$
\mathsf p(\rho)
=\bigl(\operatorname{Tr}(F_\ell\rho)\bigr)_{\ell=1}^m,
\qquad
\mathsf M(h)
=\bigl(\operatorname{Tr}(F_\ell h)\bigr)_{\ell=1}^m.
\tag{33.1}
$$

The target and the actual prepared state must belong to the same known domain $Q$.

If all calibration effects lie in $W$ and their responses are injective on this same $Q$, then $\mathcal K_Q=\{0\}$; a nontrivial equal-response pair cannot be fully calibrated from those $W$ responses alone without additional information.

### 33.2. Compact injectivity gives an inverse modulus

For compact $Q$ and $\delta\ge0$, define

<a id="eq-preparation-33-2"></a>

$$
\omega_Q(\delta)
=\max_{\substack{\rho,\sigma\in Q\\
\lVert\mathsf p(\rho)-\mathsf p(\sigma)\rVert_2\le\delta}}
D(\rho,\sigma),
\qquad
D(\rho,\sigma)=\frac12\lVert\rho-\sigma\rVert_1.
\tag{33.2}
$$

The constraint set is nonempty and compact, so the maximum exists. The response map $\mathsf p$ is injective on $Q$ exactly when $\omega_Q(0)=0$. Under injectivity, $\omega_Q(\delta)\to0$ as $\delta$ decreases to zero.

To prove the last assertion, suppose instead that pairs with response differences tending to zero have state distances bounded below by a positive number. Compactness of $Q\times Q$ gives a convergent subsequence. The limits remain distinct but have equal responses, contradicting injectivity. This is the standard compact inverse-continuity argument. It gives no numerical convergence rate by itself.

### 33.3. Positive conditioning gives a linear calibration rate

For a domain $Q$ containing at least two states, a sufficient Lipschitz condition is

<a id="eq-preparation-33-3"></a>

$$
s_Q
=\inf_{\substack{\rho,\sigma\in Q\\\rho\ne\sigma}}
\frac{\lVert\mathsf M(\rho-\sigma)\rVert_2}
{\lVert\rho-\sigma\rVert_2}
>0.
\tag{33.3}
$$

Trace norm is at most $\sqrt D$ times Hilbert–Schmidt norm, by the Euclidean comparison of the $D$ eigenvalues. Therefore

<a id="eq-preparation-33-4"></a>

$$
D(\rho,\sigma)
\le\frac{\sqrt D}{2s_Q}
\lVert\mathsf p(\rho)-\mathsf p(\sigma)\rVert_2.
\tag{33.4}
$$

On a singleton domain, state distance is identically zero and no conditioning constant is needed.

For a nontrivial affine direction space $L=\operatorname{span}_{\mathbb R}(Q-Q)$, a directly computable sufficient constant is the least singular value $s_L$ of $\mathsf M|_L$, using Hilbert–Schmidt norm on $L$. If $\mathsf M$ is injective on $L$, finite dimension gives $s_L>0$ and $s_Q\ge s_L$, so (33.4) may use $s_L$. In an orthonormal basis of $L$, $s_L$ is the square root of the smallest eigenvalue of the measurement Gram operator $\mathsf M^*\mathsf M$.

### 33.4. Convex domains and a separated nonconvex catalog have different conditioning

For convex $Q$, injectivity of $\mathsf p$ on $Q$ is equivalent to injectivity of $\mathsf M$ on $L$. Indeed, a nonzero kernel direction in $L$ and the relative ball of §29 would produce two distinct states of $Q$ with the same responses. Conversely, the difference of an indistinguishable pair lies in that kernel. Every direction in $L$ is realized by a scaled difference from the relative ball. Hence $s_Q=s_L$ for a nontrivial convex domain.

For nonconvex $Q$, the equivalence fails. The three-state catalog of §30 is separated by the single effect $\operatorname{diag}(0,1/2,1)$, although its two-dimensional diagonal affine direction space has a nonzero measurement kernel. Its minimum nonzero response gap is $1/2$, and every pairwise Hilbert–Schmidt state distance is $\sqrt2$. Thus

$$
s_Q=\frac1{2\sqrt2}>0,
\qquad s_L=0.
$$

### 33.5. An injective arc has a sharp square-root rate without a Lipschitz inverse

Injectivity on a compact nonconvex family need not give positive $s_Q$. On a qubit, take the known preparation arc

<a id="eq-preparation-33-5"></a>

$$
\begin{aligned}
\rho_t&=|\psi_t\rangle\langle\psi_t|,
\qquad
|\psi_t\rangle=\cos t|0\rangle+\sin t|1\rangle,\\
0&\le t\le\pi/4,
\qquad F=|1\rangle\langle1|.
\end{aligned}
\tag{33.5}
$$

The measured probability $p(t)=\sin^2t$ is strictly increasing and identifies every state on this declared arc. For $0\le s\le t\le\pi/4$,

<a id="eq-preparation-33-6"></a>

$$
\begin{aligned}
D(\rho_t,\rho_s)&=\sin(t-s),\\
p(t)-p(s)
&=\sin(t+s)\sin(t-s)
\ge\sin^2(t-s).
\end{aligned}
\tag{33.6}
$$

The inequality uses $t+s\ge t-s$ and monotonicity of sine on $[0,\pi/2]$. It follows that $D(\rho_t,\rho_s)\le\sqrt{|p(t)-p(s)|}$, with equality for $s=0$. Consequently the inverse modulus is exactly $\omega_Q(\delta)=\sqrt\delta$ for $0\le\delta\le1/2$.

Nevertheless $s_Q=0$: at $s=0$, the ratio in (33.3) is $\sin t/\sqrt2$ and tends to zero. This restricted-domain readout is complete and has a sharp square-root calibration rate, while admitting no finite Lipschitz inverse constant.

Every state on the arc has spectrum $(1,0)$, so spectral data do not improve that rate. If the source instead admits the signed arc $-\pi/4\le t\le\pi/4$, then $p(t)=p(-t)$ although $\rho_t\ne\rho_{-t}$ for $t\ne0$. The spectrum and current $F$ response no longer identify the state. The additional effect $|+\rangle\langle+|$ has response difference $\sin(2t)$ between $\rho_t$ and $\rho_{-t}$; at $t=\pi/4$ it distinguishes them perfectly. The sign restriction is part of the source contract and is not inferred from the single measured probability.

### 33.6. Readout errors feed into the preparation calibration

Suppose estimates satisfy $|\widetilde p_\ell-p_\ell(\rho_{\rm actual})|\le\eta_\ell$, and the target $\rho_*$ lies in the same domain $Q$. Put $e_\ell=|\widetilde p_\ell-p_\ell(\rho_*)|+\eta_\ell$. A supplied inverse modulus gives

<a id="eq-preparation-33-7"></a>

$$
D(\rho_{\rm actual},\rho_*)
\le\omega_Q(\lVert e\rVert_2).
\tag{33.7}
$$

In the positive-conditioning case, (33.4) gives the upper bound $\sqrt D\lVert e\rVert_2/(2s_Q)$, or the version with certified $s_L$. These estimates can supply $\zeta_a^+$ and $\zeta_a^-$ for the probe targets in §33.1. They require membership in the declared state domain, known effects, common calibration conventions and a certified rate. Admitting unmodeled hidden components changes the domain and requires checking the restricted inverse guarantee again.

### 33.7. Existing suppliers and unresolved acquisition

At the fixed dev source pin `e307ede5b6d5d591f8bc44a4ec150d302e7f31a6`, acquisition-IV §§18–22 concern coherent historical recording and retain an unproved logarithmic sufficiency target. Those results supply neither a quantum preparation ball nor the product probes (32.1).

The existing suppliers and their distinct interfaces are:

- *AURIC_COMPLETE_QUANTUM_PROCESSES_INTERNAL_MEMORY_AND_RANK_BOUNDARY_STABILITY_V38.md*, Theorem 8.1: all-joint-state autonomy forces a product unitary. Its adjacent discussion already separates a fixed environmental ready-state input family.
- `D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence.lean`: centered response spans and positive perturbations around $I/D$ supply the full-state tomography equivalence. This is a source reference, without a current compilation claim.
- `D5/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate.lean`: an informationally complete effect family has a finite separating subfamily of at most $D^2-1$ effects. This selects effects and does not itself supply preparation pairs inside an arbitrary $Q$.
- Quantum-origin atlas II §§90–93: finite weighted state-design tests concern a different fixed-chart decoder frontier. Their moment calculation and preparation-resource boundary retain their scope; no design-to-fibre identification is asserted.
- Sections 9–17 of this volume: the all-density predictor-distance and complete recorded-instrument closure results are distinct from a restricted-source span. Sections 27–32 keep the comparison quantifiers attached to the declared preparation domain and give its finite linear certificates.

Finite basis extraction, Gram inversion, relative-interior geometry, compact inverse continuity and Cauchy–Schwarz are standard mathematical tools. Their use here is a conditional application to the specified source, fibre and record contracts. The remaining AURIC bridge is to supply $Q$, its actual prepared equal-response pairs, their calibration, the common operations and complete records, together with any required successor-family closure.

The tests do not establish source-setting independence, a globally compatible $\omega$, information conservation, physical resources or quantum origin. The displayed results remain conditional paper deductions without fresh Lean compilation or physical validation.

## 追加锚（本行以下为增补区）


## 34. Fix the visible projection and every complete instrument

This continuation is a conditional application of telescoping, trace-norm contraction, geometric summation and finite-dimensional rank arguments to the declared prediction problem. The observable algebra, preparations, common instruments and complete-record resources are supplied premises. These standard tools do not obtain those interfaces or establish a new general principle of quantum origin.

Let $H$ have finite complex dimension $D$, and let $\mathcal A$ be a represented unital $*$-algebra on $H$. Its complete effect interval is the declared current observation interface. Let $P$ be the trace-preserving conditional expectation onto $\mathcal A$, and put $Q=\operatorname{id}-P$. Thus $P$ is completely positive, trace preserving, idempotent and self-adjoint for the real Hilbert–Schmidt pairing $\operatorname{Tr}(XY)$.

The represented density $P\rho$ is the block conditional expectation, including normalized identities on multiplicity factors as in §§1–8. It is not the smaller direct-sum visible density used in that classification. The distinction matters when taking norms on the original represented carrier.

Use real Hermitian spaces and trace norm. Two density matrices have the same current $\mathcal A$ responses exactly when $P\rho=P\sigma$. Their difference $h=\rho-\sigma$ belongs to $K=\ker P$ and has trace zero. The projection represents the visible state mathematically; its use below applies neither a physical reset nor an actual $P$ operation to the source.

If $K=\{0\}$, every equal-response pair is identical. All prediction widths are zero, and $b=\beta=0$ may be chosen in the vacuous hidden inequalities. No probe Gram matrix or smallest Gram eigenvalue is used in this case. The nonzero hidden-difference premise in §39 then has no instance.

<a id="statement-hidden-34-1"></a>

**定义 34.1（Uniform complete-instrument residual bounds）。** For every allowed control $j$, supply one fixed finite instrument $\{\Lambda_x^j\}_x$ on $H$. Each branch is completely positive and trace nonincreasing, their sum is trace preserving, and all failure outcomes are retained. Write the recorded channel and its block norm as

<a id="eq-hidden-34-1"></a>

$$
\Gamma_j(h)=\bigoplus_x\Lambda_x^j(h),
\qquad
\left\lVert\bigoplus_xh_x\right\rVert_1
=\sum_x\lVert h_x\rVert_1.
\tag{34.1}
$$

On recorded outputs, $P$ and $Q$ act separately in each classical block. Suppose common constants $b\ge0$ and $0\le\beta<1$ satisfy, for every allowed $j$ and every Hermitian $h\in K$,

<a id="eq-hidden-34-2"></a>

$$
\begin{aligned}
\sum_x\lVert P\Lambda_x^j(h)\rVert_1
&\le b\lVert h\rVert_1,\\
\sum_x\lVert Q\Lambda_x^j(h)\rVert_1
&\le\beta\lVert h\rVert_1.
\end{aligned}
\tag{34.2}
$$

The first line measures immediate transfer of currently hidden differences into complete visible output. The second independently bounds the remaining hidden part. Small immediate transfer, scalar occupation decay or a spectral gap measured in another norm does not establish the second line. The signed map $Q$ is not a positive physical operation.

Trace-norm contraction of the recorded channel and of $P$ supplies a first-line constant at most one. There is no corresponding trace-norm contraction guarantee for $Q=\operatorname{id}-P$, so a hidden constant below one is a substantive premise.

## 35. Adaptive complete histories retain the same residual budget

Fix a finite depth $n$. A policy selects the next allowed control from the entire preceding classical history, by the same rule under both source hypotheses. Retain all old records. Each stage is then a completely positive trace-preserving map $\Gamma_t$ from the direct sum over old histories to the direct sum over extended histories. Different history blocks can select different controls. Let $P_t$ act as $P$ on every block and let $Q_t=\operatorname{id}-P_t$.

For a blockwise hidden Hermitian input, summing (34.2) over histories preserves the same constants $b,\beta$. A randomized policy is included when its randomness is common and source independent: retain the random labels and use the corresponding convex mixture. The policy may not read an additional hidden preparation label outside this channel contract.

Define the actual recorded process and a mathematical residual chain by

<a id="eq-hidden-35-1"></a>

$$
\begin{aligned}
T_n&=\Gamma_n\cdots\Gamma_1,\\
h_0&=h,
\qquad h_t=Q_t\Gamma_t(h_{t-1}).
\end{aligned}
\tag{35.1}
$$

Each $h_t$ is blockwise in $\ker P$, and $\lVert h_t\rVert_1\le\beta^t\lVert h\rVert_1$. These are signed residual operators, not density states or an additional experimental procedure.

<a id="statement-hidden-35-1"></a>

**命题 35.1（Complete-history telescoping with later hidden reentry retained）。** The actual process has the exact decomposition

<a id="eq-hidden-35-2"></a>

$$
T_nh
=h_n+
\sum_{t=1}^n
\Gamma_n\cdots\Gamma_{t+1}
P_t\Gamma_t(h_{t-1}),
\tag{35.2}
$$

where the suffix at $t=n$ is the identity. Consequently,

<a id="eq-hidden-35-3"></a>

$$
\boxed{
\lVert P_nT_nh\rVert_1
\le b\frac{1-\beta^n}{1-\beta}\lVert h\rVert_1,
}
\tag{35.3}
$$

and the complete output satisfies

<a id="eq-hidden-35-4"></a>

$$
\lVert T_nh\rVert_1
\le
\left(\beta^n+b\frac{1-\beta^n}{1-\beta}\right)
\lVert h\rVert_1.
\tag{35.4}
$$

Both left sides additionally obey the ordinary completely positive trace-preserving bound $\lVert h\rVert_1$.

**证明。** Expand $\Gamma_t(h_{t-1})=P_t\Gamma_t(h_{t-1})+h_t$ successively to obtain (35.2). After a term enters the $P_t$ component, its full subsequent physical channel stays in that term. Later transfer back into hidden degrees of freedom is therefore included. This is an identity of signed operators, not a positive probability-history decomposition.

Each physical suffix in (35.2) contracts trace norm on Hermitian inputs. Applying $P_n$ kills $h_n$. The $t$th remaining term has norm at most $b\lVert h_{t-1}\rVert_1\le b\beta^{t-1}\lVert h\rVert_1$. Summing the finite geometric series gives (35.3). Retaining $h_n$ and its bound gives (35.4). Finally, $T_n$ and $P_nT_n$ are completely positive and trace preserving, giving their separate ordinary contraction bounds. $\square$

For source states with $P\rho=P\sigma$, put $\delta_0=\lVert\rho-\sigma\rVert_1/2$ and use $D(A,B)=\lVert A-B\rVert_1/2$. Then

<a id="eq-hidden-35-5"></a>

$$
\begin{aligned}
D(P_nT_n\rho,P_nT_n\sigma)
&\le\delta_0\min\left\{
1,b\frac{1-\beta^n}{1-\beta}\right\}\\
&\le\delta_0\min\left\{1,\frac b{1-\beta}\right\}.
\end{aligned}
\tag{35.5}
$$

Because the interface includes every $\mathcal A$ effect in each history block, this controls every final event depending jointly on the complete classical history and a terminal $\mathcal A$ measurement. In particular it bounds total variation of the entire classical record. No unlikely failure has been conditioned away.

The estimate is uniform over every finite depth and every policy meeting the common-instrument contract. It requires no physically completed infinite process and no fixed finite register storing all possible histories. Each declared finite run must supply its actual record backing and common control resources.

One may instead impose (34.2) on a real subspace $K_0\subseteq\ker P$ when it contains all permitted initial equal-response differences and every branch $Q\Lambda_x^j$ preserves $K_0$. Without this invariance, a bound tested only on the initial preparation span does not control the residual chain in (35.1).

## 36. Ordered residual envelopes and the limits of the comparison

The same telescoping permits depth-dependent constants $b_t,\beta_t$:

<a id="eq-hidden-36-1"></a>

$$
\lVert P_nT_nh\rVert_1
\le
\left(\sum_{t=1}^n b_t\prod_{s<t}\beta_s\right)
\lVert h\rVert_1.
\tag{36.1}
$$

More generally, if every permitted hidden residual chain has a verified envelope $\lVert h_t\rVert_1\le a_t\lVert h\rVert_1$ with $a_0=1$, the budget is $\sum_{t=1}^n b_ta_{t-1}$. An envelope $\lVert h_t\rVert_1\le Mr^t\lVert h\rVert_1$, with $M\ge1$ and $0\le r<1$, gives the conservative uniform upper budget $bM/(1-r)$ when $b_t\le b$.

Such an envelope concerns the actual ordered hidden products under every allowed switch. Individual asymptotic eigenvalue radii do not supply it.

The comparison is between two actual processes that begin with the same current observations. It is not an error bound between $T_n$ and a proposed Markov predictor, and it certifies no particular completely positive quotient update. A canonical representative chosen inside a fibre still needs an actual completely positive interface.

Classical adaptive records are covered. An extra coherent controller or untouched quantum reference changes the state space and the equivalence relation. A reference-stable version requires the needed matrix-amplified instances of (34.2), with $P\otimes\operatorname{id}$ and equality under that enlarged projection. Ordinary trace-norm inequalities do not certify this stronger contract. Every persistent quantum controller must already belong to the modeled $H$ or be included through the amplified bounds.

The preparation family remains part of the task. Enlarging its hidden span, allowing new operations or inspecting extra memory changes the hypotheses of (34.2), rather than merely changing a reported prediction.

## 37. A rare-readout instrument attains both finite geometric bounds

Take a hidden qubit with coordinate densities $P_0,P_1$, write $u=I_2/2$, and use the scalar visible algebra. Thus $P(X)=\operatorname{Tr}(X)u$. For $0\le b\le1-\beta$ and $0\le\beta<1$, supply the four outcomes reveal-$0$, reveal-$1$, keep and erase:

<a id="eq-hidden-37-1"></a>

$$
\begin{aligned}
\Lambda_{r_a}(X)
&=b\operatorname{Tr}(P_aX)u
\quad(a=0,1),\\
\Lambda_k(X)&=\beta X,\\
\Lambda_e(X)
&=(1-b-\beta)\operatorname{Tr}(X)u.
\end{aligned}
\tag{37.1}
$$

Every branch is completely positive and trace nonincreasing, and the sum is trace preserving. For a trace-zero Hermitian $h$, the reveal outputs are visible, the keep output is hidden and the erase output is zero. The first coefficient in (34.2) is at most $b$ and the second is exactly $\beta$. Taking $h=P_0-P_1$ also attains the first coefficient $b$.

Repeat this same instrument, keep every outcome, and compare initial states $P_0,P_1$. Until the first non-keep outcome, the qubit retains the original bit. A reveal records its exact value and leaves $u$. An erase also leaves $u$, so subsequent records contain no further information about the original bit. Once revealed, the earlier recorded value remains available.

Only histories with a reveal before the first erase differ visibly. Their total probability is

<a id="eq-hidden-37-2"></a>

$$
b\sum_{t=0}^{n-1}\beta^t
=b\frac{1-\beta^n}{1-\beta}.
\tag{37.2}
$$

The two source labels are disjoint on those histories; all other visible histories have identical laws. Thus the complete-record total variation is exactly (37.2), attaining (35.5) with $\delta_0=1$. The only extra joint distinguishability lies on the all-keep history, of probability $\beta^n$, where the hidden qubit still differs. The same initial state pair therefore attains (35.4) as well.

These are stipulated mathematical instruments. Their measurements, storage and fresh environments, including an erasure dilation, are distinct resources. The completely positive reset is an explicit branch of this example and was not inserted as a free operation into the proof of (35.2).

For $b=\epsilon$, $\beta=1-\epsilon$ and $0<\epsilon<1$, each step has arbitrarily small immediate visible leakage as $\epsilon$ decreases, while the complete record distinguishes the original bit with probability $1-(1-\epsilon)^n$, tending to one. The uniform ratio $b/(1-\beta)$ equals one throughout this family.

## 38. An incomplete one-step interface need not establish hidden decay

Fix $0<\epsilon<1$ and retain the reveal branches $\epsilon\operatorname{Tr}(P_aX)u$. Give two instruments the same additional outcome $f$, but choose its map differently:

$$
\Lambda_f^{\rm keep}(X)=(1-\epsilon)X,
\qquad
\Lambda_f^{\rm erase}(X)
=(1-\epsilon)\operatorname{Tr}(X)u.
$$

For every input density, the reveal probabilities and the failure probability $1-\epsilon$ agree. At the scalar visible algebra, their entire one-step visible recorded output channels are identical. Both have immediate coefficient $b=\epsilon$, while their hidden coefficients are $\beta=1-\epsilon$ and $\beta=0$, respectively.

After $n$ repetitions from $P_0$ versus $P_1$, the first instrument has complete-record total variation $1-(1-\epsilon)^n$. The second has exactly $\epsilon$: an initial failure erases the bit and makes all later records common; an initial reveal already distinguishes the two disjoint first labels. All failure records are retained in both models.

Even exact one-step visible tomography on every input therefore does not determine hidden contraction or the unlimited-depth budget. A hidden-output measurement or an additional structural channel contract can distinguish these poststate realizations.

This ambiguity concerns the incomplete output interface in the example. Full output tomography on a spanning input family would determine the branch poststates and distinguish the two instruments.

The finite preparation certificate makes the extra evidence explicit. For one fixed instrument, let $b_*,\beta_*$ denote its least operator constants in the two inequalities of (34.2), without assuming $\beta_*<1$.

If $K=\{0\}$, take $b_*=\beta_*=0$ and omit the Gram division. The following Gram estimates assume $\dim K>0$.

Let $d_a$ be a real basis of $K$ selected from actual equal-response preparation differences, with positive-definite Gram matrix $G_{ab}=\operatorname{Tr}(d_ad_b)$. Define

<a id="eq-hidden-38-1"></a>

$$
V_a=\bigoplus_xP\Lambda_x(d_a),
\qquad
Z_a=\bigoplus_xQ\Lambda_x(d_a).
\tag{38.1}
$$

Finite reconstruction gives valid, possibly loose estimates

<a id="eq-hidden-38-2"></a>

$$
\begin{aligned}
b_*
&\le
\frac{\left(\sum_a\lVert V_a\rVert_1^2\right)^{1/2}}
{\sqrt{\lambda_{\min}(G)}},\\
\beta_*
&\le
\frac{\left(\sum_a\lVert Z_a\rVert_1^2\right)^{1/2}}
{\sqrt{\lambda_{\min}(G)}}.
\end{aligned}
\tag{38.2}
$$

Indeed, for $h=\sum_ac_ad_a$,

$$
\lVert c\rVert_2
\le\frac{\lVert h\rVert_2}{\sqrt{\lambda_{\min}(G)}}
\le\frac{\lVert h\rVert_1}{\sqrt{\lambda_{\min}(G)}}.
$$

Apply the triangle inequality to the corresponding $V_a$ or $Z_a$ sum, followed by scalar Cauchy–Schwarz. This proves both estimates. Certified output-norm upper errors and a certified Gram lower bound can be included. An obtained upper bound at least one does not prove failure of actual hidden contraction.

Sufficiently complete visible-output tomography can determine the $V_a$ under its preparation contract. The $Z_a$ require hidden-output information or a verified full map. The same visible probability table does not supply them, as the paired example demonstrates. Exact zero visible gaps on the chosen pairs certify $b=0$; small visible gaps alone do not certify $\beta<1$.

## 39. Conserved complete distinguishability imposes an exit budget

Suppose a nonzero initial hidden difference retains its full trace norm under every complete $n$-stage process being compared:

$$
\lVert T_nh\rVert_1=\lVert h\rVert_1.
$$

This conservation premise concerns the modeled complete output, including every quantum memory needed for the assertion. Equation (35.4) gives

<a id="eq-hidden-39-1"></a>

$$
1\le\beta^n+b\frac{1-\beta^n}{1-\beta},
\qquad
\boxed{b\ge1-\beta.}
\tag{39.1}
$$

For $\beta<1$, any $n\ge1$ gives the second inequality after dividing by $1-\beta^n$. The strict ratio $b/(1-\beta)<1$ therefore cannot coexist with conserved hidden distinguishability. For the general envelope in §36, if $a_n\to0$ and complete distinguishability is conserved, the cumulative exit budget $\sum_{t\ge1}b_ta_{t-1}$ must be at least one.

This is a necessary condition on norm budgets; it does not say that every quantum model has a visible event attaining that budget. The rare-readout instrument with $b=1-\beta$ preserves the norm of the difference of the two classical basis states and transfers it to its record over increasing finite horizons. It need not preserve arbitrary unknown quantum superpositions, because classical revelation has a different coherence contract.

A closed isometry acting on all modeled source and memory degrees of freedom preserves the trace norm of every Hermitian difference. If an effective channel has $\beta<1$ and $b/(1-\beta)<1$, its complete modeled output cannot retain the conserved hidden distinguishability above. This does not establish global information destruction. An omitted dilation environment, a discarded quantum record, a restricted source family or a weaker meaning of conservation can remove that premise. The missing degrees of freedom must be identified before applying a closed-system information-conservation interpretation.

<a id="statement-hidden-39-1"></a>

**有限维检验 39.1（A fixed closed unitary cannot contract an oversized full hidden kernel）。** For a fixed unitary $U$ on the same carrier, let $m=\operatorname{rank}_{\mathbb R}P$ on $\operatorname{Herm}(H)$. Then $\dim K=D^2-m$. If $D^2-m>m-1$, the real linear map

<a id="eq-hidden-39-2"></a>

$$
P\operatorname{Ad}_U|_K:
K\longrightarrow\operatorname{ran}P\cap\operatorname{Herm}_0(H)
\tag{39.2}
$$

has a nonzero kernel, since its target has dimension $m-1$. For a nonzero $h$ in that kernel,

$$
Q\operatorname{Ad}_U(h)=\operatorname{Ad}_U(h),
\qquad
\lVert\operatorname{Ad}_U(h)\rVert_1=\lVert h\rVert_1.
$$

The least full-hidden one-step coefficient is thus at least one, and the strict full-kernel premise of (34.2) fails for every such unitary.

For $H=S\otimes E$ with $\dim S=d$ and $\dim E=e\ge2$, take

$$
P(X)=\operatorname{Tr}_E(X)\otimes I_E/e.
$$

Then $m=d^2$ and $D^2-m=d^2(e^2-1)>d^2-1$. No closed joint unitary on this same carrier therefore strictly contracts the entire hidden kernel in one-step trace norm. The claim concerns that full kernel and that one-step norm. It does not exclude a restricted invariant source subspace, a longer mathematical projected-product envelope, a growing record space or an effective channel that discards an environment.

## 40. Existing tools and the remaining complete-memory interface

The fixed dev source pin is `e307ede5b6d5d591f8bc44a4ec150d302e7f31a6`. Atlas II §§156–163 contain the all-spectrum transposition application, attributing the affine optimum to Brzić–Grinko–Studziński–Quintino, [arXiv:2603.23628v3](https://arxiv.org/abs/2603.23628v3). Atlas III §§1–8 contain the visible-purity and invisible-fibre results. Neither supplies (34.2) from current preparation records.

The reused mathematical context has distinct interfaces:

- *CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md*, Definition 56.1 and Proposition 56.3: geometric hidden-block bounds give finite task memory-tail budgets. Example 56.5 retains norm-envelope and nonnormality qualifications. Those linear-tail results provide context, without a new proof or novelty claim for geometric summation.
- *AURIC_APPROXIMATE_CLOSURE_HIDDEN_MEMORY_AND_NATIVE_RECURSION_V40.md*, Theorems 3.2–3.3: exact block memory kernels. Its §§2.3–2.4 distinguish occupation decay, full-state contraction, a final channel and a retained first-transfer archive. That amplitude model is not identified with the instruments of §37.
- Sections 9–17: complete recorded-instrument closure differs from the nonselective channel. The finite-horizon sum of approximation errors there is not promoted to a uniform unbounded estimate.
- Sections 27–33: actual equal-response pair spans and Gram conditioning supply the finite reconstruction interface used in (38.1)–(38.2). They remain conditional paper dependencies and provide no fresh Lean compilation evidence.

The complete-record telescoping, adaptive-policy estimate, paired poststate realizations and conservation/rank tests apply those established tools to the specified prediction question. The source must still supply common instruments, the complete quantum memory model, preparation alternatives, output calibration, allowed policies and a genuine hidden norm envelope. Scalar decay, a spectral catalogue or one actual $\omega$ path alone discharges none of these obligations. Conversely, effective-channel assumptions cannot be silently imported into a fully closed information-conserving interpretation.

These are conditional paper deductions, without a novelty claim, fresh Lean compilation or physical validation. They do not settle quantum origin, source-setting independence or the existence of a universal state.

## 追加锚（本行以下为增补区）

## 41. Fix the whole returned source at one cut

These are conditional paper deductions about independent settings,
proportional instrument branches and returned memory. All finite
quantum interfaces, preparations, instruments, output calibration and
corrections below are supplied premises. The arguments use standard
finite-dimensional channel linearity, convexity, Choi reconstruction and
trace-norm estimates. No mathematical priority or physical realization
claim is made.

Let H and R be nonzero finite-dimensional complex Hilbert spaces, with
d=dim H. Let S be a nonempty finite set of classical setting labels.
An actual, fixed instrument consists of complex-linear CP maps
M_s:B(H)->B(R), with

$$
\Theta=\sum_{s\in S}M_s\quad\hbox{CPTP},\qquad
\Gamma(X)=\sum_{s\in S}|s\rangle\langle s|\otimes M_s(X).
\tag{41.1}
$$

Every failure, stop and other outcome belongs to S, or to a declared
complete record refining S. No success normalization is used. If some
outcomes cannot be assigned a setting with the required local readout,
the later four-setting consumer does not apply to those runs without
an additional complete-output construction.

For a coarser designated setting s, retain any other relevant record
labels in R when defining M_s. Dropping those labels before the tests
cannot certify independence from the complete returned source.

R contains every returned source degree, controller, clock, auxiliary
and memory that can later affect results. An untouched reference T can
be correlated with H, and R tensor T is then the full returned source.
The designated setting record S is separate: its subsequent use is
only through the declared setting-controlled result interfaces. An
additional source-side copy of S is part of R if it can return and
affect results. It cannot be silently discarded in an independence
claim about that source.

The instrument describes the classical-record protocol. Its claims do
not extend to later coherent interference between setting branches.
Any environment omitted from R tensor T is stipulated never to return
or control the later result. This is a finite operational cut, not a
claim of globally destroyed information.

The same CP instrument must act on the whole admitted input family.
Correlated setting seeds and controller memory cannot be hidden in a
fixed ancillary state: include operated degrees in H and untouched
source references in T, or restrict the claim to an explicitly
justified input domain. A fixed ready ancilla in a dilation is a
resource premise, not a consequence of a globally pure input.

The universal propositions below use all densities on H tensor T.
Independence on a restricted domain alone does not assert (43.1)
outside that domain.

For an arbitrary input density rho_HT, put

$$
\begin{aligned}
\tau_{SRT}&=(\Gamma\otimes\mathrm{id}_T)(\rho_{HT}),\\
q_s(\rho_H)&=\operatorname{Tr}M_s(\rho_H),\\
\sigma_{RT}&=(\Theta\otimes\mathrm{id}_T)(\rho_{HT}),\\
\delta(\rho_{HT})&=
 D(\tau_{SRT},q(\rho_H)\otimes\sigma_{RT}),\qquad
 D(\alpha,\beta)=\tfrac12\|\alpha-\beta\|_1.
\end{aligned}
\tag{41.2}
$$

Probability vectors also denote their diagonal density matrices.
The comparison in (41.2) uses the actual output marginals. It is not a
supplied physical decorrelation operation. A statement about every
rho_HT is stronger than independence for one actual source state.

## 42. Fixed setting probabilities do not fix the returned poststates

**Proposition 42.1 (what scalar effects certify).** A fixed probability
vector p obeys q_s(rho)=p_s for every density rho on H exactly when

$$
M_s^*(I_R)=p_s I_H\quad\text{for every }s.
\tag{42.1}
$$

Under (42.1), the output setting is independent of every untouched
reference T after discarding R:

$$
\tau_{ST}=p\otimes\rho_T
\quad\text{for every input }\rho_{HT}.
\tag{42.2}
$$

These conditions do not imply independence of S from R tensor T.

Proof. The trace defining q_s is the expectation of M_s^*(I_R).
Density matrices span the real Hermitian space, so equality of all
these expectations is equivalent to (42.1). Pairing the s-th block
of tau_ST with any effect F_T gives
Tr[rho_HT (M_s^*(I_R) tensor F_T)]=p_s Tr(rho_T F_T).
Effects determine the Hermitian block, giving (42.2).

For the failed implication take H=R=C^2, Z=diag(1,-1), and

$$
M_0(X)=\tfrac12 X,\qquad M_1(X)=\tfrac12 ZXZ.
\tag{42.3}
$$

Both setting effects equal I/2. For rho=|+><+| the returned branch
states are |+><+| and |-><-|. They are orthogonal. The setting law
is uniform, the source marginal is I/2, and

$$
\delta(\rho)=\tfrac12.
\tag{42.4}
$$

Indeed each conditional source has trace distance 1/2 from I/2;
the classical block norm in (41.2) averages these distances. The
setting law is input-independent while its post-generation source
is setting-dependent. This counterexample retains both outcomes.

It also has a pure-global isometric realization:

$$
V|\psi\rangle=\frac1{\sqrt2}\sum_{s=0}^1
 |s\rangle_S\otimes Z^s|\psi\rangle_R\otimes|s\rangle_E.
\tag{42.5}
$$

The mutually orthogonal S,E records give V^dagger V=I. The omitted
E is stipulated never to return. Tracing E gives the same recorded
channel. For the pure input |+>, both conditional returned sources
are pure with spectrum (1,0), while delta remains 1/2. Global purity
and equal conditional spectra therefore do not imply the missing
setting-source relation. The isometry is a declared construction,
not a history already acquired from a native gate menu.

## 43. A reference-complete channel criterion

**Proposition 43.1 (proportional branches).** The following are equivalent.

1. For every finite untouched T and every density rho_HT,
   delta(rho_HT)=0.
2. The same independence holds for every input with a binary classical
   reference T, including all equally weighted flags of two densities.
3. There is one fixed probability vector p such that

$$
\boxed{M_s=p_s\Theta\quad\text{as complex-linear maps, for every }s.}
\tag{43.1}
$$

The fixed p is allowed to have zero entries. Full support is a separate
condition needed by a four-conditional-setting consumer.

Proof. The first item includes the second. Under the second, feed

$$
\rho_{HT}=\tfrac12\rho_0\otimes|0\rangle\langle0|
           +\tfrac12\rho_1\otimes|1\rangle\langle1|
\tag{43.2}
$$

for arbitrary densities rho_0,rho_1. Independence of S from R tensor T
implies independence from the classical flag alone. Its two conditional
setting laws q(rho_0),q(rho_1) must therefore agree. Since the two
densities were arbitrary, there is a single setting law p on all
inputs. The product relation for an input rho tensor |0><0| now reads
M_s(rho)=p_s Theta(rho). Real Hermitian spanning and complex linearity
give (43.1) on every matrix. Conversely (43.1), tensored with id_T, gives
tau=p tensor sigma for every joint input, establishing the first item.

The scalar-effect condition (42.1) follows from (43.1), but (42.3) shows
that its converse fails. Equation (43.1) requires equality of complete
unnormalized branch poststates, rather than just their traces.

There is also a single entangled mathematical test. Let T=C^d and
Phi_d be the density of d^(-1/2) sum_i |i>_H|i>_T. Independence of
S from R tensor T for the one input Phi_d is equivalent to (43.1),
where p_s=Tr M_s(I_H/d). In fact the s-th Choi block must equal p_s
times the Choi matrix of Theta. The explicit expansion

$$
(M_s\otimes\mathrm{id})(\Phi_d)
 =\frac1d\sum_{i,j}M_s(E_{ij})\otimes E_{ij}
\tag{43.3}
$$

then identifies every matrix-unit image. This is the standard Choi
injectivity argument. The ability to prepare and measure that joint
input is not supplied by its mathematical existence. Section 46 gives
an alternative exact test using ordinary input densities.

Failure of (43.1) does not refute independence on one actual input.
For example, (42.3) is independent on rho=I/2, although it fails on
rho=|+><+|. The universal and actual-source claims have different
quantifiers.

## 44. Omitting a reference admits a second, erasing alternative

**Proposition 44.1 (unreferenced product-output classification).** Suppose
that for every density rho on H the S,R output is a product of its own
marginals:

$$
\Gamma(\rho)=q(\rho)\otimes\Theta(\rho).
\tag{44.1}
$$

Then at least one of the following holds:

1. q is constant on the entire density space, and (43.1) holds.
2. There is one density sigma_0 on R with

$$
\Theta(X)=\operatorname{Tr}(X)\sigma_0,\qquad
M_s(X)=\operatorname{Tr}(F_s X)\sigma_0,
\quad F_s\ge0,\quad\sum_sF_s=I_H.
\tag{44.2}
$$

Conversely either displayed type implies (44.1). The two types can
overlap. Neither the product-output classification nor the second
type asserts global information destruction.

Proof. Apply (44.1) to rho, sigma and t rho+(1-t)sigma for 0<t<1.
Linearity of Gamma, q and Theta yields

$$
t(1-t)[q(\rho)-q(\sigma)]\otimes
       [\Theta(\rho)-\Theta(\sigma)]=0.
\tag{44.3}
$$

A tensor of two finite real vectors is zero only if a factor is zero.
If q is constant, Hermitian spanning gives (43.1). Otherwise choose
rho_a,rho_b with different q values. Equation (44.3) gives
Theta(rho_a)=Theta(rho_b)=sigma_0. For any third density rho, either
q(rho) differs from q(rho_a), or it equals that value and differs
from q(rho_b). Applying (44.3) to the corresponding pair gives
Theta(rho)=sigma_0. In (44.1) each branch is now q_s(rho)sigma_0.
Put F_s=M_s^*(I_R) and extend by spanning to get (44.2).
Positivity and normalization of these effects follow from the
instrument. Conversely each type directly has product output.
The maps in (44.2) are CP: if sigma_0=sum_k lambda_k|k><k| and
F_s=sum_a f_sa|v_sa><v_sa|, Kraus operators
sqrt(lambda_k f_sa)|k><v_sa| give the stated branch.

The second alternative can fail the reference-complete property.
Take a qubit H, any fixed sigma_0 and F_s=|s><s| for s=0,1.
Every unreferenced output is q(rho) tensor sigma_0. On a Bell
input Phi_2 with untouched T, however, the output is

$$
\tau_{SRT}=\frac12\sum_{s=0}^1
 |s\rangle\langle s|\otimes\sigma_0\otimes|s\rangle\langle s|,
\qquad \delta(\Phi_2)=\tfrac12.
\tag{44.4}
$$

The returned R has forgotten the input, while the untouched source
reference retains its setting correlation. Independence from R alone
therefore does not justify independence from the complete source.

## 45. A supplied correction can remove branch dependence

Suppose R=H and actual branches are known to have the form

$$
M_s(X)=p_sU_s XU_s^\dagger,
\tag{45.1}
$$

where each U_s is a unitary and p is fixed. If the protocol supplies
the setting-controlled correction U_s^dagger on the whole returned
source, the corrected branches are

$$
M'_s(X)=U_s^\dagger M_s(X)U_s=p_sX.
\tag{45.2}
$$

Thus Proposition 43.1 supplies independence including every untouched
reference. In (42.3), applying Z on branch 1 and identity on branch 0
does this. Every setting record remains; there is no postselection.

The corrected source in (45.2) must be the complete returned source.
For example, if a returned controller C also contains an orthogonal
copy |s><s|, correcting the logical source alone gives

$$
M'_s(X)=p_sX\otimes|s\rangle\langle s|_C.
\tag{45.3}
$$

For two equally likely labels this still has delta=1/2 for every
input. A supplied controlled uncomputation can restore a known
controller copy to a common ready state while preserving S, but that
operation and its action on all other returned memory require proof.
There is no inference from logical-source restoration alone.

A calibrated pure ready marginal is mathematically uncorrelated with
the rest: a positive joint density supported on its one-dimensional
ready subspace factors with that marginal. Acquiring that marginal,
resetting it between uses and implementing (45.1)-(45.2) are resource
premises, rather than consequences of global pure-state notation.

If S is the pair (x,y), choosing a fixed full-support p_xy in (45.1)
and achieving (45.2) supplies the common-source input condition of the
existing CHSH result. It supplies no native gate menu or local
readout by itself. Fixed p is essential when invoking Proposition 43.1:
an input-dependent setting law is detectable by a binary correlated
reference, independently of a logical-source restoration claim.

## 46. Finite exact tomography certifies the full map equality

Fix an orthonormal basis |i>, 1<=i<=d, of H. Use the following d^2
pure density matrices:

$$
\begin{aligned}
P_i&=|i\rangle\langle i|,\\
P^+_{ij}&=\tfrac12(|i\rangle+|j\rangle)
                        (\langle i|+\langle j|),\\
P^{\mathrm{i}}_{ij}&=\tfrac12(|i\rangle+\mathrm{i}|j\rangle)
                        (\langle i|-\mathrm{i}\langle j|),
\qquad i<j.
\end{aligned}
\tag{46.1}
$$

They span Herm(H) over the reals. In particular, with E_ij=|i><j|,

$$
\begin{aligned}
A_{ij}&=2P^+_{ij}-P_i-P_j=E_{ij}+E_{ji},\\
B_{ij}&=2P^{\mathrm{i}}_{ij}-P_i-P_j
                              =-\mathrm{i}E_{ij}+\mathrm{i}E_{ji},\\
E_{ij}&=(A_{ij}+\mathrm{i}B_{ij})/2.
\end{aligned}
\tag{46.2}
$$

**Proposition 46.1 (finite exact branch certificate).** Suppose the
preparations in (46.1) and complete unnormalized output tomography on
the entire R, in every branch, are supplied for the same instrument.
For one fixed probability vector p, check

$$
M_s(P)=p_s\Theta(P)
\quad\text{for every }s\text{ and every probe }P\text{ in (46.1)}.
\tag{46.3}
$$

Then (43.1) holds, hence independence holds for every input and every
untouched reference. Conversely (43.1) implies all these checks.

Proof. Equations (46.2) and complex linearity extend (46.3) to every
matrix unit, hence every matrix. Apply Proposition 43.1.

Traces of the tests establish only (42.1). Normalized poststates
without their branch probabilities do not give (46.3). Summing over s
before comparison always returns Theta(P), which cannot test the
branch equality. Restricted visible-output tomography must first
be proved sufficient on the declared output domain; it does not
automatically provide full-R matrix equality or trace-norm errors.

The case d=1 uses its one density and no off-diagonal probes.
Zero-probability branches cause no division: they are tested as
zero maps. The certificate is exact and finite, not a free ability
to prepare the probes or to measure every returned memory.

## 47. A conservative error certificate valid with arbitrary references

Define the actual comparison map and its difference by

$$
\mathcal B(X)=p\otimes\Theta(X),\qquad
\Delta=\Gamma-\mathcal B.
\tag{47.1}
$$

Both Gamma and B are CPTP. Supply certified trace-norm bounds on
the full, unnormalized probe-output differences:

$$
\|\Delta(P_i)\|_1\le u_i,\quad
\|\Delta(P^+_{ij})\|_1\le u^+_{ij},\quad
\|\Delta(P^{\mathrm{i}}_{ij})\|_1\le u^{\mathrm{i}}_{ij}.
\tag{47.2}
$$

The u's are nonnegative and include preparation, full-output
calibration and reconstruction uncertainty needed to justify these
inequalities for the actual maps. Merely observing small scalar
probability errors does not supply (47.2).

**Proposition 47.1 (a complete-norm upper certificate).** Put

$$
\begin{aligned}
C&=\sum_i u_i+2\sum_{i<j}
          (u^+_{ij}+u^{\mathrm{i}}_{ij}+u_i+u_j),\\
\varepsilon&=\min\{1,C/2\}.
\end{aligned}
\tag{47.3}
$$

For every finite T and joint input density rho_HT,

$$
\begin{aligned}
\|\Delta\|_\diamond&\le\min\{2,C\},\\
D\bigl((\Gamma\otimes\mathrm{id})(\rho),
             p\otimes(\Theta\otimes\mathrm{id})(\rho)\bigr)
             &\le\varepsilon,\\
\delta(\rho)&\le\min\{1,2\varepsilon\}.
\end{aligned}
\tag{47.4}
$$

If the actual setting marginal on that input is p, the last bound
improves to delta(rho)<=epsilon. In particular that improvement
holds on all inputs when (42.1) is exact.

Proof. From (46.2), (47.2) and the triangle inequality,

$$
\|\Delta(E_{ii})\|_1\le u_i,\qquad
\|\Delta(E_{ij})\|_1,
\|\Delta(E_{ji})\|_1
 \le u^+_{ij}+u^{\mathrm{i}}_{ij}+u_i+u_j.
\tag{47.5}
$$

For arbitrary complex X on H tensor T, expand
X=sum_ij E_ij tensor X_ij. Each block is an isometric compression
of X on the left and right, so ||X_ij||_1<=||X||_1. Tensor
multiplicativity of trace norm and the triangle inequality give

$$
\begin{aligned}
\|(\Delta\otimes\mathrm{id})(X)\|_1
&\le\sum_{i,j}\|\Delta(E_{ij})\|_1\|X_{ij}\|_1\\
&\le\left(\sum_{i,j}\|\Delta(E_{ij})\|_1\right)\|X\|_1
 \le C\|X\|_1.
\end{aligned}
\tag{47.6}
$$

This is uniform over every finite reference dimension and every
complex input operator, hence bounds the diamond norm. The norm
of a CPTP map is one, giving the separate bound two for Delta.
The second line of (47.4) follows by applying the norm bound to a
unit-trace density and dividing by two.

Let tau be that actual output, sigma its actual RT marginal, and q
its actual S marginal. The comparison state is p tensor sigma:
the source marginal is exactly the same because sum_s M_s=Theta.
Marginal contraction gives D(q,p)<=epsilon. Therefore

$$
\begin{aligned}
\delta(\rho)
&\le D(\tau,p\otimes\sigma)+D(p\otimes\sigma,q\otimes\sigma)\\
&\le\varepsilon+D(p,q)\le2\varepsilon.
\end{aligned}
\tag{47.7}
$$

Trace distance is at most one. If q=p, the second term vanishes.

The coefficient in (47.3) is a conservative reconstruction bound,
not an optimal stability constant. It converts full-output errors
to a reference-complete claim using linearity; it does not treat
unassisted scalar-response errors as a diamond-norm certificate.
If the actual instrument varies with the probe or the source
preparation procedure, a single map Delta has not been supplied
and this argument cannot be used.

## 48. Consume the existing common-source result without changing it

Identify S with the four joint settings (x,y), and the complete
returned source Q with R tensor T. The common-source paper at
the source pin below defines the same own-marginal defect delta.
Its Theorem 2.3 supplies the conditional-state interpretation;
Theorem 3.2 supplies, for fixed local self-adjoint contraction
readouts and actual positive q_min,

$$
|S_{\rm obs}|\le
 \min\{4,\ 2\sqrt2+2\delta/q_{\min}\}.
\tag{48.1}
$$

No CHSH result is reproved here. If p_min=min_s p_s>0 and
epsilon<p_min, marginal contraction in (47.4) gives
q_s>=p_s-epsilon, so q_min>=p_min-epsilon>0. Substitution yields

$$
|S_{\rm obs}|\le
 \min\left\{4,\ 2\sqrt2+
                  \frac{4\varepsilon}{p_{\min}-\varepsilon}\right\}.
\tag{48.2}
$$

If q=p exactly, the stronger defect bound gives instead

$$
|S_{\rm obs}|\le
 \min\{4,\ 2\sqrt2+2\varepsilon/p_{\min}\}.
\tag{48.3}
$$

For uniform p, (48.3) has correction 8 epsilon. Exact proportional
branches give delta=0 and permit zero probe-error bounds and epsilon=0.
No positive conditional-setting support follows from an error bound
epsilon>=p_min, and none is
inserted into (48.2) in that case.

These statements retain the local-readout, same-source-cut and
complete-record hypotheses of the cited consumer. They do not
replace a missing realization of those hypotheses. Moment-level
conditions can suffice for the four CHSH correlators, as the cited
Corollary 3.4 states; failing the stronger full-channel certificate
does not refute those weaker sufficient conditions.

For a prior classical history h, Proposition 43.1 can be applied
conditionally. If all positive histories have the same setting law
p, retaining h gives the joint product
p tensor sum_h w_h |h><h| tensor sigma_h, even when the source
depends on h. With different p^h, independence conditional on h
does not itself imply independence from the complete source
including h, nor after forgetting h. This reuses the history
boundary of the common-source paper, Proposition 6.3.

## 49. What remains to acquire in the native theory

The precise sufficient interface added here is a fixed, full-output
instrument whose branches satisfy (43.1), or a certified approximate
version (47.2), on the whole declared returned source. Scalar
setting effects, input-independent probabilities and logical
source correction are each insufficient replacements, as the
examples show. A conditional correction construction and finite
verification interface are explicit.

For one actual AURIC native menu, the following remain to be supplied:
legal preparation and setting-generation histories from its declared
root and ready resources; coverage of every returning controller and
reference at the result cut; fixed local result readouts; positive
four-setting support; and either the actual-source joint equality or
a justified channel certificate. A universal certificate is sufficient
but not necessary for the state-specific native acquisition bridge.

No native program, ready-state acquisition, full-memory tomography,
correction permission or physical independence calibration is obtained
from the abstract CP description. These are the still-open realization
obligations in Definition 6.4 of the source paper. This analysis neither
closes that bridge nor gives an obstruction to every legal program.
Global purity, a common numerical spectrum and separate setting
marginals do not supply the missing branch-poststate relation.

### 49.1. Source correspondence

The pinned source is
`docs/develop/theory/AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md`
at commit `93e104ec4047c81aa471a5b65140c754e231c2c6`.
Its Hypothesis 1.2 and Definition 2.2 fix the returned-memory cut and defect;
Theorems 2.3 and 3.2 and Corollary 3.4 supply the reused
common-source consumers; Definition 6.4 states the native
acquisition bridge.

The elementary product-image argument, instrument/POVM distinction,
Choi identity, spanning probes and complete-norm estimates are used
as standard finite-dimensional mathematics. No claim is made that
the channel classification or the certificate is a new theorem in
the literature. These are conditional paper deductions, without Lean compilation
or physical verification.

## 追加锚（本行以下为增补区）
