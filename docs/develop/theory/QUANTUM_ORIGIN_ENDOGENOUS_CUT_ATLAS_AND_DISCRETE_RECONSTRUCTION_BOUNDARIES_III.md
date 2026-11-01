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
