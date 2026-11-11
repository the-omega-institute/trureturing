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


## 50. Original-interval anchoring outside a three-direction short core

**定义 50.1（Successive minima and fixed reduction constants）。** Retain exactly the single dimension-four original table, all labelled binary and ternary menus, zero and repeated effects, and its original tomography matrix $H$ from [Part I, Definition 16.1](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md). Write $R=\mathbb Z[i]$ and $e(X)=p(X)-\operatorname{Tr}(HX)$. Let $\mathcal S_4$ denote the integral matrices expressible as finite sums of $vv^*$ with $v\in R^4$, including the empty sum. For $B\succ0$ integral, define the squared complex successive minima

$$
\mu_j(B)=\min\left\{t:\text{there are }j\text{ complex-linearly independent }v_a\in R^4
\text{ with }v_a^*Bv_a\le t\right\},\qquad 1\le j\le4.
\tag{50.1}
$$

Fix an integer $\tau\ge5$ at least the threshold $G_{\mathbb Q(i)}(4)$ in Beli--Chan--Icaza--Liu, [*On a Waring's problem for integral quadratic and hermitian forms*, Proposition 5.3](https://arxiv.org/html/1702.08854v1). Thus $\mu_1(F)\ge\tau$ implies $F\in\mathcal S_4$ for every positive-definite integral $F$. Their Proposition 2.3, Lemma 3.3 and equations (3.1)--(3.2), in the fixed field and rank, also give constants $\alpha,c\ge1$ such that every $B$ has a basis $V\in\operatorname{GL}_4(R)$ with

$$
 V^*BV=X^*\operatorname{diag}(h_1,h_2,h_3,h_4)X,
 \quad h_1=\mu_1(B),\quad
 h_i\le\alpha h_j\ (i<j),
 \quad |X_{ij}|,|(X^{-1})_{ij}|\le c.
\tag{50.2}
$$

Here $X$ is upper triangular unipotent and $h_i>0$. Only this established fixed-rank reduction and the established large-minimum representation theorem are used from that paper. Set

$$
\begin{aligned}
 L&=64\alpha c^2\tau,& K&=2c^2L,& M&=3c^2L,\\
 N_c&=4\tau^2L^2+1,&
 A_*&=1+\max\{44,(\tau+K)^2,2K(\tau+2K),N_c^2\},\\
 S&=902826,& C_*&=2S+2=1805654.
\end{aligned}
\tag{50.3}
$$

All these constants are fixed independently of $N,p,\epsilon$ and the target. No numerical value of the reduction constants is needed.

**定理 50.2（A third-minimum anchor and a necessary three-dimensional obstruction）。** Let $N=2^m\ge2048$. Let $G\in\operatorname{Herm}_4(R)$ be a positive-definite integral interval atom, with

$$
 0\prec G\prec NI_4,\qquad d=\det G\le11,
 \qquad \lambda_{\max}(G)\le N-A_*/N,
 \qquad B=NI_4-G.
$$

For every original table in Definition 50.1,

$$
 \mu_3(B)>M
 \quad\Longrightarrow\quad
 |e(G/N)|\le C_*\epsilon.
\tag{50.4}
$$

More generally, if $|e(G/N)|>C_*\epsilon$, there is a unimodular basis $V=(v_1,v_2,v_3,v_4)$ such that the saturated submodule $\Lambda=Rv_1+Rv_2+Rv_3$ and the integral vector $q=V^{-*}e_4$ satisfy

$$
\begin{gathered}
 v_j^*Bv_j\le M\quad(1\le j\le3),\qquad
 0\ne\tau qq^*\succeq0,\qquad \tau qq^*\preceq B/4,\\
 \text{there is }0\ne z\in\Lambda\text{ with }2\le z^*Gz<\tau,\\
 \mu_4(B)\ge(N+d)^{1/4}.
\end{gathered}
\tag{50.5}
$$

Every matrix $\tau qq^*/N$ and $(G+\tau qq^*)/N$ occurring here is an effect on the original grid. Conditions (50.5) are necessary for failure of this absolute anchor, not a converse or a full-event counterexample.

**证明。** The trace grouping in the proof of [Part I, Theorem 57.4](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md), applied to a supplied Gram decomposition rather than to an arbitrary extraction order, gives

$$
 F\in\mathcal S_4,\quad 0\preceq F\prec NI_4
 \quad\Longrightarrow\quad |e(F/N)|\le S\epsilon.
\tag{50.6}
$$

Indeed each Gram summand is a strict rank-one effect; Part I, Lemma 57.2 applies to it. There are at most eleven summands of trace greater than $1/3$ and at most twelve remaining trace groups of norm below $2/3$. The same legal additions and the zero bound $p(0)\le2\epsilon$ give $902824\epsilon+2\epsilon$. This is a reuse of those estimates, not an assertion that an arbitrary extraction residual vanishes whenever a Gram representation exists.

Consequently it suffices to construct an integral $W\in\mathcal S_4$ with

$$
 0\preceq W\preceq B/4,\qquad G+W\in\mathcal S_4.
\tag{50.7}
$$

Both $W$ and $G+W$ are strictly below $NI_4$. Comparing the actual menus $(G/N,W/N,I_4-(G+W)/N)$ and $((G+W)/N,I_4-(G+W)/N)$ gives

$$
 |e(G/N)+e(W/N)-e((G+W)/N)|\le2\epsilon.
\tag{50.8}
$$

Together with (50.6), this proves the bound $C_*\epsilon$. If instead $B\in\mathcal S_4$, (50.6) and the original complementary binary menu give the stronger bound $(S+10)\epsilon$. The $10\epsilon$ is the binary defect plus the original $|\operatorname{Tr}H-1|\le9\epsilon$.

Choose (50.2) for $B$. If $h_1\ge\tau$, Proposition 5.3 supplies $B\in\mathcal S_4$. Hence assume $h_1<\tau$. First suppose either $h_2>L$, or $h_2\le L<h_3$. Put $k=1$ in the former case and $k=2$ in the latter, and write $V_k=(v_1,\ldots,v_k)$. Then

$$
 v_j^*Bv_j\le K\quad(j\le k),\qquad
 h_j>L/\alpha\quad(j>k).
\tag{50.9}
$$

The first assertion follows by expanding the corresponding diagonal entries of (50.2), and the second from $h_{k+1}>L$ and $h_{k+1}\le\alpha h_j$.

For $i>k$, let $q_i=V^{-*}e_i\in R^4$. Upper triangularity of $X^{-1}$ gives

$$
 q_i^*B^{-1}q_i
 =\sum_{j\ge i}\frac{|(X^{-1})_{ij}|^2}{h_j}
 <\frac{4\alpha c^2}{L}.
\tag{50.10}
$$

Cauchy--Schwarz gives $q_iq_i^*\preceq(q_i^*B^{-1}q_i)B$. Therefore

$$
 W=\tau\sum_{i>k}q_iq_i^*\in\mathcal S_4,
 \qquad W\preceq\frac{3}{16}B\preceq B/4.
\tag{50.11}
$$

No values of $p$ in the reduced coordinates have been introduced: the $q_i$ and $W$ in (50.10)--(50.11) are integral vectors and matrices in the original coordinates.

We next prove $\mu_1(G+W)\ge\tau$. If $z\in R^4$ lies outside $V_k\mathbb C^k$, some coordinate $(V^{-1}z)_i=q_i^*z$, $i>k$, is a nonzero Gaussian integer. Thus $z^*Wz\ge\tau$. If $z\in V_k\mathbb C^k$, unimodularity gives $z=V_ku$ with $u\in R^k$. Put

$$
 P=V_k^*V_k,\qquad B_k=V_k^*BV_k,
 \qquad V_k^*GV_k=NP-B_k.
\tag{50.12}
$$

The entries of $P$ are Gaussian integral, so $\det P$ is a positive integer. Also $B\succeq(A_*/N)I_4$ and (50.9) imply

$$
 \operatorname{Tr}P\le\frac{kKN}{A_*},\qquad
 \|B_k\|_{\rm op}\le kK.
\tag{50.13}
$$

For $k=1$, $P\ge1$ and hence $NP-B_k\succeq(N-K)I_k\succ\tau I_k$. Here $B\prec NI_4$ and $B\succeq(A_*/N)I_4$ force $N^2>A_*>(\tau+K)^2$. For $k=2$, positivity and integrality of $\det P$ give

$$
 \lambda_{\min}(P)\ge\frac{1}{\operatorname{Tr}P}
 \ge\frac{A_*}{2KN},\qquad
 NP-B_k\succeq\left(\frac{A_*}{2K}-2K\right)I_k
 \succ\tau I_k.
\tag{50.14}
$$

Thus every nonzero integral $z$ in this submodule has $z^*Gz>\tau$. In both cases $\mu_1(G+W)\ge\tau$, so Proposition 5.3 supplies the second membership in (50.7). This proves the anchor whenever $h_2>L$ or $h_3>L$. If neither holds, the first three basis vectors have $B$-norm at most $3c^2L=M$. Hence $\mu_3(B)>M$ forces one of the already anchored cases, proving (50.4).

It remains to prove the additional necessary structure. Suppose the anchor bound fails. The preceding argument leaves

$$
 h_1<\tau,\qquad h_2\le L,\qquad h_3\le L.
\tag{50.15}
$$

The small determinant, exact complement relation and the margin $A_*>44$ now have a separate role. [Part II, Theorem 164.2](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_II.md) gives

$$
 D=\det B\ge N+d.
\tag{50.16}
$$

Since $D=h_1h_2h_3h_4$, (50.15) yields $h_4>N/(\tau L^2)$. Put $q=V^{-*}e_4$. The last row of $X^{-1}$ is $e_4^*$, so

$$
 q^*B^{-1}q=h_4^{-1},\qquad
 \tau qq^*\preceq\frac{\tau}{h_4}B
 \prec\frac{\tau^2L^2}{N}B\preceq B/4.
\tag{50.17}
$$

The last inequality follows from $N>\sqrt{A_*}>N_c$. The first three columns of $V$ span a saturated rank-three submodule $\Lambda$. If every nonzero $z\in\Lambda$ had $z^*Gz\ge\tau$, the matrix $G+\tau qq^*$ would have arithmetic minimum at least $\tau$: outside $\Lambda$, $|q^*z|^2\ge1$. Equation (50.17), Proposition 5.3 and (50.8) would then prove the anchor, a contradiction. Thus some nonzero $z\in\Lambda$ has $z^*Gz<\tau$.

Atomicity supplies the lower bound in (50.5). If $z^*Gz=1$, Cauchy--Schwarz gives the nonzero integral rank-one matrix $(Gz)(Gz)^*\preceq G$. A positive-definite rank-four interval atom cannot equal this matrix and cannot contain it properly. Since integral Hermitian values are positive integers, $z^*Gz\ge2$ for every nonzero integral $z$.

Finally, for four independent integral vectors $u_j$ with $u_j^*Bu_j\le t$, their column matrix $U$ satisfies

$$
 D\le|\det U|^2D=\det(U^*BU)\le t^4.
$$

The first inequality uses the nonzero Gaussian integer $\det U$, and the last is Hadamard's inequality. Taking $t=\mu_4(B)$ and using (50.16) proves the final assertion of (50.5). All additions in (50.8), (50.11) and (50.17) lie in the original interval. $\square$

**命题 50.3（The anchored bounded-minimum branch contains qualifying atoms at arbitrarily large dyadic scales）。** For every dyadic $N\ge8$ there is a positive-definite integral interval atom $G_N$ of determinant one such that, with $B_N=NI_4-G_N$, there is a fixed $\eta>0$ independent of $N$ satisfying

$$
 B_N\succeq\eta\operatorname{diag}(1,N,N,N),\qquad
 \mu_1(B_N)\le4,\qquad \mu_2(B_N)\ge\eta N.
\tag{50.18}
$$

In particular, for each fixed finite $A>44$, all sufficiently large members satisfy $0\prec G_N\prec NI_4$ and $\lambda_{\max}(G_N)\le N-A/N$. For $A=A_*$ they eventually satisfy (50.4), while their first arithmetic minimum remains below $\tau$.

**证明。** Reuse the even unimodular atom from Part I, Theorem 32.1 at $N=4$:

$$
 F=\begin{pmatrix}
 2&0&\pi&1\\
 0&2&-1&\overline\pi\\
 \overline\pi&-1&2&0\\
 1&\pi&0&2
 \end{pmatrix},\qquad \pi=1+i.
\tag{50.19}
$$

Its positivity, determinant one and full integral interval atomicity are supplied there. Lagrange's four-square theorem gives a representation of $2N-9$. This integer is $7$ modulo $8$. In every four-square representation of such an integer exactly three entries are odd and the remaining entry is even. Permute them to write

$$
 2N-9=a^2+b^2+c_0^2+d_0^2,
 \qquad a,b,c_0\text{ odd},\quad d_0\text{ even}.
$$

Set $x=(a-1)/2+i(b+1)/2$, $y=(c_0-1)/2+id_0/2$, and

$$
 U=I_4+xe_3e_1^*+ye_4e_1^*,\qquad G_N=U^*FU.
\tag{50.20}
$$

The matrix $U$ is Gaussian unimodular. Hence $G_N$ is still positive definite, determinant one and an integral interval atom; this is an order congruence of integral forms, not a covariance assertion about the table. The four-square identity gives

$$
 2+2(|x|^2+|y|^2)+2\operatorname{Re}(\pi x+y)=N-4.
$$

Therefore, for a column $b_N$,

$$
 G_N=\begin{pmatrix}N-4&b_N^*\\b_N&C\end{pmatrix},
 \quad
 C=\begin{pmatrix}2&-1&\overline\pi\\-1&2&0\\\pi&0&2\end{pmatrix},
 \quad \|C\|_{\rm op}=2+\sqrt3=:c_0'<4.
\tag{50.21}
$$

The Schur complement of the first entry gives $b_Nb_N^*\preceq(N-4)C$. In the coordinates scaled by $\operatorname{diag}(1,\sqrt N I_3)$, the complementary form is

$$
 \begin{pmatrix}4&-b_N^*/\sqrt N\\-b_N/\sqrt N&I_3-C/N\end{pmatrix}.
$$

Its Schur complement after the first entry is at least

$$
 I_3-C/N-\frac{b_Nb_N^*}{4N}
 \succeq I_3-C/4\succeq\beta I_3,
 \qquad \beta=1-c_0'/4>0.
$$

Moreover $\|b_N\|/(4\sqrt N)\le\sqrt{c_0'}/4<1/2$. For a scalar $u$ and column $v$, put $a_0=u-b_N^*v/(4\sqrt N)$. Then

$$
 |u|^2+\|v\|^2\le2(|a_0|^2+\|v\|^2),\qquad
 4|a_0|^2+\beta\|v\|^2\ge\frac{\beta}{2}(|u|^2+\|v\|^2).
$$

Thus (50.18) holds with $\eta=\beta/2$. Also $e_1^*B_Ne_1=4$. Every two independent integral vectors include one with a nonzero last-three-coordinate column, whose $B_N$-norm is at least $\eta N$. This proves the two successive-minimum assertions. Finally $\lambda_{\min}(B_N)\ge\eta$ implies the displayed margin whenever $N\ge A/\eta$, and $\mu_3(B_N)\ge\mu_2(B_N)\to\infty$. This family verifies that the anchored branch includes actual original qualifying atoms with bounded first minimum. $\square$

## 51. The remaining three-direction inference and its parent consumer

**定义 51.1（Unresolved core obligation）。** Retain the full original atom quantifiers and the same table and tomography, without imposing (50.5) as a new premise on that event. Theorem 50.2 supplies a uniform original-interval absolute anchor for the whole branch $\mu_3(B)>M$, including bounded first minima. For the remaining branch, it supplies a saturated rank-three short $B$ submodule, a legal rank-one capacity in its annihilator, and an integral vector in that submodule with $G$-norm in $[2,\tau)$ whenever its displayed error bound fails. It does not assert that these simultaneous conditions are impossible or that the capacity necessarily raises this short $G$ value.

The missing inference is an absolute original-table anchor on this three-direction core, or a different argument covering it. Neither the existence of $q$ in (50.17) nor the bounded list of possible scalar values $z^*Gz$ proves that inference. No parity lift $R\preceq B$, $R\equiv B\pmod2$ has been assumed or proved for the core.

The parent consumer is the unchanged positive-definite determinant-at-most-eleven atom estimate in Part I, (57.15), with the complement-first lower-side transfer in Part II, (164.11). The proved branch can be used directly inside that consumer. The full existence of constants $A>44$ and $C_{\rm atom}$ for every original qualifying atom, and its faithful negation, remain unproved here; (50.4) is not substituted for the full event.

The established balanced HKZ and large-minimum results of Beli--Chan--Icaza--Liu, the original rank-one and trace-group estimates of Part I, and the determinant quantization of Part II are credited intermediate tools. The dual-coordinate thickening, the integral one- and two-dimensional compression bounds, their three-direction obstruction consequence and the qualifying bounded-minimum realization above are repo-derived ordinary mathematical deductions. No global literature priority claim is made.

## 追加锚（本行以下为增补区）
## 52. A second dual direction reduces the ternary determinant obstruction

**定义 52.1（Fixed kernel-basis constants）。** Retain $R$, $e$, $\mathcal S_4$, $\tau$, $\alpha$, $c$, $L$, $M$, $A_*$ and $C_*$ from Definition 50.1, with the same original table and tomography. Put

$$
 r_0=\max\left\{1,\left\lceil\frac{3M}{2\tau}\right\rceil\right\},
 \qquad
 \mathcal A=\{a\in R^3:a\text{ is primitive},\ 1\le\|a\|^2\le r_0\}.
\tag{52.1}
$$

This is a nonempty finite set. For each $a\in\mathcal A$, choose a Gaussian unimodular matrix $T_a$ satisfying $a^*T_a=e_3^*$. Successive elementary Gaussian column operations reduce the primitive row $a^*$ to a unit coordinate row; multiplication by a unit and a column permutation give the stated $T_a$. All these operations are unimodular. Write $u_{a,1},u_{a,2}$ for its first two columns, so they form an $R$-basis of $\ker(a^*:R^3\to R)$. Define the finite constants

$$
\begin{aligned}
 J_0&=\max\bigl(\{1\}\cup
       \{\|u_{a,j}\|^2:a\in\mathcal A,\ 1\le j\le2\}\bigr),\\
 K_0&=3MJ_0,\\
 A_\dagger&=1+\max\{A_*,\ (6\tau^2L^2+1)^2,
                         \ 2K_0(\tau+2K_0)\}.
\end{aligned}
\tag{52.2}
$$

These choices concern only a bounded set of three-coordinate integer vectors, not a restriction of the original targets or menus. They are independent of $N,\epsilon,p$ and $G$.

**定理 52.2（An absolute anchor from the compressed ternary determinant）。** Let $N=2^m\ge2048$ and let $G\in\operatorname{Herm}_4(R)$ be a positive-definite integral interval atom satisfying

$$
 d=\det G\le11,\qquad
 0\prec G\prec NI_4,\qquad
 \lambda_{\max}(G)\le N-A_\dagger/N.
\tag{52.3}
$$

Put $B=NI_4-G$. Choose a balanced basis $V=(v_1,v_2,v_3,v_4)$ as in (50.2), with heights $h_j$, and write

$$
 V_3=(v_1,v_2,v_3),\qquad
 C=V_3^*BV_3,\qquad
 \Delta=\det C=h_1h_2h_3,\qquad
 \nu(C)=\min_{0\ne a\in R^3}a^*C^{-1}a.
\tag{52.4}
$$

For every original table of Definition 50.1, the additional branch

$$
 h_1<\tau,\qquad h_2,h_3\le L,\qquad
 \nu(C)\le\frac1{2\tau}
 \quad\Longrightarrow\quad
 |e(G/N)|\le C_*\epsilon
\tag{52.5}
$$

has an absolute anchor. In particular $\Delta\ge64\tau^3$ is sufficient for this branch. In this branch there are explicitly constructed independent vectors $q,w\in R^4$ such that

$$
 W=\tau(qq^*+ww^*)\in\mathcal S_4,\qquad
 W\preceq\tfrac34B,\qquad
 \mu_1(G+W)\ge\tau,\qquad G+W\in\mathcal S_4.
\tag{52.6}
$$

Consequently, if the bound $|e(G/N)|\le C_*\epsilon$ fails, its basis from Theorem 50.2 can be chosen with all the properties there and, in addition,

$$
 \begin{gathered}
 \nu(C)>\frac1{2\tau},\qquad
 1\le\Delta<64\tau^3,\qquad
 \det B=d+kN,\quad k\in\mathbb Z_{\ge1},\\
 q=V^{-*}e_4,\qquad
 k\|q\|^2<\Delta<64\tau^3.
 \end{gathered}
\tag{52.7}
$$

In particular the original-coordinate normal $q$, up to multiplication by a Gaussian unit, and the positive integer $k$ range over finite sets independent of the scale. The restriction $C$ and the short $G$ vectors within its saturated submodule are not thereby fixed.

**证明。** In the branch of (52.5), expansion of (50.2) gives

$$
 C_{jj}\le M\quad(1\le j\le3),\qquad
 \|C\|_{\rm op}\le3M,\qquad
 \Delta<\tau L^2.
\tag{52.8}
$$

Write the full reduced matrix in blocks as

$$
 V^*BV=\begin{pmatrix}C&b\\b^*&\beta\end{pmatrix},
 \qquad h_4=\beta-b^*C^{-1}b.
\tag{52.9}
$$

The determinant quantization in Part II, Theorem 164.2 applies because $A_\dagger>44$. Therefore

$$
 \Delta h_4=\det B\ge N+d,\qquad
 h_4>\frac{N}{\tau L^2}>6\tau.
\tag{52.10}
$$

For the last inequality, (52.3) and $G\succ0$ force $N^2>A_\dagger$, while (52.2) forces $\sqrt{A_\dagger}>6\tau^2L^2+1$.

The dual minimum in (52.4) is attained because $C^{-1}$ is positive definite and $R^3$ is discrete. Under the hypothesis of (52.5), choose a nonzero $a\in R^3$ with $\rho:=a^*C^{-1}a\le1/(2\tau)$. For the determinant sufficient condition, use the ordinary real six-dimensional Hermite bound on this dual lattice, exactly with the normalization in Part I, (57.2):

$$
 \nu(C)\le\gamma_6\Delta^{-1/3}
 <2\Delta^{-1/3}\le\frac1{2\tau}
 \qquad(\Delta\ge64\tau^3).
\tag{52.11}
$$

Here $\gamma_6=2/3^{1/6}<2$ is an ordinary-lattice bound: Vance, [*A Mordell Inequality for Lattices over Maximal Orders*, §4.2, Table 3 and the paragraph preceding it](https://arxiv.org/html/0810.2336v5#S4.T3), records both this value and ordinary-lattice optimality in dimension six. No Eisenstein-module hypothesis is imposed on $C$. Dividing $a$ by the Gaussian gcd of its coordinates if necessary makes it primitive and cannot increase $\rho$. Moreover

$$
 \|a\|^2\le\|C\|_{\rm op}\rho
 \le\frac{3M}{2\tau}\le r_0,
\tag{52.12}
$$

so this $a$ belongs to the finite set in Definition 52.1.

Choose a nearest Gaussian integer $s$ to $b^*C^{-1}a$; independent rounding of its real and imaginary parts gives

$$
 |s-b^*C^{-1}a|^2\le\tfrac12.
$$

Construct the original-coordinate vectors

$$
 q=V^{-*}e_4,\qquad
 w=V^{-*}\binom a s.
\tag{52.13}
$$

They are integral and independent, since $V$ is Gaussian unimodular and $a\ne0$. The block inverse formula in (52.9) gives the actual dual costs

$$
 q^*B^{-1}q=\frac1{h_4},\qquad
 w^*B^{-1}w
 =\rho+\frac{|s-b^*C^{-1}a|^2}{h_4}
 \le\rho+\frac1{2h_4}.
\tag{52.14}
$$

For each vector $x$, Cauchy--Schwarz gives $xx^*\preceq(x^*B^{-1}x)B$. Using $\rho\le1/(2\tau)$ and (52.10) therefore proves

$$
 W=\tau(qq^*+ww^*)
 \preceq\tau\left(\rho+\frac3{2h_4}\right)B
 \prec\tfrac34B.
\tag{52.15}
$$

The use of $3B/4$ leaves a strictly positive complementary interval; no bound $W\preceq B/4$ is needed.

It remains to control the common kernel, rather than to assume that the new direction detects every short $G$ vector. For $z\in R^4$,

$$
 q^*z=w^*z=0
 \quad\Longleftrightarrow\quad
 z\in F R^2,\qquad
 F=V_3(u_{a,1},u_{a,2}).
\tag{52.16}
$$

Indeed $V^{-1}z$ is integral, its fourth coordinate must vanish, and its first three coordinates then belong exactly to $\ker a^*$. This also proves saturation of the displayed rank-two submodule. Its two basis columns $f_j$ satisfy

$$
 f_j^*Bf_j=u_{a,j}^*Cu_{a,j}\le3MJ_0=K_0.
\tag{52.17}
$$

Set $P=F^*F$ and $D_2=F^*BF$. The Euclidean Gram matrix $P$ is positive definite and integral, so $\det P$ is a positive integer. Since $B\succeq(A_\dagger/N)I_4$,

$$
 \operatorname{Tr}P\le\frac{2K_0N}{A_\dagger},\qquad
 \|D_2\|_{\rm op}\le2K_0,\qquad
 \lambda_{\min}(P)\ge\frac1{\operatorname{Tr}P}
 \ge\frac{A_\dagger}{2K_0N}.
\tag{52.18}
$$

Using the exact original complement identity now gives

$$
 F^*GF=NP-D_2
 \succeq\left(\frac{A_\dagger}{2K_0}-2K_0\right)I_2
 \succ\tau I_2.
\tag{52.19}
$$

Thus every nonzero integral vector in the common kernel has $G$-value greater than $\tau$. Outside it, at least one of $q^*z,w^*z$ is a nonzero Gaussian integer, so $z^*Wz\ge\tau$. This proves $\mu_1(G+W)\ge\tau$ without a congruence transformation of any table value.

The large-minimum representation theorem of Beli--Chan--Icaza--Liu, [*On a Waring's problem for integral quadratic and hermitian forms*, Proposition 5.3](https://arxiv.org/html/1702.08854v1), applies to the positive-definite integral rank-four matrix $G+W$, by the fixed choice of $\tau$ in Definition 50.1. Hence $G+W\in\mathcal S_4$. Also $W\in\mathcal S_4$ directly, since $\tau$ is an integer. Equation (52.15) proves

$$
 0\preceq W\prec NI_4,\qquad
 0\prec G+W\preceq NI_4-B/4\prec NI_4.
\tag{52.20}
$$

Both Gram estimates (50.6) therefore concern the supplied original table. The same actual ternary and binary menus as in (50.8) give $|e(G/N)|\le(2S+2)\epsilon=C_*\epsilon$, proving (52.5)--(52.6).

For (52.7), suppose this error bound fails. Theorem 50.2 leaves $h_1<\tau$ and $h_2,h_3\le L$, and the argument just given forces $\nu(C)>1/(2\tau)$ and $\Delta<64\tau^3$. Part II, Theorem 164.2 gives $\det B=d+kN$ with integer $k\ge1$. Since $B\prec NI_4$, its inverse satisfies $B^{-1}\succ N^{-1}I_4$. Equations (52.9) and (52.14) consequently give

$$
 \frac{\|q\|^2}{N}<\frac1{h_4},\qquad
 kN+d=\Delta h_4<\frac{\Delta N}{\|q\|^2},
 \qquad k\|q\|^2<\Delta.
\tag{52.21}
$$

This proves the asserted finite ranges. The short-vector obstruction in (50.5) still applies because (52.3) implies its margin hypothesis.

The new capacity in (52.13)--(52.15) uses a ternary dual short vector and a rounded fourth coordinate; (52.16)--(52.19) prove the required rank-two compression for its actual common kernel. These constructions supply the additional branch of the original atom estimate (57.15) of Part I, with the original complementary-menu transfer (164.11) of Part II. The Hermite and large-minimum representation results are credited intermediate tools. No claim of global literature priority is made for this deduction. The cases remaining in (52.7), including their short $G$ vectors from (50.5), have not acquired an absolute error bound here. Neither existence nor nonexistence of uniform constants for the full original event follows from these necessary conditions. $\square$

## 追加锚（本行以下为增补区）

## 53. Transverse extraction closes the original upper-margin atom estimate

**定义 53.1（Uniform constants and the unchanged table）。** Retain the single original dimension-four table, all labelled binary and ternary menus including zeros and repetitions, the original tomography matrix $H$, and $e(E)=p(E)-\operatorname{Tr}(HE)$ from Definition 50.1. Retain $\tau$, $A_\dagger$ and $C_*$ from Definitions 50.1 and 52.1. Define the finite constants

$$
\begin{aligned}
 D_0&=64\tau^3,&
 T&=4\tau(D_0+1),&
 \lambda&=1+\frac1{4\tau},\\
 K_{\mathrm{tr}}&=53142+2+902824=955968,\\
 N_0&=1+\max\{2048,\ D_0+64,\ (4\tau+2)D_0,\ 2TD_0\},\\
 A_0&=2A_\dagger,&
 C_0&=\max\{C_*+TK_{\mathrm{tr}},\ 33N_0\}.
\end{aligned}
\tag{53.1}
$$

Here $D_0,T,N_0$ are positive integers. None of these constants depends on the scale, table, tolerance, target or reduced basis.

**引理 53.2（A transverse rank-one extraction with determinant growth）。** Let $N=2^m>N_0$. Let $G$ be a positive-definite Gaussian integral interval atom with $0\prec G\prec NI_4$ and $d=\det G\le11$. Put $B=NI_4-G$ and $D=\det B$. Let $V=(V_3,v_4)\in\operatorname{GL}_4(R)$, and set

$$
 C=V_3^*BV_3,\qquad
 \Delta=\det C,\qquad
 q=V^{-*}e_4,\qquad
 \nu(C)=\min_{0\ne a\in R^3}a^*C^{-1}a.
$$

Suppose

$$
 D\ge N,\qquad 1\le\Delta<D_0,\qquad
 \nu(C)>\frac1{2\tau}.
\tag{53.2}
$$

There is an integral matrix $G'$ that is either zero or a positive-definite interval atom with determinant at most $11$, such that, writing $B'=NI_4-G'$,

$$
\begin{aligned}
 0&\preceq G'\prec NI_4,\\
 B'&\succeq\left(1-\frac{D_0}{N}\right)B,\\
 \det B'&>\lambda D,\\
 |e(G'/N)-e(G/N)|&\le K_{\mathrm{tr}}\epsilon.
\end{aligned}
\tag{53.3}
$$

The convention at $G'=0$ is $e(0)=p(0)$. All table evaluations in this conclusion are on the original grid.

**证明。** Cofactors under a Gaussian unimodular change of basis give

$$
 q^*B^{-1}q=\frac{\Delta}{D}.
\tag{53.4}
$$

Indeed the bottom-right entry of $(V^*BV)^{-1}$ is $\Delta/D$, and $\det(V^*BV)=D$. Consequently, for $Q=qq^*$,

$$
 0\preceq Q\preceq\frac{\Delta}{D}B
 \prec\frac{D_0}{N}B\prec B.
\tag{53.5}
$$

Thus $F=G+Q\prec NI_4$, and both $Q/N$ and $F/N$ are original-grid effects.

A second cofactor identity, now for $G$, gives the positive integer

$$
 a_G:=q^*\operatorname{adj}(G)q
     =\det(V_3^*GV_3).
\tag{53.6}
$$

Entrywise reduction modulo $N$ gives $B\equiv-G$ and hence

$$
 \operatorname{adj}(B)\equiv-\operatorname{adj}(G)\pmod N,
 \qquad \Delta+a_G\in N\mathbb Z_{>0}.
\tag{53.7}
$$

The minus sign is because the cofactors have degree three. The scalar cofactor identity for $B$ is $q^*\operatorname{adj}(B)q=\Delta$. Both scalars in (53.7) are positive real integers, so

$$
 a_G\ge N-\Delta>N-D_0>64.
\tag{53.8}
$$

Write

$$
 V^*GV=\begin{pmatrix}C_G&b\\b^*&\beta\end{pmatrix},
 \qquad C_G=V_3^*GV_3.
$$

Since $V^*q=e_4$, the corresponding block matrix for $F$ has the same $C_G,b$ and bottom-right entry $\beta+1$. Its last Schur complement is

$$
 h_F=\beta+1-b^*C_G^{-1}b
     =1+\frac{d}{a_G}>1.
\tag{53.9}
$$

Apply the ordinary real six-dimensional Hermite bound, with the dual-lattice normalization of Part I, (57.2), to $C_G$. It supplies $0\ne\eta\in R^3$ such that

$$
 \rho_G:=\eta^*C_G^{-1}\eta
 \le\gamma_6a_G^{-1/3}
 <2a_G^{-1/3}<\frac12.
\tag{53.10}
$$

Here $\gamma_6=2/3^{1/6}<2$ is the ordinary-lattice constant recorded by Vance, [*A Mordell Inequality for Lattices over Maximal Orders*, §4.2, Table 3 and the paragraph preceding it](https://arxiv.org/html/0810.2336v5#S4.T3). As in (52.11), no Eisenstein-module hypothesis is used.

Choose a nearest Gaussian integer $s$ to $b^*C_G^{-1}\eta$, and define the original-coordinate vector

$$
 u=V^{-*}\binom{\eta}{s}\in R^4.
\tag{53.11}
$$

It is independent of $q$, because $\eta\ne0$. The block inverse formula and Gaussian rounding give

$$
 u^*F^{-1}u
 =\rho_G+\frac{|s-b^*C_G^{-1}\eta|^2}{h_F}
 \le\rho_G+\frac1{2h_F}<1.
\tag{53.12}
$$

Cauchy--Schwarz in the $F$ inner product therefore implies $uu^*\preceq cF$ for $c=u^*F^{-1}u<1$. In particular $F-uu^*\succ0$.

Apply Part I, Theorem 57.3 to $F-uu^*$, and prepend $uu^*$ to its Gram summands. This produces a decomposition

$$
 F=uu^*+\sum_j w_jw_j^*+G',
\tag{53.13}
$$

with $G'$ zero or an atom of the asserted kind. The trace grouping in the proof of Part I, Theorem 57.4 applies to this supplied decomposition: every summand and every partial sum is below $F\prec NI_4$. Hence

$$
 |e(F/N)-e(G'/N)|\le902824\epsilon.
\tag{53.14}
$$

The strict rank-one estimate of Part I, Lemma 57.2 gives $|e(Q/N)|\le53142\epsilon$. Comparing the original menus $(G/N,Q/N,I_4-F/N)$ and $(F/N,I_4-F/N)$ gives

$$
 |e(F/N)-e(G/N)-e(Q/N)|\le2\epsilon.
\tag{53.15}
$$

Equations (53.14)--(53.15) prove the error bound in (53.3). They do not accumulate an error for each individual extracted vector.

It remains to prove the determinant increase. Put $B_-=B-Q\succ0$. By (53.13),

$$
 B'=B_-+uu^*+\sum_jw_jw_j^*\succeq B_-+uu^*.
\tag{53.16}
$$

The matrix determinant lemma and (53.4) give $\det B_-=D-\Delta$. Moreover $B_-^{-1}\succeq B^{-1}$. In the block inverse formula for $V^*BV$, the first three coordinates of $V^*u$ are $\eta$, so

$$
 u^*B_-^{-1}u\ge u^*B^{-1}u
 \ge\eta^*C^{-1}\eta
 \ge\nu(C)>\frac1{2\tau}.
\tag{53.17}
$$

Monotonicity of the determinant on positive-definite matrices and another application of the determinant lemma now imply

$$
 \det B'
 \ge(D-\Delta)(1+u^*B_-^{-1}u)
 >(D-\Delta)\left(1+\frac1{2\tau}\right).
\tag{53.18}
$$

Since $\Delta/D<D_0/N<1/(4\tau+2)$,

$$
 \det B'>
 D\left(1-\frac1{4\tau+2}\right)
  \left(1+\frac1{2\tau}\right)
 =\left(1+\frac1{4\tau}\right)D.
\tag{53.19}
$$

Finally, (53.5) and (53.16) give $B'\succeq B_-\succeq(1-D_0/N)B$. This proves all of (53.3). Only integral vectors constructed in the original coordinates were added or removed; no transformed probability table or congruence covariance has been used. $\square$

**定理 53.3（Absolute original-table bound for the entire upper-margin atom class）。** Let $N=2^m\ge2048$ and let the single table satisfy Definition 50.1, with its original $H$ and $\epsilon\in[0,1/10]$. For every positive-definite Gaussian integral interval atom $G$ with

$$
 0\prec G\prec NI_4,\qquad
 \det G\le11,\qquad
 \lambda_{\max}(G/N)\le1-\frac{A_0}{N^2},
\tag{53.20}
$$

one has

$$
 \boxed{\ |p(G/N)-\operatorname{Tr}(HG/N)|
          \le C_0\left(\epsilon+\frac1N\right).\ }
\tag{53.21}
$$

For $N>N_0$, the stronger bound $(C_*+TK_{\mathrm{tr}})\epsilon$ holds. In particular (53.21) covers the entire residual class (52.7), for every residual basis satisfying its stated conditions. No short-$G$-vector condition is an additional premise.

**证明。** First suppose $N\le N_0$. Part I, Theorem 16.2 gives $\|H\|_{\mathrm{op}}\le8$. Since $0\preceq G/N\preceq I_4$ and $p(G/N)\in[0,1]$,

$$
 |e(G/N)|\le1+8\operatorname{Tr}(G/N)\le33
 \le\frac{33N_0}{N}\le\frac{C_0}{N}.
\tag{53.22}
$$

This accounts for every allowed coarse scale.

Now let $N>N_0$, and suppose for contradiction that $G_0=G$ satisfies

$$
 |e(G_0/N)|>(C_*+TK_{\mathrm{tr}})\epsilon.
\tag{53.23}
$$

We construct $G_0,\ldots,G_T$ using Lemma 53.2. Put $B_k=NI_4-G_k$ and $\mathcal D_k=\det B_k$. At each stage the error transfer gives

$$
 |e(G_k/N)|>
   \bigl(C_*+(T-k)K_{\mathrm{tr}}\bigr)\epsilon
 \ge C_*\epsilon.
\tag{53.24}
$$

In particular $G_k\ne0$: the menu hypotheses give $p(0)\le2\epsilon$, while $C_*>2$.

The margin needed to apply Theorems 50.2 and 52.2 persists throughout these $T$ steps. Indeed, the margin part of (53.3), Bernoulli's inequality, $N>2TD_0$, and (53.20) give, for $0\le k\le T$,

$$
\begin{aligned}
 B_k
 &\succeq\left(1-\frac{D_0}{N}\right)^k B_0\\
 &\succeq\left(1-\frac{kD_0}{N}\right)B_0
 \succeq\frac12B_0
 \succeq\frac{A_\dagger}{N}I_4.
\end{aligned}
\tag{53.25}
$$

This is an inductive estimate: the initial inequality holds at $k=0$, and Lemma 53.2 supplies its next step once the current stage has the stated margin and residual conditions.

At every current stage, (53.24)--(53.25) allow the failure implication (52.7) to be applied to $G_k$. It supplies a balanced basis, with its associated $C_k,\Delta_k,q_k$, such that

$$
 \nu(C_k)>\frac1{2\tau},\qquad
 1\le\Delta_k<D_0,\qquad
 \mathcal D_k=d_k+j_kN,\qquad
 j_k\ge1,\qquad
 j_k\|q_k\|^2<\Delta_k.
\tag{53.26}
$$

Here $d_k=\det G_k\le11$. Since $q_k$ is a nonzero integral vector, $\|q_k\|^2\ge1$. Thus each such stage satisfies

$$
 N\le \mathcal D_k<D_0N+11.
\tag{53.27}
$$

Equations (53.26)--(53.27) are exactly the input needed for Lemma 53.2. For $k<T$ it produces the next atom $G_{k+1}$ with (53.24), (53.25), and $\mathcal D_{k+1}>\lambda \mathcal D_k$. The zero alternative would contradict (53.24), so the construction reaches $G_T$. The same failure implication at $k=T$ gives the upper bound in (53.27).

On the other hand, the determinant growth and the integer choice of $T$ give

$$
 \mathcal D_T>\lambda^T\mathcal D_0
 \ge\lambda^TN
 \ge\left(1+\frac{T}{4\tau}\right)N
 =(D_0+2)N>D_0N+11,
\tag{53.28}
$$

The initial lower bound $\mathcal D_0\ge N$ follows from (53.27), and the last inequality uses $N\ge2048$. This contradicts (53.27). Consequently (53.23) is impossible, proving the asserted stronger fine-scale bound and, with (53.22), (53.21).

The construction uses only one supplied table at one scale. The constants in (53.1) are independent of every target and every basis; the residual bases may change at successive stages. Theorem 52.2 supplies necessary conditions only when its own bound fails, and those conditions are used here to continue the contradiction, not as a sufficient anchor or as a replacement event. In particular no extra hypothesis from the short-vector consequence (50.5) enters the proof.

The new deduction is the combination of the cofactor congruence (53.7), the transverse extraction (53.10)--(53.12), and the strict determinant increase (53.18)--(53.28). The original rank-one and trace-group estimates of Part I and the failure implication of Theorem 52.2 are reused with their stated hypotheses. The ordinary Hermite bound is credited above; the balanced reduction and large-minimum representation theorem of Beli--Chan--Icaza--Liu, [*On a Waring's problem for integral quadratic and hermitian forms*, Proposition 5.3](https://arxiv.org/html/1702.08854v1), enter through Theorems 50.2 and 52.2. This is a repo-derived ordinary mathematical conclusion, with no global literature-priority assertion. It establishes the upper-margin atom estimate with $A=A_0\ge A_\dagger$, including the entire residual class, and does not assert an unrestricted estimate for the complementary boundary band. $\square$

## 追加锚（本行以下为增补区）

## 54. Original-grid face relations and tomography coordinates

**定义 54.1（One grid, its free symbols and its legal rows）。** Fix $m\ge1$, $N=2^m$, and $R=\mathbb Z[i]$. In $\mathbb C^4$ let

$$
 K_{4,N}=\{E\in\operatorname{Herm}_4(N^{-1}R):0\le E\le I_4\},
 \qquad W_{4,N}=\bigoplus_{E\in K_{4,N}}\mathbb R\delta_E.
\tag{54.1}
$$

A legal row is

$$
 r(A,B,X)=\delta_{A+X}+\delta_B-\delta_A-\delta_{B+X}
\tag{54.2}
$$

when $X\in\operatorname{Herm}_4(N^{-1}R)$ and all five matrices $A,B,A+X,B+X,C=I_4-A-B-X$ belong to $K_{4,N}$. The increment $X$ may have either sign. Write $\mathcal R_{4,N}$ for this finite set of rows. Let $\mathcal B_4$ be precisely the basis of [Part I, Definition 16.1](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md):

$$
 D_i=e_ie_i^*,\qquad
 R_{ij}=(D_i+D_j+S_{ij})/2,\qquad
 J_{ij}=(D_i+D_j+T_{ij})/2,
\tag{54.3}
$$

where $S_{ij}$ has entries $1,1$ in positions $(i,j),(j,i)$ and $T_{ij}$ has entries $i,-i$ there. The actual anchor set is

$$
 \mathcal A_N=\mathcal B_4\ \cup\
 \{F\in K_{4,N}:\|F\|_{\rm op}\le1/52\}.
\tag{54.4}
$$

All equalities of symbols below are in the free real vector space (54.1). In particular, matrix addition is not imposed as a relation between symbols.

**定义 54.2（A coordinate face and its own identity）。** For a three-element subset $J\subset\{1,2,3,4\}$ put $S=\sum_{j\in J}D_j$ and

$$
 K_{S,N}=\{E\in\operatorname{Herm}_4(N^{-1}R):E=SES,\ 0\le E\le S\},
 \qquad W_{S,N}=\bigoplus_{E\in K_{S,N}}\mathbb R\delta_E.
\tag{54.5}
$$

The space $S\mathbb C^4$ is identified with $\mathbb C^3$ by its ordered coordinate basis; its identity is $S$, with $\operatorname{Tr}S=3$. Define $\mathcal R_{S,N}$ by (54.2), with every matrix supported on $S$ and complement $C_3=S-A-B-X$ required to lie in $K_{S,N}$. Let

$$
 \mathcal B_S=\{D_j:j\in J\}\cup\{R_{jk},J_{jk}:j<k,\ j,k\in J\}.
\tag{54.6}
$$

Thus $\mathcal B_S\subset\mathcal B_4$ consists of nine original-grid rank-one projections, all of trace one. The sets $K_{S,N}$ and $\mathcal R_{S,N}$ are finite: an effect has bounded entries on a discrete grid, and a row is determined by its finitely many endpoints.

**定义 54.3（The original real coefficients）。** For $E\in K_{S,N}$ write $E_{jk}=x_{jk}+iy_{jk}$ for $j<k$ in $J$. The coefficients $\alpha_Q(E)$ are exactly those of Part I, (16.6):

$$
 \begin{aligned}
 E&=\sum_{j\in J}a_jD_j+
       \sum_{\substack{j<k\\j,k\in J}}(2x_{jk}R_{jk}+2y_{jk}J_{jk})
       =\sum_{Q\in\mathcal B_S}\alpha_Q(E)Q,\\
 a_j&=E_{jj}-\sum_{\substack{k<j\\k\in J}}(x_{kj}+y_{kj})
                  -\sum_{\substack{k>j\\k\in J}}(x_{jk}+y_{jk}).
 \end{aligned}
\tag{54.7}
$$

Taking traces and using the first coefficient inequality of Part I, (16.7), with $d=3$, gives

$$
 \sum_Q\alpha_Q(E)=\operatorname{Tr}E,\qquad
 \sum_Q|\alpha_Q(E)|\le27\|E\|_{\rm op}\le27,\qquad
 |1-\operatorname{Tr}E|\le2.
\tag{54.8}
$$

The coefficient inequality is valid for every effect; its use here does not require the local-ball condition $27\|E\|\le1$ used later in Part I's local proof.

## 55. Perturbing an arbitrary functional and obtaining exact finite coefficients

**定理 55.1（Fine-scale finite-dual face supplier）。** Suppose $N=2^m\ge1024$. For every coordinate face $S$ of Definition 54.2 and every $E\in K_{S,N}$ there are a finite list $r_1,\ldots,r_k\in\mathcal R_{S,N}$ and real coefficients $\lambda_1,\ldots,\lambda_k$ such that

$$
 \begin{aligned}
 \delta_E&=R_E+\sum_{Q\in\mathcal B_S}\alpha_Q(E)\delta_Q
                 +(1-\operatorname{Tr}E)\delta_0,\\
 R_E&=\sum_{j=1}^k\lambda_jr_j,\qquad
 \sum_{j=1}^k|\lambda_j|\le664016.
 \end{aligned}
\tag{55.1}
$$

The coefficients $\alpha_Q(E)$ are fixed by (54.7); the row coefficients need not be unique. Counting rows, tomography symbols and the zero symbol together gives total absolute coefficient sum at most $664045$.

Proof. Let $f:K_{S,N}\to\mathbb R$ be arbitrary, and use the same letter for its linear extension to $W_{S,N}$. Set

$$
 \rho=\max_{r\in\mathcal R_{S,N}}|f(r)|,\qquad
 g(E)=f(E)-f(0),\qquad
 h(E)=g(E)-\frac{\operatorname{Tr}E}{3}g(S).
\tag{55.2}
$$

For $A,B\ge0$ on the original grid with $A+B\le S$, the row $r(0,B,A)$ has endpoints $0,B,A,A+B$ and complement $S-A-B$. Thus it is legal, and

$$
 |g(A)+g(B)-g(A+B)|\le\rho.
\tag{55.3}
$$

The trace correction is additive. Consequently (55.3) holds with $h$ in place of $g$, and $h(0)=h(S)=0$. For every labelled two-entry menu $E_1+E_2=S$ it follows that

$$
 |h(E_1)+h(E_2)|\le\rho.
\tag{55.4}
$$

For every labelled three-entry menu $E_1+E_2+E_3=S$, the partial sum $E_1+E_2$ is an original-grid effect. Two applications of (55.3) give

$$
 |h(E_1)+h(E_2)+h(E_3)|\le2\rho.
\tag{55.5}
$$

These arguments include every zero entry and every repetition.

There are positive finite endpoint margins. Indeed, positivity implies $\operatorname{Tr}E=0$ only at $E=0$, and positivity of $S-E$ implies $\operatorname{Tr}E=3$ only at $E=S$. Hence, writing $q(E)=\operatorname{Tr}E/3$,

$$
 \eta=\min_{E\in K_{S,N}\setminus\{0,S\}}
                  \min\{q(E),1-q(E)\}>0,
 \qquad M=\max_{E\in K_{S,N}}|h(E)|<\infty.
\tag{55.6}
$$

The set defining $\eta$ is nonempty, since it contains the coordinate rank-one projections. Choose, for example,

$$
 0<t\le\min\left\{\frac{\eta}{2(1+M)},\frac1{20(1+\rho)}\right\},
 \qquad p_t(E)=q(E)+t h(E),\qquad \epsilon=2t\rho.
\tag{55.7}
$$

At $0,S$ the values are exactly $0,1$. At every other effect, $|t h(E)|\le\eta/2$, so $0\le p_t(E)\le1$. Equations (55.4)--(55.5), together with $\sum_jq(E_j)=1$, verify every two- and three-entry menu condition with defect at most $\epsilon\le1/10$. If $\rho=0$, this choice has $\epsilon=0$. No bound on $f$, and no endpoint margin uniform in $N$, is required.

Apply the fine clause of Part I, Theorem 33.1, namely its bound (33.20), to this complete table on its own three-dimensional identity $S$. Its threshold $N\ge648$ holds here. For any real table $u$ on this face let $H_u$ be the unique Hermitian operator on $S\mathbb C^4$ with $\operatorname{Tr}(H_uQ)=u(Q)$ for every $Q\in\mathcal B_S$. This is a linear function of $u$, and $H_q=S/3$. Therefore

$$
 \begin{aligned}
 |p_t(E)-\operatorname{Tr}(H_{p_t}E)|
   &=t|h(E)-\operatorname{Tr}(H_hE)|\\
   &\le332008\epsilon=664016t\rho.
 \end{aligned}
\tag{55.8}
$$

Division by $t>0$ is legitimate also when $\rho=0$. By (54.7), $\operatorname{Tr}(H_hE)=\sum_Q\alpha_Q(E)h(Q)$. Since every $Q$ has trace one and $\sum_Q\alpha_Q(E)=\operatorname{Tr}E$, direct substitution from (55.2) cancels the trace correction and gives

$$
 \begin{aligned}
 h(E)-\sum_Q\alpha_Q(E)h(Q)
   &=f(E)-\sum_Q\alpha_Q(E)f(Q)
                         -(1-\operatorname{Tr}E)f(0),\\
 v_E&=\delta_E-\sum_Q\alpha_Q(E)\delta_Q
                         -(1-\operatorname{Tr}E)\delta_0,\\
 |f(v_E)|&\le664016\max_{r\in\mathcal R_{S,N}}|f(r)|.
 \end{aligned}
\tag{55.9}
$$

This inequality has been established for every real linear functional on the free space, without assuming positivity or normalization of that functional.

Now use the standard finite-dimensional separating-hyperplane theorem, as in R. T. Rockafellar, *Convex Analysis*, §11. This is an intermediate convex-geometric fact. The set

$$
 C=\operatorname{conv}\bigl(\{0\}\cup
                    \{r,-r:r\in\mathcal R_{S,N}\}\bigr)
\tag{55.10}
$$

is compact, convex and symmetric in the finite-dimensional space $W_{S,N}$. If $v_E\notin664016C$, strict separation from this compact convex set would give a linear functional $f$ with

$$
 f(v_E)>664016\sup_{c\in C}f(c)
       =664016\max_{r\in\mathcal R_{S,N}}|f(r)|,
\tag{55.11}
$$

contrary to (55.9). Thus $v_E\in664016C$. A finite convex combination in (55.10), with signs absorbed into the coefficients, supplies $v_E=\sum_j\lambda_jr_j$ and $\sum_j|\lambda_j|\le664016$. This is exact equality of free symbols, not equality modulo unspecified relations. Finally (54.8) gives $664016+27+2=664045$. $\square$

## 56. Embedding each five-effect row into the original four-dimensional grid

**定理 56.1（Same-grid face embedding with actual anchors）。** Every row in $\mathcal R_{S,N}$ embeds as a legal row in $\mathcal R_{4,N}$. Every tomography symbol and the zero symbol in (55.1) is an actual anchor in $\mathcal A_N$.

Proof. The four face endpoints embed by zero on the missing coordinate, retain their entries in $N^{-1}R$, and satisfy $0\le E\le S\le I_4$. The signed increment remains an original-grid Hermitian matrix. If the fifth face effect is $C_3=S-A-B-X$, then its four-dimensional complement is

$$
 C_4=I_4-A-B-X=(I_4-S)+C_3.
\tag{56.1}
$$

The two summands have orthogonal supports, with $0\le C_3\le S$. Hence $0\le C_4\le I_4$, and $C_4$ also belongs to the original grid. This checks all five required effects. The embedding $W_{S,N}\to W_{4,N}$ sends distinct effect symbols to distinct effect symbols, so it preserves (55.1) as an exact equality. By (54.6), each $Q\in\mathcal B_S$ is literally a member of $\mathcal B_4$. Also $0\in K_{4,N}$ and $\|0\|=0\le1/52$. Thus all delivered anchors are in $\mathcal B_4\cup\{0\}$; the proof uses no positive-radius small effect as an anchor. $\square$

## 57. A direct certificate for the complementary-column projection family

**定理 57.1（Uniform finite certificate on all dyadic scales at least 1024）。** Let $m\ge10$, $N=2^m$, and let $a,b\in\mathbb Z[i]$ satisfy $|a|^2+|b|^2=N-1$. With the same matrices as Part I, Proposition 19.1, put

$$
 U=\begin{pmatrix}a&b\\-\overline b&\overline a\end{pmatrix},\qquad
 V=\begin{pmatrix}I_2\\U\end{pmatrix},\qquad P=VV^*/N.
\tag{57.1}
$$

There are finite lists of original legal rows $r_j\in\mathcal R_{4,N}$, actual anchors $F_\ell\in\mathcal B_4\cup\{0\}\subset\mathcal A_N$, and real coefficients with

$$
 \delta_P=\sum_j\lambda_jr_j+\sum_\ell\beta_\ell\delta_{F_\ell},
 \qquad \sum_j|\lambda_j|\le1328033,\qquad
 \sum_\ell|\beta_\ell|\le56.
\tag{57.2}
$$

In particular the total coefficient cost is at most $1328089$, independently of $m,a,b$ in this domain. Every symbol uses the one original grid with denominator $N$.

Proof. Reuse the complementary-column identities of Part I, Proposition 19.1. Set

$$
 W=\begin{pmatrix}-U^*\\I_2\end{pmatrix},\qquad
 w_j=We_j,\qquad Q_j=w_jw_j^*/N\quad(j=1,2).
\tag{57.3}
$$

Here $e_j$ in (57.3) is the $j$th coordinate vector of $\mathbb C^2$. Since $U^*U=UU^*=(N-1)I_2$,

$$
 W^*W=NI_2,\qquad VV^*+WW^*=NI_4,\qquad
 Q_1Q_2=0,\qquad Q_1+Q_2=I_4-P.
\tag{57.4}
$$

Each $Q_j$ is a rank-one projection with Gaussian-integer numerator and denominator $N$. Explicitly,

$$
 w_1=(-\overline a,-\overline b,1,0)^{\mathsf T},\qquad
 w_2=(b,-a,0,1)^{\mathsf T}.
\tag{57.5}
$$

Thus $Q_1$ is supported on the coordinate face $\{1,2,3\}$, while $D_3Q_2=0$. Define

$$
 E=I_4-Q_2-D_3.
\tag{57.6}
$$

The orthogonality of $Q_2,D_3$ makes $E$ a rank-two original-grid projection, and $E$ is supported on $\{1,2,4\}$. Put

$$
 A=D_3,\qquad B=Q_1,\qquad X=P-D_3.
\tag{57.7}
$$

Then $X$ is a signed Hermitian matrix on the original grid, and the five effects required for legality are exactly

$$
 A=D_3,\quad B=Q_1,\quad A+X=P,\quad
 B+X=P+Q_1-D_3=E,\quad
 I_4-A-B-X=Q_2.
\tag{57.8}
$$

All five are projections in $K_{4,N}$. Hence the original row

$$
 r=\delta_P+\delta_{Q_1}-\delta_{D_3}-\delta_E
\tag{57.9}
$$

is legal, and $\delta_P=r+\delta_{D_3}+\delta_E-\delta_{Q_1}$.

Apply Theorem 55.1 to $E$ on $S_{124}=D_1+D_2+D_4$ and to $Q_1$ on $S_{123}=D_1+D_2+D_3$. Theorem 56.1 embeds their finite row combinations $R_E,R_{Q_1}$ legally into $W_{4,N}$. Their traces are $2,1$, respectively, so substitution gives the exact certificate

$$
 \begin{aligned}
 \delta_P={}&r+R_E-R_{Q_1}+\delta_{D_3}-\delta_0\\
 &+\sum_{Q\in\mathcal B_{S_{124}}}\alpha_Q(E)\delta_Q
   -\sum_{Q\in\mathcal B_{S_{123}}}\alpha_Q(Q_1)\delta_Q.
 \end{aligned}
\tag{57.10}
$$

There is no residual effect symbol in (57.10). The row cost is at most $1+2\cdot664016=1328033$. The anchor cost is at most $1+1+27+27=56$, where the two unit terms are $D_3$ and $0$. Combining repeated symbols can only decrease the resulting absolute coefficient sum. Altogether,

$$
 1+1+2\cdot664016+27+27+1=1328089.
\tag{57.11}
$$

Both face lists are finite by the finite convex-combination step in Theorem 55.1, and the direct row adds one further row. $\square$

**定义 57.2（The remaining scale domain）。** The dyadic scales outside Theorem 57.1 are exactly

$$
 N\in\{2,4,8,16,32,64,128,256,512\}.
\tag{57.12}
$$

For every pair $a,b$ with $|a|^2+|b|^2=N-1$ at each of these nine scales, this argument supplies no certificate and claims no finite exact coefficient cost. The term proportional to $N^{-1}$ in the coarse clause of Part I, Theorem 33.1, does not give the homogeneous functional inequality (55.9) by division by arbitrarily small $t$. A finite number of remaining grids alone establishes neither row-and-anchor span nor a finite certificate cost. The assertion of one uniform cost for every $m\ge1$ therefore remains unresolved by these theorems, as does any implication to the parent approximate-density existence question. The fine-scale family result concerns the original-Hermitian error relations of Part I, Definition 18.1, before positivity repair.

## 58. Mathematical sources of the finite-dual application

**文献 58.1（Reused ingredients and precise scope）。** [Part I](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md), Definition 16.1 and (16.6)--(16.7), supply the original basis, its sign convention and its coefficient bound. Theorem 33.1, specifically the fine estimate (33.20), supplies the inequality $332008\epsilon$ for a complete table normalized on its own three-dimensional identity when $N\ge648$. Proposition 19.1 supplies the complementary-column projections used in (57.3)--(57.4). R. T. Rockafellar, *Convex Analysis*, Princeton University Press, §11, supplies the standard finite-dimensional separation principle used between (55.9) and (55.11). The perturbation (55.2)--(55.9) and the subsequent exact finite-coefficient conclusion are the interface asserted here; the final direct row reuses the existing projections. The conclusions are ordinary mathematical deductions in the stated finite-grid setting, with no global literature-priority assertion.

## 追加锚（本行以下为增补区）

## 59. Exact integer-norm descent on a three-coordinate face

**定理 59.1（Costed rank-one descent on every original dyadic grid）。** Fix any coordinate face $S$ of Definition 54.2, any $N=2^m$ with $m\ge1$, and any nonzero $v\in\mathbb Z[i]^3$ with $s=\|v\|^2\le N$. Write

$$
 q_N(v)=\delta_{vv^*/N}-\delta_0,\qquad [E]=\delta_E-\delta_0.
\tag{59.1}
$$

Then $q_N(v)$ is a finite real combination of rows in $\mathcal R_{S,N}$ and anchors in $\mathcal B_S\cup\{0\}$ with total absolute coefficient sum at most $100\cdot4^s$. No values of a function on different grids are identified.

Proof. All symbols in this proof have denominator $N$. We first specify the exact row identities and the initial cases, and then give a strict descent. For positive grid matrices with $A+B=C+D\le S$, the identity

$$
 [A]+[B]-[C]-[D]=r(C,B,A-C)
\tag{59.2}
$$

uses a single legal row: its four endpoints are $C,B,A,D$, and its fifth effect is $S-A-B$. In particular $[A]+[B]-[A+B]=r(0,B,A)$. Repeatedly using this last identity gives, whenever $LT\le S$ for a positive integer $L$,

$$
 [LT]=L[T]-\sum_{k=1}^{L-1}r(0,kT,T).
\tag{59.3}
$$

Every complement in (59.3) is $S-(k+1)T\ge0$.

If $s=1$, the matrix $vv^*/N$ is $D_j/N$. Apply (59.3) with $L=N$ to express its centered symbol with cost at most $2/N+(N-1)/N\le3$. For $s=2$, either $vv^*/N=2D_j/N$, or $v$ has two unit coordinates. In the latter case $T=vv^*/2$ is one of the four two-coordinate unit-phase projections. Two are $R_{jk},J_{jk}$ in (54.3); each of the other two is the orthogonal complement of one of these inside $D_j+D_k$. Formula (59.2), comparing the two orthogonal projections with $D_j,D_k$, expresses its centered symbol with cost at most five. Applying (59.3) with $L=N/2$ consequently expresses $q_N(v)$ with cost at most six. The single-coordinate case follows by the same scaling from $D_j$. Thus the bound eleven is valid for every $s\le2$.

For $s=3$, necessarily $N\ge4$. If there are two nonzero coordinates, their squared norms are two and one. Let $w$ vanish on the norm-two coordinate and equal $i$ times the norm-one coordinate of $v$. Then $w\equiv v\pmod{1+i}$, $\|w\|^2=1$, and $\operatorname{Re}(v^*w)=0$. The largest eigenvalue of $vv^*+ww^*$ is $2+\sqrt2<4$. The integral vectors

$$
 u=(v+w)/(1+i),\qquad z=(v-w)/(1+i)
\tag{59.4}
$$

both have squared norm two. Equation (59.2) applied to $vv^*/N+ww^*/N=uu^*/N+zz^*/N\le S$ gives a certificate of cost at most $1+3\cdot11=34$.

In the remaining case write $v_0=(a,b,c)$ with $a,b,c$ units and put $v_1=(-a,b,c)$, $v_2=(a,-b,c)$. For each of the three pairs, $v_i\equiv v_j\pmod{1+i}$ and $|v_i^*v_j|=1$. Hence the largest eigenvalue of $v_iv_i^*+v_jv_j^*$ is four, and (59.4) produces one vector of squared norm two and another of squared norm four. The latter outer product is twice the outer product of a vector of squared norm two. Its centered symbol has cost at most $2\cdot11+1=23$ by (59.3). Thus each equation for $q_N(v_i)+q_N(v_j)$ has right-hand certificate cost at most $1+11+23=35$. Half the sum of the equations for pairs $(0,1),(0,2)$ minus the equation for $(1,2)$ expresses $q_N(v_0)$ with cost at most $105/2<100$. This proves a common initial bound of one hundred for $s\le3$, including all coordinate phases.

Now use strong induction on the positive integer $s\ge4$. Put $\pi=1+i$. If every coordinate of $v$ is divisible by $\pi$, then $v=\pi u$ and $vv^*=2uu^*$. Equation (59.3) with $L=2$ reduces the certificate to two copies at squared norm $s/2<s$, and one row.

Otherwise let $r\in\{1,2,3\}$ be the number of coordinates not divisible by $\pi$. For such a coordinate $v_j=x+iy$, the integers $x,y$ have opposite parity. Choose a unit $w_j$ so that

$$
 |\operatorname{Re}(\overline{v_j}w_j)|=\min(|x|,|y|)
 \le (|v_j|^2-1)/4;
\tag{59.5}
$$

set the other $w_j$ equal to zero. To check the inequality, put $t=\min(|x|,|y|)$. Opposite parity gives $|v_j|^2\ge t^2+(t+1)^2\ge4t+1$, also when $t=0$. Thus

$$
 w\equiv v\pmod\pi,\qquad \|w\|^2=r,\qquad
 |\operatorname{Re}(v^*w)|\le(s-r)/4.
\tag{59.6}
$$

First suppose $s<N$ and put $k=N-s$. If $r\le k$, then $vv^*+ww^*\le(s+r)S\le NS$. The vectors (59.4) are integral and satisfy

$$
 \max(\|u\|^2,\|z\|^2)
 =\frac{s+r+2|\operatorname{Re}(v^*w)|}{2}
 \le\frac{3s+r}{4}<s.
\tag{59.7}
$$

Also $r<s$. Equation (59.2) therefore expresses $q_N(v)$ using three smaller squared norms and one row.

The congruence $r\equiv s\equiv k\pmod2$ shows that the only omitted possibility is $k=1,r=3$. For $N\ge16$, use the unit choice in Part I, (33.11)--(33.12), which gives $\|w\|^2=3$, $w\equiv v\pmod\pi$ and

$$
 vv^*+ww^*\le NS,\qquad |v^*w|^2\le N-3.
\tag{59.8}
$$

Here $\sqrt{N-3}<(N-4)/2$, because $N^2-12N+28>0$ for $N\ge16$. Consequently the norms in (59.4) are at most $(N+2)/2+\sqrt{N-3}<N-1=s$. This again gives strict descent.

At $N=8$, the omitted vector has squared coordinate norms $5,1,1$. On the norm-five coordinate choose a unit $w_j$ with $\overline{v_j}w_j=1+2i$ or $1-2i$; every Gaussian integer of norm five permits one of these choices. On the other coordinates put $w_j=-v_j$. Then $v^*w=-1\pm2i$, $\|w\|^2=3$ and $w\equiv v\pmod\pi$. The Gram matrix of the two columns $v,w$ has diagonal $7,3$ and off-diagonal squared modulus five. Its complement in $8I_2$ has diagonal $1,5$ and determinant zero, so $vv^*+ww^*\le8S$. The two transformed vectors have squared norms four and six, both below seven. At $N=4$ this exceptional case has $s=3$, already proved; at $N=2$ it is an initial case. These are all dyadic possibilities.

Finally suppose $s=N$. Since $N$ is even, $r=2$. Permute notation so $v=(a,b,c)$ with $a,b$ not divisible by $\pi$ and $c$ divisible by $\pi$. Each of $|a|^2,|b|^2$ is one modulo four. As $s\ge4$ is divisible by four, $|c|^2\equiv2\pmod4$, so $c\ne0$. Put

$$
 w=(-\overline b,\overline a,0),\qquad r'=\|w\|^2=N-|c|^2<N.
\tag{59.9}
$$

Then $v^*w=0$, $w\equiv v\pmod\pi$, and $vv^*+ww^*\le NS$. The two transformed vectors have squared norm $(N+r')/2<N$. This is again a reduction to three smaller positive squared norms and one row. These are the orthogonal parity identities of Part I, (33.16), used here without its large-$N$ estimates.

In every induction step the certificate cost is at most $1+3\cdot100\cdot4^{s-1}\le100\cdot4^s$; the divisible case uses only two smaller terms. All row endpoints and their complements were checked before the induction was applied. Each step lowers a positive integer, so the resulting lists are finite. The initial cases and this induction prove the assertion. $\square$

## 60. Coarse face certificates and the original complementary-column target

**定理 60.1（Exact costed face supply and all-scale original target）。** For every coordinate face $S$ and every dyadic $N\ge2$, each $E\in K_{S,N}$ has a centered certificate using $\mathcal R_{S,N}$ and $\mathcal B_S\cup\{0\}$ with cost at most

$$
 M_N=3N(100\cdot4^N+1).
\tag{60.1}
$$

For every $m\ge1$, $N=2^m$, and every $a,b\in\mathbb Z[i]$ with $|a|^2+|b|^2=N-1$, the projection $P$ of (57.1) has a finite certificate in the original space $W_{4,N}$, using only original legal rows and anchors in $\mathcal B_4\cup\{0\}$, with total absolute coefficient sum at most the single finite real constant

$$
 L=3072(100\cdot4^{512}+1)+4.
\tag{60.2}
$$

Proof. Reuse the integral positive-semidefinite three-dimensional decomposition proved in Part I, (33.5)--(33.8). It applies to $NE$ for every $N$; the large-scale assumption there is needed for the later error estimates, not for this integral decomposition. Thus

$$
 NE=\sum_{j=1}^{\ell}v_jv_j^*,\qquad
 v_j\in\mathbb Z[i]^3\setminus\{0\},\qquad \ell\le\operatorname{Tr}(NE)\le3N.
\tag{60.3}
$$

Each summand and every partial sum, divided by $N$, lies between zero and $E\le S$. In particular $\|v_j\|^2\le N$. Successive additive rows give

$$
 [E]=\sum_{j=1}^{\ell}q_N(v_j)
 -\sum_{j=2}^{\ell}r\left(0,\sum_{h<j}v_hv_h^*/N,v_jv_j^*/N\right).
\tag{60.4}
$$

Theorem 59.1 bounds the cost by $\ell\,100\cdot4^N+\ell-1\le M_N$. For $E=0$ the empty certificate suffices.

For the original target use precisely the legal row $r$ in (57.7)--(57.9), with $Q_1,E$ on the two specified coordinate faces. Its identity, in centered symbols, is

$$
 \delta_P=r+[D_3]+[E]-[Q_1]+\delta_0.
\tag{60.5}
$$

Theorem 56.1 embeds each face row with all five legality effects on the original four-dimensional grid. The symbols in $[D_3]$ and $\delta_0$ are actual anchors. Applying (60.1) twice therefore gives total cost at most $1+2+2M_N+1=2M_N+4$ for every original Gaussian pair, with no parameter reduction or covariance assumption. For $N\le512$, monotonicity of the displayed numerical bound gives $2M_N+4\le L$. For $N\ge1024$, reuse Theorem 57.1, whose cost $1328089$ is less than (60.2). These two domains exhaust all $N=2^m$, $m\ge1$. All coefficients are real, all lists are finite, and all equalities used are identities of free symbols generated by the original rows. $\square$

**定义 60.2（Scope and mathematical attribution）。** Theorem 60.1 concerns the exact original-Hermitian relation for the specific family (57.1). It does not assert the parent's approximate-density existence conclusion or a physical realization. The integral decomposition, orthogonal parity exchange and exceptional-margin unit choice are reused from Part I, Theorem 33.1; its cited Hermite bounds and Gaussian module facts retain their original attributions. The new deduction is the strict squared-norm descent (59.5)--(59.9), its complete small-norm initialization and the exact norm-seven exchange, which supply finite coefficient bounds at the formerly omitted scales. The fine constant and the final complementary-column row are reused from Theorem 57.1.

## 追加锚（本行以下为增补区）

## 61. Complement transfer closes the full quadratic-margin event

**定理 61.1（四维二次谱析取的全事件闭合）。** Retain the original table, the labelled binary and ternary menus, and the tomography matrix $H$ of Definition 50.1. Let $A_0$ and $C_0$ be the finite constants of Definition 53.1, and put

$$
 A_{\mathrm{full}}=A_0,\qquad
 C_{\mathrm{full}}=C_0+902824+10.
\tag{61.1}
$$

For every integer $m\ge1$, with $N=2^m$, every $\epsilon\in[0,1/10]$, and every $E\in K_{4,m}$ satisfying

$$
 \lambda_{\max}(E)\le 1-\frac{A_{\mathrm{full}}}{N^2}
 \quad\text{or}\quad
 \lambda_{\min}(E)\ge\frac{A_{\mathrm{full}}}{N^2},
\tag{61.2}
$$

the same single table obeys

$$
 \boxed{\ |p(E)-\operatorname{Tr}(HE)|
       \le C_{\mathrm{full}}\left(\epsilon+\frac1N\right).\ }
\tag{61.3}
$$

The constants are independent of $N$, the table, $\epsilon$ and $E$.

**证明。** Write $e(X)=p(X)-\operatorname{Tr}(HX)$, with the convention $e(0)=p(0)$ when a residual is zero. For $N<2048$, Part I, Theorem 16.2 gives $\lVert H\rVert_{\mathrm{op}}\le8$ and hence $|e(E)|\le33$. Since $N_0\ge2048$ and $C_0\ge33N_0$ by Definition 53.1, (61.3) follows at every such scale.

Assume now $N\ge2048$. First suppose the upper alternative in (61.2). It gives $\lVert E\rVert_{\mathrm{op}}<1$, so Part I, Theorem 57.4 supplies a decomposition residual $G_0=G/N$, either zero or a positive-definite Gaussian integral interval atom, with

$$
 |e(E)-e(G_0)|\le902824\epsilon,\qquad 0\preceq G_0\preceq E.
\tag{61.4}
$$

If $G=0$, the zero convention and $p(0)\le2\epsilon$ give the required estimate. Otherwise $G_0\preceq E$ implies

$$
 \lambda_{\max}(G_0)\le\lambda_{\max}(E)
 \le1-A_0/N^2.
\tag{61.5}
$$

Part III, Theorem 53.3 therefore gives $|e(G_0)|\le C_0(\epsilon+1/N)$. Combining this with (61.4) proves (61.3) in the upper branch.

Now suppose the lower alternative in (61.2), and set $F=I_4-E$. Then $F\in K_{4,m}$, $\lVert F\rVert_{\mathrm{op}}<1$, and

$$
 \lambda_{\max}(F)=1-\lambda_{\min}(E)
 \le1-A_0/N^2.
\tag{61.6}
$$

Apply Part I, Theorem 57.4 to $F$. It supplies a residual $G_F/N$, zero or a positive-definite interval atom, with $G_F/N\preceq F$ and

$$
 |e(F)-e(G_F/N)|\le902824\epsilon.
\tag{61.7}
$$

The zero case again has $|e(0)|\le2\epsilon$. In the nonzero case, (61.6) and $G_F/N\preceq F$ give the upper margin required by Part III, Theorem 53.3, so

$$
 |e(F)|\le(C_0+902824)\epsilon+C_0/N.
\tag{61.8}
$$

Finally the original binary row for $(E,F)$ and the existing anchor estimate $|\operatorname{Tr}H-1|\le9\epsilon$ give

$$
 |e(E)+e(F)|
 =|p(E)+p(F)-\operatorname{Tr}H|
 \le10\epsilon.
\tag{61.9}
$$

Equations (61.8)--(61.9) yield

$$
 |e(E)|\le(C_0+902824+10)\left(\epsilon+\frac1N\right),
$$

which is (61.3). The lower branch therefore uses the complement before extraction; no lower spectral margin is asserted for a subatom of $E$.

The only inputs beyond the displayed definitions are the original-grid residual decomposition of Theorem 57.4, the absolute upper-margin atom estimate of Theorem 53.3, and the binary complement estimate (61.9), which is the same relation recorded in Part II, (164.11). The result is an ordinary theory-text consequence on one supplied finite table. It adds no cross-scale relation, continuum extension, probability-acquisition premise, physical realization or kernel verification, and it makes no claim about the smaller value of $A$ or the optimality of $C_{\mathrm{full}}$. $\square$

**定义 61.2（Result boundary）。** Theorem 61.1 closes the original four-dimensional quadratic-margin estimate at the explicit finite threshold $A_0=2A_\dagger$ inherited from Definition 53.1. It does not assert the estimate for every $A>2$, remove the dependence on the previously fixed finite-menu constants, or supply a physical implementation of the table. The former residual atom obligation (57.15) is consumed by the upper-margin closure (53.21) together with complement-before-extraction; the source's dimension-$d\ge4$ unrestricted finite-menu counterfamily remains a separate statement.

## 追加锚（本行以下为增补区）

## 62. 两个原始映射、内部插入与严格恢复

**定义 62.1（比较入口与条件性接口）。** 对每个实际载体 $X=A,D,E$，先取非零有限维实有序空间、闭尖生成锥 $X_+$、严格正的归一化泛函 $u_X$、紧的全态基底 $K_X=\{x\in X_+:u_X(x)=1\}$ 和全部对偶效应 $[0,u_X]$。记纯态集合为 $P_X$，对 $x\in K_X$ 定义最小确认读数，并在每个载体上保留有限混合律 S：

$$
\begin{aligned}
T_\xi(x)&=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\\
T_\xi\!\left(\sum_\ell w_\ell\eta_\ell\right)
 &=\sum_\ell w_\ell T_{\eta_\ell}(\xi)
\quad\left(\xi,\eta_\ell\in P_X,\quad w_\ell\ge0,\quad\sum_\ell w_\ell=1\right).
\end{aligned}
\tag{62.1}
$$

第二式量化于每个有限纯态族及每个概率权重族。另行保留 [Müller–Ududec 条目「Complete conditional candidate and its scope」](../../../Library/QuantumStates/mullerududec2012selfduality.md#complete-conditional-candidate-and-its-scope) 中保归一化的 S 到标准迹 Jordan 几何的纸面桥，应用于三个实际全载体。只有该桥之后，才使用下面的 Jordan 单位、标准迹和迹伴随。单点混合给出的端点互反不能替代有限混合律，也不能替代这条条件桥。

下述推导复用 [Library 条目中的仓内推导「Positive marginals recover the joint-effect contract」](../../../Library/QuantumStates/barnumhilgert2019spectral.md#positive-marginals-recover-the-joint-effect-contract) 的二元边缘纸面接口 (15)–(18)：标准迹 EJA 间的正双线性且实张成的准备，若有两条在整个联合正锥上正且标准保迹的边缘，并满足两条全部实向量的普通乘积丢弃律，则准备保单位，其实张量线性化为满迹内积等距同构。两次使用前均须满足这组完整前提。最终几何只在严格恢复之后复用同条目「Three primitive maps and the forced missing pair view」的既有表示结论，不重新分类。

**定义 62.2（二映射的前置条件）。** 在定义 62.1 的桥后，$A,D,E$ 是实际非零有限维实 Euclidean Jordan 代数，取整个平方锥、全部正迹一态、全部效应区间 $[0,1_X]$，以及

$$
\langle x,y\rangle_X=\tau_X(x\circ y),\qquad
n=\tau_A(1_A)=\operatorname{rank}A>0,\qquad e=\frac{1_A}{n},\qquad
\omega=\frac{1_D}{\tau_D(1_D)}.
\tag{62.2}
$$

每个直和扇区的每个本原幂等元的标准迹均为一，不另作扇区迹缩放。实张量积只取乘积迹内积，尚不预设张量正锥或正重括号映射。仅给两个原始映射：实双线性 $L:D\times A\to E$ 与实线性 $p:E\to D$，满足

$$
L(D_+,A_+)\subseteq E_+,\qquad p(E_+)\subseteq D_+,
\qquad \tau_Dp=\tau_E.
\tag{62.3}
$$

这里 $L$ 的正性覆盖每个 $d\in D_+$，包括纠缠 $d$；$p$ 的正性覆盖整个 $E_+$。依次定义

$$
\begin{aligned}
B(d,c)&=pL(d,c),& B&:D\times A\to D,\\
M(a,b)&=B(B(\omega,a),b),& M&:A\times A\to D,\\
Q(a,b,c)&=L(M(a,b),c),& Q&:A^3\to E,\\
J(a)&=M(a,1_A),& r&=J^*:D\to A,\\
H(d)&=L(d,1_A),& h&=H^*:E\to D.
\end{aligned}
\tag{62.4}
$$

$M$ 的两次读回都用同一个 $p$；$J,H$ 插入的都是未归一化单位 $1_A$。保留两条实际实张成条件

$$
\operatorname{span}_{\mathbb R}\{M(a,b):a,b\in A\}=D,\qquad
\operatorname{span}_{\mathbb R}\{L(d,c):d\in D,c\in A\}=E,
\tag{62.5}
$$

以及 I、W、III 三条全部实向量恒等式：

$$
\begin{aligned}
\mathrm{(I)}\quad&rM(a,b)=\tau_A(b)a &&(a,b\in A),\\
\mathrm{(W)}\quad&H^*H=n\,\mathrm{id}_D &&\text{在整个实 }D\text{ 上},\\
\mathrm{(III)}\quad&pQ(a,b,c)=\tau_A(a)M(b,c) &&(a,b,c\in A).
\end{aligned}
\tag{62.6}
$$

W 等价于 $\langle Hd,Hd'\rangle_E=n\langle d,d'\rangle_D$ 对所有实 $d,d'\in D$ 成立，包含纠缠方向，并非只检验已准备的乘积。它只保留旧律 $hL(d,c)=\tau_A(c)d$ 在 $c=1_A$ 的未归一化单位切片；完整旧律记为 (II)，将在定理 62.3 中推出。归一化插入 $L(d,e)=H(d)/n$ 的比较配对因子是 $1/n$，不是一。

这些量词包括有符号和迹零向量。此阶段不另给 $r,h$ 的正性或保迹性，不给 $M,L$ 的单位律，不给任何张量等距性。实张成也不表示每个联合正态都是乘积态的凸组合。

**定理 62.3（单位切片推出完整丢弃律）。** 定义 62.2 的前置条件及定义 62.1 的二元接口推出 $M,J,r$ 正，且有正保迹的 $s:D\to A$ 满足第二边缘律。更确切地，

$$
\begin{gathered}
M(1_A,1_A)=1_D,\qquad L(1_D,1_A)=1_E,\\
rM(a,b)=\tau_A(b)a,\qquad sM(a,b)=\tau_A(a)b,\\
\tau_Ar=\tau_D=\tau_As,\qquad
\tau_Dh=\tau_E,\qquad t:=sp\text{ 正且保迹},\\
hL(d,c)=\tau_A(c)d,\qquad tL(d,c)=\tau_D(d)c.
\end{gathered}
\tag{62.7}
$$

$h$ 也在整个 $E_+$ 上正。线性化

$$
\begin{aligned}
\mathcal M &: A\otimes_{\mathbb R}A\longrightarrow D,
 &\mathcal M(a\otimes b)&=M(a,b),\\
\mathcal L &: D\otimes_{\mathbb R}A\longrightarrow E,
 &\mathcal L(d\otimes c)&=L(d,c),\\
\mathcal Q&=\mathcal L(\mathcal M\otimes\mathrm{id}_A)
 &: (A\otimes_{\mathbb R}A)\otimes_{\mathbb R}A&\longrightarrow E
\end{aligned}
\tag{62.8}
$$

均为满迹内积等距同构。在其余前置条件下，W 与完整 (II) 等价；此推导不使用交叉插入 $I_{13}$ 的正性。

**证明。** 先只用 I、III 建立归一化，不使用 II 或 W。正双线性与正映射的复合使 $B,M,J$ 正；平方锥自对偶使 $r=J^*$ 正。置 $U=M(1_A,1_A)\ge0$，定义正映射

$$
s=r\,pL(\mathord\cdot,e):D\to A.
\tag{62.9}
$$

由 (III) 再用 (I)，对全部实 $a,b$ 有

$$
sM(a,b)=\tau_A(a)rM(b,e)=\tau_A(a)b,
\qquad r^*1_A=U=s^*1_A.
\tag{62.10}
$$

最后的伴随等式尚非保迹断言：$r^*1_A=J(1_A)=U$，而在每个 $M(a,b)$ 上，$s^*1_A$ 与 $U$ 的配对都等于 $\tau_A(a)\tau_A(b)$，再由 (62.5) 的 $D$ 张成得到相等。

$U$ 在 $D_+$ 内部。对 $a,b\ge0$，取 $a\le\lambda1_A$、$b\le\mu1_A$，正双线性给出 $0\le M(a,b)\le\lambda\mu U$。若 $z\ge0$ 且 $\langle z,U\rangle_D=0$，则 $z$ 消去全部正乘积；锥生成性使它消去全部实乘积，实张成遂使 $z=0$。若 $U$ 的某个谱值为零，该谱空间的非零本原幂等元就给出这样的 $z$。故每个扇区的谱值都严格为正。

采用上述 Library 条目「Readback from unit insertion」(58)–(60) 中的二次表示归一化，写成

$$
\ell_x(y)=x\circ y,\qquad P_x=2\ell_x^2-\ell_{x^2},\qquad
C=P_{\sqrt U},\qquad C^{-1}=P_{U^{-1/2}}.
\tag{62.11}
$$

这里使用的标准二次表示正性由 [van de Wetering, Proposition 2.21 及包含 EJA 的 Proposition 2.25](https://arxiv.org/html/1912.01903v1#S2.counter21) 承担；公式采用该文引言中的 $P_x$ 公式。其余所需关系可直接由 Peirce 分解核对：对角化 $U$ 的本原框架中，设谱值为 $u_i>0$，则 $C$ 在对角空间上系数为 $u_i$，在非对角 Peirce 空间上系数为 $\sqrt{u_i u_j}$；显示的逆取对应倒数。迹形式结合性使 $\ell_x$ 自伴随，因而两者自伴随。它们均正，且

$$
C^{-1}U=1_D,\qquad CU=U^2.
\tag{62.12}
$$

这同时覆盖例外 EJA 与直和，不需要矩阵嵌入。置

$$
\widehat M=CM,\qquad \widehat R=rC^{-1},\qquad
\widehat S=sC^{-1}.
\tag{62.13}
$$

逐项检查第一次二元接口：$\widehat M$ 正双线性，因 $C$ 可逆仍实张成 $D$；两条边缘在整个 $D_+$ 上正；(62.10) 给出全部实向量的两条乘积丢弃律。再由自伴随性及 (62.12)，

$$
\widehat R^*1_A=\widehat S^*1_A=C^{-1}U=1_D.
\tag{62.14}
$$

故两条边缘都对未改动的标准迹保迹。现在才将 Library (15)–(18) 应用于 $(\widehat M,\widehat R,\widehat S)$。其单位结论给出 $1_D=\widehat M(1_A,1_A)=CU=U^2$。$U\ge0$ 的谱值于是全为一，故 $U=1_D$、$C=\mathrm{id}_D$。同一次二元结论遂给出原 $M$ 的单位律及 $\mathcal M$ 的满等距性，$r,s$ 也已正且保迹。特别地，

$$
\tau_DM(a,b)=\tau_A(a)\tau_A(b),\qquad
\langle M(a,b),M(x,y)\rangle_D
 =\langle a,x\rangle_A\langle b,y\rangle_A.
\tag{62.15}
$$

接着 $t=sp:E\to A$ 正且保迹，这里使用原始 $p$ 的已给保迹性。由 (III) 与 (62.10)，

$$
\begin{aligned}
tL(M(a,b),c)
 &=\tau_A(a)sM(b,c)\\
 &=\tau_A(a)\tau_A(b)c
 =\tau_D(M(a,b))c.
\end{aligned}
\tag{62.16}
$$

$M$ 的实张成将它扩展为所有实 $d,c$ 的 $tL(d,c)=\tau_D(d)c$。由于 $t$ 保迹，尚未使用 W 或 II 就有

$$
\tau_EL(d,c)=\tau_AtL(d,c)=\tau_D(d)\tau_A(c)
\quad(d\in D,\ c\in A).
\tag{62.17}
$$

以下使用标准 EJA 谱、支撑及范数事实；谱展开、规范迹基底和本原纯态的对应见 [Barnum–Hilgert, Theorem 4.2、Definition 4.3、Proposition 4.4](https://arxiv.org/html/1904.03753v1#S4)。为明确包含直和与例外代数，所需支撑推论可直接由 Peirce 分解给出：对幂等元 $v$ 及 $z=w^2\ge0$，迹形式结合性给出

$$
\langle v,z\rangle
 =\langle\ell_vw,w\rangle
 =\|w_1\|^2+\tfrac12\|w_{1/2}\|^2.
\tag{62.18}
$$

因此零配对迫使 $z\in E_0(v)$。对效应 $F$ 作谱展开，$\langle F,z\rangle=0$ 将 $z$ 限于 $F$ 的零谱支撑面；$\langle F,z\rangle=\tau(z)$ 则由 $1-F$ 将它限于一谱支撑面。这两个谱支撑面正交，故被同一效应分别以概率一和零接受的两个正迹一态彼此正交。对正元作谱展开也给出：零迹配对蕴涵零 Jordan 乘积。又若 $z\ge0,\tau(z)=1$，其非负谱系数 $\lambda_k$ 满足

$$
\|z\|^2=\sum_k\lambda_k^2\le1,\qquad
\|z\|^2=1\ \Longleftrightarrow\ z\text{ 是本原幂等元}.
\tag{62.19}
$$

若本原 $q$ 还满足 $\langle q,z\rangle=1$，则 $\langle1-q,z\rangle=0$ 迫使 $z\in E_1(q)=\mathbb Rq$，所以 $z=q$。这里 $E_1(q)$ 为一维，否则该子代数的谱分解会把 $q$ 分成两个非零正交幂等元，与本原性矛盾。这些论证逐扇区成立，不使用矩阵实现。

现固定任意本原 $q\in D$。由 (62.17)，$K_q(c):=L(q,c)$ 是正保迹映射，且 $tK_q=\mathrm{id}_A$。取 $A$ 的任意完整本原框架 $(f_j)_{j=1}^n$，令 $\rho_j=K_q(f_j)$。它们正且迹一；$t$ 正保迹使 $t^*$ 正且保单位，故同一个完整效应族给出

$$
0\le t^*f_j\le1_E,\qquad \sum_jt^*f_j=1_E,\qquad
\langle t^*f_j,\rho_k\rangle_E=\delta_{jk}.
\tag{62.20}
$$

上述一、零饱和支撑论证使 $\rho_j$ 两两正交。现在才使用 W：$Hq=\sum_j\rho_j$，而 $\|q\|^2=1$，所以

$$
n=\|Hq\|^2=\sum_{j=1}^n\|\rho_j\|^2.
\tag{62.21}
$$

每项至多一，故每项恰为一，所有 $\rho_j$ 都是本原幂等元。任意本原 $f\in A$ 均可补成完整框架，因此每个 $L(q,f)$ 都纯。这不是仅在指定乘积族上的额外检验或假设。

再取 $D$ 的完整本原框架 $(q_i)$，置 $\rho_{ij}=L(q_i,f_j)$。同一行已正交；不同行由 W 得 $\langle Hq_i,Hq_k\rangle_E=0$。每个 $0\le\rho_{ij}\le Hq_i$，故正锥自对偶性使所有跨行配对也为零。由零配对支撑事实，全部 $\rho_{ij}$ 是正交本原幂等元，因而

$$
V:=L(1_D,1_A)=\sum_{i,j}\rho_{ij},\qquad V^2=V.
\tag{62.22}
$$

还须证明 $V=1_E$，不能由等距性直接断言保单位。对任意 $d,c\ge0$，取 $d\le\lambda1_D,c\le\mu1_A$，全域正双线性给出 $0\le L(d,c)\le\lambda\mu V$。若 $z\ge0$ 且 $\langle z,V\rangle_E=0$，则它消去所有正乘积，再由锥生成性及 $L$ 实张成消去整个 $E$，所以 $z=0$。零谱值会提供非零正交本原元，故 $V$ 为内点。内点幂等元的全部谱值只能为一，遂 $V=1_E$。$H$ 正使 $h=H^*$ 在整个 $E_+$ 上正，且对所有实 $z$，$\tau_D(hz)=\langle H1_D,z\rangle_E=\tau_E(z)$，故 $h$ 保迹。

对任意本原 $q\in D,f\in A$，选择经过 $f$ 的框架，则 $\rho=L(q,f)$ 是 $Hq$ 的一个正交本原框架和项。因此 $h\rho$ 正且迹一，并有 $\langle q,h\rho\rangle_D=\langle Hq,\rho\rangle_E=1$。上述本原饱和事实迫使 $hL(q,f)=q$。两代数的本原幂等元各自实张成，实谱线性遂给出

$$
\mathrm{(II)}\qquad hL(d,c)=\tau_A(c)d
\quad\text{对所有实 }d\in D,c\in A.
\tag{62.23}
$$

反向只须在 II 中取 $c=1_A$，即得 $hH=H^*H=n\,\mathrm{id}_D$，恰为 W。完整 II 至此在第二次二元接口之前成立。

逐项检查第二次二元接口：两局部载体为标准迹 $D,A$，准备 $L$ 在整个 $D_+\times A_+$ 上正且实张成 $E$；两条边缘 $h:E\to D$、$t:E\to A$ 在整个 $E_+$ 上正且标准保迹；两条全部实向量的普通丢弃律正是 (II) 和 (62.16) 的线性扩展。现在应用同一 (15)–(18)，得到 $\mathcal L$ 满等距。与 $\mathcal M$ 复合即得 (62.8) 的 $\mathcal Q$。这只是指定实张量空间间的恒等式，没有预设独立右载体或正重括号映射。$\square$

**定义 62.4（已定型的插入及保留的整锥条件）。** 先用定理 62.3 得到可逆 $\mathcal M$，再定义双线性 $T$、其线性化 $\mathcal T$ 和线性插入 $I_{13}$：

$$
\begin{aligned}
T(a,c)&=L(M(a,1_A),c),& T&:A\times A\to E,\\
\mathcal T(a\otimes c)&=T(a,c),&\mathcal T&:A\otimes_{\mathbb R}A\to E,\\
I_{13}&=\mathcal T\mathcal M^{-1},&I_{13}&:D\to E.
\end{aligned}
\tag{62.24}
$$

因此 $I_{13}M(a,c)=Q(a,1_A,c)$ 在整个 $D$ 上给出唯一良定义的线性映射。这里使用的逆属于 $\mathcal M$；不能把定义域为 $D\otimes A$ 的 $\mathcal L$ 直接当成三份 $A$ 的映射来复合。完整二映射条件在此前置阶段之上，明确再要求一条几何条件：

$$
I_{13}(D_+)\subseteq E_+\quad\text{对整个实际正锥成立}.
\tag{62.25}
$$

随后才定义 $p_{13}:=I_{13}^*:E\to D$，并记 $p_{23}=p$。条件 (62.25) 保留了原来交叉读回的整锥正性内容；正乘积上的正性不能替代它，给它改名也没有删去它。

**定理 62.5（同载体、同映射上的严格唯一扩张）。** 定义 62.1–62.4 的完整条件，与将 W 换回完整 II 而其余数据及条件不变的二映射表示逐点等价；也与 Library「Readback from unit insertion」的 (53)、(56)、(57) 条件严格唯一扩张等价。该旧条件保留原始 $L,p_{13},p_{23}$，以混合式内部定义准备；本节只保留相同实际 $L,p=p_{23}$，以两次相同 $p$ 内部定义准备。互忘与互补保持实际载体及这两个映射逐个不变，并逐点恢复旧 $p_{13}$ 和两种内部 $M$。具体地，新条件推出

$$
\begin{gathered}
p_{13}\text{ 在整个 }E_+\text{ 上正},\qquad \tau_Dp_{13}=\tau_E,\\
p_{13}Q(a,b,c)=\tau_A(b)M(a,c),\\
M(a,b)=pL\bigl(p_{13}L(\omega,a),b\bigr)
\quad(a,b,c\in A).
\end{gathered}
\tag{62.26}
$$

**证明。** 先从完整二映射条件出发。定理 62.3 已在没有 (62.25) 时建立定义 62.4 的良定义性和单位律，故

$$
I_{13}(1_D)=L(M(1_A,1_A),1_A)=1_E.
\tag{62.27}
$$

此时使用 (62.25) 及自对偶性得到 $p_{13}=I_{13}^*$ 在整个 $E_+$ 上正。对所有实 $z\in E$，

$$
\tau_D(p_{13}z)=\langle I_{13}1_D,z\rangle_E=\tau_E(z),
\tag{62.28}
$$

故 $p_{13}$ 保迹。由 $\mathcal Q$ 的等距性，对全部实 $x,y,a,b,c\in A$，

$$
\begin{aligned}
\langle M(x,y),p_{13}Q(a,b,c)\rangle_D
 &=\langle Q(x,1_A,y),Q(a,b,c)\rangle_E\\
 &=\langle x,a\rangle_A\tau_A(b)\langle y,c\rangle_A\\
 &=\langle M(x,y),\tau_A(b)M(a,c)\rangle_D.
\end{aligned}
\tag{62.29}
$$

$M$ 实张成给出 (62.26) 的交叉律，另一条交叉律已是 (III)。

还必须恢复原来的混合内部定义。先由两条交叉律及 $M$ 实张成，将它们线性扩展到所有实 $d\in D,c\in A$：

$$
p_{13}L(d,c)=M(rd,c),\qquad
pL(d,c)=M(sd,c).
\tag{62.30}
$$

例如第一式在 $d=M(a,b)$ 上两边均为 $\tau_A(b)M(a,c)$，第二式两边均为 $\tau_A(a)M(b,c)$，所以线性扩展合法。这也正是 Library (52) 的全向量形状。由 $M$ 单位律、(I) 及 (62.15)，$r1_D=n1_A$、$\tau_D(1_D)=n^2$，从而

$$
r\omega=e,\qquad
sM(r\omega,a)=\tau_A(e)a=a.
\tag{62.31}
$$

现在用 (62.30) 得到

$$
\begin{aligned}
pL\bigl(p_{13}L(\omega,a),b\bigr)
 &=pL(M(r\omega,a),b)\\
 &=M(sM(r\omega,a),b)=M(a,b).
\end{aligned}
\tag{62.32}
$$

这没有在证明混合定义相等之前调用依赖该定义的旧条件。至此旧条件的全部前提已逐项成立：$L$ 全域正且张成，两个旧交叉读回全锥正，$p_{13}$ 保迹，(53) 的内部准备与当前 $M$ 相同，$J,r,Q$ 因而相同，两条实张成和 (57) 的三条全部实向量律也相同，其中完整 (II) 已由 W 推出。于是可以复用旧唯一扩张及表示定理。

反向从旧 (53)、(56)、(57) 条件出发，以 $\bar M,\bar Q,\bar r$ 表示其混合定义的映射，保留相同 $L,p=p_{23}$。此时旧「Readback from unit insertion」的归一化结论及其到「Three primitive maps and the forced missing pair view」的等价已适用；「One preparation determines the binary preparation」(51)–(52) 提供全向量扩展；(40)、(48) 提供缺失丢弃。精确取用的结论是：$p$ 保迹，$\bar M$ 保单位，$\bar{\mathcal M},\bar{\mathcal L},\bar{\mathcal Q}$ 满迹等距，且

$$
\begin{gathered}
\bar s=\bar r\,pL(\mathord\cdot,e)\text{ 正且保迹},\\
\bar s\bar M(a,b)=\tau_A(a)b,\qquad
pL(d,c)=\bar M(\bar s d,c)\quad(d\in D,c\in A),\\
h=H^*\text{ 是旧 }p_{12},\qquad hL(d,c)=\tau_A(c)d.
\end{gathered}
\tag{62.33}
$$

这些纸面接口的前提正是当前完整旧条件，不把乘积上的断言冒充全向量断言。由 (62.33)，对每个实 $d,a,b$，

$$
\begin{aligned}
pL\bigl(pL(d,a),b\bigr)
 &=pL\bigl(\bar M(\bar s d,a),b\bigr)\\
 &=\bar M\bigl(\bar s\bar M(\bar s d,a),b\bigr)\\
 &=\tau_A(\bar s d)\bar M(a,b)
 =\tau_D(d)\bar M(a,b).
\end{aligned}
\tag{62.34}
$$

取 $d=\omega$，便得二映射内部的 $M=\bar M$。因此 $J,r,Q$ 分别等于旧 $\bar J,\bar r,\bar Q$；两条实张成、(I)、(III) 直接保留；(62.33) 中旧派生 $p_{12}$ 满足完整 (II)，在 $c=1_A$ 处即给出 W。定义 62.2 的全部前置条件已经成立，故依 (62.24) 定义新的 $I_{13}$。

还需证明它确为旧 $p_{13}$ 的伴随，而非另一个同名插入。用旧交叉律和旧 $\bar{\mathcal M}$ 等距性，对所有实 $a,c,x,y,z\in A$，

$$
\begin{aligned}
\langle p_{13}^*\bar M(a,c),\bar Q(x,y,z)\rangle_E
 &=\langle\bar M(a,c),p_{13}\bar Q(x,y,z)\rangle_D\\
 &=\tau_A(y)\langle a,x\rangle_A\langle c,z\rangle_A\\
 &=\langle\bar Q(a,1_A,c),\bar Q(x,y,z)\rangle_E\\
 &=\langle I_{13}\bar M(a,c),\bar Q(x,y,z)\rangle_E.
\end{aligned}
\tag{62.35}
$$

倒数第二步用旧 $\bar{\mathcal Q}$ 的等距性。$\bar Q$ 乘积实张成 $E$，故两向量相等；$\bar M$ 乘积实张成 $D$，故整个 $D$ 上 $I_{13}=p_{13}^*$。旧 $p_{13}$ 全锥正，自对偶性于是给出恰好 (62.25)。

从二映射条件补入 $p_{13}=I_{13}^*$ 再忘去它，保留的实际 $L,p$ 不变；从旧条件忘去 $p_{13}$ 再补入，由 (62.35) 得回原 $p_{13}$，由 (62.34) 得回原 $M$。若另一个实线性读回满足相同旧交叉律，它在每个张成的 $Q(a,b,c)$ 上都与 $p_{13}$ 相同，因而在 $E$ 上唯一。这是同一实际对象上的严格逆关系，不只是选取矩阵坐标后的同构类对应。$\square$

此处既减少原始映射数据，也将完整 (II) 缩为其未归一化单位切片 W；在其余保留条件内，这是实际的切片冗余，不只是改名。幸存的 $p$ 仍直接要求保迹，旧 $p_{13}$ 的全锥正性仍为 (62.25)。完整 II、纯乘积、$r,h$ 保迹、两个单位律及等距性均已推导，没有另行假设。由 (62.17)，正的归一化插入 $K=L(\mathord\cdot,e)=H/n$ 保迹，且

$$
\langle Hd,Hd'\rangle_E=n\langle d,d'\rangle_D,\qquad
\langle Kd,Kd'\rangle_E=\frac1n\langle d,d'\rangle_D
\quad(d,d'\in D).
\tag{62.36}
$$

数学单位插入不表示物理上可用的装置；未由此得到全部剩余条件相互独立或公理数最小的结论。

**定理 62.6（两项保留条件的反例）。** 对每个整数 $n\ge2$，存在满足定义 62.1–62.2 和定理 62.3 全部结论，却违反 (62.25) 的矩阵实例；另有全经典实例满足除 W 外的全部完整候选条件，包括 (62.25)，但完整 II 失败。

**证明。** 取标准迹和整个正半定锥上的

$$
A=\operatorname{Herm}_n(\mathbb C),\qquad
D=\operatorname{Herm}_{n^2}(\mathbb C),\qquad
E=\operatorname{Herm}_{n^3}(\mathbb C).
\tag{62.37}
$$

所有转置在固定矩阵基中进行。$T_D$ 表示剩余两个因子的全转置，$\operatorname{Tr}_j$ 表示丢掉所标因子的普通部分迹。令

$$
L(d,c)=d\otimes c^{\mathsf T},\qquad
p=T_D\operatorname{Tr}_1:E\to D.
\tag{62.38}
$$

$L$ 对全部 $d,c\ge0$ 正，包括纠缠 $d$，因为转置保持单个矩阵正性，两个正矩阵的张量积正。部分迹全域正且保迹，剩余双份的全转置也是正保迹序自同构，所以 $p$ 对整个 $E_+$ 正且保迹。转置可逆，Hermitian 简单张量实张成全部 Hermitian 矩阵空间，所以所需两条张成均成立。全效应矩阵载体上对 $x\in K_X$ 的比较是 $T_\xi(x)=\operatorname{Tr}(\xi x)$，故满足有限混合 S 和已指定 Jordan 条件桥。

由原始定义直接计算，对全部实 Hermitian 输入，

$$
\begin{aligned}
B(d,c)&=(\operatorname{Tr}_1d)^{\mathsf T}\otimes c,\\
\omega&=I_{n^2}/n^2,\qquad B(\omega,a)=(I_n/n)\otimes a,\\
M(a,b)&=B(B(\omega,a),b)=a^{\mathsf T}\otimes b,\\
Q(a,b,c)&=a^{\mathsf T}\otimes b\otimes c^{\mathsf T}.
\end{aligned}
\tag{62.39}
$$

两个单位均保留，两个准备的迹张量等距性也可由转置保持迹配对直接验证。$J(a)=a^{\mathsf T}\otimes I_n$、$H(d)=d\otimes I_n$，故其指定伴随为 $r=T\operatorname{Tr}_2$、$h=\operatorname{Tr}_3$。于是

$$
\begin{aligned}
rM(a,b)&=\operatorname{Tr}(b)a,\\
hL(d,c)&=\operatorname{Tr}(c^{\mathsf T})d=\operatorname{Tr}(c)d,\\
pQ(a,b,c)&=\operatorname{Tr}(a)(b^{\mathsf T}\otimes c)
 =\operatorname{Tr}(a)M(b,c).
\end{aligned}
\tag{62.40}
$$

这逐项验证所有实输入的 (I)、(III) 及完整 (II)，而非只在正乘积上验证；$H(d)=d\otimes I_n$ 也直接给出 $H^*H=n\,\mathrm{id}_D$，故满足 W。

由 (62.24) 的唯一线性定义，插入满足

$$
I_{13}(a^{\mathsf T}\otimes c)
 =a^{\mathsf T}\otimes I_n\otimes c^{\mathsf T}.
\tag{62.41}
$$

因此它先对 $D$ 的第二个因子作部分转置，再把两个标签置于第一、第三位置并插入中间的未归一化单位。它保单位，而且在每个准备的正乘积上正，却不在整个 $D_+$ 上正。令

$$
|\Omega\rangle=\frac1{\sqrt n}\sum_{j=0}^{n-1}|j,j\rangle,
\qquad \rho=|\Omega\rangle\langle\Omega|\ge0,
\qquad (\mathrm{id}\otimes T)\rho=\frac Fn,
\tag{62.42}
$$

其中 $F|i,j\rangle=|j,i\rangle$。把中间单位插入，得到 $I_{13}(\rho)=F_{13}/n$；这里 $F_{13}$ 交换第一、第三因子且在中间因子上为恒等。对任意中间基向量 $|k\rangle$，

$$
v_k=\frac{|0,k,1\rangle-|1,k,0\rangle}{\sqrt2},\qquad
I_{13}(\rho)v_k=-\frac1n v_k.
\tag{62.43}
$$

所以 (62.25) 失败，$n=2$ 时负本征值恰为 $-1/2$。此控制例证明这个二映射表示必须保留该整锥条件，不能用乘积正性替代；它没有证明每个其他条件独立。原始条件只要求全域正性，不能另加完全正性来排除此例，再称已从原条件推出结论。

对 W 的控制取经典 $A=\mathbb R^2,D=\mathbb R^4,E=\mathbb R^8$，均用坐标正锥、坐标和迹及全态全效应。令

$$
P=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix},\qquad
L(d,c)=((P\otimes\mathrm{id})d)\otimes c,\qquad
p=\operatorname{Tr}_1.
\tag{62.44}
$$

$P$ 双随机且可逆，故 $L,p$ 全域正、$p$ 保迹，两条实张成成立。经典纯态为坐标本原元，比较为坐标配对，故有限混合 S 及标准迹 Jordan 桥成立。直接算得 $B(d,c)=(\operatorname{Tr}_1d)\otimes c$，$\omega=1_4/4$，$B(\omega,a)=(1_2/2)\otimes a$，从而两次同一个 $p$ 给出 $M(a,b)=a\otimes b$。于是 $r=\operatorname{Tr}_2$，I 成立；$Q(a,b,c)=Pa\otimes b\otimes c$ 给出 III。插入在全部实简单张量上为

$$
I_{13}(a\otimes c)=Pa\otimes1_2\otimes c,
\qquad (I_{13}d)_{ijk}=\sum_\ell P_{i\ell}d_{\ell k}.
\tag{62.45}
$$

后式逐坐标非负，验证整个经典 $D_+$ 上的 (62.25)，不仅是乘积上正。然而

$$
\begin{gathered}
P^{\mathsf T}P=P^2=
\begin{pmatrix}5/8&3/8\\3/8&5/8\end{pmatrix}\ne\mathrm{id},\\
H^*H=2(P^{\mathsf T}P\otimes\mathrm{id})\ne2\,\mathrm{id}_D,\qquad
hL(d,c)=\tau_A(c)(P^{\mathsf T}P\otimes\mathrm{id})d.
\end{gathered}
\tag{62.46}
$$

例如对坐标基 $e_0,e_1$，取 $d=e_0\otimes e_0,c=e_0$，末式为 $\tfrac58e_0\otimes e_0+\tfrac38e_1\otimes e_0\ne d$。故删除 W 会丢失比较校准，不能推出 II；这两个控制不声称全部条件独立或最小。$\square$

**定理 62.7（条件性复量子几何与同一三份载体）。** 在定义 62.1–62.4 的完整条件下，复用定理 62.5 所接回的既有三映射纸面表示，得到同一实际 $A,D,E$ 上固定的保迹 Jordan 序坐标：存在有限非空指标集 $\Lambda$ 和整数 $n_i\ge1$，使

$$
\begin{aligned}
A&\simeq\bigoplus_{i\in\Lambda}\operatorname{Herm}_{n_i}(\mathbb C),\\
D&\simeq\bigoplus_{i,j\in\Lambda}\operatorname{Herm}_{n_in_j}(\mathbb C),\\
E&\simeq\bigoplus_{i,j,k\in\Lambda}\operatorname{Herm}_{n_in_jn_k}(\mathbb C).
\end{aligned}
\tag{62.47}
$$

记这些坐标同构为 $\theta_A,\theta_D,\theta_E$。在同时选定的这些坐标中，准备是普通分块张量，读回是分块部分迹：

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes b_j,&
L(d,c)_{ijk}&=d_{ij}\otimes c_k,\\
(r d)_i&=\sum_j\operatorname{Tr}_2d_{ij},&
(h z)_{ij}&=\sum_k\operatorname{Tr}_3z_{ijk},\\
(p z)_{jk}&=\sum_i\operatorname{Tr}_1z_{ijk},&
(p_{13}z)_{ik}&=\sum_j\operatorname{Tr}_2z_{ijk}.
\end{aligned}
\tag{62.48}
$$

$L$ 的坐标公式包括整个实际 $D$ 上的实向量及纠缠正向量。局部态、效应与 Born 读数为

$$
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,
\qquad 0\le F_i\le I_{n_i},\qquad
\Pr(F\mid\rho)=\sum_i\operatorname{Tr}(F_i\rho_i).
\tag{62.49}
$$

纯态分支是 $\mathbb{CP}^{n_i-1}$，同扇区比较为 $\operatorname{Tr}(\xi\eta)=|\langle\psi,\phi\rangle|^2$，异扇区比较为零；$n_i=2$ 的态基底是 Bloch 球，$n_i=1$ 的标量扇区仍在。单扇区非经典选择需要另外的条件。

**证明。** 定理 62.5 已在不改变实际 $L,p$ 的前提下建立旧条件的全部前提。故直接应用 Library「Three primitive maps and the forced missing pair view」到「One actual triple and three positive pair views」的表示 (29)–(30)，得到 (62.47)–(62.48)；同条目「Complete finite comparison candidate and quantum correspondence」给出 (62.49) 及纯态、比较和扇区解释。这里没有新的分类步骤。

只在该结果之后，依 Library「Construct the other bracket and all three-label changes」(36)，在同一个 $E$ 上选择右准备

$$
\mu_R(a,d)=\theta_E^{-1}\bigl(\theta_A(a)\otimes\theta_D(d)\bigr),
\qquad \mu_R(a,M(b,c))=Q(a,b,c).
\tag{62.50}
$$

它对全部 $A_+\times D_+$ 正且实张成。同一实三张量空间的两种括号按典范向量空间结合识别后，左右嵌套线性化均为 $\mathcal Q$，所以所选重括号在 $E$ 上为恒等。又可定义

$$
P_\sigma=\mathcal Q\,\tau_\sigma\,\mathcal Q^{-1},\qquad
P_\sigma P_\pi=P_{\sigma\pi}\quad(\sigma,\pi\in S_3),
\tag{62.51}
$$

其中 $\tau_\sigma$ 为三个 $A$ 标签的普通置换。在 (62.47) 坐标中，它们是扇区及矩阵因子的普通置换，故为保迹序自同构。它们是所得表示上的构造，不是此前另给的独立右载体或旁观置换条件。

上述实乘积张成不等于两两边缘层析。既有三量子比特实例的

$$
|G_\pm\rangle=\frac{|000\rangle\pm|111\rangle}{\sqrt2}
\tag{62.52}
$$

给出两个不同的正迹一态，但三个两两约化态都相同，均为对应基中的 $\tfrac12(|00\rangle\langle00|+|11\rangle\langle11|)$。故读回映射的唯一性不意味着任意三份态可从三条两两边缘唯一恢复。$\square$

**定义 62.8（完整条件与解释范围）。** 这个候选只给实双线性 $L$ 与实线性 $p$ 两个原始映射，但完整保留三个实际非零有限维、全态全效应载体上的有限混合比较律 S、保归一化的标准迹 Jordan 条件桥、每扇区本原迹一、$L$ 在全部 $D_+\times A_+$ 上正、$p$ 在全部 $E_+$ 上正且保迹、两次同一个 $p$ 定义的 $M$ 与 $L$ 的两条实张成、I、W、III 的全部实向量律，以及在等距性建立之后良定义的 $I_{13}$ 对整个 $D_+$ 的正性。在这些条件及明确引用的二元、三映射纸面接口下，先由 W 推出完整 II、单位、所需边缘保迹和张量等距性，$I_{13}^*$ 严格且唯一恢复旧 $p_{13}$，两种内部准备逐点相同，继而得到含经典扇区的复量子几何、Born 概率、普通分块张量与同一三份载体上的标签及括号交换；Bell 部分转置例满足 W 却违反整锥插入正性，经典模糊例满足插入正性却违反 W；两条件仍各自保留。未归一化 $H$ 将比较配对乘以 $n$，正保迹的归一化插入 $H/n$ 将它乘以 $1/n$；这不是独立或最少公理的结论。

端点比较的双方互换、标签置换和括号交换，均不等于测量时间顺序互换，也不产生任意不相容测量的共同经典联合结果律。这里的结论范围是有限、静态、全域有序几何及其条件性表示；没有从 $\omega$、辅助 $C$ 或插入映射推出物理准备、滤波、参考装置的可用性或成本。完全正性、仪器、态更新、动力学、时钟、Hamiltonian、$\hbar$、无限维延拓以及四份或无界份数的一致性均不在所证结论内。定理 62.3 的 W 与完整 II 等价及定理 62.5 的严格表示，是本仓在已指明纸面接口下的综合推导；标准谱支撑与范数事实是已知中间成分，二元接口、既有三映射表示和二次表示事实各保留其原有数学引文范围，不是新的已发表分类，也不据此主张文献优先性。

## 追加锚（本行以下为增补区）

## 63. 两个单位切片与完整读回律

**定义 63.1（全载体入口与两切片条件）。** 对每个实际非零有限全态全效应载体 $X=A,D,E$，保留定义 62.1 的整个有序空间、全态基底和全部对偶效应，以及其有限混合律 S：

$$
T_\xi(x)=\inf\{f(x):0\le f\le u_X,\ f(\xi)=1\},\qquad
T_\xi\!\left(\sum_\ell w_\ell\eta_\ell\right)
 =\sum_\ell w_\ell T_{\eta_\ell}(\xi)
\tag{63.1}
$$

对每个纯态 $\xi$、每个有限纯态族 $(\eta_\ell)$ 和每个概率权重族 $(w_\ell)$ 成立。对三个实际载体分别另保留定义 62.1 引用的保归一化 S 到标准迹 Jordan 纸面桥；S 本身不替代该桥。桥后取实际有限 EJA 的整个平方锥、全部正迹一态及全部效应 $[0,1_X]$，每个扇区的每个本原幂等元迹一，并用未变的标准迹配对。记

$$
\langle x,y\rangle_X=\tau_X(x\circ y),\qquad
n=\tau_A(1_A),\quad m=\tau_D(1_D),\quad e=1_A/n,\quad\omega=1_D/m.
\tag{63.2}
$$

只给实双线性 $L:D\times A\to E$ 与实线性 $p:E\to D$，要求 $L(D_+,A_+)\subseteq E_+$、$p(E_+)\subseteq D_+$ 和 $\tau_Dp=\tau_E$。$L$ 的量词包括全部纠缠 $d\in D_+$，$p$ 的保迹律在整个实空间成立。沿用同一个 $p$ 的内部定义：

$$
\begin{aligned}
B(d,c)&=pL(d,c),& M(a,b)&=B(B(\omega,a),b),\\
Q(a,b,c)&=L(M(a,b),c),&J(a)&=M(a,1_A),&r&=J^*,\\
H(d)&=L(d,1_A),&h&=H^*.
\end{aligned}
\tag{63.3}
$$

$J,H$ 均插入未归一化的 $1_A$。两条实张成与全部实方向的三条律为

$$
\begin{gathered}
\operatorname{span}_{\mathbb R}M(A,A)=D,\qquad
\operatorname{span}_{\mathbb R}L(D,A)=E,\\
\mathrm{(W_J)}\quad J^*J=n\,\mathrm{id}_A,\qquad
\mathrm{(W_H)}\quad H^*H=n\,\mathrm{id}_D,\\
\mathrm{(III)}\quad pQ(a,b,c)=\tau_A(a)M(b,c)\quad(a,b,c\in A).
\end{gathered}
\tag{63.4}
$$

这把 (62.6) 中完整 I 换成其 $b=1_A$ 切片 $W_J$，并保留原 W 为 $W_H$；两切片的配对律都量化于所有实向量，包括迹零方向。没有另给 $r,s,h$ 保迹、联合效应律、CP、右载体或迹规范变换；实张成不表示可分离性。定义 63.1 暂不使用 $I_{13}$，其良定义与完整候选的附加条件见定理 63.3。

**定理 63.2（第一切片恢复完整 I）。** 定义 63.1 的条件及定义 62.1 引用的二元边缘纸面接口 (15)–(18) 推出

$$
\begin{gathered}
U:=M(1_A,1_A)=1_D,\qquad m=n^2,\\
s:=r\,pL(\mathord\cdot,e):D\to A\text{ 在整个正锥上正},\\
\mathrm{(I)}\quad rM(a,b)=\tau_A(b)a,\qquad
sM(a,b)=\tau_A(a)b\quad(a,b\in A),\\
\tau_Ar=\tau_D=\tau_As,\qquad
\mathcal M(a\otimes b):=M(a,b)
\text{ 是 }A\otimes_{\mathbb R}A\to D\text{ 的满迹内积等距同构}.
\end{gathered}
\tag{63.5}
$$

这一步不使用 $W_H$、$p$ 保迹、$L$ 的 $E$ 张成或交叉插入正性；它们继续保留在完整候选中。

**证明。** （一）$B,M,J$ 正，平方锥自对偶使 $r=J^*$ 正。$W_J$ 给出 $rM(b,e)=b$，所以 III 给出正映射 $s$ 的全部实向量律及其线性扩展：

$$
sM(a,b)=\tau_A(a)b,\qquad
B(d,c)=M(sd,c)\quad(d\in D,c\in A).
\tag{63.6}
$$

第二式在 $d=M(a,b)$ 上由 III 成立，再用 $M$ 实张成。把它代入确切的两次同一个 $p$ 定义，得到

$$
\begin{aligned}
M(a,b)&=M\bigl(sM(s\omega,a),b\bigr)
       =\tau_A(s\omega)M(a,b),\\
\tau_A(s\omega)&=1,\qquad
V:=s^*1_A\ge0,\qquad \tau_D(V)=m.
\end{aligned}
\tag{63.7}
$$

$D\ne0$ 和 $M$ 张成保证存在非零乘积，故第二行合法。这只是一个标量迹平衡，尚不是 $V=1_D$。对正 $a\le\lambda1_A,b\le\mu1_A$ 有 $0\le M(a,b)\le\lambda\mu U$；正元若与 $U$ 正交，就消去所有正乘积，再由锥生成性与实张成消去整个 $D$。零谱值将产生这样的非零正元，故 $U$ 为内点。而 $W_J$ 给出 $\tau_D(U^2)=\langle1_A,J^*J1_A\rangle_A=n^2$。

（二）写 $\ell_x(y)=x\circ y$ 和标准二次表示 $P_x=2\ell_x^2-\ell_{x^2}$，置

$$
C=P_{\sqrt U},\quad C^{-1}=P_{U^{-1/2}},\qquad
F=C^{-1}M,\quad R=sC,\quad
\alpha(a)=F(a,1_A),\quad\beta(b)=F(1_A,b).
\tag{63.8}
$$

此处 $F=C^{-1}M$，不同于 (62.13) 的 $\widehat M=CM$；不改变标准迹。所用二次表示正性正是 (62.11) 引用的 [van de Wetering, Propositions 2.21、2.25](https://arxiv.org/html/1912.01903v1#S2.counter21)，公式采用该文引言的 $P_x$。在对角化 $U$ 的本原框架中，$C$ 的对角与非对角 Peirce 系数分别为 $u_i$、$\sqrt{u_iu_j}$，$u_i>0$；显示的逆取倒数。迹形式结合性使两者自伴随，二次表示正性使两者全锥正，且

$$
C1_D=U,\quad C^{-1}U=1_D,\quad C^{-1}1_D=U^{-1},\qquad
F(1_A,1_A)=1_D,\quad RF(a,b)=\tau_A(a)b.
\tag{63.9}
$$

$F$ 正双线性且实张成 $D$，$R$ 正，$\alpha,\beta$ 正且保单位；尚未断言 $F$ 等距或 $R$ 保迹。上述谱与支撑事实均包括例外 EJA 和直和。

（三）取 $A$ 的任意完整本原框架 $(q_i)$。由 $W_J$，正元 $x_i=Jq_i$ 两两迹正交，故其支撑 $c_i$ 为正交幂等元，和为 $1_D$，因为 $\sum_i x_i=U$ 为内点；支撑规则见 (62.18) 或二元接口 (19)。在 $D_1(c_i)$ 上 $U$ 就是 $x_i$，由同一 Peirce 系数计算得

$$
C^{-1}x_i=c_i,\qquad \alpha(q_i)=c_i.
\tag{63.10}
$$

因此谱展开给出 $\alpha(a^2)=\alpha(a)^2$，极化使 $\alpha$ 为保单位 Jordan 同态。它单射，因为 $J^*J=n\,\mathrm{id}_A$ 且 $C$ 可逆。对 $b\ge0$，取 $b\le\lambda1_A$，则 $0\le F(q_i,b)\le\lambda c_i$，故 $F(q_i,b)\in D_1(c_i)$。于是 $\beta(b)=\sum_iF(q_i,b)$ 在这些支撑块上对角，并有

$$
F(q_i,b)=c_i\circ\beta(b),\qquad
F(a,b)=\alpha(a)\circ\beta(b),\qquad
[\ell_{\alpha(a)},\ell_{\beta(b)}]=0\quad(a,b\in A).
\tag{63.11}
$$

最后两式由谱展开及实线性延拓。这里是整个 $D$ 上的算子交换：对每个 $c_i$，块内元素及其他正交块内元素的乘法都保持 $D_1(c_i),D_{1/2}(c_i),D_0(c_i)$，由 Peirce 乘法规则使 $\ell_{\beta(b)}$ 与 $\ell_{c_i}$ 交换，再对 $\alpha(a)=\sum_i\lambda_i c_i$ 线性组合。这不是只在所生成子代数内交换；亦可用上述主文 Proposition 2.12 的幂等元判据。没有用特殊 Jordan 矩阵嵌入，也尚未假定 $\beta$ 保平方。

（四）对任意本原 $q\in A$，令 $c=\alpha(q)$。由同态性和 (63.11)，$P_c=2\ell_c^2-\ell_c$ 与 $\ell_{\beta(b)}$ 交换，故

$$
\begin{aligned}
P_{\alpha(q)}F(a,b)&=F(P_q a,b),&P_q a&=\langle q,a\rangle_Aq,\\
R_q&:=R P_{\alpha(q)}:D\to A,&
R_qF(a,b)&=\langle q,a\rangle_A b.
\end{aligned}
\tag{63.12}
$$

第一式还用了 $P_c\alpha(a)=\alpha(P_q a)$；本原性使 $A_1(q)=\mathbb Rq$，而正交 Peirce 投影 $P_q$ 因 $\|q\|^2=1$ 有显示形状。二次表示正性使 $R_q$ 在整个 $D_+$ 上正。设 $\mathcal F:A\otimes_{\mathbb R}A\to D$ 线性化 $F$。若 $\mathcal Fz=0$，则对所有本原 $q$ 及所有实 $g\in A$，

$$
\langle q\otimes g,z\rangle
 =\langle R_q^*g,\mathcal Fz\rangle_D=0.
\tag{63.13}
$$

本原元实张成 $A$，所以 $z=0$。$F$ 张成给出满射；至此才第一次得到张量逆，未从张成直接跳到单射。

（五）现在定义对偶准备，且保留所有原标准迹：

$$
N(f,g)=(\mathcal F^*)^{-1}(f\otimes g),\qquad
\langle N(f,g),F(a,b)\rangle_D
 =\langle f,a\rangle_A\langle g,b\rangle_A.
\tag{63.14}
$$

(63.12) 和非退化配对给出 $N(q,g)=R_q^*g$，故本原 $q$ 与任意 $g\ge0$ 给出正向量；对正 $f$ 作本原谱展开，得到 $N(A_+,A_+)\subseteq D_+$。其线性化可逆，因而 $N$ 实张成 $D$。$\alpha,\beta$ 正且保单位，使 $\alpha^*,\beta^*$ 全锥正且标准保迹。由 $\alpha(a)=F(a,1_A)$、$\beta(b)=F(1_A,b)$ 及 (63.14)，对全部实 $f,g$ 有

$$
\alpha^*N(f,g)=\tau_A(g)f,\qquad
\beta^*N(f,g)=\tau_A(f)g.
\tag{63.15}
$$

这恰好满足 Library「Positive marginals recover the joint-effect contract」(15) 的每一项：实际标准迹 EJA、全域正双线性准备、实张成、两个全锥正保迹边缘及全部实向量丢弃律。此时才把其 (16)–(18) 用于 $(N,\alpha^*,\beta^*)$，在没有 $r,s$ 保迹前得到 $\mathcal N$ 为满等距同构、$N(1_A,1_A)=1_D$ 及 $m=n^2$。因

$$
\mathcal N=(\mathcal F^*)^{-1},\qquad
\mathcal F=(\mathcal N^*)^{-1}=\mathcal N,
\tag{63.16}
$$

$F=N$，$\mathcal F$ 也是满等距同构，(63.15) 同时成为 $F$ 的两条普通边缘律。这仅用接口已经给出的等距性，不额外假定其乘积公式。

（六）(63.9)、(63.15) 和 $F$ 张成给出 $R=\beta^*$。因此

$$
CV=R^*1_A=\beta(1_A)=1_D,\qquad V=U^{-1}.
\tag{63.17}
$$

(63.7) 及 $W_J$ 已分别给出 $\tau_D(U^{-1})=m$、$\tau_D(U^2)=n^2=m$。对 $U$ 的完整本原谱框架，恰有 $m$ 个正谱值 $\lambda_k$，包括各扇区。于是

$$
\begin{aligned}
0&=\sum_{k=1}^{m}\bigl(\lambda_k^2+2/\lambda_k-3\bigr),\\
\lambda^2+2/\lambda-3
 &=\frac{(\lambda-1)^2(\lambda+2)}{\lambda}\ge0
 \quad(\lambda>0).
\end{aligned}
\tag{63.18}
$$

每项必须为零，故 $U=1_D$、$C=\mathrm{id}_D$、$M=F=N$。又 $J=\alpha$，故 $r=\alpha^*$、$s=\beta^*$，(63.15) 给出完整 I、第二边缘律及保迹性，得到 (63.5)。恢复的缺失条件是完整 I 及其所需归一化：其中 $V$ 的迹平衡来自同一个 $p$ 的内部一致性，不能提前把它当成 $V=1_D$。$\square$

**定理 63.3（完整候选与同一实际数据的严格等价）。** 定义 63.1 与二元纸面接口先推出完整 II、$h$ 正保迹、$L(1_D,1_A)=1_E$ 及 (62.8) 的 $\mathcal L,\mathcal Q$ 满迹等距。仅在已证明 $\mathcal M$ 可逆后定义

$$
\begin{aligned}
T(a,c)&=L(M(a,1_A),c),&\mathcal T&:A\otimes_{\mathbb R}A\to E,\\
\mathcal T(a\otimes c)&=T(a,c),& I_{13}&=\mathcal T\mathcal M^{-1}:D\to E.
\end{aligned}
\tag{63.19}
$$

完整两切片候选在上述前置条件外明确保留

$$
I_{13}(D_+)\subseteq E_+\quad\text{在整个实际正锥上}.
\tag{63.20}
$$

它与定义 62.1–62.4 的完整候选在同一实际 $A,D,E,L,p$ 上逐点等价，并与定理 62.5 的旧三映射条件严格唯一扩张等价。唯一补入的读回是 $p_{13}=I_{13}^*$；它全锥正保迹，且旧混合内部准备逐点恢复为

$$
p_{13}Q(a,b,c)=\tau_A(b)M(a,c),\qquad
pL\bigl(p_{13}L(\omega,a),b\bigr)=M(a,b).
\tag{63.21}
$$

**证明。** 定理 63.2 先建立完整 I，定义 63.1 原已给 $W_H$、III、两条实张成、全域正性及原始 $p$ 的标准保迹性。故定义 62.2 的全部前提此时齐备，才调用定理 62.3：其 $s$ 正是 (63.5) 的定义，完整 II、$h,t=sp$ 保迹、单位及等距结论全部适用，无需再作支撑或分类证明。

现在 (63.19) 恰为 (62.24)，类型与逆相同；(63.20) 恰为 (62.25)，尚未由两切片推出。补入它后，定理 62.5 直接给出 (63.21)、$p_{13}$ 唯一性和两种内部准备相等。反向从完整第 62 节条件出发，I 在 $b=1_A$ 给出 $J^*J=n\,\mathrm{id}_A$，其 W 就是 $W_H$；其他数据与条件原样保留，故得到完整两切片条件。从旧三映射条件出发，定理 62.5 已证明忘去与补入在同一 $L,p$ 上互逆，并恢复两次同一个 $p$ 的 $M$，再取 I 的切片即可。因而等价保持实际数据，而非仅保持存在性或表示同构类。

由同一次定理 62.3，未归一化插入 $J,H$ 的比较配对因子均为 $n$；正保迹的 $J/n=M(\mathord\cdot,e)$、$H/n=L(\mathord\cdot,e)$ 的配对因子均为 $1/n$。不把这两个因子交换，也不改变原始 $p$ 的全局保迹条件。$\square$

**命题 63.4（保留条件的控制）。** 定理 62.6 的 Bell 部分转置例满足 $W_J,W_H$，却违反 (63.20)；其经典模糊例满足 $W_J$ 与 (63.20)，却违反 $W_H$ 和完整 II。

**证明。** 严格采用 (62.38)–(62.43) 的方向：$L(d,c)=d\otimes c^{\mathsf T}$、$M(a,b)=a^{\mathsf T}\otimes b$，$p=T_D\operatorname{Tr}_1$。它已有完整 I 和 $W_H$，故取 I 的 $b=1_A$ 即得 $W_J$；相同插入在 Bell 态上有负本征值 $-1/n$。经典例 (62.44)–(62.46) 有 $M(a,b)=a\otimes b$，所以 $J^*J=2\,\mathrm{id}_A$；其余断言正是该例的全锥插入公式和 $H^*H\ne2\,\mathrm{id}_D$。这些控制没有声称 $W_J$ 的独立性，也不声称全部条件最少。$\square$

**定理 63.5（几何与解释范围）。** 在定理 63.3 的完整条件下，复用定理 62.7，得到同一实际数据的保迹 Jordan 序坐标

$$
A\simeq\bigoplus_i\operatorname{Herm}_{n_i}(\mathbb C),\qquad
D\simeq\bigoplus_{i,j}\operatorname{Herm}_{n_in_j}(\mathbb C),\qquad
E\simeq\bigoplus_{i,j,k}\operatorname{Herm}_{n_in_jn_k}(\mathbb C),\quad n_i\ge1,
\tag{63.22}
$$

指标集有限非空。相同实际 $M,L,p$ 与派生读回由 (62.48) 给出普通分块张量及部分迹，$L$ 的公式覆盖全部纠缠输入。全态、全效应、Born 概率和纯态分支分别为

$$
\rho_i\ge0,\quad\sum_i\operatorname{Tr}\rho_i=1,\quad
0\le F_i\le I_{n_i},\quad
\Pr(F\mid\rho)=\sum_i\operatorname{Tr}(F_i\rho_i),\qquad
P_A=\coprod_i\mathbb{CP}^{n_i-1}.
\tag{63.23}
$$

同扇区纯态比较是 $\operatorname{Tr}(\xi\eta)=|\langle\psi,\phi\rangle|^2$，异扇区为零；经典标量扇区仍保留，选择单扇区需要额外条件。

**证明。** 定理 63.3 已建立第 62 节的全部完整前提，故直接应用定理 62.7，不重新分类。只在这些坐标建立后，(62.50)–(62.51) 构造同一个 $E$ 上所选右括号与 $S_3$ 标签作用；不识别一个独立给定的右载体。(62.52) 的两种 GHZ 态仍有相同三个两两边缘，故张成与读回唯一性均不等于成对层析。$\square$

**定义 63.6（纸面条件的含义与边界）。** 对三个实际有限的全态全效应系统，仍分别保留有限混合比较 S 及保归一化 Jordan 条件桥、每扇区本原迹一、全锥正的 $L$ 与全局正保迹的同一个 $p$、两条实张成、全部实方向的 $W_J,W_H,\mathrm{III}$，以及良定义之后的整锥交叉插入正性。在这个完整有限载体入口下，插入数学上的完整单位参考只把比较配对乘以 $n$；相同 $p$ 的内部一致性、正性和这些保留条件足以恢复完整读回律，再接回含经典扇区的复量子几何。这不是单靠数值对称性推出量子理论，也没有把其他条件藏进一句“可比较”中。

标准谱展开、规范迹与本原纯态事实采用 (62.18)–(62.19) 已指明的 [Barnum–Hilgert, Theorem 4.2、Definition 4.3、Proposition 4.4](https://arxiv.org/html/1904.03753v1#S4)；二次表示正性与环境算子交换采用上述 van de Wetering 主文及 Peirce 支撑计算。定理 63.2 的对偶准备归一化和定理 63.3 的组合等价是仓内条件性纸面综合推导；二元接口及整体表示亦为已明确引用的仓内纸面结果，不作为主文的分类定理，不主张新颖性、优先性、独立或最少公理，也不作内核验证声明。

端点双方互换、标签置换与所选括号交换不等于测量时间顺序交换，不提供不相容测量的共同经典联合结果律。数学上的 $\omega,C$ 与单位插入不保证物理装置、参考或滤波的可用性或成本。CP、参考扩张、仪器、态更新、动力学、时钟、Hamiltonian、$\hbar$、独立右载体、无限维、四份及无界份数的一致性仍在结论之外；不声称完整量子起源。

## 追加锚（本行以下为增补区）
