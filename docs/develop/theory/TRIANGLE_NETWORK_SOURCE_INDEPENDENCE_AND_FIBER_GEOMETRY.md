# Triangle Network Source Independence as a Fibered Three-Geometry

**Status.** This is a theory supplement for the Auric FIB geometry and the quantum interface. It records ordinary mathematical definitions and proofs, together with explicit boundaries between inherited results, new interfaces, and open obligations. It does not claim that the triangle network is a physical three-dimensional space, and it does not claim a Lean admission. The target is a common formal carrier for three independent sources, two-source local responses, the trureturing three-coordinate quotient, and noise certificates.

## 0. Main statement

A triangle network has three source edges and three party vertices:

\[
E=\{\alpha,\beta,\gamma\},\qquad V=\{A,B,C\},
\]
\[
I(A)=\{\beta,\gamma\},\qquad I(B)=\{\gamma,\alpha\},\qquad I(C)=\{\alpha,\beta\}.
\]

The word three has three different meanings that must be kept separate.

1. There are three independent edge sources.
2. A finite observation may have three retained coordinates, such as the Auric FIB quotient \((X,Y,Z)\).
3. A nonzero fully \(SO(3)\)-invariant alternating response is three-dimensional under the explicit hypotheses of the stable-relation volume.

Only the third item is a dimension theorem, and it is conditional on a supplied real positive-definite metric, a nonzero trilinear response, and full simultaneous \(SO(V,g)\)-invariance. Source count alone does not imply a spatial dimension.

The useful common object is therefore a **fibered incidence geometry**:

\[
\text{independent edge measure}
\longrightarrow
\text{two-edge local response}
\longrightarrow
\text{observed quotient}
\]

with a hidden gluing fiber above the quotient. In the five-mode Auric FIB carrier, the quotient is \((X,Y,Z)\), while \(\kappa\) is the residual two-edge coupling. In the triangle network, source independence is a separate product constraint on \((\alpha,\beta,\gamma)\). The two constraints are related by the incidence map, but they are not the same equation.

## 1. The exact triangle-local carrier

Let \(\Omega_\alpha,\Omega_\beta,\Omega_\gamma\) be standard Borel source spaces with probability measures \(\mu_\alpha,\mu_\beta,\mu_\gamma\). A classical triangle model consists of the product measure

\[
\mu=\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma
\]

and three stochastic response kernels

\[
A(a\mid\beta,\gamma),\qquad
B(b\mid\gamma,\alpha),\qquad
C(c\mid\alpha,\beta).
\]

For every output triple,

\[
P(a,b,c)=
\int_{\Omega_\alpha\times\Omega_\beta\times\Omega_\gamma}
A(a\mid\beta,\gamma)
B(b\mid\gamma,\alpha)
C(c\mid\alpha,\beta)\,d\mu.
\tag{1.1}
\]

The triangle-local set \(\mathcal L_\triangle\) is the set of all finite-output distributions admitting (1.1). The response kernels may contain local private randomness. Such randomness can be represented by additional independent local seeds and absorbed into the kernels. It must not be replaced by a common selector shared by the three parties.

For finite source alphabets the same object is a multilinear contraction. If the source probabilities are \(r_\alpha,r_\beta,r_\gamma\), then

\[
P(a,b,c)=
\sum_{\alpha,\beta,\gamma}
r_\alpha r_\beta r_\gamma
A_{a\mid\beta\gamma}
B_{b\mid\gamma\alpha}
C_{c\mid\alpha\beta}.
\tag{1.2}
\]

This tensor form explains the geometry. The source point is a product point in the three source simplices. The response map is multilinear in the three edge measures. The image is generally non-convex.

### Proposition 1.1: source independence is not observed-party independence

The product law implies

\[
I(\alpha:\beta:\gamma)=0,
\]

where the total correlation is

\[
I(\alpha:\beta:\gamma)
=
D\!\left(
\mu_{\alpha\beta\gamma}
\middle\|
\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma
\right).
\]

It does not imply \(A\), \(B\), and \(C\) are independent. Alice and Bob share \(\gamma\), Alice and Charlie share \(\beta\), and Bob and Charlie share \(\alpha\). The observed outputs can therefore be strongly correlated even though the three sources are mutually independent.

**Proof.** The first assertion is the defining product condition. The second follows because, for example, \(A\) and \(B\) are both functions of \(\gamma\), in addition to their other inputs. A common edge is enough to create output correlation. No common tripartite source is required. ∎

### Proposition 1.2: why source-product mixtures need a separate lift

Let \(P\) and \(P'\) be triangle-local with source products \(\mu_\alpha\mu_\beta\mu_\gamma\) and \(\mu'_\alpha\mu'_\beta\mu'_\gamma\). The mixture

\[
tP+(1-t)P'
\tag{1.3}
\]

has the evident hidden representation

\[
t\,\mu_\alpha\mu_\beta\mu_\gamma
+
(1-t)\,\mu'_\alpha\mu'_\beta\mu'_\gamma.
\]

The evident implementation uses one shared selector \(S\) to choose between the two entire models. Giving \(S\) to every edge generally correlates the augmented edge variables \((S,\alpha)\), \((S,\beta)\), and \((S,\gamma)\), violating their independence. Independent selectors preserve a product law but generally introduce cross terms instead of the desired two-term mixture. Therefore this construction does not establish triangle locality of the mixture; a different local representation might still exist.

This is the precise point where the Bell-hyperplane intuition breaks. In an ordinary Bell scenario, convex mixtures can be implemented by a shared hidden selector because one source already connects the relevant parties. In the triangle scenario, a selector shared by all three edge sources is an additional common ancestor and changes the causal graph.

## 2. The trureturing five-mode quotient

The existing Auric FIB pyramid uses five modes

\[
\Sigma=\{0,2,5,25,3\}
\]

with binary features \(x,y,z\) satisfying \(xz=yz=0\). A probability law is written

\[
p=(p_0,p_2,p_5,p_{25},p_3).
\]

The retained coordinates and the hidden fiber coordinate are

\[
X=\mathbb E[x],\qquad
Y=\mathbb E[y],\qquad
Z=\mathbb E[z],\qquad
\kappa=\mathbb E[xy].
\tag{2.1}
\]

The probability reconstruction is exact:

\[
p_{25}=\kappa,\quad
p_2=X-\kappa,\quad
p_5=Y-\kappa,\quad
p_3=Z,\quad
p_0=1-X-Y-Z+\kappa.
\tag{2.2}
\]

The quotient \((X,Y,Z)\) is the five-vertex pyramid. For a fixed quotient point, the complete legal fiber is

\[
\max(0,X+Y+Z-1)
\le \kappa \le
\min(X,Y).
\tag{2.3}
\]

Its width is

\[
\Delta_\kappa
=
\min\{X,Y,1-X-Z,1-Y-Z\}.
\tag{2.4}
\]

These formulas are inherited from AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md and AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md. They are an ordinary finite probability calculation, not a quantum-network theorem.

### Proposition 2.1: the FIB conditional-independence surface

Assume \(Z<1\), so that the event \(z=0\) has positive probability. On that event, the two features \(x\) and \(y\) are conditionally independent exactly when

\[
\Delta_{\mathrm{FIB}}
:=
(1-Z)\kappa-XY
=0.
\tag{2.5}
\]

**Proof.** Since \(P(z=0)=1-Z\),

\[
P(x=1\mid z=0)=\frac{X}{1-Z},\quad
P(y=1\mid z=0)=\frac{Y}{1-Z},\quad
P(x=y=1\mid z=0)=\frac{\kappa}{1-Z}.
\]

The equality of the last expression with the product of the first two is exactly (2.5). If \(Z=1\), the conditioning event has probability zero: the polynomial equation still vanishes, but does not define a conditional-independence claim. ∎

The equation \(\Delta_{\mathrm{FIB}}=0\) is a local two-feature conditional-independence relation. It is not the triangle source condition

\[
\mu_{\alpha\beta\gamma}
=
\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma.
\tag{2.6}
\]

The former concerns two features after a conditioning event. The latter concerns three hidden edge variables before the response map. Confusing them would identify a visible response fiber with the causal source layer.

### Proposition 2.2: the fiber-blind statistic

For a function \(f:\Sigma\to\mathbb R\), define

\[
J_f=f_{25}-f_2-f_5+f_0.
\tag{2.7}
\]

Then, at fixed \((X,Y,Z)\),

\[
\mathbb E_p[f]
=
f_0+(f_2-f_0)X+(f_5-f_0)Y+(f_3-f_0)Z+J_f\kappa.
\tag{2.8}
\]

Consequently, \(\mathbb E_p[f]\) is constant on every non-degenerate \(\kappa\)-fiber if and only if \(J_f=0\).

**Proof.** Substitute (2.2) into \(\sum_s p_s f_s\). The coefficient of \(\kappa\) is exactly (2.7). ∎

This is a fiber-blindness statement for the five-mode FIB carrier. Any statistic with \(J_f=0\) factors through the three-coordinate quotient. It cannot see the hidden joint coupling \(\kappa\), even though two laws with the same \((X,Y,Z)\) can have different full distributions and different continuation behavior. Applying this statement to a triangle distribution requires a specified readout \(\Phi\) relating its events to the FIB carrier. A triangle-locality test must retain sufficient data for the edge-incidence constraints; the FIB fiber identity alone supplies no source-independence criterion.


### Proposition 2.3: the product completion and the information action

Write \(r=1-Z\) and form the bottom conditional table

\[
Q=
\begin{pmatrix}
r-X-Y+\kappa&Y-\kappa\\
X-\kappa&\kappa
\end{pmatrix}.
\]

Its determinant is

\[
\Delta=r\kappa-XY.
\tag{2.9}
\]

When \(r>0\), the unique conditional-product completion with the same \(X,Y,Z\) is

\[
\kappa_*=\frac{XY}{r}.
\tag{2.10}
\]

Under the finite FIB model, the entropy difference satisfies

\[
H(p_*)-H(p)=r\,I(x:y\mid z=0),
\tag{2.11}
\]

and the total-variation difference is

\[
d_{\mathrm{TV}}(p,p_*)
=\frac12\|p-p_*\|_1
=\frac{2|\Delta|}{r},
\qquad
\|p-p_*\|_1=\frac{4|\Delta|}{r}.
\tag{2.12}
\]

These identities provide a useful thermodynamic interpretation of the hidden fiber: \(\Delta\) measures displacement from the maximum-entropy conditional-product section. They do not turn the FIB \((x,y,z)\) variables into the three triangle sources.

Under the mean-field mass-action closure used in the existing information-escape volume, the reversible move \(2+5\rightleftharpoons0+25\) has

\[
\dot\kappa=-\gamma(r\kappa-XY),\qquad
\Delta(t)=\Delta(0)e^{-\gamma r t}.
\tag{2.13}
\]

Thus the hidden coupling decays while the quotient coordinates remain fixed. Near the apex \(r\to0\), the fiber width is \(O(r)\), its admissible determinant is \(O(r^2)\), and the relaxation time \((\gamma r)^{-1}\) diverges. This is an escape bottleneck: the hidden amount is small but slow to resolve. Equation (2.13) is a deterministic closure, not a general quantum channel, Lindblad equation, or theorem about physical source noise. A quantum lift must separately retain coherence, entanglement, and the environment ledger.

## 3. What “three-dimensional” means in the network interface

The triangle incidence matrix has three edge columns and three party rows. Each party sees exactly two columns:

\[
\begin{array}{c|ccc}
 & \alpha & \beta & \gamma\\
\hline
A&0&1&1\\
B&1&0&1\\
C&1&1&0
\end{array}.
\tag{3.1}
\]

This is a three-edge incidence geometry. It is not a coordinate chart for physical space.

The FIB three-axis interface starts with a supplied real positive-definite \(g\), a nonzero trilinear form \(T\), and full simultaneous \(SO(V,g)\)-invariance. Under those hypotheses, the invariant tensor calculation gives

\[
T=0\quad(d\ne3),\qquad
T=c\,\operatorname{vol}_g\quad(d=3).
\tag{3.2}
\]

The associated bilinear response is \(B=c\,\times_g\). The result is a conditional representation theorem for a response interface. It does not follow from the existence of three sources, three parties, or a cycle.

The correct combined interpretation is:

- the network contributes three independent edge slots and two-edge local access;
- the FIB quotient contributes a three-coordinate observable carrier;
- the hidden \(\kappa\)-fiber records information lost by that quotient;
- a full triangle-local model is a lift of the observed carrier that must preserve the product law on the three edges and every unconnected-source invariance;
- an inflation proof is a finite lifted obstruction to such a global lift.

This is the same distinction used elsewhere in the project between a local projection and a future-complete boundary. A valid projection can be geometrically closed and still fail to have a compatible hidden lift.

## 4. Fibered lift and global gluing

Let \(\Phi\) be a specified finite feature map from output events to a FIB mode alphabet, or more generally a linear readout from the observed distribution to a finite coordinate vector. Define the observable projection

\[
\pi_\Phi(P)=(X(P),Y(P),Z(P)).
\]

A **triangle-compatible lift** of an observed point \(q=\pi_\Phi(P)\) is a tuple

\[
(\mu_\alpha,\mu_\beta,\mu_\gamma,A,B,C,\widetilde p)
\]

such that:

1. the source law is the product \(\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma\);
2. the response kernels use only the two incident source variables;
3. the pushforward of the resulting distribution is \(\widetilde p\);
4. \(\pi(\widetilde p)=q\);
5. every required shared-edge marginal and normalization condition is satisfied.

Write \(\operatorname{Lift}_\triangle(q)\) for the set of all such lifts. The observed quotient is locally compatible if \(\operatorname{Lift}_\triangle(q)\ne\varnothing\). A full observed distribution \(P\) is triangle-local exactly when its entire event table, not merely \(q\), has such a lift.

This definition separates two failure modes.

- **Fiber failure:** the quotient point has a legal FIB fiber, but the chosen \(\kappa\) or continuation statistic is incompatible with the claimed local model.
- **Global gluing failure:** every retained local marginal is legal, but there is no one product-source lift satisfying all three party responses simultaneously.

The second is the network analogue of information escaping through a projection. It is also why pairwise or one-party checks cannot certify triangle locality.

### Definition 4.1: source-independence defect

For a candidate hidden law \(\nu_{\alpha\beta\gamma}\), set

\[
\mathfrak d_{\mathrm{src}}(\nu)
=
D\!\left(
\nu_{\alpha\beta\gamma}
\middle\|
\nu_\alpha\otimes\nu_\beta\otimes\nu_\gamma
\right).
\tag{4.1}
\]

It is zero exactly for a product source law. The defect belongs to the hidden lift, not to an arbitrary observed quotient. A visible \(\kappa\)-defect can be nonzero in a perfectly triangle-local model because two outputs share an edge. Conversely, \(\mathfrak d_{\mathrm{src}}=0\) for one selected hidden representation does not by itself prove that the observed distribution has the required response incidence unless the kernels are also supplied.

## 5. Inflation as a discrete covering and obstruction

Inflation replaces each source edge by several copies and each party by copies connected according to the incidence pattern. The resulting graph is a finite cover-like lift of the original causal incidence complex. A triangle-local model induces a distribution on the lifted parties with:

- equal-copy symmetries;
- marginal consistency whenever two lifted events descend to the same original event;
- factorization or d-separation constraints for disjoint source copies;
- the original \(P(a,b,c)\) as an appropriate marginal.

The lifted feasible event vectors form a convex relaxation. The original triangle-local set remains non-convex because the source product structure is still imposed before the response contraction. This explains the apparently paradoxical division of labor:

- the original local set is non-convex;
- an inflation relaxation is a convex polytope or cone;
- an infeasibility certificate is a linear separating cochain for the lifted relaxation;
- a certificate must separate the required target from every lifted deterministic image, not merely be positive on those images.

More precisely, let \(K\) map a lifted law to the coordinates constrained by inflation, and let \(T(P)\) be the target coordinates required by the observed distribution. Soundness must first establish that a triangle-local \(P\) admits a lifted probability law \(q\) with \(K(q)=T(P)\). A linear functional \(f\) certifies infeasibility when

\[
\left\langle f,K(\delta_\omega)-T(P)\right\rangle>0
\quad\text{for every lifted deterministic event }\omega.
\]

Indeed, taking the convex combination with coefficients \(q(\omega)\) would give \(0>0\). Positivity of \(\langle f,K(\delta_\omega)\rangle\) alone is insufficient: the target value must also be compared. For rational maps and targets, clear their denominators by a common positive integer and verify the resulting strict integer inequalities. This is an exact separation certificate, not a floating-point numerical distance.

The 2025 Gitton–Renner EJM result is the canonical example. The EJM distribution has four outcomes per party,

\[
P_{\mathrm{EJM}}(a,b,c)=
\begin{cases}
25/256,&a=b=c,\\
5/256,&a,b,c\text{ all distinct},\\
1/256,&\text{otherwise}.
\end{cases}
\tag{5.1}
\]

A symmetry-reduced inflation with source-copy size \((2,2,4)\), followed by a Frank–Wolfe search and an exact integer certificate, proves that this distribution is outside the classical triangle-local set. The proof is a global gluing obstruction in a lifted event space. It is not a Bell inequality on the original three-party table.

This makes the geometry-to-network map precise: the EJM proof does not merely find a negative coordinate in the three-dimensional quotient. It shows that no globally consistent product-source lift exists after all copied-edge compatibility conditions are imposed.


### 5.1 A concrete three-dimensional EJM encoding

There is an exact geometric encoding of the four EJM outcomes that makes the three-dimensional connection concrete without identifying the network with physical space. Let \(t_0,t_1,t_2,t_3\in\mathbb R^3\) be the unit vectors at the vertices of a regular tetrahedron, so

\[
t_i\cdot t_j=
\begin{cases}
1,&i=j,\\
-1/3,&i\ne j.
\end{cases}
\]

For an output triple \((a,b,c)\), put

\[
d_{ab}=t_a\cdot t_b,\quad
d_{bc}=t_b\cdot t_c,\quad
d_{ca}=t_c\cdot t_a,
\]
\[
S=d_{ab}+d_{bc}+d_{ca},\qquad
R=d_{ab}d_{bc}+d_{bc}d_{ca}+d_{ca}d_{ab}.
\]

Then the exact EJM table (5.1) is the symmetric Gram polynomial

\[
P_{\mathrm{EJM}}(a,b,c)=\frac{4+S+6R}{256}.
\tag{5.2}
\]

The three equality patterns give

\[
\begin{array}{c|c|c|c}
\text{pattern}&S&R&(4+S+6R)/256\\
\hline
a=b=c&3&3&25/256\\
\text{exactly two equal}&1/3&-5/9&1/256\\
a,b,c\text{ all distinct}&-1&1/3&5/256.
\end{array}
\]

Among the 64 ordered output triples, four are all equal, 36 have exactly two equal entries, and 24 are all distinct. Thus every entry is nonnegative and the total mass is

\[
\frac{4\cdot25+36\cdot1+24\cdot5}{256}=1.
\]

The Gram expression therefore specifies an exact rational probability law on the 64 output triples.

This identity is an exact finite calculation. It is a genuine three-dimensional representation of the output symmetry because the four outcomes are encoded by a regular tetrahedron in \(\mathbb R^3\). It is not a proof that the causal sources are spatial axes.

The term \(S\) is a sum of pairwise Gram interactions. The term \(R\) is the symmetric sum of pairwise products among the three edge-pair Gram entries, so it is a cycle-sensitive invariant that still respects the full permutation symmetry of \(a,b,c\). Equivalently,

\[
256P_{\mathrm{EJM}}
=5-4(\delta_{ab}+\delta_{bc}+\delta_{ca})
+32\,\mathbf 1_{\{a=b=c\}}.
\]

The last form makes the three pattern weights transparent; the Gram form makes the regular-tetrahedron, three-dimensional realization transparent. The identification of \(R\) with a physical curvature or holonomy remains a conjectural interpretation. What is proved here is only the polynomial identity (5.2).

The encoding also explains why a purely low-order quotient can be blind. A statistic that retains only one-party means or a single pairwise Gram average can preserve the same \((X,Y,Z)\) while losing the cycle-sensitive \(R\) sector. A global triangle-local test must keep enough lifted data to decide whether the pairwise Gram sectors and the symmetric cycle sector admit one common product-source realization.

## 6. Noise must be typed before it is compared

The phrase “add noise” hides three mathematically different paths.

### 6.1 Global output white-noise proxy

For \(d=d_A d_B d_C\), define

\[
P^{\mathrm{glob}}_v
=
vP+(1-v)U_d,\qquad
U_d(a,b,c)=1/d.
\tag{6.1}
\]

This is an affine radial path in the observed probability simplex. It is useful for exact certificate studies, but it is not generally the same as independently replacing each source by a Werner state or applying detector noise.

### 6.2 Independent source Werner or white noise

For each edge \(e\in\{\alpha,\beta,\gamma\}\), let

\[
\rho_e(w_e)
=
w_e\rho_e+(1-w_e)\frac{I_e}{d_e}.
\]

With fixed local measurements \(M_A,M_B,M_C\),

\[
P_{\mathbf w}
=
\operatorname{Born}\!\left(
\rho_\alpha(w_\alpha)\otimes
\rho_\beta(w_\beta)\otimes
\rho_\gamma(w_\gamma);
M_A,M_B,M_C
\right).
\]

Expanding the tensor product gives

\[
P_{\mathbf w}
=
\sum_{S\subseteq\{\alpha,\beta,\gamma\}}
\left(\prod_{e\in S}w_e\right)
\left(\prod_{e\notin S}(1-w_e)\right)
P_S,
\tag{6.2}
\]

where \(P_S\) is the distribution with ideal state on edges in \(S\) and maximally mixed state on the other edges. This is a multi-affine polynomial in the three source visibilities. It is a mixture of eight quantum distributions, not generally the one-dimensional global line (6.1).

### 6.2.1 Exact finite source-noise application

For eight rational tables \(P_i(a,b,c)\), index the source choices by the binary tuples

\[
0=000,\quad1=100,\quad2=010,\quad3=110,\quad
4=001,\quad5=101,\quad6=011,\quad7=111,
\]

where the tuple order is \((\alpha,\beta,\gamma)\) and one means the ideal source. The exact coefficient list is

\[
\begin{aligned}
c_0&=(1-w_\alpha)(1-w_\beta)(1-w_\gamma),&
c_1&=w_\alpha(1-w_\beta)(1-w_\gamma),\\
c_2&=(1-w_\alpha)w_\beta(1-w_\gamma),&
c_3&=w_\alpha w_\beta(1-w_\gamma),\\
c_4&=(1-w_\alpha)(1-w_\beta)w_\gamma,&
c_5&=w_\alpha(1-w_\beta)w_\gamma,\\
c_6&=(1-w_\alpha)w_\beta w_\gamma,&
c_7&=w_\alpha w_\beta w_\gamma.
\end{aligned}
\]

Define \(N_{\mathbf w}(P)(a,b,c)=\sum_{i=0}^{7}c_iP_i(a,b,c)\). This is precisely the eight-term expansion of (6.2). The coefficients satisfy

\[
\sum_i c_i=
((1-w_\alpha)+w_\alpha)
((1-w_\beta)+w_\beta)
((1-w_\gamma)+w_\gamma)=1.
\]

Grouping terms with the same first source choice gives

\[
N_{(w_\alpha,w_\beta,w_\gamma)}(P)
=(1-w_\alpha)N_{(0,w_\beta,w_\gamma)}(P)
+w_\alpha N_{(1,w_\beta,w_\gamma)}(P).
\]

The identities hold algebraically for arbitrary rational visibilities and tables. To interpret the result as a probability law, require \(0\le w_e\le1\) and normalized nonnegative component tables. Then each \(c_i\ge0\), and summing the output entries gives \(\sum_i c_i=1\). Physical source-noise semantics require a further construction identifying each \(P_i\) with the Born-rule table of its indicated source replacements; arbitrary tables with these labels do not supply that construction.

These finite calculations preserve the EJM and source-noise application. They are applications of rational arithmetic and finite distributivity, rather than new reusable library theorems. The repository's existing `Erdos7.FiniteLaw` carrier describes the resulting finite probability law; the separate `IsTriangleLocal` predicate supplies no locality conclusion for it. No new D5 declaration, first freeze, inflation certificate, or physical noise threshold is claimed here.

### 6.3 Independent local output post-processing

Let \(\Lambda_A,\Lambda_B,\Lambda_C\) be stochastic output channels. Then

\[
P'=(\Lambda_A\otimes\Lambda_B\otimes\Lambda_C)P.
\tag{6.3}
\]

### Proposition 6.1: local post-processing monotonicity

If \(P\in\mathcal L_\triangle\), then \(P'\in\mathcal L_\triangle\) for every product output channel (6.3).

**Proof.** Replace Alice's response by

\[
A'(a'\mid\beta,\gamma)
=
\sum_a\Lambda_A(a'\mid a)A(a\mid\beta,\gamma),
\]

and similarly for \(B,C\). The source product measure is unchanged and the three new kernels still use only their incident edges. ∎

Therefore, if a noisy distribution \(P'\) obtained by local output post-processing is proved nonlocal, the parent P is also nonlocal. This gives a monotone detector-noise threshold. No analogous monotonicity follows for global white noise or independent source Werner noise merely from non-convexity.

### Proposition 6.2: exact linear-certificate visibility bound

Suppose a linear functional \(\ell\) is valid for a triangle-local relaxation,

\[
\ell(Q)\le b\qquad\text{for every }Q\in\mathcal L_\triangle,
\]

and \(\ell(P)>b\). Along the global line (6.1), if \(\ell(P)-\ell(U_d)>0\), then

\[
\ell(P^{\mathrm{glob}}_v)>b
\quad\Longleftrightarrow\quad
v>
\frac{b-\ell(U_d)}{\ell(P)-\ell(U_d)}.
\tag{6.4}
\]

This is a sufficient nonlocality region certified by that particular relaxation. It is not automatically the exact local/nonlocal transition.

For independent source noise, the same certificate gives the explicit multi-affine condition

\[
\ell(P_{\mathbf w})
=
\sum_S
\left(\prod_{e\in S}w_e\right)
\left(\prod_{e\notin S}(1-w_e)\right)
\ell(P_S)>b.
\tag{6.5}
\]

Equation (6.5) is the correct starting point for source-specific noise robustness. It keeps the three edge visibilities separate and can be evaluated exactly when the component tables and certificate are rational.

## 7. What the current literature establishes

The precise status is as follows.

1. **Fritz.** A standard CHSH test can be embedded in the triangle by using two independent classical sources as effective input bits and one entangled source for the Bell pair. The obstruction is therefore inherited from ordinary Bell nonlocality. It is a valid triangle-nonlocal example, but it does not isolate the genuinely network-specific joint-measurement effect.

2. **Renou et al. 2019.** The four-output family \(P_u\), generated by three entangled sources and a four-outcome joint measurement, is proven non-trilocal for
   \[
   u_{\max}^2<u^2<1,\qquad u_{\max}^2\approx0.785.
   \]
   Their proof is noiseless and uses incompatible coarse-grained constraints. They explicitly left a reasonable noise threshold open.

3. **Continuous-family inflation.** Later inflation work proves nonlocality on separated parameter intervals for the RGB4 family. The intervals are exact certificates for those ranges, not a complete characterization of every parameter value and not a noise threshold.

4. **EJM.** Gitton–Renner prove the exact noiseless EJM distribution non-classical using symmetry-reduced inflation and exact arithmetic. For their purified affine visibility proxy
   \[
   P_v=vP_{\mathrm{pure}}+(1-v)U_{64},
   \]
   the known local construction reaches \(v=3/7\), while the exact inflation certificate reaches the grid point \(v=383/512\), giving the rigorous upper bound \(v_*<383/512\) for the transition on that purified affine path; this is not an exact transition theorem. The physical EJM point is \(v=3/4\) on this proxy. This proxy must not be identified with independent source Werner noise.

5. **Rigorous noise robustness.** Approximate parity-token-counting rigidity gives a general method for noisy four-output triangle distributions. For a best-parameter TBSM family, the published proof tolerates approximately \(0.544\%\) independent source white noise and approximately \(80\%\) dephasing in the reported regime, and proves a total-variation nonlocal ball of approximately \(0.24\%\). These are rigorous sufficient regions for the specified family and noise model. They are not exact transition points, and the white-noise figure should not be transferred automatically to the maximally entangled RGB4 point.

The most important unresolved distinction is therefore:

\[
\text{exact EJM nonlocality}
\;\ne\;
\text{exact physical EJM noise threshold}.
\]

The first is now proved. The second still requires a source-typed noise model and a stronger inflation or rigidity certificate.

## 8. A formalization target for trureturing

The next Lean-compatible layer should avoid formalizing the full measurable theory at once. Use finite alphabets first.

### 8.0 Existing certified anchor

The repository already contains a finite classical interface in D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.lean. Its predicate IsTriangleLocal has exactly the three independent uniform edge variables on \([0,1]^3\), measurable response functions \(p_A(a\mid\beta,\gamma)\), \(p_B(b\mid\gamma,\alpha)\), \(p_C(c\mid\alpha,\beta)\), normalization, non-negativity, and the triple integral (1.1). The companion TriangleInequalityL1Refutation.lean reuses this predicate.

The repository also has a reusable product-source skeleton in D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.lean and the associated response-factorization modules. It proves normalization, pushforward regrouping and restriction, and factorization for disjoint readouts. A triangle is the first overlapping case: the three readouts have supports \(\{\beta,\gamma\}\), \(\{\gamma,\alpha\}\), and \(\{\alpha,\beta\}\), so pairwise output independence is false in general even though the source law is a product. The missing theorem is a single three-output pushforward formula with these overlapping supports, followed by a typed FIB readout map.
 
Those modules certify explicit **local** models and refute two proposed global bounds. They do not formalize the EJM distribution, Fritz embedding, the Renou parameter family, inflation certificates, quantum sources, or a physical noise threshold. This separation is useful: the finite Lean carrier is the correct base for the source-product layer, while the FIB documents supply a separate readout and hidden-fiber layer. The present document defines the bridge but does not claim that bridge is already kernel-checked.

A second repository warning is already machine-checked in D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.lean: pairwise local laws can have all one-coordinate marginals compatible and still admit no common global state around a three-cycle. This is not a triangle-locality criterion, but it is the exact finite analogue of why local marginal compatibility is weaker than a product-source global lift. The later inflation layer must therefore carry the common lifted state, not only its pairwise projections.

### 8.1 Finite incidence carrier

Define finite types

\[
\mathsf{Edge}=\{\alpha,\beta,\gamma\},\qquad
\mathsf{Party}=\{A,B,C\}
\]

and an incidence predicate \(\mathsf{Inc}(v,e)\). Define a source product law by a finite probability vector on each edge and a tensor product constructor. Define a response kernel with domain the product of the two incident edge alphabets.

The first theorem should state normalization of the contraction (1.2) and invariance under local output channels.

### 8.2 Five-mode quotient

Formalize the finite carrier \(\Sigma\), the map \(p\mapsto(X,Y,Z,\kappa)\), the reconstruction (2.2), the interval (2.3), and the fiber-blind identity (2.8). This can reuse the existing probability and convex-geometry interfaces. The conditional-independence equation (2.5) should be a separate theorem with its own hypotheses \(Z<1\).

### 8.3 Lift obstruction interface

Do not encode an arbitrary inflation graph as an untyped table. Define a finite inflation specification containing:

- copied edge indices;
- copied party indices;
- allowed marginal projections;
- a symmetry action;
- factorization constraints.

Then define an InflationCertificate with the required target \(T(P)\), an integer linear functional, and a strictly positive target-centered gap on every deterministic lifted event. Prove that every triangle-local law supplies the required lift before deriving the soundness implication

\[
\text{certificate exists}
\Longrightarrow
P\notin\mathcal L_\triangle.
\]

The exact EJM certificate can be admitted later as finite data. The theorem should first be generic.

### 8.4 Noise interfaces

Use three separate structures:

- GlobalVisibility with \(P,U,v\);
- IndependentSourceNoise with the eight tables \(P_S\);
- LocalOutputChannel with stochastic matrices.

The post-processing monotonicity theorem is the easiest first admission. The multi-affine source expansion (6.2) and certificate evaluation (6.5) follow by finite distributivity.

## 9. Boundary and conclusion

The project now has a precise answer to why triangles and three-dimensional closures keep reappearing.

A triangle is the smallest cycle in which each node receives two relational inputs while no node receives the third edge. Its geometry is therefore an incidence geometry of three edge sources and three two-edge faces. A three-coordinate quotient can summarize some of the response, but it cannot certify a global independent-source lift. The missing information is carried by hidden fibers such as \(\kappa\), by higher moments, or by an inflation cover.

The deepest connection is not “three sources produce three physical axes.” It is:

\[
\boxed{
\text{three-edge product structure}
+
\text{two-edge local response}
+
\text{fiber-preserving global gluing}
}
\]

A quantum distribution is network-nonlocal when its observed and low-order geometric projections look admissible, yet every attempt to lift them to a product-source, two-edge response object fails. This is a mathematically concrete form of information escape. The project’s three-dimensional response theorem supplies a conditional geometric representation of one layer. Inflation supplies the discrete global-lift obstruction. Neither layer should be promoted to a claim about physical spacetime without an additional operational bridge.

**Open obligations.**

- Construct a nontrivial finite \(\Phi\) for which the FIB \(\kappa\)-fiber is explicitly a necessary marginal of a triangle-local lift.
- Prove a sound fiber-sensitive inflation relaxation whose certificate can be expressed in the existing Gram or boundary language.
- Evaluate one exact EJM or RGB4 certificate on the multi-affine independent-source noise polynomial (6.5).
- Separate rigorous outer bounds, numerical inner models, and exact transition claims in every future noise table.


## References and repository anchors

- Fritz, “Beyond Bell’s theorem: correlation scenarios,” New J. Phys. 14 (2012), arXiv:1206.5115.
- Renou, Bäumer, Boreiri, Brunner, Gisin, Beigi, “Genuine quantum nonlocality in the triangle network,” Phys. Rev. Lett. 123, 140401 (2019), https://arxiv.org/abs/1905.04902.
- Pozas-Kerstjens, Gisin, Renou, “Proofs of network quantum nonlocality in continuous families of distributions,” Phys. Rev. Lett. 130, 090201 (2023), https://arxiv.org/abs/2203.16543.
- Bäumer, Gitton, Kriváchy, Gisin, Renner, “Exploring the Local Landscape in the Triangle Network,” Phys. Rev. A 111, 052453 (2025), https://arxiv.org/abs/2405.08939.
- Boreiri, Ulu, Brunner, Sekatski, “Noise-robust proofs of quantum network nonlocality,” Quantum 9, 1830 (2025), https://arxiv.org/abs/2311.02182.
- Gitton, Renner, “The Elegant Joint Measurement is Non-Classical in the Triangle Network,” arXiv:2510.15143 (2025), https://arxiv.org/abs/2510.15143.
- Existing finite classical carrier: D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.lean.
- Existing inequality counterexample using that carrier: D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.lean.
- Existing FIB quotient and hidden-fiber source: docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md and docs/develop/theory/AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md.
## 10. Finite observable certificates for a source dependence budget

**Definition 10.1 (one finite incident realization).** Let $\Omega_\alpha,\Omega_\beta,\Omega_\gamma$ and $\mathcal O$ be nonempty finite sets. Let $\nu$ be any probability law on the source product, with no independence or full-support assumption. For every incident input pair let $K_A(\cdot\mid\beta,\gamma)$, $K_B(\cdot\mid\gamma,\alpha)$ and $K_C(\cdot\mid\alpha,\beta)$ be nonnegative probability vectors on $\mathcal O$. All random variables in §§10–12 have the single joint law

$$
\mathbb P(\alpha,\beta,\gamma,a,b,c)
=\nu(\alpha,\beta,\gamma)
 K_A(a\mid\beta,\gamma)K_B(b\mid\gamma,\alpha)K_C(c\mid\alpha,\beta).
\tag{10.1}
$$

Thus output draws are independent conditional on all three sources, and their private randomness supplies no extra common selector. Write $P$ for the output marginal. With natural logarithms, $0\log0=0$, and zero-probability conditioning values omitted, use the usual finite Shannon entropy $H$, mutual information $I(U;V)$, conditional mutual information $I(U;V\mid W)$, and relative entropy $D$. The hidden source budget is the source-independence defect of Definition 4.1:

$$
C_{\rm src}
:=D(\nu\Vert\nu_\alpha\otimes\nu_\beta\otimes\nu_\gamma)
=H(\alpha)+H(\beta)+H(\gamma)-H(\alpha,\beta,\gamma).
\tag{10.2}
$$

Every positive cell of $\nu$ has three positive one-source marginals, so this relative entropy is finite, even with structural zeros. It is the classical total correlation of the actual hidden law. It vanishes exactly when that law is the full product of its three marginals; pairwise independence alone does not suffice.

**Theorem 10.2 (observable source-budget obstruction).** Every realization in Definition 10.1 satisfies

$$
\begin{aligned}
I(A;B)+I(A;C)-H(A)&\le 2C_{\rm src},\\
I(B;C)+I(B;A)-H(B)&\le 2C_{\rm src},\\
I(C;A)+I(C;B)-H(C)&\le 2C_{\rm src}.
\end{aligned}
\tag{10.3}
$$

Consequently the observable quantity

$$
\mathcal B(P):=\frac12\max\bigl\{0,
 I(A;B)+I(A;C)-H(A),
 I(B;C)+I(B;A)-H(B),
 I(C;A)+I(C;B)-H(C)\bigr\}
\tag{10.4}
$$

is a lower bound on the source defect of every such realization of $P$. For any specified $c\ge0$, the strict inequality $\mathcal B(P)>c$ excludes every finite incident lift of $P$ having $C_{\rm src}\le c$.

*Proof.* Reuse the finite entropy chain rule, strong subadditivity and Markov data processing. Their roles in the product-source case are exactly Fritz, Lemma 2.14, equation (2.10), with $\lambda_{AB}=\gamma$, $\lambda_{CA}=\beta$, $\lambda_{BC}=\alpha$. For the possibly dependent law (10.1), keep the two additional conditional information costs rather than importing product-source conditional independences.

Indeed, summing over unobserved outputs in (10.1) shows that $A$ and $B$ are conditionally independent given $(\alpha,\gamma)$: the conditional law of $B$ is the fixed kernel $K_B$, irrespective of $\beta$ or $A$. Also $A$ and $\alpha$ are conditionally independent given $(\beta,\gamma)$. Conditional versions of data processing are obtained by applying the finite inequality on each positive conditioning slice and averaging. Hence

$$
\begin{aligned}
I(A;B)&\le I(A;\alpha,\gamma)
 =I(A;\gamma)+I(A;\alpha\mid\gamma)\\
&\le I(A;\gamma)+I(\beta;\alpha\mid\gamma),\\
I(A;C)&\le I(A;\alpha,\beta)
 \le I(A;\beta)+I(\gamma;\alpha\mid\beta).
\end{aligned}
\tag{10.5}
$$

The second line uses the corresponding conditional independences with $C$. Each assertion concerns marginals of (10.1), including when a conditioning value has no mass. The standard chain-rule identity is

$$
I(A;\beta)+I(A;\gamma)-H(A)
=I(\beta;\gamma)-I(\beta;\gamma\mid A)-H(A\mid\beta,\gamma)
\le I(\beta;\gamma).
\tag{10.6}
$$

Combining (10.5) and (10.6) bounds the first left side of (10.3) by

$$
\begin{aligned}
&I(\beta;\gamma)+I(\alpha;\beta\mid\gamma)+I(\alpha;\gamma\mid\beta)\\
&\quad=H(\alpha,\beta)+H(\alpha,\gamma)+H(\beta,\gamma)
       -2H(\alpha,\beta,\gamma)\\
&\quad=2C_{\rm src}
 -I(\alpha;\beta)-I(\alpha;\gamma)-I(\beta;\gamma)
 \le 2C_{\rm src}.
\end{aligned}
\tag{10.7}
$$

The middle entropy expression is the classical three-variable dual total correlation, used here only as an attributed intermediate. The equalities are the standard entropy identities for total and dual total correlation, not a new entropy functional. Nonnegativity of mutual information proves the final inequality. Cyclic permutation of $(A,B,C)$ together with $(\alpha,\beta,\gamma)$ proves the other two bounds. Nonnegativity of relative entropy gives (10.4) and its budget consumer.

When $\nu$ is a product, all source information terms in (10.5)–(10.7) vanish. Thus (10.3) explicitly recovers the existing Fritz product-source baseline $I(A;B)+I(A;C)\le H(A)$ and its cyclic versions. No continuity comparison with a different output law is involved. ∎

## 11. Exact common records, equality fibers and the binary boundary

**Theorem 11.1 (recoverability and complete equality criterion).** Suppose (10.1) has $A=B=C=X$ almost surely. Then there exist incident maps $f_A,f_B,f_C$ such that

$$
X=f_A(\beta,\gamma)=f_B(\gamma,\alpha)=f_C(\alpha,\beta)
\quad\text{almost surely}.
\tag{11.1}
$$

In particular,

$$
C_{\rm src}\ge\frac12H(X).
\tag{11.2}
$$

Equality in (11.2) holds on this same realization if and only if both of the following conditions hold: the three source pairs are unconditionally independent, and for every $x$ with $p_x:=\mathbb P(X=x)>0$,

$$
\nu(\alpha,\beta,\gamma\mid X=x)
=\nu_\alpha(\alpha\mid x)\nu_\beta(\beta\mid x)\nu_\gamma(\gamma\mid x)
\quad\text{for all }\alpha,\beta,\gamma.
\tag{11.3}
$$

Thus the conditional requirement is a threefold product on each positive output fiber, including its zero cells.

*Proof.* First derive (11.1) from the stochastic kernels. For a source triple $s$ with $\nu(s)>0$, the conditional product of the three response vectors must give mass one to the output diagonal. Otherwise its positive off-diagonal mass would contribute positively to $\mathbb P(A,B,C\text{ not all equal})$. Choose one positive coordinate in each response vector. Their labels must be the same, say $x_s$. Keeping the chosen coordinates of the other two vectors fixed shows that every positive coordinate in any one vector has label $x_s$. Each of the three vectors is therefore $\delta_{x_s}$.

If an incident pair $(\beta,\gamma)$ has positive marginal mass, it has at least one positive extension $\alpha$. The preceding argument makes $K_A(\cdot\mid\beta,\gamma)$ a point mass. Its label cannot depend on the chosen extension because it is the same kernel row. Define $f_A$ to be this label, and do the same for $f_B,f_C$. On zero-marginal incident pairs assign any label of the nonempty output alphabet; these assignments affect no probability. This proves (11.1), and in particular

$$
H(X\mid\alpha,\beta)=H(X\mid\alpha,\gamma)
=H(X\mid\beta,\gamma)=H(X\mid\alpha,\beta,\gamma)=0.
\tag{11.4}
$$

Theorem 10.2 now gives (11.2), since $I(A;B)=I(A;C)=H(X)$.

For the full equality assertion, retain all terms in a different, exact entropy balance. The classical conditional dual total correlation, averaged over the positive $X$-fibers, is the intermediate quantity

$$
\begin{aligned}
\mathcal D_X
&:=H(\alpha,\beta\mid X)+H(\alpha,\gamma\mid X)
  +H(\beta,\gamma\mid X)-2H(\alpha,\beta,\gamma\mid X)\\
&=I(\alpha;\beta,\gamma\mid X)
  +I(\beta;\gamma\mid\alpha,X)\ge0.
\end{aligned}
\tag{11.5}
$$

By (11.4), each unconditional source-pair entropy is $H(X)$ plus its entropy conditional on $X$, and the same holds for the source triple. Substituting into (10.7) yields the exact same-law identity

$$
2C_{\rm src}-H(X)
=I(\alpha;\beta)+I(\alpha;\gamma)+I(\beta;\gamma)+\mathcal D_X.
\tag{11.6}
$$

All four terms are nonnegative. Vanishing of the first three is exactly unconditional pairwise source independence, by the zero-relative-entropy characterization. It remains to identify $\mathcal D_X=0$ without replacing it by conditional pairwise independence.

Since (11.5) is a finite average of nonnegative terms, $\mathcal D_X=0$ forces, on every positive $x$-fiber, both

$$
\alpha\perp(\beta,\gamma)\mid X=x,
\qquad I(\beta;\gamma\mid\alpha,X=x)=0.
\tag{11.7}
$$

The first relation makes the conditional law of $(\beta,\gamma)$ given $(\alpha,x)$ equal to its law given $x$ for every positive $\alpha$ in that fiber. Thus the second term of (11.7) equals $I(\beta;\gamma\mid X=x)$, which must be zero. The fiber law is consequently the product in (11.3). This argument only divides by positive conditioning masses; cells outside the conditional marginal supports have zero mass on both sides of (11.3). Conversely, (11.3) makes both conditional information terms in (11.5) zero. Together with unconditional pairwise independence, (11.6) then proves equality. This establishes both directions on the stipulated joint law. ∎

**Theorem 11.2 (strict binary cost and finite-lift exclusion).** Let $0<p<1$ and let the observed common record have $\mathbb P(X=1)=p$, $\mathbb P(X=0)=1-p$. Every individual finite realization of this diagonal output law satisfying Definition 10.1 has

$$
C_{\rm src}>\frac12 h(p),
\qquad h(p):=-p\log p-(1-p)\log(1-p).
\tag{11.8}
$$

Equivalently, for

$$
P_p(0,0,0)=1-p,\qquad P_p(1,1,1)=p,
\qquad P_p(a,b,c)=0\text{ otherwise},
\tag{11.9}
$$

there is no choice of nonempty finite source alphabets, hidden law and normalized incident kernels realizing $P_p$ with source budget at most $h(p)/2$. Such finite realizations do exist at larger budgets.

*Proof.* Suppose equality held in (11.2). By Theorem 11.1, the two positive conditional source laws would be threefold products. Write their one-source probability vectors as $u_i,v_i,w_i$ for $i\in\{0,1\}$. Then

$$
\nu=(1-p)u_0\otimes v_0\otimes w_0
       +p u_1\otimes v_1\otimes w_1.
\tag{11.10}
$$

Unconditional independence of $\alpha,\beta$ implies, entry by entry,

$$
0=\nu_{\alpha\beta}-\nu_\alpha\otimes\nu_\beta
=p(1-p)(u_1-u_0)\otimes(v_1-v_0).
\tag{11.11}
$$

A tensor product of two finite real vectors is zero only if at least one vector is zero: if each had a nonzero coordinate their product at that pair of coordinates would be nonzero. Thus $u_0=u_1$ or $v_0=v_1$. The other two unconditional pair independences give the analogous alternatives for $(u,w)$ and $(v,w)$. At most one of the three source marginal vectors can change with $i$; at least two are identical across the two fibers.

Choose two such sources, say $\alpha,\beta$. Their conditional joint law in each fiber is the same product $u_0\otimes v_0=u_1\otimes v_1$. They are jointly independent of $X$. This contradicts $H(X\mid\alpha,\beta)=0$ in (11.4), because joint independence would give $H(X\mid\alpha,\beta)=h(p)>0$. Equivalently, choose a positive coordinate in each of the two common marginal vectors. Their pair has positive probability under both output fibers, so it cannot have a unique deterministic incident readout. This also verifies the contradiction when other cells are structural zeros. The same argument applies whichever two source vectors are unchanged. Equality is impossible, and (11.2) gives (11.8).

For nonvacuity take a Bernoulli $Y$ of parameter $p$, put $\alpha=\beta=Y$ and let $\gamma$ be constant. Use the deterministic incident responses $A=\beta$, $B=\alpha$, $C=\alpha$. They are normalized kernels of exactly the permitted form, can be defined the same way on off-support input pairs, and give $A=B=C=Y$. Here

$$
C_{\rm src}=H(\alpha)+H(\beta)+H(\gamma)-H(\alpha,\beta,\gamma)=h(p)>h(p)/2.
$$

This proves existence without assigning an optimal binary cost. ∎

The quantifier in Theorem 11.2 is over each finite realization, with no cardinality bound imposed uniformly on all realizations. Pointwise strictness does not prove a uniform positive margin above $h(p)/2$, nor determine whether the infimum over unbounded finite alphabets equals that boundary or a larger value. For $p=0$ or $p=1$, the record is constant and a product-source realization has cost zero; the strict assertion requires both fibers to have positive probability. For a constant record in any finite model, Theorem 11.1 reduces equality to $C_{\rm src}=0$, as expected.

## 12. A sharp group family and the noisy-agreement consequence

**Proposition 12.1 (incidence-faithful attainment of the factor two).** Let $G$ be any finite group of order $n\ge2$. Take independent uniform $U,V\in G$, and define the source law and deterministic output maps by

$$
\begin{gathered}
\alpha=U,\qquad\beta=V,\qquad\gamma=UV,\qquad\mathcal O=G\times G,\\
f_A(\beta,\gamma)=(\gamma\beta^{-1},\beta),\qquad
f_B(\gamma,\alpha)=(\alpha,\alpha^{-1}\gamma),\qquad
f_C(\alpha,\beta)=(\alpha,\beta).
\end{gathered}
\tag{12.1}
$$

With kernels $K_v(o\mid\cdot)=\mathbf1_{\{o=f_v(\cdot)\}}$, this is a realization of Definition 10.1 with

$$
A=B=C=X=(U,V),\qquad H(X)=2\log n,\qquad C_{\rm src}=\log n.
\tag{12.2}
$$

Each response depends essentially on both incident source slots. Hence the universal coefficient $2$ in (10.3) cannot be decreased, and the coefficient $1/2$ in (11.2) is attained for these larger output alphabets.

*Proof.* Every source is uniform. For fixed $u,g$ there is exactly one $v=u^{-1}g$, and for fixed $v,g$ exactly one $u=gv^{-1}$. Thus the pairs $(\alpha,\beta)$, $(\alpha,\gamma)$ and $(\beta,\gamma)$ are all uniform on $G^2$ and pairwise independent, whereas the triple is supported on $\gamma=\alpha\beta$. Its $n^2$ positive cells have mass $n^{-2}$; the product of its marginals has mass $n^{-3}$ on all $n^3$ cells. Therefore $C_{\rm src}=\log n$, also obtained from the three marginal entropies and triple entropy $2\log n$.

Group cancellation in the specified order gives all three outputs $(U,V)$; commutativity is unnecessary. The conditional source law given $X=(u,v)$ is a point mass at $(u,v,uv)$, hence a threefold product. This verifies the equality criterion directly. For fixed $\beta$, changing $\gamma$ changes the first coordinate of $f_A$; for fixed $\gamma$, changing $\beta$ changes its second coordinate. For $f_B$, changing $\alpha$ changes its first coordinate, and changing $\gamma$ at fixed $\alpha$ changes its second coordinate. Both slots of $f_C$ are explicit coordinates. Every incident pair has positive marginal probability, so this essential dependence is not hidden in unused kernel rows. All three maps use only incident sources, proving the claimed incidence fidelity. Finally $I(A;B)+I(A;C)-H(A)=H(X)=2C_{\rm src}>0$. ∎

**Corollary 12.2 (Fano certificate from two observed errors).** In Definition 10.1 let $\mathcal O$ have $m\ge2$ symbols, let $A$ be uniform, and assume

$$
\mathbb P(A\ne B)\le\varepsilon,\qquad
\mathbb P(A\ne C)\le\varepsilon,\qquad
0\le\varepsilon\le1-1/m.
\tag{12.3}
$$

Then

$$
C_{\rm src}\ge
\max\left\{0,\frac{\log m}{2}-h(\varepsilon)
                         -\varepsilon\log(m-1)\right\}.
\tag{12.4}
$$

For $m=1$ the output is constant and the conclusion is simply $C_{\rm src}\ge0$; no $\log(m-1)$ expression is used.

*Proof.* Use Fano's finite-alphabet inequality in nats, with $B$ itself as an estimator of $A$, and separately with $C$ as an estimator of $A$. If their actual error probabilities are $e_B,e_C$, the classical inequality gives

$$
H(A\mid B)\le h(e_B)+e_B\log(m-1),\qquad
H(A\mid C)\le h(e_C)+e_C\log(m-1).
\tag{12.5}
$$

These are the sharp-cardinality Fano bounds, not an independence assertion about errors. For clarity, the first follows by adjoining $E_B=\mathbf1_{\{A\ne B\}}$: since $E_B$ is determined by $(A,B)$,

$$
H(A\mid B)=H(E_B\mid B)+H(A\mid E_B,B)
\le h(e_B)+e_B\log(m-1).
$$

When $E_B=0$ there is no uncertainty in $A$; when $E_B=1$, at most $m-1$ symbols remain. The same argument gives the second bound. Zero-probability error events contribute zero conditional entropy. This is the usual Fano argument, attributed to Fano's *Transmission of Information* and represented in the repository by `FanoSharp.fano_inequality_sharp`.

The function $g_m(t)=h(t)+t\log(m-1)$ is continuous on $[0,1]$ and has derivative

$$
g_m'(t)=\log\!\left(\frac{(1-t)(m-1)}{t}\right)\ge0
\quad\text{for }0<t\le1-1/m.
$$

Thus both upper bounds in (12.5) are at most $g_m(\varepsilon)$, including the endpoints by continuity. Since $H(A)=\log m$,

$$
\begin{aligned}
I(A;B)+I(A;C)-H(A)
&=\log m-H(A\mid B)-H(A\mid C)\\
&\ge\log m-2g_m(\varepsilon).
\end{aligned}
$$

Apply Theorem 10.2 and $C_{\rm src}\ge0$. No step conditions on, multiplies, or assumes independence of the two error events. At $\varepsilon=0$, (12.4) agrees with the half-entropy bound; for a nonconstant binary exact record Theorem 11.2 strengthens that particular conclusion to strictness. At $\varepsilon=1-1/m$, $g_m(\varepsilon)=\log m$, so (12.4) gives only zero. ∎

## 13. Information retained, literature correspondence and remaining scope

The observable inputs to (10.4) are the three one-party entropies and the three pairwise mutual informations, all calculated from the same $P$. Equivalently, the one-party and two-party marginal tables suffice. A single chosen cyclic inequality needs just the two pair tables incident to its central output. Corollary 12.2 instead needs the declared common output alphabet, uniformity of $A$, and the two probabilities in (12.3), with no independence of errors. Theorem 11.2 needs the exact Bernoulli diagonal output law, including absence of every off-diagonal event.

These observable quantities constrain $\mathfrak d_{\rm src}(\nu)$ of a candidate hidden lift in §4; they do not identify the hidden law or its defect. In particular (10.4) is only a necessary condition for a lift of a given budget. A statistic that retains an arbitrary FIB quotient need not retain the marginal tables, entropy values or error events just specified. Applying these certificates after such a quotient requires a supplied map proving that the requisite quantities are determined by it. The fiber identity (2.8), by itself, gives no such entropy access.

The product-source baseline used inside Theorem 10.2 is literature-attested: Tobias Fritz, *Beyond Bell's theorem: correlation scenarios*, [arXiv:1206.5115v2](https://arxiv.org/abs/1206.5115v2), Lemma 2.14 and equation (2.10), in the classical triangle with mutually independent sources. The total correlation in (10.2) is Watanabe's classical quantity (*Information theoretical analysis of multivariate correlation*, IBM Journal of Research and Development 4, 66–82); the dual total correlation in (10.7) and (11.5) is the classical entropy quantity of Han (*Nonnegative entropy measures of multivariate symmetric correlations*, Information and Control 36, 133–156). They are attributed intermediate identities here. Fano's conditional-entropy inequality is also an attributed intermediate; its use in (12.4) composes it with the source-budget certificate.

Marc-Olivier Renou, Yuyi Wang, Sadra Boreiri, Salman Beigi, Nicolas Gisin and Nicolas Brunner, *Limits on correlations in networks for quantum and no-signaling resources*, [arXiv:1901.08287v1](https://arxiv.org/abs/1901.08287v1), Theorem 1, prove the independent-source triangle bound

$$
P(a,b,c)\le\sqrt{P_A(a)P_B(b)P_C(c)}.
$$

Their Theorem 2 extends the Finner bound to arbitrary graphs of independent bipartite quantum sources and fractional independent-set weights; the classical multipartite-source version is also discussed there. This is independent-source context, not a KL-budget theorem for (10.1), and it is not the distinct Renou et al. four-output nonlocality family cited in §7.

Ivan Šupić, Jean-Daniel Bancal and Nicolas Brunner, *Quantum nonlocality in networks can be demonstrated with an arbitrarily small level of independence between the sources*, [arXiv:2007.12950v1](https://arxiv.org/abs/2007.12950v1), equations (3)–(5), introduce a central variable $\lambda$ and require pointwise minorization

$$
p(\alpha,\beta,\gamma\mid\lambda)
\ge\epsilon_1 p(\alpha)p(\beta)p(\gamma),\qquad\epsilon_1>0,
$$

with their accompanying pointwise upper comparison. That restriction, for every $\lambda$, is different from the upper bound $D(\nu\Vert\nu_\alpha\nu_\beta\nu_\gamma)\le c$ on one actual source law. The latter allows structural zeros even where the product of the marginals is positive, as Proposition 12.1 demonstrates. None of the pointwise minorization conclusions is imported as a consequence of a KL upper budget.

The relevant repository suppliers have correspondingly narrower mathematical scopes. `Entropy/Submodularity/MarkovDataProcessing` supplies finite Markov data processing and its conditional-product equality characterization; `MutualInformationChainRule`, `ConditionalMutualInformation` and `StrongSubadditivity` supply the finite entropy identities and inequalities. `Entropy/ConditionalEntropyEquality` handles point masses only on positive-marginal conditioning slices, and `CommonStateEntropyBound` concerns a state determined by either of two supplied coordinates. Its deterministic-readout premise is supplied here by the kernel-support argument, rather than postulated for stochastic outputs. `Estimation/FanoSharp` supplies the finite $\log(m-1)$ correction for a non-singleton target alphabet. These are the D5 modules under `D5/S3/` and their corresponding Blueprint Scribe sources; their existing statements do not by themselves assert Theorem 11.2.

`ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping` preserves the full elementary product law under regrouping and restriction. Its companion `IndependentSourceCounterfactualFactorization` requires disjoint readout supports for response independence. The triangle supports overlap, so that disjoint-support result cannot certify independence of $A,B,C$. `Quantum/Entanglement/TriangleInflationSoundness` constructs observable laws on independent continuous source copies with four-output measurable kernels. That product-source construction is not transferred unchanged to dependent $\nu$. The separate `TriangleSymmetricLocalRefutation` concerns a fully symmetric four-output local model with agreement probability $41/144>1/4$; it concerns imperfect agreement under independent sources, rather than a nonconstant exact common record at a source-KL boundary.

The source-budget certificate, its same-realization equality analysis and the binary finite-lift exclusion are repo-derived consequences in this finite incidence model. They are not assertions of worldwide novelty or resolutions of a named external open problem. The Bernoulli exclusion is a concrete strengthening of the observable budget test exactly at its boundary; Proposition 12.1 shows why that exclusion cannot be extended to all finite output alphabets. Determining the infimum source cost for binary common records over unbounded finite source alphabets remains a separate mathematical question. Likewise, arbitrary output laws, physical source installation, statistical estimation from samples, infinite-alphabet extensions and the physical EJM noise-threshold obligations in §9 require additional arguments.

## 追加锚（本行以下为增补区）
