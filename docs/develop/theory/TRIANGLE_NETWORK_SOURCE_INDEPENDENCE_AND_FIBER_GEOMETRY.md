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

### Proposition 1.2: why the triangle-local set is non-convex

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

Introduce a selector \(S\) that chooses the first or second product. Unless \(S\) is available to every source edge, the joint source law is not a product of three independent edge marginals. Thus the mixture is not automatically triangle-local.

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

On the event \(z=0\), the two features \(x\) and \(y\) are conditionally independent exactly when

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

The equality of the last expression with the product of the first two is exactly (2.5). ∎

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

This is the first rigorous information-escape statement for the triangle interface. Any statistic with \(J_f=0\) factors through the three-coordinate quotient. It cannot see the hidden joint coupling \(\kappa\), even though two laws with the same \((X,Y,Z)\) can have different full distributions and different continuation behavior. A witness for source independence must therefore be sensitive either to a nonzero fiber coordinate or to a higher lift carrying the edge-incidence constraints.

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
- proving that the certificate is positive on every lifted deterministic event proves the original distribution is not triangle-local.

For a rational target \(P=N/D\), the certificate can be checked by clearing denominators. If \(K\) is the inflation map and \(f\) is an integer vector, it is enough to verify

\[
\left\langle f,\,
D^2|G_P|K(\delta_\omega)
\right\rangle>0
\]

for every lifted deterministic event \(\omega\), where \(G_P\) is the relevant symmetry group. This is an exact integer certificate, not a floating-point numerical distance.

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
   the known local construction reaches \(v=3/7\), while the final exact inflation certificate proves nonlocality for \(v>383/512\). The physical EJM point is \(v=3/4\) on this proxy. This proxy must not be identified with independent source Werner noise.

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

Those modules certify explicit **local** models and refute two proposed global bounds. They do not formalize the EJM distribution, Fritz embedding, the Renou parameter family, inflation certificates, quantum sources, or a physical noise threshold. This separation is useful: the finite Lean carrier is the correct base for the source-product layer, while the FIB documents supply a separate readout and hidden-fiber layer. The present document defines the bridge but does not claim that bridge is already kernel-checked.

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

Then define an InflationCertificate as an integer linear functional whose value is strictly positive on every deterministic lifted event. Prove the soundness implication

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
