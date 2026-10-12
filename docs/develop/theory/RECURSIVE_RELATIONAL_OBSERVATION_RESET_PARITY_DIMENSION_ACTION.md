# Reset parity, complement and the full dimension action

The arithmetic state records the sum of the two sign coefficients at every
suffix. Complement preserves that state, while the stationary unit transition
scales it. A class invisible to the state can nevertheless obstruct an
automorphism of the full integer dimension group. For the reset family, the
actual geometric representation contains identity plus unit transition
precisely at positive even orders.

## Definition 1. The native group and the two actions

Let \(C_2=\{1,\tau\}\), with \(\tau^2=1\), and write \([s]\) for its
group-ring basis elements. For \(q>0\), put
\[
(A_q)_{ij}=\mathbf1_{j=0}[\tau]+\mathbf1_{j=i+1}[1],\qquad
M_q=\operatorname{Fin}(q)\to\mathbb Z[C_2],\qquad
T_q(v)=vA_q,\qquad G_q=\varinjlim(M_q,T_q).
\]
Multiplication is on the right of rows. In particular,
\[
(T_qv)_0=\Bigl(\sum_i v_i\Bigr)[\tau],\qquad
(T_qv)_j=v_{j-1}\quad(0<j<q).
\]
Write \(\operatorname{of}_n(v)\) for a stage class, so that
\(\operatorname{of}_{n+1}(T_qv)=\operatorname{of}_n(v)\).

There are two commuting actions:
\[
\sigma_q\operatorname{of}_n(v)=\operatorname{of}_n(L_\tau v),
\quad (L_\tau v)_i=[\tau]v_i,\qquad
\Theta_q\operatorname{of}_n(v)=\operatorname{of}_n(T_qv).
\]
Associativity implies \(L_\tau T_q=T_qL_\tau\), and
\(\sigma_q^2=\mathrm{id}\). Complement \(\sigma_q\) and time transition
\(\Theta_q\) retain their separate definitions, including when their actual
actions coincide in a degenerate case.

## Proposition 2. The exact integral arithmetic kernel

For \(q\ge2\), let \(\beta\in(1,2)\) be the positive root of
\(X^q-\sum_{j<q}X^j\), put \(p=\beta^{-1}\), and define
\[
h_i=\sum_{a=0}^{q-i-1}p^{a+1}.
\]
The compatible state on the native integer group is
\[
\Phi_q(\operatorname{of}_n(v))
 =p^n\sum_i\bigl(\operatorname{coeff}_1(v_i)
                 +\operatorname{coeff}_\tau(v_i)\bigr)h_i.
\]
It satisfies
\[
\ker\Phi_q=\operatorname{range}(\mathrm{id}-\sigma_q)
          =\ker(\mathrm{id}+\sigma_q).
\]

Proof. The scalar polynomial is irreducible over \(\mathbb Q\), so
\(1,\beta,\ldots,\beta^{q-1}\) are linearly independent over \(\mathbb Q\).
The expansion
\(h_i=\beta^i-\sum_{j<i}\beta^j\) is triangular with diagonal one;
the \(h_i\) are therefore linearly independent as well. The relations
\(h_0=1\), \(\beta h_i=1+h_{i+1}\) for \(i<q-1\), and
\(\beta h_{q-1}=1\), together with the row formula, give
\(\ell_q(T_qv)=\beta\ell_q(v)\), where
\(\ell_q(v)=\sum_i(a_i+b_i)h_i\) for
\(v_i=a_i[1]+b_i[\tau]\). This proves compatibility of the stage formula.

Since \(p^n\ne0\), a stage class has zero state exactly when every
\(a_i+b_i\) vanishes. Then
\[
v_i=a_i([1]-[\tau])
   =(\mathrm{id}-L_\tau)(a_i[1]),\qquad L_\tau v=-v.
\]
This gives an integral witness, with no division by two. Conversely,
complement preserves each coefficient sum, so the displayed range lies in
the state kernel.

For the remaining inclusion, suppose
\(x=\operatorname{of}_n(v)\) and \(x+\sigma_qx=0\). Eventual equality in
the direct limit gives a later stage \(m\ge n\) where
\(T_q^{m-n}(v+L_\tau v)=0\). Put \(u=T_q^{m-n}v\). Commutation yields
\(u+L_\tau u=0\), hence each pair of coefficients of \(u_i\) sums to
zero. The same integral witness works at stage \(m\). No injectivity of
stage maps or torsion-free hypothesis is required. The irreducibility and
weight identities used here are the scalar arithmetic inputs; they are
not assertions about the characteristic polynomial of the expanded graph.

## Proposition 3. What the state detects

Under the hypotheses of Proposition 2,
\[
\Phi_q\sigma_q=\Phi_q,\qquad
\Phi_q\Theta_q=\beta\Phi_q,\qquad
\Phi_q((\mathrm{id}+\Theta_q)x)=(1+\beta)\Phi_q(x).
\]
Consequently
\(\ker(\mathrm{id}+\Theta_q)\subseteq\ker\Phi_q\), and
\(\Theta_q\ne\sigma_q\) for \(q\ge2\).

Proof. Complement swaps the coefficients, whereas the transition obeys
\(\ell_qT_q=\beta\ell_q\). Apply these identities to the stage formula;
every colimit element has a stage representative. If
\((\mathrm{id}+\Theta_q)x=0\), then
\((1+\beta)\Phi_q(x)=0\). Finally
\(\Phi_q(\operatorname{of}_0(e_0[1]))=h_0=1\), and the two multipliers
are respectively \(\beta>1\) and one.

The state identifies \(G_q/\ker\Phi_q\) with its image in \(\mathbb R\).
It does not identify the action on the state kernel. In particular,
invariance of this state does not prove inertness: inertness requires the
identity action on the full dimension group. Nor do the rational projections
\((\mathrm{id}\pm\sigma_q)/2\) provide an integral splitting, since they
send \([1]\) to \(([1]\pm[\tau])/2\), outside the vertex lattice.

## Proposition 4. The odd obstruction, including order one

For positive odd \(q\), set
\(w_i=(-1)^i([1]-[\tau])\) and \(c_q=\operatorname{of}_0(w)\). Then
\[
c_q\ne0,\qquad (\mathrm{id}+\Theta_q)c_q=0.
\]

Proof. At a nonzero suffix, the predecessor formula gives
\((T_qw)_j=w_{j-1}=-w_j\). At suffix zero,
\(\sum_{i<q}(-1)^i=1\), and right multiplication by \([\tau]\) negates
\([1]-[\tau]\). Thus \(T_qw=-w\) and
\(T_q^kw=(-1)^kw\). The identity coefficient at suffix zero is
\((-1)^k\), so no iterate vanishes. If \(c_q=0\), eventual equality
would force some iterate to vanish. The stage formula for \(\Theta_q\)
now gives \(\Theta_qc_q=-c_q\).

The argument includes the deterministic flip \(q=1\). Proposition 2
does not extend to that case: its spectral radius is one, while the support
fallback \(p=1/2\) is not the reciprocal of that radius. For odd
\(q\ge3\), the two coefficients of every \(w_i\) sum to zero, so
\(\Phi_q(c_q)=0\). The obstruction is invisible to the arithmetic state.

## Definition 5. The full geometric representation

Expand \(A_q\) on vertices \((i,s)\in\operatorname{Fin}(q)\times C_2\).
The natural adjacency counts every numbered edge:
\[
(B_q)_{(i,s),(j,t)}
 =\operatorname{coeff}_{s^{-1}t}((A_q)_{ij}).
\]
Let \(X_q\) consist of all legal integer-indexed edge histories with the
product/subspace topology. Let \(Sx\) have coordinate \((Sx)_k=x_{k+1}\),
and let \(\operatorname{Aut}(X_q,S)\) be all homeomorphisms commuting with
this unit shift.

For any integer cut \(m\), the whole past ray is
\[
\mathcal R(x,m)=\{y\in X_q:\forall k\le m,\ y_k=x_k\}.
\]
A beam is a finite disjoint union of such rays at some cut. Finite tagged
families retain separate copies and all endpoint multiplicities. Common
refinement splits each ray by its actual numbered continuations. At a
common cut, an endpoint-preserving bijection of ray pieces gives a
geometric matching by replacing the whole past and retaining the legal
future. Group completion of these matching classes gives the integer
beam group \(\mathcal G_q\).

The standard beam identification with a stationary dimension group is due
to the established theory of shifts of finite type; see Schmieding,
Section 2, Proposition 2.1, for the fixed-past and row-right conventions.
Here its coordinate maps can be described explicitly. At a nonnegative
cut \(N\), count one vertex basis row for each ray piece. Refinement
multiplies that row on the right by \(B_q\), so its colimit class is
independent of cut. At an arbitrary integer cut \(m\), use any
\(N\ge\max(0,m)\) and the row \(zB_q^{N-m}\) at stage \(N\).
Only nonnegative transition powers are used. Conversely, each vertex has
a legal full history, and its ray supplies the inverse stage generator;
common refinement proves both inverse identities after group completion.

The integral coefficient map
\[
u\longmapsto\left(i\longmapsto\sum_{s\in C_2}u_{(i,s)}[s]\right)
\]
has inverse coefficient extraction and intertwines row multiplication by
\(B_q\) with \(T_q\). Their composite is an integer-group isomorphism
\(E_q:\mathcal G_q\cong G_q\).

Every member \(h\) of the full automorphism group, and its inverse, has a
finite coordinate window: continuity, compactness and commutation with
the unit shift give uniform windows. The actual image of a whole past ray
is therefore a beam at a sufficiently late cut. Conjugating past splices
by \(h\) respects the geometric matching relations. Actual set image
thus induces an automorphism \(h_*\) of \(\mathcal G_q\), with
\((gh)_*=g_*h_*\). Define
\(\rho_q(h)=E_qh_*E_q^{-1}\).
The domain imposes no extra window, endpoint or supplied-action hypothesis.

## Proposition 6. Unit shift and the even whole-ray action

For every \(q>0\), \(\rho_q(S)=\Theta_q\). For every positive even
\(q\), the numbered reset square-lift gives
\(H_q\in\operatorname{Aut}(X_q,S)\) with
\(\rho_q(H_q)=\mathrm{id}+\Theta_q\).

Proof. The unit shift sends \(\mathcal R(x,m)\) onto
\(\mathcal R(Sx,m-1)\) with the same endpoint. Refinement from cut
\(m-1\) to cut \(m\) multiplies the row by \(B_q\); under \(E_q\)
this is exactly \(T_q\). This includes the cut-zero to cut-minus-one
calculation.

For the even construction, use the reset numbered commuting squares and
their finite-forgetting lifts. Their mutually inverse finite-window
tables define the square-lift homeomorphism \(H_q\) and commute with the
unit shift. Put \(C_q=I+A_q\). The whole-ray calculation of the lift is
\[
H_q\bigl(\mathcal R(x,m)\bigr)
 =\bigsqcup_{\substack{r\text{ numbered expanded }C_q\text{-edge}\\
                       s(r)=t(x_m)}}\mathcal R(\beta_r,m).
\]
Each component has endpoint \(t(r)\). Every legal future in that
component lifts back to the original whole past of \(x\), with its
prescribed numbered boundary \(r\). This supplies actual equality of
sets and disjointness, rather than just finite-window agreement or
equality of endpoint counts.

The image endpoint row at the same cut is consequently
\(e_{t(x_m)}(I+B_q)\). Counted edge fibers, including the separate
identity edges, give this multiplicity exactly. Under the two-coefficient
integral transport,
\[
T_{I+A_q}v=v+T_qv.
\]
Hence \(\rho_q(H_q)\) agrees with \(\mathrm{id}+\Theta_q\) on every
vertex basis generator at every natural stage. Every element of \(G_q\)
has a stage representative, so the equality holds on the whole original
integer group.

## Theorem 7. Exact parity membership

For every \(q>0\),
\[
\boxed{\quad
\bigl(\exists h\in\operatorname{Aut}(X_q,S):
       \rho_q(h)=\mathrm{id}+\Theta_q\bigr)
\quad\Longleftrightarrow\quad q\text{ is even}.
\quad}
\]

Proof. At even order, Proposition 6 supplies the actual witness \(H_q\).
At odd order, Proposition 4 gives a nonzero class killed by
\(\mathrm{id}+\Theta_q\). Every \(\rho_q(h)\) is injective, so it
cannot equal that map. The dichotomy covers all positive orders, including
\(q=1\), without a mixing, entropy, injective-transition or torsion-free
premise.

## Proposition 8. A conditional entropy consequence

Suppose \(q\ge2\) is even, the expanded shift is irreducible with
positive entropy, and the transported beam state is precisely \(\Phi_q\),
normalized on rays by \(p^m h_i\) at vertex \((i,s)\). Then
\[
\log(1+\beta)\le h_{\mathrm{top}}(H_q).
\]

Proof. Proposition 3 gives state multiplier \(\lambda_{H_q}=1+\beta\).
Apply Schmieding's Theorem 3.3; Remark 3.5 gives the general form
\(|\log\lambda_H|\le h_{\mathrm{top}}(H)\) by also applying the theorem
to the inverse. The geometric state identification and irreducibility
are hypotheses here. Irreducibility of the scalar degree-\(q\) polynomial
does not establish irreducibility of the expanded \(2q\)-vertex graph's
characteristic polynomial. No injection of the full history automorphism
group into its state multipliers is asserted.

Reference: Scott Schmieding, *Lyapunov exponents and entropy for
automorphisms of the shift*,
[arXiv:1803.04060v1](https://arxiv.org/pdf/1803.04060v1), Section 2,
pp. 3–5 (Proposition 2.1), and Section 3, pp. 6–7 (Theorem 3.3,
Remark 3.5). These published beam and entropy results are used with their
stated hypotheses; the reset-specific parity calculation is the deduction
above.
