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

## Proposition 9. Finite additive companion elimination

Let \(A\) be an additive commutative group, \(J:A\to A\) an additive
endomorphism, and \(q>0\). Define \(L_J:A^q\to A^q\) by
\[
(L_Jv)_0=v_0+J\left(\sum_{i=0}^{q-1}v_i\right),
\qquad (L_Jv)_j=v_j+v_{j-1}\quad(1\le j<q).
\]
Set
\[
K_q=\{j:1\le j<q,\ q-j\text{ odd}\},\qquad
s_q=\begin{cases}0&q\text{ even},\\1&q\text{ odd}.\end{cases}
\]
There are separate additive domain and codomain equivalences
\(D,C:A^q\longrightarrow A\times A^{q-1}\), given by
\[
D(v)=\bigl(v_0,(v_j+v_{j-1})_{1\le j<q}\bigr),\qquad
C(y)=\left(y_0-J\left(\sum_{j\in K_q}y_j\right),
                  (y_j)_{1\le j<q}\right),
\]
such that
\[
C L_J D^{-1}(a,t)=\bigl(a+J(s_q a),t\bigr).
\]
No involutivity of \(J\) is required.

Proof. The inverse of \(D\) is the recurrence
\(v_0=a\), \(v_j=t_j-v_{j-1}\). The inverse of \(C\) adds
\(J(\sum_{j\in K_q}t_j)\) to the initial coordinate and retains every
tail coordinate. The adjacent pairs indexed by \(K_q\) partition all
coordinates when \(q\) is even, and all except coordinate zero when
\(q\) is odd. Hence
\[
\sum_{i=0}^{q-1}v_i=s_q v_0+
       \sum_{j\in K_q}(v_j+v_{j-1}).
\]
Apply additivity of \(J\) and cancel the tail sum in the codomain shear.
The tail equations are unchanged. These are separately defined domain and
codomain equivalences, so this calculation asserts equivalence of an operator's
domain and codomain, without a conjugacy conclusion.

## Theorem 10. Complete finite integral reset defect

On the original lattice \(M_q=(\mathbb Z[C_2])^q\), let
\(L_q=\mathrm{id}+T_q\), with \(T_q\) the original right-row reset
transition. Write \([1]\) and \([\tau]\) for the two integral group
basis elements. For a row \(y\), define the integer character
\[
\ell_q(y)=\sum_{\substack{0\le i<q\\i\text{ even}}}
       \bigl(\operatorname{coeff}_1(y_i)-
             \operatorname{coeff}_\tau(y_i)\bigr).
\]
For every positive even \(q\), \(L_q\) is an integral bijection.
Its kernel and cokernel vanish. For every positive odd \(q\),
\[
\ker L_q=\mathbb Z w,\qquad
\operatorname{im}L_q=\ker\ell_q,\qquad
M_q/\operatorname{im}L_q\cong\mathbb Z,
\]
where \(w_i=(-1)^i([1]-[\tau])\) is the row of Proposition 4.
Its kernel coefficient is unique, and \(\ell_q\) is surjective.
Every solvable equation \(L_qv=y\) has the complete solution family
\(v=v^*(y)+kw\), with unique \(k\in\mathbb Z\) and an explicit
integral particular solution \(v^*(y)\).

Proof. The actual right multiplication \(J(x)=x[\tau]\) swaps both
integer coefficients. Proposition 9 therefore applies to the unchanged
\(M_q\) and \(T_q\). At even length the residual map is identity;
apply \(C\) to \(y\) and solve the tail recurrence with initial value
\((C y)_0\). Both equivalences are invertible, giving uniqueness and
vanishing kernel and cokernel.

At odd length the residual map is
\[
a[1]+b[\tau]\longmapsto(a+b)([1]+[\tau]).
\]
Its kernel is exactly the primitive anti-diagonal
\(\mathbb Z([1]-[\tau])\), and its image is exactly the primitive
diagonal \(\mathbb Z([1]+[\tau])\). Zero tails force
\(v_i=(-1)^iv_0\), so the original kernel is precisely \(\mathbb Zw\).
The identity coefficient of \(v_0\) determines the generator coefficient.

Put \(z=(C y)_0\). Multiplication by \([\tau]\) negates coefficient
difference. Since \(q\) is odd, \(K_q\) consists of the positive even
suffix indices, and consequently
\[
\operatorname{coeff}_1(z)-\operatorname{coeff}_\tau(z)=\ell_q(y).
\]
When \(\ell_q(y)=0\), both coefficients of \(z\) equal an integer
\(d\). Choose \(v_0=d[1]\); then \((\mathrm{id}+J)v_0=z\).
The recurrence \(v_j=y_j-v_{j-1}\) constructs the particular solution.
Conversely, a residual in the image has equal coefficients, so
\(\ell_q\) vanishes on every image row. Subtracting a particular
solution reduces all solutions to the already classified kernel.

The row with coordinate zero \(k[1]\) and every other coordinate zero
has character \(k\), so \(\ell_q\) is onto \(\mathbb Z\).
The first isomorphism theorem gives the displayed cokernel equivalence.
The quotient is therefore torsion-free, not merely nonzero.

For \(q=1\), the transition is \(T_1(a,b)=(b,a)\), and
\(L_1(a,b)=(a+b,a+b)\). The image contains the primitive diagonal
vector \((1,1)\), since \(L_1(1,0)=(1,1)\); it is not restricted to
even diagonal vectors. The vectors \((1,1),(1,-1)\) have determinant
\(-2\), so diagonalizing in that eigenframe would replace the original
lattice by an index-two sublattice. By contrast, Proposition 9 with
\(A=\mathbb Z\), \(J=\mathrm{id}\) and \(q=1\) really leaves
\(2\mathrm{id}\), with cokernel \(\mathbb Z/2\mathbb Z\).
The absence of order-two torsion in the reset case follows from the
actual swap on the original lattice, not from involutivity alone.

## Theorem 11. Native integral coordinates and signed time character

Let \(q>0\), \(M_q=(\mathbb Z[C_2])^q\), and retain the original
right-row transition \(T_q\) and stationary group \(G_q\) of Definition 1.
For \(q=n+1\), define
\[
 P_q(y)=\bigl(y_1,\ldots,y_n,
              y_0[\tau]-\sum_{j=1}^{n}y_j\bigr).
\]
Then \(P_qT_q=T_qP_q=\mathrm{id}\), and there is an integer-linear
equivalence \(F_q:G_q\to M_q\) whose inverse is the original stage-zero
map and which satisfies
\[
 F_q(\operatorname{of}_m(v))=P_q^m v,
 \qquad F_q\Theta_q=T_qF_q.
\]
For odd \(q\), put \(\Lambda_q=\ell_qF_q\), with the primitive
character \(\ell_q\) of Theorem 10. Then
\[
 \Lambda_q(\operatorname{of}_m(v))=(-1)^m\ell_q(v),\qquad
 \Lambda_q\Theta_q=-\Lambda_q,
\]
and \(\Lambda_q:G_q\to\mathbb Z\) is surjective.

Proof. Right multiplication by \([\tau]\) is involutive. The sum of the
coordinates of \(P_qy\) is \(y_0[\tau]\), so the head of \(T_qP_qy\)
is \(y_0\), and its remaining coordinates are \(y_1,\ldots,y_n\).
Conversely, the first \(n\) coordinates of \(P_qT_qv\) recover the
first \(n\) coordinates of \(v\); its last coordinate is the total sum
minus that recovered prefix, hence \(v_n\). These statements also apply
to the empty prefix at \(q=1\).

The endomorphism identity
\(P_q^jT_q^{j-i}=P_q^i\), for \(i\le j\), makes \(P_q^m\) a
compatible family on the original forward stationary system. Its induced
map is \(F_q\). It is inverse to stage zero because
\[
 \operatorname{of}_0(P_q^m v)
   =\operatorname{of}_m(T_q^mP_q^m v)=\operatorname{of}_m(v).
\]
Since the two inverses commute, the same stage calculation proves the time
intertwining. By Theorem 10,
\(\ell_q(v+T_qv)=0\), so \(\ell_qT_q=-\ell_q\).
Substitute \(P_qv\) to get \(\ell_qP_q=-\ell_q\), and iterate.
Surjectivity follows from the surjectivity of \(\ell_q\) and \(F_q\).
The universal property of the module direct limit and the first isomorphism
theorem used here are the standard module constructions; the inverse and
character formulas concern this specific original reset transition.

This is an equivalence of integer modules, without a coordinatewise cone
claim. For \(q=2\), the nonnegative row \((0,[1])\) is sent by \(P_2\)
to \(([1],-[1])\). Moreover, an unsigned stage prescription cannot replace
\(\Lambda_q\). At \(q=1\), \(T_1([1])=[\tau]\) and
\(\operatorname{of}_0([1])=\operatorname{of}_1([\tau])\), whereas their
unsigned finite characters are \(1\) and \(-1\).

## Theorem 12. Complete native integral defect and arithmetic index

Write \(D_q=\mathrm{id}+\Theta_q\) and
\(c_q=\operatorname{of}_0(w)\), retaining the original class of
Proposition 4. For positive even \(q\), \(D_q\) is an integer-linear
bijection. For positive odd \(q\),
\[
 \ker D_q=\mathbb Zc_q,\qquad
 \operatorname{im}D_q=\ker\Lambda_q,\qquad
 G_q/\operatorname{im}D_q\cong\mathbb Z.
\]
The coefficient of \(c_q\) in the kernel is unique. If
\(\Lambda_q(y)=0\), all solutions of \(D_qx=y\) are exactly
\[
 x=F_q^{-1}\bigl(v^*(F_qy)\bigr)+kc_q,\qquad k\in\mathbb Z,
\]
with unique \(k\), where \(v^*\) is the particular finite solution of
Theorem 10. The exact kernel-character pairing and combined quotient are
\[
 \Lambda_q(c_q)=q+1,\qquad
 \ker D_q\cap\operatorname{im}D_q=\{0\},\qquad
 G_q/(\operatorname{im}D_q+\ker D_q)
    \cong\mathbb Z/(q+1)\mathbb Z.
\]
In particular,
\[
 x\in\operatorname{im}D_q+\ker D_q
 \quad\Longleftrightarrow\quad
 (q+1)\mid\Lambda_q(x).
\]

Proof. The equivalence of Theorem 11 gives
\(F_qD_q=(\mathrm{id}+T_q)F_q\) and \(F_qc_q=w\).
Transport the whole finite classification of Theorem 10, including its
constructive solver, unique kernel coefficient and surjective character.
This yields the native kernel, image, fibres and ordinary cokernel; no
second finite elimination is needed.

For the pairing, the contribution of suffix \(i\) in \(w\) is two
when \(i\) is even and zero when it is odd. Equivalently it is
\(1+(-1)^i\). Therefore
\[
 \ell_q(w)=\sum_{i<q}\bigl(1+(-1)^i\bigr)=q+1
\]
for odd \(q\). If \(kc_q\) belongs to the image, its character is zero,
so \(k(q+1)=0\), forcing \(k=0\). If
\(x=a+kc_q\), with \(a\) in the image, then
\(\Lambda_q(x)=k(q+1)\). Conversely, if
\(\Lambda_q(x)=k(q+1)\), the difference \(x-kc_q\) has zero
character and lies in the image. Thus reduction of \(\Lambda_q\)
modulo \(q+1\) has kernel exactly the actual sum of the two submodules.
It is onto, and the first isomorphism theorem gives the combined quotient.

At \(q=1\), the native coordinates are \(\mathbb Z^2\), genuine time
swaps the coordinates, \(c_1=(1,-1)\), and
\(\Lambda_1(a,b)=a-b\). The ordinary cokernel is \(\mathbb Z\);
the combined quotient has order two. Thus a zero intersection does not make
the image and kernel a decomposition of the entire integer lattice.
The obstruction is the exact index \(q+1\), not torsion in the ordinary
cokernel and not a rational spectral obstruction.

## Theorem 13. Integral equivariant nonsplitting

For positive odd \(q\), there is no integer-linear section
\(s:\mathbb Z\to G_q\) satisfying
\[
 \Lambda_qs=\mathrm{id}_{\mathbb Z},\qquad
 \Theta_qs(n)=s(-n)\quad(n\in\mathbb Z).
\]
Here the action on \(\mathbb Z\) is negation and the action on \(G_q\)
is the original genuine time action.

Proof. Equivariance and additivity imply
\(D_qs(1)=s(1)+s(-1)=0\). The full kernel classification gives
\(s(1)=kc_q\). Applying the section equation and the pairing yields
\(1=k(q+1)\), impossible for \(q>0\).

The underlying integer-linear surjection does split after forgetting time:
choose \(e\in G_q\) with \(\Lambda_q(e)=1\) and send \(n\) to
\(ne\). The assertion also requires additivity. At \(q=1\), the
nonadditive set map
\(n\mapsto(\max(n,0),\max(-n,0))\) is a section of \(a-b\) and
intertwines negation with coordinate swap. The arithmetic index therefore
obstructs a linear dynamic splitting, without forbidding equivariant set
sections or a nonequivariant linear section.

## Theorem 14. Integral normal form of two genuine time steps

Let $A$ be an additive commutative group and $J:A\to A$ additive with
$J^2=I$. On $A^q$, genuine time is
$(Tv)_0=J(\sum_i v_i)$ and $(Tv)_{i+1}=v_i$. Put $L_2=I+T^2$.
For $q\ge2$, two independently defined integral additive equivalences on
its domain and codomain reduce $L_2$ to an identity tail and the following
head operator:

| $q\bmod4$ | Head on $A^2$ |
| --- | --- |
| $0$ | $I$ |
| $1$ | $\operatorname{diag}(2I,I)$ |
| $2$ | $\operatorname{diag}(3I+2J,I)$ |
| $3$ | $\operatorname{diag}(I+J,I+J)$ |

At $q=1$, the operator is $2I$. This is equivalence on two sides, with
no conjugacy assertion; the domain and codomain transformations differ.
No torsion-free hypothesis is imposed on $A$.

Proof. Write $a=v_0$, $b=v_1$, and $t_j=v_{j+2}+v_j$. Reconstruct by
$v_{j+2}=t_j-v_j$. This is an integral additive equivalence onto the two
seeds and the $q-2$ tails. Subtract from the two image heads the actual
$L_2$ image of the zero-seed reconstructed tail. The remaining homogeneous
coordinates repeat $a,b,-a,-b$. An induction in the length gives

$$
(S,v_{q-1})=
\begin{cases}
(0,-b)&q\equiv0,\\
(a,a)&q\equiv1,\\
(a+b,b)&q\equiv2,\\
(b,-a)&q\equiv3
\end{cases}\pmod4,
\qquad S=\sum_i v_i.
$$

The two residual heads are $(a+S+J(S-v_{q-1}),b+JS)$. For residues zero,
one, two and three, respectively, use the domain head coordinates
$(a+Jb,b)$, $(a,b+Ja)$, $(a,b+2a+Ja)$ and $(a+b,b)$.
For residue two use the codomain head shear $(r,s)\mapsto(r+Jr-s,r)$;
in the other residues leave the residual heads alone. Each change has an
integer additive inverse. Direct substitution with $J^2=I$ gives the
table. The other coordinates remain identity. At length one $T=J$,
so $I+T^2=2I$.

## Theorem 15. Ordinary two-step kernel and cokernel on the original group

For the original right-row lattice $M_q=\mathbb Z[C_2]^q$ and its genuine
transition, put $L_{2,q}=I+T_q^2$. At every $q>0$, its ordinary kernel and
cokernel are:

| $q\bmod4$ | $\ker L_{2,q}$ | $M_q/\operatorname{im}L_{2,q}$ |
| --- | --- | --- |
| $0$ | $0$ | $0$ |
| $1$ | $0$ | $(\mathbb Z/2\mathbb Z)^2$ |
| $2$ | $0$ | $\mathbb Z/5\mathbb Z$ |
| $3$ | $\mathbb Z^2$ | $\mathbb Z^2$ |

The same table holds on the original stationary dimension group $G_q$
for $I+\Theta_q^2$. In particular this operator is bijective exactly when
$4\mid q$. Ordinary cokernel here means quotient by the image alone.

Proof. Specialize Theorem 14 to right multiplication by $[\tau]$.
The literal basis $[1],[\tau]$ is retained. The eigenvectors
$[1]+[\tau],[1]-[\tau]$ have index two and cannot serve as an integral
basis. The residue-two block has literal matrix

$$
3I+2J=\begin{pmatrix}3&2\\2&3\end{pmatrix}.
$$

Its zero equations force both input coefficients to vanish. A target
$(r,s)$ lies in its image exactly when $5\mid r+s$: necessity follows
by adding the image equations, and if $r+s=5k$ then the integral preimage
is $(r-2k,s-2k)$. This proves the exact image without division or a
claim based only on the determinant. The residue-one block doubles both
literal coefficients. Each residue-three block is the length-one
$I+J$ operator from Theorem 10, whose kernel is generated by
$[1]-[\tau]$ and whose cokernel is the coefficient difference in
$\mathbb Z$. There are two independent blocks. The domain reconstruction
returns their two primitive parameters to the original row lattice.

The independent codomain coordinates give an onto arithmetic readout
with kernel exactly the image, so the first isomorphism theorem gives
the displayed cokernels. The stage-zero integral equivalence in
Theorem 11 intertwines $T_q$ and $\Theta_q$, hence transports both kernel
and ordinary image quotient. Every nonzero cokernel in the table
prevents surjectivity, while the residue-zero normal form is identity
and has zero kernel. At $q=1$ the full defect is doubling on $\mathbb Z^2$.

## Theorem 16. Primitive five-character and the actual time action

Suppose $q\equiv2\pmod4$. Let $\operatorname{aug}(x)$ be the sum of the
literal sign coefficients and let $w_i\in\mathbb Z/5\mathbb Z$ repeat
$1,2,0,4$ in original vertex order. Define

$$
\nu_q(x)=\sum_{i<q}w_i\operatorname{aug}
\bigl((\operatorname{resetNativeEquiv}_q x)_i\bigr).
$$

This is an onto integer-linear map, and

$$
\ker\nu_q=\operatorname{im}(I+\Theta_q^2),\qquad
\nu_q(\Theta_qx)=3\nu_q(x).
$$

Thus the ordinary cyclic-five quotient has genuine time action given by
multiplication by three. Its nonzero residues form the four-phase orbit
$1\mapsto3\mapsto4\mapsto2\mapsto1$.

Proof. First work in the original row lattice. Augmentation is unchanged
by right multiplication by $[\tau]$. The weights satisfy
$w_{i+1}=3w_i-1$, while $w_0=1$ and $w_{q-1}=2$. Expanding the actual reset
head and successor coordinates makes all nonterminal terms telescope;
the terminal equality is $3\cdot2=1$ modulo five. Hence the character
of $T_qv$ is three times that of $v$. An integer coefficient at vertex
zero and sign one reaches every residue, proving primitivity. Applying
time twice shows the character of $(I+T_q^2)v$ is zero, since
$1+3^2=0$ modulo five. To prove the reverse inclusion, descend the
character to the independently computed ordinary cokernel from
Theorem 15. This is an onto map from a five-element group to itself,
hence injective; its kernel is zero. Transport through the same native
equivalence proves both assertions on $G_q$.

The full representation from Definition 5 satisfies
$\rho_q(\operatorname{unitShift})=\Theta_q$, and multiplicativity gives
the actual squared shift. If an actual history element $h$ had
$\rho_q(h)=I+\Theta_q^2$, its image would be an integral equivalence,
so Theorem 15 forces $4\mid q$. This is only a necessary condition;
no converse history realization is proved. Complement is not substituted
for time, and $I+\Theta_q^2$ is not $(I+\Theta_q)^2$.

These are repository-derived recurrence and integral-lattice results.
Pinned Mathlib supplies finite sums, additive equivalences, quotient
isomorphisms and finite surjective-to-injective conversion. The source
interfaces inspected outside the repository do not supply this exact
normal form or clock. No literature novelty, full representation image,
Gaussian image-plus-kernel quotient or arbitrary-time classification is
claimed.

## 追加锚（本行以下为增补区）

## Theorem 17. The oriented integral ring of the native square quotient

For every $q>0$, including $q=1$, write

$$
S_q=\sum_{k<q}X^k,\qquad F_q=X^{2q}-S_q^2,\qquad
W_q=S_q-(X-1)X^q,\qquad H=X^2+1.
$$

Let $N_q$ be the original integer dimension group, $\Theta_q$ its forward
time and $U_q$ its literal sign action. Its normalized integer chart
$\Phi_q:\mathbb Z[X]/(F_q)\to N_q$ sends $1$ to the original stage-zero
vector $g_q$ and intertwines multiplication by $X$ with $\Theta_q$.
The literal sign intertwines with multiplication by $W_q$.
Put $L_q=I+\Theta_q^2$. There is an onto integer-linear map
$\eta_q:N_q\to A_q$ with

$$
\ker\eta_q=\operatorname{im}L_q,\qquad \eta_q(g_q)=1,
$$

where the following table fixes the ring and its orientations:

| $q\bmod4$ | $A_q$ | Forward time $t_q$ | Literal sign $u_q$ |
| --- | --- | --- | --- |
| $0$ | $\mathbb Z/1\mathbb Z$ | $1=0$ | $1=0$ |
| $1$ | $(\mathbb Z/2\mathbb Z)[C_2]$ | $[\tau]$ | $[\tau]$ |
| $2$ | $\mathbb Z/5\mathbb Z$ | $3$ | $1$ |
| $3$ | $\mathbb Z[i]$ | $i$ | $-1$ |

For every $p\in\mathbb Z[X]$ and $z\in N_q$,

$$
\eta_q(p(\Theta_q)z)=p(t_q)\eta_q(z),\qquad
\eta_q(U_qz)=u_q\eta_q(z).
$$

The canonical additive quotient $N_q/\operatorname{im}L_q$ is identified
with $A_q$. Its ring structure is transported through this proved
identification; no ring structure on the original $N_q$ is assumed.
Both ring maps are inverse and preserve one, integer coefficients and
all polynomials. Original quotient addition is preserved.

Put $d_q=(1,2,4,4)_{q\bmod4}$ and let $\sigma_q$ be the actual
forward history shift. The element $t_q$ is a unit, with inverse
$1,[\tau],2,-i$ in residue order. Every $a\in A_q^\times$ has an
exponent $0\le j<d_q$ such that

$$
a=t_q^j,\qquad \eta_q\bigl(\rho_q(\sigma_q^j)g_q\bigr)=a.
$$

Here the second equality uses the underlying ring value of the unit.

Proof. First work in $\mathbb Z[X]/(H)$ and put $t=[X]$. Here
$t^2=-1$, $t^4=1$, and $1+t+t^2+t^3=0$. Splitting the geometric sum
into four-term blocks proves $[S_{q+4}]=[S_q]$. Induction therefore reduces
$S_q$ to $S_{q\bmod4}$, while $t^q=t^{q\bmod4}$. Direct substitution gives

$$
[F_q]=(1,-2,1-2t,0),\qquad
[W_q]=(1-t,2+t,2t,-1)
$$

in residue order. Consequently $(F_q,H)=(r_q,H)$, with $r_q$ the
displayed literal polynomial residue. This is an integral ideal equality:
the difference $F_q-r_q$ lies in $(H)$, which proves both inclusions.
For residue two the further equality $(H,1-2X)=(5,X-3)$ follows in both
directions from

$$
\begin{aligned}
5&=4H+(2X+1)(1-2X),\\
X-3&=-3(1-2X)-5X,\\
1-2X&=-2(X-3)-5,\\
H&=(X-3)(X+3)+10.
\end{aligned}
$$

Residue zero gives the whole ideal. For residue one, reduce the integer
coefficients modulo two and send $X$ to $[\tau]$. The reverse ring map
sends $[\tau]$ to $[X]$ and coefficients to their constant classes.
The relations $2=0$ and $X^2=1$ make this map well-defined. Checking both
composites on integer coefficients and the two group elements proves
that the maps are inverse. For residue two evaluation at three identifies
$\mathbb Z[X]/(5,X-3)$ with $\mathbb Z/5\mathbb Z$, with the inverse given
by constant classes. For residue three the forward map evaluates at
$i$; the inverse sends $a+bi$ to $a+b[X]$. The relation $[X]^2=-1$
proves multiplicativity, and checking the composites on $i$, constants
and $X$ gives the inverse laws. These maps send the displayed residues
of $W_q$ to exactly the sign entries in the table.

The ring third-isomorphism theorem identifies
$(\mathbb Z[X]/(F_q))/([H])$ with $\mathbb Z[X]/(F_q,H)$, retaining the
canonical polynomial projection. The normalized native chart gives

$$
L_q\Phi_q(b)=\Phi_q([H]b).
$$

An ideal witness $[H]b=\Phi_q^{-1}(x)$ therefore supplies the actual
native preimage $\Phi_q(b)$. Conversely $x=L_qy$ supplies the ideal
witness $\Phi_q^{-1}(y)$. These are both kernel directions on the original
integer group. Surjectivity follows from the polynomial quotient
projection and $\Phi_q$. The additive first-isomorphism theorem gives
the original image quotient, through which multiplication is transported.
Normalization at $1$, forward time, every polynomial and the literal
sign follows along these same maps.

For an original stage-$n$ vector $v$, its chart coordinate is the cyclic
coordinate polynomial of $T_q^{-n}v$, transported through the literal
sign-to-integer polynomial ring equivalence. Applying the same quotient
projection gives its arithmetic coordinate. Thus later stages retain
inverse time; $t_q$ continues to denote forward time. No division by
$X-1$, rational sign splitting, cardinality argument or unit-square
quotient is used.

For the unit assertion, the zero ring has a single unit. In
$(\mathbb Z/2\mathbb Z)[C_2]$, write an element as $a+b[\tau]$.
The augmentation homomorphism takes a unit to a unit, so $a+b=1$;
the two binary coefficient possibilities leave exactly $1$ and
$[\tau]$. In $\mathbb Z/5\mathbb Z$, the four nonzero elements are
$3^0,3^1,3^2,3^3=1,3,4,2$. For a Gaussian unit $a+bi$, the norm-one
criterion gives $a^2+b^2=1$. Thus $-1\le a,b\le1$ and the integer
solutions give $1,i,-1,-i$. These are precisely the displayed bounded
powers of $t_q$. Finally $\rho_q(\sigma_q)=\Theta_q$, multiplicativity,
the polynomial action law and $\eta_q(g_q)=1$ give
$\eta_q(\rho_q(\sigma_q^j)g_q)=t_q^j$. This realizes every arithmetic
unit by an actual history shift at the normalized native generator.

## Theorem 18. Converse realization correcting the limitation in Theorem 16

For every $q>0$, an actual full numbered-history homeomorphism $h$ with

$$
\rho_q(h)=I+\Theta_q^2
$$

exists if and only if $4\mid q$. This replaces the final no-converse
limitation in Theorem 16; its five-character assertions are unchanged.

Proof. Necessity is Theorem 15, since the image of a homeomorphism under
$\rho_q$ is an integer-linear equivalence. For sufficiency use the
existing two-step numbered-history endpoint realization at $4\mid q$
([D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.TwoStep.rho_eq](../../../D5/S3/ConceptDynamics/Coding/ResetTwoStepArithmetic.lean#L919)).
Its set-image action on every original beam generator is the sum of that
generator and its two forward-time image. Those generators generate the
original integer dimension group, giving $\rho_q(h)=I+\Theta_q^2$.

## 追加锚（本行以下为增补区）
