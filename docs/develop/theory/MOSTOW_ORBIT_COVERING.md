# Isometric representations and orbit coverings

This volume fixes the bridge between a homomorphism into the isometry group
and the orbit covering used to model a hyperbolic manifold by its universal
cover. It proves a conditional covering statement; it does not assert that a
finite-volume hyperbolic lattice satisfies the stated hypotheses.

## 1. The representation action

**Definition 1.1.** Let (G) be a group, (X) a metric space, and
(ho:G\to\operatorname{Isom}(X)) a homomorphism. Its associated action is
(g\cdot x=\rho(g)(x)). Write (X/\rho) for the equivalence classes of the
relation (x\sim_\rho y\iff \exists g,\rho(g)(x)=y).

**Theorem 1.2 (comparison of the two orbit conventions).** The relation
(x\sim_\rho y) agrees with the standard group-action relation
(x\in G\cdot y). The resulting orbit quotients are canonically homeomorphic
with their quotient topologies.

**Proof.** If (y=\rho(g)(x)), then (x=\rho(g^{-1})(y)). Conversely, invert
the witness in the same way. The identity on representatives therefore
respects both equivalence relations and induces mutually inverse maps of the
quotients. Each map is continuous by the defining quotient topology. The
group-action quotient construction and its topology are standard; the
comparison here identifies its convention with the quotient fixed above.

## 2. Covering projection

**Definition 2.1.** The representation is *free* if
(\rho(g)(x)=x\Rightarrow g=1) for every (g,x). It is *properly
discontinuous* if, for all compact (K,L\subseteq X), the set

\[
\{g\in G:(\rho(g)(K)\cap L)\ne\varnothing\}
\]

is finite.

**Theorem 2.2 (covering bridge).** Suppose (X) is Hausdorff and locally
compact. If the isometric representation is free and properly discontinuous,
then the canonical projection (X\to X/\rho) is a covering map.

**Proof.** Under the action in Definition 1.1, freeness is the cancellation
condition for scalar multiplication, proper discontinuity is the compact-set
condition for the action, and each action map is continuous because it is an
isometry. The standard covering theorem for free, properly discontinuous
group actions applies to the standard orbit quotient. Transport its covering
projection across the homeomorphism of Theorem 1.2.

The theorem supplies a topological covering map. It does not establish a
hyperbolic metric or smooth quotient structure, finite volume, or rigidity of
the acting lattice.

## 追加锚（本行以下为增补区）

## 3. Upper half-space metric and horizontal isometries

**Definition 3.1.** Let (E) be a real inner product space. Put
(U_E=\{(x,t)\in E\times\mathbb R:t>0\}), with the Euclidean product distance
(d_2), and write (h(x,t)=t). For (p,q\in U_E), define

\[
 d_H(p,q)=2\operatorname{arsinh}
 \frac{d_2(p,q)}{2\sqrt{h(p)h(q)}}.
\]

For (q=(y,s)), write (q^*=(y,-s)) for reflection in the boundary plane.

**Theorem 3.2 (Ptolemy construction of the metric).** The function (d_H) is a
metric on (U_E), for every real inner product space (E).

**Proof.** The Euclidean product distance gives
(d_2(p,q^*)^2=d_2(p,q)^2+4h(p)h(q)). Thus

\[
 \sinh\frac{d_H(p,q)}2
 =\frac{d_2(p,q)}{2\sqrt{h(p)h(q)}},\qquad
 \cosh\frac{d_H(p,q)}2
 =\frac{d_2(p,q^*)}{2\sqrt{h(p)h(q)}}.
\]

Ptolemy's inequality for the four Euclidean points (p,q,r,q^*) states

\[
 2h(q)d_2(p,r)\leq
 d_2(p,q)d_2(r,q^*)+d_2(q,r)d_2(p,q^*).
\]

Divide by (4h(q)\sqrt{h(p)h(r)}), which is positive. The hyperbolic sine
addition formula turns the right side into
(\sinh((d_H(p,q)+d_H(q,r))/2)); the left side is
(\sinh(d_H(p,r)/2)). Strict monotonicity of hyperbolic sine proves the
triangle inequality. Symmetry follows from symmetry of (d_2) and the height
product. Since (\operatorname{arsinh}(z)=0) exactly when (z=0), positivity of
the heights makes (d_H(p,q)=0) equivalent to (p=q).

**Theorem 3.3 (horizontal translation action).** For (u\in E), let
(T_u(x,t)=(x+u,t)). Each (T_u) preserves (d_H). The assignment
(u\mapsto T_u) is a homomorphism from the additive group of (E) to the
isometry group of (U_E,d_H), and (T_u(p)=p) for one point (p) if and only if
(u=0).

**Proof.** Translation preserves height and Euclidean product distance,
hence the formula in Definition 3.1. Direct substitution gives
(T_0=\operatorname{id}) and (T_{u+v}=T_u\circ T_v). If (T_u(x,t)=(x,t)),
then (x+u=x), so (u=0); the converse follows from (T_0=\operatorname{id}).

## 4. Positive dilations

**Theorem 4.1 (positive dilation isometry).** For every positive real (a),
the map (D_a(x,t)=(ax,at)) preserves the upper half-space distance of
Definition 3.1 and is an isometric bijection with inverse (D_{a^{-1}}).

**Proof.** Positivity gives (at>0). Euclidean product distances satisfy
(d_2(D_a p,D_a q)=a d_2(p,q)), while the geometric mean of the heights
satisfies (\sqrt{h(D_a p)h(D_a q)}=a\sqrt{h(p)h(q)}). The two factors cancel
inside the inverse hyperbolic sine defining (d_H), proving distance
preservation. Since (a^{-1}>0), both composites of (D_a) and (D_{a^{-1}})
are the identity on coordinates.

## 5. Inversion centered on the boundary

**Theorem 5.1 (boundary-centered inversion isometry).** Let (E) be a real
inner product space and (U_E) the upper half-space of Definition 3.1. For
(p=(x,t)\in U_E), put (r(p)=d_2(p,0)>0) and

\[
 J(p)=r(p)^{-2}p.
\]

Then (J(p)\in U_E), (J(J(p))=p), and
(d_H(J(p),J(q))=d_H(p,q)) for every (p,q\in U_E). Thus (J) is an
involutive isometric equivalence.

**Proof.** Since (t>0), the ambient point (p) is nonzero, so (r(p)>0) and
(h(J(p))=h(p)/r(p)^2>0). Euclidean sphere inversion about the origin of
radius one is involutive and gives

\[
 d_2(J(p),J(q))=\frac{d_2(p,q)}{r(p)r(q)}.
\]

The positive square root of the product of the new heights is
(\sqrt{h(J(p))h(J(q))}=\sqrt{h(p)h(q)}/(r(p)r(q))). Substituting both
identities into Definition 3.1 cancels the same factor in the numerator
and denominator. The involution and distance identity give the stated
isometric equivalence. The cancellation for arbitrary (E) is the new
geometric content; Mathlib supplies the Euclidean inversion identities.

## 6. Completeness of upper half-space

**Theorem 6.1 (complete horizontal space gives complete hyperbolic space).**
Let (E) be a complete real inner product space. Then the upper half-space
(U_E,d_H) of Definition 3.1 is a complete metric space. For all (p,q),

\[
 |\log h(p)-\log h(q)|\leq d_H(p,q).
\]

In particular, a hyperbolic Cauchy sequence cannot approach the height-zero
boundary.

**Proof.** The Euclidean separation is at least the separation of the two
heights. Compare the distance formula with the vertical-line formula in
the ordinary upper half-plane, where the distance is the absolute
difference of the logarithms of the heights. Thus log-height is
1-Lipschitz. Exponentiating gives
(h(p)\leq h(q)\exp d_H(p,q)). For a hyperbolic Cauchy sequence (p_n), its
hyperbolic distances are bounded, so its heights admit a common positive
upper bound (B). The defining distance identity then gives

\[
 d_2(p_n,p_m)
 =2\sqrt{h(p_n)h(p_m)}\sinh\frac{d_H(p_n,p_m)}2
 \leq 2B\sinh\frac{d_H(p_n,p_m)}2.
\]

Consequently the Euclidean coordinates form a Cauchy sequence, and
completeness of (E\times\mathbb R) supplies a limit. The logarithms of the
heights also converge, say to (a), so the limit height is (\exp a>0).
Finally the distance formula, continuity of square root and inverse
hyperbolic sine, and positivity of the limiting height show convergence
in (d_H). This establishes metric completeness of the model; it does not
establish manifold curvature, quotient completeness, finite volume or
Mostow--Prasad rigidity.
