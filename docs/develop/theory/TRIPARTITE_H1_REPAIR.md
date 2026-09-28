# Complete-tripartite degree-one cochains and octahedral repair

Let $A,B,C$ be nonempty sets. An edge cochain over $\mathbf F_2$ has three
components $f_{AB}:A\times B\to\mathbf F_2$,
$f_{AC}:A\times C\to\mathbf F_2$, and
$f_{BC}:B\times C\to\mathbf F_2$. Its defect at $(a,b,c)$ is
$d_1f(a,b,c)=f_{AB}(a,b)+f_{AC}(a,c)+f_{BC}(b,c)$. A vertex potential
$g=(p,q,r)$ has $d_0g=(p+q,p+r,q+r)$.

**Theorem 1 (degree-one exactness).** The defect vanishes at every triangle
if and only if $f=d_0g$ for a single vertex potential. One direction is the
characteristic-two cancellation $d_1d_0=0$. For the converse choose anchors
$a_0,b_0,c_0$ and put
$p(a)=f_{AB}(a,b_0)$,
$q(b)=f_{AB}(a_0,b)+f_{AB}(a_0,b_0)$, and
$r(c)=f_{AC}(a_0,c)+f_{AB}(a_0,b_0)$. The triangle equations at the anchors
give all three edge identities.

Now let $A=B=C=\{0,1\}$. Write $R(f)$ for the least edge support weight in
$f+\operatorname{im}d_0$ and $T(f)$ for the number of defective triangles.

**Theorem 2 (antipodal defect fibers and their minimum representatives).**
Let $x=(a,b,c)$ and $\bar x=(1-a,1-b,1-c)$. Define $w_x$ by its exact
support: the AB edge $(1-a,1-b)$, the AC edge $(1-a,c)$, and the BC edge
$(b,c)$, each with value one. Its defects are exactly $x$ and $\bar x$,
so $\operatorname{wt}(w_x)=3$ and $T(w_x)=2$. For every $f$ whose defects
are exactly this pair, every potential $g$ satisfies
$3\leq\operatorname{wt}(f+d_0g)$, and some potential satisfies
$f+d_0g=w_x$. Consequently $R(f)=3$ on this entire defect fiber.

**Proof.** The three path edges have boundary $x+\bar x$: each intermediate
dual cube vertex occurs twice. Summing defects over the half-cube with A
coordinate $a$ gives the parity of the BC edge family, since every AB and
AC term occurs twice. Exactly one of the two defects lies in that half-cube,
so the BC family contains a nonzero edge. The analogous B and C cuts force
nonzero AC and AB edges. Coboundaries preserve defects, giving the lower
bound for every repair. Finally $d_1(f+w_x)=0$, and Theorem 1 gives a single
potential attaining $w_x$.

The choice $x=(1,0,0)$ gives the explicit cochain $w$ with
$w_{AB}(0,1)=w_{AC}(0,0)=w_{BC}(0,0)=1$ and no other supported edges.
Its defects are $(0,1,1)$ and $(1,0,0)$; every repair has weight at least
three, and the zero potential attains three.

**Theorem 3 (exact octahedral repair coefficient).** For natural numbers
$p,q$, including $q=0$,

$$
\bigl(\forall f\;\exists g,\quad
q\operatorname{wt}(f+d_0g)\leq pT(f)\bigr)
\quad\Longleftrightarrow\quad 3q\leq2p.
$$

**Proof.** The upper estimate $2R(f)\leq3T(f)$ is prior literature:
Dotterrer--Kahle, *Coboundary expanders* (2012), Proposition 5.5,
DOI 10.1142/S1793525312500197, at $n=3,k=1$. Their norms count support;
normalizing by the numbers of edges and triangles changes the coefficient.
Here is a structural derivation of this premise in the present cochain
coordinates. The total defect sum is zero because every edge belongs to
two triangles. Hence the defect set has even cardinality. Remove two
defective dual cube vertices and join them by a path changing each coordinate
at most once. The path has at most three edges and boundary precisely the
selected pair. Induction on the remaining defect set constructs a cochain
$h$ with $d_1h=d_1f$ and $2\operatorname{wt}(h)\leq3T(f)$; adding paths
cannot increase support beyond the sum of their lengths. Apply Theorem 1
to $f+h$ to obtain a potential with $f+d_0g=h$. If $3q\leq2p$, multiply
this upper estimate to obtain the claimed repair inequality. Conversely,
apply any universal repair inequality to the explicit cochain $w$ above.
Theorem 2 and $T(w)=2$ give $3q\leq2p$. Thus the published upper estimate
and the cut obstruction determine the exact coefficient together.

No claim is made here for a min-part coefficient on arbitrary finite parts.
