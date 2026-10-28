# Six-read constant-drift recovery and different-slope collisions

Six exact scalar reads on one predetermined forward history recover the complete effective target for constant additive drift and every real affine-gain slope. On that same history, allowing affine additive drift produces a different phenomenon: every prescribed-slope slice is injective, but distinct positive slopes have explicit positive-source collisions. The unrestricted minimum over all fixed histories remains unresolved.

## 1. Common source, reading clock, and elementary interfaces

**Definition 1.1 (model and recovery target).** Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

The effective relation is one matrix

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},\qquad
p,q,r,s>0,\qquad ps=qr.
$$

For a known integer $d\ge0$, the observations are

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\qquad \kappa\in\mathbb R,\qquad \deg D\le d.
$$

The degree bound includes the zero polynomial. The target is exactly $(S,\kappa,D)$, including the entire polynomial $D$. In original parameters, $S=\alpha R$ and $\kappa=\beta/\alpha$, where $\alpha>0$ and $R$ is strictly positive of rank one.

The initial cumulative matrix is $A_0=I$, and its read is counted. Between recorded reads one executes a predetermined finite word in $M,J$, possibly empty, on the left of the current cumulative matrix. A product is executed from right to left: the chronological pair $(M,J)$ has multiplier $JM=U$. Every recorded read advances the consecutive index $i$ once, including a repeat at an unchanged matrix. Unread atoms do not advance this clock. There is one object column and one fixed instrument row in each run. No reset, copy, inverse acquisition, extra clock, or data-dependent acquisition is allowed. Different candidate realizations may have different fixed rows.

**Lemma 1.2 (one-source coordinates and legal states).** Every allowed $S$ has the unique coordinates

$$
x=\frac pr>0,\qquad y=\frac sr>0,\qquad
S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix},\qquad r>0.
$$

It has a positive factorization with one fixed row, and every intermediate state on every legal word remains positive. Every legal word matrix has nonnegative integer entries and determinant $1$ or $-1$.

**Proof.** The rank-one equation gives $q=ps/r=rxy$, proving the coordinates. Take

$$
c=\begin{pmatrix}rx\\r\end{pmatrix},\qquad \ell=(1,y).
$$

Then $c\ell=S$. For an arbitrary matrix $C=(\begin{smallmatrix}a&b\\c_0&e\end{smallmatrix})$,

$$
\operatorname{tr}(CS)=ap+br+c_0q+es=\ell Cc.
$$

Both atoms preserve positive columns, because

$$
M\binom{c_1}{c_2}=\binom{c_2}{c_1+c_2},\qquad
J\binom{c_1}{c_2}=\binom{c_2}{c_1}.
$$

Thus the same fixed row realizes all read and unread states. Taking $\alpha=1$, $\beta=\kappa$, and $R=S$ realizes every effective target in original parameters. Both atoms are nonnegative integer matrices of determinant $-1$; products preserve those entry properties and multiply determinants, and the empty product is $I$. ∎

**Lemma 1.3 (complete representation scales).** For any fixed effective target $(S,\kappa,D)$, its original relation/gain representations are exactly

$$
R=S/t,\qquad \alpha=t>0,\qquad \beta=\kappa t,\qquad D\text{ fixed}.
$$

For a fixed positive relation $R=c\ell$, its positive factorizations differ exactly by $c'=\mu c$, $\ell'=\ell/\mu$, with $\mu>0$.

**Proof.** The equations $\alpha R=S$ and $\beta/\alpha=\kappa$ force the displayed representation with $t=\alpha$. Conversely substitution preserves every observation on every common operation history and recorded index. For the internal factorization, equality of the first positive columns in $c\ell=c'\ell'$ gives $c'=(\ell_1/\ell'_1)c=\mu c$, with $\mu>0$. Equality of the second columns then gives $\ell'_2=\ell_2/\mu$, while the definition of $\mu$ gives the first component as well. The converse follows by multiplying the factors. These representation scales do not identify distinct effective targets. ∎

**Lemma 1.4 (polynomial interpolation).** A nonzero polynomial of degree at most $n$ has at most $n$ distinct real roots. At distinct nodes $t_0,\ldots,t_n$, arbitrary values $v_0,\ldots,v_n$ have the unique degree-at-most-$n$ interpolant

$$
P(t)=\sum_{j=0}^n v_j
\prod_{\substack{0\le h\le n\\h\ne j}}
\frac{t-t_h}{t_j-t_h}.
$$

**Proof.** A root $t_j$ gives a factor $t-t_j$ by polynomial division. Each additional distinct root remains a root of the quotient, since its removed factor is nonzero there. Iteration proves the root bound. The displayed products are defined by distinctness of the nodes, equal one at their own nodes, and vanish at every other node. They therefore interpolate. The difference of two interpolants has $n+1$ distinct roots and degree at most $n$, so it is zero. The empty product for $n=0$ is one. Lower actual degrees, zero interpolants, and repeated roots elsewhere cause no exception. ∎

## 2. Six reads with constant additive drift

**Theorem 2.1 (global recovery for $d=0$).** The six cumulative matrices

$$
A_0=I,\quad A_1=U,\quad A_2=U,\quad
A_3=U^5MU,\quad A_4=U^6MU,\quad A_5=U^7MU
$$

recover the complete target $(S,\kappa,D)$ for every allowed positive rank-one $S$, every real $\kappa$, and every constant $D(t)=\delta$. A literal implementation uses seventeen atoms.

**Proof.** First specify the complete chronological history. Read $I$ at index $0$. Execute $M,J$ and read $U$ at index $1$. Execute the empty word and read $U$ at index $2$. Execute $M$ followed by five consecutive chronological pairs $(M,J)$, with no intervening reads, and read $U^5MU$ at index $3$. Execute one more pair $(M,J)$ and read $U^6MU$ at index $4$, then another such pair and read $U^7MU$ at index $5$. The atom counts between these reads are $2,0,11,2,2$, totaling $17$. This is a literal implementation count, with six recorded reads on the one clock of Definition 1.1.

Induction and multiplication give

$$
U^m=\begin{pmatrix}1&m\\0&1\end{pmatrix},\qquad
MU=\begin{pmatrix}0&1\\1&2\end{pmatrix},\qquad
U^mMU=\begin{pmatrix}m&1+2m\\1&2\end{pmatrix}.
$$

Consequently the terminal matrices, at their actual indices $i=3,4,5$, are

$$
A_i=\begin{pmatrix}i+2&2i+5\\1&2\end{pmatrix}.
$$

Lemma 1.2 realizes the entire history with one positive column and one fixed positive row.

Write $a=p+s=r(x+y)$ and set

$$
\widehat r=2z_1-z_2-z_0,\qquad H=z_2-z_1.
$$

The three prefix observations are

$$
z_0=a+\delta,\quad
z_1=(1+\kappa)(a+r)+\delta,\quad
z_2=(1+2\kappa)(a+r)+\delta.
$$

They give

$$
\widehat r=r>0,\qquad H=\kappa(a+r).
$$

Henceforth write $r=\widehat r$. Since $a+r>0$, $H=0$ is equivalent to $\kappa=0$. Neither identity divides by a gain.

Set

$$
Z=x+2>2,\qquad Y=p+2r=rZ,
$$

$$
L=2p+5r+q+2s=r\bigl[Z(y+2)+1\bigr].
$$

The terminal trace formula is $\operatorname{tr}(A_iS)=iY+L$. Let the unique quadratic interpolant through $(3,z_3),(4,z_4),(5,z_5)$ be

$$
Q(t)=\mathsf A t^2+\mathsf B t+\mathsf C.
$$

It is precisely $(1+\kappa t)(tY+L)+\delta$, because that polynomial has degree at most two and gives those three values. Thus

$$
\mathsf A=\kappa Y,\qquad
\mathsf B=Y+\kappa L,\qquad
\mathsf C=L+\delta.
$$

This interpolation uses the terminal formula at indices $3,4,5$; it makes no assertion that their matrices were used at any earlier index. With $h=\kappa r$, the identities become

$$
\mathsf A=hZ,\qquad H=h(Z+y-1),\qquad
\frac{\mathsf C-z_0}{r}=(Z-1)y+Z+3.
\tag{2.1}
$$

If $H=0$, then $\kappa=0$, $\mathsf A=0$, and $\mathsf B=Y$. The complete inverse is

$$
Z=\frac{\mathsf B}{r},\qquad x=Z-2,\qquad
y=\frac{(\mathsf C-z_0)/r-Z-3}{Z-1},
$$

$$
S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix},\qquad
\delta=z_0-r(x+y).
\tag{2.2}
$$

The denominators are positive, since $r>0$ and $Z-1=x+1>1$.

Now suppose $H\ne0$. Then $h\ne0$ and $\mathsf A=hZ\ne0$. From (2.1),

$$
Z=\frac{\mathsf A}{h},\qquad
y=1+\frac{H-\mathsf A}{h}.
$$

Substitution into $\mathsf B=Y+\kappa L$ gives, term by term,

$$
\mathsf B=rZ+h[Z(y+2)+1]
=3\mathsf A+h+\frac{\mathsf A(r+H-\mathsf A)}h.
$$

Therefore $h$ solves the monic quadratic

$$
h^2-(\mathsf B-3\mathsf A)h
+\mathsf A(r+H-\mathsf A)=0.
\tag{2.3}
$$

A finite exact inverse takes its real roots

$$
h=\frac{\mathsf B-3\mathsf A\ \pm
\sqrt{(\mathsf B-3\mathsf A)^2-4\mathsf A(r+H-\mathsf A)}}2,
$$

counts a repeated root once, and retains only nonzero roots satisfying

$$
hH>0,\qquad x=\mathsf A/h-2>0,\qquad
y=1+(H-\mathsf A)/h>0.
$$

For each retained root construct $S=r(\begin{smallmatrix}x&xy\\1&y\end{smallmatrix})$, $\kappa=h/r$, and $\delta=z_0-r(x+y)$, and require all six original observation equations. The actual target supplies such a root. It remains to prove that two different valid targets cannot pass.

Suppose two targets give the same data. They have the same $r,H,Q$. The $H=0$ branch is already unique by (2.2). In the other branch, equal $h$ gives equal $Z,x,y,S,\kappa,\delta$. Assume instead that the two nonzero roots $h,h'$ are distinct. Put

$$
Z=\mathsf A/h>2,\qquad Z'=\mathsf A/h'>2,
\qquad u=r/\mathsf A.
$$

Then $Z\ne Z'$. The product of the roots of (2.3) gives

$$
\frac1{ZZ'}=u+\frac H{\mathsf A}-1.
$$

Using $H/\mathsf A=1+(y-1)/Z$ for the first target, and its primed version for the second, gives

$$
y=1+\frac1{Z'}-uZ,\qquad
y'=1+\frac1Z-uZ'.
$$

Their common value of $(\mathsf C-z_0)/r$ in (2.1) implies

$$
0=(Z-1)y+Z+3-(Z'-1)y'-Z'-3
$$

$$
=(Z-Z')\left[2-(Z+Z'-1)
\left(u-\frac1{ZZ'}\right)\right].
$$

Since $Z\ne Z'$, this requires

$$
2=(Z+Z'-1)\left(u-\frac1{ZZ'}\right).
\tag{2.4}
$$

If $u\le0$, the right side is negative, since $Z+Z'-1>0$. If $u>0$, positivity of $y,y'$ gives

$$
uZZ'<Z'+1,\qquad uZZ'<Z+1.
$$

Consequently

$$
(Z+Z'-1)\left(u-\frac1{ZZ'}\right)
<\frac{Z+Z'-1}{\max(Z,Z')}
=1+\frac{\min(Z,Z')-1}{\max(Z,Z')}<2.
$$

Both signs of $u$ contradict (2.4). Thus distinct valid roots are impossible. The inverse returns exactly one effective target, including its whole constant drift.

All gain-zero cases are included. At indices $1$ and $2$, zero gains do not affect the prefix subtraction identities. At any of $3,4,5$, a zero gain gives $Q(i)=\delta$ and does not affect quadratic interpolation. Index $0$ has gain one. In the nonzero-slope branch, $h=\kappa r$ and $\mathsf A=hZ$ remain nonzero regardless of sampled gain zeros. The only other divisors are $r>0$, $Z-1>1$, the fixed integer $2$, and the nonzero node differences in Lemma 1.4. The monic quadratic cannot be the zero polynomial; a repeated real root is covered by the same uniqueness argument. No source ratio has an additional bound. ∎

**Proposition 2.2 (exact finite-data realizability).** For arbitrary real $z_0,\ldots,z_5$ on Theorem 2.1's path, the following criterion is necessary and sufficient for a constant-drift realization.

First form $r=2z_1-z_2-z_0$, $H=z_2-z_1$, and $Q$ as above, and require $r>0$. If $H=0$, require $\mathsf A=0$, form $Z=\mathsf B/r$, require $Z>2$, and then form $y$ by (2.2) and require $y>0$. Set $x=Z-2$, $\kappa=0$, and $\delta=z_0-r(x+y)$. If $H\ne0$, require $\mathsf A H>0$ and examine the real roots of (2.3), discarding zero roots and those failing $hH>0$, $x>0$, or $y>0$. A negative discriminant means no candidate. In either branch require all six equations

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+\delta,
\qquad S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix}.
$$

Compatibility holds exactly when one candidate passes, and there is then exactly one effective target.

**Proof.** Theorem 2.1 proves necessity of every condition, including $\mathsf A H>0$ in the nonzero branch. Every construction is made only after its divisors have been justified. A passing candidate has $r,x,y>0$ and determinant zero. Set $\alpha=1$, $\beta=\kappa$, $R=S$, $c=(rx,r)^{\mathsf T}$, and $\ell=(1,y)$. Lemma 1.2 supplies a single positive source and fixed row throughout the actual seventeen-atom history, and the six checked equations give exactly the proposed data with constant $D=\delta$. This proves sufficiency. Two passing candidates would be two actual realizations, contradicting Theorem 2.1's global uniqueness. Lemma 1.3 therefore describes all original representations of compatible six-read constant-drift data, including the complete internal positive-factor scale. ∎

## 3. The same path with affine additive drift

In this section keep exactly the same six matrices, reading indices, and chronological atoms, but allow $D(t)=\delta_0+\delta_1t$.

**Theorem 3.1 (the exact prescribed-slope kernel).** For every prescribed $\kappa\in\mathbb R$, define

$$
K(\kappa,1)=\{\Delta:\ (1+\kappa i)\operatorname{tr}(A_i\Delta)=P(i)
\text{ for }0\le i\le5\text{ and some affine }P\}.
$$

Then

$$
K(\kappa,1)=\operatorname{span}\left\{
\begin{pmatrix}0&1\\0&-1\end{pmatrix}\right\}.
$$

This line is contained in the union of the cone

$$
\mathcal C_{\mathrm{safe}}=
\left\{\begin{pmatrix}a&b\\c&e\end{pmatrix}:
a,e\ge0,\ b,c\le0\right\}
$$

and its negative. No nonzero point of that union is a difference of two strictly positive rank-one matrices.

**Proof.** Work first with an arbitrary real matrix $T=(\begin{smallmatrix}p&q\\r&s\end{smallmatrix})$ and arbitrary affine drift, without a rank-one or sign assumption. Write $a=p+s$, $Y=p+2r$, and $L=2p+5r+q+2s$. The same prefix and terminal expansions give

$$
2z_1-z_2-z_0=r,\qquad H=z_2-z_1=\kappa(a+r)+\delta_1,
$$

$$
\mathsf A=\kappa Y,\qquad
\mathsf B=Y+\kappa L+\delta_1,\qquad
\mathsf C=L+\delta_0.
\tag{3.1}
$$

The prefix combination also annihilates the affine drift. Set all six observations to zero. Then $r=H=0$, and the terminal polynomial is zero at three distinct nodes, so $\mathsf A=\mathsf B=\mathsf C=0$. If $\kappa\ne0$, $\mathsf A=\kappa p=0$ gives $p=0$. If $\kappa=0$, $H=\delta_1=0$ and $\mathsf B=p+\delta_1=0$ give $p=0$ as well. The initial equation gives $\delta_0=-s$, the $H$ equation gives $\delta_1=-\kappa s$, and the terminal constant equation gives $q+s=0$.

Thus every homogeneous solution is

$$
T=\begin{pmatrix}0&b\\0&-b\end{pmatrix},\qquad
\delta_0=b,\qquad \delta_1=\kappa b.
$$

Conversely the trace of this $T$ is $-b$ at each of the six matrices, including each terminal matrix, where it is $b-2b=-b$. Its signal is canceled by the affine drift $b(1+\kappa t)$. Replacing that drift by $-P$ proves the exact formula for $K(\kappa,1)$, without a restriction on $\kappa$ or on sampled gain zeros.

The negative of the displayed generator has nonnegative diagonal entries and nonpositive off-diagonal entries. Its scalar multiples therefore lie in $\mathcal C_{\mathrm{safe}}\cup-\mathcal C_{\mathrm{safe}}$. To prove the final assertion for the whole union, suppose two positive matrices differ by a nonzero element of $\mathcal C_{\mathrm{safe}}$. Their diagonal product weakly increases and their off-diagonal product weakly decreases; at least one comparison is strict, since an entry changes and all factors are positive. If the first matrix has equal diagonal and off-diagonal products, the second cannot also have them equal. Exchanging the endpoints handles the negative cone. This proves the safe-direction implication used here; no converse secant classification is needed. ∎

**Theorem 3.2 (independent inverse for each fixed slope).** For each prescribed real $\kappa$, the six-read map on positive rank-one sources with affine drift is globally injective. It has the following inverse on actual data, valid also at every gain-erasure slope.

**Proof.** Form $r=2z_1-z_2-z_0>0$, $H=z_2-z_1$, and the terminal interpolant $Q$ as before. Recover

$$
Y=\begin{cases}
\mathsf A/\kappa,&\kappa\ne0,\\
\mathsf B-H,&\kappa=0.
\end{cases}
$$

Indeed (3.1) gives the first branch. In the second branch $H=\delta_1$ and $\mathsf B=Y+\delta_1$. Put $Z=Y/r=x+2>2$. Since $\mathsf C-z_0=L-a$, the same source identity gives

$$
y=\frac{(\mathsf C-z_0)/r-Z-3}{Z-1},\qquad x=Z-2,
\qquad S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix}.
$$

Finally

$$
\delta_0=z_0-r(x+y),\qquad
\delta_1=H-\kappa r(x+y+1).
$$

Every formula returns the original parameter. Divisors are $r>0$, $Z-1>1$, interpolation node differences, and $\kappa$ only on its declared nonzero branch. No sampled gain is divided out. Two actual targets at the same prescribed slope and with the same data therefore agree in all source entries and both drift coefficients.

These formulas also give an exact arbitrary-data existence criterion for a prescribed slope: require $r>0$, compute $Y,Z$, require $Z>2$, compute $y$, require $y>0$, form $S,\delta_0,\delta_1$, and check all six observation equations, including every zero-gain position. Necessity follows from the identities. Sufficiency follows from the fixed-row factorization in Lemma 1.2 on the actual history. Thus this inverse proves fixed-slope injectivity independently of the safe-cone interpretation. ∎

**Theorem 3.3 (positive different-slope collision family).** Choose arbitrary

$$
r>0,\qquad Z,Z'>2,\qquad Z\ne Z',\qquad
V>\max(Z,Z')+3,\qquad \zeta,\eta\in\mathbb R.
$$

Define

$$
x=Z-2,\quad y=\frac{V-Z-3}{Z-1},\qquad
x'=Z'-2,\quad y'=\frac{V-Z'-3}{Z'-1},
$$

$$
S=r\begin{pmatrix}x&xy\\1&y\end{pmatrix},\quad
S'=r\begin{pmatrix}x'&x'y'\\1&y'\end{pmatrix},\quad
\kappa=\frac{Z'}{V-1},\quad \kappa'=\frac{Z}{V-1}.
$$

Writing $a=\operatorname{tr}S$ and $a'=\operatorname{tr}S'$, let

$$
D(t)=\zeta-a+[\eta-\kappa(a+r)]t,\qquad
D'(t)=\zeta-a'+[\eta-\kappa'(a'+r)]t.
$$

These are two distinct effective targets with the same six observations on the actual path. Both slopes, and all their recorded gains, are strictly positive.

**Proof.** All denominators are positive. The inequality on $V$ gives $y,y'>0$, and $Z,Z'>2$ gives $x,x'>0$. Thus both sources are strictly positive and have determinant zero. Their actual factorizations are

$$
c=(rx,r)^{\mathsf T},\quad \ell=(1,y),\qquad
c'=(rx',r)^{\mathsf T},\quad \ell'=(1,y').
$$

Take $\alpha=\alpha'=1$, $\beta=\kappa$, and $\beta'=\kappa'$. The two displayed drifts are allowed affine polynomials. Since $V-1>0$ and $Z,Z'>0$, both slopes are positive, hence $1+\kappa i$ and $1+\kappa'i$ are positive for every recorded $i\ge0$.

Substitution into the prefix equations gives, in both runs,

$$
z_0=\zeta,\qquad z_1=\zeta+r+\eta,\qquad
z_2=\zeta+r+2\eta.
$$

For the first source, $Y=rZ$ and

$$
\frac{L-a}{r}=(Z-1)y+Z+3=V,
\qquad L=a+rV.
$$

The terminal polynomial coefficients in (3.1) are therefore

$$
\mathsf A=\frac{rZZ'}{V-1},\qquad
\mathsf B=rZ+\kappa L+\eta-\kappa(a+r)
=\eta+r(Z+Z'),\qquad
\mathsf C=\zeta+rV.
$$

For the primed source, exchanging $Z$ and $Z'$ gives the same three coefficients. Thus at each actual terminal index $i=3,4,5$ the common observation is

$$
z_i=\frac{rZZ'}{V-1}i^2+[\eta+r(Z+Z')]i+\zeta+rV.
$$

This verifies all six equations explicitly. Lemma 1.2 supplies the positive intermediate column states under the same chronological seventeen-atom list, with its own one fixed row in each run. Each run uses one source and its one fixed gain and drift throughout.

Finally $p=r(Z-2)$ differs from $p'=r(Z'-2)$, and $\kappa\ne\kappa'$. The effective targets are distinct, so the collision is not a representation scale from Lemma 1.3. Theorem 3.2 proves injectivity within every prescribed-slope slice, whereas these targets lie on different slices. The collision is a failure of this particular six-read $d=1$ history; it supplies no all-history lower bound and excludes no other six-read history. ∎

## 4. Unrestricted fixed-history bounds

Let $C_{\mathrm{fix}}(d)$ be the smallest uniform read bound over all predetermined finite-composite-word histories in Definition 1.1 that recover the complete target on the whole stated source domain.

[Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md), Theorem 5.1, gives the lower bound $d+5$. It applies directly: its target is the same $(S,\kappa,D)$, with strictly positive rank-one $S$, arbitrary real $\kappa$, and drift of degree at most $d$, on the same counted-initial-read, finite-composite-word clock, including empty-word repeats. Its lower bound concerns all predetermined histories under this contract, including a fixed word list with earlier stopping.

For the upper bound, apply [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md), Theorem 4.1 and Lemma 3.2, at $k=1$. Every target here is in that model by taking $R=S$, $G(t)=1+\kappa t$, and the same $D$. The gain is nonzero and of degree at most one, and the normalized-target correspondence is

$$
R_0=\frac S{\operatorname{tr}S},\qquad
H(t)=(\operatorname{tr}S)(1+\kappa t),
$$

$$
S=H(0)R_0,\qquad \kappa=\frac{H'(0)}{H(0)},\qquad H(0)>0.
$$

Thus the cited recovery of $(R_0,H,D)$ recovers exactly $(S,\kappa,D)$ on this positive-intercept affine restriction, without changing the source, the drift, the operations, or the reading clock. The cited read count specializes to

$$
\max(1,d)+6=\max(d+6,7),
$$

with a literal nine-atom implementation. The polynomial companion's Corollary 4.2 and Proposition 5.1 provide the division-domain and exact finite-data compatibility conditions; the affine restriction is $H(0)>0$, with the displayed target conversion. All recorded equations remain required, including zero-gain positions and unused surviving samples, and the recovered entire drift must satisfy $\deg D\le d$. The polynomial theorem also permits initial gain zero, which is outside this volume's positive-intercept restriction.

Combining the cited lower and upper bounds with the new six-read constant-drift upper bound of Theorem 2.1 gives

$$
5\le C_{\mathrm{fix}}(0)\le6,\qquad
d+5\le C_{\mathrm{fix}}(d)\le d+6\quad(d\ge1).
$$

The original global target is unchanged: find the sharp uniform read count across all predetermined cumulative $M/J$ histories for every $d\ge0$, together with an actually legal fixed path and a one-source inverse covering all affine-gain zero crossings. For $d=0$ the minimum is still either five or six; for each $d\ge1$ it is still either $d+5$ or $d+6$. No five-read construction or five-read impossibility is established for $d=0$. No universal $d+5$ construction or universal obstruction at $d+5$ is established for $d\ge1$. Theorem 3.3 addresses one particular path and does not resolve the $d=1$ choice between six and seven.

## 5. The credited polynomial-prefix optimum and its scope

In the broader model of [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md), Definition 1.1, the gain $G\not\equiv0$ has degree at most known $k\ge0$, the strictly positive rank-one source is $R$, and $\deg D\le d$. Its complete target is $(R_0,H,D)$, with $R_0=R/\operatorname{tr}R$ and $H=(\operatorname{tr}R)G$. Definition 3.1 fixes the prefix with

$$
B=\max(k,d)+1,\qquad T=B+k+1:
$$

$B$ reads at $I$, followed by the $k+1$ reads at $U,\ldots,U^{k+1}$. It has $T$ reads and ends at cumulative matrix $U^{k+1}$ at recorded index $T-1$.

The polynomial companion's Theorem 8.1 and Corollary 8.2 establish that exactly $k+2$ further predetermined reads are necessary and sufficient in the worst case over that declared model, after this entire specified prefix. The corresponding total is $\max(k,d)+2k+4$. This is a continuation optimum for this prefix; it is neither a lower bound for other prefixes nor a necessity statement for every individual gain polynomial or prescribed root pattern. Its Theorem 6.1 gives the separate complete positive-scale fibre $R=tR_0$, $G=H/t$, $t>0$, with $D$ fixed, and agreement along common future histories.

For $k=1$, this prefix has $B=\max(1,d)+1$ reads at $I$, then reads at $U,U^2$. The positive-intercept affine restriction is the one mapped in Section 4. [Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md), Theorem 4.1, supplies the obstruction to at most two further reads directly within this restriction, with an allowed gain of initial value one. Combined with the cited polynomial upper construction at $k=1$, it gives exactly three further reads for this affine prefix as well. The unrestricted polynomial lower bound alone is not used to infer a lower bound on a smaller positive-intercept domain.

This baseline/shear prefix differs from Theorem 2.1's initial $I,U,U$ prefix. Its continuation optimum therefore leaves the different six-read construction and the all-history alternatives of Section 4 intact. Likewise, Theorem 3.3's collision concerns its particular six-read history and does not exclude other histories.

## 6. Credits and unresolved boundaries

The common-source trace model, positive factorization, recorded-reading contract, and effective affine target come from Definitions 10.1–10.3 and 38.1 of [FIB self-calibrating relation mathematics](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md). Its Sections 1–5 give the trace and scale interfaces. Its fixed/adaptive unweighted read distinctions, drift recurrences, ten-dimensional lifted inverse, and common-source compatibility warnings retain their own assumptions and targets. In particular an independently fitted pair of lifted matrices is not a replacement for the single source used here.

The same source's Theorem 38.2 gives the earlier $d+7$ sufficient bound under its specified nonzero switching gains and $d+8$ without that restriction, on its single-switch path; its Proposition 38.4 gives a zero-gain collision on that path. Its Definition 39.1 and Theorem 39.2 give the broader polynomial-gain single-switch bound $3k+d+5$ and complete normalized target. These are prior sufficient constructions and path-specific collisions. They do not determine the unrestricted fixed-history optimum.

[Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md), Theorem 2.1, supplies the repeated-baseline/shear calibration and the $\max(d+6,7)$ affine upper bound; its Corollary 2.2 gives the positive scale fibre, Theorem 4.1 the affine-prefix obstruction, and Theorem 5.1 the all-fixed-history lower bound $d+5$. [Common polynomial-gain shear calibration and erasure recovery](FIB_POLYNOMIAL_GAIN_SHEAR_CALIBRATION_AND_ERASURE_RECOVERY.md), Theorem 4.1 and Lemma 3.2, supply the full polynomial recovery and its read/atom counts; its Proposition 5.1 gives common-source finite-data compatibility, Theorem 6.1 the positive-scale fibre, and Theorem 8.1 with Corollary 8.2 the prefix continuation optimum. Sections 4–5 apply these existing results with their stated targets and scopes.

Theorem 2.1 establishes this volume's six-read constant-drift construction, and Proposition 2.2 gives its exact finite-data criterion. Theorems 3.1–3.3 establish the prescribed-slope safe line, independent fixed-slope inverse, and different-positive-slope collision family on the same actual history. Their complete proofs use one positive source and one fixed row within each run. The constant-drift result confines the unrestricted optimum to five or six. The collision family shows that every prescribed-slope slice can be injective while unknown-slope recovery fails on that history, leaving other histories available for the global question.

All recovery claims assume the exact declared degree-bounded model, the known operations, strict positive rank one, and the recorded-reading clock. Relation/gain scales and the internal positive-factor scale are exactly those of Lemma 1.3. Read counts and literal atom counts are separate resources; neither seventeen nor nine is asserted to be an optimal atom count. The lower bounds concern predetermined histories under the finite-composite-word contract, which does not require a read after every atom. The fixed-prefix polynomial optimum does not determine an unrestricted polynomial-gain optimum or an adaptive optimum. Both alternatives in each bound of Section 4 remain unresolved, as do any stronger conclusions beyond these stated targets and contracts. These exact-model statements do not assert noisy stability, bit precision, acquisition cost, physical or empirical certification, general neural-network performance, or literature priority.

## 追加锚（本行以下为增补区）
