# Projection–ideal averages for prime-cube six-letter returns

## 1. The literal count

For $c\ge1$ put

$$
R_c(x)=\begin{pmatrix}x&-1\\1&0\end{pmatrix},\qquad
 W_{a_1,a_2}(h)=\prod_{i=1}^3 R_c(a_1h_{2i-1})R_c(a_2h_{2i}),
$$

where the displayed product alternates $a_1,a_2$, starting with $a_1$.
Equivalently it is
$R_c(a_1h_1)R_c(a_2h_2)R_c(a_1h_3)R_c(a_2h_4)  R_c(a_1h_5)R_c(a_2h_6)$.
Let $N_c(X,Y;a_1,a_2)$ be the number of literal integer tuples with
$|h_1|,|h_3|,|h_5|\le X$ and $|h_2|,|h_4|,|h_6|\le Y$ for which
$W_{a_1,a_2}(h)=\gamma I$ for some $\gamma\in\mathbb Z/c\mathbb Z$ with $\gamma^2=1$.
Because the scalar is determined by the word, this is also the sum
over these scalar centers of their separate counts.

**Theorem 1.1.**

Let $\varepsilon>0$ and $C_0\ge1$ be fixed.
There is $C=C(\varepsilon,C_0)>0$ such that for every prime $p$, units
$a_1,a_2\in\mathbb Z/p^3\mathbb Z$ and real widths satisfying

$$
p^{3/2}\le X\le Y,\qquad XY\le C_0p^{15/4},
 \qquad 6Y<p^2,
$$

one has $N_{p^3}(X,Y;a_1,a_2)\le C Y^2p^\varepsilon$.

**Corollary 1.2.**

For every fixed $\alpha<15/4$, the same conclusion holds under
$XY\le C_0p^\alpha$, with a constant depending only on $\varepsilon,C_0$.

*Proof.*

For $p\ge2$, $p^\alpha\le p^{15/4}$, so Theorem 1.1 applies.

The coefficient $g=a_1a_2$ is fixed throughout all averages.
An index denoted $g_{\rm idx}$ below is a lattice index, not this word
coefficient. The source problem and its arbitrary-modulus conjecture
are due to Pascadi [Pascadi](#reference-pascadi2026).

## 2. The original counting problem and the source reductions

The reductions in this section from the six original integer letters to the averaged singular family are the original-count results of [R](#reference-formalsource). All counts count literal integer representatives; their hypotheses and multiplicities are retained in the arithmetic arguments below.

### 2.1 Word, signs, and scalar centers

For a modulus $c\geq 1$, let

$$
A(x)=\begin{pmatrix}x&-1\\1&0\end{pmatrix},\qquad
 W_{a_1,a_2}(h_1,\ldots,h_6)
 =A(a_1h_1)A(a_2h_2)A(a_1h_3)A(a_2h_4)A(a_1h_5)A(a_2h_6),
$$

with entries in $\mathbb Z/c\mathbb Z$. A scalar return is $\gamma I_2$.
For real $X,Y\geq0$, define

$$
\begin{aligned}
 N_\gamma(c;X,Y;a_1,a_2)
  =\#\{(a,b,w;d,v,t)\in\mathbb Z^6:
  &\ |a|,|b|,|w|\leq X,\quad |d|,|v|,|t|\leq Y,\\
  &W_{a_1,a_2}(a,t,b,d,w,v)=\gamma I_2\}.
\end{aligned}
$$

The two rows are $(a,b,w)$ and $(d,v,t)$, but the word order is $(a,t,b,d,w,v)$. For real widths the literal intervals use integer floors; the displayed membership condition is the original real-box count of [R](#reference-formalsource).

**Lemma 2.1 (The four minus equations).**

Assume $a_1,a_2\in(\mathbb Z/c\mathbb Z)^*$ and put $g=a_1a_2$. Then
$W_{a_1,a_2}(a,t,b,d,w,v)=-I_2$ if and only if

$$
\tag{2.1}

 a+b+w=gtab,\qquad t+d+v=gwdv,\qquad wd=ta,\qquad wv=tb
 \pmod c.
$$

These equations also imply $av=bd\pmod c$.

*Proof.*

The four-equation equivalence and third-minor identity are original-count inputs from [R](#reference-formalsource).
The matrix proof cancels only the units $a_1,a_2$; it does not divide
by any of the six letters. Thus zero and nonunit letters are retained.

The original scalar-to-minus comparison of [R](#reference-formalsource) gives, for every $\gamma^2=1$,

$$
\tag{2.2}

 N_\gamma(c;X,Y;a_1,a_2)
 \leq64\,N_{-1}(c;2X,2Y;a_1,a_2).
$$

Both widths are doubled separately. There is no assumption that the
scalar center was already $-1$. For $c=p^3$, the number of centers
$\gamma^2=1$ is at most four (and is two for odd $p$). The final
center sum consequently costs an absolute factor only.

For most of this section we work with a minus-return box $(X,Y)$
satisfying

$$
\tag{2.3}

 1\leq X\leq Y,\qquad 3Y<p^2,\qquad
 p^3\leq A:=XY\leq C_0p^\alpha,
$$

where $p$ is prime, $a_1,a_2$ are units modulo $p^3$, and $C_0$ is
fixed. The original hypothesis $6Y_0<p^2$ will imply precisely this
three-width condition after $(X,Y)=(2X_0,2Y_0)$ in
(2.2).

### 2.2 The unit-middle reduction and the six actual charts

Let $U_-(p;X,Y)$ count the minus returns whose middle $(w,t)$ satisfies
$p\nmid wt$. The original three-width unit-middle reduction of [R](#reference-formalsource) gives, with floors when the widths are real,

$$
\tag{2.4}

 N_{-1}(p^3;X,Y)\leq3U_-(p;X,Y)
             +8(2\lfloor Y\rfloor+1)^2.
$$

It uses only $3Y<p^2$, together with $X\leq Y$. Even cyclic
rotation of the word preserves its alternating coefficients, so the
three unit-column charts retain the original $a_1,a_2$. The last
term counts the remaining row-divisible cases; these are not omitted.

Fix a finite set $T$ of the unit-middle returns. Choose one reduced
basis $(R_{w,t},V_{w,t})$ of

$$
\Lambda_{w,t}=\{(x,u)\in\mathbb Z^2:wu-tx\equiv0\pmod{p^3}\}
$$

for each occupied original middle, and reuse that same choice in every
chart. Put $H=\sqrt A$ and

$$
Q_{X,Y}(x,u)=\frac YX x^2+\frac XY u^2,\qquad
 \sigma_{w,t}^2=Q_{X,Y}(R_{w,t}),\qquad
 \kappa_{w,t}=1+gtw\pmod{p^3}.
$$

The minor equations in Lemma 2.1 place the two
physical endpoints $(a,d),(b,v)$ in this same lattice.

The original six-chart decomposition of [R](#reference-formalsource) gives the following six subsets of the actual $T$. They form a cover; they need not be disjoint. The first five estimates require no seventh-height assumption:

| Condition | Proved bound |
|:---|:---|
| $N$: $R_{w,t,x}$ is nonunit | $66048\,A^2/p^4$ |
| $S$: $R_{w,t,x}$ is a unit and $A\sigma_{w,t}^2\leq p^6$ | $148992\,A\,L(p)$ |
| $U$: the unit-shortest long chart, $\kappa_{w,t}$ nonunit | $O_\eta(p^\eta A^2/p^4)$ |
| $Z$: at least one physical endpoint is $(0,0)$ | $18A$ |
| $D$: $\kappa_{w,t}$ a unit and some nonzero endpoint has nonunit first coordinate | $O_\eta(p^\eta(A/p+A^2/p^4))$ |
| $G$: unit shortest first coordinate, $A\sigma_{w,t}^2>p^6$, $\kappa_{w,t}$ a unit, and both endpoint first coordinates units | the retained count treated below. |

Here

$$
L(p)=1+\frac{\log(2p)}{\log2}.
$$

The five discarded-chart bounds are the original-count estimates of [R](#reference-formalsource).
Their width hypotheses follow from (2.3):
$2X<p^2$, $2Y<p^3$, $Y<p^2$, and $A<p^4$. In the long nonunit
right-side theorem the strict long condition supplies its required
$p^3\leq H\sigma_{w,t}$. The endpoint theorem only needs
$2Y<p^2$ and $p^2\leq A$. Thus no six-width hypothesis is being
reintroduced here.

### 2.3 The finite maximum and the unconditional retained moment

For one middle, write its negative anchor in basis coordinates as $q$,
so $\operatorname{physical}(R,V,q)=(-w,-t)$. An ordered endpoint pair
$e=(x,y)$ consists of two vectors $x,y\in\mathbb Z^2$ in these same basis
coordinates. Define

$$
\begin{aligned}
 L_e(T)&=(x_1+y_1-q_1)+(x_2+y_2-q_2)T,\\
 Q_e(T)&=(x_1+x_2T)(y_1+y_2T),\\
 P_{b,e}(T)&=L_b(T)Q_e(T)-L_e(T)Q_b(T),\qquad
 \beta=V_xR_x^{-1}\pmod{p^3}.
\end{aligned}
$$

The anchor is subtracted in $L_e$; it is not a free independent coefficient.

Let $E_{w,t}$ be the actual finite endpoint family of the retained
chart, reconstructed bijectively from its original integer rows. Put

$$
\tag{2.5}

 B_{w,t}(b)=\{e\in E_{w,t}:P'_{b,e}(\bar\beta)=0\pmod p\},
 \qquad d(w,t)=\max_{b\in E_{w,t}}\#B_{w,t}(b),
$$

with $d(w,t)=0$ when $E_{w,t}$ is empty. For a nonempty finite family the maximum is attained by one actual retained baseline. No sum over possible baselines is present in the subsequent average.

Let $G(E)$ count ordered pairs $(b,e)\in E^2$ with nonzero derivative.
For each $b$, $\#E\leq\#\{e:P'_{b,e}(\bar\beta)\ne0\}+d$.
Summing gives

$$
(\#E)^2\leq G(E)+(\#E)d.
$$

Consequently $(\#E)^2\leq2G(E)$ if $2d\leq\#E$. Families with
$\#E<2d$ pay their actual maximum once. Cauchy–Schwarz applied to
the other families gives the following proved interface.

**Proposition 2.2 (Original retained moment).**

Suppose $s$ is a finite set of original middles and its retained
endpoint families satisfy the original word, physical boxes, unit
conditions, common reduced bases and longness conditions above.
If their anchor and endpoints have one common coordinate bound
$(I,J)$, with $I,J\geq1$, then

$$
\tag{2.6}

 \sum_{(w,t)\in s}\#E_{w,t}
 \leq2\sum_{(w,t)\in s}d(w,t)
    +\sqrt{\#s\,C_\eta p^\eta(9IJ)^5}.
$$

After the actual reduced-basis scales are summed dyadically, the
corresponding conclusion is

$$
\tag{2.7}

 \sum_{(w,t)\in s}\#E_{w,t}
 \leq2\sum_{(w,t)\in s}d(w,t)
   +\sqrt{\#s\,C_\eta p^\eta(A/p^3)^5L(p)}.
$$

Neither statement assumes a seventh-height separation.

*Proof.*

These are the original fixed-scale and dyadic retained-moment inputs of [R](#reference-formalsource). Their second-moment input is the original large-retained record incidence count and its dyadic version. The original rows reconstruct injectively in coordinates, and $\#T_G=\sum_{(w,t)}\#E_{w,t}$, so (2.7) holds for $T_G$ itself. The argument uses the finite inequality just displayed and Cauchy–Schwarz with that incidence count; no endpoint-count estimate is assumed as an input.

For completeness, the good-record integer uniqueness has no strict area
saving hidden in it. On this good chart both coordinates of $R$ are
units, and reducedness gives $0<|R_1R_2|<p^3$, since
$2|R_1R_2|\le Q_{X,Y}(R)<2p^3$. In a long chart the reconstructed second
basis vector has $|V_1|<3X/2$. Equal record data give
$V_1'\equiv V_1\pmod{p^3}$, whereas
$|V_1'-V_1|<3X\le3Y<p^2\le p^3$; hence $V_1'=V_1$ and the determinant
$p^3$ fixes $V_2$ too. This is the original good-record reconstruction of [R](#reference-formalsource). The fixed-good-record
realization count uses at most three simple roots and the divisor bound
for $R_1R_2$; it needs the stated width, not $A=o(p^{15/4})$.

In a dyadic bin $s_0^2\leq Q_{X,Y}(R)<4s_0^2$, the original reduced-basis coordinate, anchor and long-scale estimates of [R](#reference-formalsource) give

$$
\tag{2.8}

 I=\frac{8H}{s_0},\quad J=\frac{4Hs_0}{p^3},\quad
 J\leq I,\quad J>2,\quad IJ=\frac{32A}{p^3},
 \quad I<\frac{16A}{p^3},\quad J<5\sqrt{A/p^3}.
$$

The notation $B=IJ$ below denotes this coordinate area, not the bad
degree $d(w,t)$.

**Corollary 2.3 (The sufficient bad-degree average).**

Fix $\alpha\leq15/4$. If, uniformly for the actual retained families
and for every $\eta>0$, one proves

$$
\tag{2.9}

 \sum_{(w,t)\in s}d(w,t)\ll_{\eta,C_0,\alpha}p^\eta Y^2,
$$

then the original unit-middle count, and hence the minus count, is
$O_{\varepsilon,C_0,\alpha}(Y^2p^\varepsilon)$.

*Proof.*

There are at most $(2X+1)(2Y+1)\leq9A$ occupied middles. The square
root in (2.7) is therefore

$$
O_\eta\!\left(p^{\eta/2}A^3p^{-15/2}\sqrt{L(p)}\right).
$$

Since $A\leq C_0p^\alpha$ and $4\alpha\leq15$, we have
$A^4/p^{15}\leq C_0^4$; the last expression is
$O_\eta(Ap^{\eta/2}\sqrt{L(p)})$. Choose $\eta$ smaller than
$\varepsilon$ and absorb the logarithm into the remaining power. Use
$A\leq Y^2$ for both this term and the five discarded-chart bounds.
This proves $\#T_G\ll Y^2p^\varepsilon$, then $U_-\ll Y^2p^\varepsilon$.
Equation (2.4) completes the minus reduction.
The same numerical absorption applies to the $A$ and $A^2/p^4$ errors. For every $\alpha\le15/4$ and arbitrary $C_0\ge1$, the endpoint inequality $A^4/p^{15}\le C_0^4$ is a fixed bound, not a required vanishing quantity. No translated-box partition is needed.

The new rank-three arithmetic estimate naturally has scale $Y^2$.
Corollary 2.3 does not replace it by
the stronger and unjustified scale $A$. In particular one must insert
(2.9) into the moment above, rather than
call the old whole-count seventh-height wrapper.

### 2.4 The polynomial partition and the sixth-height zero case

Select the maximizing baseline once at each nonempty middle. Every
row in that chosen bad family has the same
$\lambda=Q_b(\beta)/L_b(\beta)\pmod{p^3}$ and

$$
\delta=\frac{Q'_b(\bar\beta)-\lambda L'_b(\bar\beta)}
               {L_b(\bar\beta)}\pmod p.
$$

The original word makes the denominators units. Its pencil-divisibility identity gives $p^3\mid P_{b,e}(\beta)$, and the bad-family definition gives $p\mid P'_{b,e}(\beta)$. The original modular-zero partner estimate of [R](#reference-formalsource) removes the modular-zero pencils under the numerical premises

$$
\tag{2.10}

 8IJ<p,\qquad6I^3<p^3,\qquad I\leq p.
$$

They hold for sufficiently large $p$ under $B\ll p^{\alpha-3}$,
$\alpha<4$. It counts both identically zero and content-$p$
pencils, with no nonalignment assumption on the baseline.

Write the remaining coefficient rows, including the baseline row
indexed by $0$, as

$$
(q_i,r_i,s_i,\ell_i,m_i),\qquad
 Q_i=q_i+r_iT+s_iT^2,\quad L_i=\ell_i+m_iT,\quad
 P_i=L_0Q_i-L_iQ_0.
$$

The actual source coefficient bounds are

$$
\tag{2.11}

 |q_i|\leq I^2,\quad |r_i|\leq2IJ,\quad |s_i|\leq J^2,
 \quad |\ell_i|\leq3I,\quad |m_i|\leq3J,
 \qquad I\geq J\geq1,
$$

and $|[T^j]P_i|\leq18I^{3-j}J^j$.
These are the original coefficient and pencil-height estimates of [R](#reference-formalsource).

For three rows let $[f,g,h]$ denote the determinant of the three
indicated columns, and define the Dixon residual

$$
\tag{2.12}

 \mathscr D=\det\begin{pmatrix}
 [r,q,\ell]&[s,q,\ell]+[r,q,m]&[s,q,m]\\
 [s,q,\ell]&[s,r,\ell]+[s,q,m]&[s,r,m]\\
 [m,q,\ell]&[m,r,\ell]&[m,s,\ell]
 \end{pmatrix}.
$$

The exact Dixon resultant identity of [R](#reference-formalsource) is

$$
\tag{2.13}

 \mathop{\mathrm{Res}}_{3,3}(P_1,P_2)
 =(m_0^2q_0-\ell_0m_0r_0+\ell_0^2s_0)\mathscr D.
$$

The subscripts denote the padded Sylvester resultant, so that a
separate argument is needed when both pencils have degree two.

**Lemma 2.4 (Zero residual, two genuine quadratics).**

Assume (2.11), $L_0(\beta)$ a $p$-unit,
and $P_1,P_2$ have degree exactly two and nonzero reductions modulo
$p$. Assume their values are divisible by $p^3$, their derivatives
by $p$, and $\mathscr D=0$. If
$6804I^6J^4<p^5$, then $\mathop{\mathrm{Res}}_{2,2}(P_1,P_2)=0$.

*Proof.*

Vanishing cubic coefficients gives
$m_0s_i-m_is_0=0$. If $(m_0,s_0)\ne(0,0)$, choose a primitive
integer direction $(d,n)$ and integers $k_i$ with
$m_i=dk_i$, $s_i=nk_i$. With $D_*:=\max_i|k_i|$,

$$
|d|D_*\leq3J,\qquad |n|D_*\leq J^2,\qquad D_*\leq3J^2.
$$

The last inequality follows from primitivity: either $|d|\geq1$,
or $d=0$ and $|n|=1$. A nonzero quadratic reduction with a double
root at $\bar\beta$ has unit quadratic leading coefficient. Thus the structured quadratic-direction resultant elimination of [R](#reference-formalsource) applies and gives the desired actual $2,2$ resultant. This elimination assumes neither $k_0\ne0$ nor $d,n$ individually nonzero.

It remains to treat $m_0=s_0=0$. Here $\ell_0$ is a $p$-unit.
Put

$$
A_i=\ell_0s_i-r_0m_i,\quad
 B_i=\ell_0r_i-r_0\ell_i-q_0m_i,\quad
 C_i=\ell_0q_i-q_0\ell_i,
$$

so that $P_i=A_iT^2+B_iT+C_i$. Substitution into the determinant
(2.12) and the quadratic formula

$$
\mathop{\mathrm{Res}}_{2,2}=(A_1C_2-C_1A_2)^2
       -(A_1B_2-B_1A_2)(B_1C_2-C_1B_2)
$$

gives the exact integer identity

$$
\tag{2.14}

 \ell_0\mathscr D
   =-(m_1s_2-m_2s_1)\mathop{\mathrm{Res}}_{2,2}(P_1,P_2).
$$

This is a polynomial identity obtained by expanding the displayed
determinants, not a cancellation of a specialized leading coefficient.
If $m_1s_2-m_2s_1\ne0$, the conclusion follows immediately over
$\mathbb Z$. Otherwise the two partner leading pairs are collinear. At
least one is nonzero, since otherwise both pencils would have degree
at most one. Choose its primitive direction. The zero baseline has
$k_0=0$, and the same bounds on $D_*$ hold. Apply the same direction
resultant theorem, which explicitly allows this value of $k_0$.

**Lemma 2.5 (Zero-residual root-relevant cover).**

Suppose the family above has the bounds (2.11),
unit $L_0(\beta)$, and nonzero pencil reductions, with
$p^3\mid P_i(\beta)$ and $p\mid P_i'(\beta)$.
Assume $\mathscr D(0,i,j)=0$ for every pair. There is an absolute constant
$C_*$ such that $C_*B^6<p^5$ guarantees a set of at most three
primitive irreducible nonconstant integer polynomials covering every
$P_i$ by divisibility. Every covering polynomial vanishes at $\beta$
modulo $p$ and has nonzero reduction modulo $p$.

*Proof.*

The root-localized cubic factorization of [R](#reference-formalsource), which has no numerical separation premise, gives

$$
P_i=R_iU_i,\qquad U_i(\beta)\in(\mathbb Z/p\mathbb Z)^*,\qquad
 \deg R_i\in\{2,3\}.
$$

Here $R_i$ is primitive, retains the $p^3$ value and $p$ derivative
divisibilities, has coefficients bounded by
$8\cdot18I^{3-j}J^j$, and every irreducible factor of $R_i$ is
root-relevant at $\bar\beta$.

We show that $R_i,R_j$ have a common rational factor. If one has
degree three, its original $P_i$ is a genuine cubic and $U_i$ is a
nonzero constant. Equations (2.13) and
$\mathscr D=0$ give a zero ordinary rational resultant: converting
the padded resultant is legitimate because this cubic has nonzero
leading coefficient. A common irreducible factor lies in $R_i$ and
cannot divide $U_j$, since the factor vanishes at $\bar\beta$ whereas
$U_j(\beta)$ is a unit. Hence it divides $R_j$.

If both $R$ factors have degree two and one original $P$ has degree three, use the genuine-cubic quadratic-factor height estimate of [R](#reference-formalsource):

$$
|\mathop{\mathrm{Res}}_{2,2}(R_i,R_j)|\leq24(8\cdot18)^4 B^6.
$$

The double-root quadratic resultant divisibility of [R](#reference-formalsource) gives divisibility by $p^5$, so the resultant is zero under the stated gap. If both originals have degree two, apply
Lemma 2.4; its height hypothesis follows
from $I^6J^4\leq B^6$. The complements are then constants, so the
same factor transfer applies. This last step cannot be replaced by
the padded $3,3$ resultant, which vanishes at infinity for two
quadratics regardless of their finite common roots.

For a nonempty family fix one $R_{\rm ref}$. Its at most three
primitive irreducible factors cover all the $R_i$ by the pairwise
common-factor conclusion. They are root-relevant, and cannot reduce
to zero because $R_{\rm ref}$ does not. An empty family is trivial.

No rank-three assumption or unit condition on the coefficient
$m_0^2q_0-\ell_0m_0r_0+\ell_0^2s_0$ was used in this lemma. In
particular it includes low row rank, linear-projection rank at most
one, and a zero baseline resultant. The original algebraic factor-value and singular-partner estimates of [R](#reference-formalsource) then bound this family by

$$
\tag{2.15}

 O_\eta\!\left(p^\eta\left(1+
       \frac{6H}{p\sqrt{Q_{X,Y}(R^{(2)}_{w,t})}}\right)\right),
$$

where $R^{(2)}_{w,t}$ is a reduced shortest vector for the index-$p^2$
lattice. The factor-value theorem permits coordinate bounds up to
$p$, and requires no old $B^7$ gap or unit baseline resultant.
The three required modular units follow from the actual original word by its singular-unit identities in [R](#reference-formalsource). The original physical-weight average gives

$$
\sum_{(w,t)\in s}\left(1+
       \frac{H}{p\sqrt{Q_{X,Y}(R^{(2)}_{w,t})}}\right)
 \leq2048\left(A+\frac ApL(p)+\frac{A^2}{p^4}\right).
$$

Thus this case contributes to the old admissible average without the
seventh-height restriction.

### 2.5 Rank four and the remaining rank-three supplier

**Lemma 2.6 (Rank bound and rank-four relevant factor).**

For the coefficient family above assume the common value and derivative
conditions, and

$$
\tag{2.16}

 2160B^4<p^4,\qquad233280B^6<p^5,\qquad93312B^6J<p^5.
$$

Its rational row rank is at most four. If its rank is four, a single
primitive linear polynomial $f$ divides every $P_i$, with nonzero
reduction and $f(\beta)=0\pmod p$. Its root $\theta\in\mathbb Q$
satisfies $L_0(\theta)\ne0$.

*Proof.*

Choose integer lifts of the common $\lambda,\delta$ and set

$$
v_0=(1,\beta,\beta^2,-\lambda,-\lambda\beta),\qquad
 v_1=(0,1,2\beta,-\delta,-\lambda-\delta\beta).
$$

Every row pairs with $v_0$ in $p^3\mathbb Z$ and with $v_1$ in $p\mathbb Z$.
The matrix $T=[v_0,v_1,e_2,e_3,e_4]$ has determinant one. Any
five-row determinant is therefore divisible by $p^4$, while its
absolute value is at most $2160B^4$. This proves the rank bound.

Choose four independent actual rows and let $U_j$ be their signed
$4\times4$ cofactors. Then $U\ne0$ and every row annihilates $U$.
The direct determinant bounds are

$$
\begin{aligned}
 |U_0|&\leq432I^2J^4,&|U_1|&\leq216I^3J^3,&
 |U_2|&\leq432I^4J^2,\\
 |U_3|&\leq144I^3J^4,&|U_4|&\leq144I^4J^3.
\end{aligned}
$$

In particular every $|U_j|<p^4$. Let $w$ be the cofactors after
multiplication by $T$. Then $U=Tw$ and

$$
p\mid w_0,\quad p^3\mid w_1,\quad
 p^4\mid w_2,w_3,w_4.
$$

Consequently

$$
\begin{aligned}
 U_0U_2-U_1^2&=w_0w_2-w_1^2\in p^5\mathbb Z,\\
 U_0U_4-U_1U_3
   &=\delta w_1^2+w_0w_4-\beta w_0w_3-w_1w_3\in p^5\mathbb Z.
\end{aligned}
$$

Their respective heights are at most $233280B^6$ and $93312B^6J$.
Both minors vanish by (2.16). If $U_0=0$,
the first gives $U_1=0$, hence $w_0=w_1=0$; all five $U_j$ would
be divisible by $p^4$ and strictly smaller than $p^4$, a contradiction.
Thus $U_0\ne0$. The third scroll minor follows from

$$
U_0(U_1U_4-U_2U_3)
  =U_1(U_0U_4-U_1U_3)-U_3(U_0U_2-U_1^2).
$$

Writing $\theta=U_1/U_0$ and $\zeta=U_3/U_0$, the row equations
become $Q_i(\theta)+\zeta L_i(\theta)=0$, hence $P_i(\theta)=0$.

Write $\theta=b/a$ in lowest terms with $a>0$. Integrality of
$U_2=U_1^2/U_0$ gives
$(U_0,U_1,U_2)=d(a^2,ab,b^2)$ for a nonzero integer $d$, so
$w_2=d(b-a\beta)^2$. If $p\nmid b-a\beta$, then $p^4\mid d$;
the displayed divisibilities and $U=Tw$ would again force every
$U_j$ to be zero. Thus $p\mid b-a\beta$, and primitivity gives
$p\nmid a$. Gauss’s lemma now makes $f=aT-b$ an integer divisor
of every $P_i$, with the asserted modular relevance. Finally
$aL_0(\theta)=a\ell_0+bm_0\equiv aL_0(\beta)\not\equiv0\pmod p$,
so $L_0(\theta)\ne0$.

This proof uses actual row heights and no unit baseline resultant.
It costs the same root-relevant factor weight
(2.15). Since $J\leq\sqrt B$, the last
gap follows from $93312^2B^{13}<p^{10}$. Thus it holds whenever
$B\ll p^{\alpha-3}$ with fixed $\alpha<49/13$; in particular
throughout $A\le C_0p^{15/4}$ for each fixed $C_0$.

After these reductions the only exceptional polynomial case is an
actual rank-three family with a nonzero Dixon residual. The rank always
includes the fixed maximum baseline and the complete selected partner
family; no rebase or partner deletion is made in the new argument.

The common-$\delta$ relations are used only to identify the actual
$p$-saturated row space. We do not assume that the selected baseline has
unit resultant $E_b$, and we do not change the maximum-baseline choice.
For the $j=3$ rank-three nonzero-residual family, Section 6.2
uses the fixed actual baseline $b$, an actual independent row $c$, and the
functional $f(r)=\det_L(r_b,r_c,r)$. The identity
$D_{\rm phys}(r_b,r_c,r)=D_Lf(r)^3$, including $f=0$, gives the complete
layer count (6.3). This is the only layer input used in
the new average; any auxiliary row appearing in the old affine-plane
lemma is not a replacement baseline and carries no extra family weight.
The same section proves the actual height correlation
$h\ll T$, $n\ll K/T$, the affine ideal coset, the inverse graph, and the
middle/projection support estimate. Consequently the source moment is
fed directly by (6.19), rather than by the old
seventh-height wrapper.

The numerical branch table records the retained $j=4$ bound and two
older $j=3$ auxiliary comparisons:

| Branch | Old normalizing scale | Old remaining power |
|:---|:---|:---|
| $j=4$ | $A$ | $(61\alpha-233)/9$ |
| $j=3$, rationally split | $A$ | $(43\alpha-161)/9$ |
| $j=3$, old nonsplit supplier | $Y^2$ | $(106\alpha-395)/9$. |

The two old $j=3$ lines are auxiliary comparisons only. Both are replaced
by (6.19), including the new ramified $j=3$ case.
The $j=4$ line remains in use: Lemma 3.4 and
Theorem 4.1 give

$$
\tag{2.17}
 \mathcal W_{j=4}\ll_\eta p^\eta\frac{A^7}{p^{23}}K^{1/9},
 \qquad K=C_DA^7/p^{26},\quad K\ge1,
$$

with the same sufficiently large absolute $C_D$ as in
(6.1). Relative to $A$ its exponent is $(61\alpha-233)/9$, so its threshold
is $233/61$ and its endpoint exponent is $-17/36$. Rank four has
threshold $49/13$, zero residual has threshold $23/6$, and the retained
source moment permits $\alpha\le15/4$. No $j=4$ identity
$D_L=p^8\kappa$ is asserted. No baseline multiplicity or free slope lift
is introduced.

### 2.6 Return to the original scalar count

The preceding source reductions and the new rank-three estimate establish
the averaged bad-degree bound at $A\le C_0p^{15/4}$. For
original widths satisfying

$$
p^{3/2}\leq X_0\leq Y_0,\qquad X_0Y_0\leq C_0p^{15/4},
 \qquad6Y_0<p^2,
$$

apply the minus argument to $X=2X_0,Y=2Y_0,A=4X_0Y_0$.
Then $3Y<p^2$, $p^3\leq A\leq4C_0p^{15/4}$, and all the
source reductions above are available. Corollary 
2.3,
(2.4), and (2.2)
give

$$
\sum_{\gamma^2=1}N_\gamma(p^3;X_0,Y_0;a_1,a_2)
       \ll_{\varepsilon,C_0}Y_0^2p^\varepsilon.
$$

Only absolute factors arise from the four-center bound, the factor
$64$, and $Y^2=4Y_0^2$. Finitely many smaller primes can be absorbed
uniformly: the literal box count is at most $729Y_0^6$, and the width
bound makes $Y_0$ bounded when $p$ lies below a fixed threshold.

## 3. Saturation and intrinsic physical kernels

Throughout this section $p$ is a sufficiently large odd prime; the
bounded-prime case is treated in Section 7.
The middle $(w,t)$ and one actual singular family are fixed. Its actual coefficient rows are

$$
r_e=(q_e,r_e^{(1)},s_e,\ell_e,m_e)
 = (z_1z'_1,z_1z'_2+z_2z'_1,z_2z'_2,
 z_1+z'_1-q_1,z_2+z'_2-q_2).
$$

Here the anchor $q$ represents $(-w,-t)$ in an oriented basis $M=(R,V)$
of the literal lattice $wU-tW\equiv0\pmod{p^3}$, with $\det M=p^3$.
Write $Q_e(T)=q_e+r_e^{(1)}T+s_eT^2$ and
$L_e(T)=\ell_e+m_eT$. The reduced-coordinate bounds are
$|z_1|,|z'_1|,|q_1|\ll I$ and
$|z_2|,|z'_2|,|q_2|\ll J$, where

$$
\tag{3.1}
 I\ge J\ge1,\qquad B=IJ\ll A/p^3,\qquad A=XY.
$$

All constants include these fixed coordinate-normalization factors.
The original Dixon divisibility and height identities of [R](#reference-formalsource) give the following bounds before saturation is invoked. The divisibility requires the actual baseline $L_0(\beta)$ to be a unit, and does not require the auxiliary $E_0$ to be a unit.
A nonzero actual three-row Dixon residual has

$$
\tag{3.2}
 p^5\mid D,\qquad |D|\ll B^7.
$$

For every fixed $C_0$ and $A\le C_0p^{15/4}$, sufficiently large $p$
gives $B\ll_{C_0}p^{3/4}=o(p)$ and $0<|D|<p^6$ whenever $D\ne0$,
since $B^7\ll_{C_0}p^{21/4}$. Thus $v_p(D)=5$.
These are the only smallness bounds used for saturation. The bound
$|\Delta_0|\ll B^4\ll_{C_0}p^3$ does not exclude valuation three;
we retain and prove that stratum separately below.
The integer polynomial $D$ is the determinant of

$$
\begin{pmatrix}
 [r,q,\ell]&[s,q,\ell]+[r,q,m]&[s,q,m]\\
 [s,q,\ell]&[s,r,\ell]+[s,q,m]&[s,r,m]\\
 [m,q,\ell]&[m,r,\ell]&[m,s,\ell]
\end{pmatrix},
$$

where brackets denote the three-column minors of the actual three-row
matrix. Its root/derivative divisibility and height are the explicit
Dixon identities in the preceding source reductions. Under a change
of row basis of determinant $d$, it is multiplied by $d^3$.

**Lemma 3.1 (Actual saturation).**

Let the actual row span $W\subset\mathbb Q^5$ have dimension three and contain
an independent actual triple with $D\ne0$. Every such triple generates
$(W\otimes\mathbb Q_p)\cap\mathbb Z_p^5$ over $\mathbb Z_p$.

*Proof.*

Only for this local calculation make a determinant-one $\mathbb Z_p$ change
of binary coordinates that sends the actual slope $\beta$ to zero.
The common word and derivative conditions are

$$
q-\lambda\ell\in p^3\mathbb Z_p,\qquad
 r^{(1)}-\delta\ell-\lambda m\in p\mathbb Z_p.
$$

The $L=(\ell,m)$ projection of an independent triple has rank two,
otherwise the last row of the Dixon matrix vanishes. A nonzero
$L$-minor has absolute value $O(B)<p$, so it is a $p$-unit. Thus the
actual $\mathbb Z_p$ row lattice has a basis $u,v,p^h k$, where the $L$
projections of $u,v$ are $(1,0),(0,1)$ and $k=(a,b,c,0,0)$ is primitive
in the saturated lattice. Since the saturated residual is integral,
$5-3h\ge0$, so $h\in\{0,1\}$.
If $h=1$, the first congruence on $pk$ gives $a\in p^2\mathbb Z_p$.
Modulo $p^3$ write

$$
u=(\lambda,\gamma,C,1,0),\qquad
 v=(0,\eta,F,0,1),\qquad \tau=\eta-\lambda\in p\mathbb Z_p.
$$

Put $G=F-\gamma$. The exact Dixon expansion for these rows is

$$
D(u,v,k)=a\{(b\tau-aG)(Cb+cG)-(c\tau+Ca)^2\}.
$$

It is divisible by $p^3$, contradicting the required valuation
$5-3h=2$. Replacing the two omitted $q$-entries changes this integer
polynomial only modulo $p^3$, so the same contradiction applies to the
original rows. Hence $h=0$. The change of binary coordinates was
used for valuations only; all real height estimates remain in the
original reduced coordinates.

**Lemma 3.2 (The coordinate discriminant and its two strata).**

Under Lemma 3.1, the primitive integer generator
$(a_0,b_0,c_0,0,0)$ of $W\cap\{\ell=m=0\}$ has

$$
\Delta_0=b_0^2-4a_0c_0=p^2d\ne0,\qquad |d|\ll B^4/p^2.
$$

Either $v_p(\Delta_0)=2$, $p\nmid d$, and $(d/p)=1$; or
$v_p(\Delta_0)=3$ and $v_p(d)=1$. The first stratum may be rationally
split. The second is a ramified quadratic field locally at $p$.

*Proof.*

In the local coordinates of the saturation proof, $a\in p^3\mathbb Z_p$,
$b\in p\mathbb Z_p$, $c\in\mathbb Z_p^*$. Divide by $c$ and eliminate the last
quadratic coordinate of the other two rows to obtain

$$
u=(\xi,\gamma,0,1,0),\quad v=(\zeta,\eta,0,0,1),\quad
 k=(a,b,1,0,0),\quad \zeta\in p^3\mathbb Z_p,\quad
 \omega=\xi-\eta\in p\mathbb Z_p.
$$

Their exact residual is

$$
\tag{3.3}
 -\{(a\gamma+\zeta)^2+a\omega^2-ab\gamma\omega
       -b^2\gamma\zeta+b\zeta\omega\}.
$$

If $v_p(b^2-4a)\ge4$, including zero, then $b\in p^2\mathbb Z_p$
and $a\in p^4\mathbb Z_p$; every displayed term is divisible by $p^6$,
contradicting valuation five. Thus the discriminant has valuation two
or three. The integer cofactor vector
$([q,\ell,m],[r,\ell,m],[s,\ell,m])$ is a nonzero integer multiple of
the primitive kernel, and has sizes $O(I^2B),O(B^2),O(J^2B)$.
This proves $|\Delta_0|\ll B^4$. In valuation two,
$(b^2-4a)/p^2\equiv(b/p)^2\not\equiv0\pmod p$ locally.
The determinant-one coordinate change and primitive unit scaling
change this by a unit square, proving the assertion globally.
In valuation three necessarily

$$
\tag{3.4}
 v_p(a)=3,\qquad v_p(b)\ge2,\qquad v_p(\omega)=1.
$$

The first two follow from $a\in p^3$ and the discriminant valuation.
In (3.3) all terms other than
$a\omega^2$ have valuation at least six, so valuation five forces the
last assertion. In the single ramified field, normalized by $v(p)=1$,
both roots $\tau$ of $a+bT+T^2$ have valuation $3/2$. Hence

$$
E_{\rm coord}=\zeta-\omega\tau-\gamma\tau^2,
 \qquad v(E_{\rm coord})=5/2:
$$

the middle term has valuation $5/2$, strictly below the other two.
No unit condition on $\gamma$ or baseline resultant was used.

Write $M=\left(\begin{smallmatrix}r&v\\s&z\end{smallmatrix}\right)$,
$rz-sv=p^3$, with $r,s$ $p$-units. Its product-coefficient action is

$$
T(M)=\begin{pmatrix}r^2&rv&v^2\\2rs&rz+sv&2vz\\s^2&sz&z^2\end{pmatrix}.
$$

Put $K_0(T)=a_0+b_0T+c_0T^2$ and
$(A_0,B_0,C_0)=T(M)(a_0,b_0,c_0)$, with $\rho_0=s/r$.
Exactly,

$$
\begin{aligned}
 A_0&=r^2K_0(v/r),\\
 B_0-2\rho_0 A_0&=p^3K'_0(v/r),\\
 C_0-\rho_0 B_0+\rho_0^2A_0&=p^6c_0/r^2.
\end{aligned}
$$

In the valuation-two stratum $v_pK'_0(v/r)=1$, so the complete content
is $p^j$, $j\in\{3,4\}$. In valuation three,
$v_pK_0(v/r)=3$ and $v_pK'_0(v/r)\ge2$ by
(3.4), so $A_0$ has valuation exactly three:
the complete content is exactly $p^3$. No other prime can enter the
content, since $T(M)$ is invertible away from $p$ and the coordinate
kernel is primitive. Define $(a,b,c)=p^{-j}(A_0,B_0,C_0)$ with fixed sign.
It is independent of the middle basis, and

$$
\tag{3.5}
 b^2-4ac=p^{8-2j}d.
$$

In particular the ramified stratum is only $j=3$, with physical
discriminant $p^2d$, $v_p(d)=1$, and $p\nmid abc$.
The kernel polynomial $a+bT+cT^2$ must be distinguished from the dual
middle form $F(W,T)=cW^2-bWT+aT^2$.

**Lemma 3.3 (Physical height and fixed-kernel support).**

For $j\in\{3,4\}$ the physical kernel has

$$
|a|\ll X^2A/p^{3+j},\quad |b|\ll A^2/p^{3+j},
 \quad |c|\ll Y^2A/p^{3+j}.
$$

Each fixed primitive physical kernel arises at $O(A/p^2)$ distinct
actual integer middles in the literal box. This counts middles, not
residue classes, and is uniform in the choices of actual triples.

*Proof.*

If the coordinate cofactor vector is $m(a_0,b_0,c_0)$, then its physical
counterpart is $\det(M)T(M)$ times that vector, hence has content
$p^{3+j}|m|$. Expanding the physical cofactors gives bounds
$54X^2A,108A^2,54Y^2A$, proving the heights.
For the middle quadratic

$$
F(W,T)=aT^2-bWT+cW^2
$$

finite Taylor expansion at $s/r$, followed by $t/w-s/r\in p^3\mathbb Z_p$,
gives exactly

$$
v_pF(w,t)=6-j,\qquad
 v_p(2a(t/w)-b)=4-j\quad\text{in the valuation-two stratum}.
$$

In particular $F(w,t)\ne0$ as an integer. For $j=4$ the discriminant
is a $p$-unit: the unit slope $t/w$ lies in at most two simple root
classes modulo $p^2$. For unramified $j=3$, the roots in $\mathbb Z_p$ differ by valuation one,
and $v_pF(w,t)=3$ forces root distances one and two; again there are
two slope classes modulo $p^2$. For ramified $j=3$, the transport
identities give $b-2\rho_0a\in p^2\mathbb Z_p$ and
$v(c-\rho_0b+\rho_0^2a)=3$. Replacing $\rho_0$ by $t/w$ changes the
last value only by $p^5\mathbb Z_p$, so $v_pF(w,t)=3$ here as well.
Completing the square,

$$
\tag{3.6}
 F(W,T)=c(W-bT/(2c))^2-p^2dT^2/(4c).
$$

Since $t$ is a unit and the second term has valuation three, the
integer valuation of $w-bt/(2c)$ must be at least two. Thus there is
one class $W\equiv(b/(2c))T\pmod{p^2}$. Every vector of this lattice
has $F$ divisible by $p^3$ by the same identity, and $d$ cannot be a
rational square.
For each of these at most two classes $\eta$ all these middles belong to

$$
\Lambda_\eta=\{(W,T)\in\mathbb Z^2:T\equiv\eta W\pmod{p^2}\},
 \qquad \det\Lambda_\eta=p^2,
$$

and $F(\Lambda_\eta)\subset p^{6-j}\mathbb Z$. In the ramified case this was
just proved by completing the square. In the unramified repeated-root case
this follows by expanding
$F(m,\eta m+p^2n)=m^2f(\eta)+p^2mnf'(\eta)+p^4an^2$.

We use the elementary quantized quadratic count

$$
\tag{3.7}
 \#\{v\in\Lambda:|v|\le R,\ F(v)\ne0\}
 \le1+2R\sqrt{M/q}+6R^2/D,
$$

when $\det\Lambda=D$, $F(\Lambda)\subset q\mathbb Z$ and
$|F(v)|\le M|v|^2$. Take a shortest primitive vector $u$ of length
$\lambda\le R$. The noncentral parallel lattice lines are spaced
$D/\lambda$ apart and contribute at most
$(2R\lambda/D)(1+2R/\lambda)\le6R^2/D$.
If $F(u)=0$ the central line contributes no counted point.
Otherwise $q\le |F(u)|\le M\lambda^2$, and that line contributes at
most $1+2R\sqrt{M/q}$. Empty sections are immediate.

Apply the determinant-one weighting
$(W,T)\mapsto(W\sqrt{Y/X},T\sqrt{X/Y})$.
The box lies in a disk of radius $\sqrt{2A}$ and the form bound holds
with $M\ll A^2/p^{3+j}$. Summing (3.7) over the
two lattices gives

$$
O(1+A/p^2+A^{3/2}/p^{9/2})=O(A/p^2).
$$

Here $A\ge p^3$ and $A\ll p^\alpha$, $\alpha<4$, absorb the boundary
term for large $p$. The argument includes rational null directions
and therefore does not delete a split branch.

**Lemma 3.4 (The easy physical branches).**

Writing $\mathcal M$ for the set of selected actual middles,

$$
\#\mathcal M_4\ll A^7/p^{23},\qquad
 \#\mathcal M_{3,\mathrm{split}}\ll_\varepsilon p^\varepsilon A^5/p^{15}.
$$

*Proof.*

A nonzero residual requires $A\gg p^{26/7}$. For $j=4$ the smallest
coefficient-box height is
$X^2A/p^7=A^3/(Y^2p^7)\gg A^3/p^{11}\gg p^{1/7}$,
using $Y<p^2/3$. Thus all floor and zero-coefficient terms are absorbed
in the product of the three heights. There are $O(A^6/p^{21})$
integer kernels; Lemma 3.3 proves the first bound.
For $j=3$ the unit slope forces $p\nmid abc$.
In the rationally split case $b^2-4ac=p^2e^2$, $e\ge1$.
Put $H_2\asymp A^2/p^6$. There are $O(H_2^2/p)$ pairs $(b,e)$,
and each determines a nonzero integer $ac$ of polynomial height.
The divisor bound gives $O_\varepsilon(p^\varepsilon)$ ordered signed pairs $(a,c)$.
Multiplying by the fixed-kernel support proves the second assertion.

## 4. An all-layer bound for a nonzero-residual rank-three family

We count actual ordered integer endpoints throughout. In particular, a
one-dimensional projection is not identified with an endpoint, and a
fixed residual value is not identified with the union of its layers.
The endpoint-line estimate needed below will be proved inside the
argument; it carries no additional physical multiplicity weight.

### 4.1 Actual data and the local inputs

Fix an odd prime $p$, a unit $g\in(\mathbb Z/p^3\mathbb Z)^\times$,
and integers $w,t$ prime to $p$. Let $X,Y>0$, with

$$
\tag{4.1}
  2X<p^3,\qquad 2Y<p^3.
$$

The working minus-box condition $3Y<p^2$, with $X\leq Y$, implies
(4.1). An actual middle-lattice basis is
an integral matrix

$$
M=\begin{pmatrix}R_1&V_1\\R_2&V_2\end{pmatrix},
 \qquad \det M=p^3,
$$

whose columns form a basis of

$$
\{(x,u)\in\mathbb Z^2:wu-tx\equiv0\pmod{p^3}\}.
$$

We assume $R_1$ is prime to $p$. Write $\operatorname{phys}(z)=Mz$,
and choose the integer anchor $\mathbf a$ with

$$
\operatorname{phys}(\mathbf a)=(-w,-t).
$$

Let $\mathcal E$ be a finite set of ordered pairs
$e=(z,z')\in\mathbb Z^2\times\mathbb Z^2$. For every $e\in\mathcal E$,
put $\operatorname{phys}(z)=(x,u)$ and
$\operatorname{phys}(z')=(y,v)$. We require literal bounds
$|x|,|y|,|w|\leq X$, $|u|,|v|,|t|\leq Y$, unit first coordinates
$p\nmid xy$, and the actual word equations

$$
\tag{4.2}
 \begin{split}
  x+y+w&=gtxy,& u+v+t&=gwuv,\\
  wu&=tx,&wv&=ty
 \end{split}
 \qquad\pmod{p^3}.
$$

The retained unit chart is

$$
\tag{4.3}
 \kappa=1+gtw\in(\mathbb Z/p^3\mathbb Z)^\times.
$$

For $e=(z,z')$, define its coefficient row

$$
\mathbf r_e=(q_e,r_e,s_e,\ell_e,m_e)
 =\bigl(z_1z'_1,z_1z'_2+z_2z'_1,z_2z'_2,
        z_1+z'_1-a_1,z_2+z'_2-a_2\bigr).
$$

For any row $b=(q_b,r_b,s_b,\ell_b,m_b)$ set

$$
L_b(S,T)=\ell_bS+m_bT,\qquad
 Q_b(S,T)=q_bS^2+r_bST+s_bT^2,
 \qquad P_{b,c}=L_bQ_c-L_cQ_b.
$$

Dehomogenization means $L_b(T)=L_b(1,T)$, and similarly for $Q_b$.

Here is the residual convention. For three rows, let $[f,g,h]$ denote
the determinant of the indicated three coefficient columns. Define

$$
\tag{4.4}
 \mathcal D=\det\begin{pmatrix}
 [r,q,\ell]&[s,q,\ell]+[r,q,m]&[s,q,m]\\
 [s,q,\ell]&[s,r,\ell]+[s,q,m]&[s,r,m]\\
 [m,q,\ell]&[m,r,\ell]&[m,s,\ell]
 \end{pmatrix}.
$$

If $\mathbf R$ is the matrix of the three rows, each bracket acquires
the determinant of a row-basis change, so

$$
\tag{4.5}
 \mathcal D((A\mathbf R)_1,(A\mathbf R)_2,(A\mathbf R)_3)
  =\det(A)^3\mathcal D(\mathbf r_1,\mathbf r_2,\mathbf r_3),
$$

where $(A\mathbf R)_i$ denotes its $i$th row. Thus nonvanishing depends
only on the rational
three-space, rather than on its chosen basis.
Direct substitution also gives the binary-coordinate covariance
$\mathcal D_{\mathrm{new}}=\det(U)^7\mathcal D_{\mathrm{old}}$
when all endpoints and the anchor are changed by $U\in\mathrm{GL}_2(\mathbb Q)$.

Let

$$
\mathcal V=\operatorname{span}_{\mathbb Q}
      \{\mathbf r_e:e\in\mathcal E\},\qquad
 H_p=(\mathcal V\otimes\mathbb Q_p)\cap\mathbb Z_p^5.
$$

The following are the precise local conclusions of the saturated
rank-three reduction used in this section. They are stated explicitly
so that the all-layer assertion has a fixed scope:

1.  $\dim\mathcal V=3$, its projection to $(\ell,m)$ has rank two,
    and its residual (4.4) is nonzero.

2.  The projection $H_p\longrightarrow\mathbb Z_p^2$ is onto. Put

    $$
    \beta=V_1/R_1,\qquad \lambda=(gtR_1)^{-1}
        \quad\text{in }\mathbb Z/p^3\mathbb Z.
    $$

    For some $\delta\in\mathbb F_p$, every row in $H_p$ satisfies

    $$
    \tag{4.6}
      Q(\beta)-\lambda L(\beta)\equiv0\pmod{p^3},\qquad
      Q'(\beta)-\lambda L'(\beta)-\delta L(\beta)
           \equiv0\pmod p.
    $$

    Integer representatives of $\beta,\lambda$ may be used in these
    congruences. The primitive pure-quadratic kernel of $\mathcal V$ is
    generated by $(a_0,b_0,c_0,0,0)$, with

    $$
    \tag{4.7}
      b_0^2-4a_0c_0=p^2d_0\ne0,\qquad
      \begin{cases}
       p\nmid d_0,\ (d_0/p)=1,&\text{unramified stratum},\\
       v_p(d_0)=1,&\text{ramified stratum}.
      \end{cases}
    $$

3.  There are fixed constants $C_0,C_D\geq1$ and heights $I\geq J\geq1$
    such that $B=IJ\leq p^{C_0}$, the anchor and both endpoints have
    $|z_1|\leq3I$, $|z_2|\leq3J$, and every nonzero actual three-row
    residual satisfies

    $$
    \tag{4.8}
       v_p\mathcal D=5,\qquad |\mathcal D|\leq C_D B^7.
    $$

The root scaling is literal: the first physical coordinate is
$R_1(z_1+\beta z_2)$ and
$a_1+\beta a_2=-w/R_1$ modulo $p^3$. Thus the first equation in
(4.2) is exactly $Q_e(\beta)=\lambda L_e(\beta)$;
only $g,t,R_1$ have been inverted. The remaining middle relations
then give the second word equation by multiplication by $t/w$.
For example, the previously established fifth-power divisibility and
$C_DB^7<p^6$ give the exact valuation in
(4.8). The local saturation and
discriminant conclusions are supplied by the preceding local reduction;
they are not conclusions about an arbitrary candidate rational section.
All polynomial-height assertions below have exponents depending only on
the fixed constants in this setup.

**Theorem 4.1 (All residual layers in rank three).**

Under the preceding actual and saturated local hypotheses, for every
$\varepsilon>0$,

$$
\tag{4.9}
 \#\mathcal E\ll_{\varepsilon,C_0,C_D}
  p^\varepsilon\left(1+K^{1/9}\right),\qquad
 K=\frac{C_DB^7}{p^5}.
$$

All ordered integer endpoint multiplicities and all residual layers are
included. No fixed-endpoint-line estimate is a hypothesis of the theorem.

We first record uniqueness, which will be used only after counting
actual first endpoints. From (4.2),

$$
\tag{4.10}
 (gtx-1)(gty-1)=\kappa\pmod{p^3}.
$$

Both factors are units by (4.3). Thus a fixed actual
$x$ determines $y$ modulo $p^3$; the interval condition determines its
integer representative. The middle relation with $w$ a unit then
determines $u,v$ modulo $p^3$, and their literal intervals determine
the integer representatives. Consequently one first endpoint has at
most one actual partner. This statement does not discard residue-lift
multiplicities; those multiplicities are excluded by
(4.1) itself.

### 4.2 The quadratic-algebra model and its actual unit chart

**Lemma 4.2 (A rational model with a controlled local chart).**

After a rational binary-coordinate change of polynomial height which
is invertible over $\mathbb Z_p$, the pure kernel is $(-d,0,1,0,0)$ and
the rational row space has equations

$$
\tag{4.11}
 q=\xi\ell+\zeta m-ds,\qquad r=\gamma\ell+\eta m,
$$

where $d\ne0$. In the quadratic etale algebra
$F_2=\mathbb Q[\theta]/(\theta^2-d)$, put

$$
Z(z)=z_1+\theta z_2,\qquad A=Z(\mathbf a),
$$

$$
\begin{aligned}
 \mu&=\frac{\xi+\eta}{2}
       +\frac{\gamma+\zeta/d}{2}\theta,&
 \nu&=\frac{\xi-\eta}{2}
       +\frac{\gamma-\zeta/d}{2}\theta,\qquad W=Z-\mu.
\end{aligned}
$$

Then the full affine ordered-endpoint section is

$$
\tag{4.12}
 WW'-\nu(\overline W+\overline W')=C,\qquad
 C=\mu^2-\mu A-\nu\overline A+2\nu\overline\mu.
$$

Moreover $N(\nu)\ne0$. In the unramified case work in the two
$\mathbb Q_p$ components; in the ramified case work in the single ramified
quadratic field $K/\mathbb Q_p$, with valuation $v(p)=1$ and its conjugation.
In either case, in each conjugate embedding into $\overline{\mathbb Q}_p$,

$$
\tag{4.13}
 \mu\equiv\lambda\pmod{\mathfrak m},\qquad v(\nu)\ge1,\qquad
 C\equiv\lambda^2\kappa\pmod{\mathfrak m},
$$

where $\mathfrak m$ is the maximal ideal of the relevant valuation ring.
In the ramified case $v(\nu)=1$ exactly. Actual $W,W'$ and their
conjugates are units, and $N(W)-N(\nu)$ is a $p$-adic unit.

*Proof.*

First use a representative of $\beta$ between $0$ and $p^3-1$ to send
the actual root to zero. The kernel coefficients then obey
$a\in p^3\mathbb Z_p$, $b\in p\mathbb Z_p$, and $c\in\mathbb Z_p^\times$.
Indeed a failure of the last assertion, together with the two kernel
congruences, would contradict primitivity. Divide by $c$ and complete
the square by the rational shear $z_1\mapsto z_1-(b/2c)z_2$.
This gives $(-d,0,1)$ with $v_p(d)=2$ or $3$. In valuation two the
new evaluation point $\beta_*\in p\mathbb Z_p$; in valuation three,
(3.4) gives $\beta_*\in p^2\mathbb Z_p$. All changes have polynomial height
and are invertible over $\mathbb Z_p$: a primitive kernel generator is
obtained by dividing the three actual cofactors $[q,\ell,m]$,
$[r,\ell,m]$, $[s,\ell,m]$ by their integer gcd, so its coefficients
already have polynomial height. By (4.7),
the valuation-two local algebra splits over $\mathbb Q_p$, with roots of
valuation one; the valuation-three algebra is the ramified field with
roots of valuation $3/2$. These are separate local realizations of the
same rational quadratic-algebra formulas.

Surjectivity of the linear projection gives the unique rational
normalized lifts $(\xi,\gamma,0,1,0)$ and
$(\zeta,\eta,0,0,1)$, proving (4.11).
They are $p$-integral. Their rational heights are polynomial by Cramer’s rule on three
independent actual rows. Applying
(4.6) to them gives

$$
\xi\equiv\eta\equiv\lambda\pmod p,\qquad
 \zeta+\beta_*(\eta-\lambda)\in p^3\mathbb Z_p.
$$

Thus $\zeta\in p^2\mathbb Z_p$ in valuation two. In valuation three,
$\beta_*\in p^2\mathbb Z_p$ and $\eta-\lambda\in p\mathbb Z_p$ give
$\zeta\in p^3\mathbb Z_p$. Consequently $\zeta/d$ is $p$-integral in
both strata; this is the extra step required in the ramified case. Evaluation at $\theta$
in (4.11) gives

$$
ZZ'=\mu(Z+Z'-A)
       +\nu(\overline Z+\overline Z'-\overline A),
$$

and translating $W=Z-\mu$ proves (4.12).

Direct substitution in (4.4) on the normalized basis
gives

$$
\mathcal D_0=d(\xi-\eta)^2-(\zeta-\gamma d)^2,\qquad
 N(\nu)=\frac{\mathcal D_0}{4d}\ne0.
$$

Nonvanishing is unchanged by either rational coordinate or row-basis
changes. In the split local case $\theta_\pm\in p\mathbb Z_p$, so
(4.13) follows. In the ramified field
$v(\theta)=3/2$, while $\xi-\eta\in p\mathbb Z_p$ and $\zeta/d$ is
integral; hence $\mu\equiv\lambda\pmod{\mathfrak m}$ and
$v(\nu)\ge1$. The normalized basis has residual valuation five:
its row normalization has unit determinant and the binary changes have
unit determinant. Thus $v_p(N\nu)=5-3=2$; conjugation preserves the
ramified valuation, giving $v(\nu)=1$ exactly.
The anchor reduces to $-w/R_1$ in either local realization. Therefore

$$
C\equiv\lambda^2+\lambda w/R_1
       =\lambda^2(1+gtw)=\lambda^2\kappa\pmod{\mathfrak m}.
$$

The original product (4.10) implies that
$z_1-\lambda$ and $z'_1-\lambda$ are units; these are the reductions
of $W,W'$ and their conjugates. Hence $N(W)$ and
$N(W)-N(\nu)$ are units. This treats the ramified field without
assuming two independent $\mathbb Q_p$ components.
The actual equations determine the second endpoint by a $2$ by $2$
linear system with determinant $N(W)-N(\nu)$, so there is no actual
basepoint of this rational graph.

### 4.3 Affine lines: a complete argument without a fiber weight

**Lemma 4.3 (Classification of the affine-line curves).**

Over an algebraically closed field of characteristic zero, consider

$$
\tag{4.14}
 uU=a(v+V)+c,\qquad vV=b(u+U)+d,\qquad ab\ne0.
$$

Every nonconstant morphism $\mathbb A^1$ into this affine surface is
contained in one of at most sixteen fixed coordinate fibers. For
$u=k$ or $U=k$ the possible constants are $k=0$ and the roots of

$$
H_u(k)=bk^3+dk^2+bck+a^2b^2.
$$

For $v=k$ or $V=k$ they are $k=0$ and the roots of

$$
H_v(k)=ak^3+ck^2+adk+a^2b^2.
$$

For $u=0$, the fiber is the polynomial curve

$$
v=T,\qquad V=-c/a-T,\qquad U=(TV-d)/b.
$$

For $k\ne0$ with $H_u(k)=0$, the fiber $u=k$ is the union of the two
affine lines $v=ab/k$ and $V=ab/k$, with $U$ determined linearly.
The other fibers have the analogous descriptions.

*Proof.*

Pull back the four coordinates to polynomials. If all four are
nonconstant, their positive degrees $i,j,I,J$ satisfy

$$
i+I\leq\max(j,J),\qquad j+J\leq\max(i,I),
$$

which is impossible after addition. Thus some coordinate is constant.
For $u=k\ne0$, eliminate $U$ to obtain

$$
\tag{4.15}
 (kv-ab)(kV-ab)=H_u(k).
$$

If $H_u(k)\ne0$, both factors are constant polynomials, and then all
four coordinates are constant. Otherwise the descriptions follow from
(4.15) and the two equations. The
$k=0$ fiber is computed directly. The other coordinates follow by
exchanging endpoints and/or exchanging the two equations.

**Lemma 4.4 (No actual point on an $\mathbb A^1$ curve).**

The actual retained unit chart in (4.12) contains
no point on any geometric image of a nonconstant morphism
$\mathbb A^1$ into that affine section.

*Proof.*

Split the quadratic algebra over an algebraic closure. Equation
(4.12) becomes (4.14) with

$$
(u,v,U,V)=(W_+,W_-,W'_+,W'_-),\qquad
 (a,b,c,d)=(\nu_+,\nu_-,C_+,C_-).
$$

Here $a,b$ are nonzero and have positive valuation in the chosen
embeddings into $\overline{\mathbb Q}_p$, whereas $c,d$ are units. This holds
in the ramified field as well as in the locally split algebra. Every actual $u,v,U,V$ is a
unit by Lemma 4.2. If an $\mathbb A^1$ image
contained such a point, Lemma 4.3 would
put it in a constant fiber. Its constant $k$ would be a unit. But

$$
H_u(k)\equiv dk^2\ne0\pmod{\mathfrak m},\qquad
 H_v(k)\equiv ck^2\ne0\pmod{\mathfrak m},
$$

and $k\ne0$, contradicting that classification. A curve defined over an
extension causes no exception: at an actual point its constant equals
the corresponding actual unit coordinate in an embedding into
$\overline{\mathbb Q}_p$. The finitely many constants in the
classification are algebraic.

**Lemma 4.5 (Actual partners on a fixed rational endpoint line).**

For every $\varepsilon>0$, the actual pairs in $\mathcal E$ with first
endpoint on any fixed rational affine line number
$O_{\varepsilon,C_0}(p^\varepsilon)$, uniformly in the line and across
all residual layers. The same is true for a fixed second-endpoint line.

*Proof.*

If at most one actual integer first endpoint lies on the line, partner
uniqueness proves the assertion. Otherwise choose an actual integer
point $z_0$ and the primitive integer direction $v_0$ obtained from two
actual points. All integer points on the line are $z_0+nv_0$, $n\in\mathbb Z$.
The heights of $z_0,v_0$ are fixed powers of $p$, regardless of any
initial presentation of the line.

The two row-space relations give two rational bilinear endpoint
equations, with polynomial-height coefficients obtained from minors
of three independent actual rows. Cramer’s rule and restriction to
the line express the second endpoint as

$$
z'_1=\frac{N_1(n)}{D(n)},\qquad
  z'_2=\frac{N_2(n)}{D(n)},
$$

with degrees at most two and polynomial-height rational coefficients.
The denominator is nonzero at every actual point by
Lemma 4.2; in particular it is not identically
zero. Cancel a common polynomial gcd, and clear denominators, to obtain
integer polynomials of the same bounded degrees and polynomial height
with $\gcd(D,N_1,N_2)=1$ over $\mathbb Q[T]$. Bounded-degree
subresultants, or the elementary fixed-degree factor-height bound,
preserve a polynomial height in this operation.

Suppose first that $D$ is nonconstant. At most two distinct algebraic
roots of $D$ each exclude at most one $j$ from $\{0,1,2\}$ for which
$N_1+jN_2$ vanishes at that root. Thus one such $j$ satisfies
$\gcd(D,N_1+jN_2)=1$. Its nonzero integer resultant $R$ with $D$ has
polynomial height. The integral Sylvester adjugate identity gives

$$
A(T)D(T)+B(T)(N_1(T)+jN_2(T))=R\ne0
$$

for integral polynomials $A,B$. At an actual integer parameter $n$,
the second endpoint has integer lattice coordinates, so
$D(n)\mid N_1(n),N_2(n)$ and hence $D(n)\mid R$. There are
$2\tau(|R|)$ possible signed divisors, and each equation $D(n)=r$
has at most two integer roots. The usual divisor bound therefore gives
$O_\varepsilon(p^\varepsilon)$ parameters.

If $D$ is a nonzero constant, all four endpoint coordinates are
polynomial functions of $n$ over $\mathbb Q$. The two bilinear
relations hold identically, so this is a nonconstant morphism
$\mathbb A^1$ into the affine section. It is nonconstant because its
first endpoint varies on a line. Lemma 4.4
excludes every actual point on its image. No actual basepoint was
removed in taking the rational graph, so there is no omitted family
in this case. This proves the first assertion; exchange the two
endpoints for the second. The proof counts integer endpoints directly,
and uses no physical line-fiber multiplicity.

### 4.4 A uniform factor count and affine row planes

**Lemma 4.6 (Bounded-degree algebraic factors).**

Fix $d_*,M\geq1$. Uniformly for number fields $F$ of degree at most
$d_*$ and $0\ne C\in\mathcal O_F$ with $|N_{F/\mathbb Q}C|\leq p^M$,
the number of pairs $A,B\in\mathcal O_F$ satisfying

$$
AB=C,\qquad |\sigma(A)|,|\sigma(B)|\leq p^M
       \quad\text{for every embedding }\sigma
$$

is $O_{\varepsilon,d_*,M}(p^\varepsilon)$.

*Proof.*

Put $n=|NC|$. Above each rational prime there are at most $d_*$ prime
ideals, so the number of ideal divisors of $(C)$ is at most
$\tau(n)^{d_*}$, and hence $O_\varepsilon(p^\varepsilon)$ after
budgeting the exponent. For a fixed principal ideal choose one allowed
generator $A_0$. Every other allowed generator is $A_0\epsilon$ with
$\epsilon\in\mathcal O_F^\times$. Nonzero algebraic integers of
degree at most $d_*$ whose embeddings are at most $p^M$ have every
embedding at least $p^{-M(d_*-1)}$ in absolute value, since their norm
is a nonzero integer. Thus the logarithms of all embedding absolute
values of $\epsilon=A/A_0$ lie in a box of sidelength $O_{d_*,M}(\log p)$.

For fixed degree there is a uniform positive lower bound for the height
of a non-torsion algebraic unit: combine finiteness of algebraic numbers
of bounded degree and height with the fact that height-zero units are
roots of unity. Consequently distinct unit logarithmic vectors, modulo
torsion, have a uniform positive separation. Packing this box gives
$(1+\log p)^{O(d_*)}$ possibilities. The number of roots of unity of
bounded degree is uniformly bounded. This proves the assertion, since
$B=C/A$ is then determined. In particular the argument uses neither a
class-number bound nor a regulator upper bound, uniformly in $F$.

For a row $b$ define the homogeneous cubic

$$
\mathfrak E(b)=m_b^2q_b-\ell_bm_br_b+\ell_b^2s_b.
$$

It is the resultant of $L_b$ and $Q_b$, including the case of a root
at infinity.

**Lemma 4.7 (A usable auxiliary baseline in every row plane).**

The polynomial $\mathfrak E|_{\mathcal V}$ is absolutely irreducible.
In particular it is not identically zero on a two-dimensional linear
subspace of $\mathcal V$. If $f$ is a primitive integer functional on
a rank-three integer row lattice in $\mathcal V$, and $b_0,c_0$ is an
integer basis of $\ker f$, one can choose
$b=b_0+jc_0$, $j\in\{0,1,2,3\}$, with $\mathfrak E(b)\ne0$.
The pair $b,c_0$ is still an integer basis of that kernel.

*Proof.*

Use (4.11). On $\mathcal V$,

$$
\mathfrak E=(\ell^2-dm^2)s
    +m\bigl[-\gamma\ell^2+(\xi-\eta)\ell m+\zeta m^2\bigr].
$$

The two homogeneous coefficients in $(\ell,m)$ have resultant

$$
(\zeta-\gamma d)^2-d(\xi-\eta)^2=-\mathcal D_0\ne0.
$$

They are coprime over the algebraic closure. Gauss’s lemma for a
primitive polynomial linear in $s$ proves absolute irreducibility.
Its vanishing on a whole linear plane would give a linear factor, a
contradiction. Finally the nonzero polynomial
$\mathfrak E(b_0+Tc_0)$ has degree at most three, so one of the four
displayed integer values is nonzero. These statements survive the
invertible rational binary-coordinate change used in the proof:
$\mathfrak E$ is a binary resultant and changes by a nonzero scalar.

**Lemma 4.8 (Every affine row plane has subpower many actual pairs).**

Let $\Gamma\subset\mathbb Z^5$ be a rank-three lattice containing the
actual rows and spanning $\mathcal V$. Suppose its basis has polynomial
height. Let $f:\Gamma\to\mathbb Z$ be a primitive nonzero integer
functional of polynomial height, and let $n$ be an integer of polynomial
height. Then

$$
\#\{e\in\mathcal E:f(\mathbf r_e)=n\}
      \ll_{\varepsilon,C_0}p^\varepsilon,
$$

where the constant also depends on the fixed exponents of these heights.

*Proof.*

Choose an integer basis $b_0,c_0$ for $\ker f$ and $h\in\Gamma$ with
$f(h)=1$. In fixed rank these can be chosen at polynomial height by
integer elimination and the extended Euclidean algorithm. By
Lemma 4.7, replace $b_0$ by
$b=b_0+jc_0$ with $\mathfrak E(b)\ne0$, and put $c=c_0$.
The auxiliary row $b$ need not be an actual endpoint row and no word
or modular-unit property is required of it.

The binary cubic $P_{b,c}=L_bQ_c-L_cQ_b$ is nonzero. Otherwise the
coprimality of $L_b,Q_b$, supplied by $\mathfrak E(b)\ne0$, would force
$c$ to be proportional to $b$. There is a projective algebraic root
$\vartheta=[\vartheta_0:\vartheta_1]$ of $P_{b,c}$ for which
$L_b(\vartheta)\ne0$. Indeed if all its roots were the unique root of
$L_b$, then $P_{b,c}=\rho L_b^3$. Evaluation at that root first gives
$L_c=\tau L_b$, then $Q_c-\tau Q_b=\rho L_b^2$. The nonzero row
$c-\tau b$ would be the pure kernel with a square quadratic, contrary
to (4.7).

If $\vartheta$ is finite choose $\vartheta_0=1$; the field
$\mathbb Q(\vartheta_1)$ has degree at most three. If it is the point
at infinity use $\vartheta=(0,1)$
and the field $\mathbb Q$. All coefficients and root heights are
polynomially bounded: the cubic has bounded degree and polynomial
coefficient height, and its primitive irreducible factors and their
roots have polynomial height. Define the endpoint and anchor projections

$$
Z=\vartheta_0z_1+\vartheta_1z_2,\qquad
 Z'=\vartheta_0z'_1+\vartheta_1z'_2,\qquad
 A_\vartheta=\vartheta_0a_1+\vartheta_1a_2.
$$

Every row in the layer is $\mathbf r_e=i b+j c+n h$ with integers
$i,j$. Since $P_{b,b}=0$ and $P_{b,c}(\vartheta)=0$,

$$
P_{b,e}(\vartheta)=nP_{b,h}(\vartheta).
$$

Using $Q_e(\vartheta)=ZZ'$ and
$L_e(\vartheta)=Z+Z'-A_\vartheta$ gives the exact identity

$$
\tag{4.16}
 \begin{split}
 &[L_b(\vartheta)Z-Q_b(\vartheta)]
  [L_b(\vartheta)Z'-Q_b(\vartheta)]\\
 &\quad=Q_b(\vartheta)^2
       -L_b(\vartheta)Q_b(\vartheta)A_\vartheta
       +nL_b(\vartheta)P_{b,h}(\vartheta).
 \end{split}
$$

This right side is fixed on the whole affine plane $f=n$.

For clarity, the algebraic denominators cause no loss of uniformity.
If the finite coordinate $\vartheta_1$ has primitive minimal polynomial
with leading coefficient $A_0$, then $A_0\vartheta_1$ is integral. A fixed bounded
power of $A_0$, together with the fixed rational denominators of the
chosen coordinates, clears the factors in
(4.16). Its size is a fixed power of $p$.
The resulting factors are algebraic integers; every embedding and the
norm of their fixed product are bounded by fixed powers of $p$.
For infinity the same statement holds in $\mathbb Q$ directly.

If the product is nonzero, Lemma 4.6
gives $O_\varepsilon(p^\varepsilon)$ ordered factor values. For a
finite nonrational $\vartheta_1$, the map
$(z_1,z_2)\mapsto z_1+\vartheta_1 z_2$ is injective on $\mathbb Z^2$.
Since $L_b(\vartheta)\ne0$, a factor value then fixes the first
endpoint, and partner uniqueness finishes the count. If $\vartheta$
is rational, including infinity, a factor value instead puts that
endpoint on one rational affine line. Apply
Lemma 4.5, using a smaller epsilon in the
factor estimate and in the line estimate.

If the fixed product is zero, at least one factor is zero. For
nonrational $\vartheta$ that fixes at most one endpoint on that side;
for rational $\vartheta$, including infinity, it specifies a rational
affine endpoint line. Apply the same injection or line estimate and,
for the second side, exchange the endpoints. This adds only a factor
two. Thus zero products and projections at infinity are included,
and the affine-plane estimate follows.

### 4.5 A thin integer functional and the ninth-root loss

*Proof of Theorem 4.1.*

Let $\Gamma=\sum_{e\in\mathcal E}\mathbb Z\mathbf r_e$. This is a
rank-three integer lattice. Choose an integer basis and let
$D_\Gamma$ be (4.4) on that basis. It is a nonzero
integer. By (4.5), for all actual triples,

$$
\tag{4.17}
 \mathcal D(\mathbf r_{e_1},\mathbf r_{e_2},\mathbf r_{e_3})
   =D_\Gamma\det_\Gamma
       (\mathbf r_{e_1},\mathbf r_{e_2},\mathbf r_{e_3})^3.
$$

Actual rows generate $\Gamma/p\Gamma$, so three of them have
$\Gamma$-determinant a $p$-unit. Equation
(4.8) applied to this triple gives

$$
\tag{4.18}
  v_pD_\Gamma=5,\qquad |D_\Gamma|\geq p^5.
$$

Choose three actual rows $x_1,x_2,x_3$ with maximal absolute
$\Gamma$-determinant $d$. It is a positive integer. Equations
(4.8) and
(4.17) imply

$$
\tag{4.19}
  d^3p^5\leq d^3|D_\Gamma|\leq C_DB^7,\qquad d\leq K^{1/3}.
$$

In particular this nonzero-residual branch is empty when $K<1$.
By Cramer’s rule and the maximality of $d$, every actual row is

$$
\tag{4.20}
  \mathbf r_e=t_1x_1+t_2x_2+t_3x_3,\qquad |t_i|\leq1.
$$

Identify $\Gamma$ with $\mathbb Z^3$ and put the coordinates of the
$x_i$ in the columns of $X_0$. The sublattice
$X_0^{\mathsf T}\mathbb Z^3\subset\mathbb Z^3$ has index $d$. Set
$m=\lceil d^{1/3}\rceil$. The cube $\{0,\ldots,m\}^3$ has more than
$d$ integer points. Two of them are congruent modulo this sublattice;
their nonzero difference is $X_0^{\mathsf T}f$ for an integer
functional $f\ne0$, and

$$
|f(x_i)|\leq m\qquad(i=1,2,3).
$$

Divide $f$ by the gcd of its coordinates to make it primitive; the
inequalities only improve. Equation (4.20)
then gives

$$
\tag{4.21}
 |f(\mathbf r_e)|\leq3m\qquad(e\in\mathcal E).
$$

Hence the actual rows occupy $O(1+d^{1/3})$ integer affine planes.

We verify the height condition rather than treating this functional as
an arbitrary supplier. The actual row entries have fixed polynomial
height. A fixed-rank Hermite basis of their generated lattice has fixed
polynomial height, as do the coordinates of the $x_i$ in it, by minors
and Cramer’s rule. In the pigeonhole construction,
$f=(X_0^{\mathsf T})^{-1}v$ with $|v_i|\leq m$ and $d\geq1$; its
height is consequently polynomial. A kernel basis and a complementary
vector for primitive $f$ again have polynomial height by fixed-rank
integer elimination. The layer values in
(4.21) have polynomial height as well.

Lemma 4.8 therefore applies uniformly to all
these planes, proving

$$
\#\mathcal E\ll_\varepsilon p^\varepsilon(1+d^{1/3})
       \ll_\varepsilon p^\varepsilon(1+K^{1/9}),
$$

as required. The decomposition was by an auxiliary integer functional,
not by the original residual layer. All actual pairs in $\mathcal E$,
including the original zero and nonzero layers, occur in the counted
planes, and the zero-product case in
(4.16) was retained. This completes the
all-layer count.

**Remark 4.9.**

The estimate is uniform for the specified actual rank-three family.
It does not say that every endpoint family at the same middle has the
same derivative parameter or rational span. For the original maximum
bad-degree average, one first chooses a single actual maximizing
baseline, then applies the theorem to the corresponding common-parameter
nonzero-residual rank-three family. Empty, lower-rank, zero-residual,
other-rank and nonunit-chart strata require their separate estimates.
The all-layer proof itself introduces neither another baseline sum nor
a physical multiplicity factor.

## 5. The retained ideal-only auxiliary average

This section retains the complete older ideal-only estimate, restricted
to the unramified nonsplit $j=3$ stratum. Its common index, norm and
Archimedean arguments are later instantiated separately for ramification
and for the new joint count; its splitting hypotheses are not silently
dropped. Throughout this section, $p$ is an odd prime and $A=XY$, where

$$
\tag{5.1}

 p^{3/2}\le X\le Y,\qquad 3Y<p^2.
$$

The coefficients in the original word are fixed. In particular, none of
the averages below is over a coefficient of the word.
Write

$$
\tag{5.2}

 H_1=C\frac{X^2A}{p^6},\qquad
 H_2=C\frac{A^2}{p^6},\qquad
 H_3=C\frac{Y^2A}{p^6},\qquad
 D_{\max}=C'\frac{A^4}{p^{14}},
$$

where $C,C'$ are fixed constants, enlarged when necessary. Thus
$H_1\le H_2\le H_3$, $H_1H_3=H_2^2$, and $H_3\ll p^2$.
We use $K$ for a common bound for the nonzero Dixon layers and assume
$1\le K<p$. If the layer bound is less than one, the nonzero branch is
empty.

We count primitive kernel polynomials

$$
\tag{5.3}

 F(T)=a+bT+cT^2,\qquad c>0,\qquad
 |a|\le H_1,\quad |b|\le H_2,\quad c\le H_3,
$$

with

$$
\tag{5.4}

 \Delta=b^2-4ac=p^2d,\qquad
 0<|d|\le D_{\max},\qquad
 p\nmid abcd,
$$

where $d$ is not a rational square and is a nonzero square modulo $p$.
The sign convention $c>0$ chooses one generator of each kernel line.

The kernels under consideration come from a selected actual family of
physical rows

$$
\tag{5.5}

 r_i=(q_i,r_i',s_i,\ell_i,m_i),\qquad
 \begin{split}
 Q_i(T)&=q_i+r_i'T+s_iT^2=(x_i+u_iT)(y_i+v_iT),\\
 L_i(T)&=\ell_i+m_iT
       =(x_i+y_i+w)+(u_i+v_i+t)T,
 \end{split}
$$

where the integer endpoints satisfy
$|x_i|,|y_i|,|w|\le X$ and $|u_i|,|v_i|,|t|\le Y$.
Their rational span $W$ has dimension three and a nonzero Dixon residual.
The kernel of $W\longrightarrow\mathbb Q^2$ under projection to
$(\ell,m)$ is the line generated by $(a,b,c,0,0)$.
The endpoint and middle vectors lie in

$$
\tag{5.6}

 \Gamma_{w,t}
 =\{(x,u)\in\mathbb Z^2:wu-tx\equiv0\pmod {p^3}\},
 \qquad p\nmid wt.
$$

This lattice has index $p^3$.

We recall the local properties of the selected rank-three branch that
will be used. In an oriented basis of $\Gamma_{w,t}$, its coordinate
rows are $p$-saturated, their $(\ell,m)$ projection has a $p$-unit minor,
and an independent actual triple has

$$
\tag{5.7}

 D_{\mathrm{coord}}=p^5k,\qquad 0<|k|\le K<p.
$$

The change to physical endpoints has determinant $p^3$. The unramified
nonsplit $j=3$ branch considered here means that the transformed primitive coordinate kernel has
content exactly $p^3$. After a $p$-integral shear to the common slope,
the coordinate kernel and a projection-normalized local basis have the
form

$$
\tag{5.8}

 \begin{split}
 &(a_c,b_c,c_c),\qquad
   v_p(a_c)=3,\quad v_p(b_c)=1,\quad v_p(c_c)=0,\\
 &u_c=(\xi_c,\gamma_c,0,1,0),\qquad
   v_c=(\zeta_c,\eta_c,0,0,1),
 \end{split}
$$

where $\xi_c,\eta_c$ are $p$-units and $\zeta_c\in p^3\mathbb Z_p$.
The two coordinate root offsets have valuations $2,1$. In the local
normalization $c_c=1$, $E_c=\zeta_c-(\xi_c-\eta_c)\tau-\gamma_c\tau^2$,
so its values have valuations at least $3,2$, respectively. Their product
has valuation five by the normalized Dixon/norm identity; hence the
valuations are exactly $3,2$ in that order. These are properties of the
one selected family with its common derivative parameter. They are not imposed on an unfiltered family with varying
parameters.

**Lemma 5.1 (Cofactor content and the small layer).**

For an independent actual coordinate triple, write

$$
([q,\ell,m],[r',\ell,m],[s,\ell,m])
       =m_0(a_c,b_c,c_c),\qquad m_0>0,
$$

where the brackets denote three-column minors and the coordinate kernel
is primitive. Let $\mathcal L=W\cap\mathbb Z^5$, let $G$ be the index
in $\mathcal L$ of the actual physical three-row lattice, and put

$$
P=\operatorname{pr}_{\ell,m}(\mathcal L),\qquad
 h=[\mathbb Z^2:P].
$$

There is a positive integer $\iota$, prime to $p$, such that

$$
\tag{5.9}

 G=p^6\iota,\qquad m_0=\iota h,\qquad p\nmid h,
 \qquad k=\iota^3\varkappa,
 \qquad h\mid\varkappa.
$$

In particular $\iota^3h\mid k$ and $1\le h\le|\varkappa|\le K$.

*Proof.*

The displayed cofactor vector is the pure quadratic vector obtained by
eliminating $\ell,m$. The last row of the Dixon matrix is exactly this
vector: its entries are $[m,q,\ell],[m,r',\ell],[m,s,\ell]$, and the
cyclic column permutations have positive sign. Thus $m_0$ divides
$D_{\mathrm{coord}}$. Coordinate saturation and the unit projection
minor imply $p\nmid m_0$, so $m_0\mid k$.

The exact sequence

$$
0\longrightarrow\mathbb Z(a,b,c,0,0)
 \longrightarrow\mathcal L\longrightarrow P\longrightarrow0
$$

shows that the cofactor content on a basis of $\mathcal L$ is $h$.
Indeed, lift a basis of $P$ and adjoin the primitive kernel vector.
Passing to the actual triple multiplies all three-column minors by $G$,
so the physical cofactor content is $Gh$. On the other hand, physical
change of variables acts on this vector by
$\det(M)\operatorname{Sym}^2(M)$, where $\det(M)=p^3$. The $j=3$
content therefore gives

$$
\tag{5.10}

 Gh=p^6m_0.
$$

For completeness, the physical Smith valuations are $(0,3,3)$.
Compatible integral local changes reduce the endpoint map to
$\operatorname{diag}(1,p^3)$, up to units. The basis
(5.8) becomes

$$
\begin{pmatrix}
 \xi_c&p^3\gamma_c&0&1&0\\
 \zeta_c&p^3\eta_c&0&0&p^3\\
 a_c&p^3b_c&p^6c_c&0&0
 \end{pmatrix}.
$$

After the unit pivot in the $\ell$ column, the last two rows are
divisible by $p^3$. Upon dividing them by $p^3$, their $(q,m)$ minor is
$-a_c/p^3$, a unit. Hence $G=p^6\iota$ with $p\nmid\iota$.
Equation (5.10) now gives
$m_0=\iota h$ and $p\nmid h$.

The Dixon residual is cubic in the complete Plücker vector, and its
physical change-of-variables weight is seven. Thus

$$
D_{\mathrm{phys}}=p^{21}D_{\mathrm{coord}}=p^{26}k,
 \qquad G^3\mid D_{\mathrm{phys}}.
$$

Since $p\nmid\iota$, we have $\iota^3\mid k$. On a basis of
$\mathcal L$ the residual is, up to orientation, $p^8\varkappa$.
Its last Dixon row has content $h$, so $h\mid p^8\varkappa$.
As $p\nmid h$, this proves $h\mid\varkappa$.

Put $F_d=\mathbb Q(\sqrt d)$ and

$$
\tag{5.11}

 \theta=\frac{-b+p\sqrt d}{2c},\qquad
 \mathcal O=\mathcal O_{p^2d},\qquad
 \mathcal O_0=\mathcal O_d,\qquad
 J=\mathbb Z+\mathbb Z\theta.
$$

The subscript on an order denotes its discriminant. In particular
$\mathcal O=\mathbb Z+p\mathcal O_0$ and
$[\mathcal O_0:\mathcal O]=p$; $\mathcal O_0$ need not be maximal.
Ideal norms are positive, and the norm of a field element is used with
its absolute value when it occurs in an ideal-norm formula.

The projection-normalized rows in $W$ are uniquely determined by

$$
u=(\xi,\gamma,0,1,0),\qquad
 v=(\zeta,\eta,0,0,1).
$$

Define

$$
\tag{5.12}

 U=\xi+\gamma\theta,\qquad
 V=\zeta+\eta\theta,\qquad E=V-\theta U.
$$

Every row in $W$ then satisfies $Q(\theta)=U\ell+Vm$.

**Lemma 5.2 (The actual principal ideal).**

The fractional $\mathcal O$-ideal $J$ is proper and invertible, with
$N(J)=1/c$. The element $E$ is nonzero and satisfies

$$
\tag{5.13}

 |N_{F_d/\mathbb Q}(E)|
     =\frac{p^8|\varkappa|}{h^3c^3}.
$$

Its two $p$-adic components have valuations $3,5$, up to exchange.
There are a split prime $\mathfrak p$ above $p$ in $\mathcal O_0$ and
an integral invertible $\mathcal O_0$-ideal $\mathfrak A$, prime to $p$,
such that, with $J_0=J\mathcal O_0$,

$$
\tag{5.14}

 (hE)\mathcal O_0
       =(p)^3\mathfrak p^2\mathfrak A J_0^3,
 \qquad
 n:=N(\mathfrak A)=\frac{|\varkappa|}{h}\le K.
$$

Consequently

$$
\tag{5.15}

 [J_0]^3=[\mathfrak p]^{-2}[\mathfrak A]^{-1}
       \quad\text{in }\operatorname{Pic}(\mathcal O_0).
$$

*Proof.*

The primitive quadratic form gives the proper invertible ideal

$$
I=(c,(-b+p\sqrt d)/2),\qquad N(I)=c,
$$

and $J=I/c$. Primitivity is sufficient for invertibility; coprimality
of $c$ with the remaining conductor is not needed.

For a triple write $H=[s,\ell,m]$. Its determinant in the ordered basis
$u,v,(a/c,b/c,1,0,0)$ is $H$. Direct evaluation of the Dixon matrix gives

$$
\tag{5.16}

 N(E)=-\frac{D}{H^3}.
$$

For example, if $\omega=\xi-\eta$, the norm on the left is

$$
\left(\zeta+\frac{a\gamma}{c}\right)^2
 +\left(\omega-\frac{b\gamma}{c}\right)
       \left(\frac{a\omega+b\zeta}{c}\right),
$$

which is the negative normalized residual. For a basis of $\mathcal L$,
$H=\pm hc$ and $D=\pm p^8\varkappa$, proving
(5.13).

Every integral row evaluates into $J^2$. Since $h\mathbb Z^2\subset P$,
there are integral rows with projections $(h,0)$ and $(0,h)$. Hence
$hU,hV\in J^2$, and $hE\in J^3$, because $1,\theta\in J$ and
$J^2\subset J^3$. The ideal

$$
\mathfrak B=(hE)J^{-3}
$$

is therefore integral and invertible, with

$$
\tag{5.17}

 N(\mathfrak B)=\frac{p^8|\varkappa|}{h}.
$$

We verify the two local valuations, retaining their pairing. Write the
physical endpoint matrix as $M=\left(\begin{smallmatrix}r&v\\s&z \end{smallmatrix}\right)$, with $\det M=p^3$ and $r,s$ units.
For a physical root $\theta$, the corresponding coordinate root is
$\tau=(v+z\theta)/(r+s\theta)$. Projection normalization gives exactly

$$
\tag{5.18}

 E_{\mathrm{phys}}(\theta)
       =\frac{(r+s\theta)^3}{p^3}E_{\mathrm{coord}}(\tau),
 \qquad
 \tau-\frac vr=\frac{p^3\theta}{r(r+s\theta)}.
$$

The physical roots are units. The coordinate offsets of valuations
$2,1$ therefore give valuations $1,2$ for $r+s\theta$, paired with
coordinate residual valuations $3,2$. Formula
(5.18) gives $3,5$ for $E$.

At $p$ we have $J=\mathcal O$ locally, since $p\nmid c$.
Extending $\mathfrak B$ to $\mathcal O_0$ preserves its norm away from
$p$ and gives local exponents $3,5$ at $p$. Thus
$p^{-3}\mathfrak B\mathcal O_0$ is integral and invertible, with local
exponents $0,2$. As $0<|\varkappa|<p$, it is uniquely of the form
$\mathfrak p^2\mathfrak A$, where $\mathfrak A$ is integral,
invertible and prime to $p$, of norm $|\varkappa|/h$.
This proves (5.14) and
(5.15). Primes dividing the remaining conductor
of $\mathcal O_0$ have not been removed from $\mathfrak A$.

**Lemma 5.3 (Short bases in a Euclidean lattice).**

Let $\Lambda$ be a lattice in $\mathbb R^2$ of covolume $V$.
The number of ordered $\mathbb Z$-bases $(u,v)$ of $\Lambda$ satisfying
$|u|,|v|\le R$ is $O(R^2/V)$, with an absolute constant.

*Proof.*

If such a basis exists, let $u_0$ be a shortest nonzero vector and put
$\lambda=|u_0|$. It is primitive, and an independent vector of length
at most $R$ gives $V\le\lambda R$. The only primitive vectors on its
central line are $\pm u_0$; their basis completions contribute
$O(1+R/\lambda)=O(R^2/V)$.

The other parallel lattice lines have spacing $V/\lambda$, with point
spacing $\lambda$ on each line. If a noncentral vector occurs in the
$T$-ball, then $T\ge\lambda$ and $T\lambda\ge V$. Counting lines and
then points shows that the number of noncentral vectors in that ball
is $O(T^2/V)$. For a primitive $u$ of length in $(T/2,T]$, its basis
completions form, for each orientation, an affine progression of step
$u$, with $O(1+R/T)$ terms in the $R$-ball. Summing over
$T=R,R/2,\ldots$ gives

$$
\sum_T O\left(\frac{T^2}{V}\left(1+\frac RT\right)\right)
       =O(R^2/V).
$$

**Proposition 5.4 (Height count with a fixed real ideal class).**

Fix $d>0$, a split branch $\mathfrak p\mid p$, an integral invertible
$\mathcal O_d$-ideal $\mathfrak A$ of norm $n\le K$, and a class
$[\mathfrak a]$ satisfying

$$
[\mathfrak a]^3=[\mathfrak p]^{-2}[\mathfrak A]^{-1}.
$$

The number of kernels (5.3) admitting actual
rows as above and having $[J_0]=[\mathfrak a]$ is

$$
\tag{5.19}

 \ll \frac{H_3}{\sqrt d}\log(2p).
$$

The constant is independent of the ideal representative, its generator,
and the regulator.

*Proof.*

Put $H=H_3$. Choose any invertible fractional representative
$\mathfrak a$, write $\nu=N(\mathfrak a)$, and choose a generator

$$
\tag{5.20}

 (\eta_0)=(p)^3\mathfrak p^2\mathfrak A\mathfrak a^3,
 \qquad |N(\eta_0)|=p^8n\nu^3.
$$

No bound on this representative or generator is required.
For each kernel choose $\chi\in F_d^\times$ with
$J_0=\chi\mathfrak a$. Since the two orders agree away from $p$, and
at $p$ we have $J=\mathcal O$ and $J_0=\mathcal O_0$, locally,

$$
\tag{5.21}

 [J_0:J]=p,
 \qquad \Lambda:=\chi^{-1}J\subset\mathfrak a,
 \qquad[\mathfrak a:\Lambda]=p.
$$

There are exactly $p+1$ index-$p$ subgroups of the free rank-two group
$\mathfrak a$, corresponding to the lines in
$\mathfrak a/p\mathfrak a$.

By (5.14),
$hE=\chi^3\eta_0\epsilon$ for a unit
$\epsilon\in\mathcal O_0^\times$. The units of a real quadratic order
are $\{\pm1\}$ times an infinite cyclic group, so

$$
|\mathcal O_0^\times/(\mathcal O_0^\times)^3|=3.
$$

Choose representatives $\epsilon_1,\epsilon_2,\epsilon_3$.
Absorbing a cube unit into $\chi$, we obtain

$$
\tag{5.22}

 hE=\chi^3\eta_r,
 \qquad \eta_r=\eta_0\epsilon_r,
 \qquad |N(\eta_r)|=p^8n\nu^3.
$$

This changes $\Lambda$ to a unit multiple inside $\mathfrak a$,
which is still one of the same $p+1$ subgroups. There is no additional
unit-index or ring-class factor.

We next obtain the height constraint that uses the actual rows. Since
their linear projections have rank two, choose $i,j$ for which
$M_{ij}=\ell_i m_j-\ell_jm_i\ne0$. Both projections lie in
$\Gamma_{w,t}$, so $p^3\mid M_{ij}$ and $|M_{ij}|\ge p^3$.
The exact identity

$$
\tag{5.23}

 L_i(\theta)Q_j(\theta)-L_j(\theta)Q_i(\theta)=M_{ij}E
$$

and the actual factorizations in
(5.5) imply, in either real embedding,

$$
\tag{5.24}

 |E_\sigma|
   \le\frac{6(X+Y|\theta_\sigma|)^3}{p^3}
   \le\frac{6Y^3}{p^3}(1+|\theta_\sigma|)^3,
 \qquad\sigma\in\{+,-\}.
$$

In particular all rational denominators in $U,V,E$ are retained in
(5.23).

Fix $r$ and $\Lambda$. The vectors

$$
v_1=\chi^{-1},\qquad v_2=\chi^{-1}\theta
$$

are a $\mathbb Z$-basis of $\Lambda$. Put
$T_\sigma=|(v_1)_\sigma|+|(v_2)_\sigma|$.
Since $N(J_0)=1/c$, we have
$|N(\chi)|=1/(c\nu)$. The norm, trace and discriminant of $\theta$
give

$$
\tag{5.25}

 T_+T_-
   =\nu\bigl(|a|+c+\max\{|b|,p\sqrt d\}\bigr)
   \le(2+\sqrt5)\nu H=:M.
$$

Here the cross products use
$|x|+|y|=\max\{|x+y|,|x-y|\}$ for real $x,y$.
The embedded lattice $\Lambda$ has covolume $p\nu\sqrt d$.

On the other hand, (5.22) and
(5.24) give

$$
|(\eta_r)_\sigma|
   =h|E_\sigma||(v_1)_\sigma|^3
   \le\frac{6KY^3}{p^3}T_\sigma^3.
$$

Consequently

$$
\tag{5.26}

 T_\sigma\ge\mathcal L_\sigma
      :=\frac{p|(\eta_r)_\sigma|^{1/3}}{(6K)^{1/3}Y},
 \qquad
 \mathcal L_+\mathcal L_-
      =\frac{p^{14/3}n^{1/3}\nu}{(6K)^{2/3}Y^2}.
$$

Thus $T_+$ lies between $\mathcal L_+$ and $M/\mathcal L_-$,
an interval of multiplicative width

$$
\tag{5.27}

 \frac{M}{\mathcal L_+\mathcal L_-}
   \ll\frac{HY^2K^{2/3}}{p^{14/3}n^{1/3}}
   \ll p^2.
$$

The last estimate uses $H\ll p^2$, $Y<p^2$, $K<p$, and $n\ge1$.
If the width is less than one there are no kernels. Otherwise the
interval is covered by $O(\log(2p))$ dyadic intervals.

On an interval $S\le T_+<2S$, we have $T_-\le M/S$.
The determinant-one real map

$$
(x_+,x_-)\longmapsto
 \left(\frac{\sqrt M}{S}x_+,\frac{S}{\sqrt M}x_-\right)
$$

sends both basis vectors into the ball of radius $\sqrt{5M}$.
Lemma 5.3 bounds their number by

$$
O\left(\frac{M}{p\nu\sqrt d}\right)
       =O\left(\frac{H}{p\sqrt d}\right).
$$

The ordered basis determines $\theta=v_2/v_1$ and hence its primitive
integer minimal polynomial, with the chosen sign $c>0$. Thus this is
a count of kernels, even when a kernel has several actual witnesses.
Multiplying by the dyadic intervals, the three unit classes, and the
$p+1$ subgroups proves (5.19).
There is no summation over $h,\iota,\varkappa$.

**Lemma 5.5 (Uniform count of small integral ideals).**

For every $\delta>0$ there is a constant $C_\delta$ such that, for
every quadratic order $\mathcal O$ and every real $K\ge1$,

$$
\tag{5.28}

 \#\{I\subset\mathcal O:I\text{ is an integral ideal},\quad
                         [\mathcal O:I]\le K\}
       \le C_\delta K^{1+\delta}.
$$

The constant is independent of the discriminant and conductor, and
the count includes noninvertible ideals.

*Proof.*

Choose an integral basis $\mathcal O=\mathbb Z+\mathbb Z\omega$ with
$\omega^2=t\omega-n$, where $t,n\in\mathbb Z$. Every finite-index
additive subgroup has a unique Hermite normal form

$$
I=\mathbb Za+\mathbb Z(b+c\omega),\qquad
 a,c>0,\quad 0\le b<a.
$$

Stability under multiplication by $\omega$ first requires
$c\mid a$ and $a\mid(a/c)b$. Writing $a=cA$, these are equivalent
to $b=cB$ for some $0\le B<A$. For the other generator,

$$
\omega(b+c\omega)-(B+t)(b+c\omega)
       =-c(B^2+tB+n).
$$

Thus the necessary and sufficient conditions for an ideal are

$$
\tag{5.29}

 a=cA,\qquad b=cB,\qquad 0\le B<A,\qquad
 A\mid B^2+tB+n,
 \qquad [\mathcal O:I]=c^2A.
$$

Multiplication by $\omega$ suffices since $\mathcal O=\mathbb Z[\omega]$.
No assumption about invertibility or the conductor has been made.

Let $r(A)$ count the roots of $B^2+tB+n$ modulo $A$, with $r(1)=1$.
For an odd prime $\ell$, completing the square gives the equivalent
congruence

$$
(2B+t)^2=t^2-4n\pmod{\ell^e}.
$$

If the right side is zero modulo $\ell^e$, there are
$\ell^{\lfloor e/2\rfloor}$ roots. Otherwise its valuation must be
$2u<e$. Dividing by $\ell^{2u}$ leaves at most two unit roots modulo
$\ell^{e-2u}$, each with $\ell^u$ lifts. Therefore

$$
\tag{5.30}

 r(\ell^e)\le2\ell^{\lfloor e/2\rfloor}
       \quad(\ell\text{ odd}),\qquad
 r(2^e)\le4\cdot2^{\lfloor e/2\rfloor}.
$$

For the second bound, if $t$ is odd the derivative is odd and there
are at most two roots, each lifting uniquely. If $t$ is even, use
$(B+t/2)^2=t^2/4-n$. A nonzero right side of valuation $2u<e$
reduces to a unit square root modulo $2^{e-2u}$, with at most four
roots and $2^u$ lifts per root. When it is zero modulo $2^e$ there
are $2^{\lfloor e/2\rfloor}$ roots. The bound of four for unit
square roots also includes exponents one and two, where the sharper
bounds are one and two. For higher exponents, any two odd roots
$y,z$ satisfy $(y-z)(y+z)\equiv0\pmod{2^e}$; the smaller valuation
of the factors is one, so $z\equiv\pm y\pmod{2^{e-1}}$.

By the Chinese remainder theorem, $r$ is multiplicative. Write
$A=u^2v$ uniquely with $v$ squarefree. The bounds
(5.30) give

$$
r(A)\le4\,2^{\omega(A)}u\ll_\eta A^\eta u
       \qquad(\eta>0),
$$

where $\omega(A)$ here denotes the number of distinct prime divisors.
This estimate is uniform in $t,n$. Consequently, for $T\ge1$,

$$
\begin{aligned}
 F(T):=\sum_{A\le T}r(A)
   &\ll_\eta T^\eta
         \sum_{u\le\sqrt T}u\left\lfloor\frac{T}{u^2}\right\rfloor\\
   &\ll_\eta T^{1+\eta}\log(2T).
\end{aligned}
$$

Dropping the squarefree restriction on $v$ only enlarges this sum.
Finally (5.29) yields

$$
\begin{aligned}
 \#\{I:[\mathcal O:I]\le K\}
   &=\sum_{c\le\sqrt K}F(K/c^2)\\
   &\ll_\eta K^{1+\eta}\log(2K)
                  \sum_{c\ge1}c^{-2-2\eta}
    \ll_\eta K^{1+\eta}\log(2K).
\end{aligned}
$$

Taking $\eta=\delta/2$ and absorbing the logarithm proves
(5.28). In this argument ideal norm
means additive index; no norm factorization for noninvertible ideals
is required.

**Proposition 5.6 (Both signs of the discriminant).**

Let $N_+$ and $N_-$ be the numbers of kernels admitting the actual
generation above with respectively $d>0$ and $d<0$. For every
$\delta>0$,

$$
\tag{5.31}

 \begin{aligned}
 N_-&\ll_\delta H_3\sqrt{D_{\max}}K^{1+\delta},\\
 N_+&\ll_\delta H_3\sqrt{D_{\max}}K^{1+\delta}\log(2p).
 \end{aligned}
$$

In particular, for every $\varepsilon>0$,
$N_++N_-\ll_\varepsilon p^\varepsilon H_3\sqrt{D_{\max}}K$.

*Proof.*

For an order discriminant $d$, put
$t_3(d)=|\operatorname{Pic}(\mathcal O_d)[3]|$.
For fixed $\mathfrak p,\mathfrak A$, equation
(5.15) admits at most $t_3(d)$ classes $[J_0]$.
Lemma 5.5 gives, uniformly in $d$,

$$
\tag{5.32}

 \#\{\mathfrak A:N(\mathfrak A)\le K\}
       \ll_\delta K^{1+\delta}.
$$

The count includes every integral invertible ideal, even at
primes in the remaining conductor. There are two choices of
$\mathfrak p$.

For $d>0$, Proposition 5.4 now gives

$$
\tag{5.33}

 N_+\ll_\delta H_3K^{1+\delta}\log(2p)
          \sum_{0<d\le D_{\max}}\frac{t_3(d)}{\sqrt d},
$$

where the sum is over nonsquare real quadratic-order discriminants.

For $d<0$, a proper positive definite class of discriminant $\Delta$
has $O(H_3/\sqrt{|\Delta|})$ forms with coefficients bounded by $H_3$.
Indeed, realize it as an oriented complex ideal lattice of covolume
$\sqrt{|\Delta|}/2$; such forms arise from its bases with both vectors
of length at most $\sqrt{H_3}$, and apply
Lemma 5.3. Multiplication by $-1$
handles negative definite forms.
The extension map from $\operatorname{Pic}(\mathcal O_{p^2d})$ to
$\operatorname{Pic}(\mathcal O_d)$ has fibers of size at most $p-1$:
the order exact sequence has local term

$$
(\mathcal O_d/p\mathcal O_d)^*/(\mathbb Z/p\mathbb Z)^*,
$$

of order $p-1$ because $p$ splits. Combining this with
(5.32) and
(5.15) gives

$$
\tag{5.34}

 N_-\ll_\delta H_3K^{1+\delta}
          \sum_{-D_{\max}\le d<0}\frac{t_3(d)}{\sqrt{|d|}}.
$$

The use of the largest height $H_3$ is essential here; the analogous
bound with $H_2$ does not hold for arbitrary anisotropic boxes.

Bhargava–Varma [Bhargava–Varma, Theorem 2(a),(b)](#reference-bhargavavarma2016) prove the
finite mean values

$$
1+\frac{\zeta(2)}{\zeta(3)}\quad(d<0),\qquad
 1+\frac{\zeta(2)}{3\zeta(3)}\quad(d>0)
$$

for $t_3(d)$ over all orders in imaginary and real quadratic fields,
respectively, ordered by absolute discriminant. Their class group is
the group of invertible fractional ideals modulo principal ideals,
so it is the ordinary $\operatorname{Pic}(\mathcal O_d)$ used here.
In particular, for either sign,

$$
\tag{5.35}

 \sum_{0<\pm d\le D}t_3(d)\ll D,
 \qquad
 \sum_{0<\pm d\le D}\frac{t_3(d)}{\sqrt{|d|}}\ll\sqrt D,
$$

the second estimate following by partial summation. These are sums
over all quadratic orders, including nonmaximal orders. We simply drop
the restrictions $p\nmid d$ and splitting at $p$; no average with
varying local specifications is required. Inserting
(5.35) into
(5.33) and
(5.34) proves (5.31).
For the final estimate take $\delta=\varepsilon/2$ and use $K<p$
to bound $K^\delta\log(2p)\ll_\varepsilon p^\varepsilon$.

**Corollary 5.7 (The nonsplit contribution to the selected degree).**

Let $\mathcal M$ be the finite set of original middles being averaged.
At each middle start with one actual baseline attaining its maximum
derivative-zero degree. Denote by $b(w,t)$ and $\mathcal S(w,t)$ the
single baseline and actual ordered partner family retained in the
old auxiliary zero-reduction separation. This auxiliary corollary is
not used for the enlarged range. Define

$$
W(w,t)=\operatorname{span}_{\mathbb Q}
   \bigl(\{r_{b(w,t)}\}\cup\{r_e:e\in\mathcal S(w,t)\}\bigr).
$$

In particular the baseline row is retained even though its pencil is
zero. Let $\mathcal M_{\rm ns}$ consist of those middles for which this
span has rank three, has nonzero Dixon residual, and has unramified
nonsplit physical kernel in the $j=3$ branch. Put

$$
\mathsf d_{\rm ns}(w,t)=
 \begin{cases}
  |\mathcal S(w,t)|,&(w,t)\in\mathcal M_{\rm ns},\\
  0,&(w,t)\in\mathcal M\setminus\mathcal M_{\rm ns}.
 \end{cases}
$$

Thus the weight counts actual ordered partners, whereas a middle in
$\mathcal M_{\rm ns}$ is assigned only its one primitive kernel.
Assume the fixed-kernel middle bound and fixed-middle all-layer bound

$$
\tag{5.36}

 \#\{(w,t)\text{ assigned to one fixed kernel}\}\ll A/p^2,
 \qquad
 \mathsf d_{\rm ns}(w,t)
       \ll_\varepsilon p^\varepsilon(1+K^{1/9}).
$$

Then

$$
\tag{5.37}

 \sum_{(w,t)\in\mathcal M}\mathsf d_{\rm ns}(w,t)
   \ll_\varepsilon p^\varepsilon
       Y^2\frac{A^4}{p^{15}}K^{10/9}.
$$

If $A\le C_0p^\alpha$ and $K\le C_1A^7/p^{26}$, this retained
auxiliary contribution is $O_\varepsilon(Y^2p^\varepsilon)$ for every fixed
$\alpha<395/106$; the enlarged range uses Section 6.

*Proof.*

Each selected rank-three space has one primitive physical kernel.
Proposition 5.6 and the first bound in
(5.36) give

$$
\#\mathcal M_{\rm ns}
   \ll_\varepsilon p^\varepsilon\frac A{p^2}
                      H_3\sqrt{D_{\max}}K
   \ll_\varepsilon p^\varepsilon Y^2\frac{A^4}{p^{15}}K.
$$

For a prescribed final $\varepsilon$, apply this kernel bound with
$\varepsilon/2$ and the all-layer input with $\varepsilon/2$.
The former uses the small-ideal lemma with exponent $\varepsilon/4$,
and the remaining logarithm is bounded by $O_\varepsilon(p^{\varepsilon/4})$.
Multiplication and $1+K^{1/9}\le2K^{1/9}$ now give
(5.37) with total loss at most $p^\varepsilon$.
There is one selected family per middle; no sum over all baselines or
over decompositions of a higher-rank family is present.

The power of $p$ relative to $Y^2$, apart from the arbitrarily small
subpower loss, is

$$
4\alpha-15+\frac{10}{9}(7\alpha-26)
       =\frac{106\alpha-395}{9}.
$$

It is strictly negative for the stated range. For example,
$\alpha=149/40$ gives $-1/60$. At $\alpha=26/7$ the saving is
$p^{-1/7}$ before the subpower loss.

## 6. The actual rank-three projection correlation

This section treats only $j=3$ rank-three nonzero-residual families:
unramified nonsplit, rationally split, and ramified. The $j=4$ branch
keeps (2.17). At each middle we keep the one selected actual
maximum baseline and its whole selected partner family in $W$, including
the baseline’s zero pencil. Every object below belongs to that same
family, with the original $g=a_1a_2$ fixed. Use the heights
$H_1,H_2,H_3,D_{\max}$ in (5.2), and fix once and for all

$$
\tag{6.1}
 K:=C_D\frac{A^7}{p^{26}},\qquad A=XY,
$$

where $C_D$ is a sufficiently large absolute constant covering *all*
actual triple residual bounds and the norm-height constants below.
This is a public common scale, not a potentially smaller intrinsic maximum.
If $K<1$ the nonzero branch is empty; for $A\le C_0p^{15/4}$,
$K\ll_{C_0}p^{1/4}<p$ for sufficiently large $p$.

### 6.1 The ramified index and principal ideal

Here we instantiate the ideal data for $v_p(\Delta_0)=3$ rather than
invoke the unramified statement with its splitting hypothesis removed.
Use $c>0$ and

$$
\Delta=b^2-4ac=p^2d,\quad v_p(d)=1,\quad
 \theta=\frac{-b+p\sqrt d}{2c},\quad
 J=\mathbb Z+\mathbb Z\theta,\quad \mathcal O=\mathcal O_{p^2d},\quad \mathcal O_0=\mathcal O_d.
$$

All other conductor primes of $\mathcal O_d$ remain in this order.
For the full physical lattice $L=W\cap\mathbb Z^5$ put
$P=\operatorname{pr}_{\ell,m}L$ and $h=[\mathbb Z^2:P]$, and define
$U,V,E=V-\theta U$ from its projection-normalized rows as in
(5.12).

**Lemma 6.1 (Ramified physical indices and ideal factor).**

For any independent actual triple there is $g_{\rm idx}\in\mathbb Z_{>0}$,
prime to $p$, such that

$$
G=[L:\langle r_1,r_2,r_3\rangle]=p^6g_{\rm idx},\quad
 D_L=\pm p^8\kappa,\quad |k|=g_{\rm idx}^3|\kappa|,\quad
 h\mid\kappa,\quad p\nmid h\kappa.
$$

Here $\kappa$ is the integer normalized residual, distinct from the
word-chart unit $1+gtw$. Thus $n=|\kappa|/h$ is a positive integer,
$h,n\le K$.
In the single ramified local field, with $v(p)=1$, $v(E)=4$.
There is an integral invertible $\mathcal O_d$-ideal $\mathfrak A$, prime to $p$,
with $N\mathfrak A=n$, for which

$$
\tag{6.2}
 (hE)\mathcal O_d=(p)^4\mathfrak A J_0^3,\qquad J_0=J\mathcal O_d,\qquad
 [J_0]^3=[\mathfrak A]^{-1}.
$$

The fixed principal factor has norm $p^8$, with no additional norm or
ramified-prime class factor.

*Proof.*

The coordinate saturated basis of Lemma 3.2
has $v(a_c)=3$, $v(b_c)\ge2$ and $c_c$ a unit. Compatible integral local
changes reduce the endpoint map to $\operatorname{diag}(1,p^3)$ up to
units. Its physical row image is

$$
\begin{pmatrix}
 \xi_c&p^3\gamma_c&0&1&0\\
 \zeta_c&p^3\eta_c&0&0&p^3\\
 a_c&p^3b_c&p^6c_c&0&0
 \end{pmatrix}.
$$

After the unit pivot in $\ell$, the remaining rows are divisible by $p^3$;
after dividing them by $p^3$ their $(q,m)$ minor is $-a_c/p^3$, a unit.
So the Smith valuations are exactly $(0,3,3)$. In the notation of
Lemma 5.1, coordinate cofactor content $m_0$ is
prime to $p$, physical cofactor transport gives $Gh=p^6m_0$, and hence
$m_0=g_{\rm idx}h$ and $p\nmid h$. Row and binary covariance give

$$
D_{\rm phys}=p^{21}D_{\rm coord}=p^{26}k=\pm G^3D_L.
$$

The last Dixon row on $L$ has content $h$, so $h\mid D_L$; since
$p\nmid h$, $h\mid\kappa$. Because $0<|k|\le K<p$, all stated
prime-to-$p$ and size assertions follow. This is the same cofactor
argument as before, now with its ramified Smith calculation supplied.

Let $\tau$ be the corresponding coordinate root. Exact transport is

$$
\tau-\frac vr=\frac{p^3\theta}{r(r+s\theta)},\qquad
 E=\frac{(r+s\theta)^3}{p^3}E_c(\tau).
$$

The coordinate offset has valuation $3/2$, so $v(r+s\theta)=3/2$.
Lemma 3.2 proved $v(E_c)=5/2$ from the
unique minimum term. Therefore $v(E)=3(3/2)-3+5/2=4$.
Conjugation here preserves valuation in one ramified field; it is not
a pair of independent $\mathbb Q_p$ components.

Primitivity gives $I=(c,(-b+p\sqrt d)/2)$ with
$I\overline I=c\mathcal O$: after dividing the product by $c$, the resulting
ideal contains $a,b,c$, hence $1$. Thus $J=I/c$ is proper invertible
and $N(J)=1/c$. The direct determinant identity
(5.16) remains valid, giving

$$
|N(E)|=\frac{p^8|\kappa|}{h^3c^3}
        =\frac{p^8n}{h^2c^3}.
$$

Rows over projections $(h,0),(0,h)$ show $hU,hV\in J^2$, hence
$e=hE\in J^3$. Therefore
$\mathfrak B=(e)J^{-3}$ is integral invertible of norm $p^8n$.
Since $v_p(d)=1$, $p$ does not divide the conductor of $\mathcal O_d$.
At $p$, write $\pi=\sqrt d$, so

$$
(\mathcal O_d)_p=\mathbb Z_p[\pi],\quad v(\pi)=1/2,\qquad
 \mathcal O_p=\mathbb Z_p+p\mathbb Z_p\pi,
 \qquad \theta=-\frac b{2c}+\frac{p\pi}{2c},\quad J_p=\mathcal O_p.
$$

The unique prime $\mathfrak P$ of $(\mathcal O_d)_p$ has norm $p$ and
$\mathfrak P^2=(p)$. Since $v(e)=4$,
$\mathfrak B(\mathcal O_d)_p=\mathfrak P^8=(p)^4$.
For a principal local ideal its additive index in either order is the
field norm of its generator; that index is $p^8$ here, even in the
conductor-$p$ order. Away from $p$ the orders agree. Consequently
$\mathfrak A=(p)^{-4}\mathfrak B\mathcal O_d$ is integral invertible,
prime to $p$, of norm $n$. Rearranging proves
(6.2). No other conductor prime has been removed.

For unramified $j=3$, Lemmas 5.1 and
5.2 give the same indices and norm, with
fixed ideal factor $(p)^3\mathfrak p^2$ instead of $(p)^4$.
Their algebraic proofs apply to rationally split kernels as well; the
split order and its classes are proved explicitly in
Section 6.9. Thus all three $j=3$ cases have
$D_L=\pm p^8\kappa$, $|\kappa|=hn$ and the same norm formula.

### 6.2 The corrected layer count, including the zero layer

Keep the raw integer functional on the primitive physical lattice

$$
f(r):=\det_L(r_b,r_c,r),
$$

where $r_b$ is the selected maximum baseline and $r_c$ is one actual row
independent of it. If $\delta_f$ is the gcd of its coefficients in a
polynomial-height integer basis of $L$, define the *separate*
primitive functional $f_0=f/\delta_f$ only for the affine-plane lemma.
For actual rows $f(r_e)=p^6g_e$, $g_e\in\mathbb Z$, including $g_e=0$.
The identities involving the raw $f$ are exactly

$$
D_{\rm phys}(r_b,r_c,r_e)=D_L f(r_e)^3=p^{26}k_e,
 \qquad |k_e|\le K.
$$

Thus $|g_e|\le(K/(hn))^{1/3}$ on nonzero layers. The family lies in
$O(1+(K/(hn))^{1/3})$ planes $f=p^6g$, including zero.
Apply Lemma 4.8 to
$f_0=p^6g/\delta_f$: a nonintegral level is empty, and a nonempty level
has integer polynomial height. More explicitly, the integral
coordinate-to-physical row map sends $W_{\rm coord}\cap\mathbb Z^5$ into $L$;
composing $f_0$ with it gives an integer functional on that coordinate
lattice. Divide its coefficients by their gcd once more if necessary,
discarding nonintegral levels. This transports exactly the same affine
plane to the setup of Lemma 4.8. The map and
fixed-rank integer elimination preserve polynomial heights. The expanded
local unit-chart proof of that lemma covers ramification too. Therefore

$$
\tag{6.3}
 W(h,n)\ll_\eta p^\eta\left(1+(K/(hn))^{1/3}\right).
$$

No determinant identity has been renormalized, no baseline was replaced,
and no unit resultant for the actual baseline is assumed.

### 6.3 One height scale for the same actual triple

Define

$$
\tau=\max\{|a|/X^2,|b|/(2A),|c|/Y^2\},\qquad
 \tau_0=C_\tau A/p^6,
$$

with sufficiently large absolute $C_\tau$, and use dyadic segments
$T\le\tau_0/\tau<2T$, $T\ge1$. Explicitly, on a $T$-segment,

$$
\tag{6.4}
 |a|\ll H_1/T,\quad |b|\ll H_2/T,\quad |c|\ll H_3/T,
 \qquad |d|=|b^2-4ac|/p^2\ll D_{\max}/T^2.
$$

Choose an actual $e_0$ with raw $f(r_{e_0})\ne0$ and fix
$(r_b,r_c,r_{e_0})$ for every comparison in this paragraph. Let
$M=\max_{i<j}|\ell_i m_j-\ell_jm_i|$ for this same triple and write
its index as $p^6g_{\rm idx}$. Its three quadratic cofactors are
$p^6g_{\rm idx}h(a,b,c)$. Expanding them gives directly

$$
p^6g_{\rm idx}h|a|\le3X^2M,\quad
 p^6g_{\rm idx}h|b|\le6AM,\quad
 p^6g_{\rm idx}h|c|\le3Y^2M.
$$

Hence $M\gg p^6g_{\rm idx}h\tau$, $M\ll A$, and
$g_{\rm idx}h\ll T$. Choose the pair attaining this $M$ in the
exact Cramer identity

$$
L_i(\theta)Q_j(\theta)-L_j(\theta)Q_i(\theta)=M_{ij}E.
$$

In the two real embeddings (also in the rationally split case),

$$
|E_\sigma|\le6(X+Y|\theta_\sigma|)^3/M,\qquad
 (X+Y|\theta_+|)(X+Y|\theta_-|)\ll A^2\tau/|c|.
$$

The latter follows from the norm, trace and root difference: its numerator
is $X^2|c|+A\max(|b|,\sqrt\Delta)+Y^2|a|$.
For imaginary roots use
$|c|(X+Y|\theta|)^2\le2X^2|c|+2Y^2|a|$.
Combining these bounds with $|N(E)|=p^8n/(h^2|c|^3)$ yields

$$
n\ll\frac{h^2A^6\tau^3}{p^8M^2}
   \ll\frac{A^6\tau}{p^{20}g_{\rm idx}^2}
   \ll\frac{K}{Tg_{\rm idx}^2}.
$$

The last implication uses the fixed scale (6.1) in the
correct direction. Thus nonemptiness implies $T\ll K$ and

$$
\tag{6.5}
 h\ll T,\qquad n\ll K/T.
$$

Let $a_{\mathcal O_d}(n)$ count integral invertible ideals of norm $n$; bounding
it by all ideals is safe. Lemma 5.5
and partial summation give
$\sum_{n\le N}a_{\mathcal O_d}(n)n^{-1/3}\ll_\delta N^{2/3+\delta}$,
uniformly also for split orders. Accordingly

$$
\tag{6.5a}
\begin{aligned}
 \sum_{h\ll T}\sum_{n\ll K/T}a_{\mathcal O_d}(n)W(h,n)
 &\ll_{\eta,\delta}p^\eta\left[T(K/T)^{1+\delta}
   +K^{1/3}T^{2/3}(K/T)^{2/3+\delta}\right]\\
 &\ll_{\eta,\delta}p^\eta K^{1+\delta}.
\end{aligned}
$$

Since $K<p$, this is $O_\rho(p^\rho K)$ for any prescribed
$\rho>0$, by choosing $\eta,\delta>0$ with $\eta+\delta\le\rho$.
This exponent budgeting does not use a strict area saving.

### 6.4 The exact affine ideal coset

Fix the kernel, $h$, and $e=hE\in J^3$. Invertibility gives
$J^3=J^2+\theta J^2$ and $(J^2:J)=J$. Hence solutions of

$$
(hU,hV)\in J^2\oplus J^2,\qquad hV-\theta hU=e
$$

exist, and all of them are exactly

$$
\tag{6.6}
 hU=X_*+x+y\theta,\quad x,y\in\mathbb Z,\qquad hV=\theta hU+e,
$$

where $X_*$ is a fixed *element of $J^2$*, with rational coefficients
in $(1,\theta)$; it is not generally a rational number. For the difference
$z$ of two $hU$ values, $z,\theta z\in J^2$, equivalently
$zJ\subset J^2$, so $z\in J$. Conversely every $z\in J$ is allowed.
No global denominator is cleared.

### 6.5 The actual inverse graph modulo $p^2$

Write $q=p^2$. All coefficients of $U=u_0+u_1\theta$ are $p$-integral,
since $p\nmid h$ and $J_p=\mathcal O_p=\mathbb Z_p[\theta]$.
The following transport keeps the conductor order, not merely its
maximal-order components. In an actual reduced middle basis
$M=\left(\begin{smallmatrix}r&v\\s&z\end{smallmatrix}\right)$ put
$\beta=v/r$, $\rho_0=s/r$, $q_0=1+\rho_0\theta$ and
$\tau=(v+z\theta)/(r+s\theta)$. Saturation gives

$$
U_c(\tau)=(gtr)^{-1}+\gamma_c(\tau-\beta)+p^3A_c,
 \quad A_c,\gamma_c\in\mathbb Z_p.
$$

The exact identities

$$
U+\rho_0E/q_0=rq_0U_c(\tau),\qquad
 \tau-\beta=p^3\theta/(r^2q_0)
$$

therefore give

$$
\tag{6.7}
 U+\rho_0E/q_0-q_0/(gt)
   =p^3(\gamma_c\theta/r+rq_0A_c)\in p^3\mathcal O_p.
$$

For the actual $\rho=t/w$, $\rho-\rho_0\in p^3\mathbb Z_p$. Replacing
$\rho_0$ by $\rho$ changes the left side by

$$
(\rho-\rho_0)\{E/[(1+\rho\theta)q_0]-\theta/(gt)\}.
$$

In the unramified branch the quotient has paired valuations $(1,1)$;
in the ramified branch its valuation is $4-3/2-3/2=1$.
In both cases it belongs to $p(\mathcal O_d)_p\subset\mathcal O_p$.
Thus, with $q_\rho=1+\rho\theta$,

$$
\tag{6.8}
 \Phi:=U+\rho E/q_\rho-q_\rho/(gt)\in p^3\mathcal O_p.
$$

This proves the required conductor-order gluing before any division
could lose a root precision.

For unramified $j=3$, the paired valuations of $q_\rho,E$ are
$(1,2)$ and $(3,5)$. Formula (6.8) gives paired
valuations $(1,2)$ for $U$. Let $\theta_{\rm hi}$ denote the component
selected by $v(w+t\theta_{\rm hi})=2$, and set
$\lambda_0=-\theta_{\rm hi}\pmod q$. Then

$$
w\equiv\lambda_0t,\qquad u_0\equiv\lambda_0u_1\pmod q.
$$

For ramification write in the *single* field

$$
\theta=\theta_0+\frac{p\pi}{2c},\quad
 \theta_0=-b/(2c),\quad \pi=\sqrt d,\quad v(\pi)=1/2,\qquad
 \mathcal O_p=\mathbb Z_p+p\mathbb Z_p\pi.
$$

Equation (3.6) gives
$w\equiv\lambda_0t\pmod q$, $\lambda_0=b/(2c)=-\theta_0$, a unit.
Here $v(q_\rho)=3/2$, $v(E/q_\rho)=5/2$, so
(6.8) gives $v(U)=3/2$. In

$$
U=(u_0+\theta_0u_1)+\frac{pu_1}{2c}\pi
$$

the first summand has integer valuation and the second has half-integer
valuation. Their minimum is $3/2$ only if $u_1$ is a unit and
$u_0+\theta_0u_1\in p^2\mathbb Z_p$. Thus again
$u_0\equiv\lambda_0u_1\pmod q$.

To recover the inverse parameter, use the local middle basis
$\left(\begin{smallmatrix}w&0\\t&p^3/w\end{smallmatrix}\right)$,
write $s_m=w+t\theta$, $\vartheta=p^3\theta/(ws_m)$, and let
$U_c=\xi+\gamma\vartheta$. Saturation gives
$\xi\equiv(gwt)^{-1}\pmod{p^3}$ and the exact transport identity is

$$
U+tE/s_m=s_m\xi+(p^3\gamma/w)\theta.
$$

Taking the constant coefficient in $(1,\theta)$, with
$f_E(r)=r\operatorname{ct}_\theta(E/(1+r\theta))$, yields

$$
\tag{6.9}
 u_0+f_E(t/w)\equiv(gt)^{-1}\pmod{p^3}.
$$

For two slopes on a fixed actual branch, $r-r'\in p^2\mathbb Z_p$ and exactly

$$
f_E(r)-f_E(r')=(r-r')\operatorname{ct}_\theta
                   \frac{E}{(1+r\theta)(1+r'\theta)}.
$$

In the unramified branch the quotient has component valuations $(1,1)$;
expressing its constant coefficient loses at most the root-gap valuation
one, so that coefficient is integral. In the ramified field its
valuation is one, so write the quotient as $Z=p(A+B\pi)$,
$A,B\in\mathbb Z_p$. Its constant coefficient is

$$
\operatorname{ct}_\theta Z=pA-2cB\theta_0\in\mathbb Z_p.
$$

It need not be divisible by $p$. This proves $f_E(r)\equiv f_0\pmod q$
on the support of each branch in both cases, with $f_0$ chosen from
one actual middle. An empty support contributes nothing.
All coefficients of $X_*$ are locally integral, since $X_*\in J^2$.
Combining (6.6) and (6.9) gives

$$
\tag{6.10}
 (w,t,x,y)=\left(\lambda_0t,t,\frac hg t^{-1}+b_0,
                  \frac{h}{g\lambda_0}t^{-1}+b_1\right)\pmod q,
$$

with fixed phases and unit slopes. The second word equation is encoded
in the same actual construction, not an independent density factor.

### 6.6 Finite unit-safe shears and projection boxes

Choose $m'$ from $\{\lceil Y/X\rceil,\lceil Y/X\rceil+1\}$ prime
to $p$, and take the five nodes $z=jm'$, $0\le j\le4$.
For $p>4$ they are distinct modulo $p$ and $zX\ll Y$.
Under $(x,u)\mapsto(x,u+zx)$ the primitive kernel becomes

$$
(a',b',c')=(a,b+2za,c+zb+z^2a).
$$

At most two nodes have $p\mid c'$. Interpolation at any three good
indices in $\{0,\ldots,4\}$ gives

$$
\max(|c|,|m'b|,|(m')^2a|)\le36\max_{\rm good}|c+zb+z^2a|.
$$

The left side is at least a fixed multiple of $Y^2\tau$.
Consequently a chart, chosen from the kernel alone, has

$$
|c'|\asymp Y^2\tau,\quad p\nmid c',\quad
 |a'|\ll X^2\tau,\quad |b'|\ll A\tau.
$$

Put $d_z=1-z\theta$ and $\theta'=\theta/d_z$. Exact transport is

$$
J'=J/d_z,\quad E'=E/d_z^3,\quad
 U'=U/d_z-zE/d_z^2,\quad V'=V/d_z^2.
$$

With $e=hE$ define

$$
X_*'=X_*/d_z-ze/d_z^2.
$$

Then, exactly,

$$
\tag{6.11}
 hU'=X_*'+x'+y'\theta',\qquad (x',y')=(x,y+zx)\in\mathbb Z^2.
$$

This is an integral unimodular change of free parameters.
Since $N(d_z)=c'/c$ is a $p$-unit, $d_z$ is a unit in each local
component or in the ramified local field. In particular
$1+z\lambda_0$ is a unit. The correction $E/d_z^2$ has coefficients
in $p^2$ in the $(1,\theta')$ basis in the unramified case (its
component valuations are at least $3,5$, with root gap one).
In the ramified field it has valuation four; write
$\theta'=\theta'_0+p\pi/(2c')$ with a possible unit sign on $\pi$.
Integer versus half-integer valuations show that its scalar and
$\pi$ coefficients have valuations at least four, hence its
$(1,\theta')$ coefficients are in $p^3\mathbb Z_p$.
Thus $u_0'\equiv u_0$, $u_1'\equiv u_1+zu_0\pmod q$ in either case.
The projection coset and inverse slope become

$$
x'-\lambda'y'=\text{constant}\pmod q,\qquad
 \lambda'=\frac{\lambda_0}{1+z\lambda_0},\qquad
 y'=\frac{h(1+z\lambda_0)}{g\lambda_0}t^{-1}+\text{constant}\pmod q.
$$

Both Fourier slopes are units. The original middle intervals remain
in their old coordinates. The auxiliary physical shear need not
preserve the original word equation: the displayed identities transport
the actual graph. The indices $h,g_{\rm idx}$ and the ideal norm $n$
are unchanged; indeed $e'(J')^{-3}=eJ^{-3}$.

For completeness, the projection boxes follow from coefficient Cramer
bounds using the *same* actual triple and its unchanged $M$.
Its sheared rows have bounds $O(X^2),O(A),O(Y^2),O(X),O(Y)$.
In the $c'$ chart reduce
$\theta'^2=-a'/c'-(b'/c')\theta'$. Cramer elimination for $U'$ gives

$$
\begin{aligned}
 |hu_0'|&\ll\frac{hY(X^2+Y^2|a'/c'|)}M
          \ll\frac{hXA}M\ll TX/g_{\rm idx},\\
 |hu_1'|&\ll\frac{hY(A+Y^2|b'/c'|)}M
          \ll\frac{hYA}M\ll TY/g_{\rm idx}.
\end{aligned}
$$

Here $|a'/c'|\ll X^2/Y^2$, $|b'/c'|\ll X/Y$ by the chosen chart.
Subtracting the fixed coefficients of $X_*'$ shifts only the interval
centers. Hence the actual integers $x',y'$ lie in intervals of lengths
$O(TX),O(TY)$. There is no real root-gap divisor or omitted denominator.

### 6.7 Shortest root lattices, split directions, and support

Let $F(r,s)=cr^2-brs+as^2$ and
$\Gamma=\{(r,s)\in\mathbb Z^2:r\equiv\lambda_0s\pmod q\}$.
In the unramified case one norm factor is divisible by $p^2$ and the
other by $p$, so $F(\Gamma)\subset p^3\mathbb Z$. In the ramified case the
same assertion follows directly from (3.6).
If $F(v)\ne0$, then

$$
p^3\le|F(v)|\ll A^2\tau\|v\|_*^2,\qquad
 \|v\|_*:=\max(|r|/X,|s|/Y).
$$

Since $p\tau\ll_{C_0}p^{-5/4}/T$ is bounded,
$\|v\|_*\gg p^2/A$. For a rationally split $F$ a nonzero null
vector may occur; retain an actual middle $m=(w,t)$ in this branch.
Lemma 3.3 gives $v_pF(m)=3$, so $F(m)\ne0$.
A null vector $v$ is independent of $m$, and
$0\ne\det(v,m)\in q\mathbb Z$, whereas
$|\det(v,m)|\le2A\|v\|_*$. This proves the same lower bound.
The ramified field has no rational null line, since $v_p(d)=1$.
Keep the original middle difference lattice $\Gamma_0=\Gamma$.
Under the finite shear $S_z(W,T)=(W,T+zW)$, the projection difference
lattice is

$$
\Gamma_z=S_z\Gamma_0
 =\{(r,s)\in\mathbb Z^2:r\equiv\lambda' s\pmod q\},
 \qquad \det\Gamma_z=q,\qquad F'(S_zv)=F(v).
$$

The same actual witness becomes $m_z=(w,t+zw)$, with
$F'(m_z)=F'(w,t+zw)=F(w,t)\ne0$, $|(m_z)_1|\le X$ and $|(m_z)_2|\ll Y$.
It need not lie in a box short modulo $q$. If $v\in\Gamma_z$ is a
nonzero null vector for $F'$, then $0\ne\det(v,m_z)\in q\mathbb Z$
and $|\det(v,m_z)|\ll A\|v\|_*$, proving the same shortest-vector
bound. For nonnull vectors the coefficient heights and
$F'(\Gamma_z)\subset p^3\mathbb Z$ give that bound. The transformed
projection coset in (6.11) is an affine translate of $\Gamma_z$.
Divisibility of $F'$ is asserted on the linear difference lattice,
not on that affine translate.

For a rank-two lattice of determinant $q$ with this shortest-vector bound,
normalize by $(r,s)\mapsto(r/X,s/Y)$, so its covolume is $D=q/A$ and
shortest Euclidean length $\lambda\gg D$. A translated box of widths
$RX,RY$ lies after normalization in a disk of radius $O(R)$. If it
contains at most one point the bound is immediate; otherwise
$\lambda\ll R$. Parallel lattice lines have spacing $D/\lambda$ and
points on a line have spacing $\lambda$, so the count is at most

$$
(1+O(R\lambda/D))(1+O(R/\lambda))
 \ll1+R/\lambda+R^2/D.
$$

Using $\lambda\gg D$ gives, for every translate and $R\ge1$,

$$
\#\ll1+RA/q+R^2A/q\ll R^2A/q,
$$

since $A\ge p^3$. Take $R=1$ with $\Gamma_0$ for the original middle
box, and $R=T$ with the difference lattice $\Gamma_z$ for the affine
projection coset. This proves

$$
\tag{6.12}
 N_{\rm mid}\ll A/p^2,\qquad N_{\rm proj}\ll T^2A/p^2.
$$

These are integer support counts; the projection count does not count lifts.

### 6.8 The four-interval inverse-graph lemma

Let $I_1,\ldots,I_4$ be cyclic intervals modulo $q=p^2$; an interval of
length at least $q$ means the whole residue circle. For units $a,c,C$ put

$$
F_1(t)=1_{I_1}(t)1_{I_2}(at+b),\qquad
 G_1(s)=1_{I_3}(s)1_{I_4}(cs+d),
 \quad N_F=\sum F_1,\quad N_G=\sum G_1.
$$

Then, for every $\eta>0$,

$$
\tag{6.13}
 \sum_{t\bmod q}^{*}F_1(t)G_1(Ct^{-1})
 \ll N_FN_G/q+p^{3/2+\eta}.
$$

Indeed, with $\widehat F(A)=\sum_xF(x)e_q(-Ax)$,
$q^{-1}\|\widehat{1_I}\|_1\ll\log(2q)$, by the geometric-series
bound and a harmonic sum. Affine unit substitutions preserve this norm;
product is normalized convolution, so each of $F_1,G_1$ has normalized
Fourier $L^1$ norm $O(\log^2(2q))$. Fourier expansion reduces the sum to
$q^{-2}\sum_{A,B}\widehat F_1(A)\widehat G_1(B)S(A,BC;p^2)$, where

$$
S(A,B;c)=\sum_{t\bmod c}^{*}e_c(At+Bt^{-1}).
$$

The external input is the gcd-aware complete Kloosterman bound, for every
integer $A,B$ and positive integer $c$,

$$
|S(A,B;c)|\ll_\delta c^\delta\sqrt{c\gcd(A,B,c)}\quad(\delta>0),
$$

as stated in Pascadi [Pascadi, Lemma 3.3, Section 3.2](#reference-pascadi2026), using
his \[27, Corollary 11.12\] and the divisor bound. The $(A,B)=(0,0)$
term is $\varphi(q)N_FN_G/q^2\le N_FN_G/q$. For every other residue
frequency pair, $v_p\gcd(A,BC,p^2)\le1$; the bound is
$O_\delta(p^{3/2+2\delta})$, including frequencies both divisible by $p$.
Budgeting $\delta$ and the four logarithms proves (6.13).

Apply the lemma with $F_1$ supported on the original middle intervals:
its variable is the original $t$, and its second slope is $\lambda_0$.
These intervals have lengths less than $q$ by $3Y<p^2$, so each residue
has at most one integer representative in each interval. Thus $N_F$
is the integer $\Gamma_0$ support count and $N_F\ll A/p^2$.
The sheared projection graph has unit multipliers $h/g$ and
$h(1+z\lambda_0)/(g\lambda_0)$; its two-interval function $G_1$ uses
the unit slope $\lambda'^{-1}$, which need not equal the middle slope.

Projection intervals may be longer than $q$. Their residue images are
existence indicators, equal to the whole circle if an interval has at
least $q$ integers. For each residue parameter counted by $G_1$, choose
one integer lift of each projection coordinate inside its actual interval.
Every such pair lies in the same affine $\Gamma_z$ coset, since lifting
changes neither modular coordinate. Distinct parameters have distinct
first-coordinate residues and hence distinct chosen integer pairs.
This injects the residue support into the actual integer projection-coset
support. Therefore $N_G\le\min(q,N_{\rm proj})$, without a projection
lift factor. No shortness of the sheared witness or projection box is
required.
By (6.10) and its exact shear transport, followed by
(6.12), for fixed $(\text{kernel},e,h)$,

$$
\tag{6.14}
 M_T(\text{kernel},e,h)\ll_\eta p^\eta
             (T^2A^2/p^6+p^{3/2}).
$$

Only support is counted here. Each original middle has exactly one
selected $W$; its actual ordered endpoint multiplicity is paid by
$W(h,n)$ in (6.3). There is no sum over $U$ lifts.

### 6.9 Generator pairs, unit classes, and quadratic orders

Fix an order discriminant $d$ and a small integral invertible ideal
$\mathfrak A$ of norm $n$; then sum over the allowed cube-root ideal
classes. In the unramified case fix also one of the two $p$-primes and
write $\mathfrak Q=(p)^3\mathfrak p^2$. In the ramified case put
$\mathfrak Q=(p)^4$ and use (6.2). In either
case $N\mathfrak Q=p^8$, and an allowed class satisfies
$[\mathfrak a]^3=[\mathfrak Q\mathfrak A]^{-1}$.
For a fractional representative $\mathfrak a$ of norm $\nu$, choose
$(\eta_0)=\mathfrak Q\mathfrak A\mathfrak a^3$, so
$|N\eta_0|=p^8n\nu^3$. Write $J_0=\chi\mathfrak a$.
Locally at $p$, $J_p=\mathcal O_p$, $J_{0,p}=(\mathcal O_d)_p$, and their index is
$p$ in both strata. Away from $p$ the orders agree. Consequently

$$
\Lambda=\chi^{-1}J\subset\mathfrak a,\qquad
 [\mathfrak a:\Lambda]=p.
$$

There are exactly $p+1$ index-$p$ additive subgroups of $\mathfrak a$;
allowing all of them is a valid upper bound. No other conductor prime
is removed.

The equality of principal ideals gives $e=hE=\chi^3\eta_0\epsilon$.
Modulo cube units there are three choices in a real quadratic order,
and at most three in an imaginary quadratic order. Absorb cube units
into $\chi$; they merely permute the same $p+1$ subgroups. With a fixed
representative $\eta=\eta_0\epsilon_r$, the ordered basis

$$
v_1=\chi^{-1},\qquad v_2=\chi^{-1}\theta
$$

determines *both* $\theta=v_2/v_1$ and $e=\eta/v_1^3$.
Thus the following counts pairs, not just kernels admitting a generator.
The height proof of Proposition 5.4 uses only
$h\le K$, not a fixed $h$. With $H=O(H_3/T)$ it gives
$T_+T_-\ll\nu H$, covolume $p\nu\sqrt d$, and lower embedding bounds
from $|\eta_\sigma|\le6KY^3T_\sigma^3/p^3$.
The product of those lower bounds is
$\frac{p^{14/3}n^{1/3}\nu}{(6K)^{2/3}Y^2}$; the aspect-ratio window has
polynomial width, hence $O(\log p)$ dyadic intervals. The Euclidean
basis lemma gives $O(H/(p\sqrt d))$ bases per subgroup and interval.
The $p+1$ subgroups cancel that $p$.
For imaginary $d$, the complex embedded lattice has covolume
$p\nu\sqrt{|d|}/2$, and
$|v_1|^2+|v_2|^2=\nu(c+|a|)\ll\nu H$; the same basis lemma and
finite cube-unit choices give the same estimate without an aspect ratio.
For each fixed $\mathfrak A$ this proves, uniformly over all actual
$h\le K$,

$$
\tag{6.15}
 \#\{(\text{kernel},e)\}\ll_\eta p^\eta
       \frac{H_3}{T\sqrt{|d|}}\,|\operatorname{Pic}(\mathcal O_d)[3]|.
$$

Applying this union bound separately in the later $h$ sum is safe
overcounting; there is no missing $h$, generator, or unit factor.
Ramification has introduced no $p$ loss: its fixed norm is still $p^8$.

For rationally split $d=f^2$, use
$\mathbb Q\times\mathbb Q$ and $\mathcal O_{f^2}=\{(r,s)\in\mathbb Z^2:r\equiv s\pmod f\}$.
The primitive ideal $I=(c,(-b+\sqrt\Delta)/2)$ satisfies
$I\overline I=c\mathcal O$ because, after division by $c$, the product ideal
contains $a,b,c$ and thus $1$. It is invertible and proper. The actual
nonzero norm of $E$ ensures both components of $E,\eta,\chi,v_1$ used
in divisions are nonzero. Here $p\nmid f$, so the local algebra at $p$
is unramified split and the fixed factor is $(p)^3\mathfrak p^2$.
The same index-$p$ extension and Euclidean basis argument apply to its
two real components. Its units are a subgroup of $\{\pm1\}^2$ and
all are cubes. To bound classes explicitly, extension to $\mathbb Z\times\mathbb Z$
makes each component ideal principal. After choosing their generators,
an invertible ideal is specified by gluing their reductions modulo $f$
by a unit in $(\mathbb Z/f\mathbb Z)^*$, up to changing those generators by signs.
Hence $|\operatorname{Pic}(\mathcal O_{f^2})|\le\varphi(f)\le f$, and

$$
\tag{6.16}
 \sum_{f\le\sqrt D}\frac{|\operatorname{Pic}(\mathcal O_{f^2})[3]|}{f}\ll\sqrt D.
$$

The small-ideal HNF proof also applies to this split order verbatim.
For nonsplit orders, the precise all-order mean theorem of
Bhargava–Varma [Bhargava–Varma, Theorem 2(a),(b)](#reference-bhargavavarma2016), stated in
(5.35), gives

$$
\tag{6.17}
 \sum_{0<\pm d\le D}\frac{|\operatorname{Pic}(\mathcal O_d)[3]|}{\sqrt{|d|}}\ll\sqrt D.
$$

Drop the restrictions of splitting at $p$ or $v_p(d)=1$ before this
average. It includes all remaining nonmaximal orders, so no estimate
uniform in a varying local specification is asserted or needed.

### 6.10 Joint summation and the endpoint

At each middle one $W$ is selected, so projection support requires only
existence of its lift. Its endpoint weight is (6.3).
For fixed $d,\mathfrak A$, use (6.15); then sum
that weight over $h\ll T$, $n\ll K/T$ by
(6.5a). Finally sum over discriminants using
(6.4), (6.16) and
(6.17). The weighted data count is

$$
\tag{6.18}
 \mathcal D_T\ll_\rho p^\rho
                 \frac{H_3\sqrt{D_{\max}}K}{T^2}.
$$

One factor $T^{-1}$ is the coefficient height, and the other is the
square root of the discriminant cutoff $D_{\max}/T^2$.
Multiplying by (6.14) and summing over dyadic
$1\le T\ll K$ gives a logarithm for the principal terms and the bounded
sum $\sum_TT^{-2}$ for the errors. After assigning arbitrarily small
subpower exponents to each input and the logarithm, for every $\eta>0$,

$$
\mathcal W_{j=3}\ll_\eta p^\eta H_3\sqrt{D_{\max}}K
                            (A^2/p^6+p^{3/2}).
$$

Since $H_3\sqrt{D_{\max}}\ll Y^2A^3/p^{13}$ and
$K=C_DA^7/p^{26}$, this proves for all three $j=3$ strata

$$
\tag{6.19}
 \mathcal W_{j=3}\ll_\eta Y^2p^\eta
                \left(\frac{A^{12}}{p^{45}}+
                      \frac{A^{10}}{p^{75/2}}\right).
$$

At $A\le C_0p^{15/4}$ the two factors are at most $C_0^{12}$ and
$C_0^{10}$. Logarithms and $K^\delta$ have been absorbed by splitting
the prescribed final exponent, not by appealing to negative area powers.
For strict $\alpha<15/4$ the corresponding exponents are
$12\alpha-45$ and $10\alpha-75/2$.

### 6.11 Assembly of the arithmetic branches

The $j=4$ contribution is (2.17), with threshold $233/61$
and endpoint relative-$A$ exponent $-17/36$; it was not treated by the
$j=3$ norm identity. Rank four has threshold $49/13$, zero residual
has threshold $23/6$, and the source moment allows $\alpha\le15/4$.
Together with (6.19) these bounds give the required
actual bad-degree average at the endpoint.

## 7. Completion of the original count

*Proof of Theorem 1.1.*

Write the original widths as $X_0,Y_0$. Apply
(2.2) for every scalar center and set
$X=2X_0$, $Y=2Y_0$, $A=XY$. Then

$$
3Y<p^2,\qquad p^3\le A\le C_1p^{15/4},\qquad C_1=4C_0.
$$

The unit-middle cover (2.4) retains all remaining
integer tuples. The five chart estimates need only the width inequalities
listed in Section 2.2; in particular
$A\le Y^2<p^4/9$. They are uniform in the fixed original units.

We spell out why every strict arithmetic cutoff used in the proof
survives for arbitrary fixed $C_1$. In a source bin
$B=IJ=32A/p^3\ll_{C_1}p^{3/4}$ and $J\le\sqrt B$. Hence

$$
\frac Bp=O_{C_1}(p^{-1/4}),\quad
 \frac{C_DB^7}{p^6}=O_{C_1}(p^{-3/4}),\quad
 \frac{C_*B^6}{p^5}=O_{C_1}(p^{-1/2}),\quad
 \frac{B^6J}{p^5}=O_{C_1}(p^{-1/8}).
$$

Also $B^4/p^4=O_{C_1}(p^{-1})$,
$I\ll_{C_1}p^{3/4}$, and $I^3/p^3=O_{C_1}(p^{-3/4})$.
These imply (2.10), (2.16),
the sixth-height zero-$D$ gap, saturation, and $K<p$ after raising a
single $C_1$-dependent prime threshold. We have not used the false
endpoint inference $B^4=o(p^3)$: Lemma 3.2
retains valuation three and excludes valuation at least four, including
zero, by the exact residual. The ramified proofs in
Sections 3, 4.2, and
6 apply to that actual stratum.

At each occupied middle choose exactly one actual maximum baseline.
Keep it in the whole selected row span. The source chart estimates and
the paper lemmas handle modular-zero pencils, zero residual, and rank
four. Lower rank is included in the zero-residual cover. The $j=4$
nonzero-residual branch contributes (2.17); at this area
its bound is $O_{\eta,C_1}(Ap^{-17/36+\eta})$. The remaining $j=3$
branches, including split null directions and ramification, contribute
(6.19), which is
$O_{\eta,C_1}(Y^2p^\eta)$ since its two area factors are at most
$C_1^{12}$ and $C_1^{10}$. The old unramified ideal-only estimate in
Section 5 is auxiliary and is not substituted for this
joint bound. The maximum was paid once and no $U$-lift multiplicity was
silently removed.

Choose the subpower parameters in the divisor, class, layer, Fourier,
and dyadic bounds smaller than the prescribed $\varepsilon$, as in
(6.5a); all logarithms fit within the remaining exponent.
The actual dyadic bins number $O(\log p)$, since the source has
$1\le\sqrt{Q_{X,Y}(R)}\le2p^2$. Summing them gives
(2.9) for every positive input exponent.
Corollary 2.3 now applies at
$\alpha=15/4$: it uses $A^4/p^{15}\le C_1^4$, not a strictly negative
power. Thus the minus count is $O_{\varepsilon,C_1}(Y^2p^\varepsilon)$.

There are at most four centers; their factor $64$ and the doubled
$Y^2=4Y_0^2$ change only the constant. For $p$ below the chosen threshold
$P$, the literal count is at most $729Y_0^6\le729P^8Y_0^2p^\varepsilon$,
using $6Y_0<p^2$. This includes $p=2$ and is uniform in the units.
The endpoint assertion follows for every fixed $C_0\ge1$.

## Mathematical references

<a id="reference-pascadi2026"></a>

[Pascadi] Alexandru Pascadi, *Non-abelian amplification and bilinear forms with Kloosterman sums*, Geometric and Functional Analysis **36** (2026), 1174–1243, [DOI:10.1007/s00039-026-00746-0](https://doi.org/10.1007/s00039-026-00746-0), [arXiv:2511.08445v2](https://arxiv.org/abs/2511.08445v2), Section 6; complete Kloosterman bound: Lemma 3.3, Section 3.2.

<a id="reference-bhargavavarma2016"></a>

[Bhargava–Varma] Manjul Bhargava and Ila Varma, *The mean number of 3-torsion elements in the class groups and ideal groups of quadratic orders*, Proceedings of the London Mathematical Society **112** (2016), 235–266, [DOI:10.1112/plms/pdv062](https://doi.org/10.1112/plms/pdv062), [arXiv:1401.5875](https://arxiv.org/abs/1401.5875), Theorems 1–2 and Lemma 13. The all-order means used here are Theorem 2(a),(b).

<a id="reference-formalsource"></a>

[R] The Omega Institute, *Original prime-cube return-count reductions*, [trureturing](https://github.com/the-omega-institute/trureturing). Section 2 uses its real-box scalar comparison, six-chart estimates, retained moments, root-localized factors, singular-partner and physical-weight estimates, with their explicit hypotheses as stated there. The [owning source note](../../../Library/CharacterSums/pascadi2025nonabelianamplification.md#exact-locators-for-the-mathematical-inputs) identifies these mathematical inputs precisely.

## 追加锚（本行以下为增补区）
