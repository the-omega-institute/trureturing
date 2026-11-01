# ACMS squared-reciprocal tail boundary

## 1. Recurrence and the two source conditionals

**Definition 1.1 (Sequence and positive indices).** Write
$\mathbb P=\{1,2,3,\ldots\}$. For integers $s,t$ and integers $j\geq0$, define

$$
U(s,t,0)=0,\qquad U(s,t,1)=1,\qquad
U(s,t,j+2)=sU(s,t,j+1)+tU(s,t,j).
$$

Set $U_j^{(s)}=U(s,-1,j)$. The function $U(s,t,j)$ is denoted by
$\{j\}_{s,t}$ in Amdeberhan, Chen, Moll and Sagan,
[*Generalized Fibonacci polynomials and Fibonomial coefficients*,
arXiv:1306.6511v1](https://arxiv.org/abs/1306.6511v1) and
[v2](https://arxiv.org/abs/1306.6511v2), Section 1. Both versions explicitly
state that $\mathbb P$ denotes the positive integers and that
$U(2,-1,j)=j$. That identity is also recorded in the repository's
[reciprocal-tail problem](https://github.com/the-omega-institute/trureturing/blob/631777b65a1c926a81d21d681b8f8ac47c985b07/Problems/amdeberhan-chen-moll-sagan-2014-reciprocal-tail-floor-conjecture-4-6.md).

**Definition 1.2 (Printed conditionals and their interpretation).** In
Section 4, immediately before Conjecture 4.6, both arXiv versions say:
“The restriction $(s,t)\neq(2,-1)$ in the following conjecture is to ensure
that the series converges.” The conjecture then has the following two
conditional sentences, written here with $U$ in place of the source braces.

“If $s>t\geq1$ with $(s,-t)\neq(2,-1)$ and $n,r\in\mathbb P$ then”

$$
\left\lfloor
\left(\sum_{k=n}^{\infty}\frac{1}{U(s,-t,rk)}\right)^{-1}
\right\rfloor
=U(s,-t,rn)-U(s,-t,r(n-1))-1.
$$

“If $t=-1$ and $s,n,r\in\mathbb P$ then”

$$
\left\lfloor
\left(\sum_{k=n}^{\infty}\frac{1}{U(s,-1,rk)^2}\right)^{-1}
\right\rfloor
=U(s,-1,rn)^2-U(s,-1,r(n-1))^2-1.
$$

The positive $t$ in the first sentence appears as the negative coefficient
$-t$; the second sentence instead fixes the recurrence coefficient itself
to $-1$. The separately quantified reading of the second sentence retains
all $s,n,r\in\mathbb P$. A reading that additionally imposes
$(s,-1)\neq(2,-1)$ on that sentence imposes $s\neq2$ and gives a different
assertion. The counterexample below concerns the separately quantified
reading. This distinction makes no inference about authorial intent.

The first displayed identity, with its stated hypotheses and convergence,
is supplied by the repository's
[ACMSReciprocalTailFloor.result](https://github.com/the-omega-institute/trureturing/blob/631777b65a1c926a81d21d681b8f8ac47c985b07/D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.lean).
The same problem reference in Definition 1.1 already identifies the excluded
sequence $U(2,-1,j)=j$ and the harmonic divergence of its unsquared
reciprocal tails. These are inherited inputs; the squared-tail endpoint
comparison is the subject of Section 2.

**Definition 1.3 (Domain and endpoint).** Let $D$ be the set of triples
$(s,n,r)\in\mathbb P^3$ such that $U_{rk}^{(s)}>0$ for every integer
$k\geq n$ and the real series

$$
S(s,n,r)=\sum_{k=n}^{\infty}\frac{1}{(U_{rk}^{(s)})^2}
$$

converges to a positive real number. For triples in $D$, write

$$
E(s,n,r)=(U_{rn}^{(s)})^2-(U_{r(n-1)}^{(s)})^2-1.
$$

The set $D$ makes the positivity and convergence of the witness explicit;
it does not replace the printed quantifiers in Definition 1.2. A failure
inside $D$ already contradicts the separately quantified second conditional,
even if positivity and convergence are added as hypotheses.

## 2. A convergent squared-tail endpoint mismatch

**Theorem 2.1 (Exact witness).** The positive-integer triple
$(s,n,r)=(2,2,1)$ belongs to $D$ and satisfies

$$
\left\lfloor S(2,2,1)^{-1}\right\rfloor=1,
\qquad E(2,2,1)=2.
$$

Consequently it is a counterexample to the separately quantified second
conditional of Definition 1.2.

*Proof.* Use the inherited identity $U(2,-1,j)=j$ from Definition 1.1.
Its recurrence verification is immediate: the initial values are $0,1$,
and $2(j+1)-j=j+2$, so induction gives the identity at every nonnegative
integer index. Thus all the witness denominators are positive and

$$
S(2,2,1)=\sum_{k=2}^{\infty}\frac{1}{k^2}.
$$

The following are the classical telescoping comparisons for a reciprocal
square series, used here as intermediate estimates. For every integer
$k\geq3$, positivity of the denominators gives

$$
\frac{1}{k(k+1)}\leq\frac{1}{k^2}\leq\frac{1}{k(k-1)},
\qquad
\frac{1}{k(k+1)}=\frac1k-\frac{1}{k+1},
\qquad
\frac{1}{k(k-1)}=\frac{1}{k-1}-\frac1k.
$$

For an integer $m\geq2$, put $T_m=\sum_{k=2}^{m}k^{-2}$. Summing the
comparisons from $k=3$ to $m$, with empty sums interpreted as zero, yields

$$
\begin{aligned}
\frac{7}{12}-\frac{1}{m+1}
&=\frac14+\sum_{k=3}^{m}\left(\frac1k-\frac{1}{k+1}\right)
\leq T_m\\
&\leq\frac14+\sum_{k=3}^{m}\left(\frac{1}{k-1}-\frac1k\right)
=\frac34-\frac1m.
\end{aligned}
$$

The partial sums $T_m$ increase, since every summand is positive, and are
bounded above by $3/4$. Completeness of the real numbers therefore gives
their finite limit $S=S(2,2,1)$. Taking limits in the displayed inequalities
gives

$$
0<\frac{7}{12}\leq S\leq\frac34,
\qquad
1<\frac43\leq S^{-1}\leq\frac{12}{7}<2.
$$

Inversion reverses order because all quantities being inverted are
positive. The last interval proves $\lfloor S^{-1}\rfloor=1$, as well as
membership of $(2,2,1)$ in $D$. On the other hand,

$$
E(2,2,1)=U(2,-1,2)^2-U(2,-1,1)^2-1
=2^2-1^2-1=2.
$$

The witness satisfies the printed second antecedent $t=-1$ and
$s,n,r\in\mathbb P$, yet its floor and endpoint differ. This proves the
claimed counterexample. $\square$

**Proposition 2.2 (Necessary restriction for a repair only in $s$).** Let
$A\subseteq\mathbb P$. Suppose the same endpoint formula

$$
\left\lfloor S(s,n,r)^{-1}\right\rfloor=E(s,n,r)
$$

holds for every $s\in A$ and every $n,r\in\mathbb P$ for which
$(s,n,r)\in D$. Then $2\notin A$. In particular, any valid repair that
changes only the admissible values of $s$, retains every positive $n,r$,
and retains the same endpoint must omit $s=2$.

*Proof.* If $2\in A$, take $n=2$ and $r=1$. Theorem 2.1 places this triple
in $D$ and gives $1=2$ from the assumed formula, a contradiction. The
conclusion concerns a universal family with all positive $n,r$; it asserts
neither failure at every triple with $s=2$ nor necessity of removing every
$s=2$ triple from a repair allowed to change the index domain or endpoint.
The alternative interpretation in Definition 1.2 already excludes this
witness, so Theorem 2.1 does not refute that alternative. $\square$

The comparison with Soohyun Park,
[*Arithmetic properties of generalized Fibonacci sequences*,
arXiv:1407.8086v1](https://arxiv.org/abs/1407.8086v1), Section 3,
Theorem 18, uses exactly the same recurrence: $f_j(s,t)=U(s,t,j)$.
Its first part assumes integer $s>t\geq1$ with $(s,-t)\neq(2,-1)$,
$n,r\in\mathbb Z^+$, and sufficiently large $s,t$. Its second part says:
“Let $t=-1$ and $s,n,r\in\mathbb Z^+$. If $s$ is sufficiently large,”
followed by the squared formula in Definition 1.2. That sufficiently-large
qualification supplies no assertion at $s=2$. Theorem 2.1 is compatible
with that qualification and establishes no threshold such as $s\geq3$.
The source-specific inference here is the convergent squared-tail endpoint
mismatch in Theorem 2.1, rather than the inherited sequence identity, the
unsquared formula, harmonic divergence, or the classical comparisons
inside its proof.

## 追加锚（本行以下为增补区）
