# Graham–O'Bryant inverse-sine rows and a signed dyadic counterfamily

## 1. Modular inverses and complete rows

Let $n,q$ be positive integers and let $p_0,\ldots,p_{n-1}$ be positive
integers coprime to $q$. Choose any integer $b_i$ satisfying
$p_i b_i\equiv1\pmod q$, and define the complete row

$$
R_k(q,p)=\sum_{i=0}^{n-1}
\frac{1}{|\sin(\pi p_k b_i/q)|}.
$$

The diagonal $i=k$ is included. Replacing $b_i$ by $b_i+dq$ changes
the angle by the integer multiple $p_kd\pi$ and leaves its absolute sine
unchanged. Thus $b_i$ is a modular inverse, with no real reciprocal
interpretation. Reducing $p_kb_i$ modulo $q$ also leaves the summand unchanged.
When $q>1$, the product is a unit and is not zero modulo $q$, so its
sine denominator is nonzero.

## 2. The literal source assertion

Graham and O'Bryant's Conjecture 5.2 asserts that distinct positive
$p_i$ coprime to $q$, satisfying

$$
q>(7/4)^n,\qquad \sum_{i=0}^{n-1}p_i\le q,\qquad
R_k(q,p)\ge\frac{2}{\sin(\pi/q)}\quad(0\le k<n),
$$

force both $q=2^n-1$ and the ordinary residue-set equality

$$
\{p_i\bmod q:0\le i<n\}
=\{2^i\bmod q:0\le i<n\}.
$$

The source is *A discrete Fourier kernel and Fraenkel's tiling conjecture*,
Acta Arithmetica 118.3 (2005), 283–304, DOI
[10.4064/aa118-3-4](https://doi.org/10.4064/aa118-3-4), printed page 302.
The equality is of ordinary residues; it does not identify residues up to
independent signs.

## 3. The counterfamily and refutation

**定理 3.1（Complete signed dyadic counterfamily）。** For every integer
$n\ge3$, put $q=2^n-1$ and

$$
p_i=
\begin{cases}
2^i,&0\le i\le n-2,\\
2^{n-1}-1,&i=n-1.
\end{cases}
$$

These are $n$ distinct positive units modulo $q$, all strictly below $q$.
Their sum is $q-1$, the strict threshold $q>(7/4)^n$ holds, and every
complete row is exactly $2/\sin(\pi/q)$ with nonzero denominators.
Their ordinary residue set differs from the canonical power-of-two set.
Consequently the assertion in §2 is false.

**Proof.** Write $A=2^{n-1}$, so $q=2A-1$. Since $n\ge3$, $A\ge4$.
The earlier entries increase from $1$ to $A/2$, and $A/2<A-1<q$.
Thus all entries are positive and distinct, and their image has cardinality
$n$. The geometric sum gives

$$
\sum_i p_i=(2^{n-1}-1)+(2^{n-1}-1)=2^n-2=q-1.
$$

Modulo $q$, $2^n=1$ and $A-1=-A$. Hence each entry is a signed power
$p_i=\varepsilon_i2^i$, with only $\varepsilon_{n-1}=-1$.
An explicit inverse is $\varepsilon_i2^{n-i}$, proving the unit and
coprimality assertions even when $q$ is composite.

The strict threshold starts with $(7/4)^3=343/64<7=2^3-1$.
If $(7/4)^m<2^m-1$, multiplication by $7/4$ preserves the strict inequality,
and

$$
\frac74(2^m-1)<2^{m+1}-1,
$$

because the difference is $2^m/4+3/4>0$. Induction proves the threshold
for all $n\ge3$.

Put $x=\pi/q$. For $0\le j<n$, $0<2^j<q$, so
$0<2^jx<\pi$ and $\sin(2^jx)>0$. Also
$2^nx=\pi+x$, whence $\sin(2^nx)=-\sin x$ and
$\cot(2^nx)=\cot x$. These facts ensure all denominators in the
following use of the classical cotangent doubling identity are nonzero.
From $1/\sin(2t)=\cot t-\cot(2t)$, sum along the dyadic orbit:

$$
\sum_{j=0}^{n-1}\frac{1}{\sin(2^{j+1}x)}
=\cot x-\cot(2^nx)=0.
$$

Restoring the first term and removing the last term yields

$$
\sum_{j=0}^{n-1}\frac{1}{\sin(2^jx)}
=\frac{1}{\sin x}-\frac{1}{\sin(2^nx)}
=\frac{2}{\sin x}.
$$

For each pair $k,i$, let $j$ be the least residue of $k-i$ modulo $n$.
The explicit inverse above gives
$p_kb_i\equiv\varepsilon_k\varepsilon_i2^j\pmod q$.
Periodicity and oddness of sine remove the modular representative and the
sign. Thus its absolute sine is $\sin(2^jx)>0$. For fixed $k$, the map
$i\mapsto k-i\pmod n$ permutes all $n$ exponents. The row therefore equals
the displayed dyadic sum, and every row denominator is nonzero. The
diagonal corresponds to $j=0$ and contributes $1/\sin x$.

Finally, $A/2<A-1<A$, so the last entry is not any of the $n$ powers
$1,2,\ldots,A$. All entries of both sets lie strictly between $0$ and
$q$; equality modulo $q$ would therefore be ordinary integer equality.
The residue sets differ. At $n=3$ this gives $q=7$ and $\{1,2,3\}$ in
place of $\{1,2,4\}$, satisfying every hypothesis of §2 and contradicting
its set conclusion. ∎

## 4. Absolute sine, folded doubling, and the remaining boundary

For the cyclic action by multiplication by two, taking absolute sine
identifies the residues $a$ and $-a$. The exponent permutation in the
proof consequently sees the signed dyadic orbit without seeing the
choice of positive lifts. The sum bound does retain information about
those lifts, but replacing $A$ by $q-A=A-1$ decreases the canonical sum
$q$ by one. Thus the budget $\sum_i p_i\le q$ permits this
displayed change of sign.

This connects to the existing folded doubling interpretation of the tent
map $T(t)=1-|2t-1|$ on $[0,1]$. At $t=k/q$, its numerator action is
$k\mapsto2k$ when $2k\le q$, and $k\mapsto2q-2k$ otherwise; modulo $q$
these branches give $2k$ and $-2k$. Iteration therefore follows powers
of two with signs, as in Marcus's cycle-length interpretation of
[OEIS A003558](https://oeis.org/A003558). This common sign loss explains
the connection; a tent orbit, a sine row, and an ordinary residue set are
different observations of that cyclic action.

Requiring $\sum_i p_i=q$ excludes this displayed family. A general
classification under that stronger hypothesis is open here, as are a
modulus-only conclusion and a general classification modulo independent
signs. The family itself still has $q=2^n-1$, so it does not refute that
part of the source conclusion. The main Fraenkel conjecture additionally
requires a Beatty covering, which this construction does not supply.
The adjacent complex-exponential Conjecture 5.1 and the source's proved
covering criteria are separate assertions.

## 5. Sources

The source conjecture and modular-inverse convention are those of Graham
and O'Bryant, DOI 10.4064/aa118-3-4, printed pages 283 and 302;
the [author journal PDF](https://mathweb.ucsd.edu/~ronspubs/05_02_fraenkel_tiling.pdf)
and [original author version](https://arxiv.org/abs/math/0407306v2)
give the same Conjecture 5.2. The elementary sine periodicity, positivity,
cotangent doubling identity, and geometric sum are intermediate tools.
The counterfamily and its application to the literal set conclusion are
the derivation of §3. Marcus's A003558 comment supplies the tent-map
interpretation used for the comparison in §4.

## 追加锚（本行以下为增补区）
