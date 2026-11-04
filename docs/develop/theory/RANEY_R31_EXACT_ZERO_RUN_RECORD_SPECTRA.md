# Exact all-prime zero-run and record spectra of $R_{3,1}$

## 1. Sequence and record convention

**Definition 1.1 (literal Raney sequence).** For every integer $n\ge0$, put

$$
R_{3,1}(n)=\frac{\binom{3n}{n}}{2n+1}
=\frac{(3n)!}{n!(2n+1)!}
=\frac{\binom{3n+1}{n}}{3n+1}.
$$

The last equality follows by cancelling factorials; it identifies this
sequence with the $k=3,r=1$ specialization of
$R_{k,r}(n)=r\binom{kn+r}{n}/(kn+r)$.
For $n\ge1$, the same cancellation gives the integral identity

$$
R_{3,1}(n)=\binom{3n}{n}-2\binom{3n}{n-1}.
$$

For $n=0$ set $\binom{0}{-1}=0$, so both sides are $1$ and the identity
holds there as well. The quotient is an integer before reduction modulo
a prime; no division in a residue field is used.

**Definition 1.2 (maximal zero runs and records).** Fix a prime $p$. A zero
run is a finite nonempty maximal interval $[a,b]$ of consecutive nonnegative
indices on which $R_{3,1}(n)\equiv0\pmod p$. Thus $R_{3,1}(b+1)$ is nonzero
modulo $p$, and either $a=0$ or $R_{3,1}(a-1)$ is nonzero modulo $p$.
Its length is $b-a+1$. In fact $R_{3,1}(0)=1$, so $a=0$ never occurs.
A run is a record if its length is at least every earlier run length,
with ties allowed. The distinct positive record spectrum lists each such
length once. An integer interval with lower endpoint exceeding its upper
endpoint is empty and contributes no run. This is the record convention
of Eu–Huang–Kao, [§1.2](https://arxiv.org/html/2609.25742v1), also recorded
in the [corresponding Library note](../../../Library/Recurrence/euhuangkao2026zerorun.md).

## 2. Exact spectra

**Theorem 2.1 (Ma–Zhang).** For every prime $p$, every positive maximal
zero-run length of $R_{3,1}\bmod p$ occurs as a record value. The complete
sets of maximal zero-run lengths and of distinct positive record values
coincide and are as follows.

1. At $p=2$, the values are $\lfloor2^m/3\rfloor$, $m\ge2$, strictly
   increasing in $m$. Their first occurrences are
   $[\lceil2^{m+1}/3\rceil,2^m-1]$.
2. At $p=3$, the values are $3^m-1$, $m\ge1$, strictly increasing in $m$.
   Their first occurrences are $[(3^m+1)/2,(3^{m+1}-3)/2]$.
3. At every prime $p\ge5$, put $q=p^m$ for integers $m\ge1$, and define

$$
I_1(q)=[\lceil q/3\rceil,(q-3)/2],\qquad
I_2(q)=[\lceil2q/3\rceil,q-1].
$$

Every nonempty one of these intervals is a first occurrence and a record,
ordered by increasing $m$ and then by $j=1,2$. Their lengths are

$$
L_1(q)=\begin{cases}(q-7)/6&q\equiv1\pmod6,\\
(q-5)/6&q\equiv5\pmod6,\end{cases}
\qquad L_2(q)=\lfloor q/3\rfloor.
$$

Omit $I_1(5)$ and $I_1(7)$, which are empty. There are no other omissions
or duplicate retained values for a fixed prime.
The proof is by Haobo Ma and Wenlin Zhang, *Complete small-prime record
spectra for $R_{3,1}$: proofs* (29 October 2026), including its explicit
extension of the third assertion to every prime $p\ge5$.

**Proof.**
### 2.1. Valuation intervals
The factorial identity $R_{3,1}(n)=(3n)!/[n!(2n+1)!]$ and Legendre's formula give
$$
 \nu_p(R_{3,1}(n))=\sum_{h\geq1}f_{p^h}(n\bmod p^h),\qquad
 f_q(x)=\left\lfloor 3x/q\right\rfloor-\left\lfloor (2x+1)/q\right\rfloor.
$$
At $x=0$ the function is zero. For $1\leq x<q$, the two numerators differ
by $x-1\in[0,q)$, so $f_q(x)\in\{0,1\}$. Solving the inequalities that
a multiple of $q$ lies above $2x+1$ and at most $3x$ shows that
$$
 \{x:f_q(x)=1\}=\bigcup_{j=1}^2
 [A_j(q),B_j(q)],\quad
 A_j(q)=\left\lceil jq/3\right\rceil,\quad B_j(q)=\left\lfloor (jq-2)/2\right\rfloor.
$$
An interval with $A_j>B_j$ is empty. Thus $R_{3,1}(n)$ is zero modulo $p$
exactly when at least one scale in the valuation formula in §2.1 is one.

### 2.2. All primes at least five
The endpoint assertion needed in this proof is the following: for $p\geq5$, $q=p^m$, $m\geq1$, the immediate neighbors of every nonempty
$I_j(q)=[A_j(q),B_j(q)]$ are nonzero modulo $p$.

To prove the endpoint assertion, proceed as follows.
First fix a lower or equal scale $P=p^h\leq q$, $1\le h\le m$.
Since $3\nmid jq$, the left neighbor can be written
$n=A_j(q)-1=(jq-s)/3$, with $s\in\{1,2\}$. Its residue modulo $P$ is
$x=(eP-s)/3$, with $e\in\{1,2\}$; this representative lies in $[0,P)$.
The first floor in $f_P(x)$ is $e-1$. For the second floor, compute
$$
 2x+1-(e-1)P=\frac{(3-e)P-2s+3}{3}.
$$
This is strictly between $0$ and $P$ for $P\geq5$, $e,s\in\{1,2\}$:
the numerator is at least $P-1>0$, and is at most $2P+1<3P$.
Both floors therefore equal $e-1$.

The right neighbor of $I_1(q)$ is $(q-1)/2$; its residue modulo $P$ is
$(P-1)/2$. The floors in $f_P$ are both $1$, since $P\geq5$.
The right neighbor of $I_2(q)$ is $q$, whose residue is zero.
At all higher scales $P\geq pq$, every neighbor under consideration
satisfies $0\leq n\leq q$ and
$3n\leq3q<pq\leq P$, $2n+1\leq2q+1<pq$.
Both floors vanish. The valuation formula in §2.1 proves the claim.


For completeness and records at $p\ge5$, proceed as follows.
Let $W_m$ be the zero/nonzero word on $0\leq n<q=p^m$. All scales above
$q$ vanish throughout this word, because $3n<pq$. Put $Q=q/p$.
The union of scales at most $Q$ is $p$ copies of $W_{m-1}$, and the
boundary between adjacent copies is nonzero for these lower scales:
$f_{p^h}(tQ)=f_{p^h}(0)=0$ for $h<m$.
Here $W_0$ is the one-symbol nonzero word. Adding scale $q$ overlays only
$I_1(q)$ and $I_2(q)$. By the endpoint assertion above, their immediate
neighbors are nonzero for all lower scales as well. Consequently an old
zero run that meets an added interval lies entirely inside it, and any
old run that survives retains its original length. No old run can cross
an added interval boundary, and no two runs outside the intervals merge.
The end of $W_m$ is closed by the nonzero value at $q$.
Induction proves that every closed run in $[0,q]$ has length
$L_j(p^h)$ for some $h\leq m$ and nonempty $I_j(p^h)$.
Every finite run lies in such a prefix. Conversely, each nonempty
$I_j(p^h)$ is an actual maximal zero run by the interval identity and
the endpoint assertion above. This proves both directions for all lengths.

For odd $q$ not divisible by $3$, direct rounding gives the formulas in
Theorem 2.1. In particular
$$
 L_1(q)\geq(q-7)/6,\quad L_1(q)\leq(q-5)/6,
 \quad (q-2)/3\leq L_2(q)\leq q/3.
$$
For $q\geq5$, these imply $L_2(q)-L_1(q)\geq(q+1)/6>0$.
For $m\geq2$, $Q=p^{m-1}\geq p\geq5$ and
$$
 L_1(pQ)-L_2(Q)\geq\frac{(p-2)Q-7}{6}>0,
$$
because $(p-2)Q-7\geq3\cdot5-7=8$.
The only nonpositive first-scale entries are $L_1(5)=L_1(7)=0$.
Thus every retained value is strictly larger than all values at earlier
scales, and the two values within a scale strictly increase.
Before the first interval of a scale there are only lower-scale runs;
before its second interval there are those and its first interval.
Hence the displayed witnesses are first occurrences and records.


### 2.3. The binary automaton
Modulo $2$, the denominator $2n+1$ is odd, so the nonzero condition is
that $\binom{3n}{n}$ be odd. Lucas' theorem, or the binary carry formula
for this binomial coefficient, says precisely that adding $n$ to $2n$
has no carries. This is equivalent to
$$
 n\mathbin{\&}(2n)=0,
$$
where $\&$ is bitwise AND: the binary expansion of $n$ has no adjacent
ones. For completeness, the valuation identity
$\nu_2\binom{a+b}{a}=s_2(a)+s_2(b)-s_2(a+b)$ counts the carries;
here $s_2(t)$ is the sum of the binary digits of $t$, and one obtains
it from $\nu_2(t!)=t-s_2(t)$. A carry occurs if and only if
there is a first position with a one in both summands, giving
the binary condition in §2.3. The associated digit automaton records whether the
preceding digit was one and rejects a second consecutive one.

Let $S_m$ be its accepted integers below $2^m$. Then
$$
 S_0=\{0\},\quad S_1=\{0,1\},\quad
 S_m=S_{m-1}\ \cup\ (2^{m-1}+S_{m-2})\quad(m\geq2).
$$
Its greatest element is
$M_m=\left\lfloor 2^{m+1}/3\right\rfloor$: this holds at $m=0,1$, and the recurrence
$M_m=2^{m-1}+M_{m-2}$ proves it for every $m$.
Adjoin the next accepted integer $2^m$ to $S_m$, and let $G_m$ be the
set of positive numbers of zeros between consecutive accepted integers
in this augmented set. The first block through the first integer of
the second block gives exactly $G_{m-1}$. Internal gaps of the second
block are translated gaps between integers in $S_{m-2}$, hence belong
to $G_{m-2}\subseteq G_{m-1}$. The only remaining gap is the terminal
gap from $M_m$ to $2^m$, of length
$$
 \ell_m=2^m-1-M_m=\left\lfloor 2^m/3\right\rfloor.
$$
Thus $G_m=G_{m-1}\cup\{\ell_m\}$ when $\ell_m>0$, with no positive
gaps at $m=0,1$. The values $\ell_m$ strictly increase for $m\geq2$.
All gaps before the terminal one have length at most $\ell_{m-1}$;
therefore its interval $[M_m+1,2^m-1]=[\left\lceil 2^{m+1}/3\right\rceil,2^m-1]$
is the first occurrence of the new record. Every finite gap appears
in an augmented prefix. This proves all claims for $p=2$.

### 2.4. The ternary generating function
Lagrange inversion gives
$F(x)=\sum_{n\geq0}R_{3,1}(n)x^n=1+xF(x)^3$.
In characteristic $3$, Frobenius yields $F(x)=1+xF(x^3)$.
Comparison of coefficients, beginning with the constant term $1$,
determines the unique series
$$
 F(x)=\sum_{h\geq0}x^{s_h},\qquad s_h=(3^h-1)/2.
$$
Indeed $s_{h+1}=1+3s_h$, so substituting the displayed series verifies
the equation and its constant term. All these nonzero coefficients
are $1$. Consecutive support indices satisfy
$s_{h+1}-s_h=3^h$. For $h=0$ the gap is empty; for every $h\geq1$
the gap is precisely $[s_h+1,s_{h+1}-1]$ with length $3^h-1$.
These gaps exhaust the sequence and strictly increase, proving the
$p=3$ assertion, including the prime dividing $k=3$. $\square$

## 3. Affine families and initial witnesses

**Corollary 3.1 (explicit small-prime families).** A quadruple $(p,a,b,c)$
in the following table denotes the length $(ap^m+b)/c$. For each fixed
prime in the table the rows form disjoint families of distinct positive
record values, subject to the stated exponent restrictions.

| Prime | $(p,a,b,c)$ | Exponents |
| --- | --- | --- |
| $2$ | $(2,1,-1,3)$ | even $m\ge2$ |
| $2$ | $(2,1,-2,3)$ | odd $m\ge3$ |
| $3$ | $(3,1,-1,1)$ | $m\ge1$ |
| $5$ | $(5,1,-5,6)$ | odd $m\ge3$ |
| $5$ | $(5,1,-7,6)$ | even $m\ge2$ |
| $5$ | $(5,1,-2,3)$ | odd $m\ge1$ |
| $5$ | $(5,1,-1,3)$ | even $m\ge2$ |
| $7$ | $(7,1,-7,6)$ | $m\ge2$ |
| $7$ | $(7,1,-1,3)$ | $m\ge1$ |
| $11$ | $(11,1,-5,6)$ | odd $m\ge1$ |
| $11$ | $(11,1,-7,6)$ | even $m\ge2$ |
| $11$ | $(11,1,-2,3)$ | odd $m\ge1$ |
| $11$ | $(11,1,-1,3)$ | even $m\ge2$ |

The first distinct records and first three witness intervals are:

| $p$ | First distinct records | First three witness intervals |
| --- | --- | --- |
| $2$ | $1,2,5,10,21,42,85$ | $[3,3],[6,7],[11,15]$ |
| $3$ | $2,8,26,80,242,728$ | $[2,3],[5,12],[14,39]$ |
| $5$ | $1,3,8,20,41,103$ | $[4,4],[9,11],[17,24]$ |
| $7$ | $2,7,16,56,114,399$ | $[5,6],[17,23],[33,48]$ |
| $11$ | $1,3,19,40,221,443$ | $[4,4],[8,10],[41,59]$ |

**Proof.** Substitute the indicated primes and exponent parities into
Theorem 2.1. At $p=2$, $m=0,1$ give zero; at $p=3$, $m=0$ gives zero.
The first-interval families at $(p,m)=(5,1),(7,1)$ likewise give zero.
None is a positive zero run, so no positive value is removed. The strict
ordering and the first-occurrence assertion follow from Theorem 2.1.
$\square$

## 追加锚（本行以下为增补区）
