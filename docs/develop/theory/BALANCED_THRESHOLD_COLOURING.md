# Mechanical colouring for the odd balanced threshold

## 1. Two constant-gap palettes

For $t>0$, the alphabet is $\{0,\ldots,2t+2\}$.
Let $u$ be the lower mechanical word of slope $0<\alpha<1$ and intercept $\rho$.
Its successive true letters receive colours $0,1,0,1,\ldots$.
Its false letters of ranks $2j$ and $2j+1$ receive respectively colours
$2+(j\bmod t)$ and $2+t+(j\bmod(t+1))$.
All ranks start at zero.

**Theorem 1.1 (Palette colouring).** This colouring is balanced and uses every
letter of its alphabet. The assertion holds for every real intercept.

For each colour, counting in a physical window reduces to counting a single
residue class in a consecutive interval of ranks of one source letter.
Induction on the physical window length establishes that reduction.
Equal-length mechanical windows have source counts differing by at most one;
division with remainder then bounds the difference of colour counts by one.
Both source-letter prefix counts are unbounded because their discrepancies
from $n\alpha$ and $n(1-\alpha)$ are bounded. The first prefix count exceeding
a given rank constructs an occurrence at that rank, so every palette colour
appears.

## 2. The quadratic parameter

For every integer $t\geq5$, put $A=t-2$, $B=t+1$, $N=AB$ and

$$
x=\frac{\sqrt{N(N+4)}-N}{2A},\qquad
\alpha=\frac1{t+3+1/(t+x)}.
$$

**Theorem 2.1 (Quadratic parameter).** The positive tail $x$ is irrational,
satisfies $Ax^2+ABx-B=0$, and obeys

$$
\frac1{t-1}<x<\frac1{t-2},\qquad
2<(2t-1)x,\qquad (2t+1)x<t.
$$

The frequency $\alpha$ is irrational and satisfies
$1/(t+4)<\alpha<1/(t+3)$.
The discriminant lies strictly between $(N+1)^2$ and $(N+2)^2$;
classification of an integer square root by these adjacent integers excludes a square.
The quadratic identity and positivity bound $x$ between the two reciprocals.
The margin $t^2-4t-1>0$ supplies the second strict separation estimate.
This algebraic statement does not identify the infinite continued fraction or
establish a critical-exponent bound.

## 3. The attaining prefix

**Theorem 3.1 (Attainment).** Give the lower mechanical word of slope
$\alpha$ intercept $\alpha$, and colour it by the zero-phase palettes of
Theorem 1.1. Its prefix of length $2t+2$ has least positive period $2t+1$.
Consequently its critical exponent is at least $(2t+2)/(2t+1)$.

For $0\leq k\leq2t+2$, the floor of $(k+1)\alpha$ is zero for
$k\leq t+2$ and one otherwise. The only minority letter in the prefix
occurs at $t+2$. The prefix starts with $B_0$, the first $2t$ majority
occurrences are distinct, and its last letter is $B_0$ again. Equality
of the endpoints supplies the period; any smaller positive period would
identify the first letter with a distinct interior letter.

## 4. Repetition and bispecial return bounds

**Theorem 4.1 (Bispecial supplier).** Let an infinite word be uniformly
recurrent and not eventually periodic. Suppose $C>0$ and every adjacent
return displacement $r$ of every nonempty bispecial factor $w$ satisfies
$C|w|\leq r$. Then every length-$n$ window of positive period $p$ satisfies
$n\leq(1+1/C)p$.

A failure of period $p$ occurs in some factor of length $p+1$.
Uniform recurrence makes such failures have bounded gaps. Extend the
given repetition to its first right failure, move that entire pattern
to a sufficiently late occurrence, and extend left to its first failure.
The two resulting equal factors have distinct preceding and following
letters, hence are bispecial, and their common length is at least $n-p$.
The first intervening occurrence is an adjacent return of length at most
$p$. Applying the assumed return bound gives $C(n-p)\leq p$.
The cases $n\leq p$, including an empty overlap, satisfy the conclusion
directly and require no return hypothesis.

## 5. Computed continued fraction

**Theorem 5.1 (Ratio expansion).** The frequency ratio
$\theta=\alpha/(1-\alpha)$ has computed continued fraction

$$
\theta=[0;t+2,t,\overline{t-2,t+1}].
$$

Put $y=1/(t+1+x)$. The positive quadratic equation gives
$x^{-1}=t-2+y$ and $y^{-1}=t+1+x$, with both $x,y$ strictly between
zero and one. The floor algorithm therefore alternates these two complete
quotients indefinitely. A simultaneous induction computes every tail digit;
the two reciprocal prefix steps yield the initial digits $t+2,t$.
This identifies the expansion, but does not classify Sturmian factors or returns.

## 追加锚（本行以下为增补区）

## 6. Palette synchronization

**Theorem 6.1 (Synchronization).** For every positive integer $t$, any two
equal coloured mechanical windows containing at least one true source letter
and at least two false source letters have equal source windows. Their initial
true occurrence ranks are equal modulo $2$, and their initial false occurrence
ranks are equal modulo $2t(t+1)$. No irrationality or frequency bound is needed
for this statement.

The disjoint colour ranges recover each source letter. Induction on the physical
window length extracts the entire consecutive interval of observed ranks in each
palette. The first true rank fixes the two-cycle phase. The first two false ranks
contain one colour of each majority cycle. Their order fixes parity; their colour
indices fix the quotient ranks modulo $t$ and $t+1$. Consecutive-integer
coprimality combines these quotient residues, and parity recovers the full false
rank modulo $2t(t+1)$. A window containing only one false occurrence does not
determine the full majority phase.


## 7. Coloured uniform recurrence

**Theorem 7.1 (Uniform recurrence).** For every irrational frequency
$0\leq\alpha<1$, every real intercept $\rho$, and every positive $t$,
the zero-phase coloured mechanical word is uniformly recurrent: every
occurring finite window reappears within a bounded displacement from every
starting position.

Put $P=2t(t+1)$. At a given factor start $s$, choose a positive right-hand
perturbation smaller than the remaining distance to the next integer at
every endpoint $\rho+(s+k)\alpha$, for $0\leq k\leq n$. All these
floors then remain unchanged. Restrict new starts to the physical residue
class of $s$ modulo $P$. Along this arithmetic progression the normalized
phase $(\rho+j\alpha-\rho-s\alpha)/P$ advances by $\alpha$ on the
unit circle. Irrational rotation is dense; compactness turns the inverse
images of the positive perturbation interval into a finite cover, giving
a uniform return bound. At a return, all endpoint floors differ from the
original floors by the same integer multiple of $P$. Telescoping shows
that every true occurrence rank agrees modulo $P$, and the physical index
congruence gives the same agreement for every false occurrence rank.
The divisors $2$, $2t$, and $2(t+1)$ determine the two-cycle phase and
both interleaved majority colours. Thus the entire coloured factor recurs.

## 追加锚（本行以下为增补区）

## 8. Nonsynchronizing returns

**Theorem 8.1 (Short-return bound).** Fix $t\geq5$, the quadratic frequency
$\alpha$ of Theorem 2.1, and any real intercept. If a nonempty coloured
factor contains no minority letter, or at most one majority letter, then
any two occurrences at starts $i<j$ satisfy

$$
(2t+1)|w|\leq j-i.
$$

A minority-containing nonsynchronizing factor projects to $a$, $ab$, or
$ba$. Equal minority colours force an even positive minority displacement
$P$. The source spacing gives majority displacement $Q\geq P(t+2)$.
For the mixed projections, $Q$ is divisible by the gap of their observed
majority colour, either $2t$ or $2t+2$. Consequently $Q\geq4t$ and
$P+Q\geq4t+2$. A lone minority colour already has displacement greater
than $2t+1$.

A pure majority factor has length at most $t+3$. A single colour has
majority displacement at least $2t$, and the source floor constraints
exclude physical displacement $2t$. With at least two majority colours,
the two observed cycle indices force $Q$ to be divisible by
$M=2t(t+1)$. Lengths at most $t$ are covered by $Q\geq M$.

For longer runs, divide the starting mechanical fractional part by
$1-\alpha$. A run of length $t+1$ places this normalized phase in
$[0,h)$, where $h=1-t\theta$ and $\theta=\alpha/(1-\alpha)$.
At $Q=M$ the normalized phase displacement is $M\theta-P$.
Writing $f=M\theta-(2t-2)$, the quadratic parameter gives
$h<f<1-h$. No integer $P$ can put both phases in $[0,h)$.
Thus $Q\geq2M>(2t+1)(t+3)$ for the remaining run lengths.
No minority phase is imposed on a pure majority factor.

## 9. Infinite denominator residue orbit

**Theorem 9.1 (Denominator orbit).** Let $q_N$ be the denominator of
convergent $N$ in Mathlib's computed expansion of
$\theta=\alpha/(1-\alpha)$. For every $N\geq1$, its residues modulo $t$
are, in order of $N\bmod8=0,\ldots,7$,

$$
(-1,2,1,0,1,-2,-1,0).
$$

Modulo $t+1$, the residue is one for odd $N$ and zero for even $N$.
The denominators are integral. The initial denominators are
$q_1=t+2$ and $q_2=t(t+2)+1$; the tail coefficients are $t-2,t+1$
in alternating order. Two-step induction preserves the ordered residue
pair and coefficient phase. The eight transitions are local steps of
that induction, not a finite observation offered as periodicity.
The ordered pair involving $q_0$ is excluded from the periodic orbit.

## 10. Physical realization of the majority-index rotation

**Proof supplement for Theorem 8.1.** In the characteristic representative,
the majority-index model can be obtained by reconstructing every physical
prefix. This reconstruction also handles rational frequencies and exact
floor boundaries. Let $0<\alpha<1/2$, put
$\theta=\alpha/(1-\alpha)$, and define

$$
u(n)=\lfloor(n+2)\alpha\rfloor-\lfloor(n+1)\alpha\rfloor,
\qquad
v(k)=\lfloor(k+2)\theta\rfloor-\lfloor(k+1)\theta\rfloor.
$$

Both words have letters zero and one. The zero of rank $k$ in $u$ is at

$$
n_k=k+\lfloor(k+1)\theta\rfloor.
$$

Indeed, writing $q=\lfloor(k+1)\theta\rfloor$, multiplication of
$q\leq(k+1)\theta<q+1$ by $1-\alpha$ gives

$$
\lfloor(n_k+1)\alpha\rfloor
=\lfloor(n_k+2)\alpha\rfloor=q.
$$

Thus $u(n_k)=0$. Floor telescoping counts $q$ ones before $n_k$,
leaving exactly $n_k-q=k$ zeros; hence this is the zero of rank $k$.
Successive positions satisfy $n_{k+1}-n_k=1+v(k)$.
When $v(k)=1$, the endpoint floors also give $u(n_k+1)=1$.
When $v(k)=0$, the next zero is immediately adjacent.

Induction on $k$ now reconstructs $u[0,n_k)$ as the concatenation of
the first $k$ blocks obtained from $v$: the block for zero is $(0)$,
and the block for one is $(0,1)$. The initial block starts at $n_0=0$.
This identifies the intervening minority letters with the characteristic
rotation at frequency ratio $\theta$, with its intercept fixed explicitly.


## 11. One-step descent of mechanical bispecial factors

**Theorem 11.1 (Bispecial descent).** Let $0<\alpha<1/2$, set
$\theta=\alpha/(1-\alpha)$, and take the characteristic mechanical words
$u(n)=\lfloor(n+2)\alpha\rfloor-\lfloor(n+1)\alpha\rfloor$ and
$v(k)=\lfloor(k+2)\theta\rfloor-\lfloor(k+1)\theta\rfloor$.
Every nonempty bispecial factor $w$ of $u$ has the form

$$
w=\varphi(z)0,\qquad \varphi(0)=0,\qquad \varphi(1)=01,
$$

where $z$ is a bispecial factor of $v$ and $|z|<|w|$. The empty $z$
is permitted. Let $n_k$ be the position of the zero of rank $k$ in $u$,
as computed in Section 10. For every physical start $i$,

$$
u[i,i+|w|)=w\quad\Longleftrightarrow\quad
\exists k:\ n_k=i\text{ and }v[k,k+|z|)=z.
$$

Each occurrence of $z$ has the exact physical endpoint
$n_{k+|z|}+1=n_k+|w|$. This statement includes rational frequencies;
it assumes neither recurrence nor irrationality.

A true letter of $u$ has false neighbours because $2\alpha<1$.
Distinct left extensions therefore force the first letter of $w$ to be
false, and distinct right extensions force its last letter to be false.
The zeros at these endpoints identify a majority-rank interval. The prefix
reconstruction of Section 10 reconstructs this interval by the blocks
$0$ and $01$, followed by the terminal zero.

Induction on the decoded list proves uniqueness: equal initial blocks
cancel, while unequal blocks are distinguished by the next letter.
The terminal zero handles the end of the list. Thus all occurrences
of $w$ decode to the same $z$. Conversely every occurrence of $z$
reconstructs $w$; equality of encoded lengths gives its physical endpoint.
The predecessor of $n_k$ is $v(k-1)$ for $k>0$, and the successor of
$n_{k+|z|}$ is $v(k+|z|)$. Consequently the two distinct left and right
extensions descend to $z$. Every block is nonempty, so the terminal
zero makes $z$ strictly shorter than $w$.

This theorem supplies one descent step. Identifying the complete
continued-fraction return vectors and the derived-word strip remains
an additional formalization obligation.

## 12. Unimodular return classification

**Theorem 12.1.** Let $\alpha$ be irrational with $0<\alpha<1$, and let
$u(n)=\lfloor(n+2)\alpha\rfloor-\lfloor(n+1)\alpha\rfloor$.
For every bispecial factor $w$, including the empty factor, there are
nonempty binary words $r,s$ such that every adjacent return block to $w$
is either $r$ or $s$. Writing $|v|_a$ for the number of letters $a$ in $v$,
these words satisfy

$$
|r|_0|s|_1-|r|_1|s|_0\in\{-1,1\},\qquad
|r|_a+|s|_a=|w|_a+1\quad(a=0,1).
$$

The classification is an inclusion statement; realization of both candidate
return blocks is not part of this theorem.

Strong induction on $|w|$ constructs the two blocks. For the empty factor,
adjacent occurrences are consecutive positions and the candidates are $0,1$.
For $\alpha<1/2$, Section 11 descends $w$ to a shorter factor $z$ at frequency
$\alpha/(1-\alpha)$. Strict monotonicity of majority occurrence positions
identifies adjacency in both words. Section 10 reconstructs each physical
return block as the image of a return block to $z$ under $0\mapsto0$,
$1\mapsto01$. This substitution sends Parikh vectors $(P,Q)$ to $(P,P+Q)$,
where the coordinates count ones and zeros. It preserves the absolute
unimodular determinant. The terminal zero in $w=\varphi(z)0$ gives the
asserted factor-count identity.

For $\alpha>1/2$, irrationality excludes integer endpoints and identifies
the characteristic word of frequency $1-\alpha$ with the positionwise
complement of $u$. Complementing factors and return blocks swaps the two
Parikh coordinates and negates the determinant. The previous descent now
applies. Irrationality is preserved by the frequency-ratio map, so the
induction covers every positive factor length without a rational boundary
exception. Identifying these two vectors with continued-fraction convergents
and proving the derived-language strip remain separate obligations.


**Proposition 12.2 (Occurrence displacements).** For the irrational characteristic
mechanical word and bispecial factor of Theorem 12.1, the same candidates $r,s$
can be chosen so that every pair of occurrence starts $i<j$ has nonnegative
integer multiplicities $k,\ell$, with $k+\ell>0$, satisfying

$$
|u[i,j)|_a=k|r|_a+\ell|s|_a\quad(a=0,1),
$$

and

$$
\left|k\bigl(|r|_1-\alpha|r|\bigr)
 +\ell\bigl(|s|_1-\alpha|s|\bigr)\right|<1.
$$

Strong induction on $j-i$ splits the interval at the least next occurrence of
$w$. Such an occurrence exists no later than $j$. Its first return block is
$r$ or $s$ by Theorem 12.1. The remaining interval is strictly shorter;
adding one to the corresponding multiplicity completes the induction.
List concatenation adds each letter count. Since the displacement is positive,
at least one return block is used. This argument includes the empty factor and
places no upper bound on the number of intervening occurrences.

Adding the two count identities gives $j-i=k|r|+\ell|s|$. The weighted expression
is therefore $|u[i,j)|_1-\alpha(j-i)$, whose absolute value is strictly below one
by mechanical floor telescoping. This physical discrepancy bound does not give
the sharper derived-language strip: that further bound requires the diameter
of the bispecial occurrence cylinder and identification of the two return errors.

## 13. Realization of distinct returns

**Theorem 13.1 (Return variation).** Let $0<\alpha<1$ be irrational and let
$\rho$ be any intercept. For every occurring factor $w$ of the lower mechanical
word $u$ and every finite binary word $r$, there are consecutive occurrences
$i<j$ of $w$ with $u[i,j)\ne r$. The empty factor is included.

Uniform recurrence supplies a next occurrence after every occurrence. If every
return were the same word $r$, then $L=|r|>0$. Induction through successive
occurrences constructs, for every $k$, an interval of length $kL$ with exactly
$k|r|_1$ ones. Its mechanical discrepancy is
$k\bigl(|r|_1-\alpha L\bigr)$ and has absolute value below one. The coefficient
is nonzero by irrationality of $\alpha$; an Archimedean choice of $k$ gives a
contradiction. Thus a single return block cannot exhaust the returns.

For a bispecial factor, apply this theorem separately to the two candidates
of Theorem 12.1. Its exhaustive classification then realizes both candidates
as actual adjacent return blocks. This does not identify their convergent
indices or supply the sharper derived-language strip.

## 14. Strict discrepancy strip at a bispecial factor

Let $0<\alpha<1$ be irrational and let $u$ be the characteristic lower
mechanical word $u_i=\lfloor(i+2)\alpha\rfloor-\lfloor(i+1)\alpha\rfloor$.
For $i<j$ define the physical discrepancy

$$
e(i,j)=|u[i,j)|_1-\alpha(j-i).
$$

**Theorem 14.1 (Strict bispecial strip).** Let $w$ be any bispecial factor,
including the empty factor. Suppose $i<j$ are two occurrence starts of $w$,
$(a,b)$ and $(c,d)$ are adjacent occurrence pairs, and the actual return
blocks $u[a,b)$ and $u[c,d)$ are distinct. Then

$$
|e(i,j)|<|e(a,b)|+|e(c,d)|.
$$

Strong induction on the length of $w$ proves the assertion. For the empty
factor adjacent starts differ by one, so the two distinct return blocks
are the two letters. Their absolute discrepancies sum to one, and the
strict mechanical discrepancy bound applies to every physical window.
For $\alpha<1/2$, bispecial descent at the majority occurrence positions
produces a shorter bispecial factor for frequency
$\theta=\alpha/(1-\alpha)$. The occurrence correspondence is exact and
strictly increasing, so adjacent physical occurrences become adjacent
occurrences of the shorter factor. Between any two majority positions,
block reconstruction preserves the true count and adds that count to the
derived length. Consequently

$$
e_{\alpha}(\operatorname{pos}(k),\operatorname{pos}(l))
=(1-\alpha)e_{\theta}(k,l).
$$

The three discrepancies in the desired inequality share this positive
scale factor. Equality of descended return blocks would imply equality of
the original blocks, so the induction hypothesis applies to distinct
returns. When $\alpha>1/2$, irrational complementation replaces the
frequency by $1-\alpha$, preserves bispeciality and occurrence adjacency,
and negates every discrepancy. The strict inequality is therefore
unchanged. Irrationality excludes the frequency $1/2$.

This theorem uses actual physical returns, not assumed return candidates.
The two-return classification and realization theorem supply its two
returns. Continued-fraction indexing and the conversion to a particular
derived slope require the corresponding vector identification.

## 15. Euclidean indexing of a unimodular bracket

**Theorem 15.1 (Computed continuant classification).** Let $0<\theta<1$
be irrational. Let $(p,q)$ and $(r,s)$ have nonnegative integer coordinates,
determinant $ps-rq=\pm1$, and opposite signs of $p-\theta q$ and
$r-\theta s$. They are, in either order,

$$
(p_N,q_N),\qquad m(p_N,q_N)+(p_{N-1},q_{N-1}),
\qquad 0\leq m<a_{N+1},
$$

for some $N\geq0$, where these are the continuants of the computed
continued fraction of $\theta$ and $(p_{-1},q_{-1})=(1,0)$.
Zero coordinates, including the initial pair, are allowed.

Strong induction on $p+q+r+s$ proves the classification. Put
$c=\lfloor\theta^{-1}\rfloor$ and $y=\{\theta^{-1}\}$.
If one numerator is zero, unimodularity forces its denominator and the
other numerator to be one; strict bracketing bounds the remaining
coordinate by $c$. Otherwise both numerators are positive. If $q<cp$,
the other vector must satisfy $s>cr$, since $c\theta<1$.
The determinant magnitude is then at least $p+r\geq2$, a contradiction.
The symmetric argument gives $s\geq cr$ as well. Consequently

$$
(q-cp,p),\qquad(s-cr,r)
$$

are nonnegative, unimodular, bracket $y$, and have a strictly smaller
coordinate sum. Each discrepancy is the original discrepancy multiplied
by $-1/\theta$. The computed continuant recurrence lifts the inductively
classified pair through $(u,v)\mapsto(v,u+cv)$. An endpoint multiplier
equal to the next digit is represented at the next convergent with
multiplier zero. Irrationality ensures the following digit exists and
is positive, so this normalization gives the strict multiplier range.

## 16. Exact quadratic continuant error orbit

Let $t\geq5$, $x$ be the positive root of
$(t-2)x^2+(t-2)(t+1)x-(t+1)=0$, $y=1/(t+1+x)$,
$\delta=1/(t+x)$, and $\theta=1/(t+2+\delta)$.
Use the computed continuants of $\theta$, including the predecessor
$(p_{-1},q_{-1})=(1,0)$, and write
$E_N=p_N-\theta q_N$. Set

$$
z_N=\begin{cases}
\delta,&N=0,\\
x,&N\text{ odd},\\
y,&N>0\text{ even}.
\end{cases}
$$

**Theorem 16.1 (Exact error orbit).** At every $N\geq0$,
$0<z_N<1$, $E_N\ne0$, and

$$
E_{N-1}=-(a_{N+1}+z_N)E_N.
$$

The live new argument is induction through the entire infinite error orbit,
including the exceptional initial tail. The quadratic equation gives
$x(t-2+y)=1$ and $y(t+1+x)=1$, while $\delta(t+x)=1$.
Consequently $z_N(a_{N+2}+z_{N+1})=1$ at every index.
The initial relation follows from $E_{-1}=1$, $E_0=-\theta$.
The actual continuant recurrence then gives $E_{N+1}=-z_NE_N$;
the reciprocal tail identity propagates the predecessor relation and
strict tail positivity preserves nonvanishing. No truncation or finite
verification replaces this unbounded induction.

For a semiconvergent return $s=m(p_N,q_N)+(p_{N-1},q_{N-1})$,
the discrepancy ratio is therefore $a_{N+1}-m+z_N$.
Its use in the strict physical bispecial strip requires the actual
return-vector identification and both realized adjacent returns.

## 17. Exhaustive coloured bispecial projection classification

**Theorem 17.1 (Coloured projection classification).** For $t\geq5$, let
$\alpha=\operatorname{uniformSlope}(t)$ and use the zero-phase colouring of
$u=\operatorname{lowerMechanicalWord}(\alpha,\alpha)$. At every occurrence
of a nonempty coloured bispecial factor, its binary projection satisfies
exactly one of the following alternatives:

- It contains at least one minority letter and at least two majority
  letters, and is a binary bispecial factor.
- It belongs to $\{a,ab,ba\}\cup\{b^j:1\leq j\leq t+3\}$.

The classification is independent of the occurrence chosen. In the first
case the existing palette synchronization recovers both prefix-rank
residues. Adding the common factor counts recovers both right-boundary
phases. Subtracting the common extension letter recovers both left-boundary
phases. Thus two different coloured extensions cannot have the same binary
letter, on either side.

For the second case, write $A$ for the minority count and $B=n-A$ for
the majority count. If $A>0$ and $B\leq1$, the strict discrepancy estimate
gives

$$
n(1-\alpha)=A-n\alpha+B<1+B\leq2.
$$

Since $\alpha<1/3$, this implies $n<3$. At length two, the same estimate
forces $A=1$, leaving exactly $a,ab,ba$. If $A=0$, it instead gives
$n\alpha<1$; the bound $\alpha>1/(t+4)$ yields $n<t+4$.
Neither the short-factor length reduction nor the boundary phase decoding
requires a new mathematical supplier. They are direct applications of the
existing discrepancy and synchronization results inside the critical-exponent
proof. No phase constraint is imposed on a palette absent from the factor.

## 18. Growth of physical continuant lengths

**Theorem 18.1 (Continuant length growth).** For the quadratic family with
$t\geq5$, let $g$ be the computed continued fraction of
$\theta=\alpha/(1-\alpha)$ and write

$$
L_n=(g.\operatorname{contsAux}(n))_a+
    (g.\operatorname{contsAux}(n))_b.
$$

Then $L_n>0$ for every $n\geq0$, and $L_n<L_{n+1}$ for every $n\geq1$.
The initial lengths satisfy $L_0=L_1=1$; strict growth does not include
that initial pair. Consequently the physical lengths $H=L_N$ and
$R=L_{N+1}$ satisfy $0<H<R$ whenever $N\geq1$.

The computed digit stream gives the recurrence
$L_{n+2}=a_{n+1}L_{n+1}+L_n$, with every $a_{n+1}\geq3$.
The two positive seeds and two-step induction give positivity at every
index. The same recurrence, its positive predecessor, and
$a_{n+1}\geq1$ give strict growth after the equal initial lengths.
