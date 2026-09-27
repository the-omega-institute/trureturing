[Index](../../marked_head_profile.md) · [Original full-prefix constraints](../321-384/340-whole-cover-completion-constrains-original-prefix-loads.md) · [Original extremal family](../321-384/350-extremal-paired-branch-and-source-support.md)

# The private-witness profile upper is automatic for odd divisor labels

Bollobás's set-pair inequality gives a valid pointwise bound using actual
private points of congruence classes. Its integration over the original
prime-covered region has exact coefficients determined by the numerical
moduli and the full prime-power heights. However, that numerical upper
bound holds for every set of distinct odd divisor labels, whether or not
the labels admit an irredundant realization. It therefore excludes no
such numerical profile. Restricting instead to the prime-free region
still gives a uniform bound below \(5/8\). Even on the actual product
of all pure-power survivors, the conditional expectation of the same
integrand stays below \(80/81\);
these restrictions cannot turn its upper bound of one into an exclusion.

The domination proof below enlarges prefix supports to all digit
subsets and integrates an explicit nonnegative polynomial identity.
Oddness enters through \(1/p\le1/3\); no height bound is imposed.
These are ordinary deductions, not new Lean verification, a literature
novelty claim, or an unrestricted covering exclusion.

## 1. The valid private-point inequality

Let \(Q=\prod_{p\in\Lambda}p^{H_p}\), with every \(p\) odd and
\(H_p\ge1\). Use the lowest-first digit coordinates

\[
 I=\{(p,j):p\in\Lambda,\ 1\le j\le H_p\},\qquad L=|I|.
\]

Consider an irredundant family \(A_d=a_d\bmod d\) of distinct
nonunit divisors of \(Q\). For each label choose an actual private point
\(w_d\in A_d\setminus\bigcup_{e\ne d}A_e\). Put

\[
 F_d=\{(p,j):j\le v_p(d)\},\quad r_d=|F_d|=\Omega(d),\quad
 \Delta_d(x)=\{i\in I:w_d(i)\ne x(i)\}.
\]

For each fixed \(x\), the pairs \((\Delta_d(x),F_d)\) indexed by
classes containing \(x\) satisfy

\[
 \Delta_d(x)\cap F_e=\varnothing\quad\Longleftrightarrow\quad d=e.
\]

The diagonal case holds because both points lie in \(A_d\). Off the
diagonal, \(w_d\notin A_e\) while \(x\in A_e\), so they disagree in a
coordinate fixed by \(A_e\). Bollobás's inequality therefore gives

\[
 \sum_{d:x\in A_d}
       \binom{r_d+|\Delta_d(x)|}{r_d}^{-1}\le1.\tag{PW1}
\]

The source is David Ellis, *Irredundant Families of Subcubes*,
[arXiv:1003.2960v1, Theorem 3](https://arxiv.org/html/1003.2960v1#Thmtheorem3),
which states the general set-pair inequality. Ellis's
[equation (5)](https://arxiv.org/html/1003.2960v1#S2.E5) applies it to
binary subcubes of a common dimension \(k\). The argument above uses that same
set-pair theorem for varying codimensions and mixed alphabets; it does
not attribute those extra quantifiers to the literal binary statement.
Every displayed binomial coefficient in PW1 is inverted.

## 2. Exact original-Haar coefficients

Assume additionally that every support prime is an original label and,
after one CRT translation, \(A_p=0\bmod p\). Let \(H\) be uniform
probability on the complete carrier and set

\[
 U=\bigcup_{p\in\Lambda}A_p,\qquad
 P_0=\prod_{p\in\Lambda}(1-1/p),\qquad H(U)=1-P_0.
\]

For a composite label \(d\), privacy makes every first digit of \(w_d\)
nonzero. At a prime dividing \(d\), that digit is also fixed and nonzero
throughout \(A_d\). Define

\[
 W_d=\mathbb E_H\!\left[
       \frac{\mathbf1_U(X)}{\binom{r_d+|\Delta_d(X)|}{r_d}}
       \,\middle|\,X\in A_d\right].
\]

Integrating PW1 on \(U\), and dropping the nonnegative prime-label
terms, gives

\[
 \sum_{d\text{ composite}}\frac{W_d}{d}\le1-P_0.\tag{PW2}
\]

Write \(a_p=v_p(d)\). Independent free digits give the probability
generating polynomial

\[
 G_d(z)=\prod_p\left(\frac1p+\frac{p-1}{p}z\right)^{H_p-a_p}.
\]

To count only \(U^c\), a missing first-\(p\) digit has one allowed
value equal to \(w_d(p,1)\), and \(p-2\) allowed different values.
Thus the unnormalized polynomial is

\[
 G_d^0(z)=
 \prod_{p\nmid d}\left(\frac1p+\frac{p-2}{p}z\right)
 \prod_p\left(\frac1p+\frac{p-1}{p}z\right)^{{H_p-a_p-\mathbf1_{p\nmid d}}}.
\]

Consequently the exact coefficient is

\[
 W_d=\sum_{j=0}^{L-r_d}
       \frac{[z^j](G_d-G_d^0)}{\binom{r_d+j}{r_d}}.\tag{PW3}
\]

In particular \(c_d=G_d(1)-G_d^0(1)=1-\prod_{p\nmid d}(1-1/p)\).
For \(c_d>0\), put \(\beta_d=W_d/c_d\); then PW2 is
\(\sum_d\beta_dc_d/d\le1-P_0\). When \(c_d=0\), its summand is
zero. These coefficients no longer depend on the chosen private
points or the original nonzero residues.

## 3. The coefficient bound holds without any realization

**Profile domination.** For any set \(D\) of distinct composite odd
divisors of \(Q\), define \(W_d\) by the polynomial expression PW3,
without assuming the existence of classes or private points. Then

\[
 \sum_{d\in D}\frac{W_d}{d}\le1-P_0.\tag{PW4}
\]

To prove this, put \(u_i=1/p\) for \(i=(p,j)\), and distinguish the
first-digit set \(R=\{(p,1):p\in\Lambda\}\). For every nonempty
subset \(F\subseteq I\), not just a prefix support, define

\[
 \begin{aligned}
 G_F(z)&=\prod_{i\notin F}[u_i+(1-u_i)z],\\
 G_F^0(z)&=\prod_{i\in R\setminus F}[u_i+(1-2u_i)z]
             \prod_{i\notin F\cup R}[u_i+(1-u_i)z],\\
 q_F&=\left(\prod_{i\in F}u_i\right)
       \sum_{j\ge0}\frac{[z^j](G_F-G_F^0)}{\binom{|F|+j}{|F|}}.
 \end{aligned}\tag{PW5}
\]

The polynomial difference has nonnegative coefficients. Hence every
\(q_F\ge0\), and an original prefix satisfies \(q_{F_d}=W_d/d\).
Distinct numerical moduli have distinct prefix supports. It suffices
to bound \(\sum_{\varnothing\ne F\subseteq I}q_F\).

For \(r\ge1,j\ge0\), the elementary beta integral is

\[
 \binom{r+j}{r}^{-1}
       =r\int_0^1t^{r-1}(1-t)^j\,dt.
\]

Set

\[
 A_i(t)=1-(1-2u_i)t,\qquad
 C_i(t)=\begin{cases}
 A_i(t)-u_i(1-t),&i\in R,\\
 A_i(t),&i\notin R.
 \end{cases}
\]

Expanding \(r=|F|\) as a sum over the marked element \(i\in F\),
then summing independently over every other coordinate's membership
in \(F\), gives

\[
 \sum_{F\ne\varnothing}q_F=\int_0^1J(t)\,dt,\qquad
 J(t)=\sum_{i\in I}u_i
       \left(\prod_{j\ne i}A_j(t)-\prod_{j\ne i}C_j(t)\right).
 \tag{PW6}
\]

Indeed a free ordinary coordinate contributes
\(1-(1-u_i)t\), and including it in \(F\) contributes \(u_it\);
their sum is \(A_i\). At a missing first digit, the free contribution
for \(G_F^0(1-t)\) is \(1-u_i-(1-2u_i)t\); adding \(u_it\) gives
\(C_i\). This is a subset expansion, not differentiation of those
free-coordinate factors.

Define \(D(t)=\prod_iA_i(t)-\prod_iC_i(t)\). Direct differentiation
gives the exact identity

\[
 \begin{aligned}
 -D'(t)-J(t)
 ={}&\sum_i(1-3u_i)
       \left(\prod_{j\ne i}A_j(t)-\prod_{j\ne i}C_j(t)\right)\\
 &+\sum_{i\in R}u_i\prod_{j\ne i}C_j(t)\ \ge0.
 \end{aligned}\tag{PW7}
\]

For \(0\le t\le1\), \(A_i\ge C_i\ge0\), and oddness gives
\(1-3u_i\ge0\). Also

\[
 D(0)=1-\prod_{i\in R}(1-u_i)=1-P_0,\qquad D(1)=0,
\]

since \(A_i(1)=C_i(1)=2u_i\). Integrating PW7 proves

\[
 \sum_{d\in D}\frac{W_d}{d}
 \le\sum_{F\ne\varnothing}q_F
 \le D(0)-D(1)=1-P_0,
\]

as claimed. This proof uses neither coverage, irredundancy, divisor
closure of \(D\), nor comparable-class disjointness.

The extra singleton subsets in PW5 are only formal nonnegative terms.
They use the nonzero-root convention of the composite coefficient
formula; they are not the contributions of the actual prime classes
\(A_p=0\bmod p\). No change of the actual prime events is asserted.

## 4. Exact finite checks and the coarser bound

Direct rational polynomial multiplication in PW3 and PW5 gives the
following sums. The prefix column includes every nonunit divisor of
\(Q\) using the formal coefficients just defined; the composite column
omits the prime labels. These are coefficient calculations, not
claimed residue realizations.

| \(Q\) | Composite prefixes | All nonempty prefixes | All nonempty digit subsets | \(1-P_0\) |
|---|---:|---:|---:|---:|
| \(3\cdot5\cdot7\) | \(1/105\) | \(11/105\) | \(11/105\) | \(19/35\) |
| \(3^2\cdot5\cdot7\) | \(2/135\) | \(5/54\) | \(11/70\) | \(19/35\) |
| \(3^3\cdot5^2\cdot7\) | \(1453/141750\) | \(9169/141750\) | \(226/1125\) | \(19/35\) |
| \(3^2\cdot5^2\cdot7\cdot11\) | \(2311/173250\) | \(21562/259875\) | \(42397/259875\) | \(45/77\) |

For the first row, each semiprime has one free digit. Its \(U\) term
has coefficient \(1/p\) at disagreement count one, so each of the
three semiprimes contributes \(1/(3\cdot105)\). The full-support
composite contributes zero, giving \(1/105\) directly. The finite
checks agree with the all-height proof; they do not replace it.

Because \(r_d+j\le L\), PW3 also implies

\[
 W_d\ge\frac{c_d}{\binom L{r_d}},\qquad
 \sum_{d\text{ composite}}\frac{c_d}{d\binom L{\Omega(d)}}\le1-P_0.
\]

The coefficient comparison is in this direction. This weaker profile
bound is consequently automatic too. Under comparable-class
disjointness, the Chudak--Griggs antichain inequality already cited in
[340](../321-384/340-whole-cover-completion-constrains-original-prefix-loads.md#established-branching-and-antichain-results)
gives the stronger weight
\(\prod_p\binom{H_p}{v_p(d)}/\binom L{\Omega(d)}\): apply it to
the numerical labels active at each point and integrate on \(U\).

## 5. Retaining prime terms or integrating on the whole carrier

Keeping the actual prime-label terms dropped in PW2 does not evade
the domination. Put

\[
 a_i(t)=1-(1-u_i)t,\qquad
 b_i(t)=a_i(t)-\mathbf1_{i\in R}u_i(1-t).
\]

For a first digit \(i\in R\), the actual prime class lies entirely
in \(U\). Its contribution is \(u_i\int_0^1\prod_{j\ne i}a_j(t)\,dt\),
whereas the formal singleton contribution in PW5 subtracts the
integral of \(\prod_{j\ne i}b_j\). Replacing all first-digit
singletons by their actual prime contributions therefore adds

\[
 \sum_{i\in R}u_i\int_0^1\prod_{j\ne i}b_j(t)\,dt.
\]

But \(C_j=b_j+u_jt\ge b_j\ge0\), so the last sum is at most the
integral of PW7's second nonnegative term. The same derivative budget
therefore bounds the enlarged sum, with actual prime contributions,
by \(1-P_0\) as well. This comparison again only concerns the stated
numerical coefficients, not an asserted realization of all subsets.

The integration of PW1 on the entire carrier is also automatic at
the profile level. Omitting \(G_F^0\), the all-subset sum is

\[
 \int_0^1\sum_i u_i\prod_{j\ne i}A_j(t)\,dt
 \le-\int_0^1\left(\prod_iA_i(t)\right)'dt
 =1-\prod_i2u_i<1,
\]

because \(u_i\le1-2u_i\). Thus neither retaining prime labels nor
removing the localization supplies a numerical-profile exclusion.

## 6. Prime-free and pure-power-survivor integrations are automatic

Let \(Z=U^c\) and \(\mu_Z=H(\cdot\mid Z)\). For each composite label
choose any reference point \(w_d\in A_d\cap Z\); privacy is unnecessary
for the bounds below. Write \(\Delta_d(x)\) as in PW1. Under \(\mu_Z\),
the first \(p\)-digit has \(p-1\) values and higher digits have \(p\), so

\[
 \widehat u_{(p,1)}=\frac1{p-1},\qquad
 \widehat u_{(p,j)}=\frac1p\ (j>1),\qquad
 \widehat G_d(z)=\prod_{i\notin F_d}[\widehat u_i+(1-\widehat u_i)z],
 \qquad V_d=\sum_{j\ge0}\frac{[z^j]\widehat G_d(z)}
                                      {\binom{r_d+j}{r_d}}.
\]

The fixed first digits are nonzero, and \(\mu_Z(A_d)=1/\varphi(d)\).
Thus the exact integrated expression is

\[
 \mathbb E_{\mu_Z}\sum_{d\text{ composite}}
 \frac{\mathbf1_{A_d}(x)}{\binom{r_d+|\Delta_d(x)|}{r_d}}
 =\sum_d\frac{V_d}{\varphi(d)}<\frac58.\tag{PW8}
\]

To prove the strict bound, for every nonempty digit subset \(F\) define
\(\widehat q_F\) by the same coefficient formula, multiplied by
\(\prod_{i\in F}\widehat u_i\). An actual prefix gives
\(\widehat q_{F_d}=V_d/\varphi(d)\). For \(r=|F|\), the beta integral is

\[
 \widehat q_F=r\int_0^1t^{r-1}
    \prod_{i\in F}\widehat u_i
    \prod_{i\notin F}[1-(1-\widehat u_i)t]\,dt.\tag{PW9}
\]

Each term is nonnegative and coordinatewise nondecreasing in the
parameters. Distinct composite labels have distinct prefix supports of
size at least two. Enlarge to all subsets of size at least two. There is
at most one parameter above \(1/3\), namely the first \(3\)-digit with
value \(1/2\). Raising the parameters to
\((1/2,1/3,\ldots,1/3)\), with \(k=L-1\) latter coordinates, can only
increase the sum. Put the first \(3\)-digit first when present; otherwise
any coordinate can be distinguished. A carrier with no digits has no
composite terms.

Put \(a=1-t/3\), \(b=1-2t/3\). For \(k\ge1\), subtracting singleton
terms from the all-subset beta expansion gives

\[
 T_k=\int_0^1\left[
 \frac{a^k-b^k}{2}
 +\frac k3\bigl(a^{k-1}-(1-t/2)b^{k-1}\bigr)\right]dt
 =\frac12+\frac9{8(k+1)}
 -\frac{k+2}{k+1}\left(\frac23\right)^k
 +\frac{2k+3}{8(k+1)}3^{-k}.\tag{PW10}
\]

The final formula also gives \(T_0=0\). Exactly,

\[
 8(k+1)3^k(5/8-T_k)
 =8(k+2)2^k-(8-k)3^k-(2k+3)>0.\tag{PW11}
\]

For \(k\ge8\) positivity is immediate; for \(k=0,\ldots,7\) the
right side is respectively \(5,22,67,176,433,1050,2623,7012\).
This proves PW8 for every distinct composite odd divisor palette,
without any residue realization or private-point assumption on the
numerical coefficients. The added nonprefix supports are only a
nonnegative envelope, not an asserted simultaneous family of classes.

Let \(D_{\rm orig}\) denote all original nonunit modulus labels, including
the prime labels. Take exactly the complement of their pure-power classes,
\(S=\bigcap_{p,a:\,p^a\in D_{\rm orig}}A_{p^a}^c\), and put \(X=H(S)\).
This is a product over prime coordinates; no additional conditioning
is included.
Under the original distinct-label assumptions, a coordinate's removed
mass is at most \(\sum_{a\ge1}p^{-a}=1/(p-1)\). Independence of prime
coordinates gives \(X>0\); together with \(S\subseteq Z\), it gives

\[
 \frac{P_0}{X}\le\prod_{p\in\Lambda}
   \frac{(p-1)^2}{p(p-2)}\le\frac{128}{81}.\tag{PW12}
\]

For an elementary rational bound, include all odd-integer factors
\(1+a_j\), where \(a_j=(4j^2-1)^{-1}\). The first two factors multiply
to \(64/45\); telescoping gives \(\sum_{j\ge3}a_j=1/10\). Every finite
tail product is at most \((1-\sum a_j)^{-1}\le10/9\), using
\(1+a_j\le(1-a_j)^{-1}\) and
\(\prod(1-a_j)\ge1-\sum a_j\). This proves PW12.

Take any reference points \(w_d\in A_d\cap S\) for the original mixed
labels, which involve at least two distinct primes. Labels with empty
intersection can be omitted; they contribute zero. Every pure-power
label has empty intersection with \(S\). Nonnegativity, PW8, and PW12 yield

\[
 \mathbb E_{H(\cdot\mid S)}\sum_{d\text{ mixed}}
 \frac{\mathbf1_{A_d}(x)}{\binom{r_d+|\Delta_d(x)|}{r_d}}
 \le\frac{P_0}{X}\sum_{d\text{ mixed}}\frac{V_d}{\varphi(d)}
 <\frac{128}{81}\frac58=\frac{80}{81}<1.\tag{PW13}
\]

The actual \(S\)-integral can still depend on the residues. For an exact
finite check, take \(Q=3^2 5^2\) and the pure classes \(0\bmod3\),
\(1\bmod9\), \(0\bmod5\), \(1\bmod25\). Then \(|Z|=120\) and \(|S|=95\).
With one mixed class \(2\bmod15\) and reference \(w_{15}=2\), its
integrals on \(Z,S\) are \(13/360,13/285\); the conditioning comparison
in PW13 is equality. Changing that class to \(1\bmod15\) and taking
\(w_{15}=16\) leaves its \(Z\)-integral \(13/360\), while its
\(S\)-integral is \(17/570<13/285\). These numbers follow by summing
the displayed integrand over the 225 literal residues. They confirm
the stated domination without identifying the two conditional laws.

Both integrations of PW1 therefore obey its upper bound automatically,
including the actual pure-power-survivor integration with all original
digits retained. These bounds do not concern arbitrary weights, other
localizations, or joint constraints retaining the private witnesses.

## 7. What remains usable

PW1 still constrains an actual joint incidence pattern together with
its private witnesses. The obstruction covers the original-Haar
coefficients PW3, the prime-free coefficients PW8, and the actual
pure-power-survivor integration PW13 with the same original-digit
integrand. None supplies a profile exclusion through its stated upper
bound. The survivor argument retains the literal pure-power exclusions;
it does not replace their conditional digit law by a product law.

A useful further application would have to retain additional joint
information, change the localization or weights with a proved bound,
or use whole-cover exchange properties absent from the numerical
coefficient calculation. No unweighted upper on the original composite
budget, new excluded palette, or unrestricted covering contradiction
follows from PW2.
