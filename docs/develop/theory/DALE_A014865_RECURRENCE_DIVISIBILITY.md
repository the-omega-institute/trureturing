# Divisibility in Harvey P. Dale's A014865 recurrence

## Source statement and scope

Harvey P. Dale's OEIS entry A014865, revision 18, defines the integer sequence by
$$
s(1)=1,\qquad s(j)=15s(j-1)+j\quad(j\ge 2),
$$
and defines its qualifying indices by
$$
T=\{n\in\mathbb Z_{>0}:n\mid s(n)\}.
$$
The entry records the following three conjectural clauses:

1. every member of $T$ is odd;
2. every member of $T$ greater than $7$ is composite;
3. every member of $T$ greater than $1$ is divisible by $3$ or by $5$ or by $7$, with the disjunction inclusive.

The statements below prove all three clauses for every positive qualifying index. The recurrence coefficient $15$, the initial value, and the thresholds $7$ and $1$ are exactly those in the source.

## Closed form

**Lemma 1.** For every integer $n\ge 1$,
$$
196s(n)=15^{\,n+1}-14n-15.
$$

**Proof.** At $n=1$ the two sides are $196$ and
$15^2-14-15=196$. If the identity holds at $n$, then
\[
\begin{aligned}
196s(n+1)
 &=196\bigl(15s(n)+n+1\bigr)\\
 &=15\bigl(15^{\,n+1}-14n-15\bigr)+196(n+1)\\
 &=15^{\,n+2}-14(n+1)-15.
\end{aligned}
\]
Induction proves the formula. ∎

**Corollary 2.** If $n\in T$, then
$$
n\mid 15(15^n-1).
$$

**Proof.** Write $s(n)=nq$ for an integer $q$. Lemma 1 gives
\[
15^{\,n+1}-14n-15=196nq,
\]
hence
\[
15(15^n-1)=14n(1+14q).
\]
The displayed equality implies the claimed divisibility. ∎

## The even-index obstruction

For a nonzero integer $x$, let $v_2(x)$ denote the exponent of $2$ in its prime factorization.

**Lemma 3.** If $n$ is even, then
$$
v_2(15^n-1)=v_2(n)+4.
$$

**Proof.** Write $n=2^a u$ with $a\ge1$ and $u$ odd. Since
\[
15^u-1=(15-1)(1+15+\cdots+15^{u-1}),
\]
and the second factor is a sum of an odd number of odd terms, we have
$v_2(15^u-1)=1$. The first squaring step has
\[
15^u+1\equiv 15+1=16\pmod {32},
\]
because $u$ is odd and $15^u\equiv15\pmod {32}$; therefore
$v_2(15^{2u}-1)=1+4=5$. For every subsequent step, if
$k\ge1$, then $15^{2^ku}\equiv1\pmod 8$, so
\[
v_2(15^{2^{k+1}u}-1)
=v_2(15^{2^ku}-1)+v_2(15^{2^ku}+1)
=v_2(15^{2^ku}-1)+1.
\]
After $a$ doublings the value is $1+4+(a-1)=a+4=v_2(n)+4$. ∎

**Theorem 4 (oddness).** Every $n\in T$ is odd.

**Proof.** Suppose that $n\in T$ is even and write $s(n)=nq$. Corollary 2 gives the exact identity
\[
15(15^n-1)=14n(1+14q).
\]
The factor $1+14q$ is odd, so the right-hand side has 2-adic valuation
$1+v_2(n)$. The left-hand side has valuation
$v_2(15^n-1)=v_2(n)+4$ by Lemma 3, since $15$ is odd. These valuations cannot be equal. Hence no even $n$ belongs to $T$. ∎

## Least-prime-factor order lemma

**Lemma 5.** Let $n>1$ be odd, let $3\nmid n$ and $5\nmid n$, and suppose
$$
n\mid 15^n-1.
$$
If $p$ is the least prime divisor of $n$, then $p=7$.

**Proof.** Since $p\nmid15$, let $d$ be the least positive integer such that
$15^d\equiv1\pmod p$. From $p\mid15^n-1$ and the division algorithm, the minimality of $d$ gives $d\mid n$. Fermat's theorem also gives
$15^{p-1}\equiv1\pmod p$, and the same division argument gives $d\mid p-1$. Thus
\[
d\mid\gcd(n,p-1).
\]
If a prime $r$ divided this gcd, then $r\mid n$ and $r\mid p-1$, so
$r<p$, contradicting the choice of $p$ as the least prime divisor of $n$.
Therefore $\gcd(n,p-1)=1$, hence $d=1$. Consequently
$p\mid15-1=14$. The prime $p$ is odd and is neither $3$ nor $5$, so
$p=7$. ∎

The order argument in Lemma 5 is the elementary instance needed here of the
repository's kernel-verified result
D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean,
theorem firoozbakht_a092028. That result proves, for every $N>2$, that the
least $m>1$ satisfying $m\mid N^m-1$ is the least prime factor of $N-1$;
its lower-bound proof uses the same fact that a multiplicative order divides
both an exponent and the cardinality-minus-one of the finite field. The
present proof applies that credited mechanism directly to the base $15$ and
to the least prime divisor of the qualifying index, while supplying the
recurrence-specific inference from Lemma 1.

## The three clauses

**Theorem 6 (compositeness above $7$).** If $n\in T$ and $n>7$, then $n$ is composite.

**Proof.** By Theorem 4, $n$ is odd. If $n$ were prime, then $n>7$ implies
$\gcd(n,15)=1$. Corollary 2 therefore gives
\[
15^n\equiv1\pmod n.
\]
Fermat's theorem also gives $15^{n-1}\equiv1\pmod n$. Multiplying the latter
congruence by $15$ and comparing with the former yields
$15\equiv1\pmod n$, so $n\mid14$. This is impossible for a prime $n>7$.
Thus $n$ is composite. ∎

**Theorem 7 (the $3$-$5$-$7$ alternative).** If $n\in T$ and $n>1$, then
$$
3\mid n\quad\text{or}\quad5\mid n\quad\text{or}\quad7\mid n.
$$

**Proof.** Assume $3\nmid n$ and $5\nmid n$. Theorem 4 makes $n$ odd, so
$\gcd(n,15)=1$. Corollary 2 then permits cancellation of $15$ and gives
$n\mid15^n-1$. Lemma 5 applies and shows that the least prime divisor of
$n$ is $7$. In particular $7\mid n$. Therefore at least one of the three
displayed divisibilities holds. ∎

**Corollary 8 (A014865).** For every positive integer $n$ satisfying
$n\mid s(n)$:

* $n$ is odd;
* if $n>7$, then $n$ is composite;
* if $n>1$, then $3\mid n$ or $5\mid n$ or $7\mid n$.

These conclusions cover every positive qualifying index and make no claim
about indices outside $T$.

## Citations

1. Harvey P. Dale, OEIS A014865, revision 18 (2021-07-03),
   <https://oeis.org/A014865> and <https://oeis.org/A014865/internal>.
   The entry supplies the recurrence, the definition of $T$, and the three
   clauses proved here.
2. Repository source:
   D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean,
   https://raw.githubusercontent.com/the-omega-institute/trureturing/e429c138785ec7abe5af8851acf67014b17af7e4/D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean,
   theorem firoozbakht_a092028, with its Blueprint Scribe
   Blueprint/D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.md.
   This is the credited finite-field multiplicative-order connection used in
   Lemma 5.
3. Amir Hossein Parvardi, *Lifting The Exponent Lemma*, version 6
   (2011-04-07), <https://s3.amazonaws.com/aops-cdn.artofproblemsolving.com/resources/articles/lifting-the-exponent.pdf>.
   Lemma 3 is proved here directly; the citation records the standard
   2-adic valuation identity it specializes.

## 追加锚（本行以下为增补区）
