# Divisibility in Harvey P. Dale's A014865 recurrence

## Source statement and scope

OEIS A014865, revision 18, lists N. J. A. Sloane and Olivier Gerard as the entry authors and attributes its conjectural clauses to Harvey P. Dale. The entry defines the integer sequence by
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

**Proof.** At $n=1$ the two sides are $196$ and $15^2-14-15=196$. If the identity holds at $n$, then
$$
\begin{aligned}
196s(n+1)
 &=196\bigl(15s(n)+n+1\bigr)\\
 &=15\bigl(15^{\,n+1}-14n-15\bigr)+196(n+1)\\
 &=15^{\,n+2}-14(n+1)-15.
\end{aligned}
$$
Induction proves the formula. ∎

**Corollary 2.** If $n\in T$, let $q$ be the integer such that $s(n)=nq$. Then
$$
15(15^n-1)=14n(1+14q),
$$
and consequently
$$
n\mid 15(15^n-1).
$$

**Proof.** Lemma 1 gives
$$
15^{\,n+1}-14n-15=196nq,
$$
which rearranges to the displayed identity. The factor $14n$ then gives the divisibility. ∎

For a nonzero integer $x$, let $v_2(x)$ denote the exponent of $2$ in its prime factorization.

## The three clauses

**Theorem 3 (oddness).** Every $n\in T$ is odd.

**Proof.** Suppose that $n\in T$ is even. Since $T\subset\mathbb Z_{>0}$, $n$ is a positive even integer; write $s(n)=nq$ and $n=2^a u$ with $a\ge1$ and $u$ positive and odd. Corollary 2 gives
$$
15(15^n-1)=14n(1+14q).
$$
For the valuation calculation used here, factor
$$
15^u-1=(15-1)(1+15+\cdots+15^{u-1}).
$$
The second factor is a sum of an odd number of odd terms, so $v_2(15^u-1)=1$. Also $15^u\equiv15\pmod {32}$, hence
$$
15^u+1\equiv15+1=16\pmod {32}
$$
and $v_2(15^{2u}-1)=1+4=5$. For every subsequent step $k\ge1$, one has $15^{2^ku}\equiv1\pmod 8$, so
$$
\begin{aligned}
v_2(15^{2^{k+1}u}-1)
 &=v_2(15^{2^ku}-1)+v_2(15^{2^ku}+1)\\
 &=v_2(15^{2^ku}-1)+1.
\end{aligned}
$$
After $a$ doublings this yields
$$
v_2(15^n-1)=1+4+(a-1)=a+4=v_2(n)+4.
$$
This is the $p=2$ valuation identity in Parvardi's cited lifting-the-exponent result, specialized to $15^n-1$; the calculation above supplies the specialization in the present proof. Since $1+14q$ is odd, the right-hand side of Corollary 2 has valuation $1+v_2(n)$, whereas its left-hand side has valuation $v_2(n)+4$ because $15$ is odd. These valuations cannot be equal. Hence no even $n$ belongs to $T$. ∎

**Theorem 4 (compositeness above $7$).** If $n\in T$ and $n>7$, then $n$ is composite.

**Proof.** By Theorem 3, $n$ is odd. If $n$ were prime, then $n>7$ implies $\gcd(n,15)=1$. Corollary 2 therefore gives
$$
15^n\equiv1\pmod n.
$$
Fermat's theorem also gives $15^{n-1}\equiv1\pmod n$. Multiplying the latter congruence by $15$ and comparing with the former yields $15\equiv1\pmod n$, so $n\mid14$. This is impossible for a prime $n>7$. Thus $n$ is composite. ∎

**Theorem 5 (the $3$-$5$-$7$ alternative).** If $n\in T$ and $n>1$, then
$$
3\mid n\quad\text{or}\quad5\mid n\quad\text{or}\quad7\mid n.
$$

**Proof.** If $3\mid n$ or $5\mid n$, the conclusion already holds, so assume $3\nmid n$ and $5\nmid n$. Theorem 3 makes $n$ odd, hence $\gcd(n,15)=1$. Corollary 2 then permits cancellation of $15$ and gives
$$
n\mid15^n-1.
$$
Let $p$ be the least prime divisor of $n$, which exists because $n>1$. The order mechanism used here is the one in the lower-bound part of the repository theorem `firoozbakht_a092028`: in that source the base is an integer $N>2$, a prime divisor supplies a finite-field multiplicative order, and that order divides both an exponent and the prime minus one. In the present specialization the base is $15$, the exponent is $n$, and the prime is $p$; the following argument supplies the complete specialization.

Since $p\nmid15$, Fermat's theorem gives $15^{p-1}\equiv1\pmod p$, so let $d$ be the least positive integer with $15^d\equiv1\pmod p$. From $p\mid15^n-1$ and the division algorithm, the minimality of $d$ gives $d\mid n$; the same division argument applied to Fermat's congruence gives $d\mid p-1$. Thus
$$
d\mid\gcd(n,p-1).
$$
If a prime $r$ divided this gcd, then $r\mid n$ and $r\mid p-1$, so $r<p$, contradicting the choice of $p$ as the least prime divisor of $n$. Therefore $\gcd(n,p-1)=1$, hence $d=1$. Consequently $p\mid15-1=14$. The prime $p$ is odd and is neither $3$ nor $5$, so $p=7$. In particular $7\mid n$, and the inclusive disjunction follows. ∎

**Corollary 6 (A014865).** For every positive integer $n$ satisfying
$$
n\mid s(n),
$$
all three conclusions hold:

* $n$ is odd;
* if $n>7$, then $n$ is composite;
* if $n>1$, then $3\mid n$ or $5\mid n$ or $7\mid n$.

These conclusions cover every positive qualifying index and make no claim about indices outside $T$.

## Citations

1. N. J. A. Sloane and Olivier Gerard, entry authors for OEIS A014865, revision 18 (2021-07-03), with the conjectural clauses attributed there to Harvey P. Dale, <https://oeis.org/A014865> and <https://oeis.org/A014865/internal>. The entry supplies the recurrence, the definition of $T$, and the three clauses proved here.
2. Repository source: D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean, https://raw.githubusercontent.com/the-omega-institute/trureturing/e429c138785ec7abe5af8851acf67014b17af7e4/D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean, theorem `firoozbakht_a092028`, with its Blueprint Scribe Blueprint/D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.md. The theorem's lower-bound proof supplies the finite-field multiplicative-order mechanism consumed in Theorem 5; its public least-exponent conclusion is not used as a substitute for the displayed specialization.
3. Amir Hossein Parvardi, *Lifting The Exponent Lemma*, version 6 (2011-04-07), <https://s3.amazonaws.com/aops-cdn.artofproblemsolving.com/resources/articles/lifting-the-exponent.pdf>. The $p=2$ valuation identity is specialized and proved inside Theorem 3.

## 追加锚（本行以下为增补区）
