### FMR. Conditional rank-by-rank non-Wall witnesses in the fixed golden field

#### FMR.1 Statement

Let \(K=\mathbb Q(\sqrt5)\), \(\mathcal O_K=\mathbb Z[\phi]\),
\(\phi=(1+\sqrt5)/2\), and \(v=\phi^2\).  For \(p>5\) put
\(\chi_p=(5/p)\), \(N_p=p-\chi_p\),
\(q_p=F_{N_p}/p\pmod p\), and let \(\rho(p)\) be the first positive
Fibonacci zero rank.  Assume Masser's number-field abc conjecture for \(K\).
Then there is an \(\ell_0\) such that for every prime \(\ell\ge\ell_0\) there
is a rational prime \(p>5\) satisfying

\[
 q_p\ne0,\qquad \rho(p)=2\ell,\qquad
 \ell\mid p-\chi_p.
\]

The primes \(p\) selected for distinct \(\ell\) are distinct.  In
particular, under this hypothesis the fixed-golden WSS zero set misses at
least one prime in every sufficiently large even-rank channel \(2\ell\) with
\(\ell\) prime.  Moreover, for \(X\) sufficiently large,

\[
\#\{p\le X:p>5, q_p\ne0, \rho(p)/2\text{ is prime}\}
 \gg_{K,v} \frac{\log X}{\log\log X}.
\]

The Legendre sign determines the residue class: a split witness has
\(p\equiv1\pmod\ell\), while an inert witness has
\(p\equiv-1\pmod\ell\).  The theorem does not assert which sign occurs for a
specified \(\ell\), and is conditional on abc.

#### FMR.2 Input from Fellini--Murty

Fellini and Murty, *Wieferich primes in number fields and the conjectures of
Ankeny--Artin--Chowla and Mordell*, arXiv:2508.08472v2, Theorems 1.2 and 1.4,
Lemmas 5.4--5.6, prove the following under the same abc hypothesis.  For an
admissible base \(\alpha\in\mathcal O_K\), write
\(A_n=(\alpha^n-1)=U_nV_n\), with \(U_n\) square-free and \(V_n\)
powerful.  Then \(N(U_n)\to\infty\).  Their proof of Theorem 1.4 is stronger
than the final counting statement: after removing finitely many bad rational
indices, every prime index \(\ell\) has a prime ideal \(\mathfrak p\mid U_\ell\),
and distinct prime indices yield distinct prime ideals.  This is the passage
from their lines 543--548: the range of large rational primes \(\ell\) is
mapped to divisors of \(U_\ell\); Lemma 5.5 prevents reuse at coprime indices.
Lemma 5.6 says each such \(\mathfrak p\) is non-Wieferich for \(\alpha\), i.e.
\[
 \alpha^{N(\mathfrak p)-1}\not\equiv1\pmod{\mathfrak p^2}.
\]

Apply this with \(\alpha=v\).  Since \(v-1=\phi\) is a unit of norm \(-1\),
no prime ideal divides \(A_1\).  The only remaining exclusions are the finite
set of primes above 2 and 5 and the finitely many indices before
\(N(U_n)\) exceeds their square-free norm product.  Thus every sufficiently
large prime \(\ell\) has a divisor \(\mathfrak p\mid U_\ell\) above an odd
\(p\ne5\), and \(p\ne\ell\).  The last inequality also follows directly:
if \(p=\ell\), then \(v\equiv1\pmod{\mathfrak p}\) would force
\(\mathfrak p\mid(v-1)\), impossible.

For this \(\mathfrak p\), Lemma 5.4 gives
\[
 \operatorname{ord}_{\mathfrak p}(v\bmod\mathfrak p)=\ell.
\]
Indeed the only alternatives for a divisor of \(C_\ell(v)\) are
\(\ell=p^i f_v(\mathfrak p)\); \(p\ne\ell\) forces \(i=0\).

#### FMR.3 Split and inert contraction

For \(p>5\), the quadratic field is unramified.  If \(p\) splits, the
residue degree is one and \(N(\mathfrak p)=p\); the order \(\ell\) therefore
divides \(p-1\).  If \(p\) is inert, the residue degree is two,
\(N(\mathfrak p)=p^2\), and the norm-one subgroup of
\((\mathcal O_K/p\mathcal O_K)^\times\) has order \(p+1\).  Because
\(N_{K/\mathbb Q}(v)=1\), the order \(\ell\) divides \(p+1\).  In both
cases \(\ell\mid p-\chi_p\), and \(\operatorname{ord}(-v)=2\ell\), since
\(\ell\) is odd and \(-1\notin\langle v\rangle\).  The standard golden
identity \(\phi/\bar\phi=-v\) identifies this order with \(\rho(p)\).  Thus
\(\rho(p)=2\ell\), and the split/inert residue classes are as stated.

A rational prime cannot be selected for two different indices: conjugation
sends \(v\) to \(v^{-1}\), preserving its residue order, and an inert prime
has only one prime above it.  Hence two prime ideals of the construction
lying over the same rational \(p\) would have the same order \(\ell\).

#### FMR.4 The non-Wall translation

The fixed-golden lift gives (CG.1/SJC.6)
\[
 v^{N_p}-1\equiv p\,\chi_p q_p\sqrt5\pmod {p^2\mathcal O_K}.
\]
For a split prime, \(N(\mathfrak p)-1=p-1=N_p\), so Fellini--Murty's
non-Wieferich condition is equivalent to \(q_p\ne0\).  For an inert prime,
write \(v^{p+1}=1+pt\pmod{\mathfrak p^2}\).  Then
\[
 v^{p^2-1}=(1+pt)^{p-1}
 \equiv1+p(p-1)t\pmod{\mathfrak p^2},
\]
and \(p-1\) is a unit modulo \(p\).  Therefore
\(v^{p^2-1}\equiv1\pmod{\mathfrak p^2}\) if and only if
\(v^{p+1}\equiv1\pmod{\mathfrak p^2}\), again if and only if \(q_p=0\).
Thus every extracted \(\mathfrak p\) contracts to a rational non-WSS prime
with the asserted exact rank.

#### FMR.5 Counting and scope

For each prime \(\ell\) in the interval used by Fellini--Murty's proof, the
ideal \(U_\ell\) has norm at most \(N(v^\ell-1)\).  Their height estimate
bounds this norm by \(X\) whenever \(\ell\le c_v\log X\), for a fixed
\(c_v>0\).  Prime indices in this interval are
\(\gg\log X/\log\log X\), and the preceding distinctness argument makes
the contracted rational primes distinct.  This proves the stated count.

This is a fixed-golden specialization of the published number-field theorem,
not a claim that Fellini--Murty proved a rank-by-rank Fibonacci statement.  The
older Grell--Peng paper, arXiv:1511.01210, Theorem 3, also gives conditional
infinitude through square-free Fibonacci parts but does not state the exact
prime-rank channel or the split/inert contraction above.  No unconditional
WSS exclusion or WSS existence follows, and this result does not contradict
the possibility that the WSS zero set itself is empty.
