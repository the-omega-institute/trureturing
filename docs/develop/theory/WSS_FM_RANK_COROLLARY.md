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

All such witnesses are split and satisfy \(p\equiv1\pmod{2\ell}\), as proved below; the theorem is conditional on abc.

#### FMR.2 Input from Fellini--Murty

Under number-field abc, define U_n as the product of prime ideals occurring in alpha^n-1 with valuation exactly one, and let the remaining factor be powerful. Fellini--Murty's abc argument implies N(U_n) -> infinity: an infinite bounded-norm subsequence would bound the remaining factor and contradict norm growth of alpha^n-1. Their extraction proof supplies a non-Wieferich ideal for every sufficiently large prime index ell; distinct prime indices give distinct ideals.

Apply this with alpha=v. Since v-1=phi is a unit, the A_1 exception is empty. Remove primes above 2 and 5 and finitely many initial indices. Lemma 5.4 gives ord_pfrak(v)=ell; p=ell is impossible because it would force pfrak|(v-1).

#### FMR.3 Split contraction

For p>5, an inert p is impossible: Frobenius gives v^((p+1)/2)=phi^(p+1)=-1, so v cannot have odd order ell. Hence every extracted ideal lies over a split p, ell divides p-1, and p is congruent to 1 modulo 2ell. Since -v has order 2ell and phi/bar(phi)=-v, the Fibonacci rank is rho(p)=2ell. Distinct ell give distinct rational p.

#### FMR.4 The non-Wall translation

The fixed-golden lift gives v^(N_p)-1 = p chi_p q_p sqrt(5) modulo p^2 O_K. All extracted ideals are split, so N(pfrak)-1=p-1=N_p. Therefore Fellini--Murty's non-Wieferich condition is exactly q_p != 0, and each extracted ideal gives the asserted rational non-Wall witness.

#### FMR.5 Counting and scope

The exact absolute norm is |N(v^ell-1)|=v^ell+v^(-ell)-2 < v^ell. Thus ell <= (log X)/(log v)+O(1) ensures the selected p <= X. The prime number theorem then gives the stated lower bound. This is a fixed-golden specialization, conditional on abc, and does not solve WSS unconditionally.

This is a fixed-golden specialization of the published number-field theorem,
not a claim that Fellini--Murty proved a rank-by-rank Fibonacci statement.  The
older Grell--Peng paper, arXiv:1511.01210, Theorem 3, also gives conditional
infinitude through square-free Fibonacci parts but does not state the exact
prime-rank channel or the split/inert contraction above.  No unconditional
WSS exclusion or WSS existence follows, and this result does not contradict
the possibility that the WSS zero set itself is empty.
