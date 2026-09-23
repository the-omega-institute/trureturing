# Two actual prime extensions preserve a common core law

A finite family with pairwise distinct odd numerical moduli greater than one cannot cover the integers if its total prime support consists of nine primes and its eighth smallest prime is at least 43. No original exponent or residue is restricted. More generally, for two distinguished support primes q,r outside a core of at most seven primes, with no other support primes, a sufficient condition is

\[
 q,r>23,\qquad (q-23)(r-23)>463.
 \tag{PE1}
\]

For a nine-prime core whose last two primes are at least 43 and 47, the actual core survivor set has Haar density at least 17/880267500. Arbitrarily many additional primes above 3000000000, with arbitrary finite heights and support interactions, can be added using the existing joint-moment tail theorem. These are restricted noncoverage results; the first nine odd primes do not satisfy (PE1), and unrestricted Erdős #7 remains unresolved.

The proof uses [report462](462-the-final-stage-ledger-gives-a-seven-core-common-law.md)'s one-law query bound and reuses the pure-coordinate conditioning and original-label counting of [Chapter05](../../problem-details/05-unrestricted-axis-deletions-a-complete-head-bound.md), together with the joint-moment tail transfer in [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md). The seven-core seed inherits the attributed source construction and comparisons in Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1. The [source entry](../../../../../Library/Arith/schroeder2026nine.md) records its identity and verification boundary. All new deductions here are ordinary mathematical proofs with exact arithmetic, not Lean certification or a claim of a new general conditioning method.

## A fixed product law and the original modulus labels

Let K be a finite old-core period, and let mu be one probability on its actual survivor set. Suppose, simultaneously for every choice of query phases,

\[
 R_K(\mu):=\sum_{1<d\mid K}\max_a\mu(a\bmod d)\le A,
 \qquad \mu\le\Lambda H_K.
 \tag{PE2}
\]

Take a finite set Q of new odd primes, disjoint from K. Every modulus in the head family being processed has prime support contained in the old core together with Q. All coordinate heights are fixed to resolve the complete original family and the queries being considered. For q in Q, let V_q avoid all original pure q-power classes. Numerical distinctness permits at most one such class at each exponent, so

\[
 H_q(V_q)\ge1-\sum_{e\ge1}q^{-e}
 =\frac{q-2}{q-1}>0.
\]

Use the normalized conditional probability

\[
 \rho_q=H_q(\mathord\cdot\mid V_q),\qquad
 \rho_q\le c_q H_q,\qquad c_q=\frac{q-1}{q-2}.
\]

A depth-e query cylinder therefore has rho_q mass at most c_q q^{-e}, and the sum of these bounds over e>=1 is b_q=1/(q-2). Form the single probability

\[
 \nu=\mu\otimes\bigotimes_{q\in Q}\rho_q.
 \tag{PE3}
\]

This law is determined from the original family before any query layout is selected. All its old-only and pure-new-prime forbidden classes already have zero mass.

Every remaining original modulus has a unique form

\[
 d\prod_{q\in E}q^{e_q},\qquad E\subseteq Q,\ E\ne\varnothing,
 \quad e_q\ge1,\quad d\mid K.
\]

Fix E and its complete exponent vector. Distinct numerical moduli give a partial old-core query layout: there is at most one class per d. The original CRT projections supply its phases. When |E|=1, the d=1 class is already excluded by V_q, so the total old-core query expectation is at most A. When |E|>=2, d=1 is a genuine multi-prime modulus and must remain; the bound is A+1. No radical replacement or branchwise reselection of a residue occurs.

Taking the union bound under the same nu, and then summing the exact geometric series, gives the total remaining forbidden mass at most

\[
 \begin{aligned}
 D(A,Q)
 &=A\sum_{q\in Q}b_q
  +(A+1)\sum_{\substack{E\subseteq Q\\|E|\ge2}}\prod_{q\in E}b_q\\
 &=(A+1)\left(\prod_{q\in Q}(1+b_q)-1\right)-\sum_{q\in Q}b_q.
 \end{aligned}
 \tag{PE4}
\]

Finite original inventories only decrease this upper bound. If D(A,Q)<1, restricting nu outside the one complete original forbidden union gives an actual live submeasure of mass at least 1-D(A,Q). Its density is at most Lambda times the product of the c_q.

There is also a common query bound after this same deletion. Before deletion, any full nonunit layout on the enlarged period has expectation at most

\[
 B(A,Q)=(A+1)\prod_{q\in Q}(1+b_q)-1.
\]

Indeed, at every fixed new exponent vector the old layout, including its unit term, has expectation at most A+1. Deletion decreases this nonnegative load. Normalizing once gives one law, for every query on the fixed enlarged period, satisfying

\[
 R_{K\prod q^{H_q}}(\widehat\nu)
 \le\frac{B(A,Q)}{1-D(A,Q)},\qquad
 \widehat\nu\le
 \frac{\Lambda\prod_{q\in Q}c_q}{1-D(A,Q)}H.
 \tag{PE5}
\]

Neither (PE4) nor (PE5) selects a different law for different queries. The construction may change the old marginal after deletion; no marginal-preservation assertion is needed.

## One-prime query extension

For Q={q}, assume q>A+2. Equations (PE4)–(PE5) become

\[
 D=\frac A{q-2},\qquad
 R_{Kq^{H_q}}(\widehat\nu)
 \le\frac{(q-1)A+1}{q-2-A},\qquad
 \widehat\nu\le\Lambda\frac{q-1}{q-2-A}H.
 \tag{PE6}
\]

Report462 supplies A=70874/3375<21 and Lambda=455625 on any seven actual odd core primes. For q>=101, the right side of (PE6) is at most its value at q=101, namely

\[
 \frac{7090775}{263251}<\frac{2101}{78}<27,
 \qquad
 \widehat\nu\le\Lambda_8 H,\qquad \Lambda_8<\frac{7593750}{13}.
 \tag{PE7}
\]

The rational bound decreases with q: its derivative is -(A^2+A+1)/(q-2-A)^2. It increases with A. Thus any eight-prime core containing a prime at least 101 has the displayed common-query bound, with arbitrary original phases and heights. This is one application of the same product construction; the two-prime argument below permits a smaller newly exposed prime by using the actual size of the other prime.

## The symmetric two-prime condition

For Q={q,r}, formula (PE4) is

\[
 D=\frac A{q-2}+\frac A{r-2}
   +\frac{A+1}{(q-2)(r-2)}.
 \tag{PE8}
\]

The last numerator is A+1 because a modulus q^e r^f can have old cofactor d=1. Dropping that term would omit legal original constraints.

Define

\[
 N_A(q,r)=(q-A-2)(r-A-2)-(A^2+A+1).
\]

Then

\[
 1-D=\frac{N_A(q,r)}{(q-2)(r-2)}.
 \tag{PE9}
\]

Whenever N_A(q,r)>0, the unnormalized live law and the actual survivor set U satisfy

\[
 \nu(U)\ge\frac{N_A(q,r)}{(q-2)(r-2)},\qquad
 H(U)\ge\frac{N_A(q,r)}{\Lambda(q-1)(r-1)}.
 \tag{PE10}
\]

The density domination used in the second inequality is applied before normalization. This is a direct two-coordinate product construction followed by one actual union deletion; it does not combine independently chosen favorable laws on q and r.

Take the conservative A=21 and Lambda=455625 from report462. Then N_A=(q-23)(r-23)-463. Some exact prime-pair boundaries are:

| q | r | N_21(q,r) |
| --- | --- | --- |
| 29 | 101 | 5 |
| 31 | 83 | 17 |
| 37 | 59 | 41 |
| 41 | 53 | 77 |
| 43 | 47 | 17 |

For the first four q values, the immediately preceding prime r gives a nonpositive bound. This limits this scalar criterion; it is not an arithmetic covering example. For q=43, 47 is already the least larger prime.

For q>=43 and r>=47, the Haar expression in (PE10) is minimized at (43,47). To check monotonicity directly, the derivative of

\[
 \frac{qr-23q-23r+66}{(q-1)(r-1)}
\]

with respect to q is (22r-43)/((q-1)^2(r-1))>0, and the other derivative is symmetric. Therefore every such actual nine-prime core satisfies

\[
 H(U)\ge h_9:=\frac{17}{880267500}.
 \tag{PE11}
\]

The intermediate distorted live mass at (43,47) is at least 17/1845. It is not identified with Haar density. Fewer than seven old primes can be padded with unused odd primes, followed by projection, as in report462.

## Adding an unrestricted large-prime tail

Resolve all original core exponents, including the core parts of classes touching outside primes. Take the actual core survivor set U and the new seed measure H restricted to U, without normalization; uniform lifting to these heights preserves its Haar mass. Equation (PE11) gives seed mass at least h_9 and joint Haar density at most one. This is an explicit change of seed: the tail argument uses this mass and density, not an unproved transfer of the old query bound to Haar restriction.

For the nine reference primes 3,5,7,11,13,17,19,43,47, the full Haar second-moment factor of Chapter33 is

\[
 M_2=\prod_p\frac{p(p+1)}{(p-1)^2}
 =\frac{1026827659}{43877376}.
 \tag{PE12}
\]

Each factor decreases with p. Thus (PE12) bounds the factor for any seven old odd primes together with q>=43 and r>=47.

Use Chapter33's arbitrary correlated-head transfer, equations (SH8)–(SH13), with

\[
 B=3000000000,\qquad \ell=19,\qquad
 c_\ell=\frac{723}{721},\qquad 3^{19}=1162261467\le B.
\]

Its all-prime tail allowance is

\[
 \tau_7(B,\ell)=
 \frac{c_\ell^7}{B}\left(\frac B{B-3}\right)^2
 \sum_{j=0}^7\frac{7!}{(7-j)!\ell^j}.
\]

The exact consumer verifies

\[
 h_9-M_2\tau_7(3000000000,19)>\frac1{200000000}>0.
 \tag{PE13}
\]

Consequently any finite set of outside primes above B and disjoint from the core may occur, with unrestricted finite original heights and any number of outside primes in a modulus. The original classes are assigned once by their last exposed outside prime. The existing normalized kernels and final global deletion produce one live law avoiding the full original family. Its positive mass gives an avoiding point on the complete finite CRT carrier, hence an uncovered integer.

The margin in (PE13) is mass in the distorted tail law, not a Haar-density bound of that size. The analytic prime-product premise and its local verification status are inherited unchanged from Chapter33 and its cited Chapter32/source argument. The artificial exposure order is core first, then increasing outside primes; the core itself need not lie below B.

## Verification and remaining scope

The [exact consumer](../../frontier/cover-geometry/pure_prime_extensions.py) reads the pinned [seven-core seed summary](../../frontier/cover-geometry/seven_core_last_stage_bridge.json), computes the extension constants and the rational tail margin, and writes [the result data](../../frontier/cover-geometry/pure_prime_extensions.json). Its small original-modulus control retains the d=1 multi-prime classes. It neither regenerates source geometry nor certifies the inherited analytic or arbitrary-height premises.

Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_prime_extensions.py \
  --seed docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven_core_last_stage_bridge.json
```

The query bounds concern each fixed finite period and one law for all its phase layouts. No projectively compatible sequence of separately chosen laws is asserted. The product budget (PE4) is a sufficient condition, and need not remain below one as more primes are added. The large-prime tail argument supplies a separate continuation mechanism under its cutoff. Neither argument proves the missing small-prime core cases or supplies a uniform induction through all prime supports.
