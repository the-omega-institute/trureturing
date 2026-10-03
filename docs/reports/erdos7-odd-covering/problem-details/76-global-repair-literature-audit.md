# Global repair literature audit and the exact remaining interface

The unrestricted target is the negative assertion in the problem file: every
finite family of distinct odd moduli greater than one, with arbitrary fixed
residue classes, leaves an uncovered integer.  The audit below reuses the
checked published results and separates their actual conclusions from the
stronger exchange statement still needed by the project.  It does not claim a
resolution of the conjecture.

## 1. The missing conclusion is a phase-preserving strict repair

Write a hypothetical whole cover as

\[
\mathcal C=\{A_d=a_d+d\mathbb Z:d\in D\},
\qquad K=|D|,
\qquad S=\sum_{d\in D}d.
\]

For a proposed deletion set \(T\subseteq D\), let \(L\) be a common period
of the old classes and all proposed replacement classes, and put

\[
U_T=(\mathbb Z/L\mathbb Z)\setminus
       \bigcup_{d\in D\setminus T}A_d.
\]

The required global step is the existence of a family \(\mathcal R\) such
that

\[
U_T\subseteq\bigcup_{B\in\mathcal R}B,
\tag{G1}
\]

while retained phases are unchanged, all numerical moduli remain distinct
odd nonunits, no new label collides with a retained label, and the original
source and phase-inheritance conditions are preserved.  The strict EB1
improvement is

\[
\bigl(|\mathcal R|,\sum_{B\in\mathcal R}\operatorname{mod}(B)\bigr)
 <_{\mathrm{lex}}
\bigl(|T|,\sum_{d\in T}d\bigr).
\tag{G2}
\]

Numerical necessary conditions, a covering assignment on a related divisor
palette, and (G1)--(G2) are different conclusions.  The checked sources below
provide the first two in useful forms, but no universal construction of the
third.

## 2. Simpson is directly reusable and gives a prime-tail constraint

Simpson, *Regular coverings of the integers by arithmetic progressions*, Acta
Arithmetica 45 (1985), Theorem 2, states that an irredundant cover with least
common multiple \(N\) satisfies, for every proper divisor \(E\mid N\),

\[
\#\{A_d:d\nmid E\}\ge 1+f(N/E),
\qquad
f(n)=\sum_{p^\alpha\parallel n}\alpha(p-1).
\tag{S}
\]

An EB1 representative is irredundant: a redundant class could be deleted and
would improve the first lexicographic objective.  Hence (S) applies to its
actual phases and labels without any normalization.  Taking
\(E=N/p\) when \(p^\alpha\parallel N\) gives

\[
\#\{d\in D:v_p(d)=\alpha\}\ge p.
\]

Distinct numerical labels give the opposite bound
\(\#\{d:v_p(d)=\alpha\}\le\tau(N/p^\alpha)\).  Therefore every such
prime power obeys

\[
\boxed{p\le\tau(N/p^\alpha).}
\tag{S'}
\]

This is a genuine reusable necessary condition and avoids importing the
different hypothesis that an EB1 least common multiple is a *primitive*
covering number.  Simpson's cut still does not specify a receiving family for
\(U_T\), so it does not imply (G1) or (G2).

## 3. McNew--Setty: safe interfaces and a false unrestricted import

McNew and Setty, *On the densities of covering numbers and abundant numbers*,
[arXiv:2507.23041v2](https://arxiv.org/abs/2507.23041), define
\(c(n)=1+r(n)/n\) and \(h(n)=\sigma(n)/n\), where \(r(n)\) is the maximum
number of residues covered by distinct divisor moduli of \(n\).  Their
Theorem 4.3 gives, for \((u,v)=1\),

\[
c(uv)\le c(u)h(v).
\tag{M1}
\]

For a whole cover with lcm \(N=uv\), (M1) can exclude a specified divisor
palette whenever an independently certified upper bound makes
\(\overline c(u)h(v)<2\).  It does not show that every hypothetical EB1 lcm
has such a factorization.

Their Lemma 4.9 is a real coverage-preserving normalization: under its
almost-covering hypotheses it replaces the \(\ell\)-divisor part while
retaining the previously covered union.  The replacement can change phases,
use different divisor labels, and has no class-count or modulus-sum decrease,
so it is not an EB1 repair.  For odd \(n\), the paper's prescribed
almost-covering factor is \(\ell=1\), which supplies no nontrivial odd
normalization.

The displayed unrestricted Theorem 4.11 cannot be imported as stated.  Its
bound is

\[
c(n)\le 1+\frac{\ell-1}{\ell}
 +\frac1\ell\sum_{\substack{d\mid b\\d>1}}
 \frac{B(\tau(\ell),\omega(d))}{d},
\qquad n=\ell b,\quad(\ell,b)=1,
\tag{M2}
\]

with \(B(r,j)=-\sum_{k=1}^j(-r)^kS_2(j,k)\).  The concrete choice
\(\ell=64\), \(b=15\), \(n=960\) violates the displayed conclusion:

\[
r(64)=63,\qquad \tau(64)=7,
\qquad B(7,1)=7,\qquad B(7,2)=-42,
\]

so the sum in (M2) is \(14/15\), and (M2) would give

\[
c(960)\le 1+\frac{63}{64}+\frac1{64}\frac{14}{15}
 =2-\frac1{960}<2.
\]

But the five distinct classes

\[
0\pmod 2,\quad 0\pmod3,\quad 1\pmod4,\quad
5\pmod6,\quad 7\pmod{12}
\]

cover all twelve residues modulo 12, and all five moduli divide 960.  Thus
\(r(960)=960\) and \(c(960)=2\).  Direct enumeration of the twelve residues
and exact rational arithmetic verify both sides.  The paper later installs a
guard in its computational definition that avoids this example; the guarded
claims and the odd \(\ell=1\) specialization are not refuted here.  The
unrestricted statement itself is unavailable as a proof input.

## 4. Other reusable results and their exact boundary

The following sources were checked against (G1)--(G2).

* Balister--Bollobás--Morris--Sahasrabudhe--Tiba,
  [arXiv:1904.04806](https://arxiv.org/abs/1904.04806), Theorem 2.3, gives a
  generalized frame in a minimal coordinate-hyperplane cover under a linear
  size hypothesis.  CRT and prime-adic coordinates preserve the actual phases,
  but a generalized frame is not a common-phase replacement family and gives
  no strict EB1 descent.
* Klein--Koukoulopoulos--Lemieux,
  [arXiv:2212.01299](https://arxiv.org/abs/2212.01299), bound the \(j\)-th
  smallest modulus of a minimal distinct cover.  Their translate construction
  changes phases and permits repeated numerical labels, so it cannot be used
  as (G1)--(G2).
* BBMST, *On the Erdős Covering Problem: the density of the uncovered set*,
  Inventiones Mathematicae 228 (2022), Theorem 3.1, gives the phase-sensitive
  sufficient condition
  \[
  \sum_i\min\left\{M_i^{(1)},
    \frac{M_i^{(2)}}{4\delta_i(1-\delta_i)}\right\}<1
  \Longrightarrow \text{positive uncovered density},
  \tag{D}
  \]
  in its stated range.  It retains the actual congruence system, but no
  checked result derives the strict joint-moment inequality from EB1.
* Lettl--Sun, *On covers of abelian groups by cosets*,
  [arXiv:math/0411144](https://arxiv.org/abs/math/0411144), gives index and
  cardinality bounds for essential cosets.  EB1 essentiality does not imply
  exact-two-owner points or reciprocal private hulls.
* The full-divisor-palette results of Adenwalla,
  [arXiv:2501.15170](https://arxiv.org/abs/2501.15170), and Jia--Li--Liu,
  [arXiv:2504.09579](https://arxiv.org/abs/2504.09579), concern prescribed
  overlap assignments on the complete divisor palette.  An EB1 label set need
  not be that palette, and these results do not preserve an incoming phased
  assignment under a repair.

Recent odd-cover constructions allowing repeated labels, including Bispels et
al., [arXiv:2507.16135](https://arxiv.org/abs/2507.16135), likewise do not meet
the distinct-label condition.

### Cremona--Koymans' extra prime-support term cancels under the natural lift

Cremona--Koymans, [arXiv:2601.03212](https://arxiv.org/abs/2601.03212), prove
for an irredundant lattice covering with index lcm \(N\) that, for every
proper divisor \(D\) of \(N\),

\[
 \#\{L:[\mathbb Z^2:L]\nmid D\}
 \ge 1+G(N)-G(D),
 \qquad
 G(n)=\sum_{p^a\parallel n}a(p-1)+\omega(n).
\tag{CK1}
\]

The \(\omega(n)\) term might appear to strengthen Simpson's divisor cut for a
congruence cover.  It does not under the phase-preserving lift relevant here.
Given a hypothetical source cover
\(a_i\pmod {m_i}\) with \(Q=\operatorname{lcm}(m_i)\), lift each class to

\[
 L_i=\{(x,y):x-a_i y\equiv0\pmod {m_i}\},
\]

and add, for each prime \(p\) dividing \(Q\), the boundary lattice
\(H_p=\{(x,y):y\equiv0\pmod p\}\).  The lifted family covers
\(\mathbb Z^2\): if \(y\) is not invertible modulo \(Q\), some \(H_p\) contains
\((x,y)\); otherwise \(xy^{-1}\pmod Q\) is covered by an original class.
The original private points \((x_i,1)\) preserve irredundancy.  Each \(H_p\)
also has a private point: the subfamily with \(p\nmid m_i\) cannot itself
cover, or every class whose modulus is divisible by \(p\) would be redundant;
choose \(u\) outside that subfamily modulo \(Q/p^{v_p(Q)}\), and use CRT with
\(x\equiv1\pmod p\), \(y\equiv0\pmod p\), and \(y\equiv1\) at the other
prime coordinates.

For a divisor \(D\mid Q\), let
\[
 k_D=\#\{i:m_i\nmid D\}.
\]
The added boundary lattices contribute exactly
\(\omega(Q)-\omega(D)\) to the left side of (CK1).  Since the same difference
appears in \(G(Q)-G(D)\), (CK1) reduces exactly to

\[
\boxed{k_D\ge1+\sum_{p^a\parallel Q}a(p-1)
             -\sum_{p^a\parallel D}a(p-1).}
\tag{CK2}
\]

Thus this natural source- and phase-preserving lattice lift supplies no new
prime-support surplus beyond the already available Simpson cut.  This is a
negative result about one proposed bridge, not a claim that all lattice
methods are exhausted; it leaves the phase-preserving strict repair (G1)--(G2)
open.

Mian--Siddique, [arXiv:2607.25628](https://arxiv.org/abs/2607.25628), provide
an independent Lean-kernel exclusion
`odd_covering_lcm_gt_10000`: every distinct odd cover has lcm greater than
`10000`. Their public implementation is
[`ibrahimmian36/centurion`](https://github.com/ibrahimmian36/centurion). This
is a reusable finite lower bound, not a new phase-preserving repair: it removes
only the range `lcm <= 10000` and leaves the unrestricted large-lcm liability
untouched. The present lane records the source without replaying its external
Lean build.

### The Esposito Zenodo claim does not close the gap

The primary record [Zenodo 18440762](https://zenodo.org/records/18440762),
DOI [10.5281/zenodo.18440762](https://doi.org/10.5281/zenodo.18440762),
contains a three-page `Paper_I.pdf` whose Theorem 1 claims unrestricted
nonexistence.  Its proof has two checkable problems.

First, the base theorem is not supplied by the cited artifact.  Paper I invokes
a “certified” obstruction in \(\mathbb Z/11025\mathbb Z\) and calls it Paper D,
but the Zenodo record [18438201](https://zenodo.org/records/18438201) labelled
“Finite--Radical Obstructions ...” attaches a file whose first page is instead
arXiv:2012.01677, *On the Critical Exponent for \(k\)-Primitive Sets* by Chan,
Duker Lichtman and Pomerance.  That PDF contains no covering-system LP or
11025 dual certificate.  Consequently Paper I's Theorem 2.1 has no inspected
primary proof or certificate.

Second, the advertised allocation lemma is conditional on exactly that missing
base deficit.  It considers \(U\times\mathbb Z/q\mathbb Z\) and partitions the
available divisor labels among the new fibres; it does not prove that an
arbitrary hypothetical ODCS contains a kernel with a deficit \(U\), nor that
the proposed kernel obstruction is valid for the full divisor palette.  The
closing sentence “by known reductions ... any ODCS admits a finite kernel” is
not a stated theorem with the required phase and label quantifiers.

The companion [Paper G, Zenodo 18439460](https://zenodo.org/records/18439460)
and [Paper H, Zenodo 18439562](https://zenodo.org/records/18439562) only claim
eventual bounded-radical non-liftability from a \(\beta_e<1\) dual field.  Their
displayed decay argument does not provide an all-scale base obstruction for
every finite exponent, and Paper H explicitly leaves infinite prime incidence
as an escape.  The general framework [Paper J, Zenodo
18445853](https://zenodo.org/records/18445853) likewise assumes an obstructed
configuration with \(\beta<1\); it does not derive that assumption from an
arbitrary ODCS.

Thus the Esposito deposit is useful as a precise formulation of the same
allocation idea, but it is not a verified proof of (G1)--(G2) or of the
unrestricted conjecture.  The missing object remains an inspected finite
obstruction together with a valid extension theorem that covers every allowed
phase-labelled modulus.

## 5. Exact next interface

The valid composition currently available is

\[
\text{EB1 whole cover}
\Longrightarrow (S),\ (S'),\ \text{and the checked finite/project bounds}
\]

plus conditional density or frame criteria. The missing theorem is still one
of the following:

1. derive a strict inequality in (D) for every EB1 candidate while retaining
   the same phases and all original labels; or
2. construct (G1)--(G2), including occupied-label and phase-inheritance
   constraints, from the existing private-hull or digit-contraction data.

At a fixed finite palette, the second route is an exact integer-feasibility
problem: lock retained classes, enforce one class per numerical modulus, keep
the original phases, cover every point of \(U_T\), and impose (G2).  A feasible
finite instance is useful evidence, but universal feasibility is the open
bridge.  The current project floors, including the 34547 modulus-sum floor and
the least-LCM digit-contraction obstruction, remain necessary conditions only.

No checked source in this audit proves unrestricted Erdős #7 or supplies its
required global repair.
