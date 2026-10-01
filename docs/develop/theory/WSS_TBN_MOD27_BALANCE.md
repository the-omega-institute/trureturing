# A mod-27 depth balance in the split Lucas tower

## Scope and baseline

Let \(F_n\) and \(L_n\) be the ordinary Fibonacci and Lucas sequences,
\(L_0=2,L_1=1\). For \(j\ge 1\), put
\[
 n_j=3^j,\qquad r_j=3^{j+1},\qquad
 B_j=L_{2n_j}+1=L_{n_j}^{\,2}+3.
\]
The existing TBN.2--TBN.4 development in
\`Problems/wall-sun-sun-golden-unit-lift.md\` proves
\[
 B_{j+1}=B_j^3-3B_j^2+3,\quad B_1=19,
\]
and, for every prime \(p\mid B_j\),
\[
 p\equiv1\pmod{2r_j},\qquad
 v_p(B_j)=h_p,
\]
where \(h_p\) is the original Fibonacci depth
\(v_p(F_{p-(5/p)})\). Thus the exponents below are the actual WSS
depths; no index-multiplier valuation is being counted.

The rank/valuation input is the classical Fibonacci valuation formula
of Lengyel, as recorded in Medina--Rowland, *p-regularity of the
p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53
(2015), Theorem 1.4 (arXiv:0910.2907), together with the split rank
calculation already written as TBN.3. The new statement below is an
elementary 3-adic refinement of TBN.5, not a claim that the cited papers
state this balance.

## Theorem (M27)

Define
\[
 u_j=\frac{B_j-1}{2r_j},\qquad
 b_{p,j}=\frac{p-1}{2r_j}\quad(p\mid B_j).
\]
These are integers. Then
\[
 \boxed{u_j\equiv(-1)^{j+1}\pmod{27}\quad(j\ge1).}
 \tag{M27.1}
\]
For every \(j\ge2\), the actual depth vector in \(B_j\) satisfies
\[
 \boxed{\sum_{p\mid B_j} h_p\,b_{p,j}
       \equiv(-1)^{j+1}\pmod{27}.}
 \tag{M27.2}
\]
For \(j=1\), (M27.2) also holds by the direct identity \(B_1=19\).

In particular, the old mod-3 balance
\(\sum h_p(p-1)/r_j\equiv(-1)^j\pmod3\) is only the first
reduction of (M27.2). Since \(b_{p,j}\) is integral, (M27.2) forces at
least one factor with \(3\nmid h_p b_{p,j}\), but the new content is the
full mod-27 weighted congruence. It neither produces a WSS prime nor
excludes one.

## Proof

The recurrence gives
\[
 B_{j+1}-1=(B_j-1)\bigl((B_j-1)^2-3\bigr).
\]
Writing \(B_j-1=2r_j u_j\) and \(r_{j+1}=3r_j\), we obtain the exact
recurrence
\[
 u_{j+1}
 =u_j\left(-1+\frac{4r_j^2}{3}u_j^2\right)
 =u_j\left(-1+4\cdot3^{\,2j+1}u_j^2\right).
 \tag{M27.3}
\]
Here \(u_1=(19-1)/(18)=1\). The correction term in parentheses is
divisible by \(27\) for every \(j\ge1\). Induction in (M27.3) therefore
proves (M27.1).

Now fix \(j\ge2\). Every prime factor has the form
\(p=1+2r_j b_{p,j}\). Since
\[
 (2r_j)^2=4r_j^2
 \quad\text{is divisible by}\quad 54r_j
 \qquad (j\ge2),
\]
the binomial theorem gives
\[
 p^{h_p}\equiv1+2r_jh_pb_{p,j}\pmod{54r_j}.
\]
All cross terms in the product also contain \((2r_j)^2\), so multiplying
over the distinct prime factors yields
\[
 B_j=\prod_{p\mid B_j}p^{h_p}
 \equiv1+2r_j\sum_{p\mid B_j}h_pb_{p,j}\pmod{54r_j}.
\]
On the other hand, \(B_j=1+2r_ju_j\). Cancelling the common factor
\(2r_j\) in the congruence modulo \(54r_j\) gives
\[
 \sum_{p\mid B_j}h_pb_{p,j}\equiv u_j\pmod{27},
\]
which is (M27.2) by (M27.1). For \(j=1\), \(B_1=19\), \(b_{19,1}=1\),
and \(h_{19}=1\), so both sides are \(1\) modulo \(27\).

## Exact checks

The following factorizations and residue checks use only integer
arithmetic (the factorizations are displayed to make the depth exponents
auditable):
\[
\begin{array}{c|r|l|c|c}
j&r_j&B_j&u_j\bmod27&\sum h_pb_{p,j}\bmod27\\ \hline
1&9&19&1&1\\
2&27&5779=5779&26&26\\
3&81&192900153619=3079\cdot62650261&1&1\\
4&243&7177905237579946589743592924684179
 =59779\cdot120074026624398979403194983601&26&26
\end{array}
\]
All displayed factors are prime, and each is \(1\bmod 2r_j\). The
table checks both the recurrence residue and the depth-weighted product
for the first four blocks; it is not used in the proof.

## Logical boundary

M27 constrains the actual valuation vector in the split Lucas rank
channel. It sharpens TBN.5's mod-3 balance and can be combined with the
existing parity, reciprocity, and class-field constraints. It does not
imply that any \(h_p=1\), and therefore does not imply the existence of a
non-WSS prime or resolve the Wall--Sun--Sun question. The result is
unconditional relative to the TBN.2--TBN.3 rank/valuation identities; no
abc, Pell-height, equidistribution, or Chebotarev hypothesis is used.


## Theorem (M81 strengthening)

The same split Lucas tower carries one further unconditional 3-adic
constraint. Keep
\[
 m_j=2r_j=2\cdot 3^{j+1},\qquad
 u_j=\frac{B_j-1}{m_j},\qquad
 b_{p,j}=\frac{p-1}{m_j},
\]
and, for a fixed block, write
\[
 S_j=\sum_{p\mid B_j}h_p\,b_{p,j}.
\]
The integrality of \(u_j\) and \(b_{p,j}\), and the interpretation of \(h_p\)
as the original (not index-multiplied) Fibonacci depth, are exactly the
TBN.2--TBN.3 inputs used in M27.

Then
\[
 \boxed{u_j\equiv 26(-1)^j\pmod {81}\qquad(j\ge2).}
 \tag{M81.1}
\]
Moreover,
\[
 \boxed{S_j\equiv 26(-1)^j\pmod {81}\qquad(j\ge3),}
 \tag{M81.2}
\]
with the direct initial values \(S_1=1\) and \(S_2=26\). Since
\(26\equiv-1\pmod {27}\), reduction of (M81.2) recovers the M27 residue for
all \(j\ge3\); the new information is the lift from modulus \(27\) to
modulus \(81\).

### Proof

The exact identity already used in (M27.3) is
\[
 u_{j+1}=u_j\left(-1+4\cdot3^{\,2j+1}u_j^2\right),\qquad u_1=1.
 \tag{M81.3}
\]
A direct calculation gives \(B_2=5779\) and \(u_2=(5779-1)/54=107\), hence
\(u_2\equiv26\pmod {81}\). For every \(j\ge2\), the correction
\(4\cdot3^{2j+1}u_j^2\) is divisible by \(3^5=243\), and therefore
\[
 u_{j+1}\equiv-u_j\pmod {81}.
\]
Induction gives (M81.1), with residue \(26\) on even indices and \(55\) on
odd indices.

For \(j\ge3\), \(81\mid m_j\). Every prime factor has the form
\(p=1+m_jb_{p,j}\). The binomial theorem therefore gives
\[
 p^{h_p}\equiv1+m_jh_pb_{p,j}\pmod {81m_j},
\]
because every term of degree at least two contains \(m_j^2\), which is
divisible by \(81m_j\). Multiplying over the distinct prime factors of
\(B_j\), all cross terms have the same divisibility and
\[
 B_j=\prod_{p\mid B_j}p^{h_p}
 \equiv1+m_jS_j\pmod {81m_j}.
\]
Comparing with \(B_j=1+m_ju_j\) and cancelling \(m_j\) yields
\(S_j\equiv u_j\pmod {81}\), proving (M81.2).

The remaining bases are exact. \(B_1=19\) gives \(S_1=1\). Also
\(B_2=5779\) is prime (trial division through \(\sqrt{5779}<77\)), so its
single factor has \(h_{5779}=1\) and
\(b_{5779,2}=(5779-1)/54=107\), giving \(S_2=107\equiv26\pmod {81}\).

### Exact checks

These checks are independent integer arithmetic and are not used in the
proof. They also expose the first lifted residues:
\[
\begin{array}{c|r|r|l|c|c}
j&m_j&B_j&\text{factorization}&u_j\bmod81&S_j\bmod81\\ \hline
1&18&19&19&1&1\\
2&54&5779&5779&26&26\\
3&162&192900153619&3079\cdot62650261&55&55\\
4&486&7177905237579946589743592924684179&
59779\cdot120074026624398979403194983601&26&26
\end{array}
\]
The displayed factors are prime and each is \(1\bmod m_j\), as required by
TBN.3. The recurrence and the factorizations were checked with exact
integer arithmetic; no search bound or probabilistic primality assertion is
part of (M81.1)--(M81.2).

### Provenance, literature boundary, and formalization status

The rank and depth identities remain the classical Lengyel valuation input
(as recorded in Medina--Rowland, *p-regularity of the p-adic valuation of the
Fibonacci sequence*, Fibonacci Quarterly 53 (2015), Theorem 1.4,
[arXiv:0910.2907](https://arxiv.org/abs/0910.2907)) together with the
repository's TBN.2--TBN.3 split-rank calculation. A targeted search of the
current dev tree, the WSS PR history (including merged PR #11646), and the
published residue literature found no statement of this weighted actual-depth
congruence modulo \(81\). The closest residue reference is Bundschuh--Bundschuh,
“Distribution of Fibonacci and Lucas Numbers Modulo \(3^k\),” *Fibonacci
Quarterly* 49 (2011), 201--210
([PDF](https://www.fq.math.ca/Abstracts/49-3/bundschuh.pdf)); it studies
sequence residues and does not state the WSS depth-weighted product identity
proved here. This provenance statement is a bounded repository/literature
audit, not a claim of priority over unpublished work.

M81 is paper-first. The repository currently has Lean support for Fibonacci,
Lucas, and rank interfaces, but no formal block-factorization/depth-vector API;
the existing M27 result is likewise not a Lean theorem. Adding a bind-only
Lean wrapper would overstate the formal status, so no such wrapper is claimed
here. The argument above is a complete elementary proof conditional only on
the already-recorded TBN.2--TBN.3 identities.

## The 3-adic limit and the sharp depth-indexed approximation

The modulus in M81 is not the end of the recurrence information. Put

\[
 v_j:=(-1)^{j+1}u_j.
\]

Then \(v_1=1\), and the exact recurrence (M27.3) becomes

\[
 v_{j+1}=v_j-4\cdot3^{2j+1}v_j^3. \tag{A.1}
\]

Every \(v_j\) is a 3-adic unit. There is therefore a unique limit
\(A\in\mathbf Z_3\) with

\[
 A=\lim_{j\to\infty}v_j,
 \qquad
 v_3(A-v_j)=2j+1. \tag{A.2}
\]

Consequently, for every \(j\ge1\),

\[
 \boxed{u_j\equiv(-1)^{j+1}A\pmod {3^{2j+1}},}
 \qquad
 u_j\not\equiv(-1)^{j+1}A\pmod {3^{2j+2}}. \tag{A.3}
\]

The exponent \(2j+1\) is sharp. To give a finite representative of \(A\),
for \(K\ge1\) set
\[
 J_K=\max\!\left(1,\left\lceil\frac{K-1}{2}\right\rceil\right).
\]
Then \(A\equiv v_{J_K}\pmod {3^K}\), so (A.3) is an effective residue
formula at every prescribed power of 3. The first representatives are
\[
\begin{array}{c|rrrrrrrr}
 K&1&2&3&4&5&6&7&8\\ \hline
 A\bmod 3^K&1&1&1&55&136&379&1108&3295.
\end{array}
\]
Thus M81 is the \(K=4\) projection of a single 3-adic constant, while the
new sharp statement is the depth-indexed modulus in (A.3), rather than a
fixed-modulus periodicity claim.

### Proof of the limit and sharpness

From (A.1), \(v_{j+1}-v_j=-4\cdot3^{2j+1}v_j^3\) has valuation exactly
\(2j+1\), since \(v_j\) is a unit. The increments tend to zero 3-adically,
so \((v_j)\) is Cauchy and converges to \(A\). For fixed \(j\), write
\[
 A-v_j=\sum_{t\ge j}(v_{t+1}-v_t).
\]
The first summand has valuation \(2j+1\), while every later summand has
valuation at least \(2j+3\). The ultrametric inequality therefore gives
the equality in (A.2), and hence both assertions in (A.3). The formula for
\(J_K\) follows from the same tail estimate.

### Weighted-depth corollary and its exact boundary

Let
\[
 S_j:=\sum_{p\mid B_j}h_p b_{p,j},
 \qquad m_j=2\cdot3^{j+1}.
\]
For each prime factor write \(p=1+m_jb_{p,j}\). Expanding all powers and
collecting the linear term gives an integer \(Q_j\) such that
\[
 B_j=1+m_jS_j+m_j^2Q_j. \tag{A.4}
\]
Since \(B_j=1+m_ju_j\), (A.4) implies
\[
 \boxed{S_j\equiv u_j\equiv(-1)^{j+1}A\pmod {3^{j+1}}}\qquad(j\ge1). \tag{A.5}
\]
This contains M27 and M81 after reduction to their respective ranges.

The modulus \(3^{j+1}\) in the first congruence of (A.5) is the strongest
one forced by the TBN.2--TBN.3 hypotheses alone. More explicitly,
\[
 Q_j=\sum_{p\mid B_j}\binom{h_p}{2}b_{p,j}^2
     +\sum_{p<q}h_ph_qb_{p,j}b_{q,j},
\]
and
\[
 \frac{u_j-S_j}{3^{j+1}}\equiv 2Q_j\pmod3. \tag{A.6}
\]
Thus a lift to modulus \(3^{j+2}\) requires the additional condition
\(Q_j\equiv0\pmod3\), which is not part of TBN.2--TBN.3. Individual blocks
can lift accidentally (the displayed small factorizations do), but no uniform
stronger weighted congruence follows without new information on the depth and
residue vector. This is the obstruction behind the distinction between the
sharp recurrence modulus \(3^{2j+1}\) in (A.3) and the guaranteed weighted
modulus \(3^{j+1}\) in (A.5).

### Exact recurrence checks

Using integer recurrence evaluation, the sign-normalized approximants are
\[
\begin{array}{c|r|r|r}
 j&3^{2j+1}&u_j\bmod 3^{2j+1}&v_j\bmod 3^{2j+1}\\ \hline
 1&27&1&1\\
 2&243&107&136\\
 3&2187&1108&1108\\
 4&19683&9827&9856\\
 5&177147&49222&49222
\end{array}
\]
and direct factorization of the first four blocks gives the weighted sums
\(S_1=1\), \(S_2=107\), \(S_3=386749\), and
\(S_4=247065898404113126344022723\). Their differences \(u_j-S_j\) are
zero for \(j=1,2\) and have 3-adic valuation 6 for \(j=3,4\), confirming
the guaranteed congruence and illustrating the possible accidental lift.

### Relation to existing residue tables and formalization boundary

OEIS A268924 records successive Hensel representatives of the 3-adic square
root of \(-2\) (the representatives congruent to 1 modulo 3), and notes their
Lucas-number interpretation; OEIS A271223 records the corresponding base-3
digits via scaled first differences. Those entries concern the Lucas
approximants themselves. The constant \(A\) here is the limit of the
normalized residuals \((-1)^{j+1}(L_{3^j}^2+2)/(2\cdot3^{j+1})\), and (A.5)
adds the actual Fibonacci-depth product \(S_j\), which is not a statement of
either OEIS entry. See [A268924](https://oeis.org/A268924) and
[A271223](https://oeis.org/A271223).

This remains paper-first. No block-factorization/depth-vector Lean API is
present, so no bind-only formal wrapper is claimed. The result is conditional
only on the already-recorded TBN.2--TBN.3 rank and valuation identities and
does not resolve the Wall--Sun--Sun problem.
