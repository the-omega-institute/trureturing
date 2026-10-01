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


## Theorem (the sharp 3-adic limit)

The recurrence has a complete 3-adic description, beyond any fixed modulus.
Define
\[
 c_j=(-1)^{j+1}u_j\qquad(j\ge1).
\]
Then \(c_1=1\), and (M27.3) rewrites as
\[
 c_{j+1}=c_j\left(1-4\cdot3^{\,2j+1}c_j^2\right).
 \tag{L3.1}
\]
Inductively \(3\nmid c_j\) for every \(j\). Consequently
\[
 c_{j+1}-c_j=-4\cdot3^{\,2j+1}c_j^3,
 \qquad
 v_3(c_{j+1}-c_j)=2j+1.
 \tag{L3.2}
\]

There is a unique \(C\in\mathbb Z_3\) such that \(c_j\to C\), and the
convergence order is exact:
\[
 \boxed{v_3(C-c_j)=2j+1\qquad(j\ge1).}
 \tag{L3.3}
\]
Indeed, for \(n>j\),
\[
 c_n-c_j=\sum_{t=j}^{n-1}-4\cdot3^{\,2t+1}c_t^3.
\]
The summands have strictly increasing 3-adic valuations
\(2j+1,2j+3,\ldots\), so the first summand is the unique lowest-order
term. Passing to the limit proves (L3.3).

Equivalently, for every integer \(K\ge1\),
\[
 \boxed{
 u_j\equiv(-1)^{j+1}C\pmod {3^K}
 \quad\Longleftrightarrow\quad
 K\le2j+1.}
 \tag{L3.4}
\]
Thus \(3^{\,2j+1}\) is the maximal stabilization modulus at index \(j\);
the next modulus \(3^{\,2j+2}\) fails exactly. The first residues of \(C\)
(which determine all lower congruences) are
\[
\begin{array}{c|rrrrrrrr}
K&1&2&3&4&5&6&7&8\\ \hline
C\bmod3^K&1&1&1&55&136&379&1108&3295 .
\end{array}
\]
For \(K=3\), (L3.4) recovers M27; for \(K=4\), \(C\equiv55\pmod{81}\)
gives \(u_j\equiv26(-1)^j\pmod{81}\), exactly the M81 residue.

Two useful exact valuations follow immediately:
\[
 \boxed{v_3(B_j-1)=j+1,\qquad
 v_3(u_{j+1}+u_j)=2j+1.}
 \tag{L3.5}
\]
The first uses \(B_j-1=2\cdot3^{j+1}u_j\) and \(3\nmid u_j\); the second
is (M27.3) with the sign changed.

### Weighted-depth consequence at the natural growing modulus

Set \(m_j=2\cdot3^{j+1}\) and
\(S_j=\sum_{p\mid B_j}h_pb_{p,j}\), as above. TBN.3 gives the exact
factorization \(B_j=\prod_{p\mid B_j}p^{h_p}\) and
\(p=1+m_jb_{p,j}\). Since
\[
 (1+m_jb)^{h}\equiv1+m_jhb\pmod {m_j^2},
\]
multiplication over the finite support gives
\[
 B_j\equiv1+m_jS_j\pmod {m_j^2}.
\]
Comparing with \(B_j=1+m_ju_j\) and cancelling \(m_j\) yields the
growing-modulus congruence
\[
 \boxed{S_j\equiv u_j\pmod {m_j}}
 \quad\text{and hence}\quad
 \boxed{S_j\equiv u_j\pmod {3^{\,j+1}}}
 \qquad(j\ge1).
 \tag{L3.6}
\]
The direct bases \(S_1=1\) and \(S_2=107\) agree exactly. M27 and M81 are
fixed-modulus corollaries of (L3.6).

The modulus \(3^{j+1}\) is the uniform order supplied by the first-order
factorization argument. A higher S-only modulus would require control of
the second-order coefficient
\[
 T_j=\sum_p\binom{h_p}{2}b_{p,j}^2+
     \sum_{p<q}h_ph_qb_{p,j}b_{q,j},
\]
because \(u_j=S_j+m_jT_j+O(m_j^2)\). No 3-divisibility of \(T_j\) follows
from TBN.3 or the existing parity/ternary balances, so (L3.6) is the
maximal uniform conclusion from the current depth-factorization inputs.
Higher-order corrected identities can be obtained by retaining further
coefficients of \prod_p(1+b_{p,j}z)^{h_p}, but they are different
weighted statistics. The algebraic premises alone cannot force a higher
S-only modulus: the formal one-factor pattern \((1+m_j)^2\) has
\(u_j-S_j=m_j\) exactly.

### 3-adic provenance and formalization boundary

The Lucas side is a classical 3-adic approximation problem: OEIS
[A268924](https://oeis.org/A268924) records that the representatives
\(L_{3^j}\) approximate the chosen 3-adic square root of \(-2\) and gives
the recurrence \(x\mapsto x^3+3x\), with references to Nagell and Lang.
OEIS [A271223](https://oeis.org/A271223) records the corresponding base-3
digits and cites Nagell's Hensel-lifting formulas. In our notation
\(L_{3^j}^2+2=B_j-1=2\cdot3^{j+1}u_j\), so (L3.5) is the exact error order
for these approximants. The checked sources do not state the normalized
limit \(C\) together with the WSS actual-depth congruence (L3.6); this is a
bounded provenance audit, not an absolute priority claim.

This theorem remains paper-first. Existing Lean modules cover Fibonacci,
Lucas, and rank interfaces, but no formal block-factorization/depth-vector
API exists; adding a bind-only wrapper would overstate the formal status.
The only arithmetic input about prime depths is the already-recorded TBN.3
identity.


## The coefficient hierarchy and the E2 boundary

The first-order statistic \(S_j\) is only the first coefficient of an exact
finite polynomial. Define
\[
 \Phi_j(X):=\prod_{p\mid B_j}(1+b_{p,j}X)^{h_p}
       =\sum_{q=0}^{H_j}E_{q,j}X^q,
 \qquad H_j:=\sum_{p\mid B_j}h_p.
 \tag{E2.1}
\]
Here \(E_{0,j}=1\), \(E_{1,j}=S_j\), and
\[
 E_{2,j}=T_j
 =\sum_{p\mid B_j}\binom{h_p}{2}b_{p,j}^2
  +\sum_{p<q}h_ph_qb_{p,j}b_{q,j}.
 \tag{E2.2}
\]
Evaluating at \(X=m_j\) and using \(B_j=1+m_ju_j\) gives the exact hierarchy
\[
 u_j=\sum_{q=1}^{H_j}m_j^{q-1}E_{q,j}.
 \tag{E2.3}
\]
For \(Q\ge1\), write
\[
 U_{j,Q}:=\sum_{q=1}^{Q}m_j^{q-1}E_{q,j}
 \quad (Q\le H_j).
\]
Then
\[
 \boxed{u_j\equiv U_{j,Q}\pmod {m_j^Q}}.
 \tag{E2.4}
\]
Thus the second-order corrected depth statistic
\[
 \widehat S_j:=U_{j,2}=S_j+m_jT_j
\]
satisfies \(\widehat S_j\equiv u_j\pmod {m_j^2}\). This is an exact
coefficient identity, not a new recurrence for the factorization data.

### Why E2 gives no stronger uniform limit

Let \(C\) be the 3-adic limit from (L3.3), and put
\(\widehat c_j=(-1)^{j+1}\widehat S_j\). Since
\(v_3(m_j^2)=2j+2\), (E2.4) with \(Q=2\) and the sharp identity (L3.3)
give
\[
 \boxed{v_3(C-\widehat c_j)=2j+1.}
 \tag{E2.5}
\]
Therefore adding \(m_jE_{2,j}\) improves the reconstruction of \(u_j\) from
\(S_j\), but does not improve the sharp 3-adic approximation to \(C\), and
cannot produce a second limit by this correction. The same argument applies to
all \(U_{j,Q}\) with \(Q\ge2\): the intrinsic \(2j+1\) error in the Lucas
recurrence remains the first nonzero term.

Nor does TBN.3 supply a cross-\(j\) recurrence for \(E_{2,j}\). It specifies,
for each block separately, only \(p=1+m_jb_{p,j}\) and the exponent \(h_p\).
It gives no relation between the multisets
\(\{(b_{p,j},h_p):p\mid B_j\}\) and
\(\{(b_{p,j+1},h_p):p\mid B_{j+1}\}\). At the coefficient level this is a
real underdetermination: the multisets \(\{(a,1)\}\) and
\(\{(1,1),(a-1,1)\}\) have the same \(E_1=a\), while their \(E_2\) values
are \(0\) and \(a-1\), respectively. The local congruence \(p\equiv1\pmod{m_j}\)
does not remove this freedom modulo 3. Hence no stable \(E_{2,j}\pmod3\), nor
an \(E_2\) recurrence, follows from TBN.3 alone; proving one would require a
new theorem relating the prime-depth vectors of consecutive Lucas blocks.

### Exact j=3,4,5 obstruction checks

The first blocks already disprove a uniform lift of the \(S_j\)-only congruence
to \(3^{j+2}\). Exact factorizations and integer arithmetic give
\[
\begin{array}{c|c|c|c|c|c}
 j&\#\{p\mid B_j\}&(b_{p,j}\bmod27)_{p\mid B_j}
   &T_j\bmod27&v_3(u_j-S_j)&v_3(u_j-\widehat S_j)\\ \hline
 3&2&(19,9)&9&6&\infty\\
 4&2&(15,11)&3&6&\infty\\
 5&4&(1,13,3,11)&26&6&12
\end{array}
\]
Here \(v_3(0)=\infty\). For \(j=5\), the exact squarefree factorization used for
this row is
\[
\begin{aligned}
 B_5={}&1459\cdot58321\cdot67234945243909760461\\
 &\cdot64642456533364216165903625998192510598323380531684784427098565775883411861.
\end{aligned}
\]
All four factors are prime and have \(h_p=1\), so the displayed residues give
\(T_5\equiv2\pmod3\). Since \(v_3(m_5)=6\), this forces
\(v_3(u_5-S_5)=6\), and therefore \(S_5\not\equiv u_5\pmod{3^7}\). This is
a concrete sharp obstruction to any universal one-digit lift of (L3.6). The
\(j=3,4\) rows happen to have only two depth-one factors, so \(E_{q,j}=0\) for
\(q\ge3\) and \(\widehat S_j=u_j\) exactly; that accidental equality does not
persist at \(j=5\).

The coefficient identities (E2.1)--(E2.4) are elementary consequences of the
TBN.3 factorization and are paper-first. The no-go statement concerns what can
be inferred from TBN.3 alone; it neither asserts that the actual \(E_{2,j}\)
sequence has no deeper law nor changes the open status of Wall--Sun--Sun primes.

