---
bibkey: mcnewsetty2026covering
authors: "Nathan McNew; Jai Setty"
year: 2026
title: "On the densities of covering numbers and abundant numbers"
doi: 10.1090/mcom/4209
url: https://arxiv.org/abs/2507.23041v2
claim: "The literal upper bounds in arXiv v2 Lemma 4.10 and Theorem 4.11 fail on the exact finite examples below; this does not refute the separately defined c-prime branch or assert anything about the uninspected journal version."
strata_touched: []
license: citation-only
triage: anchor
---

# Exact counterexamples to two statements in arXiv:2507.23041v2

The universal upper bounds printed in Lemma 4.10 and Theorem 4.11 of
Nathan McNew and Jai Setty, *On the densities of covering numbers and
abundant numbers*, arXiv:2507.23041v2 (10 February 2026), have finite
counterexamples. The respective discrepancies are 1/225 and 7/1920.
The existing Hunter--Worsley forest inequality explains a valid replacement
for the unrestricted overlap subtraction used in the first statement.
Separately, the paper's Lemma 3.1 follows from the Simpson divisor cut
already retained in repository profile 343.

The inspected primary source is
[the arXiv v2 HTML](https://arxiv.org/html/2507.23041v2), SHA256
`d5f622d8b3aaabcb97d3d0e75597ba23ebe775ea0bc6b6f69894197092430b46`.
The statement containers are `S4.Thmtheorem10`, `S4.Thmtheorem11` and
`S3.Thmtheorem1`. All 11 accessible math formulas in those three containers
agree with their embedded `application/x-tex` annotations. The journal
version associated with DOI 10.1090/mcom/4209 was not inspected.

## 1. Lemma 4.10: a multiset counterexample

The printed hypothesis is that M is "any set (or multiset) of moduli".
For any residue system with those moduli, the asserted upper bound for
the covered proportion is

\[
 C(M)=\sum_{\substack{\varnothing\ne S\subseteq M\\
                         S\text{ pairwise coprime}}}
       \frac{(-1)^{|S|+1}}{\operatorname{lcm}(S)}.
\]

Here multiset elements retain their labels. This is also the interpretation
used explicitly in the proof of Theorem 4.11: a subset of distinct numerical
divisors contributes with multiplicity \(\tau(\ell)^{|S|}\).

Choose the ten different congruence classes

\[
 0\bmod3,\quad1\bmod3,\quad2\bmod3,\quad0\bmod9,
\]
\[
 0\bmod5,\quad1\bmod5,\quad2\bmod5,\quad3\bmod5,
 \quad4\bmod5,\quad0\bmod25.
\]

Their common period is 225. The three modulus-3 classes alone cover every
integer, so the actual covered proportion is 1. Repetition of a numerical
modulus is explicitly permitted in this lemma.

The four 3-power labels have reciprocal sum
\(A=3/3+1/9=10/9\); the six 5-power labels have reciprocal sum
\(B=5/5+1/25=26/25\). A pairwise-coprime subset contains at most one
label from each group. Thus there are ten admissible singletons,
24 admissible pairs and no admissible larger subsets. Consequently

\[
 C(M)=A+B-AB
 =\frac{484}{225}-\frac{52}{45}
 =\frac{224}{225}<1.
\]

Every retained coprime intersection has exactly the reciprocal-lcm density
required by CRT. The defect lies in the selective omission of other
inclusion-exclusion terms. For comparison, the full signed contributions
by subset cardinality are

\[
 \frac{484}{225},\quad-\frac{98}{75},\quad
 \frac4{25},\quad-\frac1{225},\quad0,\ldots,0.
\]

They sum to 1; the omitted signed total is 1/225.

## 2. The overlap cycle and the existing forest repair

Put an edge between two labels when their numerical moduli are coprime.
For this example the graph is \(K_{4,6}\), with 24 edges and no triangles.
The retained pointwise expression is therefore
\(|H(x)|-|E(H(x))|\), where \(H(x)\) is the set of classes containing x.

At \(x=0\pmod{225}\), the four hit classes are
\(0\bmod3,0\bmod9,0\bmod5,0\bmod25\). Their induced graph is
\(K_{2,2}\): four vertices and four edges, giving score zero despite the
union indicator being one. At every other residue, at least one of
\(9\nmid x\) and \(25\nmid x\) holds. Each prime-power group then has
one or two hit labels and at least one group has exactly one. Writing
their hit counts as a and b gives \(a+b-ab=1\). Hence the average
pointwise score is exactly 224/225.

The established replacement is to select a forest F of overlap edges.
For any finite family of events \(E_i\) and any point with nonempty hit
set H, the induced forest F[H] has at most \(|H|-1\) edges. Therefore

\[
 \mathbf1_{\cup_iE_i}
 \leq\sum_i\mathbf1_{E_i}
     -\sum_{\{i,j\}\in F}\mathbf1_{E_i\cap E_j}.
\]

The empty-hit case gives zero on both sides. Integration yields the
Hunter--Worsley bound

\[
 \Pr\!\left(\bigcup_iE_i\right)
 \leq\sum_i\Pr(E_i)-\sum_{\{i,j\}\in F}\Pr(E_i\cap E_j).
\]

Repository [profile 334](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/334-same-chain-overlap-and-future-risk-certificates.md), *Same-chain overlap and future-risk certificates*,
already gives this argument and inequality (JC2), including the permitted
use of a certified forest. Its references include Hunter (1976),
DOI 10.2307/3212481; Worsley (1982), DOI 10.1093/biomet/69.2.297;
and Bukszár (2003), Theorem 5, DOI 10.7153/mia-06-66.

For an exact finite check, number the displayed classes 0 through 9.
Take the nine tree edges \((0,j)\), \(4\le j\le9\), and
\((i,4)\), \(1\le i\le3\). Their intersection densities sum to
\(26/75+7/45=113/225\), so the resulting safe upper bound is
\(484/225-113/225=371/225\). It is loose, as expected; clipping at the
trivial upper bound 1 is valid. This illustration neither claims tree
optimality nor supplies a corrected Bell-polynomial theorem. No new
general graph theorem is needed.

## 3. Theorem 4.11: all stated hypotheses hold at n=1920

Section 4 defines r(n) as the maximum number of residues modulo n covered
using distinct moduli greater than 1 dividing n, and
\(c(n)=1+r(n)/n\). Definition 4.5 calls \(\ell\) almost-covering
exactly when \(r(\ell)=\ell-1\).

Theorem 4.11 assumes \(n=\ell b\), \(\gcd(\ell,b)=1\), and
that \(\ell\) is almost-covering. Its displayed conclusion is

\[
 c(n)\le1+\frac{\ell-1}{\ell}
       +\frac1\ell\sum_{\substack{d\mid b\\d>1}}
         \frac{B(\tau(\ell),\omega(d))}{d},
\]

where the preceding printed definition is

\[
 B(r,j)=-\sum_{k=1}^{j}(-r)^kS_2(j,k).
\]

The statement imposes no primitivity condition on n, no noncovering
condition on n, and no comparison between \(\tau(\ell)\) and the
prime factors of b.

Take \(n=1920\), \(\ell=128\), \(b=15\). The factorization and
coprimality conditions hold. The seven classes

\[
 0\bmod2,\ 1\bmod4,\ 3\bmod8,\ 7\bmod16,\quad
 15\bmod32,\ 31\bmod64,\ 63\bmod128
\]

cover exactly the 127 residues other than 127 modulo 128. Equivalently,
every residue x other than 127 belongs to the class indexed by
\(v_2(x+1)+1\). Conversely, all available distinct nonunit divisors of
128 are \(2,4,8,16,32,64,128\). Regardless of the chosen phases, their
classes cover at most

\[
 64+32+16+8+4+2+1=127
\]

residues by the union bound. This proves \(r(128)=127\) exactly.

The following five classes have distinct moduli and cover modulo 12:

\[
 0\bmod2,\quad0\bmod3,\quad1\bmod4,\quad5\bmod6,\quad7\bmod12.
\]

The even residues lie in the first class. Of the odd residues, 3 and 9
lie in the second, 1 and 5 in the third, 11 in the fourth, and 7 in the
fifth. Every modulus divides 1920. Lifting the cover proves
\(r(1920)=1920\), hence \(c(1920)=2\).

Since \(\tau(128)=8\), the three divisors \(3,5,15\) of b contribute

\[
 B(8,1)=8,\qquad B(8,2)=8-64=-56,
\]
\[
 \sum_{\substack{d\mid15\\d>1}}
       \frac{B(8,\omega(d))}{d}
 =\frac83+\frac85-\frac{56}{15}=\frac8{15}.
\]

The printed upper bound becomes

\[
 1+\frac{127}{128}+\frac1{128}\frac8{15}
 =\frac{3833}{1920}
 =2-\frac7{1920}<c(1920).
\]

Thus this is a counterexample to Theorem 4.11 as printed. Definition 4.7 selects \(\ell(1920)=128\): the next prime 3 is not
\(\tau(128)+1=9\), so its greedy prefix stops after the 2-power.
The subsequent Definition 5.1 separately assigns the trivial bound 2 when
\(P^-(b)\le\tau(\ell)\), a condition satisfied here. This example
therefore does not refute the use of that branch in the later algorithm.

## 4. Lemma 3.1 is already supplied by the existing divisor cut

The paper's Lemma 3.1 states that a primitive covering number n satisfies
\(P^+(n)\le\tau(n/P^+(n))\). Its introductory sentence credits Sun's
Lemma 2.1. The repository already retains the needed Simpson result in
[profile 343](../../docs/reports/erdos7-odd-covering/profile-notes/321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md), *CRT to multivalued SAT: prefix-preserving reductions and
transport obstructions*, section 2. For an inclusion-minimal full cover
with actual lcm Q, Simpson's Theorem 2 gives

\[
 D\mid Q,\quad D\ne Q
 \quad\Longrightarrow\quad
 \#\{i:d_i\nmid D\}\ge1+f(Q/D),
 \qquad f(m)=\sum_pv_p(m)(p-1).
\]

The cited source is Simpson, *Acta Arithmetica* 45 (1985), 145--152,
Theorem 2, pp.149--151, DOI 10.4064/aa-45-2-145-152.

Start with a distinct-modulus covering system whose moduli divide a
primitive covering number n, and take an inclusion-minimal subcover.
Its actual lcm L divides n and is itself a covering number. Primitivity
forces L=n: otherwise L would be a smaller covering divisor of n.
This step justifies retaining n when applying the minimal-cover theorem.

For any prime p dividing n, let \(a=v_p(n)\) and set \(D=n/p\).
The Simpson cut says that at least \(1+f(p)=p\) selected labels have
moduli not dividing n/p. These are exactly the moduli with full p-height
a. Because the original numerical moduli are distinct, their number is
at most the total number of divisors of n with that height, namely
\(\tau(n/p^a)\). Consequently

\[
 p\le\tau(n/p^a)\le\tau(n/p).
\]

Taking \(p=P^+(n)\) proves the printed lemma. This is reuse of an
existing stronger result, with no new Lean declaration or novelty claim.

## 5. Verification and scope

The [standard-library checker](../../docs/reports/erdos7-odd-covering/frontier/cover-geometry/mcnew_setty_v2_counterexamples.py)
constructs exact integer residue masks, evaluates all 1,023 nonempty
label subsets for the first example, checks every residue of periods
225, 128 and 1920, and computes the divisor and Stirling-number terms
with exact rational arithmetic. It also checks the displayed forest
and the separate Definition 5.1 branch at 1920. Run it with
`--base <report-base> --check`; checks remain active under
`python3 -B -I -S -O`.

The retained source excerpts bind the stated formulas and definitions to
the inspected arXiv version and primary HTML hash above. Offline replay
reads those excerpts and binds the resulting data to their bytes and to
the checker. The ordinary proofs above establish the general forest
inequality and the Simpson specialization; finite replay verifies the
stated controls. No Lean verification or new general graph theorem is
claimed.

These conclusions concern the two literal universal statements in the
inspected arXiv v2. The journal text and the paper's remaining proofs,
implementation and density estimates have not been audited here. No
whole-paper invalidation follows. The first counterexample permits
repeated moduli, while the second uses even moduli. Neither is a system
of distinct odd moduli or a resolution of Erdős problem 7.
