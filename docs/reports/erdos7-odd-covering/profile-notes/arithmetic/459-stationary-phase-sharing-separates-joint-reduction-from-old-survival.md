# Stationary phase sharing separates joint reduction from old survival

For the stationary first-nonzero-digit family on \(\{5,7,11,13\}\), two different sharp counts apply. After a valid reduction of a joint threshold problem with threshold \(c<2\), the nonzero digit cube has at least **1190** old survivors, and this count is attained. Without that reduction, an actual old phase family has only **1185** survivors on the same cube. Its finite-height conditional survivor fraction tends to \(1185/1485=79/99\), attaining the existing all-height lower bound in [Chapter19, KE1](../../problem-details/19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md).

Thus the reduced count cannot be substituted as an unrestricted old-survival estimate. Neither count resolves the joint target \(J<2254/1185\). These are ordinary proofs and exact arithmetic controls, with no new Lean certification or claim of public mathematical priority.

## The stationary arithmetic family

Fix \(P=(5,7,11,13)\), finite heights \(h_q\ge1\), and

\[
 K=\prod_{q\in P}q^{h_q}.
\]

For each nonempty support \(I\subseteq P\), choose nonzero digits \(d_{I,q}\in\{1,\ldots,q-1\}\), one per \(q\in I\). For every exponent tuple \(1\le e_q\le h_q\), the original label

\[
 m=\prod_{q\in I}q^{e_q}
\]

has the unique CRT residue specified by

\[
 x\equiv d_{I,q}q^{e_q-1}\pmod{q^{e_q}}
 \qquad(q\in I).
 \tag{SP1}
\]

Each numerical modulus occurs once. The digit pattern depends on its support, and is constant across the exponent tuples for that support. This stationary restriction is a genuine hypothesis; arbitrary original residues need not have this form.

Normalize the pure old digits to 1. For a coordinate modulo \(q^{h_q}\), record 0 if the coordinate is zero, and otherwise record its first nonzero base-\(q\) digit, starting at the least significant end. Pure old classes delete exactly digit 1. The pure-old survivor digit space is therefore

\[
 D=\prod_{q\in P}\{0,2,\ldots,q-1\},
 \qquad
 D^*=\prod_{q\in P}\{2,\ldots,q-1\},
 \quad |D^*|=1485.
 \tag{SP2}
\]

A stationary mixed support is active exactly when its specified digits match. At a given arithmetic point and support, at most one exponent tuple in (SP1) can match, because each nonzero coordinate has a unique first nonzero position. This explains the digit representation without identifying different original numerical labels.

Every fixed nonzero digit has exactly

\[
 w_q(h_q)=\sum_{e=1}^{h_q}q^{h_q-e}
          =\frac{q^{h_q}-1}{q-1}
 \tag{SP3}
\]

arithmetic realizations; digit 0 has one. Permuting nonzero digit names preserves these weights and produces another family of the form (SP1). This is a correspondence between stationary families, not an assertion that arbitrary digit permutations are ring automorphisms.

## The joint threshold permits removing old occurrences of the new pure digit

Add a second stationary family of cofactor patterns, corresponding to one new parent layer, and let \(g\) be its raw multiplicity on the complete old survivor set \(S\). Its pure-coordinate patterns may be completed if missing, since adding a new class cannot decrease \(g\). If a new pure digit equals old digit 1, that event misses every old survivor; replacing it by a different nonzero digit cannot decrease \(g\). Independent digit permutations fixing old digit 1 then normalize all new pure digits to 2.

Set

\[
 f=g+\mathbf1_{g>0},\qquad
 J=\mathbb E_{\mu_S}f
   =\mathbb E_{\mu_S}g+\Pr_{\mu_S}(g>0),
 \tag{SP4}
\]

where \(\mu_S\) is the actual uniform arithmetic law on \(S\). In digit coordinates it uses the product weights (SP3), subsequently conditioned on all old mixed exclusions.

For \(c<2\), the condition \(J\ge c\) is equivalent to

\[
 \sum_{x\in S}w(x)(f(x)-c)\ge0.
 \tag{SP5}
\]

An old mixed pattern specifying digit 2 on any coordinate lies inside the corresponding new pure event. Replace that old pattern by one containing digit 1, making it inactive on pure-old survivors. This enlarges \(S\) by a set \(E\) on which \(g\ge1\), hence \(f\ge2>c\). Consequently

\[
 \sum_{x\in S\cup E}w(x)(f(x)-c)
 =\sum_{x\in S}w(x)(f(x)-c)
  +\sum_{x\in E}w(x)(f(x)-c)
 \ge\sum_{x\in S}w(x)(f(x)-c).
 \tag{SP6}
\]

The new pattern preserves the original numerical-label inventory. Repeating the operation shows that every stationary counterexample to a threshold \(c<2\) has a counterpart in which every active old mixed pattern uses digits at least 3. Inactive choices remain allowed. The argument also applies to the limiting uniform law on \(D^*\).

This reduction preserves the threshold violation, not the original survivor law or its denominator. It does not show that unrestricted old configurations already satisfy the reduced denominator bound. Nor does it apply to arbitrary nonstationary phases.

## Sharp counts on the nonzero digit cube

For a denominator lower bound, fill inactive mixed supports with active patterns: adding exclusions can only reduce the survivor count. There are six pair supports, four triple supports, and one full support. On \(D^*\), their individual sizes sum to

\[
 \sum_{|I|=2}|C_I|=274,\qquad
 \sum_{|I|=3}|C_I|=11+9+5+3=28,\qquad
 |C_P|=1.
 \tag{SP7}
\]

At a cell \(x\), let \(G_x\) be the graph on the four prime coordinates whose edges are the pair patterns meeting \(x\). Let \(t_x\) count the perfect matchings contained in \(G_x\). For any one specified adjacent pair of edges, let \(a_x\) indicate that both edges occur. Then

\[
 (|E(G_x)|-1)_+\ge t_x+a_x.
 \tag{SP8}
\]

With at most one edge the claim is immediate. With two edges the matching and adjacency indicators cannot both be 1. A three-edge graph has at most one perfect matching; four- and five-edge graphs have at most two; the complete six-edge graph has three. These cases prove (SP8).

Every pair of disjoint supports fixes all four digits and has exactly one common cell. Thus \(\sum_x t_x=3\). Even without the adjacency term, (SP8) gives pair union at most \(274-3=271\), total mixed union at most \(271+28+1=300\), and at least 1185 survivors for unrestricted stationary patterns on \(D^*\).

In the reduced class, the three pair patterns incident to coordinate 5 use only digits 3 and 4 there. Two agree by the pigeonhole principle. Their adjacent-support intersection leaves one of the other three coordinates free, so it has at least five cells. Choose these edges for \(a_x\) in (SP8). The total overlap credit is at least \(3+5=8\), yielding

\[
 |\text{pair union}|\le266,\qquad
 |\text{mixed union}|\le295,\qquad
 |S\cap D^*|\ge1190.
 \tag{SP9}
\]

Both bounds are attained. Support masks use bit order \((5,7,11,13)\); digits are listed in increasing prime order on each support. All pure patterns have digit 1.

| Mask | Support | Reduced pattern | Unrestricted pattern |
|---:|---|---|---|
| 3 | 5,7 | 3,3 | 2,2 |
| 5 | 5,11 | 4,3 | 3,2 |
| 6 | 7,11 | 4,4 | 3,3 |
| 7 | 5,7,11 | 3,4,6 | 2,3,5 |
| 9 | 5,13 | 4,3 | 4,2 |
| 10 | 7,13 | 5,4 | 4,3 |
| 11 | 5,7,13 | 3,5,6 | 2,4,5 |
| 12 | 11,13 | 5,5 | 4,4 |
| 13 | 5,11,13 | 4,6,6 | 3,5,5 |
| 14 | 7,11,13 | 6,4,4 | 5,3,3 |
| 15 | 5,7,11,13 | 3,6,6,6 | 4,6,6,6 |

The reduced pair union has 266 cells; its triples add 28 cells and its full-support pattern adds one. The unrestricted pair union has 271 cells, with the same subsequent additions. Thus 1191 is already false for the reduced nozero cube, and 1190 is false for unrestricted stationary patterns on that cube.

## Exact finite-height arithmetic counts

Let \(a_Z\) be the number of surviving digit words whose zero coordinates are exactly \(Z\subseteq P\). The product weights in (SP3) give the exact full arithmetic count

\[
 |S|=\sum_{Z\subseteq P}a_Z\prod_{q\notin Z}w_q(h_q),
 \qquad
 |V|=\prod_{q\in P}\bigl(1+(q-2)w_q(h_q)\bigr),
 \tag{SP10}
\]

where \(V\) avoids only the pure old classes. Each summand counts all arithmetic realizations of its digit words, and distinct digit words have disjoint realizations. Thus (SP10) is a count of the literal family (SP1), not a relaxed probability model.

The exact coefficient arrays, in zero-mask order 0 through 15, are

```text
reduced:      1190,469,274,98,145,54,32,11,117,44,26,9,14,5,3,1
unrestricted: 1185,469,273,98,145,54,32,11,117,44,26,9,14,5,3,1
```

As every height tends to infinity, divide numerator and denominator in (SP10) by \(\prod_qw_q(h_q)\). All terms with a nonempty zero mask vanish, so the unrestricted construction satisfies

\[
 \frac{|S|}{|V|}\longrightarrow\frac{1185}{1485}=\frac{79}{99}.
 \tag{SP11}
\]

Together with Chapter19's existing lower bound, this identifies the exact infimum of the old conditional survival fraction over the larger class of all actual finite families on these primes. The construction is stationary, but its attainment of the limiting bound rules out any uniformly larger bound even in that restricted class. This concerns survival under the pure-old product law, not the ambient Haar density.

Already at equal height 3, the unrestricted family has 255 distinct old moduli and

\[
 K=125375375125,\quad |S|=51897928602,\quad |V|=64864962448,
\]

\[
 \frac{|S|}{|V|}
 =\frac{1996074177}{2494806248}
 <\frac{1190}{1485}.
 \tag{SP12}
\]

Hence the proposed unrestricted 1190 fraction fails for a finite actual arithmetic family, not only at an infinite limit.

## Exact controls and remaining joint gap

The standalone [program](../../frontier/cover-geometry/stationary_phase_sharing_boundary.py) embeds the prime list and both pattern tables; its [data](../../frontier/cover-geometry/stationary_phase_sharing_boundary.json) records their coefficient arrays, exact counts at equal heights 1 through 4, and literal original residue classes at height 1. It checks all 64 four-vertex graphs in (SP8), the attaining pair/triple/full-support contributions, and every residue in the height-one period for both families: 10,010 literal checks in total. Those checks compare direct membership in the original CRT classes with digit membership and (SP10).

The height-three period is not exhaustively enumerated. Its count is obtained by the proved partition formula (SP10), using the exact finite digit coefficients. The general height conclusion uses (SP3), (SP10), and the limiting argument, not extrapolation from the tested heights. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/stationary_phase_sharing_boundary.py
```

Output defaults to JSON on stdout; `--output PATH` selects a file. There are no temporary-file or third-party dependencies, and checks remain active under optimization.

The unresolved joint question remains whether all relevant actual configurations satisfy

\[
 J<\frac{2254}{1185}.
\]

The threshold reduction is applicable to this number because it is less than 2, but a denominator bound alone supplies no corresponding numerator bound for \(\mathbb E g+\Pr(g>0)\). No universal joint estimate or actual counterexample to that target is supplied here. In particular, a configuration minimizing old survival need not maximize the joint load. [Report458](458-distinguished-prime-completion-removes-the-early-phase-restriction.md) obtains a different arbitrary-phase completion interface by changing the distinguished prime; the sharp old-survival obstruction here does not invalidate that argument.
