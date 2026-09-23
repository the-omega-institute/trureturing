# A complete query can be constant on all original survivors

Full support on the original survivor set does not force a complete divisor query to have positive variance, even if its largest-modulus class meets that set and its value exceeds the compulsory unit term. The following actual original family has eleven pairwise distinct odd moduli, all classes have private points, and every pair of comparable original classes is disjoint. Nevertheless its complete query has value two on every original survivor.

Consequently the variance is zero under **every** probability supported on those survivors, including any law supplied for this input by [report466](466-randomized-completion-retains-full-original-survivor-support.md) or [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md). This does not identify the uniform survivor law with the particular law chosen by those constructions. It rules out an automatic positive-variance deduction from full support; it does not realize a constant load of twenty, rule out that load, or settle the two-prime joint-capacity problem.

This is an ordinary finite counterexample and exact arithmetic verification, with no new Lean declaration or claim of literature priority. It enlarges no proven noncoverage range.

## One original family and one complete query

Put K=315=3^2·5·7. The original class at each nonunit divisor d is a_d mod d. Independently, b_d specifies one fixed query class at every divisor, including the unit divisor:

| d | Original residue a_d | Query residue b_d |
|---:|---:|---:|
| 1 | — | 0 |
| 3 | 0 | 2 |
| 5 | 0 | 0 |
| 7 | 0 | 0 |
| 9 | 7 | 4 |
| 15 | 13 | 4 |
| 21 | 10 | 0 |
| 35 | 6 | 0 |
| 45 | 4 | 37 |
| 63 | 37 | 0 |
| 105 | 61 | 0 |
| 315 | 46 | 1 |

Let U be the complement of the union of the original classes in Z/315, and set

    L(x)=sum_(d|315) 1_(x=b_d mod d).

The query does not replace any original residue. All its choices are fixed before x is sampled. Complete-period enumeration gives |U|=86. The only active nonunit query classes partition U as follows:

| Query class | Number of points in U |
|---|---:|
| 2 mod 3 | 69 |
| 4 mod 9 | 8 |
| 4 mod 15 | 4 |
| 37 mod 45 | 4 |
| 1 mod 315 | 1 |

Every other nonunit query has residue zero and misses U because one of the original prime classes already excludes it. Thus

    L(x)=2 for every x in U.

The largest query is active at x=1, so its contribution has not simply been removed from the task.

## The five query pieces really partition the original survivors

Take x in U missing 2 mod 3. The original 0 mod 3 then forces x=1 mod 3. If x also misses 4 mod 9, the original 7 mod 9 forces x=1 mod 9.

The possible mod-15 residues are now 1,4,7,10,13. The original classes 0 mod 5 and 13 mod 15 remove 10 and 13. Missing the query 4 mod 15 removes 4. Combining the remaining residues 1 or 7 mod 15 with x=1 mod 9 gives x=1 or 37 mod 45. Missing 37 mod 45 leaves x=1 mod 45.

Its seven representatives modulo315 are

    1,46,91,136,181,226,271.

The last six are excluded, respectively, by the original classes of moduli315,7,21,35,63,105. The remaining point1 is the query class modulo315. This proves exhaustion without using the computed count86.

The query modulo3 is disjoint from the other four. Among those four, the only possible intersection is between 4 mod 9 and 4 mod 15: it is 4 mod 45, which the original class excludes. The five pieces are therefore disjoint on U. Each x in U contributes exactly one nonunit query term, as claimed.

The original classes are also irredundant on their union. In increasing order of the eleven original moduli, their private-region sizes are

    69,27,17,13,9,5,5,5,3,2,1.

The original class modulo315 has private point46. The exact checker verifies every private witness and all31 pairs of comparable original moduli. Their classes are disjoint, although some incomparable original classes intersect. These are properties of this noncovering family; they do not supply the hypothetical whole-cover extremality premise used in [report385](385-private-congruence-hulls-and-crossed-modulus-closure.md).

## The conclusion is independent of the chosen survivor law

For any probability mu supported on U, even without full support,

    E_mu L=2,     E_mu L^2=4,     Var_mu(L)=0.

Full support cannot change an identity holding on every point of U. In particular a different source policy, a mixture of supported policies or the randomized completion law cannot introduce variance for this query on this input.

For the convenient concrete law mu=uniform(U), the density relative to full Haar is315/86 on U and zero elsewhere. Direct cylinder counts give

    R_K(mu)=sum_(1<d|K) max_a mu(a mod d)=185/86.

This is the sum of each divisor's largest cylinder mass, not the mean of the one displayed query. Its complete maximum including the unit term is271/86; the displayed query mean is2.

On full Haar the same query is nonconstant. Its mean is

    sum_(d|315) 1/d=208/105,

and its counts at load values1,2,3,4,5,6,7 are respectively

    101,144,56,7,4,2,1.

For the primitive character chi(x)=exp(2 pi i x/315), [report336](../321-384/336-maximal-label-fourier-overlap-and-uncovered-density.md)'s original-cylinder Fourier identity gives

    E_H[L conjugate(chi)]=exp(-2 pi i/315)/315 != 0.

Only the query of modulus315 contributes at that conductor. There is no conflict with the zero variance under mu: the measure has changed to the actual original survivor set. The full-Haar Fourier coefficient is not a Fourier coefficient under that restricted measure.

## The same obstruction can use all seven core primes

Add the original classes 0 mod p for p=11,13,17,19. With

    K'=315·11·13·17·19=14549535,
    U'=U times product_(p=11,13,17,19) (Z/p)^×,

retain b_d for d|315 and assign query residue zero to every new divisor d of K' not dividing315. Each new query requires zero at an added prime and therefore misses U'. The complete query on K' still has value2 on every original survivor.

CRT gives |U'|=2972160. For uniform(U'), multiplication of the independent prime-cylinder maxima gives

    density=323323/66048,
    R_(K')=9545059/2972160.

In particular this same law satisfies

    (1/5) H_(K')|U' <= mu <= (6075000000000/7235955529) H_(K'),
    R_(K')(mu) <=70871/3375.

These are the density and query scalars of report467, satisfied here with slack. The construction does not assert that uniform(U') is the source-selected probability. Constancy on U' proves zero variance for any source-selected supported probability anyway. The active query at the largest carrier modulus belongs to the original315 example; in this padded example the new K' query is inactive.

## What is still needed for the two-axis capacity

For the23/29 capacity expression with one common abstract complete load l, the positive part is

    [(22-l)_+ (28-l)_+ - l]_+.

It vanishes at both l=20 and l=21. Thus even the abstract law assigning probability1/2 to each value has positive variance1/4 and zero capacity. This separate two-point observation is not an original-phase realization or a claim that all source constraints have been verified for it.

The actual family above rules out using oddness, full survivor support, private points and an active largest query as an automatic nonconstancy argument. The abstract two-point observation explains why nonconstancy alone would not close the capacity argument. A useful next bound must control the actual joint loads at the relevant levels and force mass into a region of positive joint capacity, or supply another sufficient same-family inequality. Neither of these examples provides or disproves such a bound.

## Exact verification

The [standard-library checker](../../frontier/cover-geometry/constant_survivor_query.py) reconstructs the table, enumerates all315 original integers, verifies the complete query, its partition, every original private region, comparable-class disjointness and all cylinder maxima. It also checks the full-Haar histogram and the rational constants in the seven-prime CRT extension. The latter uses the proved product formula; it does not claim enumeration of the14549535-point carrier.

The [result data](../../frontier/cover-geometry/constant_survivor_query.json) retain the final input and exact outputs. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/constant_survivor_query.py
```

Optional `--output PATH` writes the JSON to a file. Checks raise explicit exceptions and remain enabled under optimization. No source geometry producer or Lean build is part of this finite verification.
