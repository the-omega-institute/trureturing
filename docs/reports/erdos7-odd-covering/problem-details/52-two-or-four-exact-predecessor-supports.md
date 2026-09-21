[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Two or four exact predecessor supports give noncoverage

For a finite family of pairwise distinct odd original numerical moduli
larger than one, assign each mixed original class to its last prime in
a specified order. At that prime, its exact predecessor support is the
set of all other primes in the original modulus. All original exponent vectors and residues remain separate labels
within their support groups.
The hypotheses below count distinct support sets, not original classes.

The family is noncovering under either of these two sufficient conditions:

- Choose any prime order with 3 first when present; each assigned group
  has at most two distinct nonempty predecessor supports.
- Use numerical prime order; each assigned group has at most four
  distinct nonempty predecessor supports.

Both branches allow arbitrary original heights, residues, support size
and number of primes. Each constructs one full joint law with an explicit
positive survivor reserve and a complete Haar density bound including
the pure-power conditioning costs. Their order hypotheses are separate.
These are ordinary proofs with exact finite regressions, with no new
Lean declaration or resolution of unrestricted Erdős #7.

## Branch A: two exact predecessor supports in an arbitrary prime order

Let a finite congruence family have pairwise distinct odd numerical moduli greater than one. Choose any prime order, with 3 first if present. Assign every mixed original to its last prime. If each assigned group has at most two distinct exact predecessor supports, the family is a noncover. Original heights, residues, support rank, and the number of primes are unrestricted.

Writing m for the number of nonempty assigned groups, H for full original CRT Haar, and U for the complete survivor set, there is one normalized joint law P_* such that

    P_*(U) > 277/13500,
    P_* <= D H,
    D=2^m product_(p in P)(p−1)/(p−2).

Consequently H(U)>277/(13500D), and conditioning once gives a survivor probability eta with

    eta <= (13500/277) D H.

In particular, this includes a fixed nonternary predecessor support
with optional3: the two possible exact predecessors are S and S∪{3},
omitting the empty possibility when mixedness forbids it. It does not settle unrestricted systems.

### Complete original probability bridge

Remove only actual pure p-power classes in each full coordinate, giving pure survivor mass s_p>=(p−2)/(p−1) and uniform survivor law nu_p<=c_p H_p, c_p=(p−1)/(p−2). Numerical distinctness gives at most one pure exclusion per exponent.

At assigned p use the half-threshold normalized capped kernel on the union F_p(x) of actual active p-prefixes at the full earlier word x. With alpha_p=nu_p(F_p), its density relative to nu_p is zero or 1/(1−alpha_p) in the alpha<=1/2 branch, and (2alpha_p−1)/alpha_p or 2 in the alpha>1/2 branch, on or off F_p respectively. The kernel is normalized, capped by 2, including at alpha=1. Unassigned primes sample nu_p directly. Put kappa_p=2 or 1 accordingly; kappa_3=1.

Backward conditioning therefore bounds each selected joint cylinder by product kappa_q c_q q^(−h_q), without independence or conditioning on full survival. Later kernels preserve the whole earlier joint distribution. The assigned violation mass is E(2alpha_p−1)_+<=E alpha_p^2.

For every exact nonempty predecessor support S in I_p, retain all original full exponent vectors and their residues. Expanding the actual load square, compatible paired cylinders at a common q intersect in one cylinder with maximum exponent. Distinct original numerical moduli give at most one label per full vector; completing the nonnegative exponent sums yields

    E alpha_p^2 <= b_p² sum_(S,T in patterns_p) W(S,T),
    b_p=1/(p−2),
    W(S,T)=product_(q in S∩T)d_q product_(q in S symmetric-difference T)t_q,
    d_q=kappa_q (q+1)/[(q−1)(q−2)],
    t_q=kappa_q/(q−2).

A common coordinate uses one cap, not its square. A coordinate present on one side only has a positive-versus-zero exponent sum. At 3, d_3=2 and t_3=1. For q>=5, d_q<=1 and t_q<1. Each support diagonal is at most 2. All original labels, pure conditioning costs and common sources are retained.

### Universal two-support Gram bound

Suppose every nonternary preceding prime is at least r>=5. Set

    D_r=2(r+1)/[(r−1)(r−2)],
    T_r=2/(r−2),
    K(r)=2(1+D_r+2T_r).

Then d_q<=D_r<=1 and t_q<=T_r<1. For two distinct nonempty supports S,T:

1. If both contain 3, remove 3 and choose q in the symmetric difference. One stripped diagonal is at most D_r, the other at most 1, and the stripped cross term at most T_r. Restoring 3 multiplies every term by 2. Their total is at most K(r).
2. If only S contains 3, choose q in the nonempty T. If q also lies in S, the two diagonals are at most 2D_r and D_r and each cross term at most D_r, giving 5D_r. Otherwise the diagonals are at most 2 and D_r and each cross term at most T_r, giving 2+D_r+2T_r. Both are at most K(r):

       K(r)−5D_r = 2((r−1)^2−6)/[(r−1)(r−2)] > 0,
       K(r)−(2+D_r+2T_r)=D_r+2T_r>0.

3. If neither contains 3, choose a symmetric-difference prime. The sum is at most 1+D_r+2T_r=K(r)/2.

One support is bounded by2<=K(r). An empty assigned group contributes zero. Thus every actual group satisfies E alpha_p²<=K(r)/(p−2)². In particular

    K(5)=20/3, K(7)=14/3, K(11)=154/45.

### Infinite prime sum and arbitrary ordering

The complete prime-square bound is

    S_all:=sum_(p>=5 prime)(p−2)^−2 <719/3600.

To prove it, every p−2 is 3 or 5 modulo 6. The first progression sums to pi²/72<5/36. For the second, convexity bounds its terms after the first by the centered-cell integral:

    sum_(k>=0)(6k+5)^−2 <= 1/25+integral_(1/2)^infinity(6t+5)^−2 dt
                          =1/25+1/48.

These add to 719/3600.

Initially charge every odd prime p>=5 by K(5)/(p−2)², including unused primes; all charges are nonnegative. Then:

- If 5 occurs before 7, or 7 is absent, all nonternary predecessors of 5 are at least 11. Replacing the charge at 5 by K(11)/9 gives total strictly below

      (20/3)(719/3600)−(20/3−154/45)/9 =1573/1620.

- If 7 occurs before 5, all nonternary predecessors of 5 are at least 7, and those of 7 are at least 11. Replacing both charges gives total strictly below

      (20/3)(719/3600)−(20/3−14/3)/9−(20/3−154/45)/25
         =13223/13500.

- If 5 is absent, deleting its entire initial charge gives total strictly below

      (20/3)(719/3600−1/9)=319/540.

The largest displayed bound is 13223/13500, so the actual joint union of all assigned violations has mass strictly below that value. An assigned group may be empty at 5 or 7: its actual fee is then zero, and the displayed positive replacement remains a valid upper bound. If 3 is absent, the Gram case without 3 suffices and the same upper bounds remain valid. No numerical ordering of the other primes is assumed.

The pure exclusions already have probability zero. The joint complement therefore has mass >277/13500. Multiplying all local density caps gives the stated full density D, including pure conditioning. Positive finite CRT mass yields an actual avoiding integer.

### Exact checks and scope

[predecessor_support_two.py](../frontier/cover-geometry/predecessor_support_two.py) (scalar checks) uses exact fractions and explicit exceptions. It checks each Gram bound on all 465 pairs of nonempty subsets of five coordinates, separately for r=5,7,11; every maximum equals the stated K(r). It also checks all three exact prime-order fees and the final reserve.

[predecessor_support_two.py](../frontier/cover-geometry/predecessor_support_two.py) (actual-family checks) independently constructs actual original CRT residues and the complete normalized joint law, using exact cell compression by original cylinder predicates. Its five fixtures cover:

- 7 before 5 with exact predecessors {3} and {7}, original exponent repetitions and a genuine completely killed fibre;
- 5 before 7, including a support pair with 3 on only one side and a shared nonternary coordinate;
- 5 absent;
- 3 absent and nonnumerical prime order;
- 7 absent, with two distinct predecessors both containing 3.

Every full earlier joint marginal, local normalization, original squared load, exact support Gram, actual survivor probability, paired-cylinder cap, and complete Haar-density estimate passes. This checker uses explicit checks that remain active under `python3 -B -I -S -O`. Its output contains exact actual moduli, residues, counts, probabilities and costs. These finite checks support the construction; the all-height theorem relies on the general argument above.

The normalized-kernel and selected-cylinder mechanisms are existing results in [Chapter07](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md)
(DG1–DG5, RK1–RK2) and
[Chapter08](08-arbitrary-head-transfer-by-the-joint-load-invariant.md) (T3–T6). The two-support Gram bound, order-sensitive small-prime charges, and resulting closed class are the additional ordinary deductions proved here. No historical-priority claim is made.


## Branch B: four exact predecessor supports in numerical prime order

Every finite family of congruence classes with pairwise distinct odd numerical moduli greater than one is a noncover if, upon assigning every mixed original to its numerically largest prime p, at most four distinct exact predecessor supports occur at each p. All original exponents, residues, support ranks and the number of primes remain unrestricted.

For full original CRT Haar H and the genuine complete survivor set U, the construction gives one joint law P_* with

    P_*(U) > 4763/408240,
    P_* <= D H,
    D = product_(p in P) kappa_p (p−1)/(p−2),

where kappa_3=kappa_5=1, kappa_7=5/3 if its mixed group is nonempty, and kappa_p=2 for assigned p>=11. An unassigned coordinate has kappa_p=1. Hence D<=2^m product_(p in P)(p−1)/(p−2), with m the number of nonempty assigned mixed groups, including a possibly nonempty p=5 group. The latter bound deliberately overcounts that unbiased stage.

Consequently H(U)>4763/(408240D), and conditioning once on U gives a survivor probability with full Haar density at most (408240/4763)D. The pure-conditioning product must remain in any reported full density.

This is an ordinary proof with exact rational certificates. It does not
assert new Lean verification or a solution of unrestricted odd covering systems.

### Probability bridge and the unmodified fifth coordinate

Remove only actual pure p-power exclusions in each full coordinate. Their survivor Haar mass is at least (p−2)/(p−1), since original numerical distinctness permits at most one pure label per exponent. Sampling its actual uniform survivors gives nu_p<=c_p H_p, c_p=(p−1)/(p−2).

At 3 and 5 sample nu_p directly, independent of the earlier word. The p=5 mixed originals have exactly the labels 3^a5^e, a,e>=1, each full tuple at most once. Under nu_3⊗nu_5 their actual union therefore has probability at most

    sum_(a,e>=1)c_3 3^(−a)c_5 5^(−e)=1/3.

This unmodified fifth coordinate and its first-moment cost are reused
from [Chapter41, FS3](41-natural-four-predecessor-orders-are-noncovering.md). The coordinate is not conditioned to avoid those mixed originals, and its conditional density remains kappa_5=1. Later normalized kernels preserve its whole joint earlier marginal and therefore its actual mixed violation probability.

At p=7 use threshold delta=2/5. At assigned p>=11 use delta=1/2. The normalized capped kernel has density relative to nu_p

- zero on forbidden points and 1/(1−alpha) off them when alpha<=delta;
- (alpha−delta)/(alpha(1−delta)) on forbidden points and 1/(1−delta) off them when alpha>delta.

Here alpha is the nu_p mass of the actual active original-prefix union at the entire earlier assignment. Every fibre, including alpha=1, is normalized. Its assigned violation probability is

    (alpha−delta)_+/(1−delta) <= alpha²/[4delta(1−delta)].

Backward conditioning of this single sequential law gives selected-cylinder bounds product kappa_q c_q q^(−h_q), without independence. Completing the injective full exponent tuples only after expanding the actual original-label load gives

    E alpha_p² <= b_p² G(E_p),      b_p=1/(p−2),
    G(E)=sum_(S,T in E) product_(q in S∩T)d_q product_(q in S△T)t_q,
    d_q=kappa_q(q+1)/[(q−1)(q−2)],
    t_q=kappa_q/(q−2).

E_p is the set of exact, nonempty predecessor supports. Common positive exponents count 2j−1 and pay one cylinder cap. The two current exponents contribute b_p². Numerical distinctness is used for full original vectors, never for projected cofactors.

The nominal upper factors are

| Coordinate | d | t |
|---|---|---|
|3|2|1|
|5|1/2|1/3|
|7|4/9|1/3|
|q>=11|at most 4/15|at most 2/9|

An unassigned coordinate has smaller factors. All nonternary factors are at most one, and the displayed factors are nonincreasing in numerical prime order.

### Four-support compression preserves the actual distinctions

Suppose at least one of the at most four predecessor supports contains 3. Add the empty support to the list of objects whose distinctions must be preserved. Retain coordinate 3 first; it partitions these at most five objects into at least two blocks.

If two objects still have equal projections, choose a prime in their symmetric difference. It is a new nonternary coordinate and splits at least one block. At most three such additional coordinates are therefore needed to make the projection injective. Because empty was retained as an object, every projected original support is nonempty; because all originals were retained, distinct supports remain distinct.

Deleting other nonternary coordinates increases or preserves every paired Gram term: it removes only factors d_q<=1, t_q<=1, or 1. Sorting the retained nonternary coordinates maps them monotonically to virtual 5, 7 and 11. The nominal factors at these virtual coordinates dominate the actual factors term by term. Completing fewer than four images by additional distinct nonempty subsets adds only nonnegative terms.

At p=11 the actual predecessors lie in {3,5,7}; all 35 choices of four of its seven nonempty subsets have Gram at most 169/18. At p>=13 the above compression reduces the problem to the 1365 choices of four of the 15 nonempty subsets of {3,5,7,11}; the same maximum 169/18 holds. Both maxima are attained by the support masks 1,2,3,5, namely {3}, {5}, {3,5}, {3,7}.

If none of the original supports contains 3, each diagonal is at most one. Every off-diagonal pair differs on a nonternary coordinate with t<=1/3, and all its other factors are at most one. Thus a four-support Gram is at most 4+12/3=8<169/18.

The four-support bound therefore holds for all p>=11, regardless of ranks and earlier primes omitted from the family. For p=7 there are only three possible nonempty predecessor supports, {3}, {5}, {3,5}. Their complete Gram under kappa_5=1 is 13/2. Missing any support decreases the bound.

### Small-prime costs and a proved infinite tail

The p=5 first-moment fee is at most 1/3. At p=7,

    E alpha_7² <= (13/2)/25,
    fee_7 <= [(13/2)/25]/[4(2/5)(3/5)] =13/48.

At p>=11 the half threshold gives fee_p<=G/(p−2)², so p=11 costs at most (169/18)/81.

There are exactly 42 primes from 13 to 211. For every later prime, p−2 is 3 or 5 modulo 6 and greater than 209. Its possible denominators are contained in the two sequences 213+6j and 215+6j. Convexity gives

    sum_(j>=0)(213+6j)^−2 <= integral_(−1/2)^infinity(213+6t)^−2dt =1/1260,
    sum_(j>=0)(215+6j)^−2 <= integral_(−1/2)^infinity(215+6t)^−2dt =1/1272.

The exact finite comparison is

    sum_(13<=p<=211 prime)(p−2)^−2 +1/1260+1/1272 <1/35.

It bounds the complete infinite tail; it is not a sampled extrapolation. Thus the union of all actual assigned violations has mass strictly below

    1/3+13/48+(169/18)(1/81+1/35)
      =403477/408240<1.

Pure violations already have probability zero. Every nonpure original belongs to exactly one stage, and later kernels preserve its prefix event probability. The complete joint survivor mass is therefore >4763/408240. Multiplying every local Haar-density cap and then conditioning once proves the full density statements.

If 3,5,7 or11 is absent, its actual cost is zero, while the displayed positive charge remains an upper bound. Likewise empty assigned groups contribute zero. The virtual-coordinate domination uses only lower bounds for ordered distinct primes, so missing primes cause no change in the proof. Positive finite CRT mass supplies an actual avoiding integer.

### exact verification

The [exact checker](../frontier/cover-geometry/predecessor_support_four.py)
uses only standard-library exact fractions and explicit exceptions active
under `python3 -B -I -S -O`.

Its scalar calculation checks:

- all 1+35+1365 relevant nominal Gram cases and their exact maxima;
- 30100 four-support projection cases in a five-coordinate universe;
- the full list of 42 primes from13 through211 and the exact positive tail slack;
- the exact fee403477/408240 and reserve4763/408240.

The projection tests support the general finite-partition proof, rather than replacing it. The retained certificate contains the full1365-row calculation.

Its actual-family calculation encodes genuine original CRT labels, compresses only by their exact cylinder truth patterns, and constructs the normalized joint law using actual pure survivors. It checks whole-prefix preservation, all fibre normalizations, actual stage losses, original squared loads, exact-support Grams, selected paired cylinders, genuine survivor counts and full Haar density. Five fixtures include:

- an explicitly unbiased p=5 with positive actual mixed loss 5/27, repeated exponents, four p=11 supports, and three completely killed p=5 fibres;
- four higher-rank supports whose ternary-present patterns 000,100,010,001 genuinely require three additional distinguishing coordinates;
- no3;
- no5;
- no7.

There are 628 exact actual pair-cylinder checks. The first fixture has complete period108056025,1680 exact compressed cells, genuine Haar survivor count31153815, and P_*(U)=527/648. Every original modulus and residue, all local costs, full probabilities, and density bounds appear in the retained certificate.

The additional deduction is closure under four distinct predecessor
supports, using the empty comparison object to preserve all distinctions,
the finite Gram bound169/18, and the complete prime-tail budget.
The unmodified fifth coordinate, normalized kernels, exponent-pair
expansion, selected-cylinder bounds and continuation interfaces are
reused mechanisms. No literature-priority claim is made.

This restriction differs from Chapter41's bound on the number of earlier
neighbour primes. Four distinct supports may involve arbitrarily many
earlier neighbours, whereas four earlier neighbours permit up to15
distinct nonempty supports. Neither hypothesis contains the other.


## A growing number of predecessor supports at sufficiently large primes

Use numerical prime order and let k_p be the number of distinct exact nonempty predecessor supports among the original mixed moduli assigned to p. Keep the same original finite family, actual pure-survivor laws, and kernel schedule as the four-support theorem: no mixed-class bias at5, threshold2/5 at7, and threshold1/2 at every assigned p>=11.

Suppose

    k_p<=4                 for p<=10^6,
    k_p^4<=p               for p>10^6.

There is no fixed uniform bound on k_p in this hypothesis. Then the original family is still a noncover. For the single joint law P_* constructed with that unchanged schedule,

    P_*(U) >381049/51030000>1/150.

Let D be the full pointwise density cap from the four-support theorem,

    D=product_(p in P) kappa_p (p−1)/(p−2),

where kappa_3=kappa_5=1, assigned7 has kappa_7=5/3, assigned p>=11 has kappa_p=2, and unassigned coordinates have kappa_p=1. Then H(U)>381049/(51030000D), and conditioning once gives a survivor law with full Haar density at most(51030000/381049)D<150D. All original heights, residues, and support ranks remain unrestricted.

**Proof.** The original-label squared-load bound uses the exact-support Gram

    G_p=sum_(S,T in E_p) product_(q in S∩T)d_q product_(q in S△T)t_q.

There are exactly k_p² ordered terms. Each term is at most2: a common ternary coordinate contributes2, a differing ternary coordinate contributes1, and all other factors satisfy d_q,t_q<=1 under the unchanged kernel schedule. Therefore

    G_p<=2k_p².

For p>10^6, k_p^4<=p gives k_p²<=sqrt(p). The half-threshold normalized kernel consequently charges an actual violation probability at most

    G_p/(p−2)² <=2sqrt(p)/(p−2)²
                =2[p/(p−2)]² p^(−3/2)
                <=(21/10)p^(−3/2).

The factor p/(p−2) decreases for p>2, and for every integer p>=1000001,

    2(1000001/999999)²<21/10.

Completing the prime sum by all integers n>10^6 and using the decreasing-function integral comparison gives the full infinite additional fee

    sum_(p>10^6 prime) fee_p
      <=(21/10)sum_(n>10^6)n^(−3/2)
      <=(21/10)integral_(10^6)^infinity x^(−3/2)dx
       =21/5000.

The prefix through10^6 satisfies the four-support hypothesis. Its actual violation cost is bounded by the existing full four-support budget403477/408240. Using that whole bound, including its now-unneeded tail allowance, overcounts the prefix cost and is safe. Later normalized kernels preserve every earlier prefix event probability, so the two costs refer to the same full joint law. Their sum is

    403477/408240+21/5000
      =1−381049/51030000<1−1/150.

All actual pure exclusions have zero probability. The union bound gives the positive complete survivor mass. Multiplying the same local density caps and conditioning once proves the full Haar claims. No independence of overlapping support events is used. ∎

The extra flexibility follows from the decay of the prime-stage cost; it does not assert a bound on k_p for arbitrary original families. The four-support checker also verifies the exact cutoff factor, additional fee and final reserve. The complete infinite-tail guarantee is the integral argument above, not finite sampling.


## Reproducing the exact certificates

The two complete outputs are retained as
[predecessor_support_two.json](../certificates/source_norms/cover-geometry/predecessor_support_two.json)
and
[predecessor_support_four.json](../certificates/source_norms/cover-geometry/predecessor_support_four.json).
From the repository root:

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/predecessor_support_two.py --check
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/predecessor_support_four.py --check
```
