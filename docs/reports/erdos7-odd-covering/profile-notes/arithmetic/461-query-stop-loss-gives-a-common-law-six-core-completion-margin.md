# Query stop-loss gives a common-law six-core completion margin

For a core on at most five odd primes, the existing ordinary source measure can be chosen once so that every complete nonunit cylinder query has expectation below 10. For a core on at most six odd primes, the same statement holds with 14. The corresponding normalized density caps are below 47 and 150. These statements hold for arbitrary actual phases and finite heights; queries do not determine the source measure.

Consequently the weighted distinguished-prime completion interface holds on cores of at most five primes for every disjoint parent prime at least 13, and on cores of at most six primes for every disjoint parent at least 17. Bare noncoverage for these ranges is already implied by the existing stronger finite-prime noncoverage results; the new deduction supplies a common measure and quantitative original-query completion control.

This is an ordinary mathematical deduction plus exact rational postprocessing under the source construction, convex-comparison and cached geometry premises of [Chapter30](../../problem-details/30-six-prime-prefix-measures-close-all-six-vertex-blocks.md) and [Chapter31](../../problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md), especially (SV16)–(SV24). These chapters attribute the construction to Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1; its source identity and local verification boundary are in the [library entry](../../../../../Library/Arith/schroeder2026nine.md). The [earlier linear comparison](460-joint-five-prime-moments-give-a-parent-seventeen-completion-margin.md) is strengthened here by retaining query stop-loss. No new Lean certification or unrestricted Erdős #7 result is claimed.

## A query-independent measure and its stop-loss bound

Use reference anchors 3,5 and respectively the first three or four later primes from 7,11,13,17. Keep the existing stage thresholds (2,4,4,8) and caps (3/2,5/3,3/2,2). Auxiliary completion preserves the original covered subset. Original query residues are not replaced by completed residues.

On all histories retain the normalized conditional kernels before deletion, obtaining the predeletion measure sigma. Its initial anchor support avoids the completed anchor family. Restrict this one final law to the source survivor set to obtain mu <= sigma. The deleted source events may include auxiliary completed or charged classes; their covered union contains the original forbidden union, so mu avoids every original class. This does not assert that auxiliary completion preserves each original forbidden phase. First-hit accounting supplies the same live-mass lower bound as sequential deletion. Neither law depends on a query layout.

Fix a finite period K resolving the core and all query depths. A complete query layout chooses one arbitrary phase for each divisor d of K, including d=1, and has load

    L(x) = sum_{d | K} 1_{x = a_d (mod d)} >= 1.

For every real t>=1,

    L-1 <= (t-1) + (L-t)_+.

Positivity and mu<=sigma give

    mu(L-1) <= (t-1)mu(1) + sigma((L-t)_+).                 (1)

Let R denote the source anchor reserve in 135-cell units, Delta_s the sum of the source's first s deletion costs, and D_s=R-Delta_s. Then

    mu(1) >= D_s/135.

It remains to upper-bound one complete query hinge under sigma. This does not require a positive deletion credit for every query.

## Why the retained source geometry bounds arbitrary query hinges

Apply source Lemma 4.1's ordered-increment comparison to f(z)=(z-t)_+ and reverse-integrate the later normalized kernels. This comparison permits arbitrary separately labelled cylinders, including different phases at the same depth. Each later prime q supplies its independent auxiliary comparison run J_q, with tails C_q/q^e. Independence is asserted only for these comparison runs.

At fixed auxiliary runs the number of later-coordinate exponent choices is

    M = product_q (1+J_q).

The unit query and the queries with no anchor part give baseline M. The remaining anchor queries aggregate into the same seven source categories 3,9,27,5,15,45,135, with coefficients

    M*(1,1,1+u,1+v,1+v,1+v,(1+u)(1+v)).

Source weighted aggregation applies because all labels have nonnegative weights and f is convex. Hence all original independent query phases are retained until the permitted common convex upper comparison. There is no assumption that actual phases maximize different pieces simultaneously.

The function f is nonnegative, so the source's relaxed anchor domain can replace the smaller initial anchor avoid-set. Write A0 for this comparison carrier's mass in 135-cell units, W for its full linear-load upper bound, and F(z) for its cached positive-part envelope, including the existing exact positive tail majorants. The normalized source comparison has full multiplier mean EM and probabilities pi(m). Then

    135*sigma((L-t)_+) <= N_s(t),

where

    N_s(t) = sum_{m<t} m*pi(m)*F(t/m)
             + (EM-sum_{m<t}m*pi(m))*W
             - t*(1-sum_{m<t}pi(m))*A0.                    (2)

For m>=t, the anchor load is at least one, so the hinge is exactly linear; the remaining multiplier mass and first moment suffice. Thus formula (2) is precisely the source's SV24 comparison, with every core nonanchor coordinate included in M rather than only the ones before a deletion stage.

At t=1 this simplifies to

    N_s(1) = EM*W-A0.

The subtracted quantity is the relaxed comparison carrier mass A0, not the reserve R. This is legitimate because the positive hinge was first dominated on the enlarged anchor carrier. It is not an assertion that sigma(1)=A0/135.

Combining (1) and (2), the one normalized survivor measure satisfies

    muhat(L-1) <= t-1+N_s(t)/D_s.                          (3)

Since (3) holds for every complete layout, choosing a maximizing phase for each divisor gives

    sum_{1<d|K} max_a muhat(a mod d) <= t-1+N_s(t)/D_s.    (4)

The quantifiers are: for each finite original family and each fixed finite period resolving its core and query depths, there exists one law satisfying (4) for every layout on that period. The constants are uniform in these heights. The source comparison may enlarge finite inventories using nonnegative all-depth sums and their exact geometric remainders. The finite transport below does not assert projective compatibility between target laws separately chosen on increasing periods.

## One common anchor parameter throughout

The source has eight discrete charts (a,b,c), and in each chart the deeper pure-5 deletion varies over a simplex with four vertices j=1,2,3,4. R and A0 are affine in this parameter; each unrounded deletion-cost upper function and N_s(t) is convex. The latter follows directly from its positive hinge interpretation and positive remainder construction, even though its expanded formula contains a subtraction.

For one fixed threshold t and constant C>=t-1, verify at all four vertices of a chart that

    (C-t+1)(R-Delta_s)-N_s(t) >= 0.                       (5)

The left side is concave, so the vertex inequalities prove (5) throughout the chart. Upward-rounded source vertex deletion costs remain safe. No independently attained denominator/numerator optima or vertexwise minimizing thresholds are combined.

The exact consumer uses one threshold globally for each core size: t=4 for five cores and t=8 for six. It also reports all cached choices t in {1,2,4,8,12}, all at the same 32 vertices.

## Exact bounds

For five reference core primes, s=3 and EM=105/64. At t=4, the maximum right side of (3) is

    C5_exact = 354268696184847779107405
               /37639127656852367739093
             = 9.41224513529212... < 10.

For six reference core primes, s=4 and EM=945/512. At t=8 it is

    C6_exact = 8034293665870716452955503975561029997134562974
               /581858869356700257567944700688463416886232987
             = 13.80797662284221... < 14.

Both maxima occur at (a,b,c)=(2,4,1), j in {1,3,4}. The retained mass and density bounds are

    m5 = 1812390307/22500000000,
    muhat5 <= (84375000000/1812390307)*Haar < 47*Haar;

    m6 = 68006602781/1350000000000,
    muhat6 <= (10125000000000/68006602781)*Haar < 150*Haar.

The unnormalized density caps are respectively 15/4 and 15/2. These density and query bounds hold for the same measure.

Transport to arbitrary actual cores follows [report460](460-joint-five-prime-moments-give-a-parent-seventeen-completion-margin.md#transport-to-any-five-actual-odd-primes), using its random digitwise prefix injections unchanged: pullbacks preserve complete exponent vectors or are empty; source tests may be completed to full layouts; average unnormalized pushforwards, then normalize once. The inequality mu_F(L-1)<=C*mu_F(1) is linear before normalization. Haar domination is also applied before averaging. Pad smaller cores with unused odd primes, then project. The parent need not be larger than every core prime; it need only be disjoint from the core and satisfy its stated lower bound.

## Five-core parent 13 and six-core parent 17

Let S be the actual core survivor set, which contains the support of the transported law. For a distinguished prime r disjoint from the core and H resolving its original exponent heights, define the actual weighted mixed completion load by

    ell_{r,H}(x) = sum_{r^e d original, 1<=e<=H, 1<d|K}
                  r^(1-e) * 1_{x = a_(r^e d) (mod d)}.

This retains the original phases and excludes pure r powers. Its expectation is at most r/(r-1) times the complete nonunit query bound. The pure-power-reserved whole-cover threshold is

    B_{r,H} = r-sum_{e=1}^H r^(1-e) >= r-r/(r-1).

For five cores and every disjoint r>=13, use the conservative C=10. Then

    E ell < 65/6,
    B_{r,H} >= 143/12.

The actual good core set A5={x in S : ell_{r,H}(x)<=23/2} has

    muhat5(A5)>4/69,
    Haar(A5)>4/(69*47)>1/1000,
    ell <= B_{r,H}-5/12 on A5.

For six cores and every disjoint r>=17, use C=14. Then

    E ell < 119/8,
    B_{r,H} >= 255/16.

The actual good core set A6={x in S : ell_{r,H}(x)<=31/2} has

    muhat6(A6)>5/124,
    Haar(A6)>5/(124*150)=1/3720>1/4000,
    ell <= B_{r,H}-7/16 on A6.

Conditioning Haar on the selected actual good set yields one law with density below 1000 or 4000, respectively. It is chosen from the actual whole family, not separately for later query events.

The height-independent tail bridge of [report455](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md), in its distinguished-prime form from [report458](458-distinguished-prime-completion-removes-the-early-phase-restriction.md), retains the auxiliary cut min(H,floor(log_3 q)); the actual original moduli remain r^e a b. The weights obey r^(1-e)<=3^(1-e). It uses

    five: Lambda=1000, J1<=1001/384, J2<=7007/480, N=14598;
    six:  Lambda=4000, J1<=17017/6144, J2<=357357/20480, N=69797.

For every finite outside-prime set disjoint from rK and above B>=3^256*N^3, the common-law weighted tail cost is at most 324*Lambda*J1/B < 3^-250. The two numerators 324*Lambda*J1 are respectively 3378375/4 and 57432375/16. The final global conditioning may change the core marginal, but it stays supported on A5 or A6, respectively. The pointwise core margin therefore survives, and the expected total weighted completion stays strictly below B_{r,H}. Consequently some actual r-free survivor has completion below that threshold and admits an uncovered parent fibre. No prescribed-marginal preservation is claimed. The existing bridge's actual-source, arbitrary-height and original-phase assumptions remain necessary.

## Seven-core boundary of the tested fixed schedule

Continuing the same source schedule through 19 gives a positive seven-core mass lower bound 7235955529/450000000000, but the best tested global query threshold is t=12 and yields

    103343946604764246206337485917871819126956334264872936209927316564663653460367
    /3628568478963635412888860196373754287816342698470144729653354897944434417502
    =28.48063835749369... >21.

Thus these five cached query thresholds with the retained seven-core deletion schedule do not reach the parent23 target. This is a limitation of these comparison bounds, not an actual-phase obstruction or a proof that no suitable common measure exists.

## Consumer inputs and scope

The [exact consumer](../../frontier/cover-geometry/query_stoploss_completion.py) and [rational data](../../frontier/cover-geometry/query_stoploss_completion.json) use the existing helper's cached-envelope and multiplier-distribution definitions without invoking its main producer. All three inputs are checked against exact SHA-256 pins:

| Input | SHA-256 |
| --- | --- |
| `six_prime_prefix_certificate.json` | `ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61` |
| `six_prime_prefix_geometry.json` | `0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1` |
| `six_prime_prefix_certificate.py` | `3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4` |

The retained geometry contains 72 batches and 51,840 existing integer query reads. The new optimized-mode consumer checks 480 rational query-bound rows: 32 basic vertices, three core sizes, and five fixed query thresholds. It also checks all selected common-parameter vertex inequalities, exact five- and six-core constants, density caps, positive good-set margins and tail parameters. The previous geometry enumeration and source producer were not rerun. These computations do not replace the ordinary mathematical source premises or certify their full arbitrary-height proofs.

From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/query_stoploss_completion.py
```

Output defaults to JSON on stdout; `--output PATH` selects a file. All new checks remain active under optimization.
