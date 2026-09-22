[Index](../../marked_head_profile.md) · [Previous complete comparison](246-the-joint-j-heads-and-square-improve-the-complete-cost-comparison.md) · [Joint quadratic costs](247-two-original-j-quadratic-costs-share-hinges-and-factorial-head.md) · [Complete prime paths](248-the-complete-j-factorial-tail-retains-both-prime-paths.md) · [Joint AP11 blocks](249-all-four-complete-j-ap11-blocks-retain-the-same-marked-source.md)

# Joint quadratic, factorial and survival bounds improve the complete J comparison

On both entire actual saturated J faces, the complete original52-cost
comparison satisfies

    comparison <=437.955167237823267263897240767... .       (CJ1)

The improvement over246 is3.743516144802499269227708455... . All52
original costs, their positive weights, the signed actual mass, outside
square, four AP11 blocks, AP13 term and complete infinite count tail remain.
The new inputs are247's two complete quadratic bounds,248's complete
factorial bound and249's four complete AP11 bounds.

Exact independent moment witnesses give the outward decimal method bracket

    [437.9551672378111, 437.9551672378233].                  (CJ2)

The exact width is1.2109880846423054...*10^-11. This brackets the best
comparison of the specified independent scalar-moment method with the24
constraints below. It remains above403. These are new witnesses for the
updated constraint set; the previous246 method lower bound is not reused.
They do not assert actual-source attainment or a lower bound for methods
that retain additional joint information.

## Twenty-four uniform inequalities for each original test

Use246's actual source domain, raw mass1/4, survivor mass S=3/20 and
common late parameter theta in[1/135,1/90]. Retain all22 previous scalar
basis functions. Replace the complete Phi5 bound by248's

    <Phi5,mu><=6313/7200,
    Phi5(n)=(n-5)_+*(n-4)/2,                               (CJ3)

and replace the four AP11 bounds by249's exact inequalities. Their
original all-load functions, mean16/25, AP13 bound and count law are
unchanged. The square5539/1200 from245 and both heavy heads from244
remain available.

Add247's two further basis inequalities

    <(n^2-81/4)_+,mu><=126462508163303609/37800000000000000,
    <(n^2-9)_+,mu><=145684760666673439/37044000000000000.    (CJ4)

This gives24 basis functions b_j and bounds B_j, with exact mass and23
upper inequalities:

    <1,mu>=S,   <b_j,mu><=B_j for j!=mass.                  (CJ5)

Each source inequality is uniform over the original admissible tests.
Consequently all24 may be applied to the load of any one target, while
different target tests keep independently chosen original labels. Adding
(CJ4) does not identify the cost47 or cost48 test with another cost's test.

The consumer verifies the common geometry and full source closure. It
checks the four AP11 functions using their exact finite transitions and
affine continuations. It also reconstructs247's two complete identities

    (n^2-81/4)_+=(19/4)H4(n)+(17/4)H5(n)+2*Phi5(n),
    (n^2-9)_+=7*H3(n)+2*H4(n)+2*Phi5(n),
    H_t(n)=(n-t)_+,                                         (CJ6)

and retains each head's entire5089/7200 distinct-pair tail, with its
coefficient2. This verifies that(CJ4) bounds the original whole functions.
No finite factorial head replaces a complete moment.

## Every target has an exact envelope on all positive integers

For all52 original costs and seven outside targets, retain rational
coefficients y_j such that

    f(n)<=sum_j y_j*b_j(n), n>=1 integer,
    y_j>=0 for j!=mass.                                    (CJ7)

The mass coefficient is unrestricted because its measure is exact.
Integration gives U_f=sum_j y_j B_j. All59 envelopes are checked at
n=1,...,8 and on their entire affine or quadratic continuation from n=9.
For a quadratic gap the integer minimum lies at9 or at adjacent integers
to its vertex; the affine case requires a nonnegative slope. This checks
all remaining loads exactly, with no finite cutoff or numerical tolerance.

The certificate contains472 low-load inequalities,59 complete-tail
checks and163 nonzero coefficients. Each new target upper is at most its
246 upper;53 improve strictly. The canonical checker uses only Python's
standard library and exact rational arithmetic.

## Reassemble the entire numerator and denominator

Using the original positive cost weights w_i, signed mass coefficient cS,
outside-square coefficient cQ and offset C0, the complete numerator is

    Nbar=cS*S+sum_(i=0..51)w_i*U_(cost-i)+cQ*U_square
        =35.163234667050935598143822620... .                 (CJ8)

The largest weighted contributions are

| Original index | Weighted upper payment |
| --- | ---: |
|0|6.009969384412894...|
|41|4.253093314382117...|
|16|4.237926589829927...|
|47|2.982356984228751...|
|32|1.925148555705559...|
|7|1.751729486458242...|
|46|1.724638054253438...|
|1|1.538657309606221...|

All52 payments remain in(CJ8). With the recomputed AP11 envelopes,

    Tcount=(U_mean-S)/7986+S/87846=277/4392300,

    Ebar=S-U_H4/6-(sum_(e=0..3)U_(AP11-e)+Tcount)/7
        =535911669034918420973213/6345626086800000000000000
        =0.084453710588102157600518171... .                 (CJ9)

The scalar envelopes sharpen the last AP11 block slightly beyond its
direct249 input; hence this denominator is slightly larger than249's.
Mean, square and AP13 retain their exact complete bounds. Both(CJ8) and
(CJ9) are strictly positive, so C0+Nbar/Ebar gives(CJ1).

The remaining403 deficit in numerator units is

    (403-C0)*Ebar-Nbar=-2.952093577461836516608479605... .    (CJ10)

No missing cost, negative mass term or count outcome is assigned zero.

## New independent witnesses certify the updated method boundary

For each target f, the certificate retains a separate finitely supported
rational measure mu_f satisfying all24 constraints(CJ5). Their253
positive atoms pass1416 exact moment checks, including exact mass. Put
L_f=<f,mu_f>. Every valid independent envelope using only(CJ5) obeys

    U'_f >= sup_(mu satisfying CJ5)<f,mu> >= L_f.            (CJ11)

Substituting all L_f in(CJ8)--(CJ9) gives Nlo>0 and Ehi>0. Every valid
tuple of independent envelopes with a positive denominator has

    N'>=Nlo,  0<E'<=Ehi,
    C0+N'/E'>=C0+Nlo/Ehi
             =437.955167237811157383050817712... .         (CJ12)

The fixed signed mass, positive target weights and positive denominator
deductions justify this monotone substitution. The witnesses for different
targets need not coexist on a single actual source. They certify the
limitation of this independent method, without claiming that an actual
covering family attains the lower endpoint or that richer source methods
are similarly limited.

## Exact artifact and scope

The [consumer](../../frontier/j-geometry/j_face_combined_complete_moment_cost_comparison.py)
and [certificate](../../certificates/source_norms/j-geometry/j_face_combined_complete_moment_cost_comparison.json)
retain75 source pins, all24 basis bounds, all59 envelopes and new witnesses,
the full cost inventory, signed formula, infinite-tail checks and exact
method bracket. The canonical verifier recomputes the complete consumer;
its pinned predecessor certificates carry the separate source scans.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_combined_complete_moment_cost_comparison.py --check
```

This result improves the complete comparison on the saturated actual J
faces. It remains above403 and supplies no off-face extension, unrestricted
Erdos7 resolution, actual-family attainment claim or Lean verification.
