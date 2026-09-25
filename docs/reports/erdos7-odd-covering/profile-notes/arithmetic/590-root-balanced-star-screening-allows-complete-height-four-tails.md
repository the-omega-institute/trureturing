# Root-balanced star screening allows complete height-four tails

Let P={3,5,7,11,13,17,19} and P9=P union {23,29}. Every finite family
of pairwise distinct nonunit numerical moduli supported on P9 has
positive survivor density if each P-supported mixed modulus is either
squarefree or has at least one prime exponent at least 4. All pure
prime-power originals, and all originals touching 23 or 29, are
unrestricted. Each numerical modulus has one arbitrary globally fixed
residue. The uniform lower bound is

    H(full survivor) >=
      53315162291526157368887/9812119286285355207168000
      =0.005433603152995306... >1/185.                 (RS1)

Here mixed means supported on at least two primes. The exponent
condition does not bound the modulus, the number of originals, or any
original height. Section 6 also permits additional P-supported mixed
originals of maximum exponent 2 or 3 with total weight at most 3/40,
and gives survivor density greater than 1/19000.

This is ordinary mathematics with exact rational verification, not a
new Lean result or a resolution of unrestricted Erdős #7. The remaining
scope includes unrestricted low mixed powers and support primes beyond
29. The one probability constructed below is fixed before all query
phases; no individual query selects a different law.

## 1. Existing tools and the added joint estimate

[Report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md)
uses complete pure-survivor product conditioning and a weighted mixed
inventory. [Report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md)
already treats the six numerical labels 3q jointly through their common
ternary root. [Report569, SD15--SD16](569-complete-suffix-debits-close-the-six-prime-query-target.md)
continues a single raw survivor law through arbitrary originals
touching 23 or 29, retaining its actual unit mass.

Here the pure-survivor source gives equal mass to each retained first
digit. Avoidance of the six stars is then retained in every remaining
original-support estimate AND every query-support estimate. Their
deletion and query costs use the same ternary partition. Complete
geometric exponent tails are summed, giving the quantified class above.
The squarefree-only consequence is already supplied by the selected
two-phase route of Report569 and
[Report572](572-compatible-fibres-lift-one-six-prime-query-law.md);
that consequence is not claimed as a new result.

## 2. One root-balanced law for arbitrary complete pure inventories

Use product p-adic Haar probability H_P. Since the actual family is
finite, all original events are finite cylinders; their Haar survivor
mass is the ordinary surviving fraction modulo the family LCM.

For each p in P choose an excluded first digit b_p: use the actual
pure-p residue if that original is present, and any fixed digit
otherwise. For each other first digit r, let S_(p,r) be that root
intersected with the survivor of ALL actual pure p-power originals.
At most one forbidden cylinder occurs at each positive height. Within
this root the deeper forbidden relative mass is at most

    sum_(e>=2) p^(1-e)=1/(p-1).

Thus S_(p,r) has root-relative Haar mass at least (p-2)/(p-1)>0.
Define rho_p by assigning mass 1/(p-1) to each such root, distributed
there as normalized Haar on S_(p,r). Put rho=product_(p in P) rho_p.
This SINGLE probability avoids every actual pure original. Excluding
an extra root when pure p is absent is allowed: only support on the
actual survivor, not full support there, is needed.

Every cylinder of height e>=1 has rho_p mass at most

    c_p(1)=1/(p-1),
    c_p(e)=1/[(p-2)p^(e-1)],  e>=2.                    (RS2)

The height-one live cylinders have exactly that mass. Also

    rho_p <= p/(p-2) H_p,
    sum_(e>=1)c_p(e)=1/(p-2).

For a P-supported modulus m define c(m)=product_(p|m)c_p(v_p(m)).
The product source therefore satisfies

    rho<=D H_P, D=product_p p/(p-2)=1729/135,
    R_P(rho)<=N=product_p (p-1)/(p-2)-1=3161/935.       (RS3)

For any positive finite measure mu, the complete nonunit query norm is

    R_P(mu)=sum_(d>1, P-supported) max_(a mod d) mu([a]_d).

Every query height, occupied numerical label, and unused numerical
label occurs. RS3 proves convergence. Bounds below hold for each
residue separately on the same measure, hence also for this norm.

## 3. Fix the six stars, including any auxiliary deletions

Let Q=P without 3. For each q in Q, retain its actual 3q event if it
has positive rho mass. If it is missing or has zero rho mass, fix one
auxiliary 3q event using a retained ternary root and a retained q-root.
This replaces no positive-mass original. The six fixed live events
are E_q; set J=union_q E_q. Every actual 3q event is contained in J
up to a rho-null set.

Write r_0,r_1 for the retained ternary roots, and partition Q into
A_0,A_1 according to the ternary root of E_q. All auxiliary choices
and this partition are fixed before queries. Independence across
prime coordinates and the exact first-digit masses give

    rho(J)=b_star(A)
      =1-[product_(q in A_0)(1-c_q(1))
           +product_(q in A_1)(1-c_q(1))]/2.           (RS4)

There are 64 possible partitions; swapping the two groups preserves
all following bounds.

For a nonempty support S subset P put

    f_j(S)=product_(q in A_j without S)(1-c_q(1)),
    screen_A(S)=(f_0(S)+f_1(S))/2,  if 3 not in S,
                max(f_0(S),f_1(S)), if 3 in S.

For EVERY cylinder C with numerical support S,

    rho(C intersect J^c)<=screen_A(S)c(m).             (RS5)

To prove RS5, drop all star-avoidance requirements on coordinates
belonging to S. The remaining q-coordinates are independent of C.
If 3 is absent from S, average over its two roots, each of mass 1/2.
If 3 is in S, C fixes that root; bound its outside-S avoidance by the
larger f_j. The cap c_3(v_3(m)) already includes the ternary root
mass, so there is NO second factor 1/2 in this case. A cylinder on
an excluded root has zero mass and also satisfies the inequality.

Let U be the full actual P-supported survivor and define explicitly

    eta=rho restricted to (U intersect J^c).          (RS6)

The auxiliary deletions matter in RS6: eta is not asserted to be rho
restricted merely to U. It is supported on U, obeys eta<=rho|J^c,
and retains density at most D. This makes the query use of RS5 valid
even when some actual stars were absent or rho-null.

## 4. Complete original tails and queries use the same partition

For H>=2, the total cap of exponent vectors on a fixed mixed support
S with at least one exponent at least H is exactly

    t_H(S)=product_(p in S)1/(p-2)
       -product_(p in S)[1/(p-2)
                -1/((p-2)(p-1)p^(H-2))].             (RS7)

Indeed the bracket subtracts the full e>=H geometric tail from the
full e>=1 sum. Every numerical exponent vector is counted once;
there is no height cutoff or replacement of repeated prime supports
by one original label.

For a family in the class of RS1, the union bound AFTER star avoidance
gives s=eta(1)>=1-b_4(A), where generally

    b_H(A)=b_star(A)+sum_(S subset P, |S|>=2)
       screen_A(S)[sf(S)+t_H(S)],

    sf(S)=0,                  if S={3,q} for some q,
          product_(p in S)1/(p-1), otherwise.          (RS8)

The sf term covers each squarefree nonstar original; the star labels
were charged exactly in RS4. For H=4 the tail is disjoint from this
squarefree part. Missing originals can only improve the bound.

Apply RS5 also to every query cylinder, including pure queries, and
sum the complete height series. Since eta<=rho|J^c,

    R_P(eta)<=Q(A)
      :=sum_(empty != S subset P)
           screen_A(S) product_(p in S)1/(p-2).       (RS9)

This is a bound on queries of the actual restricted measure eta, not
a new probability or a sum of independently chosen source laws.

Put G=566/49. Exact evaluation of the 64 fixed partitions gives

    max_A b_4(A)=55858334259429305368613
                  /82085191914103297920000
                =0.6804922173768119...,

    delta=min_A [G(1-b_4(A))-Q(A)]
         =53315162291526157368887
                  /60942036421076690880000
         =0.8748503565444886...>0.                   (RS10)

The largest deletion bound occurs at A_0={5} or its complement.
The smallest joint margin occurs at A_0 empty or Q. These are
different optimizers; RS10 uses ONE partition inside each expression.
For every partition 1-b_4(A)>0, and

    max_A Q(A)/(1-b_4(A))=9.028838750990259...<G.

Keeping only the older unscreened query bound N in RS3 would give
the weaker uniform normalized bound 10.5811152246288...<G. RS9
retains more of the same star-avoidance information without requiring
an extra assumption on the original phases.

## 5. Continue through 23 and 29 on the same raw measure

Independently condition the 23 and 29 coordinates on their complete
actual pure survivors. Their respective density factors are at most
22/21 and 28/27; their sums of positive-height query caps are at most
1/21 and 1/27. Keep eta unnormalized, with mass s and query norm R.

Originals touching exactly one of these primes have total charge at
most R/21+R/27. Those touching both have charge at most (s+R)/567:
the old unit cofactor has its ACTUAL mass s. This is precisely the
raw continuation of Report569 SD15, with no independence assumed
among the coordinates inside eta. Hence the remaining raw mass is
at least

    s-R/21-R/27-(s+R)/567=(566s-49R)/567
      >=49 delta/567>0.                              (RS11)

Its density relative to full P9 Haar is at most D*616/567. Dividing
RS11 by this density yields 49 delta/(616D), which is RS1. The full
survivor contains the support of this submeasure, including the case
where auxiliary stars deleted additional legal points.

## 6. Additional shallow mixed originals

Let E be the inventory of additional P-supported non-squarefree
mixed originals whose largest exponent is 2 or 3. All of their phases
remain arbitrary and fixed. Define

    v=sum_(m in E)c(m).                               (RS12)

Begin with the construction for the base family, then delete these
actual extra classes under the SAME eta. Their raw deletion is at
most v; the raw query norm cannot increase. Thus RS10 becomes

    Gs_new-R_new>=delta-Gv.

The sufficient condition is

    v<delta/G=53315162291526157368887
                  /703942706414885857920000
             =0.07573792839342747... .                (RS13)

In particular v<=3/40 suffices and gives

    H(full survivor)>=519459310409718024887
                  /9812119286285355207168000
        =0.000052940582483111405...>1/19000.               (RS14)

Using sum_(m in E)screen_A(supp(m))c(m) instead of v is a valid
sharper variant if its partition is kept fixed throughout.

Consequently any covering supported on P9 would need a P-supported
shallow mixed inventory with weight at least delta/G. This necessary
condition concerns possible covers in this support range; it does
not reduce unrestricted #7 to a finite search.

## 7. Verification and remaining boundary

The retained exact producer is
[screened_root_profile.py](../../frontier/cover-geometry/screened_root_profile.py),
with its [rational results](../../frontier/cover-geometry/screened_root_profile.json).
It checks all 64 partitions with full geometric tails, compares the
star union formula with independent inclusion-exclusion, and retains
the original-loss and query bounds together in each partition.
It also checks the complete support-tail identity, the continuation
constants, both density lower bounds and the extra shallow budget.

The same displayed envelope with H=3 has negative minimum joint
margin. This is failure of this sufficient certificate, not a covering
example or an impossibility result for actual survivor measures.

The useful remaining work is to control arbitrary mixed exponents
2 and 3 by their actual shared phases, then construct a continuation
uniform over additional support primes. Arbitrary pure heights and
all deeper mixed exponent vectors are already included here; they
must remain included in any proposed strengthening. No claim is made
that every older instance-specific certificate fails on this class,
or that the underlying conditioning and union methods are new.
