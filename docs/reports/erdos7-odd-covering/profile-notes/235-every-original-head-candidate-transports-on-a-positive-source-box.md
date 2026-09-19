[Index](../marked_head_profile.md) · [Pruning](233-explicit-pruning-errors-preserve-all-four-face-ceilings-near-the-source.md) · [All retained duals](234-every-retained-dual-transports-on-a-generated-small-source-domain.md)

# Every original head candidate transports on a positive source box

All four original225/226 heads now have complete bounds on the actual source
rectangle sigma<=10^-8,rho<=10^-11, with common wrong-slot gap G=1/60.
The original two/four/six candidates, retained joint duals, and raw-prefix
certificates are all included. Each test still covers all62,500,000 containing
choices. Every independent original modulus and complete infinite tail remains.

| Original test | Complete hinge upper | Additive allowance over its face ceiling |
| --- | ---: | ---: |
| heavy0 |5.380649767170394|3.2496662095716994e-7|
| heavy16 |4.299573358337564|2.596755984763695e-7|
| AP13 |0.18159247697469302|6.841751019795985e-8|
| AP11 block0 |0.16328068494538608|6.841916984710830e-8|

Decimals present exact rational certificate values. Heavy costs still require
their original constant times actual survivor mass outside these hinge bounds.
This result does not by itself give a complete52-cost or global K comparison.
It is an ordinary mathematical and exact-rational result, with no Lean or
unrestricted Erdos7 resolution asserted.

## 1. Preserve every candidate in the original minimum

For a fixed original test and a fixed original containing branch b, let V_i(b)
be its face candidate values, with i among two,four,six,joint,prefix whenever
that candidate is available. Original225/226 checks establish

    min_i V_i(b)<=M,

where M is that test's complete face ceiling. Suppose each candidate has a
proved actual-source transport bound objective(b)<=V_i(b)+e_i. Then

    objective(b)<=min_i[V_i(b)+e_i]
                 <=min_i V_i(b)+max_i e_i
                 <=M+max_i e_i.                              (HC1)

For a branch pruned after four or six projections, use max(e2,e4) or
max(e2,e4,e6), respectively. Its recorded face value is the minimum of the
available candidates, not the last candidate alone. Source233 handles all
three pruned classes, and234 handles every retained joint-dual residual and
its complete tail. The maximum in(HC1) also includes these errors on expanded
branches, since a previously computed two/four/six value can still win there.

There are no prefix-pruned branches in the four scans. Nevertheless each
heavy scan records seven prefix-available calls, including its seed. These
prefix bounds can participate in the final minimum. Their transport is
therefore necessary; prefix_bounded=0 is not a reason to discard them.
The two survival scans have no prefix-available calls.

## 2. The twelve original raw-prefix certificates

The complete set of used prefix keys is exactly the twelve-key original209
raw-source bank. Its matrix has400 raw masses,25 independently normalized
projection weights,132 inequalities and four equalities. The inequalities
are25 node caps, three group budgets,100 projection-profile rows and four
raw CRT caps. This same raw matrix is retained as the first132 constraints
of the later systems.

Let p_i>=0 be one such certificate's inequality prices. Its four free
equality prices multiply projection normalizations, which remain exact.
The four CRT caps also remain exact. Only raw node/group caps and18 raw
profile coefficients move on the actual source rectangle.

For the current original nonnegative hinge vector a, put

    H6=sum_t a_t*(6-t)_+,
    MH=sum_t a_t*(6+min(t-1,4)-t)_+.

The prefix retains k_t=min(t-1,4) selected labels at threshold t. Thus MH
bounds its entire old-coordinate hinge at every raw atom. The unit-seven
increment is unchanged; its complete geometric continuation remains inside
the original raw objective. With234's density increment

    Dw_cs=(d/5)*I_(c!=0)+q5*I_H+q15*I_(root1,H),

the objective change is at most MH*sum_cs Dw_cs*X_cs. There is no independent
raw-measure change charge in addition to the raw constraint residual below.

The same four independently normalized profile families give230's payments

    P25=(d/450)*max_(s!=P)p_(28+s),
    P75=(d/450)*max_(s!=P)p_(78+s),
    P27=max_c[v_ROOT(c)*p_(53+5c+Q)]/27,
    P81=max_c[v_ROOT(c)*p_(103+5c+Q)]/81.          (HC2)

Each maximum belongs to its own simplex; independent original residues are
preserved. Set Cprofile=P25+P75+P27+P81. For the fixed raw containing polytope
Pbar on this source rectangle, define

    J(q)=max_(X in Pbar) sum_i
               [p_i+p_(25+group(i))+MH*Dw_i(q)]*X_i
         -sum_i p_i*r_i^face-sum_g p_(25+g)*B_g^face. (HC3)

This is exactly the sum of the node/group constraint residual and the
objective movement, optimized on one actual-source relaxation. The four
unchanged CRT constants belong in the original dual RHS check but have zero
transport residual; they are not subtracted again in(HC3).

## 3. The whole deletion credit and complete tail use the same budget

Source233's public deletion_tail_data supplies the full H-dependent deletion
error Cdel, complete six-projection assigned-tail error Ctail, four tail counts
P3,P5,P15,P45, and shifted primitive prices

    L=(P3+H6/9, kappa*P3,
       P5+H6*Cbar, P5+H6*(1+tbar),
       P3+H6, kappa*(P3+H6),
       P3+P5+P15+P45+MH).                       (HC4)

The complete original prefix candidate subtracts D_H once; its possible loss
is paid by Cdel and the deletion part of(HC4). It does not subtract a second
credit from a retained survivor. The old-hinge W payment is MH once. The raw
unit-seven increment requires no W payment.

The first two coordinates in(HC4) are Y5=E5-G*q5 and Y15=E15-G*q15.
In particular H6/9 is already a shifted price from228(JT6). Only the full
pure-three tail adds the explicit wrong-slot term G*P3*(q5+kappa*q15).
For the same seven-coordinate residual, a uniform prefix transport error is

    Eprefix=max_q [Cprofile+Cdel+Ctail+J(q)
                      +G*P3*(q5+kappa*q15)
                      +(R-G*(q5+q15))*max L],     (HC5)

where q ranges over(0,0),(R/G,0),(0,R/G). The raw feasible polytope is fixed,
so J is a support function with affine q coefficients and is convex. The
remaining terms are affine; their maximum on the whole triangle is bounded
by these three vertices. Nonnegative residual prices allow actual rho to
increase to R. No convexity of an LP with moving constraints is asserted.

Each of the twelve raw-prefix certificates is paired with each heavy test
when bounding errors. This only enlarges a residual supremum. The original
raw objective RHS stays attached to its actual source-bound test; no maximum
of unrelated objective values is used. The two prefix error maxima are
1.500417775401692e-7 and1.2135681740066063e-7, both below the corresponding
six-candidate transport allowance.

## 4. Complete head consumer and validation

The helper complete_small_retained_heads.py reads canonical233/234 outputs
and original225/226 scan data through certificate_io. It checks the original
raw matrix, all twelve used keys, the exact source rectangle, matching test
coefficients, complete face ceilings and original branch inventories. It
then applies(HC1) with every available channel. The retained-joint allowance
comes from all9,084 duals in234, so missing per-key objective labels cannot
exclude a dual actually used by an original test.

An independent prefix audit recomputed all24 records and72 raw supports with
216 group breakpoint-dual optimizations, checking600 exact fields against
the helper. Node/group, CRT and equality contributions were checked separately.
The independent measure argument verifies objective movement, whole deletion,
W multiplicity, shifted wrong-slot terms and the fixed-polytope vertex rule.

The four complete heads still need the other three AP11 blocks, all other
original numerator costs, signed actual mass, the complete square and count
tail before entering the full K quotient. Complementary source regions and
the remaining fallback branch are independent obligations.
