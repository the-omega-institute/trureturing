# Charged shallow deletions lower the actual-source upper bound

For the fixed worst completed chart of
[report509](509-finite-height-zero-edges-strengthen-the-global-support-bound.md),
the same actual source nu satisfies

    nu({x:later-fibre survival s(x)=0}) <= U_source,
    U_source = 0.016385256975953152... .                  (S1)

The exact fraction is retained in the accompanying result JSON. Compared
with the previously used source upper Uzero, the strict improvement is

    Uzero-U_source = 0.0000007693170470521132... .         (S2)

This uses the old rational row prices unchanged. It retains shallow
deletions already present in the actual source but released in the old
profile comparison. It is not a new upper bound on arbitrary auxiliary
supports measured with the old eta weights.

The source lower bound remains m7=7235955529/450000000000, and

    U_source-m7 = 0.0003053558003975962... >0.             (S3)

Thus the same-source contradiction to coverage remains unproved. The
result concerns the declared two-centre, seven-old-prime and two-new-prime
interface. These are ordinary deductions and exact rational checks, not
a Lean verification or an unrestricted Erdős#7 conclusion.

## The source already carries these deletions

Keep the actual charged completion of
[report466](466-randomized-completion-retains-full-original-survivor-support.md)
and its unchanged mass and density bounds from
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
This is one fixed completion and one fixed charged choice throughout the
comparison. The source construction and its premises retain the attribution
to Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*,
edition1.0.1, recorded in those reports and the library entry.

The initial3/5 measure is bounded above by Haar on the existing chart A6,
the complement of

    0 mod3, 1 mod9, 4 mod27, 0 mod5, 1 mod25, 2 mod15.

Its mass is221/675. Keep the later-reference paths(2,7) on3 and(3,4) on5,
split7, and common11/13/17/19, exactly as in report509. The normalized
conditional density caps are(3/2,5/3,3/2,2,9/5); nu<=(27/2)H_old and
nu(1)>=m7 still refer to this same source.

The completed classes21,35,63,105 are present. After normalizing the
selected pure7 root to0, their7 targets are nonzero. At a3/5 history h,
let s4(h) count their active projections. The charged rule deletes a
size-s4 set of nonzero7 roots containing all active targets, in addition
to root0. Therefore its live7 subkernel kappa_h obeys

    kappa_h <= (3/2)H7,
    kappa_h(1) <= min(1,3(6-s4(h))/14).                 (S4)

These bounds concern the existing charged process; no additional deletion
or new source law is introduced here. Deeper pure and mixed deletions only
decrease the live subkernel.

The completion chooses each selected class outside previously selected
proper-divisor classes. Consequently its three projections

    a=r21 mod3, b=r35 mod5, c=r63 mod9

belong to

    Phi={1,2} times {1,2,3,4} times {2,4,5,7,8}.        (S5)

This has40 elements. A redundant original selected class is moved into its
free set by the stated source completion. The residue c=4 must be kept:
27 does not divide63. No compatibility between different projected classes
is discarded by restricting to a smaller domain; S5 is an upper relaxation
of all their actual legal choices.

Fix one global phi=(a,b,c) before integrating and define

    s3(h)=1_{h3=a mod3}+1_{h5=b mod5}+1_{h3=c mod9},
    c_phi(h)=(3s3(h)-4)_+/14.                          (S6)

Since s3<=s4, (S4) implies kappa_h(1)<=1-c_phi(h).
The105 projection is released on the upper side, without choosing it anew
at different histories.

## A smaller positive comparison at7

The old split7 comparison J7 has mass4/7 at the baseline profile0 and
mass9/7^f at each signed profile +f,-f, for f>=2. It is a probability;
the two nonbaseline tails together have mass3/7.

Let f be a nonnegative bounded response increasing in the labelled-box
order, after reverse integration over common11/13/17/19. Its value f0
at split7 baseline0 is its minimum. By (S4) and (S6),

    integral f d kappa_h
      =f0*kappa_h(1)+integral(f-f0)d kappa_h
      <=(1-c_phi(h))*f0+integral(f-f0)d J7
      =integral f d[J7-c_phi(h)*delta_0].               (S7)

The tail comparison in the middle step uses the full-history density cap
3/2 and the nonnegative increments along each reference path. All three
possible nonzero credits are compatible with a positive comparison:
for s3=0,1,2,3 the credit is0,0,1/7,5/14, respectively, at most4/7.

An upward zero-survival profile set has the required monotonicity. Reverse
integration over the common coordinates preserves it. At3/5 the measure
is integrated exactly, so no monotonicity in h or in c_phi(h) is assumed.
Histories added by enlarging the initial source to A6 contribute only a
nonnegative upper comparison. Equality to a reference path is Haar-null
and nu-null and does not change the estimate.

## The new weights retain one common projection tuple

For a profile u=(u3,u5,u7,u11,u13,u17,u19), let eta(u) be its old weight.
Let E_(u3,u5) be its exact initial paired shell in A6, and write J_common
for the product of the four existing common-coordinate comparison weights.
Define

    d_phi(u)=0                                      if u7!=0,
    d_phi(u)=[integral_E c_phi(h)dH35]*J_common(u)    if u7=0,
    eta_phi(u)=eta(u)-d_phi(u).                        (S8)

These weights are nonnegative. The integral in S8 is exact because the
credit depends only on h3 mod9 and h5 mod5; the initial anchor exclusions
are resolved modulo27 and25. Deeper shell tails are summed geometrically.

The full mass of the new comparison is

    221/675-integral_A6 c_phi(h)dH35.                  (S9)

Therefore its complete Q>=39 overflow mass is S9 minus the weights of all
23408 profiles with Q<=38. This retains the entire infinite overflow,
rather than truncating it or charging only selected high profiles.

For this fixed phi, let z be the upward binary support generated by actual
zero-survival old points. Its Q<=19 coordinates vanish by the existing
single-fibre bound. The same report509 pair, clique, triple, four-point and
order rows A z<=b are valid. Use their unchanged nonnegative rational
prices y and retain the signed loads, including negative child loads from
order rows. Then

    nu({s=0})
      <=eta_phi(overflow)+sum_i eta_phi(i)z_i
      <=eta_phi(overflow)+y dot b
          +sum_i max(eta_phi(i)-(A^T y)_i,0)
      =U(phi).                                        (S10)

Only after this whole integration and dual evaluation is completed do we
take U_source=max_(phi in Phi) U(phi). This is a maximum over40 fixed
global tuples. Allowing a different tuple at each history would erase the
joint source constraint and would not prove S1 with these weights.

## Exact consumption and its limit

The maximum in S10 occurs at phi=(2,2,4). Its total comparison credit in
S9 is2/945. Only part of this credit improves the upper bound: some is
spent on already safe profiles or coordinates with zero positive dual
residual. Recomputing every signed residual and the full overflow gives
S1 and S2; subtracting2/945 directly from Uzero would be invalid.

As a check on the source credit, every phi has at least10/675 initial
Haar mass with s3>=2. If(a,b)!=(2,2), the21/35 projection intersection in
A6 has mass at least20/675. If(a,b)=(2,2), the63 projection overlaps21
by at least42/675 when c=2,5,8, or overlaps35 by at least10/675 when c=4,7.
Hence every total credit is at least(1/7)(10/675)=2/945. This does not
assert occupation of those histories by the surviving actual source;
it improves its valid upper comparison.

The new upper keeps all qualitative exact-zero constraints of report509.
It cannot be substituted for a bound on fibres with survival below a
uniform positive theta. Under a full covering, all actual old-only
survivors would have s=0, and U_source<m7 would contradict that covering.
S3 is positive, so this fixed-interface obligation and unrestricted#7
remain unresolved. Further selected source projections and actual phases
remain available for tighter comparisons.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/charged_seven_source_bound.py

The consumer pins the existing charged-source and report509 inputs,
reconstructs the original profile order, weights and dual upper, then
checks all40 fixed projection choices and all20076 signed residuals in
each. It verifies nonnegative revised weights and full overflow masses,
and compares its deterministic result with the adjacent JSON by default.
No new LP is used. Validity of the old rows is reused from report509;
S4–S10 supply the new ordinary source-comparison argument.
