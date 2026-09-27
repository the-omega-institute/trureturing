# Individual mixed budgets strengthen two-fibre noncoverage certificates

Two actual old survivors can jointly certify noncoverage even when neither
passes the single-fibre load bound. The certificate below keeps the individual
and joint capacities of the two new-coordinate axes **and** the individual and
joint mixed-deletion budgets. Its exact numerical relaxation is computable from
at most28 rational candidates; corner evaluation alone is insufficient.

For the specified opposite ternary roots with identical six-coordinate
valuation profiles, all additional positive cases have individual loads
between20 and38. There are81 unordered depth types, including23 equal-depth
types. Every such actual pair has total new-fibre survivor mass at least1/770.
These are ordinary mathematical deductions and exact rational checks, not Lean
certification. Existence of a useful actual pair in every remaining original
family is not proved, and unrestricted Erdős #7 remains unresolved.

## Original numerical labels and all six deletion bounds

Fix a finite family with pairwise distinct odd numerical moduli greater than
one. Let q,r be two distinct new primes, disjoint from the old coordinates, and
write m=q-1, n=r-1. Every later modulus is d q^j r^k with j+k>0. For each complete
numerical label its old residue is fixed once, either a mod d or b mod d; all
new-coordinate residues and finite heights are arbitrary. The selector may
differ at different pairs(j,k), even for the same d, but never changes with the
old point being tested.

Use one finite inventory of old cofactors containing all those in the family
and the unit cofactor1, adding it as a conservative bound if necessary.
For two actual old points x,y define

    A_d(z)=1[z=a mod d], B_d(z)=1[z=b mod d],
    Qz=sum_d max(A_d(z),B_d(z)),
    N=sum_d max(A_d(x)+A_d(y), B_d(x)+B_d(y)).       (IC1)

Thus max(Qx,Qy)+1<=N<=Qx+Qy: every summand of N dominates the corresponding
summand of either individual inventory, and d=1 contributes2 instead of1.
At each new exponent pair, the number of active
original labels at z is at most Qz, and their total activity at both points is
at most N. These inequalities concern the same fixed original family.

Let alpha_z,beta_z be the actual axis-union Haar masses in the q,r coordinates.
Let gamma_z be the sum of the mixed-cylinder Haar masses in that fibre. Summing
the geometric series over positive exponents gives simultaneously

    alpha_z<=min(1,Qz/m), beta_z<=min(1,Qz/n),
    alpha_x+alpha_y<=N/m, beta_x+beta_y<=N/n,
    gamma_z<=Qz/(mn), gamma_x+gamma_y<=N/(mn).      (IC2)

Distinctness is used at the complete numerical label d q^j r^k. The old unit
cofactor d=1, when present, remains in the inventory. No original phase is
optimized separately at x and y.

Within each old fibre, the untouched q and r Haar coordinates are independent.
The axis-survivor mass is therefore (1-alpha_z)(1-beta_z). Actual mixed deletion
is at most gamma_z and at most this remaining mass. Independence between x and
y is neither needed nor assumed.

## Exact optimization retaining the individual mixed budgets

The following numerical result allows any nonnegative real Qx,Qy,N. Define

    ax=min(m,Qx), ay=min(m,Qy),
    bx=min(n,Qx), by=min(n,Qy),
    A=min(N,ax+ay), B=min(N,bx+by),
    Gamma=min(N,Qx+Qy),
    I=[max(0,A-ay),min(ax,A)],
    J=[max(0,B-by),min(bx,B)].                      (IC3)

For t in I and u in J put

    rx=(m-t)(n-u),
    ry=(m-A+t)(n-B+u),
    f(t,u)=max(0,rx-Qx,ry-Qy,rx+ry-Gamma),
    K(Qx,Qy,N)=min_(t in I,u in J) f(t,u).          (IC4)

Then the full original later survivor masses satisfy

    s(x)+s(y)>=K(Qx,Qy,N)/(mn).                    (IC5)

**Proof.** The objective after mixed deletion is nondecreasing in each of the
two axis-survivor masses. Axis deletions can therefore be increased to spend
the full effective budgets A and B. In units1/m and1/n their feasible allocations
are exactly (t,A-t) and (u,B-u) on the rectangle I times J.

At a fixed rectangle point, the maximum abstract mixed deletion in units1/(mn)
is

    min(Gamma, min(rx,Qx)+min(ry,Qy)).

Subtracting this from rx+ry gives the maximum of
rx+ry-Gamma and (rx-Qx)_+ +(ry-Qy)_+. Expanding the latter positive parts gives
four affine expressions in rx,ry. Its last expression rx+ry-Qx-Qy is bounded
by rx+ry-Gamma, leaving exactly the four terms in IC4. Actual arithmetic
deletions obey these constraints, hence IC5. This is exact optimization of a
numerical relaxation, not an assertion that arbitrary optimizing capacities
can be realized by original congruence classes. In the original inventory
case IC1, Gamma=N. QED.

## A boundary reduction gives at most28 rational candidates

Although f is a maximum of bilinear expressions, its minimum is attained on
the boundary of I times J. To prove this, use residual coordinates

    X=m-t, Y=n-u, M=2m-A, L=2n-B,
    rx=XY, ry=(M-X)(L-Y).

At an interior point X,Y are positive. Along

    (X,Y) -> (X(1+epsilon),Y(1-epsilon))

the first residual becomes XY(1-epsilon^2), while the second becomes

    ry+epsilon[(M-X)Y-X(L-Y)]-XY epsilon^2.

Choose the sign of epsilon so its linear term is nonpositive, and extend in
that direction to the rectangle boundary. Both residuals are nonincreasing
along this segment. IC4 is nondecreasing in either residual, so the objective
does not increase. A degenerate rectangle already lies on its boundary.

On each boundary edge the four terms in IC4 are affine in the remaining
coordinate. The maximum is a continuous piecewise-affine function. A minimum
occurs at an endpoint, an intersection of two nonparallel affine terms, or a
constant segment whose endpoints have one of those forms. There are at most
six intersections per edge and four distinct rectangle corners: at most28
distinct candidates. Rational inputs give rational candidates and values.

Keeping only the joint mixed budget would replace IC4 by
(rx+ry-N)_+ and permit evaluation at the four corners. That weaker relaxation
can overallocate mixed deletion to one fibre. For(q,r)=(23,29):

| Qx | Qy | N | Exact K | One minimizing(t,u) |
|---|---|---|---|---|
|20|37|38|7|(20,29/2)|
|20|38|39|4/3|(20,52/3)|
|21|32|33|4/5|(21,31/5)|

The survivor lower bound is K/616. In particular K need not be an integer;
an integer lower-bound rule from the four-corner relaxation cannot be used.

## Opposite roots: the complete joint inventory

Take old primes P={3,5,7,11,13,17,19} and(q,r)=(23,29). Choose one finite old
period D resolving every old-only modulus and every later old cofactor,
including a factor3 if necessary.
Assume a,b differ modulo3 and agree at every nonternary precision used in D.
Let x lie in the a ternary root and y in the b root. Their matching ternary
depths vx,vy are truncated at v3(D).

Let Dx,Dy be their actual matching nonternary divisor sets, and write

    Cx=|Dx|, Cy=|Dy|, Ixy=|Dx intersection Dy|.

In terms of their coordinatewise truncated depths tp(z), these are products
of tp(z)+1 and of min(tp(x),tp(y))+1. With the full inventory d|D, literal
counting gives

    Qx=(vx+1)Cx, Qy=(vy+1)Cy,
    N=Qx+Qy-min(vx,vy)Ixy.                        (IC6)

At ternary exponent zero, the activity sum is Cx+Cy. At each positive
exponent, the two center choices serve opposite roots, so the maximum counts
the union of the corresponding divisor sets, subtracting their intersection
until min(vx,vy). This proves IC6 and also

    N>=max(Qx,Qy)+1.                              (IC7)

If all six nonternary depths agree coordinatewise, then Cx=Cy=Ixy=C and

    Qx=(vx+1)C, Qy=(vy+1)C, N=(max(vx,vy)+2)C.    (IC8)

Equality of the scalar products alone does not imply IC8.

## A finite actual pair supplies an uncovered integer

Let S be the actual old-only survivor set modulo D. If x,y belong to S and
their inventories satisfy K>0, IC5 makes at least one actual new-coordinate
fibre nonempty. The finite new constraints factor through some23^J29^K, so a
positive Haar mass supplies an actual surviving residue there. CRT combines
it with the corresponding old survivor x or y to give an integer avoiding
every original class.

This qualitative conclusion requires two actual old survivors, not a pair of
independently selected laws. It does not require the old pair itself to have
positive mass under a continuous source measure.

## Finite classification and completion-safe support restrictions

The single-fibre inventory bound already gives

    s(z)>=(616-51Qz+Qz^2)/616>0 for Qz<=19.

Consider additional pairs with min(Qx,Qy)>=20. K is nonincreasing in each
inventory bound: increasing a bound enlarges the original feasible set of
axis and mixed deletions. If max(Qx,Qy)>=39, the unit-label inequality after
IC1 gives N>=40. At the endpoint
(Qx,Qy,N)=(20,39,40), scaled axis allocations

    alpha=(20,20), beta=(18,22)

have residuals(rx,ry)=(20,12). Mixed deletions(20,12) satisfy both individual
caps and joint cap40, giving zero in the relaxation. Thus every additional
positive pair with the inventories IC1 must satisfy20<=Qx,Qy<=38. No agreement
between the two centers or between the two points is needed for this cutoff.
It describes this specific certificate, not every possible pair method.

For the same-profile case IC8, order vx<=vy. The complete search domain is

    1<=C<=19,
    1<=vx<=vy<=floor(38/C)-1,
    20<=(vx+1)C.

Exact evaluation gives81 unordered positive(C,vx,vy) types, of which23 have
vx=vy. Their smallest positive K is4/5, attained at(C,vx,vy)=(1,20,31), so
the uniform total-fibre lower bound on these types is1/770.

Under a hypothesized full covering, every old survivor must fail the
single-fibre test, and no pair of old survivors may have K>0. Within one
nonternary profile, IC8 and monotonicity make positivity downward closed in
vx,vy. If both roots have survivors in that profile, it is therefore enough
to test their least attained depths. This gives a necessary joint support
condition, not a characterization of which supports arise arithmetically.

The restriction is safe under auxiliary completion: deleting old survivors
cannot introduce a new positive pair. Conversely a useful pair in an actual
completed subset already gives survivors of the original family.

For a quantitative statement, let rho be a measure on actual positive pairs
whose two marginals are dominated by the same actual old source nu. Then

    integral s dnu >= (1/1232) integral K drho.

On the81 same-profile types this gives integral s dnu>=rho(1)/1540. It does
not construct rho. Full source support and separate query bounds alone do
not supply that coupling; compare [report475](475-two-center-density-and-query-bounds-lose-original-survivor-realizability.md).

An unconditional opposite-root pair-existence assertion is false: the legal
old class a mod3 removes the entire a root. The family is not a covering.
The single-center source argument in report475 handles that case and the case
of an unused mod3 label. It also applies to the freely chosen selectors here:
on the surviving root, cofactors divisible by3 cannot activate the excluded
center, while3-free cofactors have the same old phase at either center.
Every active later cofactor is therefore controlled by the other single
center. With an unused mod3 label, append one center class and construct the
source for that enlarged original family. In the remaining third-root case, proving
that a useful single fibre or actual pair must exist is still necessary.

## Verification and scope

The [standalone verifier](../../frontier/cover-geometry/two_fibre_individual_mixed_budgets.py)
and [exact result data](../../frontier/cover-geometry/two_fibre_individual_mixed_budgets.json)
enumerate the complete same-profile domain, the finite
candidate minima, their relation to the weaker joint-only mixed budget, and
literal finite CRT inventory controls. The boundary reduction, arbitrary
finite-height cutoff and passage from an actual pair to an original integer
are the ordinary arguments above. No original family is replaced by an
independently optimized reference, support or source law. The verifier checks
23821 natural inventory triples and595525 rational-grid points, including
independent mixed-flow and dominated-boundary constructions. Seven literal
CRT controls include distinct nonternary profiles with the same product;
their intersection is counted separately, as required by IC6.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_fibre_individual_mixed_budgets.py
```

The default run compares regenerated data with the retained JSON without
writing it. Use `--output PATH` to write the exact result data. Only the Python
standard library is used; all checks remain active under optimization.

This result is a repository-derived capacity deduction; the analytic
seven-core source and its attribution remain in
[report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md).
The present criterion does not require that source to prove its conditional
actual-pair conclusion. It also does not remove the common-prefix hypotheses
of [report479](479-independent-center-choices-with-simultaneous-coordinate-splits.md)
or [report480](480-arbitrary-old-phases-after-a-finite-common-prefix.md).
