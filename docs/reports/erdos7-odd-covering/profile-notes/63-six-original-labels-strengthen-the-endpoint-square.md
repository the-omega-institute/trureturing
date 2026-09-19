[Index](../marked_head_profile.md) · [Endpoint source geometry](59-endpoint-linear-source-deletion-bound.md) · [Complete pairwise square](62-endpoint-square-from-cylinder-intersections.md)

# Six original labels strengthen the uniform endpoint square bound

In the endpoint class of profiles59 and62, every independently labelled
complete original357 test A satisfies

    limsup integral_survivor A^2<=2653/540.             (1)

The endpoint class consists of actual finite forbidden families
approaching source vertex404, normalized survivor mass3/20 and
shallow carrier mixture(0,1). Test residues may vary arbitrarily
with the family. The signed square barrier45 now gives

    liminf [45*S-integral_survivor A^2]>=248/135.

The full-square upper bound improves profile62 by103/675. Its margin
improves the old profile49 value5701/3888 by7207/19440.

The new fact is a constraint on a common layout of six actual
original labels. Their pair intersections cannot separately maximize
all the cylinder caps used in profile62. Two disjoint groups of
ordered pairs give the gains3/50 and5/54. Every other pair and all
unbounded exponent tails retain the complete bounds of profile62.
This is an ordinary endpoint theorem, not a quantitative neighborhood
or global K certificate, and no Lean verification is claimed.

## 1. The six-label head and its complete finite layout space

Use old35 labels

    H={1,3,9,5,15,45},
    exponent pairs={(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)}.

For any independently chosen original residues let B be their load,
including the unit term1. On the five ternary cells and five first
five-adic slots of profile59 it has the form

    B(l,j)=1+1_(ROOT(l)=r3)+1_(l=c9)+1_(j=j5)
             +1_(ROOT(l)=r15 and j=j15)+1_(l=c45 and j=j45). (2)

The roots r3,r15 each have two surviving choices. Cells c9,c45 each
have five surviving choices, and each five-adic slot has five
choices. Thus(2) has exactly12500 independent layouts. A test root
or cell outside the surviving ternary set contributes zero and can
be replaced by a surviving one, increasing B pointwise. A missing
label can similarly be added. Consequently these12500 layouts
dominate every possible original six-label test.

The five slots are P=pure5 first source cylinder, A=alpha first
cylinder, B=beta first cylinder, Q=higher shallow tails, and H=the
source-free first slot. The name B for the beta slot is used only
as a slot name; the function B in(2) always denotes the six-label
test load.

Let M_lj(x) be the exact raw35 source cell-slot matrix from profile59,
where x is late deletion in cell3 times the beta first slot and

    1/90<=x<=1/72.

Every entry is affine in x. The same profile gives a surviving
matrix upper bound

    U_lj(x)=M_lj(x)*[1-(1_root0+1_(l=1)+1_(j=H)
                                  +1_(root1 and j=H))/5].

Write u_lj for the maximum of U_lj at the two endpoints. These
entrywise maxima need not occur at one common x; using them
simultaneously is a valid enlargement of the set of actual masses.
They are

| Cell | P | A | B | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 2/225 | 2/225 | 1/150 | 1/150 |
| 1 | 0 | 1/75 | 1/75 | 1/100 | 2/225 |
| 2 | 0 | 0 | 0 | 1/180 | 1/75 |
| 3 | 0 | 0 | 1/90 | 1/90 | 1/75 |
| 4 | 0 | 0 | 1/45 | 1/90 | 1/75 |

The complete positive-five cofactor deletions additionally give
row capacities

    r=(11/360,2/45,1/60,11/360,2/45).

Actual surviving cell-slot masses t_lj are nonnegative and satisfy

    t_lj<=u_lj, sum_j t_lj<=r_l, sum_(l,j)t_lj=S=3/20. (3)

## 2. A certified uniform zero-seven head bound

For each layout(2), put c_lj=B(l,j)^2-1>=0. Maximize sum c_lj*t_lj
subject to(3), allowing the last equality to be <=3/20. This is a
finite relaxation of the actual surviving measure, so an upper
bound for it is an upper bound for integral_survivor(B^2-1).

For nonnegative gamma,beta_l,alpha_lj satisfying

    gamma+beta_l+alpha_lj>=c_lj,

every feasible t obeys the explicit dual bound

    sum c_lj*t_lj
       <=gamma*(3/20)+sum_l beta_l*r_l+sum_(l,j)alpha_lj*u_lj. (4)

The exact checker supplies feasible primal and dual values for every
one of the12500 layouts and verifies equality between them. It uses
an integer scale1800, which clears all the capacities. A descending
coefficient fill produces the primal candidate. The upper-bound
certificate does not rely on trusting that algorithm: the dual
inequalities and the value in(4) are checked separately in every
case. The maximum over all layouts is

    integral_survivor(B^2-1)<=467/360.               (5)

The maximizing layout is

    (r3,c9,j5,r15,j15,c45,j45)=(1,4,B,1,B,4,B).

This identifies the maximum of the stated finite relaxation, not
an assertion that an actual forbidden family realizes all its
relaxed cell-slot masses.

Within the complete pair expansion of profile62, the six head
labels contribute36 ordered pairs. Their old cap sum is

    sum_(i,j in H) C_(lcm(i,j)).

Subtract its one unit-unit term S. The remaining35 ordered pairs
have old bound2443/1800. Replacing just those pairs by(5) saves

    2443/1800-467/360=3/50.                         (6)

The unit-unit pair is not replaced and remains counted once in
the full square. All ordered pairs with at least one old-coordinate
label outside H retain their previous caps.

## 3. One raw head norm controls arbitrary cross-depth labels

For any fixed head layout(2), its raw35 source integral is

    integral_Lambda B^2=sum_(l,j)M_lj(x)*B(l,j)^2.

It is affine in x. Checking the two interval endpoints for every
layout gives25000 exact values, with maximum

    integral_Lambda B^2<=769/360.                   (7)

The maximizing layout at both x endpoints is

    (1,4,H,1,H,4,H).

In contrast, summing profile62's raw source caps for the36 ordered
head pairs gives91/40. The common actual layout therefore saves

    91/40-769/360=5/36.                            (8)

This raw-source estimate also controls different original head
tests. If B_e and B_f use independently chosen residues, the
Cauchy-Schwarz inequality on the same actual measure Lambda gives

    integral_Lambda B_e*B_f
       <=sqrt(integral_Lambda B_e^2*integral_Lambda B_f^2)
       <=769/360.                                 (9)

For e=f the head is the same test block, and(9) reduces to(7).
For e different from f the original residues may be unrelated.
Neither case requires a common maximizing layout or any alignment
of the independently labelled five-coordinate cylinders.

## 4. All positive-seven ordered pairs, including their unit labels

For each seven exponent e>=0 retain the six original old-coordinate
labels in H, writing their old-coordinate load as B_e. The original
modulus is h*7^e for h in H. The seven residue can differ for every
h at a fixed e; thus the actual test block need not factor as one
seven indicator times B_e.

Nevertheless, for fixed e,f with max(e,f)>0, every individual pair
has seven-coordinate intersection of normalized mass at most

    u_max(e,f)=6/(5*7^max(e,f)).

Drop mixed-seven deletion, apply this cap to each of the36 original
head pairs, and then sum. Since the cap is the same for this fixed
depth pair, their combined actual intersection mass is at most

    u_max(e,f)*integral_Lambda B_e*B_f
       <=u_max(e,f)*(769/360).                     (10)

The old raw-unit label h=1 is retained in every B_e. At e>0 it is
the original pure7 test label7^e, whose old-coordinate indicator is
the constant1. When e=f its self-pair is counted once among the36
pairs; when e differs from f it is an ordinary cross-depth pair.
For e=0 it is the global unit label. The excluded depth pair(0,0)
is exactly the zero-seven block already treated in section2.

There are2t+1 ordered depth pairs with maximum t. Consequently

    sum_(max(e,f)>0)u_max(e,f)
       =sum_(t>=1)(2t+1)*6/(5*7^t)=2/3.

The old cap assigned these positive-seven head pairs
(2/3)*(91/40). Equation(10) instead assigns(2/3)*(769/360), giving
the complete positive-seven gain

    (2/3)*(5/36)=5/54.                             (11)

The positive-seven set of pairs in(11) and the35 zero-seven pairs
in(6) are disjoint. Both are subsets of the original complete
ordered-pair expansion, so their gains add without charging any
pair or deletion budget twice.

## 5. Full bound, tails, and scope

Keeping all other caps from profile62, the absolute square bound is

    4559/900-3/50-5/54=2653/540.

Thus

    45*(3/20)-2653/540=248/135,
    248/135-5701/3888=7207/19440.

The refinement does not truncate high old-coordinate exponents:
their complete ordered-pair contribution remains in the inherited
4559/900 bound. The positive-seven refinement includes every depth
through the exact geometric sum2/3. Partial original test families
are dominated by complete ones, with all added terms nonnegative.

For approaching finite source families, use profile62's labelwise
diagonal subsequence and uniform quadratic tail estimate. The
surviving densities converge in L1 for each fixed finite set of
labels, and the complete square-tail error is bounded uniformly by
a summable polynomial-times-geometric series in the maximum
exponents. The limiting family has the endpoint matrices and caps
used above. This proves(1) for arbitrary changing original labels.

The [standard-library checker](../frontier/endpoint_square_coherent_head.py)
reconstructs profiles59 and62 from pinned source bytes and exact
certificates. It checks all12500 primal/dual equalities, all25000
raw-source endpoint values, and the complete positive-seven sum
both by its closed formula and by finite ordered depth pairs plus
their explicit tails.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_square_coherent_head.py --check
```

The [certificate](../certificates/source_norms/endpoint_square_coherent_head.json)
contains the aggregate counts, extrema, maximizing layouts, one
maximizing primal/dual witness, and deterministic hashes over all
checked cases. It does not store a long per-case transcript. The
checker is read-only unless `--output PATH` is supplied and keeps
all required comparisons active under -O.

The finite enumeration exhausts the shallow layout space used in
the inequalities; it is not evidence from a sample of full covering
systems. The arbitrary-label grouping, actual-measure relaxation,
Cauchy-Schwarz step, and infinite-depth passage are the ordinary
arguments above. The global source-domain consumer and unrestricted
covering problem remain unresolved.
