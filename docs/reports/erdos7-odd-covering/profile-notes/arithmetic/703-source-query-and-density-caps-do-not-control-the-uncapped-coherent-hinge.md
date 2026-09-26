# The AH9 interface does not bound the uncapped coherent hinge below one

The three displayed source properties in report473(AH9) do not, by themselves,
imply an uncapped additive cofactor hinge below one, even for actual distinct
odd moduli with one common old centre. The finite construction below satisfies
all three properties, has a hinge strictly above one, and has exactly the same
actual forbidden union as a seven-label family whose additive hinge is zero.

This is an interface counterexample. It does not produce an odd cover, refute
report473, or identify its law with report467's particular source-selection
mechanism. The larger original family is highly redundant. The example does
not rule out a route which first reduces to an irredundant original family and
then uses that additional geometry. All deductions here are ordinary
mathematics with exact finite checks, not new Lean verification.

## The interface and the two different quantities

Use the old primes

    P=(3,5,7,11,13,17,19),
    A=70871/3375,
    Lambda=6075000000000/7235955529.

Report473(AH9), citing report467, records a single law on a sufficiently fine
old period M with

    supp(mu)=U,
    R_M(mu)=sum_(1<d|M) max_a mu(x=a mod d)<=A,
    mu<=Lambda H_M.

Here U is the actual survivor set of the old-only original family, and H_M is
uniform probability. The laws below are compatible across all deeper periods,
so one can take M divisible by p^21 for every p in P as required there.

At current prime23, a collection C of originals a_lambda mod(23 d_lambda)
has additive cofactor load

    f_C(x)=(1/23)sum_lambda 1_(x=a_lambda mod d_lambda).

Its actual forbidden union fraction alpha_C(x), measured in the23-coordinate,
is at most f_C(x) and at most one. Define the UNCAPPED additive hinge by

    H_(1/2)(f_C)=E_mu[(f_C-1/2)_+]/(1/2)
                =E_mu[(2 f_C-1)_+].

A survivor bound for the actual union controls alpha_C, not an upper bound for
the generally larger f_C. This distinction survives all three AH9 properties.

## One full-support law with exact all-height control

Let H be product Haar on the old prime coordinates. Equivalently, use finite
uniform old periods and compatible uniform extensions at higher digits. Put

    v_p(x)=the p-adic valuation of x relative to centre0,
    D2(x)=product_(p in P)(min(v_p(x),2)+1),
    E={x:D2(x)>=32},
    e=H(E)=8435891267/7840332174675,
    mu=(3/5)H+(2/5)H(.|E).                         (CU1)

The density depends on only two digits at each old prime. It is everywhere at
least3/5, so its support at every finite period is the entire period. Choose
an empty old-only original family; its full survivor set U is exactly that
support. No assumption about missing a prescribed nonempty old family is
being made.

The maximum density is

    3/5+2/(5e)=15705972023151/42179456335
              =372.3607032392775...<Lambda.         (CU2)

The density is nondecreasing in each truncated valuation. This proves that
for every P-supported modulus d, its zero cylinder is a maximizing cylinder:

    max_a mu(x=a mod d)=mu(x=0 mod d).              (CU3)

For completeness, fix all other prime coordinates and compare cylinders at
one prime p^j. A nonzero residue whose valuation is r<j has that fixed
valuation throughout its cylinder. The zero cylinder has valuation at least
j throughout. Both cylinders have the same Haar mass, and replacing the former
by the latter cannot decrease the conditional density. An already zero
residue needs no change. Apply these replacements one coordinate at a time.
This also applies when j>2; the density then only sees the saturated value2.

Consequently the complete all-height query sum is

    1+R_infty(mu)
       =E_mu product_(p in P)(v_p(x)+1).            (CU4)

This follows by summing the nonnegative zero-cylinder indicators for every
P-supported divisor label. For every finite M, R_M<=R_infty. There is no
exchange of separately chosen maximizing laws in this identity.

Only3^7=2187 truncated valuation cells are needed to evaluate CU4 exactly.
For a coordinate value r in{0,1,2}, their Haar probabilities are respectively

    (p-1)/p, (p-1)/p^2, 1/p^2.

The conditional factor E(v_p+1) is r+1 for r<2, and

    E(v_p+1 | v_p>=2)=2+p/(p-1)

for r=2. The unsummed deeper tail is therefore evaluated by a convergent
geometric identity, not discarded. The exact results are

    E_H product_p(v_p+1)=323323/110592,
    E_H[1_E product_p(v_p+1)]
       =680845452801113263/13006170237924864000,
    R_infty(mu)=1414458544322632571/69970656525004800
               =20.21502461988705...<A,
    A-R_infty(mu)=274211572584785561/349853282625024000>0. (CU5)

Thus the displayed support, query and density conditions in AH9 all hold,
including every greater finite query depth.

## Actual original labels with the same union but different hinges

Let

    Q2=product_(p in P)p^2=23520996524025.

The full original family is

    C_full={0 mod(23d): d|Q2, d>1}.                (CU6)

There are exactly3^7-1=2186 labels. All numerical moduli are pairwise distinct,
odd, and greater than one. All old phases and all current phases are zero;
there is no pure23 class. Every label has old height at most2 and current
height1. This family is genuinely an original congruence family, not a set of
independently selected query maximizers.

Its active old cofactor count is D2(x)-1, so

    f_full(x)=(D2(x)-1)/23.                        (CU7)

Compare it with the seven-label original family

    C_short={0 mod(23p):p in P}.

Every short label is present in the full family. Conversely, every nonunit
divisor d of Q2 has a prime factor p in P, so

    {0 mod(23d)} subset {0 mod(23p)}.

The two actual forbidden unions are therefore equal, as literal subsets of
their common full CRT period. On each old x their shared current union
fraction is

    alpha_full(x)=alpha_short(x)
       =(1/23)1_(some p in P divides x).           (CU8)

Its actual union hinge is zero. Also

    f_short(x)=(1/23)#{p in P:p|x}<=7/23<1/2,

so the short family's uncapped additive hinge is zero.

In contrast, exact integration of CU7 under CU1 gives

    H_(1/2)(f_full)
       =2581992950434626793746299/2535373939370931457423625
       =1.018387430090593...>1,                    (CU9)

with strict excess

    46619011063695336322674/2535373939370931457423625>0.

For reproduction, the two unnormalized Haar contributions are

    E_H[(2f_full-1)_+]=452456464149/60109213339175,
    E_H[1_E(2f_full-1)_+]=1701702799/623971072725.

Multiplying the first by3/5 and the second by2/(5e) gives CU9.

## Precisely which proposed bridge fails

There cannot be a theorem using ONLY the three displayed AH9 properties to
bound the uncapped additive hinge by a uniform H0<1 for every finite coherent
original family. CU1 and CU6 are a counterexample to that statement. At the
same time, the actual union hinge is zero, so neither this example nor CU9
contradicts report473's actual fibre-survival conclusion.

The source law in CU1 has not been obtained from report467's prescribed source
construction. Extra structure of that chosen law could still be useful. To
use such structure, an application must state it and prove the bridge; it
cannot substitute the three numerical/support summaries for it. The law has
full support from an actual empty old family, so the sparse-support/density
failure in report474 is not the issue here.

The larger family is redundant: all2186 classes can be replaced by the seven
short classes without changing their union. An irredundancy premise, if
actually used by a consumer, is additional information absent from the
refuted interface statement. This example supplies no counterexample under
that additional premise and does not settle an antichain-restricted bound.

One distinction is necessary for that proposed repair. If all FULL phases
share one centre, irredundancy makes numerical moduli a divisibility antichain.
If only OLD phases share a centre, as in report473, different current residues
can make nested old-cofactor classes disjoint. At current height1, one can
infer an antichain within each common-current-residue group; a single global
old-cofactor antichain does not follow. At greater current heights, current
prefix compatibility must also be preserved.

A separate repair is to work with the clipped majorant min(1,f_C). Its hinge
is bounded by one, and report473's good set can bound it strictly below one
in the specified seven-old-prime/23 coherent case. That is a different
quantity from the uncapped H in the proposed Nyx interpolation. It needs an
explicit rewritten consumer and quantitative tail budget. No unrestricted
support, arbitrary-phase or all-stage gain is established by this note.

## Reproduction and references

The [standalone verifier](../../frontier/cover-geometry/coherent_uncapped_hinge_obstruction.py)
uses the standard library and writes [exact result data](../../frontier/cover-geometry/coherent_uncapped_hinge_obstruction.json).
From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent_uncapped_hinge_obstruction.py \
  --output docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent_uncapped_hinge_obstruction.json
```

Checks use explicit exceptions and remain active under Python optimization.
They cover all2187 valuation types, the2186/7 original-label inventories,
literal divisibility certificates for the common union, the rational sums,
and all three strict comparisons. A separate exact implementation reproduced
the event mass, all-height query norm, density and both hinge integrals.
The monotone-cylinder proof and all-height geometric-tail deduction above
are ordinary proof inputs; the finite check does not enumerate infinitely
many cylinders or reconstruct the source selector.

[Report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md)
supplies the source construction not reconstructed here.
[Report473](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md),
AH9--AH14, supplies the scalar/support interface and actual-union fibre result.
[Report474](474-arbitrary-fixed-phases-admit-high-load-below-the-query-cap.md)
gives a different fixed-phase obstruction that fails the density cap.
[Report340](../321-384/340-whole-cover-completion-constrains-original-prefix-loads.md),
CP7--CP7a, already distinguishes label incidence from union incidence and
requires a same-law multiplicity bridge.
[Report562](562-joint-deletion-certificates-and-an-actual-query-antichain.md)
retains actual-original, query-weighted losses; these data are not supplied
by a clipped union bound alone.
