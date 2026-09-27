# The AH9 interface does not bound the uncapped coherent hinge below one

The three displayed source properties in report473(AH9) do not, by themselves,
imply an uncapped additive cofactor hinge below one, even for an irredundant
family of actual distinct odd moduli with one common OLD-coordinate centre.
One explicit law satisfying all three properties supports an additive hinge
strictly above one. Rank colouring the2186 original moduli gives a private
integer for every class while preserving that same law and additive load.

A separate zero-current-phase construction has exactly the same actual
forbidden union as a seven-label family whose additive hinge is zero. These
same-union and irredundancy conclusions concern two different assignments of
current phases; the zero-current-phase family remains redundant.

This is an interface counterexample. It does not produce an odd cover, refute
report473, or identify its law with report467's particular source-selection
mechanism. The irredundant example has different current phases. If the old
cofactors instead form an antichain at each current height, the existing
antichain mechanism gives H_(1/2)(f)<=R_M(mu)/(q-1), hence below one at
q=23 under AH9. Full CRT coherence with irredundancy is one sufficient
source of this structure; it is not required by the bound itself.
All deductions here are ordinary mathematics with exact finite checks, not
new Lean verification.

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

## Rank colouring makes the obstruction irredundant

The redundancy of CU6 is not necessary for the AH9-interface obstruction.
Keep the SAME old source CU1 and the same2186 numerical moduli23d. For

    d=product_(p in P)p^e_p,  0<=e_p<=2, d>1,
    r(d)=sum_p e_p in{1,...,14},

give the original class its unique normalized CRT phase

    a_d=0 mod d,
    a_d=r(d) mod23,
    a_d=d*[r(d)*(d^(-1) mod23) mod23].             (CU10)

The bracket denotes the representative in{0,...,22}. Each numerical d receives
exactly one current colour; the colours are fixed before drawing the common
old law. There is no independent optimization of a colour group or change of
source. Every old phase is still the common centre0, but the current phases
are different. This is OLD-coordinate coherence, not full CRT coherence.

Within one colour, old cofactors form a divisibility antichain. Indeed,
d'|d means e'_p<=e_p at every p, and equality of r(d') and r(d) forces equality
of every exponent. All colours are below23, so colour equality modulo23 is
literal equality of ranks, without wraparound.

More strongly, every original has an actual private integer. For the exponent
tuple of d, choose x_d by CRT with

    x_d=p^e_p mod p^3 for every p in P,
    x_d=r(d) mod23.                               (CU11)

The old valuations of this integer are exactly e_p. If x_d lies in another
original a_(d') mod23d', then d'|x_d gives e'_p<=e_p, while the current
coordinate gives r(d')=r(d). Thus d'=d. Each x_d belongs to its own original
and no other one. The family is irredundant; deleting any class changes the
actual union. The witness period is

    23 product_p p^3=2623683309902380600875.

The colour-class sizes, for ranks1 through14, are

    7,28,77,161,266,357,393,357,266,161,77,28,7,1.

Changing the current phases does not alter which old cofactor indicators are
active. Thus this irredundant family's additive load and hinge remain exactly

    f_rank(x)=(D2(x)-1)/23,
    H_(1/2)(f_rank)=H_(1/2)(f_full)>1.             (CU12)

The same all-height query and density bounds CU2--CU5 continue to hold. They
are properties of the unchanged old law, which is supported on the full
survivor of the unchanged empty old-only family.

The ACTUAL union is different from CU8 and can also be computed exactly.
Write v_p=min(v_p(x),2) and s=sum_p v_p. The active exponent vectors are
precisely the nonzero e with0<=e_p<=v_p. Their possible ranks are every
integer1,...,s: sums of the integer intervals{0,...,v_p} form the full interval
{0,...,s}. As s<=14<23, their current colours are all distinct. Hence

    alpha_rank(x)=s/23,
    alpha_rank(x)<=14/23,
    (2 alpha_rank(x)-1)_+<=5/23.                  (CU13)

The actual current fibre always has at least9/23 surviving mass. In particular,
this is not a whole cover or a counterexample to report473.

Exact integration gives

    H_(1/2)(alpha_rank)
      =1219830493798061/585086293700984182482375
      =0.0000000020848727904425514... .             (CU14)

For reproduction, its Haar value is233/41614070773275. A positive actual
hinge requires s>=12. For v in{0,1,2}, (v+1)^2>=2^v, so
D2^2>=2^s>=2^12 and hence D2>=64>32. Its positive set lies in E.
Multiplying that Haar value by the density3/5+2/(5e) from CU2 gives CU14.
The uncapped hinge above one and the small actual-union hinge therefore refer
to exactly the same source and exactly the same irredundant original family.

This rules out the proposed implication using AH9 together with
OLD-coordinate coherence and actual irredundancy. CU10 has no common
current centre and its whole single-height cofactor set is not an
antichain. The layered-antichain case has the different bound below;
the particular source-selection mechanism of report467 and the extra
consequences of a minimal whole covering family are not reconstructed
by this counterexample. A conflict/coherence extraction must state
exactly which common-centre or antichain conditions it establishes.

## Same-old-centre layered cofactor antichains control the uncapped load

The existing comparable-class and antichain mechanisms in
[Chapter16](../../problem-details/16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#congruence-and-complete-layout-specialization),
[Chapter40](../../problem-details/40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md#3-existing-actual-label-colors-and-their-boundary)
and [Report535](535-mixed-chain-moments-retain-shared-prime-correlations.md)
have a direct application to the AH9 interface. This is an ordinary
application of those mechanisms, not a new generic antichain theorem or
formal-library declaration.

Let q>=3 be prime, let M be any finite old period coprime to q, and let mu
be one probability law on Z/MZ. Consider a finite block of actual original
classes with distinct numerical moduli d*q^k, where d|M and k>=1. Assume:

* Every old residue is one common t: a_(d,k)=t mod d.
* At each fixed current height k, the set A_k of present old cofactors d is
  a divisibility antichain.

The current residues modulo q^k may differ between d and between heights.
Each original still has its one fixed global CRT phase. No global irredundancy
or common current centre is required in addition to these two hypotheses.
Define the unconditioned-Haar cofactor load

    f(x)=sum_(original(d,k)) q^(-k)1_(x=t mod d),
    R_M(mu)=sum_(1<d|M) max_b mu(x=b mod d).

Then, allowing arbitrary finite old and current heights,

    H_(1/2)(f)=E_mu(2f-1)_+<=R_M(mu)/(q-1).       (CU15)

To prove this, put

    D(x)=#{d|M:x=t mod d}
        =product_(p|M)(min(v_p(x-t),v_p(M))+1),
    N_k(x)=#{d in A_k:x=t mod d}.

The product uses truncated valuations, so it is finite even when x=t
mod M. When D(x)>=2, choose any old coordinate with positive truncated
valuation v>=1. Holding all other exponents fixed partitions the D(x) active
divisors into D(x)/(v+1) chains. At most one member of A_k lies on each
chain, so

    N_k(x)<=D(x)/(v+1)<=D(x)/2,
    f(x)<=D(x)/[2(q-1)].

The geometric sum bounds the entire finite inventory of current heights;
no height is dropped and no independently favorable laws are selected.
When D(x)=1, only d=1 can be active, at most once at each height. Hence
f(x)<=1/(q-1)<=1/2. In both cases,

    (2f(x)-1)_+<=(D(x)-1)/(q-1).

Finally, under the SAME mu,

    E_mu(D-1)=sum_(1<d|M) mu(x=t mod d)<=R_M(mu),

which proves CU15. The support and density clauses of AH9 are not needed
for this implication. M need only resolve the actual old cofactors; it can
also contain all the extra query labels required by AH9.

At q=23, every AH9 law therefore gives, under the stated layered-antichain
hypothesis,

    H_(1/2)(f)<=70871/74250
                =0.9544915824915825...<1.          (CU16)

If all current exponents equal1, the same argument uses f=N_1/q and yields
the stronger bound R_M(mu)/q, here70871/77625<1. These conclusions are not
restricted to the particular mixture CU1. The actual current union fraction
alpha(x) satisfies alpha(x)<=f(x), so its hinge obeys the same bound.
The load here uses weights q^(-k); a load normalized by a pure-survivor
measure needs its own normalization comparison.

FULL CRT coherence plus actual irredundancy is one SUFFICIENT way to obtain
the hypothesis on every A_k: comparable old cofactors at the same k would
make the corresponding common-centre original classes nested. It is not a
necessary condition for CU15. Another sufficient special case has one common
current residue separately at each k, together with old coherence and
irredundancy; those current residues need not lie on one nested path.

General irredundancy plus old coherence gives only an antichain within each
current-residue colour at a fixed height. It need not make the entire A_k
an antichain. CU10 retains many comparable cofactors at its single current
height by assigning different colours, so CU15 does not apply to it.

The distinction also affects actual unions. A full-centre block is contained
in the single current root and has alpha<=1/q. A block with one current
residue per height has alpha<=sum_(k>=1)q^(-k)=1/(q-1). Neither bound follows
merely from CU15's weaker layered-antichain hypothesis, which allows many
current residues within a layer. These special-case union observations are
not new noncoverage results; CU15 supplies an uncapped additive consumer under
a stated structural hypothesis, without solving unrestricted Erdős#7.

There remains a precise extraction obligation. A procedure which enforces
only old-coordinate coherence has not established the layered-antichain
hypothesis. Moreover, disagreement of current q-phases does not make the old
indicators1_(x=a_lambda mod d_lambda) and1_(x=a_kappa mod d_kappa) disjoint.
Their product can remain positive in E_mu f^2. Current-phase conflicts cannot
simply be subtracted from that old-cofactor square budget. A paid extraction
must either establish the actual layered-antichain condition, or reach a
sufficient stronger form of coherence through an additional same-source
comparison accounting for those current-phase conflicts. CU15 supplies no
such missing deletion comparison.

## Precisely which proposed bridge fails

There cannot be a theorem using only the three displayed AH9 properties,
old-coordinate coherence and actual irredundancy to bound the uncapped
additive hinge by a uniform H0<1. CU1 and CU10 are a counterexample to that
statement. The zero-current family CU6 separately shows that identical actual
unions can have different additive hinges. Both actual-union calculations
remain compatible with report473's fibre-survival conclusion.

The source law in CU1 has not been obtained from report467's prescribed source
construction. Extra structure of that chosen law could still be useful. To
use such structure, an application must state it and prove the bridge; it
cannot substitute the three numerical/support summaries for it. The law has
full support from an actual empty old family, so the sparse-support/density
failure in report474 is not the issue here.

Removing redundant originals fixes the zero-current family CU6 but cannot
remove a class from the rank-coloured family CU10. Full CRT coherence would
impose a stronger condition: irredundancy then forces one divisibility
antichain. Old-coordinate coherence alone gives a separate antichain within
each current-residue group at height1, and CU10 satisfies exactly those
conditions. At greater current heights, current prefix compatibility must also be
preserved. CU15 assumes an antichain of old cofactors in each entire
height layer, a property implied by full coherence and irredundancy but
not by arbitrary old-only coherent irredundant inputs such as CU10.

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
and all three strict comparisons. For CU10 the verifier additionally checks
all2186 normalized CRT phases,4,778,596 private-point/class memberships,
307020 same-colour antichain pairs and every valuation type's actual colour
union. The result's original `exact.actual_union_hinge` belongs to the
zero-current family; its `rank_colored` block records the irredundant family.
A separate exact implementation reproduced the source quantities and both
families' hinge integrals, independently constructing and checking every
rank-coloured private point against all2186 originals.
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

The irredundant examples in
[Report564](564-integrated-actual-profiles-permit-empty-root-fibres.md),
[Report609](609-linear-schedule-credit-fails-on-an-actual-irredundant-core.md)
and [Report615](615-nested-actual-incidences-force-unbounded-fixed-law-credit.md)
concern integrated support-profile or linear-schedule certificates.
[Report622](622-full-capacity-unique-maxima-refute-the-universal-hinge-bound.md)
uses a different full-capacity entropy-selected law and its stated family is
redundant. Those results do not supply the same AH9/old-coherence/current-
height1 interface of CU10--CU14. The rank-antichain and CRT reasoning here
use elementary existing structures; no new generic antichain theorem or
formal-library declaration is claimed.

[Chapter40](../../problem-details/40-fixed-order-scalar-threshold-barrier-and-cofactor-colors.md#3-existing-actual-label-colors-and-their-boundary)
already gives fixed current-residue colours, rank-coloured actual families
and symmetric-chain counting. CU10 is a same-AH9-law quantitative
application of that existing mechanism. Chapter16 and Report535, cited
above, supply the comparable-class exclusion used to derive a sufficient
instance of CU15. No new generic antichain theorem is claimed.
