[Index](../../../marked_head_profile.md) · [Extremal original family](../../321-384/350-extremal-paired-branch-and-source-support.md) · [Joint replacement obligation](../../321-384/365-coloring-literature-and-reconfiguration-interface.md) · [Automatic private-point average](384-private-witness-profile-upper-is-automatic.md)

# Private congruence hulls and joint composite-parent contractions

In the hypothetical distinct odd cover minimizing class count and then
modulus sum, every unused smaller modulus must fail to contain a class's
entire private region in one residue. This applies even when that smaller
modulus does not divide the original modulus. Saturating all but one root
at another prime gives a concrete consequence: if the original classes
of moduli 15 and 35 intersect, numerical modulus 21 must also be present.

This is a residue-sensitive specialization of the existing replacement
principle, not a new general exchange principle. It keeps the original
labels and every prime-power height. Sections6--9 also give explicit
joint composite-parent reductions, including every ternary height and
an exact mixed-carrier allocation threshold, with irredundant
divisor-closed examples where joint reduction succeeds while both
separate reductions fail. The ordinary proofs and exact finite
controls below do not establish unrestricted Erdős #7, literature
priority, or new Lean verification.

Section10 raises the private-hull closure threshold from the original
label to its largest original multiple. Moving the parent to one actual
descendant phase converts that group's joint replacement obligation
into a repair budget for the parent's complete private region.

[Section18](#18-retained-mixed-originals-couple-both-ternary-roots)
uses a retained mixed original to repair a moved parent across both
ternary roots. At H3=1 it sharpens the total105-multiple bound from45
to44 without restricting the other heights or the support size.

[Section19](#19-actual-star-roots-and-a-guarded-square-parent-repair)
uses the actual3q root to repair a movedq^2 parent. Under the same
whole-family H3=1 condition it sharpens the3q^2-multiple bound to
4q^2-6q-5 and retains stronger root-specific constraints.

[Section68](#68-private-prefix-concentration-forces-distinct-mixed-inventory-at-all-heights)
combines the existing private-hull closures into one injective mixed-label
inventory bound. At arbitrary original ternary height, all3-free
p-bearing labels whose complete private regions lie in one first-three
root receive distinct mixed labels, except for one explicit maximal top
per fully concentrated p-column. The injection uses only original mixed
labels of ternary height one. It does not yet supply a complete legal
transport below the original budget.

[Section69](#69-cross-cofactor-divisor-payment-reduces-exactly-to-nonconcentrated-ancestors)
allows payers from other cofactor columns. Its exact matching deficit
depends on whether concentrated maximal labels have enough distinct
nonconcentrated original divisors. The existing private-point reset
identifies a concentrated-prime branch where this enlargement supplies
no improvement; a whole-cover condition excluding the deficit is missing.

[Section70](#70-concentrated-prime-private-roots-require-both-ternary-colors)
shows that concentration of every nonternary prime requires both nonzero
ternary colors. Different colors cannot share an original modulus.
At ternary height one, the existing multiplicity-two exclusion forces
5 and7 into opposite colors. [Section72](#72-small-prime-overlap-excludes-the-height-one-all-concentrated-branch)
uses the stronger two-cover support-intersection consequence of published
distortion bounds to exclude this entire height-one concentrated branch.
The arbitrary-height branch and unrestricted Erdős#7 remain unresolved.

[Sections77--83](#77-independent-color-permutations-force-every-nonzero-private-p-root-of3)
give actual source permutations and count-saving replacements when
the ternary height and the unique nonconcentrated prime's height are
both one. Existing Simpson cuts force at least p-1 nonpure p-cofactor
columns; explicit replacements exclude equality for p=7,11,13. At
p=5, equality requires two prime-power columns in EACH concentrated
color. Other primes and heights in the p-free inventory remain
unrestricted. This final layout, larger inventories and higher shared
heights have not been excluded.

## 1. Replace only the region that depends on the changed classes

Use the lexicographically minimal hypothetical cover of
[350, EB1--EB3](../../321-384/350-extremal-paired-branch-and-source-support.md).
Its original classes are \(A_d=a_d\bmod d\), with distinct odd
\(d>1\), full period \(Q=\operatorname{lcm}D\), divisor-closed
numerical palette \(D\), and normalized prime classes \(A_p=0\bmod p\).
Every original class has a private point; comparable classes are disjoint.

For \(J\subseteq D\), the exact joint replacement obligation is

\[
 E_J=\mathbb Z\setminus\bigcup_{d\in D\setminus J}A_d.
 \tag{PH1}
\]

Suppose a finite family \(\mathcal B\) of odd nonunit APs covers
\(E_J\), uses pairwise distinct numerical moduli, and uses none of the
moduli in \(D\setminus J\). Replacing \(J\) by \(\mathcal B\)
preserves whole coverage and numerical distinctness. Hence extremality
requires

\[
 |\mathcal B|\ge |J|,
 \qquad
 |\mathcal B|=|J|\ \Longrightarrow\
 \sum_{B\in\mathcal B}\operatorname{mod}(B)\ge\sum_{d\in J}d.
 \tag{PH2}
\]

This is the joint-liability replacement condition of
[365, section 5](../../321-384/365-coloring-literature-and-reconfiguration-interface.md),
combined with 350's two extremal objectives. For multiple removed classes,
\(E_J\) is not in general their union of individual private regions:
points covered only by two removed classes must also be repaired.

## 2. The complete private region supplies more than divisor closure

Fix \(d\in D\), put
\(P_d=A_d\setminus\bigcup_{e\in D\setminus\{d\}}A_e\), and choose
\(w_d\in P_d\). Let \(P_d^{(Q)}\) be its residues in one complete
period. Define

\[
 \Gamma_d=\gcd\bigl(Q,\{x-w_d:x\in P_d^{(Q)}\}\bigr).
 \tag{PH3}
\]

The gcd is positive and independent of the chosen private witness and
residue representatives. A singleton private residue gives
\(\Gamma_d=Q\). For every divisor \(e\mid Q\),

\[
 P_d\subseteq w_d\bmod e
 \quad\Longleftrightarrow\quad e\mid\Gamma_d.
 \tag{PH4}
\]

Indeed, the right side says exactly that all representative differences
and the period are divisible by \(e\). In particular
\(d\mid\Gamma_d\mid Q\).

If \(1<e<d\) and \(e\mid\Gamma_d\), then

\[
 e\in D.\tag{PH5}
\]

Otherwise replace \(A_d\) by \(w_d\bmod e\). All points depending
only on \(A_d\) remain covered by PH4; every other point is covered by
a retained class. The new modulus is odd, nonunit and unused, while the
class count is unchanged and the modulus sum decreases, contrary to PH2.
Ordinary divisor closure uses only \(d\mid\Gamma_d\). Extra prime
coordinates of the actual private region can force further moduli.

## 3. Root saturation forces crossed divisors

Let \(p\) be a support prime, \(d\in D\) with \(p\nmid d\), and
suppose there are \(p-2\) original mixed classes \(A_{pg_i}\), where
\(g_i>1\) and \(g_i\mid d\), that intersect \(A_d\) and have
pairwise distinct nonzero first-\(p\) roots. Then

\[
 h\mid d,\quad h>p
 \quad\Longrightarrow\quad \frac{pd}{h}\in D.
 \tag{PH6}
\]

To see this, intersection makes \(A_d\)'s residue modulo \(g_i\)
equal to that of \(A_{pg_i}\). Thus this child covers every point of
\(A_d\) on its specified first-\(p\) root, with all higher digits
free. The original \(A_p\) covers root zero. These \(p-1\) roots
leave every private point of \(A_d\) on one remaining root. Consequently
\(pd\mid\Gamma_d\). For the displayed \(h\),
\(1<pd/h<d\) and \(pd/h\mid\Gamma_d\), so PH5 applies.

At \(p=3\), just one mixed child is sufficient:

\[
 3\nmid d,\quad 1<g\mid d,\quad 3g\in D,\quad
 A_{3g}\cap A_d\ne\varnothing
 \quad\Longrightarrow\quad
 \{3d/h:h\mid d,\ h>3\}\subseteq D.
 \tag{PH7}
\]

The condition \(g>1\) is essential: the prime class \(A_3\) itself
covers only root zero and cannot provide the second root. If some
\(h\mid d\), \(h>3\), has \(3d/h\notin D\), then every original
mixed child \(A_{3g}\) with \(1<g\mid d\) must be disjoint from
\(A_d\). For instance,

\[
 A_{15}\cap A_{35}\ne\varnothing\ \Longrightarrow\ 21\in D,
 \qquad
 A_{21}\cap A_{35}\ne\varnothing\ \Longrightarrow\ 15\in D.
 \tag{PH8}
\]

The first implication constrains the literal mod-5 residues, and the
second constrains the mod-7 residues. Neither follows just by taking
ordinary divisors of the two displayed moduli.

## 4. Same numerical labels and private-point averages, different exchanges

Consider these two partial families on period 105:

| Modulus | Intersecting family | Disjoint family |
|---|---:|---:|
| 3 | 0 | 0 |
| 5 | 0 | 0 |
| 7 | 0 | 0 |
| 15 | 1 | 7 |
| 35 | 1 | 1 |

Both palettes are divisor-closed above one with initial odd-prime
support; comparable classes are disjoint. Complete-period enumeration
gives the private-point counts, in the table's order,

\[
 (23,12,7,5,1),\qquad (23,12,7,6,2).
 \tag{PH9}
\]

Thus both are irredundant. More specifically,

\[
 P_{35}^{\parallel}=\{71\}\pmod{105},\quad
 \Gamma_{35}^{\parallel}=105;
 \qquad
 P_{35}^{\perp}=\{1,71\}\pmod{105},\quad
 \Gamma_{35}^{\perp}=35.
 \tag{PH10}
\]

In the intersecting family, replacing \(1\bmod35\) by
\(8\bmod21\) preserves every previously covered integer. In the
disjoint family, that replacement loses the integer 1. Any lex-minimal
whole completion retaining the intersecting family's displayed classes
must therefore contain numerical modulus 21. This does not claim that
the disjoint family can be completed to a cover, or that some other
condition could not force 21 there.

Let \(H\) be uniform on the full period and let \(S\) avoid all three
original prime classes. Then \(X=H(S)=16/35\). Use the full digit set
\(\{3,5,7\}\) and the inverse-binomial private-point integrand of
[384](384-private-witness-profile-upper-is-automatic.md). For either
family and any chosen private witnesses for the two composite classes,

\[
 \int_{S\cap A_{15}}\binom{2+|\Delta_{15}(x)|}{2}^{-1}\,dH
 =\frac8{315},\qquad
 \int_{S\cap A_{35}}\binom{2+|\Delta_{35}(x)|}{2}^{-1}\,dH
 =\frac4{315}.
 \tag{PH11}
\]

For modulus 15, its intersection with \(S\) has six points: the
witness itself has zero mismatches and the other five have one. For
modulus 35 the corresponding counts are one and one. Their sum is
\(4/105=X/12\), identical in the two families. The individual
integrated scores therefore do not determine the legality of this
replacement. This does not identify their pointwise or joint incidence
data: in one family the two mixed classes intersect, in the other they
do not. No claim is made that every weighted private-point method loses
the distinction.

## 5. Scope of the additional constraint

The replacement premise is already present in 350 and 365. The
congruence-hull specialization and PH6--PH8 explicitly propagate actual
intersections into previously unused numerical labels. They are not
the singleton cofactor ideal of
[364](../../321-384/364-singleton-cofactor-ideal-and-forced-colors.md),
whose relative description quantifies over labels already present.
Nor does [374](374-extremal-prime-projections-and-cardinality-descent.md)
directly give them: its \(R_3\) avoids every 3-free class, while
\(P_{35}\) is contained in a 3-free class.

[382](382-prime-star-overlaps-and-no-prime-excess.md) forces overlap
among certain children sharing a prime. PH6 instead concerns a child
\(A_{pg}\) and a \(p\)-free original \(A_d\) with \(g\mid d\).
These are different incidence conditions. No implication from 382's
forced overlap to PH6's hypothesis, additive star-excess estimate, or
uniform original-Haar deficit is established here. The two partial
families are controls of the replacement rule, not odd covering systems.

## 6. A mixed-root cross permits a joint composite-parent contraction

There is a concrete original residue pattern for which the full joint
replacement obligation in PH1 can be discharged pointwise. In particular,
the pattern below cannot occur in any distinct odd cover having the
minimum number of classes. The modulus-sum minimum, divisor closure and
probability measures are not needed for this implication.

Let p,q,t be distinct odd primes and let g>1 be odd, with
gcd(g,pqt)=1. Fix a residue c modulo g and roots satisfying

    a,u in F_p minus {0},  a!=u,
    b,v in F_q minus {0},  b!=v.                         (JC1)

Use CRT to describe the following original classes, retaining their
literal numerical moduli:

    A_p={x:x=0 mod p},    A_q={x:x=0 mod q},
    B_p=A_(pg)={x:x=a mod p, x=c mod g},
    B_q=A_(qg)={x:x=b mod q, x=c mod g}.                (JC2)

The two proposed replacement classes, on those same parent labels, are

    C_p={x:x=u mod p, x=c mod g},
    C_q={x:x=v mod q, x=c mod g}.                      (JC3)

Define the set of root pairs

    V=({a} x (F_q minus {0,v}))
       union ((F_p minus {0,u}) x {b}).                 (JC4)

Its two arms meet at exactly(a,b), so |V|=p+q-5. Suppose there is an
injective assignment(r,s) -> h_(r,s) from V to the proper positive
divisors of g, and the original family contains the class

    G_(r,s)=A_(pq h_(r,s))
      ={x:x=r mod p, x=s mod q, x=c mod h_(r,s)}        (JC5)

for every(r,s) in V. These are assumptions on actual original residues,
not permissions to choose favorable residues for already used labels.
The inequality tau(g)-1>=p+q-5 permits the numerical assignment but does
not supply any of the original phases in JC5.

Finally suppose the original labels t^e pg and t^f qg, with e,f>=1,
are present, and their classes have the respective forms

    D_p=K_p intersect C_p,    D_q=K_q intersect C_q,     (JC6)

where K_p,K_q are arbitrary t-adic prefixes of depths e,f. They need
not coincide or intersect; in particular their first t-roots may differ.
All the displayed numerical labels are distinct. For the guards this
uses h|g and gcd(g,pq)=1; t does not divide any parent or guard.

Replace B_p,B_q by C_p,C_q and delete D_p,D_q, leaving every other
original class unchanged. Then

    union of all old classes
      subset union of all new classes,                (JC7)

and the number of classes decreases by two. Every remaining modulus is
still odd, greater than one, and occurs only once.

To prove JC7, first note that both deleted children are contained in
their new parents. Every point of B_p union B_q has x=c mod g. If its
p-root is0 or its q-root is0, the corresponding unchanged prime class
covers it. If its p-root is u or its q-root is v, a new parent covers
it. All remaining points have a root pair in V. The corresponding
guard G_(r,s) covers such a point because h_(r,s)|g. Thus

    B_p union B_q
      subset A_p union A_q union C_p union C_q
              union UNION_((r,s) in V) G_(r,s).        (JC8)

This checks the entire parent union, including points in the overlap;
it does not replace E_J by a union of individual private regions.
The same argument remains valid after adjoining any unchanged classes
of other numerical labels, with arbitrary prime-power heights and
residues. Hence a minimum-cardinality whole cover cannot contain
JC1--JC6. More generally, even one original child contained in one of
the two new parents permits a one-class reduction after both parents
are moved.

This is a sufficient forbidden original pattern. No argument here
forces its guards, common g-coordinate or child phases in an arbitrary
hypothetical cover. In particular, existence of synchronized children
at one source does not alone establish JC5.

## 7. A prime-power version works at every ternary height

A second forbidden pattern retains arbitrarily deep original moduli.
Let k>=2, let g>1 be odd with gcd(g,15)=1, and fix c modulo g. Set

    r_j=(3^j-1)/2,    u=r_(k-1),    a=u+3^(k-1).       (JT1)

Assume the original family contains A_5=0 mod5, together with the
following pure and mixed blockers for every1<=j<k:

    A_(3^j)=r_(j-1) mod3^j,
    A_(g3^j)={x:x=r_(j-1)+2*3^(j-1) mod3^j,
                  x=c mod g}.                         (JT2)

At the final ternary depth retain

    A_(3^k)=u+2*3^(k-1) mod3^k.                        (JT3)

The two old parents and their proposed replacements are

    B=A_(g3^k)={x:x=a mod3^k, x=c mod g},
    D=A_(5g)={x:x=2 mod5, x=c mod g},
    C={x:x=u mod3^k, x=c mod g},
    E={x:x=1 mod5, x=c mod g}.                        (JT4)

Require three further unchanged original classes:

    A_(5*3^k)={x:x=a mod3^k, x=2 mod5},
    A_(5*3^(k-1))={x:x=u mod3^(k-1), x=3 mod5},
    A_(5g*3^(k-1))={x:x=u mod3^(k-1), x=4 mod5,
                        x=c mod g}.                  (JT5)

Let t be an odd prime not dividing15g. If there are original children
of moduli t^e g3^k and t^f 5g, with e,f>=1, whose cofactor classes
are C and E respectively, moving both parents to C,E and deleting
those two children preserves every originally covered integer and
decreases the number of classes by two. All displayed labels are
distinct: JT2--JT3 use no factor5; the three guards have different
ternary heights or different g factors; the second parent's ternary
height is zero; and t is new to all displayed parent and guard labels.

Here is the full joint repair proof. Restrict only for the proof to the
common cylinder x=c mod g, which contains both old parents. If a point
avoids JT2, an induction on j forces its first k-1 ternary digits all
to equal1. At level j, provided the preceding prefix is r_(j-1), the
pure blocker excludes digit0 and the mixed blocker excludes digit2.
Consequently x=u modulo3^(k-1). Avoiding JT3 leaves only the two
depth-k residues u and a. The new parent C covers u. On the other
residue a, the old prime class A_5 covers quinary root0, the new parent
E covers root1, and the three guards in JT5 cover roots2,3,4. Thus
these retained blockers and the new parents cover the ENTIRE cylinder
x=c mod g, in particular B union D. Both deleted children lie in
their new parents, proving the claimed inclusion of covered unions.

This implication permits arbitrary additional unchanged originals and
arbitrary heights in the two t-prefixes. It therefore excludes JT1--JT5
and the two stated children from any minimum-cardinality odd cover,
uniformly for every k>=2. It does not assert that an arbitrary such
cover has this ternary chain or these three actual guard phases.

## 8. Irredundant divisor-closed families can admit the joint contraction

The [literal input](../../../frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction_originals.json)
contains two finite families. The
[verifier](../../../frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction.py)
reconstructs their modifications from the original numerical classes
and checks every integer in the original period; its
[output](../../../frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction.json)
includes all private counts and witnesses. The input contains no stored
coverage counts or asserted new-family snapshot.

The first family realizes section6 with

    p=3, q=5, g=77, c=u=v=1, a=b=2, t=13, e=f=1.

Its old parents are155 mod231 and232 mod385. Its three unchanged
guards are2 mod15,8 mod105 and89 mod165; their root pairs are(2,2),
(2,3),(2,4), and their proper g-divisors are1,7,11. The old children
are1 mod3003 and1926 mod5005, on different first13-roots1 and2.
Move the parents to1 mod231 and1 mod385 and delete those children.

The second family realizes section7 with k=2,g=7,c=1,t=11,e=f=1.
Its old parents are22 mod63 and22 mod35. The retained blockers are
0 mod3,8 mod21,7 mod9 and0 mod5; the guards are22 mod45,13 mod15
and64 mod105. Move the parents to1 mod63 and1 mod35 and delete
the children1 mod693 and211 mod385, on first11-roots1 and2.

All remaining original classes in each input complete the respective
numerical inventory to nonunit-divisor closure while retaining a private
integer for every original. Both supports are initial segments of the
odd primes, with every original prime class normalized to zero.

| Complete-period quantity | Squarefree family | Prime-power family |
| --- | ---: | ---: |
| Period | 15015 | 3465 |
| Original classes | 26 | 18 |
| Classes after joint contraction | 24 | 16 |
| Originally covered residues | 11802 | 2741 |
| Covered after joint contraction | 11830 | 2749 |
| Originally covered residues lost | 0 | 0 |
| Lost by first parent/child contraction alone | 11 | 9 |
| Lost by second parent/child contraction alone | 10 | 9 |
| Original holes | 3213 | 724 |
| Holes after joint contraction | 3185 | 716 |

The two single contractions have explicit lost witnesses386,232 in
the first family and526,127 in the second. In particular, none of
the four original parent classes is individually deletable. The two
jointly removed parent classes overlap in13 and11 residues,
respectively; every one of those residues has an unchanged covering
class. Other overlaps also matter:6007 in the first family has exactly
the old owners385 and3003, while211 in the second has exactly the
old owners63 and385. Both points depend on two removed labels and
belong to no individual private region. The joint verification retains
them and all other points of the old covered union.

Because these examples are noncovers, their exact obligation is

    U_old minus U_retained,

which has27 and22 residues in the two full periods. Each includes
two residues with multiple old owners. This is not the entire
complement of U_retained: original holes need not be repaired. For a
whole cover U_old is all integers, and the obligation becomes PH1's
E_J. The general proofs in sections6--7 apply in either case.

The common cofactor source is1 in both examples, and it avoids every
original free of the designated prime. At this source the first
family has active nonzero13-roots only1,2,3, with labels3003,5005,39;
the second has active nonzero11-roots only1,2, with labels693,385.
Neither supplies a matching on ALL nonzero roots. These controls do
not refute a theorem that also assumes that stronger full-source
condition or actual whole coverage.

The checks include199 nonunit-divisor memberships and full-period
private-region and joint-coverage tests on18480 integers. The input
SHA256 is

    4905fd217266e3fc974095186c89c54a2ee824a36468ccf680eabaf7cfacdebc.

Both normal and optimized Python runs give the same output bytes:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction.py --input docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction_originals.json --output /tmp/e7_composite_parent_contraction.json
```

An independent direct enumeration also agrees on all original private
counts, both covered unions and both failed single contractions.
The finite checks certify these two inputs. The arbitrary-height
statement rests on section7's digit induction, not on extrapolating
the finite examples.

Thus irredundancy and divisor closure do not prohibit every joint
composite-parent contraction. Exact minimality does prohibit the two
proved patterns. The remaining whole-cover question is whether it
forces one of these patterns or some other improving replacement;
neither occurrence nor an exhaustive classification is proved here.

## 9. Mixing three carrier types lowers the exact divisor requirement

The whole-cell strategy in section6 has a larger admissible class than
using only guards of modulus pqh. Some cells can use existing divisors
of one old parent. Mixing these with pqh guards gives an exact numerical
allocation criterion. It keeps all original phases in any application;
divisor closure alone does not supply those phases.

Keep JC1--JC4: p,q are distinct odd primes, g>1 is odd and coprime to
pq, both old parents lie on g=c, and the old/new roots are a,u at p
and b,v at q. Assume normalized original prime classes and disjointness
of comparable originals. Split the exposed cross V from JC4 into

    row cells:    (a,s), s notin {0,v,b};  count q-3,
    column cells: (r,b), r notin {0,u,a};  count p-3,
    central cell: (a,b);                   count 1.    (MC1)

A cell denotes its ENTIRE congruence class modulo pqg, including all
other coordinates. A retained carrier must contain that whole class,
not just one representative integer.

### 9.1. The available numerical carrier types are exact

For a row cell, the only possible retained whole-cell carrier moduli are

    qh with 1<h<g, h|g;   or pqh with h<g, h|g.       (MC2)

For a column cell, replace qh by ph. The central cell requires pqh
with h a proper divisor of g, allowing h=1. Each carrier's phase must
agree with that cell at every prime dividing its modulus.

To prove the classification, containment of a complete pqg-class in a
d-class forces d|pqg. A row cell lies in the old pg-parent. If q does
not divide d, then d|pg, so its carrier intersects a comparable
original, contrary to the stated disjointness. Thus d is qh or pqh.
For qh, h=1 is the original q-class, whose zero root misses the cell;
h=g is the removed old qg-parent, whose q-root b also misses this
row cell. For pqh, h=g makes the carrier a subclass of the old
pg-parent, again impossible. The column argument is symmetric. At
the central cell, omitting either p or q makes the carrier a divisor
class of an intersected old parent, so both factors are required.

Every permitted carrier meets at most ONE cell of V. A qh carrier
fixes its one row root s!=b; a ph carrier fixes its one column root
r!=a; a pqh carrier fixes both roots. Consequently any whole-cell
assignment uses exactly p+q-5 distinct carriers. This is optimal
within this strategy, not a bound on fragmented coverings of cells by
several higher-modulus originals.

### 9.2. An exact allocation threshold

Let t=tau(g)-1 be the number of proper divisors of g, including1.
There are t-1 available qh labels, t-1 available ph labels, and t
available pqh labels. These three pools are mutually disjoint, since
g is coprime to pq. A divisor may be reused across the pools without
repeating a numerical modulus.

Ignoring actual phases only for this numerical allocation question,
there is an injective assignment of permitted carrier labels to all
cells of MC1 if and only if

    1+max(0,q-t-2)+max(0,p-t-2)<=t.                   (MC3)

The central cell uses one pqh label. At most t-1 row cells can use
qh labels, so max(0,q-3-(t-1)) row cells still require pqh. The analogous
column deficit is max(0,p-3-(t-1)). This proves necessity. Conversely,
use distinct qh labels for min(q-3,t-1) row cells and distinct ph
labels for min(p-3,t-1) column cells. Assign distinct pqh labels to
the central cell and both remaining deficits; MC3 supplies enough.
There are no other numerical conflicts, which proves sufficiency.

Equivalently, since p and q are odd,

    t >= max((p-1)/2, (q-1)/2, ceil((p+q-3)/3)).      (MC4)

Indeed MC3 is equivalent to the two individual inequalities
q-3<=2t-2 and p-3<=2t-2 and the joint inequality
(p-3)+(q-3)<=3t-3. They control, respectively, each arm's access to
the shared pqh pool after reserving the central cell, and the total
number of labels. This also proves the integer threshold directly.

The all-pqh construction in section6 instead requires t>=p+q-5.
MC3 includes that assignment but can use strictly fewer proper
divisors. A construction using only qh/ph on the arms and one pqh
in the center is also a special case; mixing the types can succeed
when neither special case has enough labels.

For an ACTUAL original family, MC3 by itself does not permit choosing
new residues on retained labels. The additional premise is an actual
assignment of retained originals with the cell phases in MC2. Under
that premise their union covers V pointwise. The primes, the two new
parents and these carriers therefore cover the full old parent union,
by the same cross decomposition as JC8. Any original children contained
in the new parents may then be deleted. Thus a minimum-cardinality
whole cover cannot contain this actual carrier pattern and even one
such child. Arbitrary untouched original labels and arbitrary child
heights remain allowed.

### 9.3. A strict consumer with g=27 and seven carriers

Take

    p=5, q=7, g=27, c=u=v=1, a=b=2, child prime=11.

Here the proper g-divisors are only1,3,9, so t=3. MC3 holds with
equality:1+2+0=3. The all-pqh route would require t>=7. Using only
parent divisors for the arms also fails because the four row cells
have only two qh labels. The mixed assignment is:

| Cell | Type | Actual retained residue class |
|---|---|---|
| (2,3) | qh, h=3 | 10 mod21 |
| (2,4) | qh, h=9 | 46 mod63 |
| (3,2) | ph, h=3 | 13 mod15 |
| (4,2) | ph, h=9 | 19 mod45 |
| (2,2) | pqh, h=1 | 2 mod35 |
| (2,5) | pqh, h=3 | 82 mod105 |
| (2,6) | pqh, h=9 | 307 mod315 |

The old parents are82 mod135 and163 mod189. Their original children
are1 mod1485 and1135 mod2079; both project to cofactor residue1,
and their first11-roots are1 and2. Move both parents to residue1
and delete these two children.

The [literal26-class input](../../../frontier/cover-geometry/composite-parent-contraction/mixed_cell_carrier_originals.json)
completes this pattern to a divisor-closed irredundant family with
initial odd-prime support{3,5,7,11} and normalized prime classes.
The [existing complete-period verifier](../../../frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction.py)
reconstructs every modification from this input. Its
[exact output](../../../frontier/cover-geometry/composite-parent-contraction/mixed_cell_carrier_contraction.json)
gives:

| Quantity on the full period10395 | Value |
|---|---:|
| Original classes / classes after contraction | 26 / 24 |
| Originally covered / covered after contraction | 8399 / 8422 |
| Previously covered integers lost | 0 |
| Integers lost by either single contraction | 9 / 8 |
| Full old covered-union deletion liability | 23 |
| Liability points with multiple old owners | 2 |
| Original holes / holes after contraction | 1996 / 1973 |

All26 original private regions are nonempty. The old parent
intersection has11 residues, all covered by retained originals.
The joint check also keeps the two multiple-owner liability points;
for example1486 has precisely old owners189 and1485. It would be
incorrect to certify this change from individual private sets alone.

The common cofactor1 avoids every original free of11. Only roots1,2,4
are covered at that source; there is no full nonzero-root matching
premise. This is an actual union-preserving reduction of a noncover,
not a covering counterexample, a globally minimum family, or a proof
that every hypothetical whole cover must supply these carrier phases.
The original and modified families both leave integer16 uncovered.

Normal and optimized execution use the same standard-library verifier:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/composite_parent_contraction.py --input docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/mixed_cell_carrier_originals.json --output /tmp/e7_mixed_cell_carrier_contraction.json
```

The general criterion MC3--MC4 and the coverage implication are the
ordinary proofs above. Complete-period arithmetic verifies the strict
consumer; it does not extend its chosen residues to arbitrary families
or supply new Lean verification. Together with450 section13.7, this
separates two concrete facts: more flexible actual guards can enable
a contraction, while another divisor-closed irredundant family can
resist every size of the entire same-prime centered-relocation class.
A whole-cover condition forcing an improving operation remains missing.

## 10. Descendant-assisted private-hull closure and phase-group repair budgets

These are conditional necessary consequences of a genuine distinct-odd
whole cover minimizing first its number of classes and then its modulus
sum, as in Report350(EB1). They retain one fixed original family, its
complete private regions, numerical labels and all prime-power heights.
They do not assert that a legal improving repair must occur in every
hypothetical cover, and do not infer such a cover from a noncover control.
No Lean verification or literature-priority claim is made.

### Exact removal and repair of one original phase group

Let the original classes be A_m=a_m mod m, m in D, with full period Q.
Write P_d for the COMPLETE private region of an original d. Minimum
cardinality makes the family irredundant, so P_d is nonempty and any
original classes with comparable distinct numerical moduli are disjoint.

Fix d in D and a residue c mod d induced by a proper original multiple
of d. Define

    J_c={M in D: d|M, M>d, a_M=c mod d},
    r=|J_c|>=1.

Comparable disjointness gives c!=a_d mod d. Replace the old class at d
by C=c mod d, and remove ALL classes with labels in J_c. Every removed
child is contained in C. For an old point covered by A_d but not private
to d, some other old class covers it. That other label cannot be in J_c,
since every such child is disjoint from A_d, so the other owner is
retained. Conversely every point of P_d belongs to no retained original
and misses C because c!=a_d. Therefore the exact old-union loss is

    U_old minus U_after = P_d.                          (DR1)

The statement permits overlaps among the removed children: C covers their
entire union, including all points having several child owners. The only
remaining repair obligation is P_d because parent and children are disjoint.
Under the whole-cover premise, the new family's full hole set is exactly
P_d. For a noncover, DR1 concerns old-union loss only; old holes that C
also fills must not be added to the repair obligation.

Let B be any finite AP family covering P_d, with distinct odd nonunit
numerical moduli, each in the maximal allowed palette

    (odd integers >1) minus (D minus J_c).

Thus a repair may use either an originally unused numerical modulus or
a just-freed child label in J_c. It may not duplicate the retained new
parent label d or any other retained original. After adding B, the
family again covers all integers. Its number of classes is n-r+|B|,
and when |B|=r its modulus sum differs from the old sum by
`sum_(B in B)mod(B)-sum_(M in J_c)M`. The two extremal objectives imply

    |B|>=r,
    |B|=r ==> sum_(B in B)mod(B)>=sum_(M in J_c)M.     (DR2)

This converts a particular exact joint replacement problem into a repair
budget for ONE complete private region. It does not replace a general
joint liability by a union of private regions; the comparable-disjointness
argument above is what makes this particular reduction legitimate.

### A larger private-hull closure threshold

Choose w_d in P_d and define the existing complete private hull

    Gamma_d=gcd(Q,{x-w_d:x in P_d modulo Q}).

Report385(PH3--PH4) gives d|Gamma_d|Q and
`P_d subset w_d mod e iff e|Gamma_d`, for e|Q. Define

    M_d=max{M in D:d|M}.

Then the stronger closure consequence is

    1<e<M_d, e|Gamma_d ==> e in D.                    (DR3)

If M_d=d this is the existing PH5 statement. Otherwise suppose e is
unused and choose an original M divisible by d with M>e. Remove just
A_d and A_M, add `a_M mod d` and `w_d mod e`, and retain every other
original. The new d-class covers the entire old M-class; the new e-class
covers P_d. Every nonprivate old d-point has an unchanged other owner,
because A_M and A_d were disjoint. Hence the replacement preserves the
whole old union, uses two distinct allowed labels d,e, and lowers the
modulus sum by M-e>0 at unchanged cardinality. This contradicts EB1.

No requirement says M/d is a prime power, that d is prime-free relative
to one selected prime, or that the two new phases share a common CRT
center. The argument permits every original height and composite ratio.
Equivalently, every missing odd e<M_d must distinguish at least two
actual private points of d modulo e. The earlier PH5 tested this only
for e<d.

### A crowded descendant phase constrains the whole private hull

If r=|J_c|>=2, DR2 has two immediate arithmetic consequences:

    every nonunit divisor e of Gamma_d lies in D;      (DR4)
    no M in J_c divides Gamma_d.                      (DR5)

For DR4, an unused e dividing Gamma_d would provide the single repair
class `w_d mod e`, yielding |B|=1<r. The value e=d is already present
and is not a proposed repair. For DR5, a child label M in J_c dividing
Gamma_d is freed by the phase-group removal, so `w_d mod M` is an
allowed single repair, again giving |B|=1<r.

In particular, if Gamma_d>d and Gamma_d itself is an original label,
its original phase modulo d cannot be shared by another proper original
multiple of d. Otherwise its phase group would violate DR5.

There is also an explicit simultaneous phase restriction when Gamma_d
is absent from D: every J_c has size at most one. Every actual child
phase lies in

    S_d={c mod d: c!=a_e mod e for every original e|d, e>1}.

The child class is disjoint from each such divisor class, which proves
this inclusion with every original prefix retained. Therefore

    Gamma_d notin D ==> # {M in D:d|M,M>d} <= |S_d|.  (DR6)

The map sending each proper multiple M to a_M mod d is injective here.
For a normalized prime d=p, |S_d|=p-1. After simultaneously normalizing the original prime classes by CRT,
for composite d the prime classes force S_d to consist of units, and the original d-class removes its own
unit residue, so |S_d|<=phi(d)-1. Additional divisor classes can lower
|S_d| further. These bounds concern the same actual original phases,
not independently selected root assignments.

### A strict finite consumer beyond the old PH5 tests

Take the following ten actual original APs:

    0 mod3, 0 mod5, 0 mod7, 0 mod11,
    1 mod15, 16 mod21, 1 mod35, 12 mod55, 67 mod77, 3 mod385.

Their full period is1155. The numerical inventory is distinct, odd,
nonunit and divisor-closed; all prime classes are normalized. Every
class has a private residue, and all comparable pairs are disjoint.
The COMPLETE private hulls are Gamma_d=d except

    Gamma_35=105.

For d=35, every divisor e of105 with 1<e<35 is already in D:
3,5,7,15,21. Hence every old PH5 test passes, for every original label.
But105 is absent while35<105<385 and35|385, so DR3 detects a genuine
additional missing obligation.

The explicit allowed replacement is

    remove 1 mod35 and 3 mod385;
    insert 3 mod35 and 71 mod105.

All private points of35 are71 modulo105. The new35 class contains the
entire old385 class. The ten class count is unchanged, while the modulus
sum drops from614 to334. Complete enumeration gives793 originally
covered residues and811 after replacement, with no lost residue. The
joint liability of the two removed originals contains12 residues and
is exactly the disjoint union of their two private regions, as required
by their disjointness. Integer2 is uncovered both before and after.
Thus this is an ordinary strict test comparison on a NONCOVER, not an
extremal whole cover or an odd covering counterexample.

The independent standard-library control in
[descendant-private-hull program](../../../frontier/cover-geometry/composite-parent-contraction/descendant_private_hull.py) computes each entire private
region, all its hull differences, every old PH5 test, and old/new
membership on every residue modulo1155. Its exact result is
[descendant-private-hull data](../../../frontier/cover-geometry/composite-parent-contraction/descendant_private_hull.json).

Normal and optimized execution give identical result bytes:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/descendant_private_hull.py --output /tmp/e7_descendant_private_hull.json
```

### One fresh prime digit supplies distinct legal repair labels

The occupied divisors in DR4 need not themselves be used as repair
labels. Let p be any odd prime and H=v_p(Q), allowing H=0 for a prime
absent from the original period. Suppose

    p^H divides Gamma_d,
    tau(Gamma_d/p^H)>=p.

Choose p distinct positive divisors e_0,...,e_(p-1) of Gamma_d/p^H,
and choose w in the complete private region P_d. Put rho=w mod p^H,
with rho=0 when H=0. Define p repair classes by CRT:

    B_k={x=w mod e_k,
         x=rho+k*p^H mod p^(H+1)}, 0<=k<p.

Their numerical moduli p^(H+1)*e_k are pairwise distinct odd nonunits.
Every one is UNUSED: its p-height exceeds v_p(Q), while every original
label divides Q. This remains true if divisor closure occupies every
e_k and every divisor of Gamma_d. No original shadow label is assumed
free.

Every integer in P_d is w modulo Gamma_d, hence satisfies the required
cofactor congruence for every k and is rho modulo p^H. Its next p-digit
selects exactly one B_k. Thus these p classes cover ALL integer lifts
of P_d, not just its chosen representatives modulo Q. Applying DR2
to the same original phase group gives

    |J_c|<=p;
    |J_c|=p ==> sum_(M in J_c)M
                    <=p^(H+1)*sum_(k=0..p-1)e_k.      (DR7)

For the strongest sum test, take the p smallest positive divisors of
Gamma_d/p^H. The statement asserts no reason that every private hull
must satisfy the two displayed hypotheses. It is a lawful additional
repair within DR2's full palette, at arbitrary original heights.

### At the smallest prime, a full-height parent allows at most p-1 copies

There is a stricter consequence which uses the ORIGINAL parent label,
without requiring any enlargement of its private hull. Let p be the
SMALLEST prime dividing Q, H=v_p(Q), and suppose an original parent is

    d=p^H*n, gcd(p,n)=1, tau(n)>=p.

For every actual projected phase of its proper original multiples,

    #{M in D:d|M,M>d,a_M=c mod d}<=p-1.              (DR8)

To prove this, choose p distinct divisors e_k of n and use the fresh
classes above with w=a_d. They cover the ENTIRE original A_d, since
e_k divides n and every point of A_d has the required p^H-prefix.
Each new modulus is at most p^(H+1)*n=p*d.

For every proper original multiple M of d, the quotient M/d is an
integer greater than1 and is coprime to p: d already has the full
global p-height H. All prime divisors of that quotient belong to the
original support and exceed its smallest prime p. Therefore

    M>p*d >=p^(H+1)*e_k for every k.

If a group J_c had more than p members, DR1 followed by this repair
would reduce the class count. If it had exactly p, every new repair
modulus would be smaller than every removed child modulus, strictly
reducing the modulus sum at unchanged cardinality. Both contradict
the specified lexicographic minimality. This proves DR8.

In particular, if the smallest support prime is3, every original parent
3^H*n with tau(n)>=3 has at most TWO proper descendants with the same
phase modulo that parent. Here n is neither1 nor a prime. There is no
bound on the other exponents, the support size, or the number of
different descendant phases. The same actual original residues must
satisfy DR8 simultaneously at every qualifying parent.

The replacement mechanism has a small direct check on the NONCOVER

    1 mod75, 2 mod525, 2 mod825, 2 mod975.

Its smallest prime is3 and its global ternary height is1. Moving the
75-class to phase2 and replacing the three children by

    1 mod9, 31 mod45, 151 mod225

retains the entire old union. The new75 class contains each old child;
the three new classes cover every integer1 mod75, using its three
extensions modulo9 and cofactor tags1,5,25. All new labels are unused
odd nonunits. The class count stays four, and the modulus sum drops
from2400 to354. This checks the construction without supplying a
whole-cover example. DR7--DR8 use the general argument above, not an
enumeration of finite covers. No new Lean verification is claimed.

### Remaining whole-cover obligation

DR3--DR8 strengthen the phase and palette constraints enforced by the
two extremal objectives. They expose repairs that use an unused or
freed numerical modulus, outside Report450(13.8)'s fixed-parent-label,
common-center relocation family. That noncover obstruction does not
refute these deductions or test all their repair classes.

The new conditions remain conditional. If every Gamma_d=d, the
hull-divisor consequences of DR3--DR6 reduce to existing divisor
closure; DR8 can still restrict a full-height parent's phase groups.
No argument here forces a missing divisor below M_d, a crowded phase
containing a hull divisor, or a cheap multi-class repair of P_d in every
hypothetical cover. Obtaining one of those concrete violations from
whole coverage and numerical distinctness is the outstanding positive
bridge. A single private witness or sampled gcd cannot certify the
needed whole-private-region containment: its gcd is only an upper
multiple of the true Gamma_d until all private points or a structural
containment proof are supplied.

## 11. Shared fresh-height repairs constrain several original parents at once

Continue with the same hypothetical distinct-odd whole cover minimizing
first class count and then modulus sum. Let its original classes be
`A_m=a_m mod m`, its numerical palette be D, and its period be Q.
Write p for the smallest support prime and H=v_p(Q). Divisor closure
and disjointness of comparable originals are the consequences of
Report350's stated global minimum. All heights and actual residues
remain in the model.

The following ordinary deductions extend DR8 from one parent to a
joint collection of parents. They give an additional necessary
condition, not an unrestricted covering contradiction or new Lean
verification. No literature-priority claim is made.

### Several old parents can share one fresh-height repair

Fix a divisor

    h=p^H*n | Q, gcd(p,n)=1, tau(n)>=p.

Let P be a nonempty set of original parent labels such that, for one
ACTUAL residue c modulo h,

    h|d and a_d=c mod h for every d in P.              (SR1)

Every complete old parent class is therefore contained in `c mod h`.
Choose one new residue b_d modulo each d in P and put

    J_d={M in D minus P:d|M,M>d,a_M=b_d mod d},
    J=union_(d in P)J_d.

Then simultaneous choices must satisfy

    |J|<=p-1.                                        (SR2)

The union counts a shared child label only once. The exclusion of P
from every J_d is part of the condition: selected parents are retained
and moved, while labels in J are removed. Empty groups cause no
problem. If a group is nonempty, its selected phase differs from its
parent's old phase by comparable-class disjointness.

To prove SR2, choose p distinct positive divisors e_k of n, and let
rho=c mod p^H. The p CRT classes

    B_k={x=c mod e_k,
         x=rho+k*p^H mod p^(H+1)}, 0<=k<p,

have pairwise distinct numerical moduli p^(H+1)e_k. All are unused,
odd and nonunit: their p-height is H+1, whereas every original label
divides Q. Their union covers the ENTIRE class `c mod h`, including
all integer lifts beyond Q. Its next p-digit chooses k and its
cofactor congruence satisfies every e_k.

Move each selected original parent to `b_d mod d`, delete the labels
in J, retain all other originals, and add the B_k. Each deleted child
is contained in at least one new parent. All old parents are covered
by the B_k. Thus every previously covered integer remains covered.
In particular, the new family is a whole cover.

This argument covers the complete old parent union, including its
intersections. It does not replace a joint liability by the union of
individual private regions. Points covered by several removed
parents or children are included in the same pointwise argument.

The new cardinality is `|D|-|J|+p`. If |J|>p it is smaller. If |J|=p,
the cardinality is unchanged and each fresh modulus is at most p*h.
Every deleted M is a proper original multiple of h; M/h>1 is coprime
to p and all its prime factors exceed the smallest support prime p.
Therefore M>p*h, and

    sum_k p^(H+1)e_k <= p^2*h < sum_(M in J)M.

Moving parents changes no numerical label. The modulus sum therefore
decreases strictly in the equality case. Both cases contradict the
two extremal objectives, proving SR2.

With P={h}, this recovers DR8. With several parents, their NEW phases
may differ modulo h while the OLD phases in SR1 are the same. The
bound is on the union of all removed children across those new
phases; it is not obtained by granting each parent a separate repair
budget or independently choosing its original source.

### Two incomparable saturated parents cannot share a qualified old phase

Call a full-p-height original parent saturated when one of its
actual proper-descendant phase groups has p-1 labels. A parent
divisible by a qualified h has enough cofactor divisors for DR8, so
this is its largest permitted group size.

If two incomparable original parents u,v are multiples of the same
qualified h and have the same OLD phase modulo h, then

    u and v cannot both be saturated.                (SR3)

Suppose otherwise, with saturated groups A and B. Incomparability
ensures neither group contains the other selected parent. Apply SR2
with P={u,v}; since both groups have p-1 elements, their union bound
forces A=B=S and |S|=p-1.

Now fix u's saturated group and take any proper original multiple M
of v. Use the actual phase a_M mod v as the second new phase. SR2
forces M to belong to S, since adjoining a label outside its p-1
elements would violate the bound. Reversing the roles gives equality
of the COMPLETE numerical descendant sets:

    Desc_D(u)=Desc_D(v)=S,
    Desc_D(w)={M in D:w|M,M>w}.                       (SR4)

This equality is impossible for incomparable u,v when |S|>=2. Put
ell=lcm(u,v). It divides every element of S, so original divisor
closure puts ell in D. It is a proper descendant of both parents,
hence belongs to S. Since p is odd, |S|=p-1>=2; choose N in S other
than ell and a prime r dividing N/ell. Both ur and vr divide ell*r,
which divides N, so divisor closure puts both in D. SR4 then places
both in S. Consequently v|ur and u|vr.

Writing g=gcd(u,v), the integers u/g and v/g are coprime and both
greater than one. The two divisibilities require both to divide the
same prime r, a contradiction. This proves SR3. The step p-1>=2 and
the use of divisor closure on N are essential; the argument is not
an assertion about an arbitrary labelled graph.

### A restriction on actual saturated-parent intersections

If two distinct saturated full-p-height original classes A_u,A_v
intersect, their labels are incomparable by irredundancy. Set
h=gcd(u,v). Actual CRT compatibility gives a_u=a_v mod h, and h has
the full p-height H. Applying SR3 whenever this h is qualified gives

    A_u intersect A_v !=empty
      ==> tau(gcd(u,v)/p^H)<=p-1.                    (SR5)

At p=3 this becomes

    A_u intersect A_v !=empty
      ==> gcd(u,v)/3^H is 1 or a prime.              (SR6)

Thus saturated ternary parents with a composite cofactor gcd, even
a prime square, must be disjoint as ACTUAL original classes. This
retains arbitrary global ternary height, all other heights and all
support sizes. It does not impose the same restriction on parents
whose descendant phase groups are not saturated.

### The remaining whole-cover forcing question

The new condition propagates a joint improvement obstruction through
the actual numerical divisor lattice. It goes beyond counting
additional private-neighbour suppliers outside one parent cone.
It still does not prove that a hypothetical whole cover contains a
violating collection of parents or a prohibited saturated pair.

For the ternary case, a pair of original labels s,t can certify a
saturated numerical parent when

    b=gcd(m_s,m_t,a_s-a_t),
    v_3(b)=H, tau(b/3^H)>=3,

and b is a proper divisor of both labels. Divisor closure supplies
the original b; the two endpoint classes project to the same phase
modulo b, and DR8 makes that group saturated. A same-top-support,
different-top-phase pair from the owned top-shadow argument has
b<gcd(m_s,m_t), so the proper-divisor condition holds if the other
two tests hold.

However, an owned top-shadow collision need not preserve the full
ternary phase or enough common cofactor information. Even when it
supplies b, its common endpoint phase differs from the OLD a_b
modulo b by comparable disjointness. It therefore does not establish the required OLD full-phase
compatibility, or make two such old parents intersect. This does not
assert that the old parent is absent from a projected lower fibre.
These old/new phase relations must not be identified.

SR5 concerns full original intersections, not projected lower-shadow
intersections. Disjoint original top hyperplanes can still share a
lower source, so SR5 alone cannot set an owned-shadow capacity to
zero. The outstanding bridge is to force either |J|>=p in SR2, or
two saturated parents satisfying the prohibited actual old-phase
compatibility. Neither occurrence follows from the private-neighbour
and owned top-shadow results currently used here. No bound on support
or prime-power height is added to bypass that missing implication.

## 12. Distinct odd quotient sums allow arbitrary repair primes and parent heights

The shared repair SR1--SR2 extends to ANY odd prime, including a prime
absent from Q, and to parents below its full global height. Keep the
same lexicographically minimal hypothetical whole cover. Fix p, put
H=v_p(Q), and choose a nonunit h|Q. Write

    a=v_p(h), n=h/p^a, r=p^(H-a+1), tau(n)>=r.        (AQ1)

Let P be a nonempty set of original parents satisfying h|d and
a_d=c mod h for ONE actual old phase c. Choose the new residues b_d
independently, and define the deleted descendant union J exactly as
in SR1--SR2, excluding P from J. Then

    |J|<=r-1.                                        (AQ2)

Choose r distinct positive divisors e_k|n. With rho=c mod p^a,
using rho=0 when a=0, define the repair classes by CRT:

    B_k={x=c mod e_k,
         x=rho+k*p^a mod p^(H+1)}, 0<=k<r.

Their numerical moduli p^(H+1)e_k are distinct odd nonunits and are
UNUSED because their p-height exceeds H. They cover the entire old
class c mod h: the next H-a+1 digits of any such integer choose
exactly one k, and all its cofactor congruences hold. Each new modulus
is at most r*h. All old and new moduli divide p*Q, providing one
finite common comparison period without discarding any integer lift.

Move the parents, delete J, and add these repairs. Every old parent
is covered by the B_k, every deleted child by at least one retained
moved parent, and every other original is unchanged. Thus the whole
old union remains covered, including joint liabilities. The new
cardinality is |D|-|J|+r, so |J|>r contradicts minimum cardinality.

If |J|=r, order the deleted labels M_1<...<M_r. Their quotients M_i/h
are DISTINCT ODD integers greater than one. Consequently

    M_i/h>=2*i+1,
    sum_(i=1..r)M_i>=h*r*(r+2)>r^2*h
                       >=sum_(k=0..r-1)p^(H+1)*e_k.  (AQ3)

The class count stays fixed while the modulus sum drops by at least
2*r*h. This contradicts the second extremal objective and proves AQ2.
The argument compares TOTALS: an individual deleted label can be
smaller than an individual repair label. Numerical distinctness and
oddness supply the required strict joint inequality.

When a=H, r=p, so DR8 and SR2 hold at every qualifying odd prime
without the smallest-prime restriction. For p=5 this also constrains
parents below the full global ternary height. When p=3 and a=H-1,
at least nine cofactor divisors give r=9 and a joint eight-child cap.
H=0 permits an unused prime; Report350 already forces the minimum's
support to be an initial segment of the odd primes, so such a prime
lies beyond that original support.

The saturated-parent argument extends as well. Two incomparable
original parents in the same old h-phase under AQ1 cannot BOTH have
a descendant phase group of size r-1. AQ2 would identify the two
groups and then their complete descendant sets. The divisor-lattice
contradiction in SR3--SR4 uses only r-1>=2 and original divisor
closure, so it applies unchanged. The parent labels themselves need
not have the same p-height; their divisibility by h suffices. In the
full-height specialization, distinct full-p-height originals that
each have a phase group of p-1 descendants therefore satisfy

    A_u intersect A_v !=empty
      ==> tau(gcd(u,v)/p^H)<=p-1.                    (AQ4)

These conditions hold simultaneously at every qualifying prime and
parent on the SAME original numerical palette and actual phases.
They do not identify original intersections with projected shadow
intersections or combine independently executed replacements. No
original exponent is bounded. A whole-cover theorem forcing a
violation remains missing. This is ordinary mathematics, not new
Lean verification or a literature-priority claim.

## 13. Several fresh heights give exact repair capacities below the single-layer threshold

Keep one original period Q, an odd prime p, H=v_p(Q), and a nonunit
h=p^a*n dividing Q, with gcd(p,n)=1 and 0<=a<=H. Put

    r=p^(H-a+1), t=tau(n).

The permitted repair labels in this section are exactly

    p^(H+1+j)*e,  j>=0, e|n.                         (ML1)

They are distinct across different heights or cofactors and are all
unused by the original family. The existence and minimum statements
below concern this specified palette. Other repair labels or repairs
of a smaller private region are not excluded by their necessity claim.

### Finite repair existence and its minimum number of classes

A finite family using distinct labels from ML1 can cover the ENTIRE
class c mod h if and only if

    t>r*(p-1)/p.                                    (ML2)

Restrict a proposed repair to c mod h. An incompatible phase is empty;
every nonempty restriction at height H+1+j is one p-prefix cylinder
of relative mass 1/(r*p^j). At most t labels occur at each height.
For any finite largest layer L, its covered mass is at most

    (t/r)*sum_(j=0..L)p^(-j)<t*p/(r*(p-1)).

Coverage of the target mass one therefore requires ML2, including
its strict inequality.

For sufficiency, start with the r target cylinders at height H+1.
At layer j, cover min(t,s_j) of the s_j uncovered cylinders, assigning
distinct divisors e|n and imposing the cofactor phase c mod e. The
cofactor condition is automatic on c mod h. Expand each unselected
cylinder into its p children. Before termination,

    s_0=r, s_(j+1)=p*(s_j-t).

If t>=r, the construction stops at once, using N=r classes. If t<r,
write

    delta=p*t-(p-1)*r>0,
    J=min{j>=0:p^j*delta>=t},
    s=(p*t-p^J*delta)/(p-1), N=t*J+s.                (ML3)

Solving the recurrence shows that it terminates with layer counts
t,...,t,s, with J full layers and 1<=s<t. To verify strict s<t,
equality would give

    t=p^(H-a+1+J)/(1+p+...+p^J).

Here J>=1; the denominator exceeds one and is coprime to p, so this
cannot be an integer. The constructed cylinders form a complete
disjoint prefix cut and cover every integer in c mod h, including
all lifts beyond Q.

The value N is the minimum number of repair classes from ML1.
Indeed, discard empty or redundant restrictions from any finite
repair. The remaining cylinders form a complete prefix-free cut
in a p-ary forest with r roots. If u_j nodes are exposed at layer j
and m_j<=t are chosen as leaves, then

    u_(j+1)=p*(u_j-m_j).

At every layer before the greedy construction terminates, its exposed
node count is at most u_j, and its internal-node count is at most
u_j-m_j. Later internal-node counts are nonnegative. Every complete
forest cut has

    number of leaves=r+(p-1)*sum_j(number of internal nodes at j).

Thus no repair uses fewer than N leaves. Equality forces the same
internal-node counts and consequently the same layer counts as ML3.
This proof allows arbitrary original repair phases: a minimum repair
cannot contain an empty or redundant target restriction.

### Exact modulus sum at the minimum number

Let sigma_u(n) be the sum of the u smallest positive divisors of n,
and sigma(n)=sigma_t(n). Among all N-class repairs from ML1, the
minimum numerical modulus sum is

    S=p^(H+1)*sigma_r(n),                            if t>=r;
    S=p^(H+1)*(sigma(n)*(p^J-1)/(p-1)
                  +p^J*sigma_s(n)),                 if t<r. (ML4)

Minimum cardinality fixes the layer counts. Every full layer uses
all divisors, and the last layer uses its smallest required divisors.
These assignments are compatible with the same prefix construction,
so the bound is attained. Labels at different heights remain distinct
because every e is coprime to p.

### A shared old-phase obstruction in a hypothetical minimum cover

Now impose the same hypothetical distinct-odd whole-cover minimum
as AQ1--AQ4. Select a nonempty set P of original parents such that
h|d and a_d=c mod h for every d in P, and choose new phases b_d.
Define the union of removed child labels exactly as in AQ1:

    J_d={M in D minus P:d|M,M>d,a_M=b_d mod d},
    J_removed=union_(d in P)J_d.

Move the selected parents, delete this union, and add the minimum
ML1 repair. Every old selected parent lies in c mod h and is repaired;
every deleted child lies in a moved parent; all other originals are
retained. Thus the complete old union, including joint liabilities,
remains covered on a common period dividing p^(H+1+J)*Q (with J=0
in the single-layer case). The new labels are fresh, odd and nonunit.
The two extremal objectives require

    |J_removed|<=N;
    |J_removed|=N ==> sum_(M in J_removed)M<=S.       (ML5)

For every parameter choice satisfying ML2, the repair sum and the
removed union satisfy the uniform bounds

    S<h*N^2,   |J_removed|<=N-1.                     (ML6)

The first inequality is proved below. For the second, ML5 already
excludes |J_removed|>N. If |J_removed|=N, each deleted M is a proper
odd multiple of h, so distinctness gives

    sum_(M in J_removed)M>=h*N*(N+2)>h*N^2>S,

contradicting ML5. Thus no additional modulus-sum condition is needed.

Put B=N-1. Two incomparable original parents in this same old h-phase
cannot both have a descendant phase group of size B. Here B>=2.
The union bound would identify their selected groups; fixing one group
while varying the other parent's new phase would identify their
COMPLETE descendant sets. SR4's original divisor-lattice argument
then contradicts incomparability. This concerns actual old phases
and original classes, not projected-shadow intersections.

### The repair sum is uniformly smaller than h times the squared count

In the single-layer case, N=r>=3 and ML4 gives

    S/h=r*sigma_r(n)/n<r^2=N^2.

The inequality is strict because r distinct divisors cannot all equal n.

For the multilevel case, write k=H-a+1, so r=p^k and t<r. Then k>=2.
The positive integer delta from ML3 satisfies

    delta=p*(t-(p-1)*p^(k-1))>=p.

Therefore p^(k-1)*delta>=r>t, and the stopping depth obeys

    1<=J<=k-1.

The complementary-divisor bijection and oddness of n give

    sigma(n)/n=sum_(e|n)1/e
       <=Hodd(t):=sum_(i=0..t-1)1/(2*i+1).

Indeed, the i-th positive divisor of an odd integer is at least 2*i-1.
Strict convexity of 1/(2*x+1) on each interval
[i-1/2,i+1/2], for i=1,...,t-1, gives

    1/(2*i+1)<integral_(i-1/2)^(i+1/2) dx/(2*x+1).

Summing these intervals proves

    Hodd(t)<1+(ln t)/2<1+k*(ln p)/2.

Using sigma_s(n)<=sigma(n) in ML4, and
N=t*J+s>t*J>r*(p-1)*J/p, now yields

    S/h<r*p^J*p*Hodd(t)/(p-1),
    S/(h*N^2)
       < [p^3/(p-1)^3]*(1+k*(ln p)/2)
            /[p^(k-J)*J^2].

All quantities divided by here are positive. For fixed p,k the
consecutive ratio of a_J=p^(k-J)*J^2 is

    a_(J+1)/a_J=((J+1)/J)^2/p,

which decreases with J. Hence a_J increases and then decreases,
with either part possibly empty, and its minimum on 1<=J<=k-1 is
at an endpoint:

    p^(k-J)*J^2>=min(p^(k-1),p*(k-1)^2).

Three parameter ranges make the displayed ratio strictly below one.

For p>=5 and k>=3, p^3/(p-1)^3<=125/64<2 and ln p<=p-1, so its
numerator is strictly below

    2+k*(p-1)<=k*p.

Both endpoint denominators are at least k*p: (k-1)^2>=k, and
p^(k-2)>=k. The latter inequality starts at k=3 with p>=5>=3;
multiplication by p preserves its inductive lower bound.

For p=3 and k>=3, use ln3<10/9. For example, the first five terms
of exp(10/9) already sum to 59453/19683>3. The ratio's numerator is
therefore strictly below

    (27+15*k)/8.

Both endpoint denominators are at least this quantity. The first,
3^(k-1), equals it at k=3, and its induction follows from

    3*(27+15*k)-(27+15*(k+1))=39+30*k>0.

The second, 3*(k-1)^2, is larger at k=3; after multiplying the
difference by eight, its increment is 48*k-39>0. Thus the strict
ratio bound also holds when one endpoint estimate is equality.

For k=2 and p>=7, J=1 and the denominator is p. Here
p^3/(p-1)^3<=343/216<8/5 and ln p<=(p-1)/2. The logarithm bound
follows from ln5<2 and the positive derivative of
(x-1)/2-ln x for x>=5; exp2>1+2+2^2/2=5 proves the initial value.
The numerator is strictly below

    (8/5)*(1+(p-1)/2)=4*(p+1)/5<p.

Only (p,k)=(3,2) and (5,2) remain. ML2 and t<r leave respectively
t=7,8 and t=21,22,23,24. All have J=1 and s=p*(r-t)<t.
Every proper divisor of odd n is at most n/3, and the s smallest
divisors omit n. Thus

    sigma(n)/n<=1+(t-1)/3,   sigma_s(n)/n<=s/3,
    S/h<=(r/3)*(t+2+p*s).

The six exact comparisons are:

| p | k | t | s | N | Upper bound for S/h | N^2 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
|3|2|7|6|13|81|169|
|3|2|8|3|11|57|121|
|5|2|21|20|41|1025|1681|
|5|2|22|15|37|825|1369|
|5|2|23|10|33|625|1089|
|5|2|24|5|29|425|841|

Each upper bound is strictly below N^2. These cases complete the
proof of S<h*N^2 for every ML2-qualified h, at arbitrary original
p-height and cofactor support.

### A range not covered by the single-layer qualification

The following exact instances have t<r and hence fail AQ1's t>=r
qualification. They use a=0 and c=0; the displayed construction gives
the repair residues by CRT.

| p | H | n=h | r | t | Layer counts | N | S | h*N*(N+2) |
| ---: | ---: | --- | ---: | ---: | --- | ---: | ---: | ---: |
|3|1|5^6=15625|9|7|7,6|13|281241|3046875|
|3|1|5*7*11=385|9|8|8,3|11|5535|55055|
|3|2|5^4*7^3=214375|27|20|20,20,3|43|33742359|414815625|

The corresponding conditional union caps are 12,10,42. In their
complete comparison periods 421875,10395,52093125, respectively,
the target classes have 27,27,243 residues; each is covered exactly
once by the constructed repair. These are repairs of one class,
not distinct-odd whole covers.

At a=H, r=p and the integer condition ML2 reduces to t>=p, recovering
the earlier single-layer qualification. The added cases lie below
the global p-height. This extends the possible common repairs while
retaining arbitrary original support, phases and heights. A theorem
forcing a hypothetical whole cover to violate these conditions remains
missing. These are ordinary mathematical deductions and exact finite
controls, not new Lean verification or a literature-priority claim.

## 14. Deleting some old parents strengthens the shared repair constraint

Keep the same hypothetical whole cover minimizing class count and then
modulus sum. Fix an ML2-qualified h, its fresh repair count N and sum S,
and put B=N-1. In particular, S<h*N^2. The parents below are original
labels from this ONE family; numerical moduli and phases remain those
of that family until the stated simultaneous replacement.
This specializes the existing PH2 replacement rule using ML4--ML6;
it is not a new general exchange principle. The finite example below
separates the resulting constraints from the older descendant-only
ML6 tests, not from PH2 itself.

### A joint deletion and movement inequality

Let P be any set of original labels with h|d and a_d=c mod h for
every d in P. Partition P into R, the parents retained and moved, and
E=P minus R, the parents deleted. Choose a new phase b_d for each d
in R. Define

    J=union_(d in R){M in D minus P:
                     d|M, M>d, a_M=b_d mod d}.

Then the stronger joint bound is

    |E|+|J|<=B.                                      (MX1)

Move each retained d to b_d, delete E and J, and add the N fresh
classes repairing the entire c mod h. Every OLD class with label in P
is contained in the repaired h-class. Every removed class in J is
contained in a retained moved parent. All other originals stay. This
preserves the whole old covered union, including points with several
old owners; separate private regions do not replace joint liability.

The sets E and J are disjoint and their labels are all multiples of h.
If their total count exceeds N, the new family has fewer classes. If
the count equals N, their quotients by h are N distinct positive odd
integers, possibly including1. In increasing order they are at least
1,3,...,2*N-1, so

    sum_(M in E union J)M>=h*N^2>S.

The class count is unchanged and the modulus sum strictly falls.
Both alternatives contradict the two extremal objectives, proving MX1.
Retained moved labels cancel from this sum comparison. Freshness at
the p-coordinate prevents a duplicate with ANY retained original.

Taking E empty recovers ML6. Taking R empty only gives the old-phase
count cap, which already follows from ML6 and divisor closure.
The added constraint keeps both terms: deleting old parents spends
part of the same repair budget available for descendant deletions.

### Old-phase occupancy limits cross-phase descendant groups

Let

    P_c={d in D:h|d,a_d=c mod h}, q_c=|P_c|,
    S_u(b)={M in D:u|M,M>u,a_M=b mod u}.

For u in P_c and b mod h different from c, every label in S_u(b)
lies outside P_c. Apply MX1 with R={u} and E=P_c minus {u}. It gives

    q_c-1+|S_u(b)|<=B.                              (MX2)

The condition on b is necessary for this full-group formula: when
b mod h=c, the descendants already belong to P_c and cannot also be
counted as additional deleted labels.

There is an actual-intersection form without that condition. Suppose
P consists of q originals whose moduli are multiples of h and whose
ACTUAL classes all contain the same integer x. No proper original
descendant of u in P belongs to P, by comparable-class disjointness.
Thus for every u in P and every descendant phase b,

    q-1+|S_u(b)|<=B.                                (MX3)

This concerns one actual source point. Intersections of projected
shadows do not supply the premise.

In particular, if |S_u(b)|=B, then u is the ONLY original label in
its old h-phase:

    P_(a_u mod h)={u}.                              (MX4)

First recover the elementary cap |P_c|<=B. If P_c is nonempty,
divisor closure puts h in D. At c=a_h, comparable disjointness gives
P_c={h}; at every other c, P_c is the proper-descendant phase group
of h, so ML6 applied to parent h gives the cap. If b mod h=a_u mod h,
the distinct originals u and the B members of S_u(b) would give B+1
members in one such group. Hence b has a different h-phase, and MX2
forces q_c=1.

The earlier restriction excluded two saturated incomparable parents.
MX4 excludes every other original in this old h-phase, including a
maximal label with no descendants. At h=u, comparable disjointness
already gives isolation; the added force concerns proper interfaces h.

For example, let p be an original support prime, H=v_p(Q), and let
u have full p-height and a descendant group of size p-1. For EVERY
other full-p-height original v, not assumed saturated,

    A_u intersect A_v !=empty
      ==> tau(gcd(u,v)/p^H)<=p-1.                    (MX5)

Otherwise h=gcd(u,v) has a single-layer repair with N=p. An actual
intersection makes u and v share the same old h-phase, contradicting
MX4. Thus the second saturation premise in AQ4 is unnecessary.

### A divisor-closed noncover separates the two constraints

The following17 original classes have full period13125:

| Original modulus | Original residue |
| ---: | ---: |
|3|0|
|5|0|
|7|0|
|15|7|
|21|4|
|25|3|
|35|3|
|75|4|
|105|8|
|125|4|
|175|4|
|375|1|
|525|1|
|625|1|
|875|1|
|1875|2|
|2625|2|

The labels are distinct odd nonunits, divisor-closed above1, and the
prime classes are normalized. All70 comparable pairs are disjoint.
Every original has a nonempty complete private region. The original
covered count is9065 out of13125, so this is a NONCOVER.

It satisfies every ML6 shared-parent descendant-union cap. For a
nonempty parent collection, its interface h is an original label by
divisor closure. ML2 implies p<=tau(h), and the maximum tau(h) among
these originals is16. Thus p in {3,5,7,11,13} exhausts all eligible
odd primes, including primes absent from the original period. The
exact interfaces and maximum descendant-union sizes are:

| h | p | N | Maximum union over same-old-phase parents and all new phases |
| ---: | ---: | ---: | ---: |
|75|3|3|2|
|105|3|3|1|
|375|3|3|2|
|525|3|3|1|
|525|11|11|1|
|875|3|11|1|
|1875|3|3|0|
|2625|3|3|0|
|2625|7|7|0|
|2625|11|11|0|
|2625|13|13|0|

At h=75,p=3 the fresh repair has N=3, B=2 and
S=9+45+225=279. The old parents375 and525 share phase1 modulo75.
Parent375 has the two-child group {1875,2625} at phase2 modulo375;
parent525 has only child2625. Retaining and moving both removes at
most those two children and passes the old bound. Instead delete525,
move375 to phase2, delete1875 and2625, and add

    1 mod9, 31 mod45, 151 mod225.

These three fresh classes cover the whole old class1 mod75. The moved
375 class covers both deleted children. This is MX1 with |E|+|J|=3>B;
the removed modulus sum is5025, whereas the repair sum is279.

This also separates MX5 from AQ4:375 is saturated and525 is not,
their actual classes meet at integer1, and
tau(gcd(375,525)/3)=tau(25)=3>2.

Direct enumeration on the COMPLETE common period39375 gives:

| Quantity | Original family | Replacement |
| --- | ---: | ---: |
| Class count |17|17|
| Sum of numerical moduli |7491|2745|
| Covered residues |27195|29395|

No previously covered residue is lost;2200 new residues are covered.
Both families miss integer11. Thus this is a union-preserving
improvement and a strict separation from ALL the old ML6 caps on a
divisor-closed irredundant input. It is not a whole cover, a globally
minimal realization, or a counterexample to Erdős#7.

The [exact checker](../../../frontier/cover-geometry/composite-parent-contraction/mixed_parent_exchange.py)
reads the [literal original and replacement classes](../../../frontier/cover-geometry/composite-parent-contraction/mixed_parent_exchange_originals.json)
and produces the [complete-period counts and old-cap checks](../../../frontier/cover-geometry/composite-parent-contraction/mixed_parent_exchange.json).
It checks all11 eligible interfaces,25 nonempty same-old-phase parent
subsets and39 descendant-phase group choices, including empty groups;
phases with the same descendant group have identical union effects.
From that program's directory, reproduce with Python3.9+ and its
standard library:

```sh
python3 -I -S -B mixed_parent_exchange.py --input mixed_parent_exchange_originals.json --output mixed_parent_exchange.json
```

The unrestricted missing implication remains: whole coverage must
force a violation of some available joint replacement constraint.
MX1--MX5 strengthen those constraints without supplying that forcing
theorem. These are ordinary proofs and finite arithmetic, not new
Lean verification or a literature-priority claim.

## 15. Retained pure powers reduce the fresh repair forest

Fix the same hypothetical minimum distinct-odd whole cover, original
period Q, odd prime p, H=v_p(Q), and h=p^a n|Q with n>1, gcd(p,n)=1.
Select nonempty original parents P whose actual classes lie in c mod h.
Every pure p-power original stays when parents divisible by h and their
proper descendants are moved/deleted: n>1 prevents such a pure label
from being selected or absorbed.

Let I be the heights i with a<i<=H for which p^i is original and
its actual residue equals c modulo p^a. The pure classes are pairwise
disjoint by comparable-original disjointness. Original pure classes of
height at most a are disjoint from c mod h: otherwise they would contain
one selected original parent, contrary to the same premise. A pure
class indexed by i in I covers exactly p^(H+1-i) of the r=p^(H-a+1)
first-fresh roots of c mod h. Thus the residual forest has

    R=r-sum_(i in I)p^(H+1-i).                       (RP1)

roots. They all share the same cofactor condition c mod n. In particular
R is a positive multiple of p and

    R >= ((p-2)r+p)/(p-1) > r*(p-2)/(p-1).

The inequality allows every possible subset of the actual pure chain;
no compatible phases are invented. Existing other originals may cover
more of the target, but are not used by this stated construction.

Using exactly the fresh palette p^(H+1+j)e, j>=0,e|n, together with the
retained pure classes, the whole c mod h can be covered iff

    t=tau(n) > R*(p-1)/p.                           (RP2)

This is the old forest argument with R roots. Necessity is the finite
geometric capacity sum; sufficiency repeatedly selects min(t,s_j)
exposed roots and expands the rest into p children. If t>=R, N=R.
Otherwise set

    delta=p*t-(p-1)*R,
    J=min{j>=0:p^j*delta>=t},
    s=(p*t-p^J*delta)/(p-1), N=t*J+s.                (RP3)

Now 1<=s<=t, including equality. That is the only change needed in the
minimum-count proof. The greedy construction minimizes all preceding
internal-node counts, and a minimum cardinality cut must have the same
layer counts. Its exact minimum fresh modulus sum at count N is

    S=p^(H+1)*sigma_R(n),                         t>=R;
    S=p^(H+1)*(sigma(n)*(p^J-1)/(p-1)+p^J*sigma_s(n)), t<R.

The uniform tie comparison still holds:

    S<h*N^2.                                        (RP4)

For t>=R, if R=r use the previous sigma_R(n)<R*n argument. If R<r,
then k=H-a+1>=2 and R>=6. Complementary distinct divisors give
sigma_R(n)/n<=Hodd(R). The inequality Hodd(R)<R/2 for every R>=5
follows from its R=5 value and the increment 1/(2R+1)<1/2. Since r<2R,

    S/h=r*sigma_R(n)/n<2R*(R/2)=R^2.

For t<R, k>=2, delta is a positive multiple of p, and 1<=J<=k-1.
With the old strict Hodd(t)<1+k*ln(p)/2 estimate,

    S/(h*N^2)
    < [p^3/((p-1)*(p-2)^2)]*(1+k*ln(p)/2)
        /[p^(k-J)*J^2].

Here t>R*(p-1)/p>r*(p-2)/p is the new lower bound used for N>tJ.
The denominator is at least min(p^(k-1),p*(k-1)^2), as before.

For p>=7, A=p^3/((p-1)*(p-2)^2)<7/3. Its logarithmic derivative has
numerator 6-5p<0, so it suffices to check p=7. Also ln p<=(p-1)/3:
ln7<2 follows from exp2>7, and the difference is increasing for p>=7.
For k=2, the numerator is <7(p+2)/9<=p. For k>=3 it is
<(7/3)(1+k*(p-1)/6)<=k*p, while both denominator endpoints are >=k*p.

For p=5,k>=3, ln5<5/3 (the first five exponential terms already
sum to 10009/1944>5) gives numerator <125*(6+5k)/216. Both endpoints
exceed this at k=3; multiplication by5 preserves the exponential
comparison, and the quadratic increment5*(2k-1) exceeds625/216.

For p=3,k>=6, ln3<10/9 gives numerator <(27+15k)/2. Both endpoints
exceed this at k=6, and their increments dominate the linear increment
15/2 thereafter.

The only cases left are (p,k)=(3,2),(3,3),(3,4),(3,5),(5,2). Exhaust
ALL R in p*Z with r*(p-2)/(p-1)<R<=r and ALL integers
R*(p-1)/p<t<R. This is a finite superset of actual retained-pure
geometries. Set C=1+5k/9 for p=3 and C=1+5k/6 for p=5. Then
sigma(n)/n<C. If s<t, every selected final-layer divisor is proper,
so sigma_s(n)/n<=s/3; use min(C,s/3). If s=t use C instead. Therefore

    S/h < U=r*((p^J-1)/(p-1)*C+p^J*last),
    last=min(C,s/3) if s<t; last=C if s=t.

Independent exact rational computation gives:

| p,k | Cases | Maximum U/N^2 | Maximizer R,t |
| --- | ---: | --- | --- |
|3,2|3|23/32|6,5|
|3,3|30|531/625|15,11|
|3,4|273|553/648|48,33|
|3,5|2460|55539/67712|132,89|
|5,2|7|25/49|20,18|

All2773 inequalities are strict;19 cases have s=t and use that
branch. The [exact checker](../../../frontier/cover-geometry/composite-parent-contraction/retained_pure_repair.py)
uses the [five exception ranges and literal classes](../../../frontier/cover-geometry/composite-parent-contraction/retained_pure_repair_originals.json)
to produce the [finite comparisons and complete-period control](../../../frontier/cover-geometry/composite-parent-contraction/retained_pure_repair.json).
From that program's directory, reproduce with Python3.9+ and its
standard library:

```sh
python3 -I -S -B retained_pure_repair.py --input retained_pure_repair_originals.json --output retained_pure_repair.json
```

Consequently the mixed deletion/movement bound still gives
|E|+|J_removed|<=N-1 with this cheaper repair. Its repair count N can
now depend on the ACTUAL old h-phase c. Same-phase occupancy can be
bounded by deleting that group directly; using an unrelated old
parent h-phase a_h is not justified when these counts differ.

A small actual control uses the five original classes

    0 mod3, 0 mod5, 2 mod25, 3 mod125, 1 mod625.

This is a divisor-closed irredundant noncover on period1875, with938
holes; its six comparable pairs are disjoint. Only its retained
0 mod3 class is used to help repair the target1 mod625. Here
p=3,H=1,a=0,r=9,R=6,t=5. The old ML2 test fails (5<=6), while the
retained-pure test passes (5>4), with layer counts5,3,N=8,S=7866.
Fresh classes are

    1 mod9, 11 mod45, 76 mod225, 626 mod1125, 3751 mod5625,
    8 mod27, 71 mod135, 26 mod675.

On the full comparison period16875, target1 mod625 has27 points.
The retained0 mod3 covers9 and the fresh classes disjointly cover the
remaining18; S7866<h*N^2=40000. This verifies the interface extension,
not a cardinality improvement of this five-class NONCOVER. It extends
the available joint-replacement tests to some interfaces failing ML2;
a whole-cover forcing theorem is still missing. These are ordinary
proofs and exact finite computations, not new Lean verification, a
literature-priority claim, or a solution of unrestricted Erdős#7.

## 16. Retained pure powers turn private-point demand into height bounds

Assume that a finite distinct odd nonunit whole cover exists, and choose
ONE cover globally minimizing first the number of classes and then their
modulus sum, as in [Report350, EB1](../../321-384/350-extremal-paired-branch-and-source-support.md#1-extremality-supplies-the-divisor-structure). Let its original numerical labels be D,
its full period be Q, and H_p=v_p(Q). Irredundancy, divisor closure,
comparable-class disjointness and initial odd-prime support refer to this
same chosen family. The bounds below are for this globally extremal cover;
they are not height bounds on every arbitrary irredundant odd cover.

The supplier lower bound is existing mathematics: use the original-shell
identity and [QC1--QC2](../../../../../../Library/Arith/lettlsun2008cosets.md#arbitrary-quotient-cuts-collapse-to-the-same-depth-suffixes). The top-only
private fan is also already [Report371, section2](371-private-top-fans-and-ancestor-cuts.md). Neither is a new theorem
here. The purpose is to connect that retained all-depth information to
section15's actual repair capacity RP1--RP4. These are ordinary deductions,
not new Lean declarations or claims of literature priority.

### The existing demand in the exact phase needed by repair

Fix p in the original support and a private point x of the original pure
class p^H, where H=H_p. For 1<=a<H, put c=x mod p^a. QC1--QC2 give

    S_a(x,p) >= (H-a)(p-1).

Every contributing original label M has p-height h_M>a, agrees with x
modulo p^a, agrees with x at its entire p-free cofactor, and has weight
p^(1-h_M+b_M)<=1. The pure owner p^H is not among these suppliers.
Consequently the actual phase packet

    P_a(c)={M in D:p^a|M,a_M=c mod p^a}

has at least

    1+(H-a)(p-1)                                    (HC1)

original labels. This count directly reuses QC2; it is not a separately
introduced private-prefix theorem. The original p^a class has a different
phase, by comparable disjointness. Every supplier's complete p-free
congruence contains the SAME x, not a source selected separately per label.

### Repair with another prime gives a finite height optimization

Let q!=p be any odd prime, including a prime absent from Q, and put
K=H_q. For the target h=p^a, all original pure q-powers are retained:
none can be a parent or deleted descendant whose modulus is divisible
by p^a. Since h has q-height zero, every pure q-power is compatible
with its old target phase at the q-coordinate. Their actual disjoint
classes remove exactly

    sum_(i=1..K) q^(K+1-i)

first-fresh q-roots, independently of c. Thus RP1 gives

    R=R_q(K)=q^(K+1)-sum_(i=1..K)q^(K+1-i)
            =q*((q-2)q^K+1)/(q-1),
    t=tau(p^a)=a+1.                                 (HC2)

No favorable phase is substituted: because the target has q-height zero,
these retained-pure savings are phase-independent in this particular
consumer. Relative-height-positive consumers must still use their actual
compatible pure powers, as required by RP1.

Define A_q(K)=(q-2)q^K+1. Within this specified fresh-q palette, the RP2 criterion is t>A_q(K), equivalently

    a>=A_q(K).                                      (HC3)

Let N_q(R,t) be the exact RP3 forest count: it is R when t>=R; otherwise

    delta=q*t-(q-1)*R,
    J=min{j>=0:q^j*delta>=t},
    s=(q*t-q^J*delta)/(q-1),
    N=t*J+s.                                        (HC4)

The final layer may have s=t. RP4's strict modulus-sum estimate gives
the actual phase occupancy cap |P_a(c)|<=N-1. Combining it with HC1 gives,
whenever H>a,

    (H-a)(p-1)<=N-2.

If H<=a, the following bound holds automatically. Hence in all cases

    H_p <= B_(p;q,K)
        := min_(A_q(K)<=a<=R_q(K)-1)
                  [a+floor((N_q(R_q(K),a+1)-2)/(p-1))].     (HC5)

This minimum is genuinely finite. At a>=R-1, t>=R and N=R, so its
objective increases with a; none of the a>R-1 can improve the value
at R-1. The first feasible index A_q(K) is at most R-1. All selected
repair moduli have q-height above K and are fresh relative to the ENTIRE
original family.

One must optimize a rather than always choose its first feasible value.
For example q=5,K=1,p=3 attains the displayed minimum28 at a=19,N=20.
For q=3,K=3,p=5, the optimum46 occurs at a=30,N=68; the first feasible
a=28 would give50. (At that first index N=90, so the bound is28+22=50.)

### An absent odd prime bounds every height at fixed support

For an absent odd prime ell, K=0, R=ell and A=ell-1. The optimization
has just one index a=ell-1 and N=ell. Thus

    H_p <= ell-1+floor((ell-2)/(p-1))                 (HC6)

for every present p. Taking ell to be the smallest absent odd prime
uses the existing initial-support conclusion of report350. For each
fixed finite support, all exponents of a globally extremal putative
cover now have explicit finite bounds. Support itself is still unbounded;
this does not reduce the unrestricted problem to one finite search.

This is an added consequence of the repair constraints, not a new
private-point lower bound. The classical aggregate s-number bound
n>=1+sum_p H_p(p-1) already bounds heights when n is fixed. HC6 does
not require a numerical bound on that unknown minimum n.

### Exact finite parameter values

Entries are the optimized upper bounds B_(p;q,K). A dash means q=p,
which is not this consumer's domain. These are exact integer parameter
calculations of HC5, conditional on the stated global extremality and
actual heights. They do not assert existence of a cover with those
parameters.

| q | K | R | Candidate a range | p=3 | p=5 | p=7 | p=11 | p=13 | p=17 | p=19 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|3|1|6|4..5|—|5|5|4|4|4|4|
|3|2|15|10..14|—|15|13|12|11|11|11|
|3|3|42|28..41|—|46|41|36|35|33|32|
|5|1|20|16..19|28|—|21|19|18|17|17|
|5|2|95|76..94|140|—|104|94|91|88|86|
|7|1|42|36..41|61|51|—|43|41|40|39|
|7|2|287|246..286|428|357|—|300|292|281|278|

For H_3=1, choosing a=4 uses R=6,t=5 and layer counts(5,3), so N=8.
Consequently

    H_5<=5, H_7<=5,
    H_p<=4 for every present p>=11.                  (HC7)

The same suffix-demand consumer without retained pure3 has R=9 and
first feasible a=6. Its optimized bounds for p=5,7,11 are8,7,7,
respectively. Thus the retained-pure contribution yields a strict
parameter improvement; it is not merely a renaming of ML2's forest.

For a concrete aggregate-count comparison, the initial-support profile
(H3,H5,H7,H11)=(1,6,1,1) permits43<=n<=55 under just the classical
s-number lower bound and n<=tau(Q)-1. HC7 excludes that profile for
the chosen globally extremal cover. This is a parameter comparison,
not an actual covering family or an independence result against all
classical or repository constraints.

### Keeping the common cofactor source gives a stronger H3=1 bound

Assume H3=1 and let s be the number of original support primes. Fix
p>3 and H_p>2. Use HC1 at a=2, retaining its specific QC1 suppliers and the pure owner.
This actual subset contains at least

    1+(H_p-2)(p-1)

labels. At most H_p-2 of these are pure p-powers, so at least

    1+(H_p-2)(p-2)                                  (HC8)

are mixed suppliers. All have p-height>2 and their full p-free
cofactor congruences contain the SAME private point x.

Partition these actual labels into disjoint buckets. First put every
supplier whose cofactor contains3 into the3-bucket. Assign each remaining
mixed supplier to one chosen prime q!=3,p dividing its cofactor, using
one fixed rule. No label appears in two buckets.

All3-bucket labels are proper descendants of h=3*p^2 in one actual
phase determined by x mod3 and x mod p^2. Repair at3 uses the full
original3-height: R=3,t=tau(p^2)=3,N=3. Its exact phase capacity is2.

Every q-bucket has the same original interface h=p^2*q and actual
phase given by x. Repair at3 retains the pure3 class: R=6,
t=tau(p^2*q)=6,N=6. Each such bucket has capacity5. There are at most
s-2 such q-buckets. Therefore

    1+(H_p-2)(p-2) <= 2+5*(s-2)=5s-8,
    H_p <= 2+floor((5s-9)/(p-2)).                    (HC9)

For H_p<=2 the second inequality is automatic because s>=2. The
bounds use the same actual source in every bucket. They sum disjoint
sets of labels; they do not sum separately optimized physical repairs
or execute all repairs simultaneously.

Examples within initial odd-prime support:

* s=4: H5<=5, H7<=4 and H11<=3.
* s=9: H23<=3 and H29<=3.
* s=11: H29<=3, H31<=3 and H37<=3.
* For any present p>5s-7, HC9 forces H_p<=2.

HC9 and HC7 can be imposed together. The existing
[Report528, FC13--FC14](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#eight-old-primes-and-arbitrary2931-originals)
already excludes H3=1 with initial support size at most10, even allowing
unrestricted ternary heights on the later29/31 originals. Thus the s=4
and s=9 rows above illustrate the parameter bounds; they are not new
exclusions of unresolved branches. The unrestricted H3=1 branch still
allows s>=11, and no upper bound on support size has been obtained.

### A local common-source star still does not ensure a cheap common divisor

The actual family

    0 mod3, 0 mod5, 6 mod25, 7 mod125, 8 mod625,
    1 mod15, 52 mod75, 253 mod375, 4 mod1875

is divisor-closed, comparable-disjoint and irredundant. On the complete
period1875 it has807 holes, including2. Private witnesses in the listed
order are3,5,56,7,8,1,52,253,4. No whole-cover or global-minimum premise
is claimed.

Fix the cofactor source1 mod3 and the5-adic tail zero. The four nonzero
first5 digits correspond to actual CRT points1,1252,628,4. They are
covered by the original labels15,75,375,1875 respectively. All have
cofactor3 at the same actual phase. Nevertheless h=3 has no repair
in the stated fresh-prime forest palette: with repair prime3 its
retained-root count is3 and t=1; with any other odd repair prime q,
t=2<=q-1<=R(q-1)/q. This finite noncover refutes only the inference
from those local star and divisor conditions to a feasible common
cofactor repair. It does not refute any theorem using whole coverage.

### Verification and unresolved interface

The [portable exact consumer](../../../frontier/cover-geometry/composite-parent-contraction/repair_height_bounds.py)
compares the exposed-root recurrence with the closed RP3 count, retains
the minimizing a and N, compares the unreduced forests, and checks the
complete period of the finite noncover. Its [exact output](../../../frontier/cover-geometry/composite-parent-contraction/repair_height_bounds.json)
includes q in{3,5,7}, K in{0,1,2}, plus q3K3, with11 target primes
before excluding q=p. The K0 rows apply only when q is actually absent;
initial-support compatibility is recorded explicitly. From the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/repair_height_bounds.py
```

The program uses the standard library, reads no external input, and writes
JSON to stdout unless an explicit `--output PATH` is provided. Its checks
remain active under `-O`; normal and optimized outputs agree. The general
height consequences rest on the ordinary proofs above, not extrapolation
from this parameter grid. They are not new Lean verification.

A two-coordinate or arbitrary-interface concentration does not follow
merely by combining separately changed prime digits: each supplier is
forced to contain its changed prime power, not the other target factors.
HC8--HC9 state exactly how their additional factors arise from the SAME
source. What remains is a whole-cover theorem forcing violation of these
joint height/phase capacities, or another improving replacement. The bounds
allow unbounded support and many feasible height profiles.

## 17. Small interfaces bound whole-cover numerical inventories

Retain ONE hypothetical whole distinct odd cover globally minimizing
first the number of classes and then their modulus sum, and assume H3=1.
All numerical labels and actual phases below belong to that family.
The following inventory bounds consume the existing fresh-repair and
same-phase occupancy principles of sections13--15; they are ordinary
deductions, not new Lean results or an unrestricted noncoverage theorem.

### Two distinct nonternary primes

Let p,q>=5 be distinct support primes and h=3pq. Three original multiples
of h cannot have the same phase c modulo h. To see the section15 repair
explicitly, delete those three originals and cover all of c modulo h
with the fresh labels9,9p,9q. Assign them the three different modulo9
roots above c modulo3; for their respective cofactors1,p,q retain c's
actual phase. Every point in the target meets one new class. H3=1 makes
all three numerical labels fresh relative to the entire original family.

Their modulus sum is `9(1+p+q)<9pq=3h`, below the sum of the three
removed moduli. Cardinality stays unchanged and the sum decreases, a
contradiction. Thus every actual h-phase contains at most two original
labels. This is the R=N=3 instance of the existing repair; the cofactor
palette has `tau(pq)=4>=3`.

If any multiple of h occurs, divisor closure includes h and all its
nonunit divisors. Its own phase contains only h by comparable
disjointness. If h is absent, its entire multiple inventory is empty.

Normalize the pure3,p,q phases to zero by one CRT translation and put
`a=p-1`, `b=q-1`. The two retained ternary roots initially have ab
possible(p,q) root pairs each. Original3p removes one p-root on its
actual ternary root; original3q similarly removes one q-root. Original
pq removes one actual(p,q) pair on both roots.

If3p and3q occupy the same ternary root, their union removes a+b-1
cells there, and pq removes at least one more cell in the other root.
If they occupy different roots, they already remove a+b cells. Hence
the number M of phases avoiding all proper original divisors of h obeys

    M<=2ab-a-b=2(p-1)(q-1)-p-q+2.

This proper-divisor bound is attained by putting3p and3q on the same
root and choosing pq's pair inside their blocked union on that root;
it removes exactly one additional cell on the other root. This is
attainment of the finite phase bound, not existence of a whole cover.

Every original multiple of h must use one of these M phases. The phase
of h itself has one occupant and every other phase at most two. Therefore

    # {d original:3pq|d} <=4pq-6p-6q+7.                 (PI1)

Either retained ternary root has at most ab-1 allowed phases: an
unaffected root still loses pq's one cell; a root containing a3p or3q
deletion loses at least as many. Its uniform label capacity is therefore

    # {d original:3pq|d, a_d mod3=r} <=2(p-1)(q-1)-2.  (PI2)

The root containing original h loses one additional label slot. The
total and root capacities are simultaneous constraints on the same
actual inventory; their separate maxima need not be attained together.

At(p,q)=(5,7), there are at most38 allowed105 phases, at most75 original
105-multiples in total, and at most46 on either retained ternary root.
The weaker use of only the pure prime exclusions would give95 in total.

### A shared four-label repair couples two different phases

The independent phase capacities above omit a further consequence of
the same PH2 joint replacement rule. Continue to assume H3=1 in ONE
globally cardinality-then-sum-minimal whole distinct odd cover. Put
`h=3pq`, `a=p-1`, `b=q-1`, with distinct primes p,q>=5.

Fix one actual ternary root r, one actual p-root u, and two distinct
actual q-roots v,w. Let C_v,C_w be the corresponding two classes
modulo h. Their union has a common repair using the four fresh
numerical labels

    9, 9p, 9q, 9pq.

Choose a lift rho of r modulo9. Assign the classes by CRT as follows:

    label9:   x=rho mod9;
    label9p:  x=rho+3 mod9, x=u modp;
    label9q:  x=rho+6 mod9, x=v modq;
    label9pq: x=rho+6 mod9, x=u modp, x=w modq.

Every point of C_v union C_w meets one of these four classes: its next
ternary digit selects one of the three displayed roots; the third
root is split according to the two original q-phases. This covers
the entire two congruence classes, including all higher lifts and all
other coordinates. It does not assume the two phases have a common
q-root or independently choose their original source.

The four labels are pairwise distinct and absent from the whole
original palette because their ternary height is2. If four original
h-multiples occupied these two phases, delete those originals and
insert this repair. Their old classes lie in the repaired union, so
all previously covered integers remain covered. Four distinct odd
quotients by h have sum at least1+3+5+7=16, whereas

    9(1+p+q+pq)=9(p+1)(q+1)<16h.

For example, `(p+1)(q+1)<=36pq/25` already gives the strict inequality.
The number of classes stays unchanged and the sum of moduli falls,
contradicting PH2. A larger removed inventory would reduce the number
of classes. Consequently

    occupants(C_v)+occupants(C_w)<=3.                (JP1)

Interchanging p,q gives the corresponding statement for two cells
in the same q-column. These are constraints on several ACTUAL phases
of the same family. They are a new explicit finite consumer of the
existing PH2 exchange principle, not a new general exchange theorem.
Sections9 and11--15 provide other joint repairs; their displayed
single common-phase capacities do not themselves give JP1.

### The double-occupied cells must form a matching

The previous single-phase repair gives at most two original labels
per h-phase. By JP1, any two cells occupied twice cannot share a
p-root or a q-root within one ternary root. Thus the double-occupied
cells form a matching in that root's bipartite p-root/q-root table.

Let M be the number of h-phases left after excluding all proper
original divisors, and K the number of double-occupied cells across
both retained ternary roots. The original h-multiple inventory obeys

    # {d original:h|d} <= M+K.

Assume p<q; then a<b. Each root's matching has size at most a.
Original3p removes an entire p-row on its actual ternary root, so
that root's matching has size at most a-1. These are simultaneous
facts about the same pair of physical tables. Hence

    K<=2a-1=2min(a,b)-1.

Combining this with the earlier proper-divisor bound
`M<=2ab-a-b` yields the stronger uniform inventory capacity

    # {d original:3pq|d}
       <=2(p-1)(q-1)-|p-q|-1.                      (JP2)

Either retained ternary root has at most ab-1 allowed cells and a
matching of size at most min(a,b). Therefore its uniform capacity is

    # {d original:3pq|d, a_d mod3=r}
       <=(p-1)(q-1)+min(p-1,q-1)-1.                (JP3)

For h=105 these give45 original multiples in total and at most27 on
either retained ternary root, strengthening75 and46 above. All bounds
remain necessary conditions; no claim is made that their separate
maxima can occur simultaneously in a whole cover.

If h is absent, divisor closure makes the counted inventory empty.
If h is present, its own phase has only the original h by comparable
disjointness. The count M+K already respects this: that phase can
contribute a single occupant but cannot contribute to K. The matching
upper bound above need not be attained through that phase, so this
observation does not justify subtracting one more from JP2 or JP3.

The deductions use arbitrary original cofactor heights and support
size. They constrain an actual numerical deletion inventory and can
be imposed jointly with the earlier root capacities; they do not
force any forbidden packet to exist, prove noncoverage, or constitute
new Lean verification. No additional numerical cap-grid is used.

### Divisor closure also restricts each actual label

Let m be an actual original divisible by3pq, with
`a=v_p(m)>=1`, `b=v_q(m)>=1`. Since H3=1, its nonunit divisors
include exactly

    a*b*product_(r|m, r notin {3,p,q})(v_r(m)+1)

distinct multiples of3pq. Every one is an original by divisor
closure, so JP2 implies the labelwise restriction

    a*b*product_(r|m, r notin {3,p,q})(v_r(m)+1)
        <=2(p-1)(q-1)-|p-q|-1.                      (JP4)

In particular, an actual label containing3,5,7 has this product at
most45. If it has k distinct nonternary prime factors, the product
is at least `2^(k-2)`, so k<=7 and `omega(m)<=8`. This concerns
only originals containing those three primes. It neither bounds
the union of support primes across the whole family nor imposes
the same8-prime bound on originals missing5 or7. This is a direct
consumer of JP2 and divisor closure, not a separate general result.

### A nonternary square

For h=3q^2 with q>=5, the same existing repair has R=3 and
`tau(q^2)=3`. Use the fresh labels9,9q,9q^2. Their sum is below
`27q^2=9h`, while three distinct odd multiples of h have sum at least9h.
The resulting strict sum descent again gives at most two labels per
actual h-phase.

Whenever this inventory is nonempty, proper originals3,q,q^2,3q are
present. After3 andq are removed, the two retained ternary roots have
`2q(q-1)` q^2 cells. Pure q^2 removes one cell on each root. Original
3q removes q cells on one root, with overlap at most one with that
root's already removed pure q^2 cell. Thus `M<=2q^2-3q-1`, and

    # {d original:3q^2|d} <=4q^2-6q-3.                (PI3)

Each root has at most `q(q-1)-1` allowed cells, giving its uniform
label bound `2q(q-1)-2`. At q5 the total/root bounds are67/38;
at q7 they are151/82.

When counting only originals with at least two distinct nonternary
primes, original3q^2 itself is outside that counted set but consumes
one of PI3's slots. Consequently that restricted inventory has at most
`4q^2-6q-4` labels, namely66 at q5 and150 at q7. Further known star
labels may consume more slots, but a global q-height does not by
itself imply the presence of every3q^e label.

### Fixed controls and consumer boundary

The [fixed phase control](../../../frontier/cover-geometry/composite-parent-contraction/h3_phase_capacity.py)
and [exact result](../../../frontier/cover-geometry/composite-parent-contraction/h3_phase_capacity.json)
check all2304 actual15/21/35 phase assignments outside their pure
divisors, the maximum38 cells and maximum23 cells on one root, and
all105 target phases of the9/45/63 repair on joint period315. They
also check all525 same-row or same-column two-phase unions for the
9/45/63/315 repair on that joint period, and exact bipartite matching
capacities on the same2304 proper-phase tables. The combined
phase-plus-matching bounds are45 in total and27 on either root.
The finite matching witness reserves an unmatched phase for the
original105 singleton; it is only an occupancy relaxation, not a
whole-cover construction. The controls also check the three literal
overfull-comb labels displayed in
[Report529](../500-549/529-an-irredundant-comb-separates-fibre-credits-from-supported-query-laws.md#actual-ternary-height-one-families-realize-the-single-class-fibre-charges).
The latter form a noncover witness, not a globally minimal cover.

The program uses only Python's standard library, reads no external
input and runs no geometry producer. Default output is stdout;
`--output PATH` explicitly writes the result. Normal and optimized
Python agree. The general p,q proofs above, rather than the finite
control, justify PI1--PI3 and JP1--JP4 at arbitrary primes and original heights.

[Report528](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#fixed-label-capacities-preserve-the-partition-reduction)
describes how these capacities can constrain its actual numerical
deletion inventory without changing the common source. Neither the
capacity formulas nor their finite control close that comparison or
bound the number of support primes.

## 18. Retained mixed originals couple both ternary roots

Continue with ONE hypothetical whole distinct odd cover globally
minimizing class count and then modulus sum, with full ternary height
H3=1. A repair using the actual retained3p or3q class strengthens the
previous total3pq-multiple inventory ceiling by one: for105 it becomes44.
The separate root ceiling27 remains valid. The phase cases below improve
the total further when the oldpq class has a retained mixed guard.
These are ordinary proofs, not new Lean verification or noncoverage.

### Actual phases and the retained-guard hypothesis

Let p,q>=5 be distinct primes, put h=3pq, and let D be the original numerical modulus set. Write

    N_h = #{d in D : h divides d}.

If N_h=0, all bounds below are immediate. Otherwise divisor closure puts 3,p,q,3p,3q,pq,h in D. One CRT translation normalizes the ACTUAL original prime classes to residue zero. Comparable-original disjointness then gives the following phases:

    A_3  : t=0;
    A_3p : t=r_p, x=u,       r_p in {1,2}, u!=0 mod p;
    A_3q : t=r_q, y=v,       r_q in {1,2}, v!=0 mod q;
    A_pq : x=x_0, y=y_0,    x_0!=0, y_0!=0.

Here t,x,y are the residues modulo 3,p,q. No retained original is reassigned in this notation. Let c=(x_0,y_0), and define

    eps_p = 1 if x_0=u, otherwise 0;
    eps_q = 1 if y_0=v, otherwise 0.

Thus eps_p=1 means the WHOLE old pq class on ternary root r_p is contained in the actual original A_3p. The analogous assertion holds for eps_q=1 and A_3q. This is an exact whole-cylinder containment, with every higher prime-power lift and every other coordinate unrestricted.

Call a nonzero ternary root guarded if one of these two containments holds there. If both nonzero roots were guarded, A_3 together with the two retained mixed originals would cover ALL of A_pq. Deleting pq would then reduce the original class count. Hence there are at most one guarded nonzero root. In particular,

    r_p != r_q  ==>  eps_p+eps_q <= 1.                  (CR0)

This restriction comes from the whole-cover minimality premise, not merely from the finite support table.

### One guarded root gives a vertical occupancy bound

Assume eps_p+eps_q>=1. By CR0 and its same-root analogue, there is exactly one guarded nonzero ternary root r_0. Let r_1 be the other nonzero root. Choose the three different lifts rho_0,rho_1,rho_2 of r_1 modulo 9. Insert the following three classes, specified by CRT:

    B_9   : t_9=rho_0;
    B_9p  : t_9=rho_1, x=x_0;
    B_9q  : t_9=rho_2, y=y_0.

The actual A_3 covers the part of the old A_pq on root 0. The retained guarding A_3p or A_3q covers the part on r_0. The three displayed new classes cover the ENTIRE part on r_1. Therefore

    A_pq subset A_3 union A_guard union B_9 union B_9p union B_9q.  (CR1)

The numerical repair labels 9,9p,9q are pairwise distinct, odd, and greater than one. They are absent from the entire original palette because H3=1; freshness does not depend on which originals are removed. Their phases preserve c on their respective cofactors. Nothing here substitutes an invented cofactor phase for an actual retained original's phase.

Now fix ANY target pair z=(x',y') modulo p,q. Let

    J(z) = {d in D : h divides d, a_d mod p=x', a_d mod q=y'},
    k(z) = |J(z)|.

Every d in J(z) is a proper multiple of pq. Thus pq itself is not in J(z), and neither guarding label 3p nor 3q nor the retained pure label 3 is in J(z). Move the single original label pq to the class z modulo pq, delete all J(z), and insert B_9,B_9p,B_9q.

This preserves the ENTIRE original covered union:

* Every old original outside {pq} union J(z) remains unchanged.
* Every deleted original A_d, d in J(z), lies in the moved pq class by its actual p/q residues, regardless of its ternary root, all original heights, and all other factors.
* Every point of the old A_pq is covered by CR1.

In particular, this argument covers points jointly owned by several removed originals and does not replace full liability by their separate private regions. It holds on all integers; equivalently one may compare on the common period lcm(Q,9pq)=3Q.

The moved numerical label pq cancels from the modulus-sum comparison. The new family has |D|-k(z)+3 classes, with globally distinct numerical labels. If k(z)>3, it has fewer classes. If k(z)=3, the three removed labels are distinct positive odd multiples of h. Their three distinct odd quotients have sum at least 1+3+5=9, so

    sum_(d in J(z)) d >= 9h,
    9+9p+9q = 9(1+p+q) < 9pq = 3h < 9h.

The middle strict inequality holds for p,q>=5 because pq-p-q-1>0. Under H3=1 the quotients are also coprime to 3, so the stronger lower bound (1+5+7)h=13h is available but unnecessary. The cardinality tie therefore strictly lowers the modulus sum. Both alternatives contradict the fixed global lexicographic minimum. Consequently

    k(z) <= 2 for every target pair z.                  (CR2)

All h-multiples avoid the original A_3, so k(z) is exactly the sum of their occupancies on the two nonzero ternary roots. Writing n_r(z) for these occupancies gives

    n_1(z)+n_2(z) <= 2.                                (CR3)

This is one common cross-root constraint, produced by one three-label repair. It does not run two independent repairs with reused numerical labels. When z=c, comparable disjointness already gives k(c)=0; the argument is consistent with that degenerate target.

### Exact proper-divisor support counts

Relabel p,q if necessary so p<q. Set

    a=p-1, b=q-1, B=2ab-a-b.

The physical support table on each nonzero ternary root has a nonzero p-rows and b nonzero q-columns. Let S_r be the cells avoiding all ACTUAL proper-divisor originals of h. An h-multiple can occupy only S_r. These proper divisors are exactly 3,p,q,3p,3q,pq, so the following counts are exact for these tables, not independently optimized phase bounds.

If r_p=r_q, the common root loses the row R={x=u} and column C={y=v}, a total of a+b-1 cells. The other root has no such deletion. The pq cell c is excluded on both roots. Therefore

    M=|S_1|+|S_2| = B-1,  if eps_p=eps_q=0;
    M=|S_1|+|S_2| = B,    if eps_p+eps_q>=1.          (CR4)

If r_p!=r_q, one root loses R and the other C, for a+b deletions before pq. The pq deletion removes 2-eps_p-eps_q further cells. By CR0 there are only two cases:

    M=B-2, if eps_p=eps_q=0;
    M=B-1, if eps_p+eps_q=1.                          (CR5)

The excluded case eps_p=eps_q=1 would make pq redundant, as already shown.

### Guarded cases: at most two extra occupants beyond M

Assume the guard premise, so CR3 holds. For each p/q cell z let

    s(z)=1_(z in S_1)+1_(z in S_2).

If s(z)=2, CR3 bounds its total occupancy by 2=s(z). If s(z)=0, occupancy is zero. If s(z)=1, its total occupancy is at most 1 plus the indicator that the unique allowed root has a double-occupied cell there. Summing these pointwise inequalities gives

    N_h <= M + K_single,

where K_single counts double-occupied cells located in only one of the two allowed tables. Doubles in the common support provide no extra total above M: their opposite-root single is simultaneously excluded by CR3.

Existing JP1 says that all double-occupied cells in each fixed root form a matching in the p-row/q-column table. It implies K_single<=2 as follows.

If r_p=r_q, the support in the root with the blocked cross R union C is contained in the other support, because c lies in that cross under the guard premise. The cells allowed in only one root are precisely (R union C) minus {c}, all in the other root. A matching in the union of one row and one column has size at most two: at most one edge can be in the row and at most one remaining edge in the column.

If r_p!=r_q, assume for notation eps_p=1, eps_q=0; the other case is symmetric. The cells allowed only on root r_p lie in C minus R. The cells allowed only on root r_q lie in R minus (C union {c}). On the first root at most one double lies in this one-column strip; on the second at most one lies in the one-row strip. Thus K_single<=2 again.

Combining with CR4–CR5 gives the stronger guarded bounds

    N_h <= B+2, if r_p=r_q and eps_p+eps_q>=1;
    N_h <= B+1, if r_p!=r_q and eps_p+eps_q=1.        (CR6)

These inequalities use the same actual tables and the same original family throughout. No separately attainable table extrema are asserted to occur together in a whole cover.

### Unguarded cases and the uniform improvement

If eps_p=eps_q=0, CR3 is not supplied by this repair. Retain exactly the existing JP1 matching argument: each root has at most a double cells, and the actual 3p row deletion limits its root to a-1. Thus the total double-cell count K<=2a-1. Combining this with the exact support counts above gives

    N_h <= B+2a-2, if r_p=r_q and eps_p=eps_q=0;
    N_h <= B+2a-3, if r_p!=r_q and eps_p=eps_q=0.     (CR7)

All four actual-phase cases are therefore bounded as follows:

| Actual 3p/3q roots | Their coverage of the old pq phase | Inventory ceiling |
| --- | --- | ---: |
| same | neither covers it | B+2a-2 |
| different | neither covers it | B+2a-3 |
| same | at least one covers it | B+2 |
| different | exactly one covers it | B+1 |

The remaining different-root/both-covered case is impossible by redundancy. Since a>=4, every displayed ceiling is at most B+2a-2. Replacing a,b by p,q symmetrically yields

    #{d in D : 3pq divides d}
      <= 2(p-1)(q-1)-|p-q|-2.                       (CR8)

This improves JP2 by one. The improvement is not a subtraction for the original h singleton. It comes from a dichotomy: absent a mixed guard, the proper-divisor support already loses another cell; present a mixed guard, moving pq becomes legal after full repair and forces the cross-root constraint CR3.

For p=5,q=7, B=38 and the four conditional ceilings are respectively 44,43,40,39. Hence the uniform 105-multiple inventory ceiling improves from 45 to 44. Existing JP3's uniform root ceiling 27 remains a valid separate constraint; no stronger unconditional root ceiling is claimed here.

Divisor closure gives the corresponding direct update of JP4. For any actual m divisible by 3pq,

    v_p(m)*v_q(m)*product_(r|m, r notin {3,p,q})(v_r(m)+1)
      <= 2(p-1)(q-1)-|p-q|-2.                       (CR9)

Thus the product is at most 44 for an original divisible by 105. This is a consumer of CR8, not a separate substantive theorem; the earlier omega(m)<=8 consequence is unchanged.

### Finite controls and the remaining global obligation

The expanded [phase control](../../../frontier/cover-geometry/composite-parent-contraction/h3_phase_capacity.py)
keeps all2304 original15/21/35 phase assignments outside their pure
prime classes. Exactly48 are excluded because their original35 is
covered by the retained3,15,21 classes. For every remaining assignment
it computes the actual two allowed tables and the relevant matching
capacities. The four case ceilings44,43,40,39 are attained by finite
occupancy relaxations; none is asserted to be an actual whole cover.
The original105 singleton can be assigned an allowed single cell in
these comparisons. Its extra reservation is not the reason for the
new subtraction by one.

The control also verifies the moved-parent repair on every relevant
original phase and every nonzero target5/7 pair, using the full joint
period315. Retained3/15/21 classes and the three fresh repair classes
cover the whole old35 class, and the moved35 class covers both ternary
roots of the target pair. Higher original coordinates remain free in
these cylinder containments, as the proof requires.

RP2 rules out repairing both nonzero ternary roots of an arbitrary old
pq phase using only fresh labels3^(2+j)e, e|pq, and retained pure3:
R=6 and t=4 give exactly the excluded equality t=R(3-1)/3. Merely adding
fresh heights cannot fix that repair. CR1 uses an additional actual
premise: retained3p or3q already covers one complete old-parent nonzero
root, leaving only the other root to repair. It therefore changes the
remaining liability and respects the existing obstruction.

No argument here forces an unrestricted hypothetical cover to violate
CR8. The new result is a stronger necessary original-inventory condition
and its exact phase-dependent refinement. It preserves arbitrary
nonternary heights and arbitrary finite support, with the explicit
whole-family H3=1 and global extremality hypotheses.

## 19. Actual star roots and a guarded square-parent repair

Fix the same ONE hypothetical distinct odd whole cover globally minimizing
class count and then modulus sum, with whole-family H3=1. For a prime
q>=5 put h=3q^2 and let N count all original multiples of h. Nonternary
heights and finite support size remain unrestricted. The total bound is

    N<=4q^2-6q-5.                                   (SQ1)

This improves PI3 by two: 67 becomes65 at q5, 151 becomes149 at q7,
and415 becomes413 at q11. The original roots of3q and3q^2 also give
stronger root-specific constraints below. These are ordinary proofs and
finite controls, not new Lean verification or a noncoverage theorem.

### The exact proper-divisor cells retain actual star roots

If N=0, SQ1 is immediate. Otherwise divisor closure supplies the actual
originals3,q,q^2,3q,h. Normalize the pure3 andq phases to zero by ONE
CRT translation. Write b modq^2 for the original pureq^2 phase,
(r,u) for the original3q phase modulo(3,q), and s for the originalh
root modulo3. Let delta=1 when b modq=u, and0 otherwise.
Comparable disjointness gives b modq!=0, u!=0 and r,s in{1,2}.
The pureq^2 original has no ternary root; s denotes the different
original3q^2 label.

After the pure3 andq exclusions, each remaining root has q(q-1)
q^2 cells. Originalq^2 removes cellb on both roots. Original3q
removes q cells on rootr, overlapping the already removed cell exactly
when delta=1. Hence the allowed h-phase count on roott is exactly

    M_t=q(q-1)-1-(q-delta)*1_(t=r).                 (SQ2)

PI3's existing three-label single-phase repair limits each h-phase
to two original occupants. The originalh phase is allowed and has
exactly one occupant by comparable disjointness. For the original
h-multiple count N_t on roott, put R_q=2q(q-1)-2,
y_t=1_(t=r), z_t=1_(t=s). Then

    N_t<=2M_t-z_t,
    N_t+2(q-delta)y_t+z_t<=R_q,
    N_t+2(q-1)y_t+z_t<=R_q.                         (SQ3)

These indicators refer to actual original star roots, not artificial
beta partition membership. Since y_1+y_2=z_1+z_2=1, summing gives

    N<=4q^2-6q-5+2delta.                            (SQ4)

Thus the unguarded delta=0 branch already proves SQ1. The safe root
ceilings from SQ3 are:

| q | R_q | Stars3q and3q^2 on the same root: that root / other | Stars on different roots:3q root /3q^2 root |
| ---: | ---: | ---: | ---: |
|5|38|29 / 38|30 / 37|
|7|82|69 / 82|70 / 81|
|11|218|197 / 218|198 / 217|

When delta=0, subtract a further two from the entry for the3q root.
These are simultaneous necessary ceilings, not separately attainable
maxima or a whole-cover construction.

### A guarded old square class can be moved after complete repair

Assume delta=1. Retained original3 covers the old A_(q^2) on root0,
and retained original3q covers it on rootr. Let t be the other nonzero
root. Choose its three different lifts rho_0,rho_1,rho_2 modulo9.
By CRT insert the three classes

    label9:    x=rho_0 mod9;
    label9q:   x=rho_1 mod9, x=b modq;
    label9q^2: x=rho_2 mod9, x=b modq^2.

Every point of the ENTIRE old q^2 class on roott is covered by its
corresponding lift. Higher q digits and all other coordinates are
free. Thus these three classes together with retained3 and3q repair
the full old parent, including joint liability rather than only its
private points.

Choose any targetc moduloq^2. Move originalq^2 to that target and
delete all originalh-multiples whose q^2 phase isc, across both
nonzero ternary roots. Each deleted class lies in the new parent.
The deleted set contains neither the moved numericalq^2 label nor
the retained3 and3q guards. Every other original stays. Consequently
the whole old covered union is contained in the new covered union.

All three inserted numerical labels are distinct odd nonunits,
globally fresh because their ternary height is two. Four or more
deletions strictly reduce class count. Three deletions tie the count
but strictly reduce modulus sum: three distinct odd multiples ofh
have total at least h(1+3+5)=9h, while

    9+9q+9q^2=9(1+q+q^2)<27q^2=9h.

The moved numericalq^2 label cancels in the sum comparison. Global
extremality is among all distinct odd covers; it does not prohibit
using a replacement of ternary height two. We conclude that

    #{d original:h|d, a_d=c modq^2}<=2, for everyc.  (SQ5)

This is ONE repair coupling both roots, with no reuse of its fresh
labels by separate repairs. At c=b the count is zero already, by
comparable disjointness with originalq^2. Occupied projections avoid
q-residue0 and cellb, leaving q(q-1)-1 choices. Therefore

    delta=1 ==> N<=2(q(q-1)-1)=R_q.                 (SQ6)

For q>=5, (4q^2-6q-5)-R_q=2q(q-2)-3>0. Combining SQ6 with the
unguarded SQ4 proves SQ1, using an exhaustive split on the actual
old phases.

### Mixed-label consumers must also pay the square stars

Let X_t count originalh-multiples with at least two distinct
nonternary support primes, and let P_t count actual originals3q^e
with e>=2 on roott. Because H3=1, N_t=X_t+P_t. The safe root cut is

    X_t+P_t+2(q-1)y_t+z_t<=R_q.                     (SQ7)

The original3q^2 is counted once in P_s; the additional z_s accounts
for that phase's missing second occupant, so it is a separate term.
Using only P_t>=z_t gives the weaker X_t+2(q-1)y_t+2z_t<=R_q.
All actual higher stars should remain in P_t. A height upper bound
alone does not force their existence; divisors of a present label do.
The corresponding totals are

    X_1+X_2+P_1+P_2<=4q^2-6q-5,
    delta=1 ==> X_1+X_2+P_1+P_2<=R_q.              (SQ8)

Any nonempty inventory contains3q^2. Thus its mixed portion alone
has at most4q^2-6q-6 labels, giving64,148,412 at q5,7,11, before
subtracting any further forced stars. SQ7 and the first line of SQ8
are independent of beta and can be imposed on the fixed numerical/root
selection set of [Report528](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#joint-pair-square-and-divisor-constraints-still-leave-a-negative-comparison).
The guarded line requires actual delta data or a justified disjunctive
relaxation; it cannot be selected from an artificial partition.

### Effect on the existing witness and finite controls

Report528's2206-label numerical witness explicitly assigns the5-stars
to root1 and every other star to root2. Its complete square inventories
including stars are38/2,7/82,10/218 at q5,7,11. The root containing
both3q and3q^2 must instead have at most29,69,197 by SQ3. Hence the
given root assignment violates all three constraints. Its totals
40,89,228 also exceed the guarded caps38,82,218: an actual family with
those totals would have delta=0 and root caps27,67,195.

This does not revise the earlier witness's conclusion for the explicitly
weaker uniform FC26 constraints. It shows why keeping the star roots
enables a stronger rejection. It does not prove positivity of the new
optimization or exclude reassigning the same numerical labels to other
roots. Unrestricted Erdős#7 remains unresolved.

The [phase checker](../../../frontier/cover-geometry/composite-parent-contraction/square_guarded_repair.py)
and [exact result](../../../frontier/cover-geometry/composite-parent-contraction/square_guarded_repair.json)
enumerate normalized proper-original phases at q5,7, count allowed
h-phases directly as integer residues, and check SQ2--SQ4 for every
allowed own-h phase. They check the whole old-parent repair and every
target projection on period9q^2, including both complete targeth-cells.
These cells contain any deleted originals regardless of their additional
factors and depths. They also check label distinctness and the strict
modulus-sum comparison.

| q | Proper phase assignments | Guarded assignments | Own-h phase choices | Full-liability target checks | Period |
| ---: | ---: | ---: | ---: | ---: | ---: |
|5|160|40|5320|1000|225|
|7|504|84|37884|4116|441|

The finite controls do not enumerate covers or replace the general
proof. With Python3.10+ and only the standard library, run

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/composite-parent-contraction/square_guarded_repair.py --output /tmp/square_guarded_repair.json
```

## 20. Actual mixed-column heights determine the available repair forest

The globally fresh palette ML1 waits until the full p-height has been
passed. Distinctness also permits earlier repairs in mixed columns which
stop below that height. Reuse section13's prefix-cut argument with the
actual depth-dependent availability, and PH2 for the resulting exchange.
This classifies a specified repair palette; it introduces no new general
exchange principle and makes no literature-priority claim.

### Actual vacancies and exact qualification

Let D be a finite divisor-closed set of odd nonunits, with one actual
class at each label. Fix an odd prime p, possibly absent from D, and an
original h=p^a*n>1 with gcd(p,n)=1. For each e|n define

    H_e=max({0} union {k>=0:p^k*e belongs to D}).       (VH1)

The formal zero handles e=1 when p is absent; it does not insert
modulus1. Divisor closure gives H_e>=a and makes the fresh labels
in that column exactly p^k*e,k>H_e. Also H_e>=H_f when e|f|n.
Consider repairs of the ENTIRE class c mod h using only

    R_h={p^k*e:e|n,k>H_e}.                            (VH2)

These are distinct odd nonunits absent from the ENTIRE original D,
even when k is below its global p-height. A nonempty restriction to
the target uses cofactor phase c mod e and a compatible p-prefix;
its target-relative mass is p^(a-k). No retained pure or mixed
guard is credited in this fresh-only palette.

At relative depth j>=1 the number of available labels is

    t_j=#{e|n:H_e<a+j}.

Their total target-relative capacity is

    C_h=sum_(j>=1)t_j/p^j
       =(1/(p-1))*sum_(e|n)p^(a-H_e).

A finite repair from VH2 exists if and only if

    sum_(e|n)p^(a-H_e)>p-1.                           (VH3)

Necessity is the usual cylinder/Kraft bound: every finite union has
mass at most its finite capacity sum, strictly below C_h because
each cofactor has infinitely many later available labels. This
excludes equality as well as C_h<1.

For sufficiency start with the target root u_0=1 and, at each
relative depth, select leaves and retain uncovered nodes by

    m_j=min(t_j,p*u_(j-1)),
    u_j=p*u_(j-1)-m_j.                                (VH4)

Assign distinct available cofactors to the m_j selected p-prefixes,
using c mod e for each. Labels at different depths remain distinct.
Before termination, u_j=p^j*(1-sum_(ell=1..j)t_ell/p^ell).
When C_h>1 some finite partial sum reaches1, so the construction
terminates and covers every integer of c mod h, including lifts
beyond the original period.

### Exact minimum count and modulus sum

Let J be the first terminating depth and N=sum_(j=1..J)m_j.
Then N is the minimum repair count within VH2. Discard empty or
redundant restrictions from any competing repair. Its remaining
prefixes form a complete prefix-free cut with at most t_j leaves
at depth j. Its internal-node counts satisfy u'_j>=u_j inductively.
The full p-ary tree identity

    number of leaves=1+(p-1)*sum_(j>=0)u'_j

therefore proves minimality. Equality fixes every u'_j=u_j and
hence every layer count m_j. This is ML3's forest argument with
the actual t_j retained.

Let sigma_m(E) sum the m smallest members of a finite set E, with
sigma_0(E)=0. Among all N-class repairs the exact minimum numerical
modulus sum is

    S=sum_(j=1..J)p^(a+j)*sigma_(m_j)({e|n:H_e<a+j}). (VH5)

Minimum count fixes the layer sizes. Each layer attains its least
sum by taking its smallest available cofactors; all their phases
can be imposed on any of the chosen target prefixes since e|n.
Different layers do not compete for numerical labels. Thus this
lower bound is attained. When all H_e equal the global height,
VH3--VH5 recover ML2--ML4. This is not optimality over other repair
palettes, retained guards or smaller joint liabilities.

### The old price shortcut is not automatic

The uniform-height bound S<h*N^2 from ML6 cannot be imported.
For p=3,h=25,a=0, take H_1=3,H_5=H_25=0, realized by the
divisor-closed palette {3,9,27,5,25}. Its first three relative
layers have available cofactors5,25; the fourth also has1. Then

    N=2+2+2+3=9,
    S=(3+9+27)*(5+25)+81*(1+5+25)=3681
       >25*9*11=2475.                                (VH6)

Even S<h*N*(N+2) fails for this fresh-only optimum. A different
guarded repair is cheaper: retained0 mod3 and the vacant labels
15,75 already give FC1128's two-label repair. This does not refute
that repair or assert optimality among all possible exchanges.

### Whole-cover phase capacity with the actual price

Now let the same D and phases belong to a hypothetical whole cover
globally minimizing class count and then modulus sum. Suppose VH3
holds and define q_h(c)=#{u in D:h|u,a_u=c mod h}.
The own phase c=a_h has q_h(c)=1 by comparable disjointness.
At any other phase, move h to c, delete a chosen collection of
these proper multiples, and repair the ENTIRE old a_h mod h
using VH4--VH5. Deleted classes lie in the moved h; all old h-points
are repaired; all other originals stay; every new label is unused.
Thus PH2 gives

    q_h(c)<=N,
    q_h(c)=N ==> sum_(u:h|u,a_u=c mod h)u<=S
                                         (c!=a_h).   (VH7)

Any selected N descendants whose modulus sum exceeds S likewise
give a forbidden exchange. N distinct proper odd multiples of h
have sum at least h*(3+5+...+(2N+1))=h*N*(N+2), so

    S<h*N*(N+2) ==> q_h(c)<=N-1 for every c.          (VH8)

Here N>=p>=3 because no repair label divides h, so the own-phase
value1 also satisfies VH8. If this price condition fails, retain
VH7 and its literal sum test; do not silently replace N by N-1.
For a chosen subinventory whose moduli are all at least L, N*L>S
also excludes N simultaneous occupants. The capacities are shared
across all original labels, not repeated per future prime or suffix.

At p=3 there is a useful uniform two-layer consumer. If at least
two labels are available at relative depth1 and at least three at
depth2, choose two first-layer leaves and the three children of
the remaining branch. This repairs the entire target with five
labels. Since every chosen cofactor is at most n, its modulus sum
is at most(2*3+3*9)h=33h<35h, so every h-phase has capacity4.
This conclusion requires neither a bound on the global ternary
height nor a compatible guard. If three first-layer labels are
already available, reuse the stronger one-layer capacity2 instead.

### A two-layer105 repair at arbitrary global ternary height

Take p=3,h=105,a=1,n=35 and assume the ACTUAL column heights

    H_1=H>=3,H_5=1,H_7=2,H_35=1.                     (VH9)

The first two relative layers have available cofactors{5,35} and
{5,7,35}. Their repair labels and optimum are

    absolute depth2:45,315;
    absolute depth3:135,189,945;
    N=5,S=1629<105*5*7=3675.

The first two labels cover two modulo9 lifts of the old h-phase;
the last three cover the modulo27 children of the remaining lift,
with the old cofactor residues where needed. No actual guard is
required. VH8 proves

    q_105(c)<=4 for EVERY c mod105.                   (VH10)

The old globally fresh/RP qualifications do not supply this repair.
At3 even their best retained-pure threshold is at least
3^(H-1)+1>=10, exceeding tau(35)=4. At5 the full-height threshold
is4, and tau(21)=4 does not strictly exceed it; larger5 heights
only worsen the test. At7, tau(15)=4<=6. At primes at least11,
tau(105)=8 is below even the first-layer threshold. The next
ternary layer itself has only two vacancies; a deeper single layer
has at most four labels for at least nine target lifts. Conditional
guard repairs remain valid where their phase premise holds, but
that premise is not automatic.

The profile forces the105-multiples themselves to have ternary
height one; the GLOBAL ternary height and the remaining family
stay unrestricted. No argument forces VH9 in every hypothetical
whole cover. Report528 after FC1296 gives an actual finite profile
and the shared future-inventory consumer. These are ordinary
symbolic proofs, without new Lean verification; unrestricted
Erdős#7 remains unresolved.

## 21. A retained ternary guard forces a two-level mixed-height alternative

Keep the same globally minimum whole cover, with original pure3
normalized to0 and complete p-height H_p. Fix an odd prime p>=5 and a>=2 with
p^a original. Suppose BOTH numerical labels

    3*p^a and9*p^(a-2) are absent from D.             (MH1)

Divisor closure also makes9*p^(a-1) and9*p^a absent. Retain0 mod3.
The entire old class c modp^a can be repaired with four fresh labels:

    3*p^a;
    9*p^(a-2),9*p^(a-1),9*p^a.                       (MH2)

Give the first label one nonzero ternary root and p-phase c modp^a.
Give the other nonzero root's three modulo9 children to the last
three labels, with p-phases inherited from c at their respective
depths. The retained pure class covers root0. Every old p^a-point
therefore belongs to a retained or repair class, with all higher
digits and outside coordinates unrestricted. At a=2 the label9
has no p-condition and is still an odd nonunit; MH1 asserts that
this pure label is absent. No modulus1 is inserted.

All four labels are globally unused and distinct. Their sum is

    S=[3+9(1+p^(-1)+p^(-2))]*p^a
      <=354*p^a/25 <24*p^a.                         (MH3)

Move the original p^a-class to a different phase and delete four
proper original p^a-multiples there. They have distinct odd
quotients at least3,5,7,9, so their modulus sum is at least24*p^a.
MH2 repairs the whole former class and the moved parent covers
every deleted class. PH2 contradicts the unchanged count and
strictly smaller sum. Comparable disjointness handles the own
phase. Hence MH1 implies

    q_(p^a)(c)<=3 for EVERY phase c.                 (MH4)

Now assume H_p>a. At a private point of the original pure p^H_p
class, the EXISTING HC1/QC2 demand supplies one actual p^a-phase
containing at least1+(H_p-a)(p-1)>=p>=5 original labels. This
contradicts MH4. Even the weaker count-only cap four would suffice.
We obtain the necessary mixed-height alternative

    H_p>a>=2 ==> 3*p^a in D OR9*p^(a-2) in D,
                                                    (MH5)
    H_p>=3 ==> 3*p^(H_p-1) in D OR9*p^(H_p-3) in D.

The second line is the strongest member at fixed H_p: its present
label forces the corresponding lower labels in MH5 by divisor
closure. This is a consumer of the existing private demand and
joint exchange, with a retained guard and two different fresh
depths; neither underlying general theorem is re-proved here.

For comparison, FC1150 with repair prime3 and HC1 only force
3*p^(H_p-2) to be original when H_p>=3. Indeed, if
t=max({0} union{j>=1:3*p^j in D}), its interface at a=t+2
has capacity one, implying H_p<=t+2. This permits t=H_p-2
with9*p^(H_p-3) absent; MH5 excludes that numerical profile in
the same minimum cover. For example, at H_p=4 it forces3*p^3
or9*p, even when the global ternary height is arbitrarily large.
This comparison is with that specified single-layer bound, not
an independence claim against every other repository constraint.

MH5 forces one of the displayed labels to be present; at H_p=3
the second alternative is the pure label9. It does not force a
usable vacancy elsewhere or a lower bound on joint phase activity.
The private suppliers share a p-prefix and their own
cofactor traces at one point, but need not all contain3 or another
specified common cofactor. Thus the unrestricted same-source
dense-inventory bound remains missing. These are ordinary symbolic
deductions with no new Lean verification.

## 22. The actual two-root forest gives a whole mixed-height constraint

Retain the same minimum whole cover, original0 mod3 and an original
h=p^a for a prime p>=5. Here a>=1. Define the actual ternary heights
of its cofactor columns by

    K_i=max({0} union{j>=0:3^j*p^i in D}), 0<=i<=a,
    t_j=#{i in{0,...,a}:K_i<j}, j>=1.                (GF1)

Thus K_0=H_3>=1 and K_0>=K_1>=...>=K_a. Only the original
pure0 mod3 is credited as a retained guard. The fresh palette is
3^j*p^i with0<=i<=a and j>K_i. It is absent from the full D.
Every such label can be assigned any ternary prefix with nonzero
first digit, with the old h-phase restricted to its p^i factor.

This is the existing prefix-forest construction with two depth-one
roots and depth-dependent availability from VH4. Its complete
available ternary mass is(1/2)sum_i3^(-K_i), and the remaining
target mass is2/3. Each finite subpalette has strictly smaller
capacity than that infinite sum. Hence the specified repair exists
if and only if

    sum_(i=0..a)3^(-K_i)>4/3.                        (GF2)

For the sufficient direction, start with

    m_1=min(t_1,2), u_1=2-m_1;
    m_j=min(t_j,3u_(j-1)), u_j=3u_(j-1)-m_j, j>=2.

Before termination, u_j=3^j[2/3-sum_(ell=1..j)t_ell/3^ell].
GF2 makes some finite partial capacity reach2/3, so this process
terminates and covers both remaining roots. Reuse VH4's assignment
of distinct cofactors at each depth. If J is the first stopping
depth, the minimum number of fresh classes is

    N=sum_(j=1..J)m_j=2+2sum_(j=1..J-1)u_j.         (GF3)

The two-root full-ternary-forest identity gives the equality; the
same componentwise internal-node comparison as VH4 proves the
minimum. In particular N is even. These are properties of this
specified palette; higher pure or mixed guards can make another
repair cheaper and are not included in this optimum.

PH2's count comparison gives q_h(c)<=N at every non-own phase;
the own phase has value one. If H_p>a, HC1 gives an actual phase
with at least1+(H_p-a)(p-1) labels. That demand is odd, while N
is even. Consequently every GF2-qualified pure interface obeys

    (H_p-a)(p-1)<=N-2.                              (GF4)

This conclusion needs no modulus-sum estimate for the fresh
forest. The price counterexample VH6 is not bypassed by asserting
that its false uniform bound holds in this guarded palette.

### A missing short staircase forces a deep original label

Let a>=2 and J>=2. Suppose all three labels

    3*p^a, 9*p^(a-1), 3^J*p^(a-2)                  (GF5)

are absent. Use one fresh class3*p^a on one nonzero first root.
At each depth j=2,...,J-1, use3^j*p^(a-1) and3^j*p^a on two
children of the remaining branch. At depth J use all three
labels3^J*p^(a-2),3^J*p^(a-1),3^J*p^a on its last children.
Every label is globally absent by GF5 and divisor closure, and
every p-phase is inherited from the old h-class. With retained
0 mod3 these1+2(J-2)+3=2J fresh classes repair the ENTIRE old
h-class. No compatible higher pure guard is required.

If H_p>a and2J<= (H_p-a)(p-1), the HC1 phase demand exceeds
this repair count, contrary to PH2. Taking a=H_p-1 and
J=(p-1)/2 therefore proves

    H_p>=3 ==> at least one of
       3*p^(H_p-1), 9*p^(H_p-2),
       3^((p-1)/2)*p^(H_p-3) belongs to D.           (GF6)

For p=5 this reduces to MH5 by divisor closure. For p>=7 it can
force deeper actual ternary columns. For example, at
p=7,H_p=3,K_0=2,K_1=1,K_2=0, GF1 gives layer counts1,2,3,
so N=6 but HC1 demands at least7. FC1150 gives H_7<=3 because
the last present3*7^j has j=1. That bound, MH5's requirement
that9 be present and HC5's H_7<=13 at H_3=2
do not exclude those numerical parameters. This is a comparison
with those specified bounds, not a claimed phase realization or
independence from every other constraint on a whole cover.

GF6 forces numerical presence and does not assert that the forced
original class meets a chosen private point. The following
consumer instead bounds actual suppliers at that same point.

## 23. A local second-row vacancy bounds the complete private supplier packet

Let s be the number of support primes of the same minimum whole
cover. Fix a support prime p>=5 and a>=2 with

    9*p^(a-2) notin D.                              (SP1)

There is no upper bound on H_3. Suppose first H_p>a and choose
ONE private point x of the original pure p^H_p class. Put
delta=H_p-a. QC1--QC2 supplies at least delta(p-1) other labels
of p-height greater than a, agreeing with x modulo p^a and at
their complete p-free cofactors. At most delta-1 are pure
p-powers: the owner p^H_p is not a supplier. Thus the number
of mixed suppliers is at least

    1+delta(p-2).                                   (SP2)

This is HC8's count on the same actual point, with general cut a.
Assign the mixed suppliers to disjoint buckets: put all labels
divisible by3 in the3-bucket; assign every remaining label to
one chosen prime q!=3,p of its cofactor. There are at most s-2
such q-buckets. Every bucket retains x's actual phase.

If the3-bucket is nonempty, its common original interface is
h=3*p^a. The three fresh labels9*p^(a-2),9*p^(a-1),9*p^a
cover its three next ternary children with the inherited p-phases.
Their sum is3h(1+1/p+1/p^2)<15h. Three distinct proper odd
h-multiples have sum at least15h, so the existing one-layer
exchange gives phase capacity two, just as FC1141. Every actual
supplier in the bucket shares x modulo h; hence its count is at
most two. Empty buckets require no original interface.

For a nonempty q-bucket take h=p^a*q, which is original because
it divides a supplier. Retain0 mod3 and use the six fresh labels

    9*p^i, 9*p^i*q, i=a-2,a-1,a.                   (SP3)

All are absent by SP1 and divisor closure. They are distinct
because p and q are different primes. Assign them to the six
modulo9 roots outside0 mod3, with phases inherited from the old
h-class at their p^i and q factors. This repairs that entire
class, at every higher digit and outside coordinate. Their sum is

    S_q/h=9(1+1/q)(1+1/p+1/p^2)
          <=9*(6/5)*(31/25)<48.

Six distinct proper odd h-multiples have sum at least48h, so PH2
gives phase capacity five; the own phase has only one original.
Each q-bucket is therefore at most five on the SAME private x.
These are simultaneous inequalities for disjoint label groups,
not a claim that their different hypothetical repairs are all
performed at once. Summing them with SP2 yields

    1+(H_p-a)(p-2)<=2+5(s-2),
    H_p<=a+floor((5s-9)/(p-2)).                     (SP4)

Since3 and p are support primes, s>=2 and5s-9>0. For H_p<=a
the second bound is automatic. Write k_p=floor((5s-9)/(p-2)).
The corresponding presence consequence is

    H_p>=k_p+3 ==> 9*p^(H_p-k_p-3) belongs to D.     (SP5)

Indeed otherwise SP4 at a=H_p-k_p-1>=2 would give H_p<=H_p-1.
When the exponent in SP5 is zero, the required original is pure9.
At a=2, SP1 means H_3=1 and SP4 recovers the already proved HC9.
For a>=3 it applies with arbitrary global H_3. In particular,
p>5s-7 gives k_p=0, so H_p>=3 forces9*p^(H_p-3), regardless
of whether the first alternative in MH5 is present.

The supplier lower bound, one-layer exchange and disjoint-bucket
accounting are reused. The additional interface SP3 makes the
same-source argument valid under a local vacancy in place of the
global H_3=1 restriction. Its conclusion limits actual mixed-column
heights; it still permits a densely occupied second row and does
not bound every complementary continuation charge. No unrestricted
noncoverage conclusion or new Lean verification follows here.

## 24. Separating the exact cofactor3 controls a vacant third row

Retain the same minimum whole cover and suppose9 belongs to D. Thus
the original3 and9 classes are both retained and disjoint. Let s be
the number of support primes, p>=5 a support prime, and select one
row of the following table:

| r | Fresh cofactors per layer | Fresh layer counts | N | B=N-1 |
|---:|---:|---|---:|---:|
|5|12|12,9|21|20|
|6|14|14,3|17|16|
|7|16|15|15|14|

Assume a>=r and the local vacancy

    27*p^(a-r) notin D.                             (TR1)

There is no upper bound on H_3. The conclusion is

    H_p<=a+floor((B*(s-2)+1)/(p-3)).                 (TR2)

This uses the existing HC8 mixed-supplier demand and RP3 forest
counts. The additional point is a partition which removes all
cofactors divisible by9 before counting the remaining pure3
cofactor separately. Numerical presence of a mixed original is
not substituted for its actual participation at the private point.

### Complete repairs for the same actual supplier groups

If H_p>a, put delta=H_p-a and take ONE private point x of the
original pure p^H_p class. As in SP2, at least1+delta(p-2) mixed
suppliers have p-height greater than a, agree with x modulo p^a,
and their complete p-free cofactor congruences contain x.
Partition these original labels:

* Put every supplier with9 dividing its cofactor in the9-bucket.
* Put suppliers with cofactor exactly3 in a separate group.
* Assign each remaining supplier to one chosen prime q!=3,p of
  its cofactor. Such a prime exists: the cofactor is greater than1,
  is not exactly3, and has3-height at most one.

For a nonempty9-bucket the original common interface is h=9*p^a.
The fresh labels27*p^(a-2),27*p^(a-1),27*p^a cover its three
next ternary children, with the old p-phase inherited. They are
globally absent by TR1 and divisor closure. Their sum divided by h
is3(1+1/p+1/p^2)<15, the minimum quotient sum for three distinct
proper odd multiples of h. PH2 therefore gives capacity two.

The group with cofactor exactly3 has at most delta labels: each
is3*p^k for one of a<k<=H_p, and original numerical moduli are
distinct. This bound needs no claim that all those classes actually
occur or that their different p-phases can be chosen independently.

For a nonempty q-bucket use its original interface h=p^a*q.
Since h is coprime to3, retained3 and9 remove respectively9 and3
disjoint roots modulo27 from the ENTIRE old h-class. Fifteen roots
remain, regardless of their actual positions. At every later
ternary level use the local fresh palette

    3^(3+j)*p^i*q^epsilon,
    j>=0, a-r<=i<=a, epsilon in{0,1}.              (TR3)

All these labels are globally absent by TR1. They are distinct
because3,p,q are different primes. Assign their p and q phases
from the old h-class wherever those factors are present. There
are2(r+1) available labels per layer. Reuse the RP3 greedy forest
on these fifteen actual roots: for r=5, use12 leaves and then9;
for r=6, use14 and then3; for r=7, use15 leaves immediately.
Every branch of the entire old h-class is thereby repaired, at
all higher digits and outside coordinates.

This local palette does not require global ternary height two.
The displayed vacancy proves freshness, while the original3 and9
supply the retained roots. No division or relocation of the whole
original family is involved in factoring p^(a-r) from its prices.
For either two-layer row, even charging the entire palette at
BOTH layers gives the strict upper bound

    S/h < (27+81)(1+1/q)/(1-1/p)<=162.

It is below N(N+2), namely483 for N=21 and323 for N=17.
For r=7 the single-layer price is less than81/2<255=15*17.
The minimum sum of N distinct proper odd h-multiples is
h*N(N+2). Hence PH2 gives capacity B=N-1 in every q-bucket.
At the original h-phase comparable disjointness already gives
capacity one. There are at most s-2 such buckets.

All counts refer to disjoint sets of suppliers at the SAME x;
the hypothetical repairs used to prove the separate capacities
need not be simultaneously executed. Adding their bounds yields

    1+delta(p-2)<=2+delta+B*(s-2),
    delta(p-3)<=B*(s-2)+1.                          (TR4)

This proves TR2 when H_p>a. Otherwise it holds automatically,
since3 and p belong to the support, s>=2, and the right-hand
additional term is nonnegative.

### Forced third-row originals and the global height-two branch

Write k_(p,r)=floor((B*(s-2)+1)/(p-3)) with B from the table.
Apply TR2 contrapositively at a=H_p-k_(p,r)-1. For each row,

    H_p>=r+k_(p,r)+1
      ==> 27*p^(H_p-k_(p,r)-r-1) belongs to D.      (TR5)

An exponent zero means the pure original27. Thus if H_3=2,
all three local vacancy tests are available at a=r and give

    H_p<=min{
       5+floor((20s-39)/(p-3)),
       6+floor((16s-31)/(p-3)),
       7+floor((14s-27)/(p-3))}.                    (TR6)

For example, with H_3=2,s=31 and p=131, TR6 gives H_131<=9.
The previous HC5 bound using H_3=2 permits H_131=10: its
first allowed cut a=10 has t=11,N=25 and gives10, and every
later allowed cut is at least11. If all3*p^i and9*p^i up to
i=10 are present, SP5, MH5 and GF6 do not exclude that height.
Indeed every proper pure cut a<10 has K_i=2 and fails GF2,
since(a+1)/9<=10/9<4/3. The new constraint excludes these
parameters by separating actual supplier groups. This comparison
is only with the named earlier bounds; it claims neither an
actual phase realization nor independence from all other constraints.

TR5 can force a third-row original even when a dense second row
has made SP1 unavailable. It does not control arbitrary dense
higher rows, and TR6 does not exclude the case where every
support-prime height is at most two. No unrestricted noncoverage
conclusion or new Lean verification follows from these bounds.

## 25. Fixed repair budgets have finite modulus palettes

The full repair obligation in PH1 or DR1 is Q-periodic, even when
it is not one congruence class. This supplies a necessary condition
missing from the sufficient fresh-height construction DR7. In fact,
every repair using at most four distinct odd nonunit moduli can be
reduced to the finite palette

    {d>1:d|Q} union {3^(H+1)*e:e|Q/3^H},
    H=v_3(Q).                                      (NF1)

Reduction here only discards repair classes. It preserves coverage
of the entire obligation, including every integer lift, and cannot
increase class count or modulus sum. Availability still excludes
every retained original numerical label. The second set consists
of unused labels, since none divides Q; an unused divisor of Q
belongs to the FIRST set and must not be conflated with it.

The finite palette is an application of the published essential-coset
bound of Lettl--Sun, Theorem1.3 (the integer case is due to Znam),
already retained in the
[literature entry](../../../../../../Library/Arith/lettlsun2008cosets.md).
The remaining argument reuses PH3--PH4's complete hull and DR7's
construction to classify three- and four-class repairs. The published
bound is not reproved. No enumeration of phases or new Lean
verification is used.

### Complete fibres force the normal form

Let P be any nonempty Q-periodic subset of the integers, Q odd.
For repair classes a_i mod m_i put R=lcm(Q,m_1,...,m_k). In a
fixed nonempty P-fibre r+Q*Z, count points modulo R. A class with
m_i|Q contains the whole fibre or none of it. For m_i not dividing Q,
write g_i=gcd(m_i,Q) and delta_i=m_i/g_i. Its proportion is

    0 if r!=a_i mod g_i, and 1/delta_i otherwise;
    delta_i is an odd integer >=3.                  (NF2)

When compatible, the induced condition on the fibre parameter is
one residue modulo delta_i. Thus at most two such classes cannot
cover a fibre not already covered by a modulus dividing Q.
If a repair has at most two moduli not dividing Q, all of those
classes can be discarded, regardless of the number of other classes.

The existing essential-coset theorem supplies a finite palette at
EVERY fixed class budget k. Discard redundant repair classes until
each remaining class has a private integer x in P. Its full fibre
x+Q*Z lies in P and is covered by the pullbacks of the compatible
repair classes. The selected class is still essential there, since
the fibre parameter0 is covered only by it. Its index is delta_i,
and the fibre cover uses at most k classes. Theorem1.3, applied to
this cover of the additive group Z with covering multiplicity1,
therefore gives

    f(delta_i)<=k-1,
    f(n)=sum_(p|n)v_p(n)*(p-1).                     (NF9)

No distinctness of the induced indices is needed by that theorem;
the original numerical repair labels remain distinct. An inside
class compatible with this private fibre would contain x, so it
cannot coexist there with an essential outside class. The bound
can use the actual number of compatible classes in place of k.

Thus the full palette is {m>1 odd:f(m/gcd(m,Q))<=k-1}, subject
to the unchanged original-label availability constraint. It is
finite: an odd prime dividing delta is at most k and its exponent
is at most floor((k-1)/(p-1)). In particular every retained modulus
divides Q times the product of these allowed prime powers. This
reduces a FIXED complete obligation and class budget to finitely
many numerical moduli and phases, even if new primes were initially
allowed. It supplies no bound on the budget needed for an arbitrary
hypothetical whole cover.

For k<=4 the only possible relative indices are1 and3. For k<=6
they are1,3,5,9. These small palettes are direct specializations of
the same published bound, not new small-cover theorems.

Now remove from P every point covered by repair classes whose moduli
divide Q, leaving P'. If P' is empty, discard all other repairs.
If not, reduce the repair to an inclusion-minimal subfamily covering
P. NF9 excludes every delta_i>3 when k<=4, so the remaining
outside classes have delta_i=3 and cover all of P'. The equation
delta_i=3 is equivalent to

    m_i=3^(H+1)*e_i, e_i|Q/3^H.                    (NF3)

Indeed its only exponent exceeding the corresponding exponent of
Q is one additional3. This proves NF1, with no change to the
retained repair phases. If k<=4 and both kinds of modulus are
indispensable, their counts must be one divisor of Q and three
moduli from NF3. All subsequent hull tests then use P', not P.

### Three classes not dividing Q are exactly the existing hull construction

For nonempty P choose w in P and define its complete hull as in PH3:

    Gamma_P=gcd(Q,{x-w:x in P modulo Q}).

The representative-independent PH4 equivalence applies to this P:
P is contained in w mod d, for d|Q, exactly when d|Gamma_P.
Suppose three distinct odd classes, all with moduli not dividing Q,
cover P. NF2 forces all three proportions to equal1/3 in EVERY
P-fibre. Consequently their moduli have form NF3, and
P is contained in a_i mod g_i for every i. Since
g_i=3^H*e_i, this gives

    3^H|Gamma_P,
    e_i|Gamma_P/3^H, with three different e_i.       (NF4)

All three classes have the same residue rho modulo3^H. Their
three residues modulo3^(H+1) must be different; otherwise they
would miss an integer lift of every P-fibre. The three classes
therefore cover the ENTIRE hull w mod Gamma_P, not merely P.

Conversely, NF4 with at least three available distinct divisors
supplies DR7 verbatim. Thus such a three-class repair exists iff
3^H|Gamma_P and tau(Gamma_P/3^H)>=3. Its minimum modulus sum is

    3^(H+1)*(e_1+e_2+e_3),                         (NF5)

where e_1<e_2<e_3 are the three smallest positive divisors of
Gamma_P/3^H. This optimum concerns repairs ALL of whose moduli
do not divide Q. It does not price repairs using missing divisors
of Q. DR7 already supplied the attaining construction and divisor
choice; NF2 proves their necessity at this class budget.

### A fourth class retains one actual union instead of just a hull

For a repair entirely outside the divisors of Q, discard every
class that is unnecessary for P. If at most four remain, NF3
applies. Each P-fibre needs at least three of these labels, all
with its own residue modulo3^H. Two different such residues in P
would require at least six labels. Thus P lies in one rho mod3^H,
and every remaining effective class has that same lower residue.

Sort them by their three next ternary digits. With three classes
the bucket sizes are(1,1,1), as above. With four indispensable
classes they are(2,1,1). Write C_i for their cofactor classes
a_i mod e_i. The necessary and sufficient condition is

    P subset C_u, P subset C_v,
    P subset C_j union C_k,                         (NF6)

where u,v are the singleton buckets and j,k share the third
digit. All four e_i divide Q/3^H and are numerically distinct.
Necessity tests every next digit above each actual P-fibre;
sufficiency covers that same integer by its digit's cofactor
bucket. These are simultaneous containments for one P, not
independent choices of its points or of original phases.

In particular, if no three-class repair with moduli not dividing Q
exists but a four-class one does, then

    Gamma_P=3^H*q for a prime q!=3.                 (NF7)

The two different singleton cofactors divide Gamma_P/3^H, so
that integer has at least two divisors. If it had three, NF4
would already supply a three-class repair. Thus it is prime;
the singleton cofactors are exactly1 and q. The double bucket
must use two other distinct divisors of Q/3^H and satisfy the
actual union in NF6. NF7 alone does not guarantee that union.

### The original prime3 private region cannot use any such outside repair

Return to the same globally minimum odd whole cover. The private
reset identity in
[Report364, section1](../../321-384/364-singleton-cofactor-ideal-and-forced-colors.md#1-actual-singleton-roots-and-a-common-cofactor-ideal)
writes P_3 as its original first3 root times ALL higher3 digits
times the same cofactor region R_3 avoiding every3-free original.
The projection theorem
[Report374, EP5](374-extremal-prime-projections-and-cardinality-descent.md#3-consequences-for-the-extremal-original-model)
gives at least p-2>=3 first-p roots of R_3 for every support
prime p>3. Hence R_3 is not contained in a single class modulo
any such p. The complete private hull consequently satisfies

    Gamma_3=3.                                     (NF8)

Its3 exponent is one because the higher3 digits are unrestricted;
no other support prime divides it because of those actual
cofactor projections. This conclusion uses the complete R_3,
not selected private witnesses at different primes.

If H>=2, NF8 fails the full3-height condition required even by
a four-class outside repair. If H=1, the quotient Gamma_3/3^H
is1, so it cannot supply two distinct singleton cofactors in
NF6, let alone the three in NF4. Thus P_3 cannot be covered by
at most four distinct odd APs whose moduli do not divide Q.
Moving the original3 class cannot be paid for in that palette
by deleting a group of at most four descendants. This does not
exclude a repair using unused divisors of Q or a larger budget.

### Eight outside classes cannot repair the complete private region

Take an irredundant repair of the complete P_3 by k<=8 distinct
odd nonunit moduli, none dividing Q. The old support contains5
and7: Report350 supplies initial-segment support, and the existing
two-prime reciprocal obstruction in
[Report375](375-deep-prime-prefix-projections-and-tree-contraction.md#9-liability-multiplicity-and-the-missing-distribution-of-blocked-fibres)
excludes a support contained in{3,5}. NF9 says that every prime
dividing a relative index is at most k. Thus every prime whose
repair exponent exceeds its old height is one of3,5,7.

Use the ONE probability nu on actual R_3 supplied by
[Report376, PC7](376-complete-prime-chain-transport-and-joint-prefix-laws.md#4-one-probability-controls-the-entire-selected-prime-chain)
for the full consecutive support chain above3. Every nonunit
cofactor AP modulo e|B, B=Q/3^H, has nu-mass at most1/3.
More precisely, for every support prime p>3 an old p-prefix of
positive depth j has mass at most3^(-j), since every chain gap
base is at least three.

Form mu_0 on the complete P_3 modulo Q by taking this same
cofactor law and independently choosing all old higher3 digits
uniformly, with the first3 root fixed at a_3. Let R be the full
LCM of Q and the repair moduli. Extend mu_0 uniformly over each
fibre modulo R above its old Q-point, giving a probability mu
on all lifts of P_3. For any repair class a mod m, NF2 gives

    mu(a mod m)=mu_0(a mod gcd(m,Q))/(m/gcd(m,Q)).

This is uniform lifting of a declared common law, not a product
of separately optimized old marginal laws. If m exceeds the old
height at p=5 or7, its old trace fixes at least one p digit and
its relative index is divisible by p. Consequently its mass is
at most1/(3p). If its only excess exponent is at3, write
m=3^(H+j)*e, j>=1,e|B. Its mass is at most3^(1-H-j), with
an additional factor1/3 when e>1. Therefore every outside label
has mass at most1/9, except possibly the single numerical label
3^(H+1), whose mass is at most1/3. Distinctness permits this
exception at most once.

Suppose a repair class exceeds the old p-height for p=5 or7.
Take its private integer x in P_3. Within x's complete Q-fibre,
fix all coordinates except the first new p digit and vary that
digit over its p values. Every class not exceeding the old
p-height misses x and keeps missing all these points. Every
class exceeding that height can cover at most one of the p
values. Thus there are at least p such classes in the repair,
irrespective of their other factors or higher exponents. The
private point need not have positive mu-mass.

If p=5, charge five of those classes at1/15 each. The at most
three other labels have total mass at most1/3+2/9, even if more
of them also exceed the old5-height. If p=7, charge seven at
1/21 each and the at most one other label at1/3. The resulting
total bounds are respectively

    5/15+1/3+2/9=8/9<1,
    7/21+1/3=2/3<1.

Both contradict coverage of the probability mu. In particular,
a modulus with relative index15 still fixes one new5 digit;
its simultaneous3 condition cannot invalidate the counting.

Every remaining repair modulus can exceed Q only at3, so it
is divisible by3^(H+1), hence by9. BC1 in section26 then gives
k>=N_3, independently of this probability argument.

The retained tail-incidence bound
[Report378, SF12](378-saturated-prime-fibres-and-mixed-tail-incidence.md#5-a-nonvanishing-tail-incidence-requirement)
already gives N_3>=9 at every height. Indeed, let M_mix count
the mixed3-bearing originals. Each has incidence weight at most
one, so M_mix>=I_3. Divisor closure supplies all H pure3 powers,
and N_3=H+M_mix. At H=1, SF12 gives I_3>=8. At H=2 it gives
I_3>=20/3, requiring at least seven mixed originals. At H>=3
it gives I_3>35/6, requiring at least six. In every case N_3>=9.
These are direct uses of the existing incidence and restriction
results, not new bounds on those source objects. Consequently

    H>=1 ==> P_3 has no outside repair of size<=8.   (NF10)

This concerns the complete private region and moduli not dividing
Q, with no restriction on the original support size or other
heights. It does not exclude larger outside repairs or claim
that every repair modulus is divisible by9 at a larger budget.

### Four repair classes cannot need an outside modulus

Now allow moduli dividing Q as well, and keep the moved parent
label3 occupied, as in DR1. NF1 leaves only one genuinely mixed
four-class shape: one inside class and three outside classes.
Write its inside modulus as d=3^v*e with e|Q/3^H. It is a
nonunit distinct from3.

If H>=2 and e>1, NF8 gives an actual z in R_3 outside the
inside class's cofactor residue. Above this same z, deleting the
inside class leaves every higher ternary digit in P'. Thus P'
cannot lie in one residue modulo3^H. If e=1, then v>=2, and
the inside class removes at most one ternary prefix of depth v
from P_3. At least two different residues modulo3^H remain.
Both cases contradict NF4 for the three outside classes.

For H=1, the inside modulus has form d=e or3e with e>1,e|B.
When d=3e its first ternary phase must agree with the original
3 class; otherwise it is ineffective and NF8 already excludes
the remaining three outside classes. Let C_e be the inside
cofactor class and set

    R'=R_3 minus C_e,
    K=gcd(B,{z-w:z in R'}), w in R'.

R' is nonempty by NF8. In fact K=1 by the existing joint
transport constraint
[Report376, PC5](376-complete-prime-chain-transport-and-joint-prefix-laws.md#2-a-genuine-joint-exclusion-including-the-cross-obstruction).
If a prime p divided K and e, the containment
R_3 subset C_e union (w mod K) would give at most two first-p
roots, violating EP5. If p divided K but not e, choose a prime
s dividing e. These are different support primes greater than3;
the same containment puts R_3 in one first-p cylinder and one
first-s cylinder. Order p,s and apply PC5: each single-root set
is smaller than the required prime-gap threshold, a contradiction.
Thus no prime divides K.

NF4 would require at least three distinct divisors of K to
complete this inside class by three outside classes. Since K=1,
that is impossible. Together with the H>=2 case and NF10,

    label3 unavailable, repair size<=4
      ==> all outside classes can be discarded.    (NF12)

The source is the same complete old P_3. This statement needs
neither a height restriction nor retention of every old3-free
label by a proposed exchange: it constrains covers of P_3 itself.
The remaining repair uses only available divisors of Q. It does
not assert that an inside repair exists, and it does not apply
to a proper subset of P_3 or to a composite parent's private set.

### A parallel pair alone supplies no new-period repair budget

The same count distinguishes a two-endpoint collision from an
available contraction. If the original inventory is the FULL set
{d>1:d|Q}, deleting two endpoint labels leaves only those two
available moduli among divisors of Q. Any repair of the resulting
nonempty joint liability with at most two classes discards all
moduli not dividing Q by NF2. Using both freed labels preserves
their total modulus sum; using fewer would contradict minimum
class count. The conclusion also applies when a fixed common
original parent is moved to the endpoints' common descendant phase
and retained under DR1's conditions: its complete private region
is the repair obligation, and its numerical label remains occupied.
It does not authorize a third replacement class within the same
two-deletion budget.

This explains a specific gap in using the same-support pairs from
the squarefree top-shadow theorem. Their existence supplies neither
additional deletion budget nor NF4/NF6's full-liability conditions.
NF1 nevertheless reduces ALL repairs of size at most four to an
explicit finite modulus palette, including missing old divisors.
Larger joint replacements and the unrestricted same-source covering
contradiction remain unresolved.

## 26. Prime-parent repairs must retain a first-level modulus collision

The branch restriction of Jenkin--Simpson, Theorem8, already applied
with all higher digits and original labels in
[Report350, EB5--EB6](../../321-384/350-extremal-paired-branch-and-source-support.md#2-exact-branch-restriction-retains-every-higher-digit),
gives a stopping condition for one entire repair route. This section
is a consumer of that existing restriction, not a new branch theorem.

Use the same globally minimum odd whole cover and an original prime
q. Let C0 be all q-free original classes, let N_q be the number of
q-bearing originals, and retain Report364's complete private product

    P_q={a_q mod q} times T_q times R_q,
    n=|C0|+N_q.

In particular C0 together with P_q covers the whole class a_q mod q.
Suppose k classes with distinct odd moduli m_i, all divisible by q^2,
cover P_q. Their moduli need not divide the old period, and no fixed
budget or bound on the old heights is assumed. Restrict C0 and these
repair classes to the old a_q branch, using EB5 or equivalently the
integer parametrization x=a_q+qz. Incompatible repair classes vanish.
The remaining numerical moduli are

    d for each d from C0;     m_i/q for each active repair.

The first group is q-free, the second q-bearing. Each group retains
distinct moduli, the two groups cannot collide, and all outputs are
odd nonunits. This is a cover of every integer z, not just a selected
finite sample or one cofactor projection. Its count is at most
|C0|+k. Global minimum cardinality therefore gives

    k>=N_q.                                        (BC1)

The bound is attained if original-label availability is ignored.
For each original q-bearing modulus q^v*e, q not dividing e, insert
the old prime phase a_q as one new first q-digit. Its lifted class
has modulus q^(v+1)*e, q-prefix a_q+q*a_(q^v*e) modulo q^(v+1),
and its unchanged original residue modulo e. These N_q moduli
are distinct and divisible by q^2. For any integer in P_q, remove
that first q-digit while keeping its full cofactor coordinates.
The resulting original configuration has cofactor in R_q, so it
is covered by a q-bearing original; its lifted class covers the
starting integer. The argument uses the enlarged q-height when
necessary, retaining every integer lift. Consequently the minimum
number in this unrestricted q^2-divisible repair palette is exactly
N_q. This construction need not avoid labels retained by an actual
exchange, so it does not assert a legal repair of the moved family.

In DR1 a move of the prime parent q deletes a phase group of
r<=N_q-1 proper descendants. A count-preserving or count-decreasing
exchange has at most r repair classes. BC1 excludes EVERY such
exchange whose repairs all have moduli divisible by q^2, regardless
of their modulus sum. It applies to the complete P_q; it does not
apply to a proper subset of that private region or a composite parent.

For q=3 the bound applies to every repair using only9-divisible
moduli, at every budget. NF10 separately excludes all outside
repairs of size at most eight, even before asking whether they can
pay a descendant deletion. The small-budget argument uses BC1;
the proof of BC1 uses only the branch restriction and minimum
cardinality, so it does not depend on NF10.

More generally, consider ANY legal repair B of P_q with k<N_q,
retaining all of C0 and the moved parent label q. Remove classes
unnecessary for P_q. EB5 again gives a cover with fewer than n
classes. Its moduli cannot all be distinct. Legality already
prevents a q-free repair modulus from repeating a retained C0
label. Within the q-bearing group, division by q is injective.
Thus EB6 leaves only the following possible collision:

    an effective repair class of modulus q*m, q not dividing m,
    together with a retained C0 class of modulus m
    or another q-free repair class of modulus m.    (BC2)

Here m>1 since q itself is unavailable. The two residual classes
have different phases: if they were the same, the q*m repair
would either miss P_q entirely (the C0 case) or be redundant on
P_q (the other-repair case). This is a necessary collision in the
same actual branch, not permission to merge the two different
phases into a single class modulo m.

Every prime-parent repair that could pay the DR1 deletion budget
must therefore use such a first-level collision. The statement
includes missing old divisors and new-period moduli, and requires
neither a class-budget bound nor a probability-law substitution.
It does not by itself eliminate the collisions. The existing
digit transport does exclude the following family of collision
patterns; the general case remains unresolved.

### A common prime can transport away all residual collisions

Let C be the full residual cover obtained in BC2, with L<n
classes, and let E be its nonempty set of repeated numerical
moduli. Every repetition is a pair, and every m in E is q-free.
Suppose a prime p>q satisfies all three conditions:

* Every m in E is divisible by p.
* Every q-bearing modulus in C is divisible by p.
* A set S of at most p-q first-p roots contains the phase of
  at least one endpoint of every repeated pair.

Select q first-p roots outside S and match them to all new
first-q roots. Reuse the full-height transport from
[Report348, retaining an already present q](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-digits-of-an-already-present-q).
For a retained p-bearing modulus its numerical action is

    p^alpha*q^beta*r -> p^(alpha-1)*q^(beta+1)*r,
    alpha>=1, beta>=0, gcd(r,p*q)=1.               (BC3)

The old high-p digits remain; the complete old q coordinate is
shifted one place upward while the new lowest q digit selects
the old p root. All p-free classes stay unchanged, since the
second condition makes them q-free as required by Report348.
The carrier uses the complete period of C, including any repair
primes or heights beyond Q. Every output point has one common
old witness in a selected whole p branch, so the outputs cover
all integers. No closing class is added: every new q root is used.

Every repeated pair loses at least one endpoint. The numerical
map BC3 is injective within the remaining p-bearing labels; its
outputs have a q factor and cannot collide with the unchanged
q-free group. A surviving old label p may become q safely, as in
[Report374, section2](374-extremal-prime-projections-and-cardinality-descent.md#2-too-small-a-projection-gives-a-strictly-smaller-cover),
because no added closing class competes for q. Thus the output
is a distinct odd nonunit whole cover with at most L-1<n classes,
a contradiction. This is a direct consumer of those transports,
not a new transport theorem or an assumption of independent phases.

### Necessary higher-level repairs for small collision families

If |E|<=p-q and p divides every m in E, the third condition is
automatic: choose one endpoint from each pair and let S contain
their actual p roots. Coincident roots only reduce |S|. Therefore
some q-bearing residual modulus must avoid p. In BC2 every such
modulus comes from an effective repair d with q^2|d;
C0 and all q-free repairs contribute no q-bearing output. Hence

    p>q, p divides every m in E, |E|<=p-q
      ==> some effective repair d has q^2|d and p does not divide d.
                                                        (BC4)

For a single repeated modulus m this holds for every prime
p|m with p>q. At q=3, every prime factor of m qualifies: the
9-divisible repairs must be nonempty, and no prime factor of m
can divide all of them. For up to two repeated moduli sharing5,
at least one9-divisible repair avoids5; for up to four sharing7,
at least one avoids7. These conditions retain all original heights.

The prime p can be absent from the original cover: two repairs
may create their repeated parent at a new prime. BC3 uses the
residual cover's actual full period and does not require an
original pure-p class. Larger collision families may still meet
the root-set condition directly, but no such condition is forced
for arbitrary E. Nor is every q-bearing residual label forced to
share a prime with E. The remaining mixed repairs and unrestricted
noncoverage are not settled by BC4.

## 27. Keeping the old q coordinate forces a joint repair cost

The full-height transport in section26 shifts the old q digits.
A different common-source map keeps them unchanged. It permits
p-free q-bearing classes, and gives a joint cost for the classes
which obstruct the transport. The finite matching step uses Hall's
theorem; the new interface to check is the unchanged q coordinate
and its actual numerical collisions, not another proof of Hall.

Use precisely BC2's residual whole cover C, with L<n classes,
after the repair B of the complete P_q has been made irredundant.
Let E be the nonempty set of repeated residual moduli and r=|E|.
Each is a q-free pair. Let p>q divide every m in E. Define

    h0 = #{d in C: p does not divide d, v_q(d)=1},
    h1 = #{d in C: p*q divides d}.

These count actual classes. Moduli divisible by q occur at most
once in C. In particular p-free classes of q-height at least two
are in neither count; they will be kept without changing their
digits or splitting their numerical labels.

### Exclude duplicate endpoints and reserve potential output labels

Choose a set S of at most r first-p roots hitting at least one
endpoint of every pair in E. Such a set exists by taking one
endpoint per pair.
Discard p-bearing classes whose first-p root lies in S for the
purpose of the proposed transport. Remaining p-bearing numerical
labels are distinct, since every repeated modulus is divisible by p.

For each p-free class of modulus q*u with q not dividing u,
check whether a q-free class of modulus p*u remains. If so, put
that class's first-p root in T. There is at most one such class
after the S deletion. Thus |T|<=h0. Let

    D=(Z/pZ) minus (S union T).

For every first-q root b, let F_b contain the first-p roots of
all actual classes in C divisible by p*q whose first-q root is b.
Consider the bipartite graph with left vertices b in Z/qZ,
right vertices a in D, and edge b--a exactly when a is not in F_b.
All these roots belong to the same residual cover, not to separate
choices of its phases.

### A full matching gives a smaller distinct odd whole cover

Suppose that graph has a matching covering every left vertex,
written as an injection sigma: Z/qZ -> D with sigma(b) notin F_b.
Write the complete period of C as p^A*q^B0*M, with A>=1,
B0>=0 and gcd(M,p*q)=1. On the output carrier

    p^(A-1)*q^max(1,B0)*M,

assign one old witness y to each new point z by

    y mod p^A = sigma(z mod q)+p*(z mod p^(A-1)),
    y mod q^B0 = z mod q^B0,
    y mod M = z mod M.                            (IC1)

At B0=0 the second condition is vacuous and the output still
has one q digit for branch selection. At every positive B0,
the entire old q coordinate is unchanged, including all high digits.

Every p-free class pulls back to the same class. Every p*q-bearing
class has empty pullback: its first-q root b would require an old
first-p root in F_b, whereas IC1 selects sigma(b) outside F_b.
A q-free p-bearing class with modulus p^alpha*u, gcd(u,p*q)=1,
has empty pullback if its first-p root xi is outside sigma's image.
Otherwise, for the unique b with sigma(b)=xi, its pullback is
one CRT class of modulus q*p^(alpha-1)*u, specified by

    z=b mod q,
    z=(a-xi)/p mod p^(alpha-1),
    z=a mod u,

where a is its old residue. The high-p residue is the divided
tail, not the original residue. Every z is covered by the pullback
of a class covering its SAME witness y, so these classes cover all
integers. No closing class is added.

The q-free p-bearing modulus map d -> q*d/p is injective.
Its images have q-height exactly one; the unchanged p-free
q-height at least two labels cannot collide with them. A possible
collision with an unchanged q*u requires alpha=1 and old modulus
p*u, and T has already excluded that class's root. Unchanged
q-free labels contain no q and also cannot collide. S deletes at
least one endpoint of every original duplicate pair. All output
moduli are consequently distinct odd nonunits, with at most
L-r<n classes. This contradicts global minimum cardinality.

### Hall failure forces an actual complete root rectangle

For EVERY admissible choice of S and the resulting T, the graph
above has no full matching. When d0=|D|>=q, Hall's theorem gives
a nonempty I subset Z/qZ, with t=|I|, such that

    W = D intersect intersection_(b in I) F_b,
    |W|>=d0-t+1.                                  (IC2)

Indeed the union of the allowed neighbours of I is
D minus W and has size less than t. Thus the actual first-root
incidence of the p*q-bearing classes contains the whole rectangle
I times W. Each such class supplies only ONE root pair, regardless
of its higher exponents. Therefore the same original residual
inventory satisfies

    h1>=t*|W|>=t*(d0-t+1)>=d0,                    (IC3)

where the last inequality follows from
t*(d0-t+1)-d0=(t-1)*(d0-t)>=0. This counts distinct classes inside
one actual rectangle, not separate witnesses that might be the
same class. The rectangles for different primes or choices of S
must not be added without a further disjointness argument.

Since d0>=p-r-h0, either r+h0>=p-q+1, or d0>=q and IC3 applies.
The resulting two alternatives are

    r+h0>=p-q+1  OR  r+h0+h1>=p.                 (IC4)

In particular r+h0+h1>=p-q+1. The larger lower bound p applies
only in the second branch, not unconditionally.

### The cost is paid by different original repair labels

In BC2, C0 contributes no q-bearing residual label. Thus h0+h1
counts exactly the effective repairs in the set

    B_eff(p)={d in B: q^2|d and
                         (p|d or v_q(d)=2)}.       (IC5)

An effective repair with q-height at least three and no p factor
is not in this set: its residual q-height is at least two and
it cannot block IC1 through the numerical collision tested by T.
This does not say such a repair has no covering effect.

Every m in E also requires its own effective first-level repair
q*m. These r labels are distinct and disjoint from B_eff(p).
For k=|B| this gives the actual repair-cost bound

    k>=r+|B_eff(p)|>=p-q+1,
    p<=k+q-1.                                     (IC6)

For example, a q=3 repair whose residual repeated moduli all
share7 needs at least five classes; if they all share11 it needs
at least nine. A single repeated modulus m obeys IC6 for EACH
prime factor p>q, since each is a possible common divisor of E.
At q=3 this covers every prime factor of m. The different-prime
inequalities are simultaneous constraints on the same inventory,
not additive budgets. In DR1 one may directly substitute the
actual descendant deletion count for the upper bound on k.

The baseline count of q-bearing residual classes already follows
from the full-fibre counting argument in Jenkin--Simpson Lemma7:
if one of those classes is essential, their reciprocal q-height
sum is at least one, so there are at least q of them. The repair's
private point in P_q remains private after BC2's restriction, so
that existing bound applies. IC2--IC6 add the common prime p,
the actual joint phases and the specific cost of preventing new
numerical collisions; the baseline is not counted as new content.

Neither a common divisor of all E nor a cheap root matching is
guaranteed in every repair. The argument preserves arbitrary old
and new prime heights, but it does not rule out general mixed
repairs or settle unrestricted Erdős #7.

## 28. Rebuild a common law after declared inside cofactor deletions

An outside repair must cover the complete remainder left by the
inside classes. Nonemptiness alone supplies no positive mass
bound under the particular law used in NF10. The existing tree
obstruction constructs another
common law under the following explicit root-capacity condition.

Keep the actual R_3 in B=Q/3^H and choose a support-prime chain

    3<p_1<...<p_t,
    lambda_1=3, lambda_i=p_(i-1) for i>1.

Let C_j be a finite collection of cofactor classes modulo
e_j>1 dividing B. For each j choose ONE chain prime dividing e_j.
In coordinate i let S_i be the set of actual first-p_i residues
of the classes assigned there, and put t_i=|S_i|. Shared roots
are counted only once. Assume

    lambda_i+t_i<=p_i for every i.                 (RC1)

These choices refer to the entire collection, not to a separately
optimized assignment for each future query. Define the actual set

    R*={x in R_3: x mod p_i notin S_i for every i}.

It is contained in R_3 minus union_j C_j, because avoiding a
class's assigned prime root suffices to avoid that class. It need
not equal the whole remaining region.

### Deleting first roots preserves the deeper prefix capacities

Put r_i=p_i-lambda_i+1 and b_i=r_i-t_i. There is one probability
nu* supported on R*, with simultaneous capacities

    c_i(0)=1, c_i(j)=1/(b_i*r_i^(j-1)) for j>=1,
    nu*(x=a mod p_i^j)<=c_i(j)
      for 0<=j<=v_(p_i)(B), every a.              (RC2)

Thus b_i=1 weakens the first-root bound to one, while every
further digit still has its original factor r_i. Deleting first
roots does not justify charging the same loss again at each depth.

Here is a direct reuse of
[Report376, sections3--4](376-complete-prime-chain-transport-and-joint-prefix-laws.md#3-weighted-prefix-potentials).
In one coordinate give all positive-depth prefixes nonnegative
prices w_u, let f be their path sum, and let

    C=sum_u w_u*r_i^(-length(u)), delta=t_i/r_i<1.

Give each root in S_i an additional price M, where M>C/(1-delta).
The existing weighted-tree lemma supplies a complete lambda_i-ary
tree with f+M*1_(first root in S_i)<=C+M*delta on every leaf.
Since C+M*delta<M, the tree avoids S_i. Let M decrease to
C/(1-delta). There are only finitely many full-height trees, so
a fixed subsequence gives a tree avoiding S_i on which

    f<=C/(1-delta).

This also covers C=0, by taking positive M decreasing to zero.
The cost C/(1-delta) is exactly sum_u w_u*c_i(length(u)).

In Report376's finite LP, use variables on actual R*, the global
mass bound one, and RC2's positive-depth prefix capacities.
Write w_0 for the dual price of the global mass bound. If a dual
cover had total cost below one, the trees just selected would give
w_0+sum_i f_i(x_i)<=w_0+sum_i C_i/(1-delta_i)<1.
Report376's product-tree obstruction supplies ONE point of R_3
in their product. The trees avoid all S_i, so that point belongs
to R*, contradicting the dual covering constraint. Pricing the
global mass constraint by one gives the opposite bound. Strong
duality therefore supplies an attained probability with all RC2
bounds. This proves nonemptiness at the same time and uses neither
independent marginals nor positive mass under an earlier law.

For a cofactor query a mod e, e|B, the one law therefore gives

    nu*(a mod e)<=
      min({c_i(v_(p_i)(e)):p_i|e} union {1}).      (RC3)

If the query fixes a selected forbidden root in some S_i its
mass is zero. Several query factors yield the minimum of their
caps, not their product. For example, along3<5<7, deleting one
specified5-root gives a5-prefix of depth j>=1 price
1/(2*3^(j-1)) and a7-prefix of depth j price3^(-j), under this
SAME residual law. This does not retain the old5-root price1/3
or assert that the old law gave the remainder positive mass.

### Test the whole outside repair on a declared surviving tail

Fix an actual old higher3-tail t which avoids all pure3-power
inside classes. Among the remaining inside classes, take exactly
those compatible with a_3 and this tail. Their cofactors are
nonunit classes C_j as above. If RC1 can be met for this whole
active collection, put the law nu* on R*, fix that old3-prefix,
and lift uniformly to the LCM of Q and EVERY repair modulus.
This single law is supported on actual P_3 points missed by all
inside classes. The outside repair alone must cover it.

For each outside class a_l mod m_l, let

    g_l=gcd(m_l,Q), delta_l=m_l/g_l,
    e_l=g_l/3^v_3(g_l),
    epsilon_l(t)=1 if its old3-prefix agrees with (a_3,t),
                 0 otherwise.

The exact same-law necessary condition is

    1<=sum_(outside l)
          epsilon_l(t)*nu*(a_l mod e_l)/delta_l.   (RC4)

Using RC3 gives a numerical upper bound on the RIGHT side;
if that bound is below one, this proposed repair is impossible.
All old cofactor coordinates remain on the same actual R*.
Only new digits are uniformly summed out. Different complete
assignments can give different laws and separate valid tests,
but their best per-class prices cannot be pooled into RC4.

Pure3-power inside classes are not removed by assigning a
cofactor prime; their actual tail exclusion is required above.
Nor does an arbitrary active inside collection have to satisfy
RC1. The construction supplies a certified residual source when
that condition holds, without giving a uniform payment bound for
every mixed repair or resolving the unrestricted problem.

### Full prefixes can fit even when their first-root counts do not

For each cofactor class C_j, one may instead assign its complete
prefix at a chosen dividing chain prime. In coordinate i, remove
duplicates and prefixes contained in another selected prefix;
write U_i for the resulting antichain and D_i for its union. Put

    delta_i=sum_(u in U_i) r_i^(-length(u)).

If delta_i<1 for every i, the same penalty argument applies:
put price M on every u in U_i. Since these prefixes are disjoint,
the added path score is exactly M on D_i and zero elsewhere.
Its old capacity cost is M*delta_i. Reuse the same finite LP on
R_D={x in R_3:x_i notin D_i for every i}. It gives one law with

    nu_D(x=a mod p_i^j)
      <=min(1,r_i^(-j)/(1-delta_i)), j>=1.        (RC5)

Every assigned cofactor class misses R_D. With this whole
assignment fixed, RC4 remains valid with nu_D in place of nu*.
The sufficient condition is delta_i<1 separately on each axis,
not sum_i delta_i<1. Only roots gives delta_i=t_i/r_i and
recovers RC2 exactly. This is an interface use of the existing
weighted-tree selection and common-source duality, not a new
LP-duality theorem.

For example, three depth-two5 prefixes at distinct first roots
have delta_5=3/9=1/3 along3<5<7. Their three first roots exceed
RC1's two-root allowance, but their complete prefixes satisfy
RC5. The resulting5-prefix price is min(1,(3/2)*3^(-j)); all
undeleted chain coordinates retain their original caps. This
describes a sufficient deletion certificate for those actual
prefixes, not an assertion that every inside collection has one.

## 29. Six repair classes cannot need an outside modulus

Keep the actual complete P_3 in the same lexicographically minimum
whole cover, with Q=3^H B, H>=1. Allow any repair of P_3 by at most
six distinct odd nonunit moduli, with numerical label3 unavailable.
No retention of all old3-free classes is assumed. Then

    all repair classes whose moduli do not divide Q
      can be discarded.                           (NF13)

This strengthens NF12 without a height or support-size restriction.
It does not claim that a repair by the remaining available divisors
exists. The proof reuses the essential-coset bound, the actual
prime-chain source and the distinct original repair labels.

### Count indispensable outside classes on their own private fibres

Take an inclusion-minimal subfamily of the proposed repair and
write k_out,k_in for its outside and inside counts. If k_out>0,
an outside class has a private integer x in P_3. No inside class
meets x+Q*Z: an inside class meeting that fibre contains all of
it, including x. The compatible OUTSIDE classes therefore cover
this fibre and the chosen class remains essential. NF9's published
bound applies with k_out, giving

    f(m/gcd(m,Q))<=k_out-1.                        (NF14)

NF2 excludes k_out<=2. If k_out=6 then k_in=0 and NF10 excludes
the repair. Only k_out=3,4,5 remain. For k_out=3 or4, every outside
modulus has form3^(H+1)*e with e|B; its relative index is3.
For k_out=5 the possible indices are3,5,9. The old support contains5,
as in NF10.

### Four or five outside classes fail one common residual budget

Here k_in<=2. First select one old3-tail avoiding every pure3-power
inside class. Such a tail exists: each such modulus is at least9,
and two distinct pure powers occupy at most1/3+1/9 of the old
tail space. At H=1 there are no such inside classes.

Collect all mixed inside classes active at this one tail. Assign
each to one of its cofactor prime roots, in the full consecutive
support chain above3. Every r_i>=3, and at most two roots are
assigned altogether, so RC1 holds. Use RC2's ONE law on R*, and
lift uniformly above the selected complete old Q source to the
LCM of every repair modulus. All inside classes have mass zero.

Suppose k_out=4. If every b_i>=2, each nonunit cofactor query
has mass at most1/2. There is at most one outside label with
e=1, so total outside mass is at most

    1/3+3/6=5/6<1.

Otherwise precisely one coordinate p has b_p=1; it has r_p=3
and received two distinct roots. All other coordinates retain
b_i=r_i>=3. The ONLY nonunit numerical cofactor which can have
mass above1/3 is e=p: a p^2 prefix already has mass at most1/3,
and a factor at another prime gives the same bound. Distinctness
permits e=1 and e=p at most once each among the outside labels.
Their total mass is therefore at most

    1/3+1/3+2/9=8/9<1.

Now suppose k_out=5, so k_in<=1. All b_i>=2, and at most one
coordinate can have b_i=2. If a modulus exceeds the old5-height,
use its private Q-fibre and vary just the first new5 digit, keeping
all other digits fixed. Every class not exceeding the old5-height
misses that whole set. Every remaining class covers at most one
of its five values. Thus all five outside classes exceed that
height. Under the SAME lifted law, each fixes an old5 prefix of
mass at most1/2 and an independent new5 digit, so their total
mass is at most5/10=1/2<1.

Otherwise all excess is at3, and the outside labels have form
3^(H+j)*e, j=1 or2. Only j=1,e=1 can have mass above1/6,
and it has mass at most1/3. Apart from this, the only label which
can have mass above1/9 is j=1,e=p at the possible coordinate
with b_p=2; its mass is at most1/6. All other labels have a second
new3 digit, a deeper p prefix, or a different cofactor prime.
Each then has mass at most1/9. Distinctness yields the bound

    1/3+1/6+3/9=5/6<1.

Absent exceptional labels only decrease these bounds. This excludes
both cases without optimizing a separate law for each class.

### Three outside classes would require too narrow a remainder

Let P' be P_3 minus all inside classes; it is nonempty by
irredundancy. NF4 applies to its three outside classes: P' must
lie in ONE residue modulo3^H, and its complete cofactor hull K
must have at least three distinct divisors. These are consequences
of the same three actual phases covering every integer lift.

If H>=3, choose a point of P' and fix its complete cofactor in B.
Along that fixed cofactor the inside classes cover every old3-tail
except the one containing the chosen point. Add that single tail
as a class of index3^(H-1) on the ternary-tail parameter. This
class is essential in the resulting whole cover of the parameter.
The Lettl--Sun bound already used in NF9 gives

    k_in>=f(3^(H-1))=2*(H-1)>=4,

contradicting k_in<=3. The inside pullbacks may repeat numerical
indices; the cited theorem permits this.

If H=2, fix the same witness cofactor. An inside class of3-height
zero or one misses the witness and hence every tail over this
cofactor. Each of the other two old tails consequently needs an
inside class of3-height two. Those two classes are distinct and
belong to different tails. With at most three inside classes,
each of these two tails has at most two active inside classes in
total. Numerical label9 can occur only once. At the other tail
every active class has a nonunit cofactor, of mass at most1/3
under the original PC7 law. Their total mass at most2/3 cannot
cover all of R_3, contradicting the asserted single-tail remainder.

### At height one, three inside classes leave a hull of at most two divisors

Let H=1 and write the inside cofactor classes as C_j modulo e_j>1,
e_j|B. Each numerical e can occur at most twice: its only possible
original inside labels are e and3e. Put R'=R_3 minus union_j C_j.
It is nonempty, and choose w in R'. Its complete hull is

    K=gcd(B,{x-w:x in R'}).

Thus R_3 is contained in union_j C_j together with w mod K.
We show that K is either1 or a prime.

First suppose p^2|K. Enlarge the last class to w mod p^2. If
the at most three inside cofactors are not all powers of one
prime, assign each to a dividing prime so no prime receives more
than two of them. Such an assignment exists for at most three
items: the only capacity-two Hall obstruction is three singleton
supports at the same prime. Use the full consecutive prime chain
and each assigned class's actual prefix. Every coordinate has
total PC6 capacity at most2/3 before the target, and adding its
p^2 prefix raises the p-coordinate cost by at most1/9, still below
one. If all inside cofactors are powers of one prime, numerical
distinctness instead gives total capacity at most

    2/3+1/9=7/9.

Adding the target p^2 prefix again leaves every coordinate below
one. PC6 therefore supplies in each coordinate a complete legal
tree avoiding its assigned prefix union. Their product meets R_3
by PC1--PC4, contradicting the displayed containment.

Next suppose distinct primes p,s divide K. Enlarge the target to
w mod p*s and allow its assigned prefix to be either its p root
or its s root. Assign the at most four items, including that
target, to dividing primes with capacity two each. Hall's only
possible failure is that the three inside items all have singleton
support at one prime t: a set with two available primes has total
capacity four, and the target itself has two choices. Outside
this exception every coordinate cost is at most2/3. In the
exception, keep the inside items at t with cost at most7/9, and
assign the target to one of p,s different from t, at cost at most
1/3. In both cases the same PC6 product-tree contradiction applies.
The finite assignment step is the existing capacity-Hall criterion
used in
[Report386, section3](386-pair-root-conflicts-and-original-survivor-capacity.md#3-capacitated-hall-is-a-simpler-sufficient-condition),
with every capacity set to two, not a new matching theorem.

Consequently K has at most two divisors. This contradicts NF4 and
completes all k_out cases, proving NF13. Every inclusion-minimal
subrepair therefore consists solely of inside classes, so the
inside subfamily of the original repair already covers P_3.

The six-class conclusion concerns a complete periodic obligation,
not an arbitrary proper part of P_3. Repairs with more classes,
the availability and effectiveness of inside repairs, and the
general collision families of BC2 remain to be controlled. No
unrestricted noncoverage conclusion or Lean certification follows
from this finite-budget theorem.

## 30. The complete prime3 private region needs at least five repair classes

In the same minimum whole-cover model, no family of at most four
classes with distinct odd nonunit moduli, with modulus3 unavailable,
covers the complete P_3. This allows arbitrary proposed moduli and
residues, requires no retention of C0, and imposes no height bound.
It excludes inside as well as outside repairs at this budget.

### Four shallow classes leave an actual cofactor witness

First consider at most four cofactor APs with moduli e>1 dividing B,
where each numerical e appears at most twice. They cannot cover R_3.
Apply the capacity-two assignment from section29, using each class's
actual prefix at an assigned dividing prime. If Hall holds, every
coordinate has old PC6 capacity cost at most2/3, so PC1--PC4 give
an actual point of R_3 missing all the classes.

If Hall fails, at least three of the at most four items are pure
p-powers for one prime p. A subset involving two primes has
capacity at least four, so there is no other obstruction. If all
items are p-powers, numerical multiplicity at most two bounds their
total PC6 cost by

    2/3+2/9=8/9<1.

If exactly three are p-powers, their total cost is at most7/9.
Assign the possible fourth item to a prime different from p, at
cost at most1/3. Again every coordinate cost is below one, and
the same product-tree obstruction supplies an actual point missing
all classes. This is one common cofactor witness, not a tuple of
unrelated marginal witnesses.

### Deep ternary classes cannot pay the remaining complete tail

Suppose a repair of P_3 with k<=4 classes exists. By NF13 its
inside subfamily already covers P_3; discard the outside classes.
Partition the remaining numerical moduli by their ternary height:

    low: v_3(m)<=1,    high: v_3(m)>=2.

Since1 and3 are unavailable, every low class has nonunit cofactor
e. A fixed e has at most two low labels, e and3e. The preceding
argument gives an actual z in R_3 missing every low cofactor class.
The complete P_3 contains every old higher3-tail above this SAME z.
Only high classes can cover it, and each covers at most1/3 of that
tail space. There must be at least three high classes. At H=1
there are no high inside labels, which already gives a contradiction.
At every greater height, k<=4 now leaves at most one low class.

Use the original full-chain PC7 law on R_3, independently of uniform
old higher3 digits, with the original first3 root fixed. This gives
ONE probability on complete P_3. Each low class has mass at most1/3.
Among high classes, only numerical label9 can have mass above1/9:
it has mass at most1/3; a higher pure power has an additional
ternary factor, while any mixed high class has cofactor mass at
most1/3 as well as a ternary-tail factor at most1/3. Distinctness
allows label9 at most once. Thus the total repair mass is at most

    1/3+1/3+2/9=8/9<1,                            (NF15)

contradicting coverage. Fewer than four classes or no low class
only reduce this upper bound.

Accordingly every repair of complete P_3 avoiding label3 needs
at least five classes. In DR1 a move deleting at most four
descendants cannot be paid by any distinct odd repair palette,
including unused old divisors and arbitrary new-period moduli.
This constrains that complete repair route; it does not exclude
larger repairs, simultaneous moves with another liability set,
or an unrestricted odd cover. No Lean verification is asserted.

## 31. Six-class repairs reduce to their low inside subfamily

Keep the same minimum whole-cover model, Q=3^H*B and complete
P_3. Suppose at most six classes with pairwise distinct numerical
odd moduli greater than one, none equal to3, cover P_3. Then their
subfamily with moduli dividing Q and ternary height at most one
already covers P_3. No retention of C0 is assumed here.       (NF16)

NF13 first removes every outside class. Take an inclusion-minimal
subrepair from the inside classes, and call its classes low or
high according as v_3(m)<=1 or v_3(m)>=2. Write their counts as
ell and h. If h>0, a private point of a high class has cofactor
z in R_3 missed by every low class. All old higher3 tails above
this SAME z belong to P_3. Each high class covers at most one
third of that complete tail, so h>=3 and ell<=3. At H=1 there
are no high inside classes in the first place.

For ell<=3 the following construction gives one law on the
actual cofactor remainder avoiding all low classes. Independently
adjoin uniform old higher3 digits, keeping first root a_3 fixed.
Low classes have mass zero under this law. We show that the
entire high subfamily has mass strictly below one:

| Low count ell | Maximum high count h | High mass upper bound |
| --- | ---: | ---: |
| 0 | 6 | 8/9 |
| 1 | 5 | 5/6 |
| 2 | 4 | 8/9 |
| 3 | 3 | 5/6 |

With no low class, use PC7. Numerical label9 has mass at most
1/3, and every other high label has mass at most1/9, giving
1/3+5/9=8/9.

With one low class, assign its cofactor to any dividing prime
root and use RC2. Every b_i>=2 and at most one b_p equals2.
Only9 and, at that exceptional coordinate,9p can exceed1/9;
their masses are at most1/3 and1/6. The total for h<=5 is at
most1/3+1/6+3/9=5/6.

With two low classes, assign their cofactors to dividing roots.
If every b_i>=2, each high label other than9 has mass at most
1/6, so the total is at most1/3+3/6=5/6. Otherwise precisely
one coordinate p has b_p=1 and r_p=3; both deleted roots lie
there. RC2 still gives a p^2 prefix mass at most1/3 and every
other prime-root mass at most1/3. Thus only9 and9p can exceed
1/9, each at most1/3, giving1/3+1/3+2/9=8/9.

With three low classes, assign their cofactors to primes with
capacity two each. The only Hall obstruction is that all three
cofactors are pure powers of one prime p. Outside that exception,
RC2 applies. At most one coordinate p can have b_p=1; every
other coordinate has b_i>=2. Its depth-two bound is at most1/3.
Consequently only9 and9p can exceed1/6, each at most1/3, and
three high classes have mass at most5/6. If there is no b_p=1,
the bound only improves.

In the pure-power exception a numerical cofactor may occur twice,
from low labels e and3e; this argument does not assume C0 is
retained. Assign the three complete prefixes at p. Their old
capacity, before any antichain simplification, is at most

    delta_p<=2/3+1/9=7/9.

RC5 supplies one actual residual law with first-p prefix cap at
most one and depth-two cap at most(1/9)/(1-7/9)=1/2. Every other
coordinate retains its original cap at most1/3. Under the product
with uniform old3 tails, only9 and9p can exceed1/6. A9p^2 class
has mass at most1/6, a deeper pure3 label at most1/9, and a high
class with another cofactor prime at most1/9. The same5/6 bound
therefore applies.

All four cases contradict a high-containing minimal subrepair.
Such a minimal subrepair consists only of low inside classes;
these belong to the asserted original subfamily, proving NF16.
The common-law construction does not require the private witness
to have positive mass under an earlier probability. Nor does it
assert that a low subrepair actually exists at this budget.

## 32. Retaining the original q-free classes rules out six-class repairs

The additional retained-label condition excludes the low subfamily
left by NF16. The finite assignment below reuses the capacitated
Hall criterion of
[Report386, section3](386-pair-root-conflicts-and-original-survivor-capacity.md#3-capacitated-hall-is-a-simpler-sufficient-condition)
and the prefix costs of PC6. It adds an explicit six-item consumer,
not a new Hall or tree-selection theorem.

### Six items admit strict per-coordinate prefix capacities

Let a labelled list contain at most six integers m>1 coprime to6.
Assume each numerical pure prime power occurs at most once and
every other numerical value occurs at most twice. One can assign
each item to one of its dividing primes such that

    sum_(m assigned to p) 3^(-v_p(m))<1
       for every assigned prime p.                         (NF17)

First try the capacity-two Hall assignment. If it exists, each
coordinate costs at most2/3. Otherwise consider the following
two exhaustive obstructions and use complete exponents.

Suppose at least three items are pure p-powers for some p. Assign
all pure p-powers to p. Their exponents are distinct, so their
finite total cost is less than sum_(a>=1)3^(-a)=1/2. At most
three items remain, each with a prime divisor other than p. Try
capacity two on those other primes. It fails only if precisely
three remaining items have the same singleton support {q} after
deleting p. If all three are pure q-powers, assign them to q at
total cost less than1/2. Otherwise move one mixed p^a*q^b item
to p, increasing its cost by at most1/3. The p cost is then
less than5/6, and the other two items cost at most2/3 at q.

Now suppose every prime has at most two pure-power items. A Hall
failure must contain at least five items supported within a pair
{p,q}: a singleton cannot fail, and three available primes already
have capacity six. Take all items supported within this pair.
There are five or six; any remaining item has a prime outside
the pair and can be assigned there at cost at most1/3.

At either of p,q, zero, one or two pure-power items cost at most
0,3/9 or4/9, respectively. Let S<=2 count the shallow mixed
items with numerical value pq. Each other mixed item has depth
at least two at one axis; assign it to such an axis, at cost
at most1/9. Before assigning the S shallow items, each axis has
cost at most8/9: with zero, one or two pure items its bound is
respectively6/9, (3+5)/9 or(4+4)/9.

If S=0, the assignment is complete. If S=1, let P be the total
number of pure items on the pair. For P=0,1,2,3,4 their combined
cost is at most(0,3,6,7,8)/9. There are at most5-P deep mixed
items, so the combined base cost of both axes is at most one.
One axis has cost at most1/2; assign pq to it, obtaining at most
5/6 there. The other axis remains at most8/9.

If S=2, there are at most4-P deep mixed items and the combined
base cost is at most8/9. When both axes have cost below2/3,
assign one pq to each. Otherwise one axis has cost at least2/3,
so the other has cost at most2/9. Assign both pq items to the
latter, bringing its cost to at most8/9. Every axis remains
strictly below one. This proves NF17, with indivisible items;
no fractional assignment or independent phase choice was used.

### A legal complete repair needs at least seven classes

Require the repair to retain every original class in C0, to use
pairwise distinct odd nonunit moduli, and to avoid label3 and
all numerical labels occupied by C0. Then

    number of repair classes >=7.                          (NF18)

Indeed, if there were at most six, NF16 would leave a low inside
subfamily covering P_3. Its nonunit cofactors e divide B, and each
numerical e occurs at most twice, from labels e and3e. For a pure
cofactor e=p^a, divisor closure of the lexicographically minimum
original cover makes p^a an original C0 label. That label is
unavailable to the repair, so only3p^a can occur: pure cofactor
values occur at most once.

Apply NF17 to this actual cofactor list. Use the full increasing
chain of old support primes above3, whose PC6 bases r_i are at
least3. In each coordinate, assign the actual full prefix of each
assigned class. Its total PC6 capacity is at most the corresponding
NF17 sum, hence strictly below one. PC6 gives a complete legal
tree avoiding all those prefixes on each axis. PC1--PC4 force
their product to meet actual R_3, giving one cofactor missed by
every low class. This contradicts coverage of complete P_3.

Retention of C0 is essential to this proof: without it a pure
cofactor may occur twice, and NF17's hypothesis is not established.
NF15 and NF16 have the broader unretained-label scope stated there.

### Every non-parent ternary root needs seven original classes

NF18 implies a necessary condition on the original minimum whole
cover itself, with no chosen DR1 deletion. For each first3 root
rho different from a_3, let D_rho be the original3-bearing
classes whose first3 root is rho. The whole product

    {rho} times T_3 times R_3

must be covered by D_rho: C0 misses R_3, and classes at another
first3 root miss this product. Choose one CRT translation c with

    c=a_3-rho mod3^H,    c=0 modB.

Translate every class in D_rho by this SAME c. A complete prefix
rho+3t becomes a_3+3t, so all higher3 digits and all cofactor
residues are preserved. Its numerical modulus is unchanged.
The translated family covers complete P_3, has distinct numerical
labels divisible by3, and has no label3. It therefore conflicts
with neither retained C0 nor the unavailable parent label3.
NF18 gives |D_rho|>=7 for each of the two non-parent roots.
Their original inventories are disjoint; adding the original
prime3 label gives

    N_3>=1+7+7=15.                                         (NF19)

This is a whole-cover inventory condition with unrestricted old
heights. NF13's proof through NF10 retains its independent earlier
Report378 lower bound N_3>=9; NF19 is downstream and must not
be substituted into that bootstrap proof. The lower bound15 does
not exclude larger inventories or settle unrestricted #7. These
are ordinary symbolic deductions without new Lean verification.

## 33. Distributed prefixes remove q-free residual collision families

The full-coordinate map of Report376 also applies to a BC2 residual
whole cover C having L<n classes, when every modulus in C is
q-free. This is an explicit restriction: effective repairs divisible
by q^2 would leave q-bearing residual classes and are excluded from
this consumer. Let E be the set of repeated numerical moduli in C.
Each repetition is a pair of actual classes, as established in BC2.

Choose a chain q<p_1<...<p_t such that every m in E has a selected
prime divisor. The selected primes may include new repair primes.
Use their complete heights H_i in the actual period of C, put
lambda_1=q, lambda_i=p_(i-1), and r_i=p_i-lambda_i+1. For each
m in E choose one actual endpoint of its pair and assign that
endpoint's full p_i prefix to one selected p_i dividing m.
Within each coordinate remove duplicate or contained prefixes,
obtaining an antichain U_i. If

    delta_i=sum_(u in U_i) r_i^(-length(u))<1
       for every selected coordinate i,                    (BC5)

the residual cover contradicts minimum original cardinality.

PC6 selects a complete lambda_i-ary full-height tree avoiding U_i
for every i. Apply PC1's common CRT map using these trees and all
unselected cofactor coordinates. Since C covers every integer,
each new point's one old witness is covered by a class of C.
PC2 pulls each such event back to at most one AP, with numerical map

    m=r product_i p_i^alpha_i
      -> r product_i lambda_i^alpha_i.

All C moduli are q-free, so the unselected cofactor r contains
neither q nor a selected prime. The map is injective on numerical
labels; whole coordinate exponents move, with no old tail left
to collide at a new coordinate. Every repeated pair loses at
least its chosen endpoint because the corresponding prefix was
excluded. Thus the pullbacks have distinct odd nonunit moduli,
cover every new point through its SAME old witness, and number
at most L-|E|<n. No closing class is added. This is the existing
full-height transport with a distributed deletion certificate;
no common prime divisor of E is required.

At q=3, |E|<=6 always supplies such a certificate. The numerical
bases in E are distinct odd integers coprime to3. They therefore
satisfy NF17, including uniqueness of every pure-power value.
Assign each base as in NF17 and choose either actual endpoint
of each pair. Taking all primes occurring in E as the increasing
chain gives r_i>=3, hence every coordinate capacity is below one.
The actual phases and antichain simplification can only decrease
that bound. Consequently a BC2 residual that is entirely3-free
must have at least seven repeated numerical bases, irrespective
of the total number of repair classes.

For general q, q-freeness alone does not ensure that a repeated
base has a prime divisor above q; the stated chain and assignment
remain hypotheses. For q=3 the remaining arbitrary-budget cases
include mixed3-bearing residuals and collision families with no
strict prefix assignment. The transported cover supplies a
cardinality contradiction, not a replacement repair retaining the
old labels. Neither this consumer nor NF19 is an unrestricted
noncoverage proof.

## 34. Seven distinct collision bases fit, and numerical capacity has a sharp boundary

The repeated-base set E in BC5 has distinct numerical values,
although the residual cover has two actual classes at each base.
That extra distinction improves its automatic assignment threshold.
For any at most seven pairwise distinct integers m>1 coprime to6,
take ALL their prime factors as the increasing chain
3<p_1<...<p_t. There is an assignment to dividing primes with

    sum_(m assigned to p_i) r_i^(-v_(p_i)(m))<1,
    r_1=p_1-2, r_i=p_i-p_(i-1)+1 for i>1.        (BC6)

This is a numerical sufficient certificate, before any actual
endpoint prefixes are merged. NF17 still has only its six-item
guarantee when non-pure numerical values may occur twice.

### Resolve the small Hall obstructions at their full depths

Try capacity two at each prime. A successful assignment has cost
at most2/3 at every axis. In a list of at most seven items, Hall
can fail only through at least three pure powers of one prime,
at least five items supported within two primes, or all seven
items supported within three primes.

First suppose at least three items are pure p-powers. Assign all
of them to p, at total cost less than1/2 using the conservative
base3. At most four items remain. Try capacity two for these on
primes other than p. Failure supplies a prime q for which three
or four remaining items have singleton support {q} after removing
p; let T contain ALL such remaining items. Each is p^a*q^b,
a>=0,b>=1. Any remaining item outside T has a prime outside
{p,q}, and there is at most one such item.

If at most two T items have b=1, put all of T at q, with cost
at most2/3+2/9=8/9. Otherwise move all T items with b=1,a>=2
to p. Their a values are distinct, so their added cost is less
than sum_(a>=2)3^(-a)=1/6; the total p cost is below2/3.
The q axis now has at most two b=1 items, with a=0 or1, and
at most one b>=2 item, costing at most7/9. This deals with the
first obstruction at conservative base3 on all axes.

Next suppose every prime has at most two pure-power items but
at least five items are supported within a pair {p,q}. Collect
all items supported there; at most two outside items remain and
can be assigned outside the pair, at cost at most2/3 on any axis.
At p or q the pure cost is at most0,3/9 or4/9. There is at most
ONE shallow mixed item pq. Every other mixed item has depth at
least two at one axis; initially assign it to such an axis at
cost at most1/9.

If pq is present, each axis's base cost is at most8/9. With P
pure items across the pair, P=0,1,2,3,4, their combined cost is
at most(0,3,6,7,8)/9, and there are at most6-P deep items.
Thus the combined base cost is at most10/9. The lighter axis
costs at most5/9, so adding pq there leaves it at most8/9.

If pq is absent, each axis costs at most one: the bounds for
zero, one and two pure items are7/9, (3+6)/9 and(4+5)/9.
Equality on an axis requires exactly one or two pure items there
and all six or five remaining mixed items assigned to it; the
other axis then has cost zero. Move any one mixed item to the
other axis. Its cost there is at most1/3, and the first axis's
cost becomes strictly below one. Both costs are now strict.

It remains that no prime has three pure items and no pair
contains five items. If capacity-two Hall still fails, all seven
items have support in exactly three primes. These are the entire
prime support of the list. Instead use integer capacities

    p_1-3, p_2-p_1, p_3-p_2.

Each is at least two, and their sum p_3-3 is at least eight,
since p_3>=11. Singleton-supported lists have size at most two,
pair-supported lists at most four, and the entire list has seven
items. Hall therefore holds with these capacities. Each assigned
item costs at most1/r_i, and no axis receives more than r_i-1
items. This proves BC6. All previous branches work with base3,
so including every prime in the list does not spoil them.

Choosing either endpoint of each repeated pair and applying BC6
in BC5 gives the arbitrary-budget consequence

    C entirely3-free in BC2 ==> |E|>=8.             (BC7)

The certificate uses the selected coordinates' complete heights
in C even if an exponent in E is smaller. New repair primes are
permitted; no original pure class at those primes is assumed.

### Exact boundaries of the numerical certificate

The pure-unique, mixed-at-most-two hypothesis in NF17 cannot
guarantee seven items. Consider

    {5,25,7,35,35,175,175}.

The pure items force both5 and7 into the chain, giving bases3
and3. The5 axis already pays4/9 and the7 axis1/3. Every mixed
item costs1/3 at7, so at most one of them can be assigned there.
Assigning a35 there is the best possible saving at5, but still
leaves5 cost at least4/9+1/3+2/9=1. Assigning fewer items to7,
or assigning a175 instead, only raises the5 cost. No permitted
chain changes these two bases.

Even with all numerical values distinct, BC6 cannot guarantee
eight items. Use

    {5,7,13,35,65,91,455,11}.

The four pure primes force chain3<5<7<11<13, with bases
3,3,5,3. The first seven items are the seven nonempty squarefree
products of5,7,13. Every choice of a dividing prime costs1/3;
strict cost below one allows at most two items at each of these
three axes, only six in total. The11 axis cannot receive any of
those seven items. Inserting extra chain primes cannot improve a
preceding gap, and omitting11 is forbidden by its pure item.

These are failures of the numerical sum criterion, not families
of classes asserted to cover actual R_3 or the integers. Actual
endpoint prefixes can coincide or contain each other, making the
antichain cost in BC5 smaller than the numerical sum. Nor does
failure of this particular transport imply failure of every
legal exchange. The boundary directs further work to actual
phases, label availability and their common realization.

## 35. The seven-item failure forces four actual roots and a sectional constraint

The numerical failure in section34 does not supply an actual
repair. Suppose175 divides the original cofactor period B and
seven cofactor APs with numerical list

    {5,25,7,35,35,175,175}

cover the actual R_3. Denote their5-coordinate data by

    a: the root of the5 class;
    d1,d2: the roots of the two35 classes;
    b: the depth-two prefix of the25 class;
    f1,f2: the depth-two prefixes of the two175 classes.

Then a,d1,d2 are three different roots. The prefixes b,f1,f2
are three different children under a fourth root r, different
from a,d1,d2. The root alpha forbidden by the original pure5
class is the fifth root. In particular the first5 projection
of actual R_3 is exactly {a,d1,d2,r}.                 (BC8)

### The complete-tree obstruction determines the phases

Assign the7 class and either175 class to their7 roots. There
are at most two forbidden7 roots, so a complete5-ary7 tree can
avoid them. On the5 axis the remaining assigned prefixes are
the three whole roots a,d1,d2 and two depth-two prefixes. If
there were at most two different whole roots, these extra two
prefixes could not prevent a complete3-ary5 tree: every other
first root still has at least three available second children.
Continuing freely through every remaining original height gives
trees whose product avoids all seven APs, contrary to PC1--PC4.
Hence a,d1,d2 are distinct.

Now assign the7 class and the first35 class to7. At5 the
forbidden prefixes are two whole roots a,d2 and the three
depth-two prefixes b,f1,f2. To prevent a complete3-ary tree,
those three prefixes must be different children of ONE further
root r outside {a,d2}. Otherwise at least three first roots
have at least three available children. Assigning the other35
class to7 gives the same conclusion with {a,d1} excluded.
The common parent of b,f1,f2 is therefore outside all three
whole roots, proving the asserted phase shape. This is the
depth-two case of the complete-tree obstruction used in
[Report375](375-deep-prime-prefix-projections-and-tree-contraction.md),
with full higher digits continued, not a flatness assumption.

Removing any one of the seven APs leaves a list satisfying NF17,
which cannot cover R_3 by PC1--PC6. Every AP therefore has a
private actual cofactor point. Its stated5 root occurs in R_3
and differs from alpha. All four roots in BC8 occur, and no
fifth root can occur because the original5 class excludes it.

### Label availability gives a genuine product only after conditioning

Suppose this list comes from a legal low inside repair retaining
C0. Two copies of the cofactor35 require numerical repair labels
35 and105. Since35 is occupied by a repair, it is absent from
original C0 and hence from the original cover. Original divisor
closure then excludes EVERY original modulus divisible by35.
Thus no original class contains both5 and7 as factors.

Write B=5^A*7^D*M, with gcd(M,35)=1, and fix one complete
remaining cofactor value u modM. If the actual section is
nonempty, it has the exact form

    R_3(u)=A_u times B_u,
    A_u subset Z/5^A, B_u subset Z/7^D.             (BC9)

Indeed, a C0 class involving neither5 nor7 either kills this
whole section or misses it. Every other C0 class, after u is
fixed, forbids only a5 prefix or only a7 prefix. Taking the
complement therefore gives the displayed product. This is a
conditional decomposition at the SAME u; the unconditioned
source remains a union of such products and need not be a product.

Let c be the first7 root of the repair's7 class. At a fixed
5-coordinate x outside the two pure repair columns

    x=a mod5 OR x=b mod25,

at most one of the four mixed repair classes can be active:
the35 classes use distinct roots d1,d2, while the175 classes
use distinct second prefixes f1,f2 under r. If one is active,
the repair can cover at most its single first7 root together
with c. If none is active, only c is available. Consequently
the SAME nonempty section must satisfy

    A_u not subset ({a mod5} union {b mod25})
       ==> |projection_mod7(B_u)|<=2.              (BC10)

An actual u with a5 point outside those columns and at least
three first7 roots would refute this repair. Global projection
sizes do not supply that witness: the5 escape point and the
three7 roots may occur at different u. The live-cofactor
qualification in
[Report375, section7](375-deep-prime-prefix-projections-and-tree-contraction.md#7-live-cofactors-obstruct-absorbing-a-larger-prime-into-new-higher-digits)
likewise does not assert that separately live original labels
have witnesses in one common remaining cofactor section.

### Actual suppliers must pay one of two conditional costs

At the same live u, define L5(u) by summing5^(-j) over original
C0 classes with modulus5^j*d, j>=1,d>1,d|M, whose actual residue
modulo d agrees with u. Define L7(u) similarly, summing7^(-j)
over active original moduli7^j*d. These sums keep numerical
labels, full heights and actual cofactor phases. No class occurs
in both groups, since original35 is absent. The remaining d
factors, when present, are all at least11.

Every live u must obey

    L5(u)>51/100 OR L7(u)>23/42.                    (BC11)

If B_u has at most two first7 roots, its uniform coordinate mass
is at most2/7. Active original7-bearing C0 classes cover its
complement, so their total conditional reciprocal cost is at
least5/7. The distinct pure7-power classes have finite total
cost strictly below sum_(j>=1)7^(-j)=1/6. The active mixed
classes must therefore pay L7(u)>5/7-1/6=23/42.

Otherwise BC10 puts A_u in the two pure repair columns. Their
uniform5-coordinate mass is1/5+1/25=6/25, since they have
different first roots. Active original5-bearing C0 classes must
cover mass at least19/25. The distinct pure5-power total is
strictly below1/4, giving L5(u)>19/25-1/4=51/100.

The assertion is pointwise on actual live sections, not a bound
on two separately optimized laws. Finding one live u with BOTH
L5(u)<=51/100 and L7(u)<=23/42 would exclude the repair. No
existing global budget cited here supplies such a common u.
Simultaneously moving5 and7 to a new3 coordinate is not an
alternative proof: separate originals5^j*d and7^j*d can then
collide at numerical label3^j*d, even though no single original
modulus contains both5 and7. Report376's injective full chain
avoids that collision but supplies precisely its stated joint
tree test, not two independently optimized coordinate bounds.

The existing PC7 law gives a precise sufficient budget test.
Select only the primes of M as a full-height chain starting at3,
skipping5 and7, and put

    kappa(d)=min_(p_i|d) r_i^(-v_(p_i)(d)), d>1,d|M.

The first base is at least9; later bases are the actual selected
prime gaps plus one. Project PC7's single law on R_3 to u. Its
support consists of live sections and its AP bounds are kappa(d).
Thus, if the actual original numerical inventory satisfies

    (100/51) sum_(5^j*d in C0, j>=1,d>1,d|M) 5^(-j)*kappa(d)
    +(42/23) sum_(7^j*d in C0, j>=1,d>1,d|M) 7^(-j)*kappa(d)
       <=1,

then the expected normalized cost
(100/51)*L5(u)+(42/23)*L7(u) is at most one under this SAME law.
At some live u both individual costs are therefore at most their
BC11 thresholds, contradicting BC11. When M=1 both mixed sums
are empty and the contradiction is immediate. This test directly
uses PC7 and averaging; it is not another probability construction.
Its inventory bound has not been proved for every hypothetical
cover. The minimum in kappa must not be replaced by a product,
and a four-root forest factor cannot be inserted into these
queries, whose moduli d contain neither5 nor7.

BC8--BC11 turn the numerical certificate's failure into phase,
original-label and same-section requirements. They do not prove
that these requirements are inconsistent. The existence of the
required common section, arbitrary mixed residual repairs, and
unrestricted odd-cover nonexistence remain unresolved.

## 36. A complete prime chain can retain an existing q coordinate

BC5 requires the entire BC2 residual to be q-free. The following
consumer combines Report376's full-height chain with section27's
root matching and applies to mixed residuals. It neither assumes
that E has a common prime divisor nor asserts that its required
trees and matching always exist.

Use the actual BC2 whole cover C with L<n classes. Its repeated
numerical bases E are all q-free, and each occurs twice; every
q-bearing numerical label occurs at most once. Write its actual
complete period as

    q^B product_(i=1,...,t) p_i^H_i M,
    q<p_1<...<p_t, H_i>=1,
    gcd(M,q product_i p_i)=1.

Here B is the residual q-height, not the cofactor-period symbol
used in sections31--35. It can be zero. Each repeated base must
have at least one dividing prime in the selected chain. Select
one actual endpoint of each pair and assign its full prefix to
one such prime, forming prefix collections S_i. All phases and
heights come from C, including any new repair coordinates.

### Reserve every numerical collision, at every height

Besides S_1, exclude from the p_1 tree the following collection T.
For every actual q-free class with modulus p_1^a*u, a>=1 and
gcd(u,q*p_1)=1, include its complete p_1 prefix in T whenever C
also contains numerical label q^a*u. The cofactor u may contain
other selected primes; this comparison uses the entire numerical
label. Put D_1=S_1 union T, interpreted as a union of prefix
cylinders. The exponents requiring this reservation range through
all a<=min(B,H_1), not just a=1 as in section27.

Let G be the set of p_1 first roots under which a complete q-ary
tail of depth H_1-1 avoids D_1. A forbidden whole root is not in
G. Use Report375's complete-tree condition to determine this set;
strict relative prefix capacity below one in a root's tail is
one sufficient test, not a necessary numerical characterization.

For every q root b, let F_b consist of the p_1 roots of ALL
actual classes in C divisible by q*p_1 whose first-q root is b.
Assume the graph with allowed edges

    b -- a  iff  a in G and a notin F_b

has a matching covering every q root, written as an injection
sigma: Z/q -> G with sigma(b) notin F_b. Use these matched roots
and their available tails to construct a complete q-ary p_1 tree.
For every i>=2 also require a complete p_(i-1)-ary tree through
all H_i digits avoiding S_i. BC5's capacity condition is sufficient
on those coordinates, while their exact tree condition may admit
more cases. All these choices must hold simultaneously.    (BC12)

### The source keeps the old q digits and still has single-AP pullbacks

Let lambda_1=q and lambda_i=p_(i-1). Write theta_i for the
prefix-compatible injection supplied by each chosen complete tree;
theta_1 has first-root map sigma. On the output carrier

    q^max(B,H_1) product_(i=2,...,t) p_(i-1)^H_i M,

associate to each z one actual old point y by CRT:

    y mod q^B = z mod q^B,
    y mod p_i^H_i = theta_i(z mod lambda_i^H_i),
    y mod M = z mod M.

The old q and old p_1 coordinates are correlated through z;
they are not sampled independently. The q exponent max(B,H_1)
provides every digit needed by both expressions. Every old point
y is covered by C, so its covering class supplies an output
event at that SAME z.

Every class divisible by q*p_1 has empty pullback. If its
first-q root is b, its old p_1 root lies in F_b, whereas the
source map selects sigma(b) outside F_b. A remaining class has
the unique numerical form

    m=q^beta product_i p_i^alpha_i u,
    gcd(u,q product_i p_i)=1, beta*alpha_1=0.

It pulls back to zero or one AP with numerical modulus

    m'=q^(beta+alpha_1) product_(i>=2) p_(i-1)^alpha_i u.

When beta>0 the old q prefix is unchanged and alpha_1=0.
When alpha_1>0, beta=0 and the p_1 prefix has one q-prefix
inverse under theta_1. There is consequently no unspecified
gap of q digits to split into multiple APs. All other primes
use their own complete prefix inverse, as in PC2.

The numerical map is injective within the q-free group and
within the p_1-free q-bearing group. Equality across these
groups forces old labels p_1^a*u and q^a*u with the SAME a
and complete cofactor u: output valuations at all other chain
coordinates recover all other old exponents. T has already
deleted the former class's prefix. Labels containing neither
q nor p_1 stay q-free in the output and cannot collide with
either q-bearing image group.

The S_i deletions remove at least one actual endpoint of every
repeated base. Since E is q-free and all other numerical labels
in C were unique, the remaining output labels are distinct.
They are odd and nonunit, each input class supplies at most one
output, and no closing class is added. Thus BC12 would give a
whole distinct odd cover with at most L-|E|<n classes, contrary
to minimum original cardinality.

### A failed root matching has an actual mixed-label cost

Fix one endpoint assignment and reserve collection as above, and
assume all the required trees for i>=2 exist. The first-coordinate
matching must fail. If g=|G|<q, the tail exclusions already leave
too few available first roots. If g>=q, section27's same Hall
argument supplies nonempty I subset Z/q, t=|I|, with

    W=G intersect intersection_(b in I) F_b,
    |W|>=g-t+1.

The actual q*p_1-bearing classes must supply every pair in
I times W. Each supplies only one root pair, irrespective of
its higher exponents, so their number is at least

    t*|W|>=t*(g-t+1)>=g.                          (BC13)

This is a necessary cost for the one common assignment and
source map, not additive costs from different optimized chains.
Unlike section27, G now also accounts for deep prefix deletion
and all-height collision reservation. The old count h0, which
reserved only q-height-one labels, cannot replace these conditions.

BC12--BC13 connect distributed repeated bases to actual mixed
q-bearing blockers while keeping every old q digit. A general
BC2 residual may fail the selected-tree or matching conditions;
no argument here forces a successful assignment for every one.
The unrestricted #7 objective and that joint existence problem
remain unresolved. The result is an ordinary consumer of the
existing tree transport and Hall argument, not new Lean evidence.

## 37. Pruned reservations charge actual depths and disjoint repair labels

Fix ONE endpoint selection, assignment and selected prime chain in
BC12. Remove the selected endpoint of every repeated base from the
inventory C, and call the remaining inventory C-minus. Its numerical
labels are distinct. This deletion alone is not asserted to preserve
whole coverage. The common source map below avoids every removed
endpoint through S_i, so coverage is preserved on its image.

Construct T-minus from the numerical pairs p_1^a*u and q^a*u
which BOTH remain in C-minus, with a>=1 and gcd(u,q*p_1)=1.
Reserve the actual complete p_1 prefix of the former class. This
is sufficient for BC12: a removed endpoint already has empty
pullback and cannot create an output collision. Every remaining
q-bearing p_1-free counterpart is charged at most once, because
C-minus has at most one class of each numerical modulus.

Put p=p_1, H=H_1 and r=p-q+1. Deduplicate S_1 union T-minus
and discard descendants of retained ancestors to obtain an
antichain D. Define its actual prefix cost and its good roots by

    Delta=sum_(xi in D) r^(-depth(xi)),
    G={first-p roots with a complete q-ary tail avoiding D}.

Report375's complete-tree duality and LA4 apply inside each
bad root. Its forbidden prefixes have relative tail cost at
least one, hence global cost at least1/r. A forbidden root
itself has this same cost. Costs in different first roots are
disjoint. Consequently

    p-|G|<=floor(r*Delta).                         (BC14)

This reuses the existing blocked-tree bound; it does not identify
the cost condition with an exact characterization of good roots.
In particular, if Delta<1, then |G|>=q. Assuming the other
selected-coordinate trees exist, BC13 forces at least

    h>=p-floor(r*Delta)

actual q*p-bearing residual classes. Thus every fixed assignment
with those other trees obeys Delta>=1 OR h+r*Delta>=p. The
floor and real-inequality versions are equivalent because h,p
are integers; neither strengthens the other.

### Charge each reservation to its actual high-q repair

Retain the unmerged upper costs

    s=sum_(m in E assigned to p) r^(-v_p(m)),
    t0=sum_(q^a*u,p^a*u both in C-minus) r^(-a),
    tau=#{q^a*u counterparts occurring in the latter sum}.

The same gcd and positive-a restrictions as T-minus apply to
the latter two expressions. Thus Delta<=s+t0 and t0<=tau/r.
If A=s+t0<1, a directly usable form of BC14 is

    h>=p-floor(r*A).

In BC2 the k original repair labels contain three disjoint groups:
the |E| first-level repairs q*m; the tau p-free repairs q^(a+1)*u
which produce the reserved q-bearing counterparts; and the h
repairs whose residual labels are divisible by q*p. Hence

    k>=|E|+tau+h.

Suppose s<1 and put c=ceil(r*(1-s))=r-floor(r*s)>0.
If tau<c, then s+tau/r<1, so BC14--BC13 give

    h>=p-floor(r*s+tau)=p-tau-floor(r*s).

The necessary alternative and its repair-budget consequence are

    tau>=c OR tau+h>=c+q-1,                       (BC15)
    k>=|E|+c;
    tau<c ==> k>=|E|+c+q-1.                       (BC16)

These are costs for one fixed common assignment, not sums of
separately optimized chains. If there are no reserved counterparts,
tau=0, the sharper branch reads k>=|E|+p-floor(r*s).
Deep prefixes pay their actual depth even when several first
roots are involved. For example, at q=3,p=5, three repeated
bases assigned at p-depth at least two give s<=1/3; with no
reserved counterparts and all other required trees present,
at least four actual15-bearing residual classes are necessary.
This is a conditional inventory consequence, not a covering example.

## 38. Coherent high-q rows need not enter the mixed blacklist

The shared source map in BC12 has single-AP pullbacks even
before all mixed q*p classes are killed. For an input numerical
label q^beta*p^alpha*u with gcd(u,q*p)=1, its old q-prefix and
the inverse of its p-prefix impose two prefixes on the SAME q
coordinate. They are either incompatible or one extends the
other. A nonempty pullback therefore has numerical modulus

    q^max(alpha,beta)*transport(u),

where transport sends each other selected p_i exponent to the
same exponent at p_(i-1), retaining every unselected prime.
This map is injective on the full p*q-free cofactor u. The
remaining obstruction is equality of numerical output labels
with different output phases, not splitting into several APs.

### Keep an entire high row when its complete common phase agrees

In the SAME C-minus and chain, fix beta>H and a full cofactor u.
Collect ALL actual classes with numerical labels

    q^beta*p^a*u, 0<=a<=H.

Call this row coherent when their residues modulo q^beta*u
are identical. Include the a=0 member if it exists; checking
only selected mixed members would miss a possible collision.
All cofactors and phases here are complete, including other
selected primes. A row with one member is coherent.

For a coherent row, its common q^beta prefix fixes all H input
digits of the p tree. Each member's p-prefix condition is thus
constant on that q-prefix cylinder. Its other coordinate
conditions pull back identically, because the full u phase is
common. Every nonempty output in the row is consequently the
SAME AP modulo q^beta*transport(u). Keep that AP once; if all
pullbacks are empty, the row contributes nothing.

Distinct rows have different output numerical labels: beta and
the full u are recoverable. Their output q-height exceeds H,
whereas every q-free input has output q-height at most H.
The remaining p-free q-bearing classes have unique labels, and
the low cross-family collisions are still removed by T-minus.
The strict beta>H condition matters. At beta=H a q-free label
p^H*u may collide with the row even if q^H*u is absent, in
which case the current T-minus rule need not reserve it.

Define safe mixed classes to be all actual mixed members a>=1
of these coherent high rows; call the other q*p-bearing classes
unsafe. In BC12, replace F_b by the p first roots of the unsafe
classes at q root b. With this smaller blacklist and the SAME
S_i, T-minus and other trees, a full root matching still produces
a distinct odd whole cover of size at most L-|E|<n.     (BC17)

Indeed, unsafe mixed classes have empty pullback by the matching;
safe rows produce the single AP just proved; and the remaining
cross-family conflicts are reserved. Every covered output point
uses the same old witness as in BC12. Removed endpoints have
empty preimage, and merging identical APs preserves their union.
The general rule to merge only equal complete phases is already
used in [Report450, sections9--10](../450-499/450-weighted-original-depths-and-the-uniform-lift-boundary.md#9-whole-coverage-needs-weighted-excess-of-distinct-projected-phases);
its separate probability estimates are not used here.

### The unsafe inventory pays the matching obstruction

Let h count only unsafe mixed residual classes and let v count
the safe mixed classes BEFORE any output merging. BC13--BC16
apply with this h. Moreover all v classes come from distinct
effective original repairs of q-height at least two with a p
factor. They are disjoint from the |E| first-level repairs, the
tau p-free counterparts and the h unsafe repairs. Therefore,
under the same s<1 and other-tree conditions,

    k>=|E|+v+tau+h,
    k>=|E|+v+c;
    tau<c ==> k>=|E|+v+c+q-1,
    c=ceil(r*(1-s)).                              (BC18)

Safe classes cannot pay for blocking the source tree even though
they still consume original repair labels. This distinction
strengthens the actual repair constraint; v is not a number of
output rows or a count of surviving merged APs.

There is also an exact unused charge in the first bucket. Let
kappa count ALL effective original repairs whose BC2 branch-
restriction residual modulus is q-free, before any endpoint
deletion. Let e_new count bases in E whose
numerical label does not occur in retained C0. Each such base
requires both repairs m and q*m, whereas every other repeated
base requires its q*m repair. Consequently

    kappa>=|E|+e_new,
    k>=kappa+v+tau+h.

In every BC18 bound, |E| can therefore be replaced by kappa,
or by the weaker |E|+e_new. This counts original input repairs,
including a repair whose residual endpoint was selected for
deletion; no output survival is presumed. These q-free residual
repairs are disjoint from all three q-bearing residual buckets.

For a single repeated base m, select just one prime p>q dividing
m; there are no other selected-tree obligations. Put a=v_p(m). Then
s=r^(-a), and BC18 gives

    a=1 ==> k>=v+p-q+1,
    a>=2 ==> k>=v+p-q+2.                          (BC19)

For instance, at q=3 a single repeated base divisible by11^2
forces k>=10 even if v=0; the root-only bound k>=9 in section27
does not give this exclusion of nine-class repairs. At p=7 and
a>=2, a seven-class repair must have v<=1. If tau<=4 instead,
the sharper branch already gives k>=8+v. All counts refer to
the SAME selected prime and its complete residual height H;
none of these conditional cases excludes arbitrary larger repairs.

### A partial family separates coherent rows from singleton rows

This exact control is a partial congruence family, not a whole
cover or a claimed realization of all BC2 assumptions. Take
q=3,p=5,H=3,B=4. Include0 mod5 and1 mod5. Put ell_0=7,
ell_1=11. For b in{0,1} and a in{1,2,3}, add the class A_(b,a)
of numerical modulus81*5^a*ell_b with CRT conditions

    x=b mod(81*ell_b),
    x=a+1 mod5^a.

These eight nonempty events are pairwise disjoint: the six
mixed events use first5 roots2,3,4; within a row those roots
are different, and the two rows have different mod81 phases.
Thus every event has a private integer. The only repeated
numerical base is5. Select0 mod5 for deletion, giving
S_1={0}, T-minus empty and G={1,2,3,4}.

The original blacklist has F_0=F_1={2,3,4}, so two q roots
have only the neighbor1 and cannot both be matched. Merely
exempting singleton high rows also fails: each high row here
has three members. Both rows are coherent, however, so the
unsafe blacklist is empty. Choose sigma(0,1,2)=(2,3,4) and
complete each tail tree so a zero input digit maps to zero.

On the shared source, z=0 mod81 gives theta_1(z mod27)=2,
while z=1 mod81 gives theta_1(z mod27)=3. Exactly A_(0,1)
and A_(1,2) have nonempty pullbacks, respectively

    0 mod567,    1 mod891.

Both pure5 events miss the selected first-root image. The
calculation proves a strict enlargement of the local transport
interface, not an odd covering counterexample.

BC14--BC19 reuse finite-tree duality, capacity counting and the
same-source Hall transport. They supply symbolic conditional
exclusions, not new Lean evidence. The unrestricted obligation
remains to force a simultaneous successful assignment or a
contradiction to its actual inventory costs for EVERY BC2
residual, including incoherent mixed rows and large repeated
base families. These conditional bounds do not establish that.

## 39. Seven-class repairs need three low labels and exclude a squared-seven collision

Consider a repair of the complete P_3 by at most seven distinct
odd nonunit moduli, excluding3 and retaining every original C0
label. Discard unnecessary classes. Let k be the remaining count
and let kappa count its low classes, whose original repair
moduli have3-height zero or one. These are precisely the repairs
counted by kappa in section38. Their cofactor moduli are all
greater than one. The repair need not divide the old period Q.

### Extend the existing common-source theorem to the repair period

Write Q=3^H*B and let B-star be the LCM of B and the non3
parts of ALL repair moduli. On this full finite cofactor carrier,
take the actual preimage

    R-star={x mod B-star: x mod B belongs to R_3}.

This preserves every old constraint; only additional prime
digits and new prime coordinates are free. List all primes of
B-star as3<p_1<...<p_t, at their full B-star heights, and set
lambda_1=3, lambda_i=p_(i-1), r_i=p_i-lambda_i+1>=3.

R-star meets every product of complete lambda_i-ary trees in
these coordinates. To check the precise bridge to Report376,
truncate each old-prime tree at its old height. Its required
branching is at least that of the chain containing only old
primes, since inserting new primes can only increase the
predecessor of an old prime. Prune to that old branching.
PC1--PC4 supplies ONE common point of old R_3 in the resulting
tree product. In each original expanded tree, extend that
point's old prefix to a leaf; choose leaves in all new prime
trees as well. CRT gives one R-star point in the original
expanded product. All high digits are permitted by the full
preimage definition.

This is the missing carrier check for directly reusing PC6 and
RC5. Their weighted-tree and finite-duality arguments now apply
on R-star with the same capacities r_i^(-j) at every expanded
height. In particular, for one fixed assignment of actual low
repair cofactor prefixes with costs delta_i<1, ONE law nu on
R-star avoids all those classes and simultaneously satisfies

    nu(x=a mod p_i^j)<=min(1,r_i^(-j)/(1-delta_i)). (NF20)

Use the cofactor phases of the low REPAIR classes here, not
an arbitrarily chosen duplicate endpoint from BC12: that
endpoint might belong to C0. The new law is constructed on
the actual extended source, not by separately conditioning or
optimizing one law per query. Cofactor queries with several
prime factors use the minimum of the coordinate bounds.

Finally let J be the maximum3-height needed by Q and every
repair modulus. Keep the original first3 root fixed and attach
uniform remaining3 digits through height J, independently of
nu. This is one law on the complete P_3 in the common repair
period. A high repair with modulus3^beta*e, beta>=2 and
gcd(e,3)=1, has mass zero if its first root disagrees, and
otherwise has mass

    3^(-(beta-1))*nu(x=a mod e).                   (NF21)

Both old and new higher3 digits are included. NF20--NF21 do
not use NF13's six-class restriction or assume an inside repair.

### One or two low classes leave too little high-class mass

If kappa=0, BC1 already requires k>=N_3>=9, contrary to k<=7.
This uses the independent original-cover bound already used in NF10.

If kappa=1, assign its cofactor to one prime root p. All bases
are at least3, so NF20 gives p-root capacity at most1/2,
p-depth-two capacity at most1/6, and all other prime-root
capacities at most1/3. Among high numerical labels, only9
and9p can have mass greater than1/9, with respective bounds
1/3 and1/6. A mixed cofactor involving another prime receives
that other prime's cap, not a product of two caps. The at most
six high classes therefore have total mass at most

    1/3+1/6+4/9=17/18<1.

All low classes have mass zero, so coverage is impossible.

Suppose kappa=2. If the two cofactors admit assignments to
different primes p,j, delete one actual root in each. Their
root caps are at most1/2 and their depth-two caps at most1/6;
other prime roots retain cap at most1/3. Only numerical labels
9,9p,9j,9pj can exceed1/9: their bounds are1/3 for9 and1/6
for each of the other three. The at most five high classes have
total mass at most

    1/3+3/6+1/9=17/18<1.

If no such different-prime assignment exists, both cofactors
are powers of one prime p. If either exponent is at least two,
assign its complete prefix at p and the other class's first
root. Their combined cost is at most1/9+1/3=4/9. Thus the
p-root cap is at most3/5 and its depth-two cap at most1/5.
Only9 and9p can exceed1/9, with bounds1/3 and1/5. The high
total is at most

    1/3+1/5+3/9=13/15<1.

The remaining case has both cofactors equal to p. Distinct low
moduli then force the repair labels p and3p. If p is an old
support prime, divisor closure puts the original pure label p
in retained C0, contradicting availability of the repair p.
If p is a new prime, its coordinate in R-star is wholly free.
Use the original full-chain PC7 law on R_3 and extend it
uniformly through all added old digits and other new primes.
In the independent new p coordinate use the uniform law on
the full p-power carrier avoiding the at most two actual first
roots of these low classes. At least p-2>=3 roots remain.
Every prime-root query then has mass at most1/3 under this
SAME law; old bounds hold after uniform extension. NF21 bounds
the five high classes by

    1/3+4/9=7/9<1.

These cases exhaust kappa<=2. Consequently every such legal
repair with at most seven classes must satisfy

    kappa>=3.                                     (NF22)

The inequalities use distinct numerical high labels to count
each exceptional label only once. Pure higher3 powers have
mass at most1/9. These are ordinary applications of the common
source bounds after the carrier bridge, not separate marginal
optimizations or new general probability theorems.

### A single repeated base cannot contain49 at this budget

Now suppose the BC2 residual has E={m} with49 dividing m.
Select the single prime p=7 for BC18. Then q=3,r=5 and the
one endpoint's cost is s=5^(-v_7(m))<=1/25. There are no
other selected trees to require, and

    c=ceil(5*(1-s))=5.

The strengthened kappa form of BC18 gives k>=kappa+v+5.
If k<=7, NF22 gives kappa>=3, so k>=8+v, a contradiction.
Thus

    k<=7 ==> NOT(E={m} and49 divides m).           (NF23)

This exclusion permits arbitrary other prime factors, arbitrary
phases and original heights, and moduli beyond the old period.
It concerns the complete P_3 repair retaining C0 and the parent
label3, within the hypothetical minimum whole cover. It does
not exclude multiple repeated bases or every seven-class repair.
In a minimal repair with any high class, the complete B-star
cofactor of its private point leaves the entire higher3 tail
uncovered by all low classes,
so at least three high classes are required. Combining NF22
with section31's exclusion of high-containing six-class repairs
leaves only the mixed counts(3 low,4 high) or(4 low,3 high)
at budget seven, before using other restrictions. Sections40--42
exclude these mixed cases and the all-low seven-class branch.
Unrestricted #7 and larger joint repairs remain unresolved;
no new Lean verification is claimed.

## 40. Three low classes cannot leave a cofactor confined to one nonunit AP

Use section39's same full cofactor carrier B-star and actual
R-star. Take three low classes from a repair retaining C0 and
excluding label3. Let their actual nonunit cofactor APs be
C_1,C_2,C_3, and put

    R-low=R-star minus (C_1 union C_2 union C_3).

For EVERY cofactor AP A of modulus e>1 dividing B-star,

    R-low not subset A.                            (NF24)

The extra AP is an arbitrary query, not a fourth legal low
repair. Its modulus and phase may repeat those of a low class.
The proof reuses capacity-two Hall, PC6 and the extended tree
bridge in section39, with a separate treatment of genuinely
free new coordinates.

### Four actual APs admit one simultaneous avoidance point

Consider the four labelled cofactor items C_1,C_2,C_3,A. If
they can be assigned to dividing primes with at most two items
per prime, their full-prefix cost on every assigned axis is
at most2/3<1. PC6 supplies complete avoiding trees, and the
expanded product-tree property supplies one R-star point
avoiding all four actual APs. This proves NF24 in that case.

If no such assignment exists, the existing capacitated Hall
criterion supplies at least three items supported on just
one prime p. Indeed, any set of at most four items with two
or more neighboring primes has capacity at least four. Take
ALL pure p-power items as one group, of size three or four.

If p is an old support prime, at most one of the three low
cofactors equals p: the original label p belongs to retained
C0, leaving only3p as a possible low repair with that cofactor.
The additional arbitrary AP contributes at most one more
depth-one item. Every other item in this pure group has depth
at least two. Its full-prefix cost is therefore at most

    2/3+2/9=8/9<1.

If there is a fourth item outside the group, choose one of
its prime factors other than p. Its cost on that other axis
is at most1/3. PC6 and the same expanded source give a
point avoiding the entire four-item collection.

If p is a new prime, its full coordinate in R-star is free.
When all four items are pure p powers, avoid all of their
at most four actual first roots; p>=5 leaves a choice. When
only three items are pure p powers, assign the remaining item
to a dividing prime j different from p. If j is old, the old
tree obstruction supplies an actual R_3 point outside that
one j-root. If j is new, choose a different j-root in its free
coordinate. Independently set the free p coordinate outside
the at most three pure-item roots and complete all other free
digits. CRT gives one actual R-star point avoiding all four
items. No product assumption on the old coordinates is used,
and the new p roots need not support the chain's tree branching.

This exhausts the Hall failure and proves NF24 for all original
heights and all cofactor moduli in the repair period. The point
constructed also proves R-low is nonempty.

### Four high classes would force precisely the forbidden confinement

Suppose a repair with exactly these three low classes has at most four
high classes. At every cofactor z in the SAME nonempty R-low,
the entire higher3 tail must be covered by high classes. Divide
them by the second3 digit of their actual phase. Each of the
three next roots needs at least one class. With at most four
classes, at least two roots have exactly one high class each.

A singleton class must have original3-height exactly two:
a deeper prefix misses part of that root's complete remaining
tail. Moreover its cofactor AP must contain every z in R-low,
since no other high class is available at that root and all
low classes miss z. The two singleton numerical labels are
9e_1 and9e_2. Distinctness gives e_1!=e_2, so at least one
e_i is greater than one. Its AP contains all of R-low,
contradicting NF24. Therefore

    exactly three low classes ==> at least five high classes
      in any such complete repair.                (NF25)

Combining NF25 with NF22 and the complete-tail requirement of
at least three high classes, an inclusion-minimal legal repair
with seven classes has only these possibilities:

    seven low classes;
    four low classes and three high classes.

In the second case, the three high classes occupy different
second3 roots and all have3-height exactly two. Write their
distinct numerical labels as9e_1,9e_2,9e_3. Their cofactor
APs each contain the whole nonempty remainder after the four
low classes. They are jointly compatible, and their intersection
is one AP of modulus K=lcm(e_1,e_2,e_3). Since three distinct
positive e_i divide K, the number of divisors of K is at
least three; in particular K is composite.             (NF26)

This is a condition on one actual intersection and the same
remaining cofactor set. Three separately live cofactor phases
would not suffice. Sections41--42 exclude the composite-AP
confinement and the all-low seven-class branch. These ordinary
deductions do not settle unrestricted Erdős #7 or claim new
Lean verification.

## 41. Four low cofactors cannot confine the remainder to a composite AP

Take four distinct legal low repair labels, retaining all C0
and excluding3. Write their nonunit cofactor APs as C_1,...,C_4.
Let A be an AP of a composite modulus K coprime to6. Enlarge
the old cofactor period B to include the four cofactor moduli and K,
and let R-star be the full preimage of the SAME original R_3.
Then

    R-star minus union_(i=1,...,4) C_i not subset A. (NF27)

The query A need not be a repair and may repeat a low phase.
No bound on the total number of other repair classes is used.
The proof classifies five labelled cofactor items using the
existing Hall and full-prefix criteria, and disposes of the
remaining numerical pattern by the existing whole-coordinate
transport. It does not require new probability estimates.

### Five items reduce to one two-prime squarefree pattern

Suppose the four C_i and A cover R-star. An assignment with
at most two items per prime would give prefix costs at most
2/3, contradicting the expanded product-tree property in NF20's
carrier check. By capacity-two Hall, either at least three
items are pure powers of one prime, or all five items use
only two primes. Three neighboring primes already have total
capacity six, so there is no additional Hall case.

First collect all pure p-power items when there are at least
three. If p is old, at most one low item has cofactor p,
because label p is occupied by C0. The query, if pure p,
has depth at least two since K is composite. The total full-
prefix cost of this entire group is at most

    1/3+4/9=7/9<1.

At most two other items remain, each having a prime factor
different from p. Assign them there, with at most2/3 cost on
any such axis. PC6 and the actual expanded source contradict
coverage.

If p is new, its entire coordinate is free. Among the four
low items, depth-one cofactor p can occur at most twice, from
the distinct labels p and3p. The query, if it belongs to this
pure group, has depth at least two.
Under uniform measure in this free p coordinate, the pure
group's forbidden prefixes have total mass at most

    2/p+3/p^2<1, p>=5.

Choose a point outside their actual union. The at most two
remaining items can first be avoided on non-p axes using the
expanded tree property with this free coordinate omitted.
Joining these choices by CRT preserves one old R_3 point.
This also rules out the pure-group case for arbitrary new
heights; it does not pretend that p is an old constrained axis.

There are now at most two pure items on any axis. A remaining
Hall failure forces all five items onto exactly two primes p,j.
Suppose any item has exponent at least two at p. At least three
items are divisible by p, since otherwise at least three would
be pure j powers. Assign three p-divisible items to p, including
the deep item and every pure p item. This is possible because
there are at most two pure p items. The other two items are
divisible by j. Their respective costs are at most7/9 and2/3,
again contradicting coverage. The same argument applies at j.

Thus all five cofactor moduli are squarefree, using only p,j,
and the composite query has K=p*j. If p is new and j old,
assign A and all pure j low items to j. There is at most one
such low item, so the old j coordinate has at most two roots
to avoid; its actual single-coordinate tree supplies a common
old source point. All remaining low items contain p, and the
free p coordinate can avoid their at most four first roots.
If both primes are new, the A and pure j group forbids at most
three j roots, and the remaining low group at most four p roots.
Both free complements are nonempty. These are actual free
coordinates of R-star, not independent replacements of old ones.

Only the case of two OLD primes remains. Their pure low
cofactors p and j occur at most once each. The cofactor pj
occurs at most twice, from labels pj and3pj. Four low items
therefore force the numerical list

    {p,j,pj,pj}, with query K=pj.

Order p<j and select just the chain3<p<j, with full actual
heights. Its capacities are r_p=p-2 and r_j=j-p+1. Assign
one pure item and two of the three mixed items to one axis,
and the other pure item and remaining mixed item to the other.
If either capacity is greater than three, give that axis the
three items; both costs are strictly below one. Both capacities
equal three only when p=5,j=7. Hence coverage would force

    low cofactors {5,7,35,35}, K=35,
    actual low repair labels {15,21,35,105}.

In particular original C0 has no label35: it would make repair
35 unavailable. The old pure labels5 and7 each occur in C0.

### A triple repetition can be removed by the same source map

The assumed confinement says that the five actual cofactor APs
with moduli5,7,35,35,35 cover all of R-star. Adding them to C0
therefore covers the entire cofactor carrier and, by periodicity,
all integers. This is one common family, not five separate tests.
Its only repeated numerical labels are5 and7, each twice, and35,
three times. All other C0 numerical labels occur once.

Choose one actual5 endpoint and assign its root to the5 axis.
Choose one actual7 endpoint and assign its root to the7 axis.
Of the three35 events choose any two different labelled events,
assigning one to5 and the other to7. Each axis has at most two
forbidden first roots. Continue a complete3-ary5 tree and a
complete5-ary7 tree through their full coordinate heights,
avoiding these roots. Use the SAME CRT source map of PC1.

The four selected events have empty pullback. PC2 gives at
most one AP for each other input, with numerical map

    5^a*7^b*u -> 3^a*5^b*u, gcd(u,3*5*7)=1.

It is injective on the original numerical labels, so all output
labels are distinct after the selected deletions. They remain
odd and nonunit. Every new point has one old witness covered
by the input family, so the output family covers every integer.
Its count is at most

    |C0|+5-4=|C0|+1<n.

The independent old N_3>=9 already makes this strict; no new
bound from section42 is used. This contradicts minimum original
cardinality and proves NF27. The consumer directly uses PC1--PC2;
BC5's stated pair-only hypothesis is not applied to a triple.
No condition on the relative phases of the three35 APs is needed.

## 42. Every complete legal ternary repair needs eight classes

Consider any complete P_3 repair retaining every C0 class, using
distinct odd nonunit moduli and excluding label3. Then

    number of repair classes >=8.                  (NF28)

If it had at most seven classes, discard unnecessary classes.
Section40 leaves only an all-low repair or the mixed count
four low and three high. In the mixed case, NF26 confines the
same nonempty low remainder to one composite-modulus AP.
NF27 excludes that confinement, including outside repair moduli.

The all-low case is a direct use of BC7, rather than a new
cofactor classification. Restrict C0 and the repair to the
original first3 branch as in BC2. The resulting whole cover
is entirely3-free and has at most |C0|+7<n classes, using the
independent old N_3>=9. Its repeated bases E are pairs, each
requiring a distinct effective first-level repair3m. Hence
|E|<=7. BC7 requires at least eight repeated bases in an
entirely3-free BC2 residual, a contradiction. This closes the
all-low branch without estimating its possible seven-item
cofactor phase layouts separately.

### Each non-parent ternary root now needs eight original labels

Reuse NF19's entire-branch CRT translation. For each of the
two first3 roots rho different from a_3, its full original
3-bearing inventory covers {rho} times T_3 times R_3.
Translate ALL those classes by the same c satisfying

    c=a_3-rho mod3^H, c=0 modB.

This preserves numerical labels, cofactor phases and every
higher3 digit, and yields a legal complete P_3 repair. NF28
requires at least eight labels in each of these disjoint
original inventories. Including the original prime3 class,

    N_3>=1+8+8=17.                                (NF29)

This is a necessary condition on the same minimum hypothetical
whole cover, with unrestricted original heights and total prime
support. The new bound is downstream of NF10, NF16 and BC7;
their independent N_3>=9 input must not be replaced by NF29.

The proof reuses the established matching and tree transports
and adds the four-low composite-confinement exclusion. It is
ordinary symbolic mathematics, not new Lean verification or
a claim of literature priority. Larger repairs, arbitrary
collision inventories and unrestricted Erdős #7 remain open.

## 43. Five low classes cannot confine the remainder to any nonunit AP

The complete-coordinate transport also handles one numerical
triple among the input classes. The necessary extension of NF17
concerns the list of endpoints to delete, not the list of all
repair cofactors.

### Six deletion items permit one repeated numerical value

Let D be a labelled list of at most six integers greater than
one and coprime to6. Suppose every numerical value occurs once,
except that at most one value may occur twice. Then its items
can be assigned to dividing primes with

    sum_(m assigned to p) 3^(-v_p(m))<1
      at every assigned prime p.                         (NF30)

If the repeated value is absent or is not a pure prime power,
this is exactly an application of NF17. It remains to allow
two copies of p^a. All other numerical values are distinct.
Use the same capacity-two Hall criterion as NF17.

Suppose first that at least three items are pure powers of r.
Assign all of them to r. If r=p, their finite total cost is
less than1/2+3^(-a)<=5/6. Otherwise it is less than1/2.
At most three items remain, each having a factor outside r.
Capacity two on those other factors fails only when precisely
three items have the same singleton support {q} after r is
removed.

If r!=p and one of the three is mixed, move it to r, at cost
at most1/3; the r cost stays below5/6 and the other two cost
at most2/3 at q. If all three are pure q powers, their cost
is below5/6, including the possible repeated pure power.

If r=p, the three remaining values are distinct. Unless all
three have q-exponent one, assign them all to q, at cost at
most2/3+1/9=7/9. Otherwise write them as r^u*q. Their three
u values are distinct nonnegative integers, so one is at least
two. Assign that item to r and the other two to q. The r cost
is then below5/6+1/9=17/18, and the q cost is at most2/3.
This proves the pure-group case.

Now every prime has at most two pure items. A remaining Hall
failure places five or six items in a pair of primes. That pair
must contain p: otherwise its five items and the two pure p^a
items would exceed six. Write the pair as {p,q}. Any item outside
it can be assigned to a factor outside it; there is at most one.
The pure p items are exactly the two copies of p^a, with total
cost at most2/3. Let t<=2 count the pure q items. Their values
are distinct, giving cost at most0,1/3,4/9 for t=0,1,2.

Initially assign mixed items of p-depth one to q, and those of
p-depth at least two to p. If at most two go to p, its cost is
at most8/9. The mixed items initially sent to q have distinct
q-exponents. For t=0 or1 their finite sum is less than1/2,
so the total q cost is below5/6. For t=2 there are at most
two mixed items; their cost is at most4/9, giving total at most
8/9. If instead at least three mixed items initially go to p,
move all but two of them to q. There are then at most two
items in total at q: two pure p items and two mixed p items
already account for four of the at most six items. Hence q
costs at most2/3 and p at most8/9. This completes NF30 using
indivisible assignments and the existing Hall theorem.

### One common cover supplies the endpoint list

Take any kappa<=5 distinct legal low repair labels, retaining
C0 and excluding3. Let their cofactor APs be C_1,...,C_kappa.
For ANY nonunit cofactor AP A, with modulus K coprime to6,
enlarge the common cofactor period to contain all these moduli
and take the full preimage R-star of the original R_3. Then

    R-star minus union_i C_i not subset A.                 (NF31)

This includes prime K and arbitrary new-period moduli. No total
repair-budget bound or effectiveness assumption on the low
classes is needed. A is a query; it need not be a legal repair.

If confinement held, C0 together with the kappa low cofactor
APs and A would cover the whole enlarged cofactor carrier and
therefore every integer. Before A is added, each numerical
cofactor m occurs at most twice. When C0 contains m, legality
forbids repair label m, leaving only possible label3m. When
C0 does not contain m, the only low labels with that cofactor
are m and3m. Adding A leaves multiplicity at most three, with
only its modulus K capable of occurring three times.

At every repeated modulus choose all but one actual event for
deletion. The resulting numerical deletion list has at most
kappa+1<=6 items; only K can occur twice. NF30 assigns these
events to prime coordinates at strict base3 cost. Take all
their prime factors as the chain starting at3, with full heights
in this ACTUAL cover. Every PC6 base is at least3. Merging
coincident or contained prefixes only decreases the assigned
costs, so PC6 supplies complete avoiding trees.

Apply the SAME CRT map and numerical injection of PC1--PC2.
Each selected event disappears; every remaining event pulls
back to at most one AP; no numerical repetition remains.
The output moduli are distinct odd nonunits and cover every
integer through its one old witness. Their number is at most

    |C0|+kappa+1<=|C0|+6<n,

using only the independent old N_3>=9. If the deletion list
is empty, the input cover itself gives this contradiction.
Thus NF31 holds. This reuses the transport on the actual
common cover, without a new law or an assumed product source.

NF31 strengthens NF24 and NF27, while leaving their independent
proofs and their downstream bootstrap uses intact. It does not
exclude a larger low family, or confinement to an arbitrary
union of query APs.

## 44. Every eight-class repair is entirely first-level and repeats retained labels

Keep the same complete P_3, retained C0 and unavailable label3.
Let kappa be the number of effective low repair classes and h
the number of effective high classes. All cofactor statements
below use ONE R-star in the enlarged common period. Write
R-low for its complement of all actual low cofactor APs.

### One or two low classes require larger high inventories

For kappa<=2, take t nonunit query cofactor APs whose numerical
moduli are pairwise distinct, with kappa+t<=4. Then

    the kappa low APs and t query APs cannot cover R-star.
                                                               (NF32)

This is the four-item argument of NF24 with a different role
allocation. Capacity-two Hall succeeds unless at least three
items are pure powers of one prime p. For an old p, at most
one low item has depth one, since C0 retains label p, and at
most one query has depth one, since their numerical moduli
are distinct. The entire pure group's prefix cost is at most
2/3+2/9=8/9. At most one other item remains and has a prime
factor outside p; assign it there. PC6 and the expanded tree
property supply one common avoidance point. For a new p its
coordinate is genuinely free; avoid the at most four first
roots of the pure items, and avoid any outside item on another
axis before freely completing the p coordinate. This also
proves that R-low is nonempty.

Partition high classes by their second3 root. Call a class
shallow high if its original modulus has3-height two. Within
one second3 root, every deeper high class occupies at most
1/3 of the complete remaining3 tail at any fixed cofactor.
These are finite proportions through the common maximum height;
no old or newly required digit is omitted.

Suppose first kappa=2. A root without an effective label9 cannot
have at most two high classes. If it has shallow high classes,
their nonunit cofactor moduli are distinct. NF32 gives one
z in R-low missed by all of them; at most one deeper class
remains, which cannot cover that root's complete tail at z.
If both classes are deeper, their total tail proportion is at
most2/3. Thus every such root needs at least three high classes.

For kappa=1, a root without9 cannot have at most three high
classes. If at least one is shallow, NF32 simultaneously avoids
all shallow cofactors, leaving at most two deeper classes and
tail proportion at most2/3. If all are deeper, a count at most
two again fails. For three deeper classes, covering the complete
tail for every z in R-low requires all three to have3-height
exactly three and each cofactor AP to contain the whole R-low.
Otherwise, at some z the sum of their tail proportions is
strictly below one. Their distinct labels27e force at least
one e>1, whose confinement contradicts NF32 with a single query.

At most one root can contain numerical label9; even that root
needs at least one high class. Consequently, without a bound
on the total repair budget,

    kappa=1 ==> h>=9, and h>=12 if no effective9;
    kappa=2 ==> h>=7, and h>=9  if no effective9.           (NF33)

For kappa=0, BC1 gives k>=N_3; the independent old lower bound
N_3>=9 already excludes a repair of at most eight classes.
Thus a complete repair with k<=8 must have at least three low
classes. NF33 does not assert that its equality cases exist.

### Five high classes cannot supplement three low classes

Consider an inclusion-minimal complete repair with exactly
eight classes. NF28 makes every repair of at most eight classes
have exactly eight after unnecessary classes are removed.
If both low and high classes occur, R-low is nonempty: otherwise
all high classes would be unnecessary. Each of the three next3
roots therefore requires at least one high class.

With three low classes, five high classes remain. If two
roots are singletons, their labels must be9e and9f, with e!=f,
and both cofactor APs must contain the same R-low. At least one
is nonunit, contradicting NF31. The root counts are therefore
(1,2,2), and the singleton must be label9.

In either two-class root, both high classes must have3-height
two. Two deeper classes cover at most2/3 of the tail. If one
class is shallow and the other deeper, the shallow cofactor
must contain all of R-low: at any cofactor it misses, the lone
deeper class cannot cover the complete tail. By NF31 the shallow
class would then have to be another label9, which is unavailable.

The four two-class-root labels are thus9e_1,...,9e_4, where
the e_i are distinct and greater than one. Each root's pair
of cofactor APs covers the SAME R-low. If any3e_i is not one
of the three existing low numerical labels, add a fourth low
class with numerical modulus3e_i, first3 root a_3 and exactly
that query's cofactor phase. CRT supplies its actual residue.
This is a legal low label: it is not3, is distinct from the
existing lows, and cannot coincide with any label in3-free C0.
It also differs from every high label by its3-height.

The new low remainder is contained in the other nonunit AP
from the same two-class root. NF31 forbids that confinement.
Hence each of the four distinct labels3e_i would have to be
one of only three low labels, a contradiction. This promotion
checks numerical availability; it never assumes an arbitrary
query is already a legal repair.

Together with NF25, the same argument has no total-budget
restriction: exactly three low classes require at least six
high classes. NF31 likewise shows that exactly four or five
low classes require at least five high classes, since three
or four high classes would supply two forbidden singletons.

### The only eight-class possibility repeats eight retained cofactors

For four low and four high classes, at least two next3 roots
are singletons, again contradicting NF31. For five low and
three high classes, all three roots are singletons, with the
same contradiction. Six or seven low classes leave fewer than
three high classes and cannot cover any remaining full tail.
NF33 and BC1 handle zero, one or two lows. Therefore

    every complete legal repair with at most eight classes
    has exactly eight classes, all low.                    (NF34)

This is a structural necessary condition, not an exclusion of
every eight-class repair. Apply BC2 to such a repair, using
k=8<N_3 from the independent old N_3>=9. Its restricted whole
cover is entirely3-free. BC7 requires at least eight repeated
bases, and each one consumes a different first-level repair3m.
All eight repair labels must therefore be of that form. There
is no3-free repair left to supply the other endpoint of a
repetition; each m must occur in retained C0. In particular,

    repair labels are3m_1,...,3m_8;
    m_1,...,m_8 are distinct original C0 labels.            (NF35)

Every such repair divides the original period Q, since3 divides
Q and each m_i divides its3-free part. Thus no new prime, new
height or high3 repair can occur at this minimum budget. The
actual phases of the eight pairs are still subject to coverage;
NF35 does not supply them or show they exist.

### Equality in the seventeen-label bound has ternary height one

If N_3=17, NF19 and NF28 force each non-parent first3 branch
to have exactly eight original labels. Translating each entire
branch as in NF19 yields an eight-class legal complete repair.
NF35 shows that every one of those originals has3-height one
and its cofactor label is already in C0. Together with the
original prime3 class, these account for all seventeen originals.
Consequently

    N_3=17 ==> v_3(d)<=1 for every original modulus d.      (NF36)

Equivalently, any minimum hypothetical whole cover with an
original modulus divisible by9 must have N_3>=18. This is a
downstream consequence of NF29 and NF34--NF35; the earlier
independent N_3>=9 bootstrap is unchanged.

The remaining eight-class problem is a common cofactor cover
with eight distinct repeated retained labels. BC6 stops at
seven distinct bases, and section34's eight-base example still
blocks a universal numerical assignment argument. Its actual
pair phases, larger repair budgets and unrestricted Erdős #7
remain unresolved. These are ordinary symbolic deductions,
independently checked as mathematics, not new Lean verification
or a claim of literature priority.

## 45. The eight-base obstruction forces a twin-prime cube and eighteen original labels

The selected prime chain in BC5 need not contain every prime
factor of the repeated bases. It must contain a dividing prime
to which each deletion item can be assigned. This freedom gives
an exact numerical boundary at eight DISTINCT bases.

Let E contain at most eight distinct integers greater than one,
all coprime to6. A strict certificate means a selected increasing
chain3<p_1<...<p_t and an assignment to dividing selected primes
such that

    sum_(m assigned to p_i) r_i^(-v_(p_i)(m))<1,
    r_1=p_1-2, r_i=p_i-p_(i-1)+1 for i>1.

Such a certificate fails to exist precisely when E has the form

    {5,7,s,35,5s,7s,35s,(s-2)^a},
    a>=1, s>=13, and both s and s-2 are prime.              (NF37)

This classifies the numerical certificate, not actual covering
families or all possible transports. The necessity below first
resolves the small Hall obstructions at conservative base3,
then uses the freedom to select the chain. NF17, NF30 and the
existing capacitated Hall theorem are reused directly.

For at most seven items the conclusion already follows from
BC6, so assume there are eight. Choosing a subchain is essential:
the seven nonempty squarefree products of7,13,19, together with
5*11*17, fail on their full support chain. Its7,13,19 bases
are all three. Selecting only5,7,13,19 instead allows costs
1/3,2/3,3/7,2/7: assign5*11*17 to5; assign7 and7*13 to7;
assign13,13*19 and7*13*19 to13; and assign19 and7*19 to19.
Thus the absence of a certificate on one imposed chain would
not justify invoking NF37.

### Three pure items still admit a strict assignment at eight bases

Suppose at least three items are pure powers of p. Assign all
of them to p, at finite total cost below1/2. At most five items
remain. Try capacity two on their factors other than p.

If at least three have the same singleton support {q} after
p is removed, collect ALL such items in T. They are distinct
p^u*q^v, with u>=0,v>=1. Move the v=1 items with u>=2 to p.
Their distinct u values give additional cost below1/6. At q
there remain at most two depth-one items, with u=0 or1, and
all other items have q-depth at least two.

The q cost is strictly below one except for the possible crude
bound2/3+3/9=1. Equality in that bound requires five T items:
two at depth one and three at depth two. The three depth-two
items have different u values, so one has u>=2. Move that
item to p as well. The p cost stays below

    1/2+1/6+1/9=7/9,

and the q cost becomes at most8/9. At most two items lie
outside T and the pure p group; each has a factor outside
{p,q}, so assign them there at cost at most2/3 on any axis.

If no such singleton obstruction exists, capacity-two Hall can
fail only when all five remaining items use just two primes
q,r after p is removed. If any of them still has a p factor,
assign it to p, increasing its cost by at most1/3. The four
others satisfy capacity-two Hall on q,r. If none has a p factor,
these five distinct values are assigned by NF17. This resolves
the entire pure-group case without altering actual exponents.

### Five items on a pair also admit a strict assignment

Assume no prime has three pure items. If at least five items
are supported within {p,q}, take all g of them, where5<=g<=8.
First consider the internal pair. For at most seven items use
the conservative-base pair proof in BC6. For eight items, each
axis has at most two pure items. Their total costs are bounded
by0,3/9,4/9 when their counts are0,1,2.

There is at most one shallow mixed item pq. Assign every other
mixed item to an axis where its depth is at least two, at cost
at most1/9. If pq is present, the two initial axis costs are
each at most one and together at most11/9. When both are below
one, assign pq to the lighter axis, giving cost at most
11/18+1/3=17/18 there. If an axis has cost one, move one of
its deep mixed items to the other axis and also put pq there.
The other axis originally costs at most2/9, so it finishes at
most2/9+1/3+1/3=8/9. The first axis strictly decreases.

If pq is absent, each initial axis costs at most10/9 and their
sum is at most4/3. An axis of cost exactly one can transfer
one mixed item to the other; the latter originally costs at
most1/3 and finishes at most2/3. If an axis costs more than
one, transfer two mixed items to the other. Its initial cost
is below1/3, so its final cost is below one. On the first
axis, one pure item leaves at most five deep mixed items,
giving3/9+5/9=8/9; two pure items leave at most four deep
mixed items, giving4/9+4/9=8/9. Zero pure items cannot produce
a cost above one. This proves the eight-item pair assignment.

At most three items lie outside the pair. Capacity two on
their factors outside {p,q} succeeds unless there are exactly
three, all with the same singleton outside support {r}. Then
g=5. If all three are pure r powers, their distinct values
give total cost below1/2. Otherwise choose one with a nonunit
{p,q}-part u. Apply NF30 to the five internal pair values and
u: only u can duplicate one existing value. Replace that u
item by the actual outside item; its assigned p or q exponent
is unchanged. Assign the other two outside items to r, at cost
at most2/3. Thus this obstruction also has a strict assignment.
All these assignments remain valid when further support primes
are included in the chain, since every base is at least3.

### The remaining three-axis core determines every exceptional value

There are now at most two pure items per prime and at most four
items supported on any pair. Capacity-two Hall can fail only
through seven or eight items supported on exactly three primes
U={u_1<u_2<u_3}. If all eight lie there, select U alone and use
integer capacities

    u_1-3, u_2-u_1, u_3-u_2.

Each is at least two and their sum u_3-3 is at least eight.
Singleton-supported groups have at most two items and pairs
at most four. Hall gives an assignment with at most r_i-1
items on each axis, hence strict prefix cost.

Suppose exactly seven items lie in U, with one other value w.
If a core item has depth at least two at some u in U, reserve
that item at u. The other six core items satisfy capacity two:
their singleton and pair counts remain at most two and four.
The u cost is at most2/3+1/9=7/9, and the other U costs at
most2/3. Give w to a factor outside U. Including that factor
in the chain leaves all bases at least3, so this is a strict
certificate.

Otherwise the seven distinct core values are precisely the
seven nonempty squarefree products of the three primes in U.
If w has a factor in U, select U alone. The eight items then
still have singleton-supported counts at most two and pair-
supported counts at most four, even after w's outside factors
are ignored. The preceding integer-capacity Hall argument
again succeeds.

Thus w must be coprime to all primes in U. Select one prime
j dividing w and take only U union{j} as the chain. The item
w can go to j. If any U base exceeds three, its integer capacity
is at least four; the other two capacities are at least two.
Hall assigns all seven core items strictly. Failure therefore
requires all three U bases to equal three.

In a four-prime chain above3, three specified primes have base
three only in this arrangement:

    U={5,7,s}, j=s-2, s>=13.

Indeed a first prime with base three must be5. If the extra
prime j came first or second, three successive selected primes
greater than3 would differ by two, which is impossible because
one would be divisible by3. If j came fourth, the first three
primes would have to be5,7,9. Thus j is third, giving the
displayed arrangement. If w had any other prime factor, selecting
that factor instead of j would break this arrangement and give
a certificate. Therefore w=(s-2)^a for some a>=1, proving the
necessity in NF37.

Conversely, in the displayed exceptional family the pure values
5,7,s and(s-2)^a force every certificate to include all four
primes. The bases at5,7,s are at most three; extra selected
primes cannot increase them. Each of the seven squarefree core
items costs at least1/3 wherever it is assigned. Strict cost
allows at most two such items at each of those three axes,
only six in total. The(s-2) axis cannot receive a core item.
No strict certificate exists. This proves the exact boundary.

### The two original ternary branches cannot both have eight labels

For an eight-class repair, NF35 gives eight distinct retained
cofactor labels E. Its BC2 residual is entirely3-free and has
fewer than n classes, using the independent old N_3>=9. A
strict certificate for E would let BC5 construct a smaller
distinct odd whole cover. NF37 therefore forces E to have the
displayed twin-prime form. In particular every such repair must
use both numerical labels15 and21.

If N_3 were17, NF19 and NF28 would give eight original labels
at EACH non-parent first3 root. Translate each entire branch
by its own NF19 translation, which preserves numerical labels.
Each translated repair must contain15 and21. The original
family would therefore use each of those numerical moduli in
both disjoint first3 branches, contrary to global distinctness.
The contradiction combines necessary label requirements from
two separately valid whole-cover descents; it does not combine
their source laws or choose their phases independently. Hence

    N_3>=18 in every minimum hypothetical odd whole cover. (NF38)

For an arbitrary eight-class repair, the numerical necessity
is exactly

    {15,21,3s,105,15s,21s,105s,3(s-2)^a},

with the same twin-prime condition. Its cofactor labels are all
retained in C0. This does not assert that phases completing
such a repair exist, or that all transports fail there. Actual
pair phases, nine-class repairs and unrestricted Erdős #7
remain unresolved. NF37--NF38 are ordinary symbolic deductions
using the cited existing criteria, without new Lean verification
or a claim of literature priority.

## 46. Two-axis collision inventories admit an arbitrary-budget exclusion

The number of repeated bases need not be bounded when their
joint prime support has only two axes. Let E be any finite set
of different nonunit integers supported on p<q, with p>=5.
Select only the chain3<p<q and write

    R=p-2, T=q-p+1.

Pure powers must go to their own axes. Assign a mixed p^a*q^b
to the axis with the larger exponent, assigning equal exponents
to the axis with the larger base. If that larger base is V>=5,
the total cost on it is bounded by

    sum_(a>=1) (a+1)*V^(-a)
      =(2V-1)/(V-1)^2<=9/16.

The other axis, of base W>=3, receives its pure powers and
at most b-1 mixed items at exponent b. Its cost is bounded by

    sum_(b>=1) b*W^(-b)=W/(W-1)^2<=3/4.

These are upper bounds over all possible exponent pairs, so
they hold for every finite inventory and arbitrary depths.
They are not independence assumptions about the actual classes.

Both bases equal three only for p=5,q=7. If the numerical value
5 is missing from E, send the equal-exponent mixed items to5.
The first envelope loses the missing pure term1/3, giving

    delta_5<=5/4-1/3=11/12, delta_7<=3/4.

If7 is missing, exchange the axes. A single-axis inventory
already costs less than sum_(a>=1)3^(-a)=1/2. Thus

    any finite distinct two-axis inventory has a strict
    certificate, except possibly when its support is{5,7}
    and it contains BOTH numerical values5 and7.           (NF39)

For an entirely3-free BC2 residual cover with fewer than n
classes, apply this certificate to one actual endpoint of each
repeated base and invoke BC5. Its repeated-base set cannot be
supported on at most two primes unless the exceptional condition
in NF39 holds. The OTHER residual moduli may contain arbitrary
primes and complete heights: PC1--PC2 transport the selected
coordinates through their full actual heights and preserve all
unselected coordinates. This conclusion has no bound on |E|.
It does not apply to a residual that still contains3-bearing
labels; those require the additional collision controls of
sections36--38.

### The exceptional two-axis condition cannot be discarded numerically

Consider the twenty-four distinct values

    E_4={5^a*7^b:0<=a,b<=4, (a,b)!=(0,0)}.

Any candidate chain must contain5 and7. Both have base three;
additional selected primes cannot change either base or receive
an item. The minimum possible MAXIMUM of the two numerical
loads is exactly

    min_assignment max(delta_5,delta_7)=82/81.              (NF40)

For a lower bound, place every off-diagonal mixed item in its
cheaper direction, namely the larger-exponent axis. The minimum
TOTAL cost, including pure and diagonal items, is

    2*(1/3+1/9+1/27+1/81)
      +1/3+3/9+5/27+7/81=156/81.

Before allocating diagonal items, each axis has pure plus cheap
off-diagonal cost40/81+18/81=58/81. Whichever axis receives35
therefore has baseline cost at least85/81. Let A be the sum of
cheap costs of off-diagonal items reassigned AWAY from that
axis. Reassignments into it and further diagonals only add cost.
If both final loads were at most one, A would have to be at
least4/81. Every reversed off-diagonal assignment increases
total cost by at least twice its former cheap cost. Hence the
total final cost would be at least

    156/81+2A>=164/81>2,

a contradiction. All loads are multiples of1/81, so their
maximum is at least82/81. This bound is attained: keep the
cheap off-diagonal directions except for5^3*7^2, which goes
to7; put35 at5 and all other diagonal items at7. The resulting
loads are82/81 and80/81. The same rule on the height-three
rectangle gives26/27 and25/27, so this nested rectangular
family first fails at height four.

This is an exact obstruction to the unmerged numerical prefix
sum. It is not a family of covering classes: no phases are
specified. Actual endpoint coincidences can still reduce BC5's
antichain costs, and other transports are not excluded.

### Missing seven does not extend the eight-item classification

The nine distinct values

    {5,13,19,65,95,247,1235,11,17}                         (NF41)

do not contain7 but have no strict selected-chain certificate.
Their pure values force the chain to contain5,11,13,17,19.
The first seven items are the seven nonempty squarefree products
of5,13,19. Each of those three axes has base three, and adding
more primes cannot increase these bases. Seven core items
cannot fit the six strict slots on those axes. Thus NF37's
requirement for the numerical value7 cannot be extended to nine
items. The corresponding missing5 claim holds by section48;
this numerical example does not produce a covering counterexample.

## 47. Actual endpoint phases force a positive common covering demand

Take an eight-class legal complete repair. By NF35 and NF37,
put u=s-2 and write its eight repeated cofactor bases as

    E={5,7,s,35,5s,7s,35s,u^a},
    a>=1, s>=13, with u and s prime.

Work in the ONE actual whole cofactor cover consisting of C0
and the eight low repair cofactor APs. Each base m in E has
two actual endpoints, one retained and one from the repair.
They have different full phases; otherwise the repair class
would miss R_3. For a squarefree core base m and p|m, let
S_p(m) be the one- or two-element set of first p roots offered
by its two endpoints.

### Root sharing is exactly what this endpoint certificate can use

If two different core bases m,m' containing p have
S_p(m) intersect S_p(m') nonempty, choose one endpoint of each
at a common p root. Both disappear when that root is avoided,
at antichain cost1/3 on the p axis. Assign the other five core
bases with integer capacities one at p and two at each of the
other two core primes. The existing Hall criterion holds:
singletons have at most one remaining pure item; any pair
containing p has at most three items, and the other pair at
most three; the total count is five. Hence every core axis
avoids at most two roots.

Use the chain3<5<7<u<s. Its core bases are all three, while
the u base is u-6>=5. The remaining repeated item u^a can
be deleted at cost(u-6)^(-a)<1 on its own axis. BC5 then
produces a smaller distinct odd whole cover, a contradiction.

Conversely, if every pair of incident core bases has disjoint
root sets on each shared axis, one deleted root can remove
an endpoint of only one core base. Each core axis has strict
capacity for at most two roots, while there are seven core
repetitions to eliminate. Their pure bases force the three
axes, and the pure u^a item forces the separator u. No extra
selected prime improves these capacities. Thus the exact failure
condition for these endpoint/full-prefix certificates is

    S_p(m) intersect S_p(m') empty
      for all different core m,m' divisible by p.          (NF42)

This is a condition on the actual phases of the SAME input
family. It characterizes this certificate mechanism, not every
possible transport or every whole-cover argument.

At p=5, the pure5 pair offers two different roots. The three
other incident bases35,5s,35s each offer at least one. NF42
forces them to partition all five roots with sizes2,1,1,1.
Consequently each mixed pair has the SAME5 root at its two
endpoints, and those three roots are distinct from each other
and from both pure5 roots.

The35 endpoints must therefore differ at7, and the5s endpoints
must differ at s. At7 the pure7 pair and35 pair each offer
two roots. The other incident pairs7s and35s cannot both
offer two, since that would require eight different7 roots.
At least one of those two pairs has the same7 root at both
endpoints, and must then differ at s. In particular, at least
seven different s roots occur among the four incident endpoint
sets. These are endpoint counts, not claims that all such
retained-class roots occur in actual R_3.

Every one of the eight repair classes is indispensable by NF28.
Its private point in P_3 supplies a cofactor point in R_3.
The repairs with bases5,35,5s,35s therefore make their four
different5 roots occur in R_3. The retained pure5 class excludes
its own root, proving that the first5 projection of R_3 is
exactly the other four roots. These separate private witnesses
are not assumed to lie in one further-cofactor section.

### The remaining original classes must cover one explicit complement

Under NF42, two different core events with overlapping prime
supports are disjoint: on a shared prime their endpoint-root
sets are disjoint. The two endpoints at one base are disjoint
as well. Events with disjoint prime supports have their ordinary
CRT intersection density. Inclusion-exclusion for the fourteen
core endpoint events therefore has only the following terms:

    single-event sum       =(26s+96)/(35s),
    two-event intersections=(4s+60)/(35s),
    three-event intersections=8/(35s).

There are no larger intersections. The union density is exactly
22(s+2)/(35s). The two distinct u^a endpoint phases lie in a
separate CRT coordinate and have union density2/u^a. Hence the
complement of all sixteen endpoint events has exact density

    D=(13s-44)/(35s)*(1-2/u^a)>=225/1001>0.                (NF43)

The minimum displayed bound uses s>=13 and u^a>=11. Both
factors increase with these lower bounds; no unproved joint
distribution is substituted. All statements are finite counts
in the common period, or equivalently normalized Haar counts.

Every point of this same complement must be covered by the
remaining C0 classes. None of the eight repair classes or the
eight retained E endpoints covers it. Therefore the necessary
actual-inventory condition is

    sum_(d in C0, d not in E) 1/d>=D>=225/1001.

The remaining classes are not declared independent; this last
step is only the union bound on their actual common complement.
No uniform upper bound below D is supplied for their unrestricted
inventory. The positive demand is not an uncovered-integer proof.

### The local phase conditions themselves are compatible

For a=1, the following table gives compatible endpoint phases
on coordinates5,7,s. A star means that coordinate is not part
of the event. The first endpoint is retained and the second is
the repair cofactor.

| Base | Retained phase | Repair phase |
|---|---|---|
|5|(0,*,*)|(1,*,*)|
|7|(*,0,*)|(*,1,*)|
|s|(*,*,0)|(*,*,1)|
|35|(2,2,*)|(2,3,*)|
|5s|(3,*,2)|(3,*,3)|
|7s|(*,4,4)|(*,4,5)|
|35s|(4,5,6)|(4,5,7)|

Use phases0 and1 for the two u endpoints. These satisfy NF42
and all its stated root-count consequences. The retained core
labels together with u are divisor-closed. If desired, give
the repair labels3m the common first3 root1 and add the parent
class0 mod3. The resulting partial numerical family is still
divisor-closed, and classes with comparable distinct moduli are
disjoint.

Nevertheless the cofactor point with roots2 at5,6 at7,8 at s
and3 at u misses all sixteen endpoint events. At first3 root1
it also misses the added parent. Thus this is a partial family,
not a whole cover, a complete repair, or a minimum-cover example.
It verifies that the local endpoint and divisor conditions alone
do not give a contradiction. The unresolved step is to control
the remaining original classes on the positive common complement.
These are ordinary symbolic results, not new Lean verification.

## 48. Nine distinct collision bases without five admit a strict certificate

Let E contain at most nine different nonunit integers coprime
to6. If the numerical value5 does not occur, some selected
prime chain above3 admits a strict assignment:

    sum_(m assigned to p_i) r_i^(-v_(p_i)(m))<1
      at every selected axis,
    r_1=p_1-2, r_i=p_i-p_(i-1)+1.                         (NF44)

The hypotheses concern the numerical value5, not the absence
of prime5 from every factorization. The proof reuses the Hall
criterion, NF17, NF37 and NF39. It adds the nine-item cases;
it does not reprove those assignment or transport theorems.
For at most eight items NF37 already proves the assertion,
so assume that E has nine items.

A useful way to apply the existing Hall criterion is to reserve
at most two items, each at an axis where its exponent is at
least two. Assign the remaining items with integer capacities
r_i-1. Even if both reserved items use the same axis, its
total cost is at most

    (r_i-1)/r_i+2/r_i^2=1-(r_i-2)/r_i^2<1.

Conservative capacity two and base three can also be used,
giving cost at most8/9. Reserving an item always keeps its
actual prime exponent; no numerical replacement is involved.

### A group of three pure powers admits a strict assignment

Suppose at least three items are pure powers of p. Assign all
of them to p. Their distinct exponents give cost less than1/2
at conservative base three. At most six items remain. Try
capacity two on their prime factors other than p.

First suppose a prime q has at least three remaining items
whose support after removing p is exactly {q}. Collect ALL
such items in T, with3<=|T|<=6. They are different values
p^u*q^v, u>=0,v>=1. Assign to p every T item with u>=2 and
v equal to1 or2. Their total added p cost is less than

    2*sum_(u>=2)3^(-u)=1/3.

Thus p costs less than5/6. At q there remain at most two
items of depth one, at most two of depth two, and all others
have depth at least three. Its cost is at most

    2/3+2/9+2/27=26/27.

If at most two items lie outside the pure p group and T,
assign them to factors outside {p,q}. Every such axis costs
at most2/3. This also works for three outside items whenever
their outside factors admit capacity two.

The only additional failure has exactly three pure p items,
three T items and three outside items whose outside support
is the same singleton {r}. Use a sharper assignment for T.
If their q depths are not all one, put them all at q, at cost
at most7/9. Otherwise their p depths are different, so one is
at least two; put that item at p and the other two at q.
The p cost is at most13/27+1/9=16/27, and q costs at most2/3.

If the three outside r depths are not all one, put all three
at r, at cost at most7/9. If all are one and an outside item
has a p factor, put that item at p, whose cost is at most
25/27, and the other two at r. If none has a p factor, the
three values are q^b*r with different b. Put one with b>=2
at q. Its cost is then at most7/9+1/9=8/9; the other two
cost at most2/3 at r. This resolves every singleton failure.

Now assume that no projected singleton has three items. A
capacity-two failure must place five or six remaining items
in a pair {q,r} after removing p. If there are five and one
has a p factor, put one such item at p, at total p cost less
than5/6; the other four satisfy capacity two on q,r. If all
five are p-free, assign them by NF17. At most one other item
remains, and it has a factor outside {p,q,r}.

If there are six, the entire support is U={p,q,r}. Select
only U, and denote the corresponding bases by R_p,R_q,R_r.
For the six non-pure-p items use capacities

    c_p=R_p-2, c_q=R_q-1, c_r=R_r-1.

The already assigned pure p group costs less than1/(R_p-1),
and1/(R_p-1)+(R_p-2)/R_p<1. The total capacity is
max(U)-4>=7. A singleton q or r contains at most two items;
either pair containing p also contains at most two, by the
projected-singleton assumption. Hall can therefore fail only
on {q,r}. Its capacity is even, so failure requires capacity
four and at least five p-free items. Assign those five or six
different values directly by NF17; any one remaining item has
a p factor and goes to p at total cost less than5/6.
Otherwise Hall supplies the required assignment. This completes
the pure-group case, without using the missing5 hypothesis.

### Five or more items on a pair also admit a strict assignment

Assume every prime has at most two pure-power items. Suppose
g>=5 items are supported on a pair {p,q}, and take ALL such
items. If g=9, select the pair alone and apply NF39: its only
possible exception requires the missing numerical value5.
If g is seven or eight, reuse the conservative-base pair
assignment in sections34 and45. At most two outside items
remain; assign them outside {p,q}, at cost at most2/3 per axis.

It remains to treat g=5 or6. If the outside items admit
capacity two on their factors outside {p,q}, use that assignment
and the existing internal pair assignment. Failure gives at
least three outside items with the same singleton outside
support {r}. Write U={p,q,r}. At most two distinct internal
pure powers occur at either p or q. Among the internal pair
values, only p,q,pq can be squarefree, so at least g-3 items
have a depth of at least two.

If g=6, there are exactly three outside items, all supported
on U. Reserve two deep internal items. If another pair, say
{p,r}, has five items, it must contain both internal pure p
items and all three outside items. Choose the deep pure p
item as one reservation. Both external pairs cannot have
five items: that would make all three outside items pure r
powers, contrary to the present assumption. After these two
reservations every singleton has at most two items and every
pair at most four. The seven remaining items satisfy Hall
for the actual U-chain capacities R_i-1, whose sum is
max(U)-3>=8. Restore the deep reservations using the bound
at the start of this section.

If g=5 and exactly three of the four outside items have outside
support {r}, the fourth item has a factor outside U. Reserve
two deep internal items. If {p,r} has five items, reserve the
deep pure p item as one of them; again both external pairs
cannot have five items. The six remaining U items satisfy
capacity two. Restore the reservations, and assign the fourth
outside item to a factor outside U. Every axis has cost at
most8/9, regardless of the added prime's effect on the chain.

Finally let g=5 with all four outside items supported on U.
Use the actual U-chain capacities, of total at least eight.
The following reservations leave every pair with at most four
items and at most eight items altogether:

- If both {p,r} and {q,r} have at most four items, reserve
  any deep internal item.
- If only {p,r} is too large and has six items, it consists
  of two internal pure p items and all four outside items.
  Reserve the deep pure p item and one deep outside item.
  The latter exists because the four outside values are
  supported on {p,r}, contain r, and only r and pr among
  them can be squarefree.
- If only {p,r} is too large and has five items, reserve the
  deep pure p item when there are two internal pure p items.
  If there is just one, all four outside items belong to
  {p,r}; reserve any deep internal item and a deep outside
  item. Exchange p,q for the symmetric cases.
- If both external pairs have at least five items, each has
  exactly five. There must be two internal pure p items,
  two internal pure q items, two outside pure r items, one
  outside item with support {p,r}, and one with support
  {q,r}. Indeed, counting the four outside items in both
  pairs forces at least two pure r items, and there cannot
  be three. Reserve the deep pure p and deep pure q items.

Singleton counts remain at most two. Hall applies, and at most
two restored deep items keep every cost strict. This resolves
the pair case without replacing any actual exponent.

### The remaining Hall obstructions are three- and four-axis cores

Now every singleton has at most two items and every pair at
most four. Suppose exactly g>=7 items lie on three primes
U, taking all items supported there.

For g=9, at least one item is deep, since only seven nonunit
squarefree values use U. Reserve it. The remaining eight items
satisfy the actual U-chain Hall capacities, whose sum is at
least eight, and the reservation keeps the costs strict.

For g=8, give the ninth item to a factor j outside U and
select U together with j. If any U base exceeds three, their
total integer capacity is at least eight, so Hall assigns all
eight core items. Otherwise all three U bases equal three.
The four-prime chain analysis in NF37 forces U to contain5.
Because numerical5 is missing, at most six core items are
squarefree. Reserve two deep items and apply capacity two to
the remaining six. Assign the outside item to j.

For g=7, a deep core item can be reserved while the other six
use capacity two. Assign the two outside items to factors
outside U, at cost at most2/3 per outside axis. If there is
no deep item, the core is exactly the seven nonempty squarefree
products of U. Thus5 is not in U. Choose one outside factor
for each of the other two items and select these with U.
The three U bases cannot all equal three: each U prime would
need its predecessor two smaller in the selected chain. That
predecessor cannot itself lie in U, since then three primes
greater than3 would be spaced by two. Such a triple is
impossible by reduction modulo3. Hence three different outside
predecessors would be required, but at most two were selected.
One U base is therefore at least five. Hall assigns the seven
core items using total capacity at least eight; the two outside
items use at most2/3 at their chosen outside axes.

If no triple contains seven items, capacity-two Hall can fail
only when all nine items are supported on four primes U.
Select those four primes. Their capacities sum to max(U)-3,
which is at least ten. Singletons, pairs and triples have at
most two, four and six items, respectively, so Hall holds.
If no such four-prime support exists, capacity two already
succeeds on the full support. This completes NF44.

### The missing-five threshold is sharp for this numerical criterion

Take the seven nonempty squarefree products of {13,19,31}
together with the three values11,17,29. These ten different
values omit both5 and7. Their six pure prime values force a
selected chain to contain11,13,17,19,29,31. The bases at13,19,31
are all three; adding selected primes cannot increase them.
Seven squarefree core items still require seven slots on three
axes which each have only two strict slots. No numerical strict
certificate exists. This is the same obstruction mechanism as
NF41 and establishes the sharp nine-item threshold in NF44.
It specifies no covering phases and is not a covering example.

### The whole-cover consumer keeps the three-free hypothesis

In an entirely3-free BC2 residual cover with fewer than n
classes, let E be the distinct repeated cofactor bases. NF44
and BC5 give the necessary condition

    numerical5 absent from E ==> |E|>=10.                 (NF45)

Each repeated base m consumes a different first-level repair
label3m. Consequently a legal complete repair of at most nine
classes whose BC2 residual is entirely3-free must use label15
and repeat cofactor5. Equivalently, if the repair omits15 and
its BC2 residual is entirely3-free, its class count is at least ten.
For these at-most-nine-class repairs, the already established
NF38 gives k<=9<N_3, so BC2 supplies the smaller whole cover.

There is one immediate restricted original-family consequence:
if every original3-bearing label has3-height one, the two
non-parent first3 branches cannot each have at most nine labels.
NF19 translates either whole branch into a repair with entirely
3-free BC2 residual; NF45 would force numerical15 in both
disjoint branches.
Each branch still has at least eight labels by NF28. Therefore

    original3-heights at most one ==> N_3>=19.            (NF46)

For the excluded equality N_3=18, each translated repair has
fewer than N_3 classes, so BC2 applies without an additional
small-cover assumption. In general a nine-class repair can
contain higher3 labels. The proof above does not eliminate that
case by itself. Section49 handles mixed nine-class repairs
without15 and obtains N_3>=19 without the height restriction.
The arbitrary remaining inventory in NF43 and unrestricted
Erdős #7 remain unresolved. These are ordinary symbolic
deductions, with no new Lean verification or literature-priority
claim.

## 49. Small repeated-value lists exclude all nine-class repairs without fifteen

Two additional assignment cases control the higher3 classes
which section48 leaves untreated. They reuse the same Hall,
complete-prefix and common CRT transport criteria. Numerical
items in this section are labelled: two equal values represent
two actual events whose prefixes may be different.

### Seven items permit one repeated numerical value

Let D be a list of at most seven nonunit values coprime to6,
with every value occurring once except at most one which may
occur twice. The full support prime chain above3 admits

    sum_(m assigned to p_i) r_i^(-v_(p_i)(m))<1
      on every axis.                                     (NF47)

NF30 covers at most six items, and BC6 covers seven distinct
values. Assume exactly seven items and one repeated value.
Try capacity two on all support primes.

If the full group of pure p items has size k>=3, put them at p.
Their total conservative-base3 cost is below5/6, including
the possible duplicate. At most four items remain. Unless
capacity two works on their other factors, collect all items
with singleton projected support {q} as T. There are three
or four such items; at most one further item has a factor
outside {p,q}. Write T as p^u*q^v.

Let h count T items with v=1. If h<=2, all of T costs at
most2/3+2/9=8/9 at q. If h>=3, retain the two smallest u
values among these h items at q and move the others to p.
Keep every v>=2 item at q, still at cost at most8/9.
If the duplicate is pure p, T is numerically distinct. For
k=3, the initial p cost is at most7/9, and the moved u values
are at least2 and3 when two are moved, adding at most4/27.
For k=4, three T items leave just one moved u>=2, and the
initial p cost is at most22/27. Both bounds give at most25/27.
If instead the pure p items are distinct, their cost is below
1/2. For h=3 the moved u is at least one, adding at most1/3.
For h=4, k=3 and the initial cost is at most13/27. At most
one u value repeats; the largest two u values are at least
one and two, adding at most4/9 and giving at most25/27.
Assign the possible remaining item outside {p,q}.

Now assume each axis has at most two pure items. If at least
five items lie in a pair {p,q}, take all g of them. For
g<=6 use NF30 inside the pair and put the at most two other
items outside it. It remains that all seven items use this pair.

If the duplicate is pure p^a, its two copies cost at most2/3
at p. The other at most five items have a q factor and are
numerically distinct. If at most two have q-depth one, assign
all of them to q. Its cost is at most one; equality requires
two depth-one and three depth-two items. Those three have
different p exponents, so move one with p-depth at least two
to p, giving p cost at most7/9 and q cost at most8/9.
If h>=3 have q-depth one, move the h-2 largest p exponents
to p. They are different and at least two, so their finite
cost is below1/6. The p cost is below5/6 and q costs at most8/9.

Suppose the duplicate is mixed. If pq occurs at most once,
the seven-item pair proof of BC6 applies without alteration:
that proof uses only the distinct pure powers, the number of
deep items and their depths, not uniqueness of the deep mixed
values. With pq present, the two initial deep-plus-pure loads
are each at most8/9 and have sum at most10/9; put pq on the
lighter axis. Without pq, each load is at most one. Equality
forces every mixed item onto that axis and leaves the other
load zero, so moving one mixed item makes both costs strict.

If pq is the repeated value, first assign each other mixed
item to a depth of at least two. The initial loads A,B are
each at most7/9 and their sum is at most one. Indeed, with
P=0,1,2,3,4 pure items, their maximum combined costs are
(0,3,6,7,8)/9, and at most5-P deep items remain. If both
A,B<2/3, put one pq on each axis. If the heavier load is
at least2/3 and the lighter is less than1/3, put both pq
items on the lighter axis. The sole remaining boundary is
(A,B)=(2/3,1/3), after exchanging the axes if necessary.

Attaining sum one forces every deep item's chosen depth to
be exactly two. The boundary can have two pure items, one
on each axis, with all three deep items on the heavier axis;
or three pure items, two on the heavier axis, with both deep
items there. Four pure items give loads at most5/9 on each
axis and cannot reach this boundary. The deep mixed values
are distinct because pq uses the only duplicate. At least
two of them have the same heavier-axis depth two, so their
other depths differ; one of those other depths is at least
two. Move that item to the lighter axis. The loads become
at most5/9,4/9. One pq on each gives at most8/9,7/9.

With neither a pure group of three nor a pair of five, a
remaining Hall failure places all seven items on exactly three
primes. The full-support chain has integer capacities r_i-1
of total at least eight; its singleton and pair demands are
at most two and four. Hall applies. All earlier cases used
base3 bounds and therefore remain valid on the full support
chain. This completes NF47.

Apply NF47 to the actual endpoint deletion list in NF31.
With kappa<=6 low classes plus one query, this list has at
most seven items and only the query's modulus can occur twice.
The input whole cofactor cover has at most |C0|+7<n classes,
using the independent N_3>=9. The same PC1--PC2 map therefore
gives the extended nonconfinement statement

    kappa<=6 ==> R-star minus union_i C_i not subset A
      for every nonunit cofactor AP A.                    (NF48)

The low labels remain legal and distinct, C0 is retained,
and the query is arbitrary with modulus coprime to6. Full
actual heights and any enlarged period are kept as in NF31.

### Six items with two repeated values suffice when five is missing

Let D have at most six labelled nonunit values coprime to6,
each of multiplicity at most two, with at most two values
having multiplicity two. Suppose numerical5 is absent. Then
some selected prime chain admits a strict prefix assignment.
                                                               (NF49)

Try capacity two. A Hall failure has either three pure powers
on one axis or five items supported on a pair. Suppose first
there are k>=3 pure p items. Their finite total base3 cost is
less than1/2+1/3+1/9=17/18: the distinct powers cost below
1/2, and at most two different powers can be repeated.
For k>=4, assign the at most two remaining items outside p.

For k=3, the only further capacity-two failure has three items
p^u*q^v. If any v>=2, put all three at q, at cost at most7/9.
If all v=1 and one u>=2, move such an item to p. Three pure
p items cost at most7/9, so p then costs at most8/9 and the
other two items cost at most2/3 at q. Otherwise every u is
zero or one. Both values q and pq must occur, since no value
has multiplicity three. Move one pq to p. If the pure p
items are distinct, their cost at most13/27 leaves the total
at most22/27. If a repeated pure p^a has a>=2, their cost
is at most5/9 and the new total at most8/9.

The remaining pure group is {p,p,p^b}, b>=2. As q also
occurs and5 is missing, neither p nor q is5. Select only
this pair. At least one of its bases is at least five. If
that is the q base, all three other items cost at most3/5
there. Otherwise place one pq at p, with total p cost at
most2/5+1/25+1/5=16/25, and the other two items at q.

Now every axis has at most two pure items. Collect all g>=5
items supported on a pair {p,q}. If either pair base is at
least five, the integer capacities are at least four and two;
singleton demands are at most two and total demand at most
six, so Hall succeeds. For g=6 select the pair alone. If
both bases are three, the pair is {5,7}. Without numerical5,
the only squarefree available values are7 and35. Each occurs
at most twice, so at least two items have a depth of at least
two. Reserve two such items; the other four satisfy capacity
two on the pair, and restoring them costs at most8/9 per axis.

For g=5 and one outside item, select one of its factors outside
the pair, together with p,q; if there is no outside item,
select just the pair. Unless some pair base exceeds three,
the pair must contain5. Indeed, two core primes different
from5 with base three would need two different outside
predecessors, two less than themselves. They cannot be each
other's predecessors, which would require three primes greater
than3 spaced by two. There is at most one selected outside
prime. Thus at most two squarefree pair values remain available
when5 is missing, accounting for at most four items. Reserve
one deep item, assign the other four with capacity two, and
restore it. Put the possible outside item at its chosen outside
factor. This completes NF49.

### Small high-root groups are shallow in a minimal repair

Consider an inclusion-minimal legal complete repair of nine
classes. Let kappa be its low count and h its high count.
If h>0, the common cofactor remainder R-low after all lows
is nonempty, and each of the three second3 roots needs at
least one high class. NF33, NF31 and BC1 with NF38 leave
only the mixed counts

    (kappa,h)=(2,7),(3,6),(4,5),(6,3).

The last case fails NF48. Its three roots are singletons;
each singleton must have original3-height two and its cofactor
must contain all of R-low. NF48 forces each to be the pure
label9, contrary to numerical distinctness.

For kappa<=4, every root containing at most three high
classes consists entirely of classes of original3-height two.
To see this, a mixture of shallow and deeper classes has at
most two deeper classes. They occupy strictly less than the
complete remaining3 tail at each fixed cofactor. Therefore
the shallow cofactors must already cover all of R-low, making
every deeper class in that root redundant. If all classes
are deeper, at most two cannot cover the complete tail.
Three could do so only if all have3-height exactly three
and each cofactor contains R-low. NF31 then forces all three
to have numerical label27, again impossible. This uses the
one actual R-low and complete tails through the common height.

A singleton root must consequently be the pure label9.
In a minimal repair, that label also occupies its root alone.
Every other two- or three-class root therefore supplies two
or three distinct nonunit cofactor queries with labels9e.
Their union covers the SAME R-low.

If a two-query root has a label3e absent from the current
lows, promote that query to a low class with numerical label3e,
first3 root a_3 and the same cofactor phase. Its label is legal: it is not3,
not in C0, not a high label and not an existing low label.
The new low remainder is confined to the other nonunit query.
For kappa<=4 this contradicts NF31 with at most five lows.
Thus BOTH promoted labels from every two-query root must
already occur among the lows.

If a three-query root has two promoted labels absent from
the lows, promote those two distinct queries. For kappa<=3
there are at most five lows, whose remainder is confined to
the remaining nonunit query, contradicting NF31. Hence at
least TWO of its three promoted labels must already be lows.

For (kappa,h)=(2,7), NF33 forces label9 and root counts
(1,3,3). The two triple roots demand at least four different
low labels, but there are only two. For (3,6), the only root
counts are (2,2,2) without9 or (1,2,3) with9. The former
requires six low labels; the latter requires four different
low labels. Both exceed three. These exclusions do not assume
that the query APs were originally allowed repair labels:
promotion checks their availability before adding them.

### The last mixed case without fifteen has a six-item deletion list

For (kappa,h)=(4,5), the only root counts are (1,2,2).
The singleton is9, and the other four high labels are9e_i,
with e_1,...,e_4 different nonunit cofactors. The promotion
argument forces the four current low labels to be precisely
3e_1,...,3e_4. Suppose the complete repair omits numerical15;
then every e_i differs from5.

Fix one of the two-query roots. The family consisting of C0,
the four low cofactor APs, and those two actual queries covers
the whole cofactor carrier. Its numerical multiplicities are
at most three at the two query moduli and at most two at
the other low moduli. Delete all but one event at each
repeated modulus. The deletion list has at most six items,
at most two different values occurring twice, and no value5:
all of its values lie among e_1,...,e_4.

Apply NF49 to this list and use the complete PC1--PC2 witness
map through its actual heights. Every deleted event has empty
pullback; every remaining event has at most one AP as pullback;
the surviving numerical moduli are distinct odd nonunits.
The resulting whole cover has at most |C0|+6<n classes.
This contradicts minimal original cardinality and excludes
the last mixed case without15.

For an arbitrary complete repair of at most nine classes,
first take an inclusion-minimal complete subfamily. If it has
at most eight classes, NF28, NF34 and NF37 force eight low
classes including15. If it has nine classes and is all low,
NF38 gives9<N_3 and NF45 forces15. If it has nine classes
and is mixed, the cases just proved force15. Therefore

    every legal complete repair with at most nine classes
    retaining C0 and excluding3 must use numerical15.     (NF50)

### Nineteen ternary labels are necessary without a height restriction

Apply NF19 to the two actual non-parent first3 branches of
the same minimum hypothetical original cover. Its CRT
translations keep every numerical label and every higher3
tail, and separately give legal complete repairs. Each branch
has at least eight labels by NF28. If both had at most nine,
NF50 would require numerical15 in both original branches,
violating global distinctness. One branch must therefore
have at least ten labels. Including the parent3 gives

    N_3>=1+8+10=19.                                       (NF51)

This conclusion has no bound on original prime support or
heights. The independent N_3>=18 of NF38 supplies the small
repair comparison in NF50; NF51 is downstream and does not
replace the earlier N_3>=9 bootstrap premises. The two branch
arguments use necessary numerical labels, not independently
chosen optimal phases or different source laws combined as one.

NF51 is a necessary condition on a minimum hypothetical whole
cover. Eight- and nine-class repairs containing15 have not
been excluded. Repairs of ten or more classes, the remaining
inventory in NF43 and unrestricted Erdős #7 remain unresolved. NF47--NF51
are ordinary symbolic deductions, without new Lean verification
or a literature-priority claim.

## 50. Branch contraction excludes ten-class repairs with only one or two lows

Keep the minimum hypothetical whole cover, its retained C0,
complete private region P_3 and legal repair contract of NF18.
All low classes have original3-height at most one. All high
classes are partitioned by their actual second3 digit. The
cofactor carrier includes the full periods of any new repair
labels; R-low is the actual remainder after the low classes.

### A small root must collide with a retained low parent

The branch restriction of Jenkin--Simpson, Theorem8, is already
recorded in [the source note](../../../../../../Library/Arith/jenkin2003compositecovering.md)
and used in BC1--BC2. Apply that restriction inside one
second3 root, keeping the lows. Its collision check gives

    kappa+t<8 ==> the root contains9, or contains a shallow9f
      whose parent label3f is already a low label.        (NF52)

Here kappa counts all retained low repair classes and t counts
the high classes in this root. No bound on their heights is
imposed. This is a consumer of the existing branch restriction
and NF28, not a new general restriction theorem.

For completeness, take one cofactor period B containing C0,
all low classes and the selected high classes. Choose J at
least the original3-height and every selected high height
minus one. Enlarge the old carrier to3^(J+1)*B and use
3^J*B for the new carrier. On the complete private first3
branch, use the single CRT map

    (a_3+3u,z) |-> (a_3+3s+9u,z),

where s is the selected second3 digit. It is a bijection
between these two complete tail spaces and leaves the entire
cofactor coordinate unchanged. Every retained low class has
the same membership condition before and after this map.
The pullback of a selected high class3^a*f is one actual AP
of modulus3^(a-1)*f, with its cofactor phase unchanged and
its complete ternary phase obtained from this same map.

The lows and these pullbacks cover all of the new P_3: a
point missed by the lows maps to the old selected root and
must be covered by one of that root's high classes. Distinct
selected labels remain distinct after division by3. A
contracted label cannot collide with3-free C0 or a3-free
low. A deep label stays of height at least two, so it cannot
collide with any low. The only possible low collision is
9f becoming3f; the only forbidden label3 comes from9.

If neither exception in NF52 occurs, the kappa+t classes
therefore form a legal complete repair. NF28 gives at least
eight classes, proving NF52. The contracted labels belong
to an explicitly constructed NEW repair; no claim that
contraction preserves the old numerical labels is made.
Labels from discarded original3-bearing branches are not
additional forbidden labels in the legal repair contract.

### Shallow query roots require at least two occupied parents

Reuse the small-root argument of section49 with NF48 in
place of NF31. In an inclusion-minimal repair with kappa<=6,
any root containing at most three high classes is entirely
of3-height two. If it has both shallow and deep classes,
at most two deep classes remain. At every cofactor missed
by the shallow classes they cover at most2/3 of the full
tail, so the shallow classes already cover R-low and the
deep classes are redundant. If all are deep, at most two
cannot cover a tail; three can do so only when all have
height three and every cofactor query contains R-low.
NF48 would force all three numerical labels to be27.

In particular, a singleton root must be9, which occupies
its root alone in a minimal repair. In a different shallow
root let j>=2 distinct nonunit queries cover R-low. If

    kappa+j-1<=6,

at least TWO of their distinct parent labels3e must already
be lows. Otherwise at least j-1 parents are available;
promote those queries with their actual cofactor phases.
These are legal new low classes. The remaining nonunit
query contains the new remainder, contradicting NF48.
This conclusion is two occupied parents, not j-1 parents.

### One and two low classes cannot support a ten-class repair

Take an inclusion-minimal complete repair with ten classes.
Zero lows are excluded by BC1 and the independent N_3>=19
of NF51. If kappa=1, NF33 forces9 and root counts(1,4,4).
For each four-class root, kappa+t=5<8. NF52 requires a
shallow parent already among the lows. The two roots have
different shallow numerical labels and therefore require
two different low parents, contradicting kappa=1.

If kappa=2, NF33 forces9 and root counts(1,3,4). The
three-class root is shallow. Its three queries require at
least two occupied parent labels, so both lows are parents
of labels in that root. Every shallow label in the other
four-class root is numerically different; none of its parents
is low. But kappa+t=6<8, contradicting NF52. Consequently

    every inclusion-minimal ten-class complete repair
      has at least three low classes.                    (NF53)

No absence-of15 premise is used in NF52 or NF53.

### Three or four lows in a ten-class repair require fifteen

For kappa=3,h=7, at most one root is a singleton. Without9
the root counts must be(2,2,3), whose two pair roots already
demand four different low parents. With9 they are(1,3,3)
or(1,2,4). The two triple roots in the former again demand
four parents. Thus only(1,2,4) remains.

For kappa=4,h=6, the possible root counts are(2,2,2) or
(1,2,3). Three pair roots demand six low parents, excluding
the former. Both remaining cases have a shallow pair root.
Its two cofactors e,f have their parent labels3e,3f among
the lows. If the repair omits15, neither e nor f is5.

Use ONE such root. C0, the kappa low cofactor APs and its
two actual queries cover the whole cofactor carrier. Delete
all but one event at each repeated numerical modulus. The
deletion list has at most kappa+2<=6 items, multiplicity at
most two and at most two double values. Its only possible
double values are e and f. Numerical5 is absent: neither
query has that value, and without15 at most one event of
modulus5 occurs among C0 and the lows. A low label5, when
legal, means that C0 does not contain5.

Apply NF49 and the unchanged PC1--PC2 transport to these
actual deleted events. It gives a distinct odd nonunit whole
cover with at most |C0|+6<n classes, using NF51 for the
comparison. This contradicts minimum original cardinality.
Together with NF53 this proves

    an inclusion-minimal ten-class complete repair with
      at most four low classes must contain15.            (NF54)

Also kappa=6,h=4 is impossible: two roots are singletons,
and NF48 would require both to have numerical label9.
One or two high classes cannot cover all three second3 roots
of the nonempty low remainder. Thus a ten-class repair
omitting15 is either all low or has counts(5,5) or(7,3).
These are remaining possibilities, not constructed repairs.
The deductions in this section are ordinary mathematics;
no new Lean verification or literature-priority claim is made.

## 51. Disjoint query pairs exclude five-low ten-class repairs without fifteen

All numbers in this section are integers greater than one and coprime to six. A **strict certificate** for a labelled list is a selected increasing prime chain

$$
3<p_1<\cdots<p_t,
\qquad r_1=p_1-2,\qquad r_i=p_i-p_{i-1}+1\quad(i>1),
$$

and an assignment of every labelled item $m$ to a selected prime dividing it, such that

$$
\sum_{m\text{ assigned to }p_i}r_i^{-v_{p_i}(m)}<1
\quad\text{for every }i.
$$

Repeated values remain separate labelled events. The capacities, complete-prefix avoidance theorem and the common CRT transport are those already used in NF49. All bases are at least three. Assigning at most $r_i-1$ items to axis $i$ gives a strict cost. In particular, an assignment of at most two items per axis has cost at most $2/3$.

### A prime-chain observation

If two distinct core primes $p,q>5$ are selected together with at most one further prime, their two bases cannot both be three. A base three requires the immediately preceding selected prime to be two smaller. As neither core prime is five, these two predecessor requirements would need two different external primes unless one core prime were the predecessor of the other. In the latter case the one external prime and the two core primes would be three consecutive odd integers greater than three, all prime, which is impossible modulo three. Consequently at least one core base is at least five.

We use capacitated Hall in its existing form: a two-slot assignment fails only if some collection of items has fewer than half as many neighboring prime axes. For at most seven items, a failure is witnessed by at least three items supported on one prime, at least five supported on two primes, or all seven supported on three primes.

### Lemma: an obstructed repeated pair lies in a prime triangle

Let $E$ consist of five different values, with $5\notin E$. Let $Q\subset E$ have two elements and form the seven-item list $D=E\sqcup Q$. If $D$ has no strict certificate, then there are different primes $p,q$ such that

$$
\{p,q,pq\}\subset E,
\qquad Q\subset\{p,q,pq\}.
\tag{DP1}
$$

**Proof.** There are exactly two repeated values, each of multiplicity two.

First suppose at least three items are pure powers of one prime $p$, and collect all $k\ge3$ such items. Put them at $p$. Their conservative base-three cost is less than

$$
\frac12+\frac13+\frac19=\frac{17}{18}:
$$

the different powers have finite total cost below $1/2$, and the two possible extra copies occur at different depths. If $k\ge5$, assign the at most two other items to non-$p$ factors; each other axis receives cost at most $2/3$.

It remains that $k=3$ or $4$. Try a two-slot assignment of the other items to their non-$p$ factors. If it succeeds the proof is complete. Otherwise at least three of these at most four items have the same singleton support $\{q\}$ after $p$ is removed. Collect all such items as $T$, writing each as $p^u q^v$, $u\ge0$, $v\ge1$. There are either three or four items in $T$. When there are three, at most one further item has a factor outside $\{p,q\}$; when there are four, $k=3$ and there is no further item.

For three items in $T$, if any $v\ge2$, put all three at $q$, at cost at most $7/9$. Assume instead that all $v=1$.

* If the value $q$ is absent from $T$, all $u\ge1$. For $k=3$, a largest $u$ is at least two, since no value occurs three times. Move that item to $p$; its cost there is at most $7/9+1/9=8/9$. For $k=4$ with at most one repeated pure value, the initial pure cost is at most $22/27$, so the same move gives at most $25/27$. For $k=4$ with two repeated pure values, the three $T$ values are different and their largest $u$ is at least three; the cost at $p$ is at most $8/9+1/27=25/27$. Only two items remain at $q$.
* If $q$ occurs and $p=5$, absence of numerical five makes the pure $p$ cost at most $8/27$. Some $T$ item has $u>0$; moving it to $p$ gives at most $17/27$, and leaves cost at most $2/3$ at $q$.
* If $q$ occurs and $p\ne5$, then $p,q>5$. Select just these primes and, if needed, one outside factor $r$ of the possible remaining item. By the prime-chain observation, one core base is at least five. If it is the $q$ base, all three $T$ items cost at most $3/5$. If it is the $p$ base, the pure group costs at most $2/5+2/25=12/25$; move one $T$ item with $u>0$ there, giving at most $17/25$, and leave the other two at $q$. Assign the outside item to $r$.

Now let $|T|=4$, so the pure group has three items. Let $h$ count the $T$ items with $v=1$. If $h\le2$, all of $T$ costs at most $8/9$ at $q$.

If $h=3$ and $q$ is absent from those three items, their largest $u$ is at least two. Move that item to $p$; the costs are at most $8/9$ at $p$ and $7/9$ at $q$. If $q$ occurs, some other depth-one item has $u>0$. For $p=5$, the pure group costs at most $7/27$, and moving that mixed item adds at most $1/3$. For $p\ne5$, select only $p,q>5$. If the $q$ base is at least five, place all four $T$ items there, costing at most $4/5$. Otherwise the $p$ base is at least five; move the mixed item to $p$, giving at most $11/25+1/5=16/25$, while $q$ costs at most $7/9$.

Finally let $h=4$. If $q$ is absent and the pure group is numerically distinct, its cost is at most $13/27$. The two largest $u$ values in $T$ are at least two and two; moving these two items to $p$ gives at most $19/27$. If the pure group contains a repeated value, $T$ contains at most one repeated value, so its two largest $u$ values are at least two and three. Moving them gives at most $7/9+1/9+1/27=25/27$. If $q$ occurs, the two largest $u$ values are both positive. For $p=5$, move those two items: the $p$ cost is at most $7/27+2/3=25/27$. For $p\ne5$, use the actual two-prime chain. A $q$ base at least five takes all four items at cost at most $4/5$; a $p$ base at least five takes the two moved items with total cost at most $11/25+2/5=21/25$. The other axis receives only two items.

This eliminates every case with a pure group of size at least three.

Assume now every pure group has at most two items. If no pair of primes supports five items, the only possible two-slot Hall failure places all seven items on three primes. Select those three primes. Their actual integer capacities $r_i-1$ sum to the largest prime minus three, which is at least eight; singleton and pair demands are at most two and four. Hall therefore supplies a strict assignment.

It remains to collect all $g\ge5$ items supported on a pair $\{p,q\}$.

For $g=6$, at most one outside item remains. Select $p,q$ and one outside factor if needed. If one core base is at least five, the pair capacities sum to at least six, and singleton demands are at most two, so Hall assigns the six items. If both core bases equal three, the prime-chain observation forces one core prime to be five. Since numerical five is absent, the only squarefree values on this pair are the other prime and five times that prime. They account for at most four labelled items; reserve two items that have some depth at least two. Assign the remaining four with two slots per axis and restore the reservations to deep axes. Each core cost is at most $2/3+2/9=8/9$. Give the possible outside item to its chosen factor.

For $g=7$, select only the pair. If one base is at least five, reserve one deep item, assign the other six by Hall, and restore it to a deep axis. At a base $r$, restoration leaves cost at most $(r-1)/r+r^{-2}<1$. A deep item exists because seven labelled items of multiplicity at most two cannot all come from the three squarefree values. If both bases are three, the pair is $\{5,7\}$. There are only two available squarefree values, seven and thirty-five, whereas $E$ has five different values. Reserve three numerically different deep items. Assign the other four with two slots per axis. If the reserved items can be assigned to axes at which their depth is at least two with at most two reservations per axis, restore them at cost at most $2/9$ per axis. Otherwise all three have depth at least two only at the same axis. The other exponent is zero or one; three different values then force at least one exponent on the common deep axis to be at least three. Their total restoration cost is at most $2/9+1/27<1/3$. This is also strict after the previous $2/3$ load.

For $g=5$, choose a non-$p,q$ factor for each of the two outside items and select them together with $p,q$. The outside items cost at most $2/3$ on any outside axis. If a core base is at least five, Hall assigns all five internal items because the two capacities total at least six and singleton demands are at most two. If one internal item is deep, reserve it, assign the other four with two slots per axis, and restore it for at most $1/9$.

Thus failure requires all five internal items to be squarefree on $p,q$. They take the three values $p,q,pq$, each with multiplicity at most two; their multiplicities must be $(2,2,1)$ in some order. Both duplicated values of $D$ are therefore among these three values. This proves (DP1). Notice that $p,q>5$, because the numerical value five is absent. $\square$

### Theorem: two disjoint repeated pairs cannot both be obstructed

Under the same assumptions on $E$, let $Q_1,Q_2\subset E$ be disjoint two-element subsets. At least one of the two seven-item lists

$$
D_1=E\sqcup Q_1,
\qquad D_2=E\sqcup Q_2
\tag{NF55}
$$

has a strict certificate.

**Proof.** If both failed, the lemma would give two prime triangles $T_i=\{p_i,q_i,p_iq_i\}\subset E$ with $Q_i\subset T_i$. If the triangles were equal, their two-element subsets could not be disjoint. Different prime triangles can share at most one value, and any shared value must be a prime: a product of two different primes is not prime, and equality of two such products identifies their prime pairs. Since their union lies in the five-element set $E$, they share exactly one prime. Relabel to obtain

$$
E=\{p,q,pq,r,pr\},
\qquad T_1=\{p,q,pq\},
$$

where $p,q,r$ are different primes greater than five. Select just these three primes. The core bases at $p,q$ cannot both be three by the prime-chain observation. The five items of $D_1$ on $T_1$ have singleton demands at most two and fit its total integer capacity of at least six. The two remaining items, $r,pr$, are assigned to $r$ at cost at most $2/3$. This is a strict certificate for $D_1$, a contradiction. $\square$

The disjoint-pair hypothesis matters. A single seven-item list can fail even when numerical five is absent: $\{7,7,11,13,13,65,91\}$ has no strict certificate. Pure seven, eleven and thirteen force those primes into the chain. If five is omitted, the base at thirteen is at most three and both thirteen copies together with sixty-five cost at least one. If five is included, the bases at seven and thirteen are at most three; ninety-one cannot be assigned to either without reaching one. Additional unused primes only reduce these bases. This is a numerical assignment obstruction, not a family of covering phases.

### Consumer: a ten-class repair with five low and five high classes must contain fifteen

Use the same minimum hypothetical original distinct odd cover, complete private region $P_3$, retained three-free family $C_0$, unavailable numerical label three and enlarged common cofactor carrier as NF48--NF50. Suppose an inclusion-minimal legal complete repair has exactly five low and five high classes and omits numerical fifteen. Write $R_{\mathrm{low}}$ for the same actual cofactor remainder after its five lows.

The remainder is nonempty, or all high classes would be redundant. Every second-three root requires a high class. A singleton must have original three-height two and its cofactor AP must contain all of $R_{\mathrm{low}}$; by NF48, its cofactor is a unit, so its numerical label is nine. There cannot be two singletons because numerical moduli are distinct. Hence the root counts are $(1,2,2)$, with nine occupying the singleton root.

Both two-class roots are entirely shallow. Two deeper classes cannot cover a complete tail. A mixture of one shallow and one deeper class would make the shallow cofactor contain all of $R_{\mathrm{low}}$, so NF48 would force a second numerical nine. Thus the four high labels in these roots are

$$
9e_1,9e_2,9e_3,9e_4,
$$

where the $e_i>1$ are all different and coprime to six. Their actual cofactor APs form two pairs, each of whose union contains the same $R_{\mathrm{low}}$.

For every $i$, if numerical $3e_i$ were absent from the five low labels, promote that query to a low class, with the same complete cofactor phase and the repair's first-three root. CRT supplies its actual phase. The label is not three, cannot equal a retained three-free label or a high label, and by assumption is not an existing low label. The new six-low remainder would be confined to the other nonunit query in the same root, contrary to NF48. Therefore the four labels $3e_i$ are already four of the five lows. In particular $e_i\ne5$.

For either two-class root, take one actual cofactor cover consisting of $C_0$, the five low cofactor APs and the two query APs of that root. It covers the whole cofactor carrier and hence all integers by periodicity. At each repeated numerical modulus, select all but one actual event for deletion. There are at most seven deletion items. Their multiplicities are at most two, and at most the two query moduli can have two deletion items: before queries are added, a cofactor can have at most two events, because a retained $m\in C_0$ forbids repair label $m$, leaving only $3m$, while if $m\notin C_0$ only low labels $m,3m$ are possible.

Numerical five does not enter either deletion list. None of the four promoted-parent lows or either query has cofactor five. If the fifth low does, the absence of fifteen forces its numerical label to be five; legality then means $C_0$ contains no five, so that event is unique and is not deleted.

If either deletion list has at most six items, NF49 supplies a strict certificate. Otherwise both lists have seven items. Exactly seven events were added to $C_0$, so deletion count seven means no new numerical cofactor value was introduced. Hence all five low cofactor values already occur in $C_0$. Such a value $m$ forces its low label to be $3m$, so distinct original repair labels make the five cofactor values different. They form a five-element set $E$ with $5\notin E$. Each root's two query values are a two-element subset $Q_i\subset E$, and the four high numerical labels make $Q_1,Q_2$ disjoint. The two deletion lists are numerically exactly $E\sqcup Q_i$. The theorem above supplies a strict certificate for at least one.

Equivalently, if the fifth low repeats one of the first four cofactor values, the two low labels at that value must be $m,3m$, so $m\notin C_0$. This introduces at least one new numerical value and makes the deletion count at most six; it is already covered by NF49.

Use the successful certificate with the same complete-prefix avoidance and PC1--PC2 CRT map as NF49, taking every selected axis through its full actual height in the input whole cofactor cover. All deleted events have empty pullback. Every remaining event has at most one AP pullback, with all actual heights and complete phases retained; the output numerical moduli are distinct, odd and nonunit. Every output point inherits the same old covering witness through this single map. Consequently the output is a whole distinct odd cover of size at most

$$
|C_0|+7<n,
$$

using the independent earlier bound $N_3\ge9$. This contradicts minimum original cardinality. Thus a ten-class repair with five low and five high classes must contain numerical fifteen.

Only one of the two candidate cofactor covers is transported. The proof does not combine separately optimized phases, points or prime chains into a single source. Promotion checks numerical availability within the chosen complete repair; no additional globally unused label is assumed. Numerical fifteen itself is unique in the original distinct-modulus family, so two translated original branches cannot each require their own copy. The result leaves ten-class repairs containing fifteen, other ten-class splits and unrestricted Erdős #7 unresolved. All conclusions here are ordinary mathematical deductions; no new Lean verification is asserted.

Together with NF53--NF54 and the singleton exclusions in section50,
this leaves the exact necessary alternatives

    a complete ten-class repair omitting15 is either
      all low, or has seven low and three high classes.   (NF56)

Such a repair is automatically inclusion-minimal: any smaller
complete subfamily would still omit15, contrary to NF50.
NF56 does not claim that either remaining alternative is realizable.
In its all-low alternative, BC2 and NF45 require at least ten
different repeated bases. Each consumes a different low label3m,
so all ten lows are of this form and each m is retained in C0.
Thus this alternative also has no new cofactor prime or height.

## 52. The remaining three singleton roots force retained divisors and unit phase gaps

Consider the seven-low/three-high alternative of NF56. Each
second3 root has one high class. It must be shallow: a deeper
class cannot fill that root's complete tail at any point of
the nonempty R-low. Write the three different labels as9e_i.
Their actual cofactor APs A_i all contain the SAME R-low.
At most one e_i is1. Their intersection is a nonempty AP

    A = alpha mod K, K=lcm(e_1,e_2,e_3).

In particular K is composite: three distinct positive divisors
e_i cannot all divide1 or one prime. The following necessary
conditions concern this one actual intersection:

    the seven low labels are3m for a seven-element set
      E of different retained C0 labels, with5 not in E;
    every nonunit divisor d of K is a retained C0 label;
    d|K, d>1, d!=5 ==> d in E;
    if beta_d is the actual low cofactor phase at d,
      gcd(d,alpha-beta_d)=1 for each such d.               (NF57)

Consequently tau(K)<=8+1_(5 divides K), and every singleton
cofactor belongs to{1,5} union E. These are necessary label
and phase restrictions, not a construction of a repair.

### The seven low cofactors must already be retained labels

Fix any nonunit singleton query. C0, the seven low cofactor
APs and this query form one whole cofactor cover. Delete all
but one actual event at each repeated numerical modulus.
The deletion list has at most eight items, multiplicity at
most two and at most one double value, namely the query
modulus. These are the same multiplicity facts used in NF31.

If any newly added cofactor value were absent from C0, the
number of different moduli would increase by at least one,
so at most seven deletions would be needed. NF47 and the
same PC1--PC2 transport would give a distinct odd whole cover
with at most |C0|+8<n classes, contradicting NF51 and minimum
original cardinality. Hence all seven low cofactor values,
as well as this query's value, already occur in C0.

A retained cofactor m forbids low label m, leaving only3m.
Distinct low labels therefore give seven different cofactors
E. Absence of15 gives5 not in E. Repeating this argument
with any nonunit query containing R-low shows that its
numerical modulus must also occur in C0. In particular this
applies to every projection alpha mod d with d>1 dividing K.

### All non-five divisors are occupied, and their phase differences are units

For d|K with d>1 and d!=5, suppose3d were not a low label.
Add the actual query alpha mod d as a low repair with first3
root a_3. Its label is available: it differs from3, all C0
labels, all current lows and all height-two highs. Since it
contains R-low, the seven old lows plus this new low are a
complete eight-class repair omitting15. NF50 forbids it.
Thus d belongs to E. Counting these different occupied labels
gives tau(K)-1-1_(5 divides K)<=7.

Now remove the low with cofactor phase beta_d, keeping the
other six. Their remainder is contained in

    (alpha mod d) union (beta_d mod d):

any point outside the removed low was already in R-low and
therefore in A. If g=gcd(d,alpha-beta_d)>1, both APs lie
in the same nonunit AP alpha mod g. This would confine the
six-low remainder, contradicting NF48. Hence g=1, completing
NF57. The retained C0 phase at d also differs from alpha,
since its event is disjoint from R-low. Its phase differs
from beta_d as well, or that low class would be redundant.
These three phase distinctions belong to the actual common
source; they are not arbitrary independent choices.

### Eight numerical deletion items alone do not settle this case

The one-query proof cannot extend NF47 blindly to eight items
even when numerical5 is absent. For example,

    D={7,13,13,35,65,91,455,11}

has just one repeated value but no strict selected-chain
certificate. Pure7,11,13 force those axes. If5 is omitted,
the other seven items are squarefree on their available axes
7 and13. Their bases are at most5 and3, so their total strict
integer capacity is at most4+2=6. If5 is selected, the seven
core items use5,7,13 with bases at most3, giving capacity
2+2+2=6. Extra selected primes cannot receive these core
items or increase their bases. This is a counterexample to
the numerical assignment claim, not an odd covering family.

The seven distinct values in this example are compatible with
the forced divisor inclusion for K=91. That numerical fact
does not supply the actual phases, R-low, or a complete repair
required by NF57. The unit phase gaps and the complete common
intersection remain additional restrictions to use.

There is one further consequence for a hypothetical equality
N_3=19. NF28 and NF50 force its two non-parent branch counts
to be8 and10. The eight-class branch uses15 and21 by NF37,
so the other actual branch has neither label. If that branch
has seven lows and a singleton cofactor5, promoting its query
to15 and discarding the highs gives an eight-class repair.
NF37 requires21 in that repair. The only new label is15,
so21 must have been among the seven retained original lows,
contradicting global distinctness. Such a singleton is therefore
excluded in this equality case. This argument constrains the
retained original label21; it does not forbid new repairs from
using a label discarded from another original branch.

NF56--NF57 leave all-low ten-class repairs and the remaining
seven-low/three-high phase configurations unresolved. They do
not raise NF51's unconditional bound N_3>=19 or settle
unrestricted Erdős #7. The proofs are ordinary symbolic
deductions, not newly compiled Lean results.

## 53. Missing five and seven force ternary height one at nineteen labels

The proof uses the existing capacitated Hall theorem and strict-certificate transport. It is an ordinary mathematical deduction, without new Lean verification. Every integer below is greater than one and coprime to six. A list is labelled: repeated numerical values remain different events.

### Eight items with one duplicate

Let D be a list of at most eight items. Assume that at most one numerical value occurs twice, every other value occurs once, and neither numerical five nor numerical seven occurs. There is a selected increasing support-prime chain

    3 < p_1 < ... < p_t,
    r_1 = p_1-2,   r_i = p_i-p_(i-1)+1,

and an assignment of each event m to a selected dividing prime p_i, such that

    sum_(m assigned to p_i) r_i^(-v_(p_i)(m)) < 1

at every selected prime.                                      (NF58)

The exclusions concern the numerical values five and seven; those primes may occur in composite items.

### Reused assignment tools

Every selected base is at least three. Integer capacity r_i-1 at prime p_i guarantees a strict certificate. An assignment with at most two events per axis therefore costs at most 2/3. Reserving one or two deep events (an event at an axis with exponent at least two) and restoring them after an integer-capacity assignment also remains strict, since

    (r-1)/r + 2/r^2 < 1  for r>=3.

For a two-slot assignment of at most eight events, Hall can fail only through three events supported on one prime, five supported on two primes, or seven supported on three primes. Projecting away an already used prime gives the same criterion on the remaining prime supports.

Two chain observations will be used.

1. Two core primes greater than five, selected together with at most one external prime, cannot both have base three. Otherwise the two predecessor requirements either need two different external primes or form three consecutive odd numbers above three, all prime. Thus if two core bases are three in such a chain, one core prime is five.
2. Three core primes, selected together with at most one external prime, can all have base three only if the core contains both five and seven. With at most three selected primes, three bases of three would force 5,7,9. With four selected primes, base three cannot occur simultaneously at neighboring positions j,j+1 with j>=2 (three consecutive odd primes above three are impossible). Three marked positions must consequently be positions 1,2,4; the first two core primes are 5 and7.

For a chain of exactly three primes, the total integer capacity telescopes to max(p,q,r)-3>=8. Its bases cannot all be three, so at most one pair has total capacity four; all other pairs have capacity at least six.

#### Deep reservations on two axes

Any set of at most four numerically distinct deep values supported on two primes can be assigned to axes at which their exponents are at least two, with added cost strictly below 1/3 on each axis, using conservative base three.

If at most two values can be assigned to each axis, the added costs are at most 2/9. Otherwise at least three of the values have only the same available deep axis. The exponent on the other prime is then zero or one. At most two different values can have exponent exactly two on the forced deep axis. Thus three forced values cost at most 2/9+1/27=7/27; four forced values cost at most 2/9+2/27=8/27. When exactly three are forced, the possible fourth value can be put on the other axis unless it is forced too. This proves the lemma.

#### Eight items on two primes

Every list of eight items, with at most one value occurring twice and every other value occurring once, supported on at most two primes, has a strict base-three certificate; no missing-value assumption is needed here.

If at least six events are pure powers of one prime, put all of them on that prime. Distinct powers have finite total cost below 1/2; one extra copy adds at most 1/3. Thus their cost is below 5/6. Assign the at most two remaining events to the other prime. The one-prime case is included.

Otherwise each pure group has at most five events. The list has at least seven distinct values and at most three squarefree values, so it contains at least four different deep values. Reserve four different deep values, choosing enough pure values that each remaining pure group has at most two events. This is possible: a pure group of k>2 events has at least k-2 distinct deep pure values, and the combined reservation requirement is at most four. Complete those required reservations to four different deep values. The remaining four events satisfy two-slot Hall. Restore the four reservations by the deep reservation lemma. Each cost remains below 2/3+1/3=1.

### Eight-item proof

For at most seven items, use NF47. For eight different values, use NF44. It is therefore enough to treat exactly eight items, of which one value is repeated twice and the other six occur once.

#### Case A: a pure group has at least three events

Collect all k>=3 pure powers of p. Their total conservative base-three cost is below 5/6, and below 1/2 if they are distinct. If k>=6, assign the at most two other events to non-p factors.

Let 3<=k<=5. Try a two-slot assignment of all remaining events to their factors other than p. If it exists, combine it with the pure group.

First suppose some projected singleton {q} supports at least three remaining events. Collect all such events as T. Each has the form p^u*q^v with u>=0 and v>=1. Its size t is 3,4 or5. If t=5, then k=3 and the whole list is supported on p,q, so use the two-prime lemma. Otherwise at most two events lie outside the pure group and T; each has a factor outside p,q, to which it may be assigned.

If t=3 and at least one q exponent is at least two, put all three T events at q, at cost at most 7/9. If all three q exponents are one, move one T event with positive p exponent to p and leave two at q. If the pure group has the repeated value, all T values are different, so the largest p exponent is at least two; the p cost is below 5/6+1/9=17/18. If the pure group is distinct, some p exponent is positive because three equal q events are forbidden; the p cost is below 1/2+1/3=5/6.

If t=4, necessarily k<=4. Let h be the number of T events with q exponent one. For h<=2, all four cost at most 8/9 at q. For h=3, move one of these three as in the previous paragraph; the remaining q cost is at most 7/9. For h=4, move two T events to p and leave two at q. If the pure group contains the repeated value, the four T values are different; their two largest p exponents are at least two and three. The pure group costs at most 22/27, so the new p cost is at most 22/27+1/9+1/27=26/27. If the pure group is distinct, T has at most one repeated value; its two largest p exponents are at least one and two. The p cost is below 1/2+1/3+1/9=17/18. This resolves every projected-singleton failure.

Now assume every projected singleton has at most two events. A projected Hall failure must consist of five remaining events supported on a pair {q,r}. Hence k=3 and the entire list is supported on p,q,r. Reserve one deep pure-p event, which exists because no value has multiplicity three. Select exactly these three primes. Among the remaining seven events, singleton demands are at most two; a pair containing p has demand at most four, since only two pure-p events remain and the projected singleton demand is at most two. The only possible Hall failure at actual capacities is five p-free events on {q,r} with both their bases equal to three.

If that failure does not occur, Hall assigns the remaining seven with actual capacities and the deep pure-p reservation can be restored. If it occurs, the first chain observation forces the pair {q,r} to contain five. Missing numerical five means only the other prime and the product of the two primes are available squarefree values on this pair. They account for at most three labelled events, so among the five p-free events there is a deep event. Reserve one such event as well. The remaining six satisfy two-slot Hall: every singleton has demand at most two and every pair at most four. Restore the pure-p event at p and the other reservation at q or r. The two restorations use different axes and add at most 1/9 each. This finishes Case A, including the five-event projected-pair failure.

#### Case B: every pure group has at most two events

Suppose some pair supports at least five events. Let g be the maximum number of events supported on any pair, choose a maximizing pair {p,q}, and collect all its g events.

For g=8, use the two-prime lemma.

For g=7, choose one outside factor r of the remaining event and select p,q,r. If one core base is at least five, reserve one deep internal event (there are at least six distinct internal values but only three squarefree values). The remaining six internal events fit the pair's actual capacities, whose sum is at least six and whose singleton demands are at most two. Restore the deep reservation and put the outside event at r. If both core bases are three, the first chain observation forces one core prime to be five. The absence of numerical five leaves at most two squarefree values, so there are at least four distinct deep internal values. Reserve three of them, assign the remaining four internally with two slots each, and restore using the deep reservation lemma. Put the outside event at r.

For g=6, at least two internal events are deep: three squarefree values and at most one extra copy account for at most four events. Reserve any two deep events, assign the other four internally with two slots each, and restore the reservations at cost at most 2/9 per axis. Assign each of the two outside events to a factor outside p,q. Every outside axis receives at most two events.

For g=5, at least one internal event is deep. Reserve it and assign the other four internally with two slots each. If the three outside events admit a two-slot assignment on their non-p,q factors, use it and restore the reservation. Otherwise all three outside events have the same singleton projected support {r}. The whole list is supported on p,q,r. Select these three primes and use their actual capacities. Their sum is at least eight. Every singleton demand is at most two, every pair demand is at most five, and at most one pair has capacity four. If that pair has demand at most four, Hall assigns the entire list. If it has demand five, its two bases are three and the first chain observation forces it to contain five. Missing numerical five implies that one of its five events is deep. Reserve one such event, assign the other seven by actual-capacity Hall, and restore it. All pairs of capacity at least six meet their demand bound five. This finishes every g>=5 case.

It remains that each pair supports at most four events. A two-slot Hall failure now puts seven or eight events on three primes. If all eight are supported on a triple, select just that triple. Its actual capacity sum is at least eight; singleton and pair demands are at most two and four, so Hall gives the assignment.

Otherwise choose a triple supporting seven events and one outside factor of the eighth event. Select these four primes. If at least one of the three core bases is at least five, the core's capacities total at least eight; singleton and pair demands are at most two and four, so the seven core events fit. Assign the outside event to its outside factor.

If all three core bases are three, the second chain observation shows that the core contains both five and seven. Three primes have seven nonempty squarefree products; excluding numerical five and seven leaves only five squarefree values, and one repeated value accounts for at most six labelled squarefree events. Thus one of the seven core events is deep. Reserve it, assign the other six core events with two slots each, restore the deep event for at most 1/9, and assign the outside event separately. All costs are strict. This completes the proof.

### A remaining high ten-class repair requires twenty-one

Use exactly the actual-source setup and legal label restrictions of NF57. Assume a complete repair with seven low and three high classes omits numerical fifteen. Its seven low cofactors form a seven-element retained set E inside C_0, with numerical five absent, and all low labels are 3m for m in E. Its three singleton high roots have distinct labels 9e_1,9e_2,9e_3 and actual cofactor APs containing the same nonempty low remainder.

Suppose twenty-one is also absent. Then seven is absent from E. Since the three e_i are different, at least one satisfies e_i>1 and e_i!=5. NF57 forces this e_i into E. The actual cofactor cover C_0 plus the seven low cofactor events plus this singleton query has exactly the deletion list E disjoint-union {e_i}: eight labelled values, one repeated, with numerical five and seven absent.

The theorem supplies a strict certificate. Apply the existing complete-prefix avoidance and one PC1--PC2 CRT transport to this one actual cover. Deleted events have empty pullback; every retained event has at most one AP pullback; all complete heights, phases and actual source witnesses remain as required in NF49/NF57. The result is a whole distinct odd cover with at most |C_0|+8 members, smaller than the original minimum cover because the independent earlier N_3 bound exceeds eight. Contradiction.

Therefore

    a ten-class repair with seven lows and three highs
      which omits15 must contain21.                      (NF59)
 In the actual N_3=19 branch split 8+10, the eight-class branch already requires both fifteen and twenty-one. Global numerical distinctness makes the other original branch omit both; consequently its (7,3) ten-class case is excluded. This does not exclude the all-low ten-class case and does not establish an unconditional N_3>=20.


### Equality in the nineteen-label bound has ternary height one

If N_3=19, NF28 and NF50 force the two non-parent original
first3 branches to have8 and10 labels. NF37 requires both15
and21 in the eight-class branch. The other actual branch
therefore omits both labels. NF56 leaves ten lows or the
seven-low/three-high split; NF59 excludes the latter.
The eight-class branch is already all low by NF34. NF19's
translations preserve the numerical labels and their heights,
so every original3-bearing label in either non-parent branch
has3-height one. Including the original prime3 class gives

    N_3=19 ==> v_3(d)<=1 for every original modulus d;
    an original modulus divisible by9 ==> N_3>=20.        (NF60)

This is a height-sensitive consequence, not an unconditional
increase of NF51. The all-low ten-class repair still has ten
different retained cofactor labels excluding5 and7 in this
equality case. Its actual phases and the unrestricted larger
inventories remain unresolved, as does Erdős #7.

## 54. Common-source exchanges and divisor closure restrict the nineteen-label case

Use the actual minimum hypothetical original cover with N_3=19.
By NF60 its two non-parent first-three branches are all low, with
eight and ten classes. Write their cofactor sets as

    E={5,7,s,35,5s,7s,35s,u^a},
    u=s-2, a>=1, s>=13, with u and s prime,
    |F|=10, E intersect F empty.

Every value in E and F is a retained C0 label: original divisor
closure puts the three-free divisor m of each original label 3m
into the original palette, hence into C0.

Let R=R_3 be the nonempty actual cofactor remainder outside C0,
and let A_m for m in E and B_n for n in F be the corresponding
actual repair APs. Both families cover R. All events live on one
common finite carrier retaining every original height and phase.
When combining the two repairs on P_3, lift their APs to the same
required first-three root by CRT. The labels are 3m and 3n,
pairwise different, different from three, and absent from
the retained three-free labels C0. A label from a discarded
original branch is not permanently forbidden.

### Retaining the separator fixes an eight-class numerical template

Put G=E without {u^a}. Any complete eight-class repair retaining
3u^a must have precisely cofactor set E. By NF37 its set has form

    {5,7,t,35,5t,7t,35t,(t-2)^b},
    t>=13, with t and t-2 prime, b>=1.

If a>=2, the nonsquarefree u^a must equal the separator (t-2)^b.
Unique factorization gives t=s and b=a. If a=1, the prime u>=11
could only be t or the separator. The first possibility would
require u-2,u,u+2=s all prime greater than three, impossible
modulo three. Again t=s and b=a. This fixes numerical labels,
not the AP phases.

For nonempty J contained in G define the exact joint obligation

    Q_J = R minus union_(m in E without J) A_m.

If actual F events indexed by I cover Q_J, keeping E without J
and adding I gives a legal complete repair of size 8-|J|+|I|.
NF28 forbids fewer than eight. Equality would retain u^a and
therefore force all of E, impossible because I is disjoint from E
and J is nonempty. If five belongs to J, the hybrid omits fifteen,
so NF50 forbids nine classes as well. Consequently

    Q_J contained in union_(n in I) B_n ==>
      |I|>=|J|+1;
    if also 5 in J, then |I|>=|J|+2.                     (NF61)

These are restrictions on entire actual regions, not on separately
chosen sample witnesses. In particular Q_{ {5} } cannot be covered
by two F events; no other core private region can be covered by one.

For each p in {5,7,s}, its four-element core star is

    S_5={5,35,5s,35s}, S_7={7,35,7s,35s},
    S_s={s,5s,7s,35s}.

NF42 makes the repair APs in each star pairwise disjoint. Hence for
J contained in one star,

    Q_J = union_(m in J) Q_{ {m} }.

Indeed, a point in Q_J belongs to at least one removed A_m because
E covers R, and to at most one because those APs are disjoint. It
belongs to no retained event, and so is private to that removed A_m.
This identity is not claimed for arbitrary overlapping subfamilies.

Join m in a star to n in F exactly when Q_{ {m} } meets B_n.
The neighbors of J cover Q_J, so NF61 gives their cardinality
bounds. Reusing capacitated Hall with demand three at five and
one at each other member of S_5 gives six distinct F labels:
three meet Q_{ {5} }, and one meets each of Q_{ {35} },
Q_{ {5s} }, Q_{ {35s} }. Either other star admits five distinct
labels, with two meeting any one chosen private region and one
meeting each of the other three. These separate matchings are not
combined into one independent family. Each matching edge has an
actual witness in R, and in particular its full phases satisfy

    beta_m = gamma_n modulo gcd(m,n).

CRT compatibility alone does not supply that witness in R.

### The ten cofactor values have greatest common divisor one

The original numerical palette is divisor-closed. Its complete
three-bearing part is {3} together with 3(E union F). Thus

    m in E union F, d>1, d divides m ==> d in E union F.

This uses the actual original split: the original label 3d divides
3m and must occur. Two arbitrary replacement families need not
have this property.

Any strict selected-chain certificate for the ten different values
F contradicts minimum original cardinality. Apply complete-prefix
avoidance and ONE PC1--PC2 transport to the actual whole cofactor
cover C0 together with the ten F repair APs, deleting one endpoint
at each repeated modulus. It produces a distinct odd whole cover
with at most |C0|+10 members, fewer than the original |C0|+19.
The argument retains the full actual phases and heights.

Suppose a prime p divides every F value. All values are coprime to
six, so p>=5. The following cases give strict certificates, with
the bases defined in section53.

For p=5, divisor closure of u^a forces u into E union F. Since u
is five-free, it lies in E, which forces a=1. Write each F value
as 5^k n with k>=1 and five not dividing n. Its five-free part
lies in {1,7,s,7s,u}. For the first four types k>=2, since their
depth-one values are already in E. Assign these items to five;
at conservative base three their total cost is bounded by

    4 sum_(k>=2) 3^(-k)=2/3<1.

If a u-type occurs, let K be its maximum five-depth. Divisor
closure forces the K values 5u,...,5^K u and the K-1 values
5^2,...,5^K into F. They are distinct, so 2K-1<=10 and K<=5.
Select the chain 3<5<u and assign the u-types to u, whose base
is u-4>=7. Their cost is at most 5/7<1. If no u-type occurs,
the single selected prime five already suffices.

For p=7, the seven-free part of every F value belongs to
{1,5,s,5s,u^a}. For the first four types, seven-depth one is
excluded because 7,35,7s,35s already belong to E. Thus at most
one of the ten items has seven-depth one; all others have depth
at least two. Select only seven, whose base is five. Its cost
is at most

    1/5+9/25=14/25<1.

For p=11, each depth-one value is 11n with eleven not dividing n.
Divisor closure puts n in {1} union E, so there are at most nine
such distinct values. If at least two items are deeper, select
only eleven, with base nine and cost at most

    8/9+2/81=74/81<1.

There cannot be ten depth-one items. If there is exactly one deep
item, all nine possible depth-one choices must occur. This forces
all of E to be eleven-free, and in particular 11s belongs to F.
Select 3<11<s and assign 11s to s; assign every other value to
eleven. The loads are at most 1/(s-10)<1 and 8/9+1/81=73/81<1.

For p>=13, select p alone. The ten values have cost at most
10/(p-2)<=10/11<1. These cases exhaust all possible common
prime factors. Therefore

    gcd(F)=1.                                           (NF62)

### The original three-bearing palette has bounded prime heights

Reuse the pure-group argument in section48 with the following
interface extension: any finite set of different nonunit values
coprime to six, consisting of a nonempty pure-p-power group and
at most six non-pure-p items, has a strict certificate.

The proof there assigns the pure group total conservative cost
strictly below 1/2 regardless of its finite cardinality. All its
projected singleton and pair cases depend only on the at most
six other items. The only estimate using exactly three pure
items is the case of three projected q items and three outside
items. Replace its pure-group bound 13/27 by the strict bound
1/2. The sharper assignment moves at most one q item to p at
depth at least two, and at most one outside item at depth at
least one. Its total p cost is then strictly below

    1/2+1/9+1/3=17/18<1.

If the outside item instead goes to q, the existing q bound 8/9
is unchanged. The six-on-two-projected-axes case uses the same
capacities R_p-2,R_q-1,R_r-1 and the same inequality

    1/(R_p-1)+(R_p-2)/R_p<1.

Both uses of NF17 involve only five or six different p-free items
and retain its conservative-base guarantee. Thus the existing
proof extends to every finite pure group without a missing-value
assumption; no other assignment theorem is reproved here.

If F contained four different pure powers of any prime p, at
most six other values would remain. The extended pure-group
argument would give a strict certificate, contradicting the
actual transport above. Hence F contains at most three distinct
pure powers on each prime axis.

E supplies exactly one pure power at each of 5,7,s,u and none
at other primes. For m in E union F, divisor closure puts all
p,p^2,...,p^{v_p(m)} in this union. Counting these different pure
powers gives

    m in E union F ==>
      v_p(m)<=4 for p in {5,7,s,u},
      v_p(m)<=3 for every other prime;
    in particular 1<=a<=4.                              (NF63)

Every original three-bearing label in the N_3=19 case is three
or 3m for m in E union F. Thus NF63 bounds all its non-three
prime heights. It places no height bound on retained C0 labels
outside E union F. The prime s, other support primes, remaining
retained labels and their actual common-source coverage are
still unrestricted. NF61--NF63 do not exclude the whole all-low
eight-plus-ten case, increase the unconditional bound N_3>=19,
or settle Erdős #7. These are ordinary mathematical deductions,
not newly compiled Lean results.

## 55. Ten distinct collision values have one complete obstruction pattern

Use the strict selected-chain certificates defined in section53. All
values below are distinct nonunit integers coprime to six. The following
classification allows arbitrary support primes and exponents.

Let D have ten different values and omit numerical5 and7. It has no
strict selected-chain certificate if and only if

    D = {all seven nonempty squarefree products of q_1,q_2,q_3}
          union {p_1^b_1,p_2^b_2,p_3^b_3},
    p_i=q_i-2, b_i>=1,

where all p_i,q_i are primes, q_i>=13, and the six primes are different.
                                                        (NF64)

The proof reuses NF39's two-axis envelopes, NF44, NF58's small
reservations and conservative two-prime lemma, and NF63's pure-group
extension. The pair and triple cases below are considered after the
pure-group case has restricted every axis to at most two pure powers.
These are ordinary mathematical deductions, not new Lean verification.

### Reused bounds and chain facts

All selected bases are at least three. At most r-1 assigned items give
load at most (r-1)/r. One or two reserved deep items (exponent at least
two on the chosen receiving axis) may be restored, because

    (r-1)/r + 2/r^2 < 1  for r>=3.

NF58's two-prime lemma works at conservative base three for at most
eight items with at most one numerical duplicate. Shorter lists may
be padded by fresh high pure powers on the same axes and then restricted
back. Projecting one actual item onto two axes introduces at most one
duplicate, while preserving its exponents at the receiving axis.

NF39's two-axis infinite envelopes remain available: if either axis's
actual base is at least five, both loads can be made strict. If both
bases are three and the numerical pure value on one axis is absent,
put equal-exponent mixed values on that axis; the two loads are at most
11/12 and3/4. The latter fact uses absence of the pure value itself,
not absence of that prime from all items.

For a chain of three primes, integer capacities sum to the largest
prime minus3, hence at least8. At most one pair has capacity4; the other
pairs have capacity at least6. For a chain of four primes, total capacity
is at least10. A triple has capacity6 only when its three bases are3.
At most three bases can be3 in a chain of four or five primes: two
neighboring positions j,j+1 with j>=2 cannot both have base3, since
that would require three consecutive odd primes greater than3.

Three core primes selected with at most one external prime can all
have base3 only if the core contains5 and7. Three core primes selected
with at most two external primes can all have base3 only if the core
contains5. For the latter claim, if5 is absent from the core, every
core prime needs its predecessor two smaller to be external. A core
predecessor would itself need a prime predecessor and form the same
impossible triple. Three different external predecessors would then
be required.

The two-slot Hall obstructions for ten items are: at least3 on one
prime, at least5 on a pair, at least7 on a triple, or at least9 on four
primes. Actual integer capacities will be used whenever two-slot Hall
is insufficient.

### At least three pure powers permit a certificate

Four or more pure items are already covered by the verified extension
of Report385 section48: an arbitrary finite distinct pure group plus
at most six other items has a strict certificate. It remains to treat
exactly three pure-p items and seven non-pure-p items. At conservative
base three the pure group costs at most 13/27, and at an actual base R
it costs less than 1/(R-1).

#### Reused small two-axis certificate

NF58's two-prime lemma gives a certificate at conservative base three
for eight items supported on two primes, with at most one value doubled
and every other value occurring once. It also applies to any shorter
such list: append unused sufficiently high pure powers to make eight
items, apply the lemma, and discard the appended items. No new selected
prime is introduced. This argument will be used on projected values;
their exponents on the two surviving axes are their actual original
exponents, so its assignment pulls back to the original items.

The following recurring subcase is therefore closed. Seven non-pure-p
items are supported on {p,q,r}, and at least five are p-free:

* With seven p-free items, apply the small two-axis certificate to all
  seven on q,r and leave the pure group at p.
* With six p-free items, put the remaining p-bearing item at p and use
  NF17 or the small two-axis certificate on the other six.
* With five p-free items, put one of the two p-bearing items at p.
  Remove the p factor from the other one and combine its q,r projection
  with the five p-free values. This six-item list has at most one double
  value, so the small two-axis certificate applies.

The p cost in the latter two cases is at most 13/27+1/3=22/27. All
other costs are strict at conservative base three. Call this the
five-p-free subcase.

#### Project away p and first treat projected singleton groups

Try to assign the seven remaining items on their factors other than p
with capacity two per prime. If successful, combine that assignment
with the pure-p group. Suppose first that a projected singleton supports
at least three items. Choose one with maximum count and call it q.
Collect ALL its items as T. They are different values p^u q^v, u>=0,
v>=1; write t=|T|, so 3<=t<=7. Every outside item has a factor outside
{p,q}.

If t=7, all ten items have support on p,q. NF39 applies because numerical
five and seven are absent. If t=5 or6, use the existing section48
assignment: move to p every T item with u>=2 and v=1 or2. Their added
cost is less than 1/3, while q receives at most two depth-one items,
two depth-two items and at most two further items of depth at least
three. The loads are less than 22/27 at p and at most 26/27 at q.
At most two outside items remain and are assigned to outside factors.

##### Four items in T and three outside

Let h count the T items with q-depth one. If h<=2, put all four at q;
the q cost is at most 8/9 and p remains at most 13/27. If h=3, the
three corresponding p-depths are different, so one is at least two.
Move that item to p. The costs are at most 16/27 at p and 7/9 at q.
If h=4, the two largest p-depths are at least two and three. Move those
two to p, yielding at most 17/27 at p and 2/3 at q.

If the outside items admit capacity two on their outside factors, use
that assignment. Otherwise their outside supports are all the same
singleton {r}. They have the form p^a q^b r^c, c>=1.

If their r-depths are not all one, place all three at r, costing at
most 7/9. If all are one and some item has a p factor, place that item
at p, whose cost is at most 17/27+1/3=26/27; the other two go to r.

If all are r-shallow and none has a p factor, they are three different
values q^b r. One has b>=2. Place that item at q and the other two at r.
This is strict whenever the earlier q load is less than 8/9. Equality
8/9 requires exactly two T items of q-depth one and two of q-depth two.
One of these four items has a positive p-depth, since values at each
fixed q-depth are distinct. Move such an item to p instead. This adds
at most 1/3 to its unchanged pure-group load 13/27, and removes at least
1/9 from q before the outside item adds at most 1/9. The q load remains
at most 8/9 and the p load is at most 22/27.

##### Three items in T and four outside

Use the sharper existing T assignment. If some q-depth is at least two,
put all three at q, costing at most 7/9. Otherwise their different
p-depths include one at least two; move it to p, yielding at most
16/27 at p and 2/3 at q.

If the four outside items admit capacity two on their outside factors,
we are done. Otherwise collect all l>=3 items with the same singleton
outside support {r}. If l=3, the fourth outside item has a factor
outside {p,q,r}. The existing section48 three-plus-three argument
applies to T and these three r-items: either all go to r with load
at most 7/9, or one p-bearing item goes to p with load at most 25/27,
or a p-free item of q-depth at least two goes to q with load at most
8/9. Assign the fourth item to its external factor.

It remains l=4, when the whole list is supported on p,q,r. The maximal
choice t=3 means at most three non-pure-p items have projected support
{r}. In particular, at most three of the four r-items are q-free.

If all three T items are pure q-powers, assign them to q at cost less
than 1/2. The p group also costs less than 1/2. Deal with the four
r-items as follows. With at most two r-shallow items, all four fit at
r with load at most 8/9. With three r-shallow items, move any one of
them with a p or q factor to that axis; such an item exists by
distinctness, and its cost at most 1/3 fits above the pure group.
With four r-shallow items, at least three quotients after removing r
are nonunits. If two of these quotients can be assigned to different
axes p,q, do so at cost at most 1/3 on each axis. Otherwise all nonunit
quotients are powers of one axis; the two largest distinct exponents
are at least two and three. Move those two there at total cost at most
4/27. In each case at most two r-shallow items remain at r.

If instead at least three of the four r-items are pure r-powers, put
all four at r: the pure subgroup costs less than 1/2, and any single
remaining item adds at most 1/3. Use the sharper T assignment above.

Now suppose both the pure-q and pure-r counts are at most two. Select
exactly p,q,r, and use capacities

    c_p=R_p-2, c_q=R_q-1, c_r=R_r-1

for the seven non-pure-p items. Their total capacity is max(p,q,r)-4,
which is at least seven. Every singleton demand fits. The {p,q} demand
is t=3 and the {p,r} demand is at most three by maximality of T; their
capacities are at least three. Only {q,r} can fail Hall, which requires
at least five p-free items. That subcase was closed above. Otherwise
Hall applies, and the pure-group envelope combines strictly with c_p.
This finishes every projected singleton case.

#### No projected singleton has three items

A capacity-two failure now places at least five projected items on a
pair {q,r}, or all seven on a triple. Collect ALL items on a chosen
projected pair and write g for their number.

If g=5, at most two other items remain and have factors outside
{p,q,r}. If an internal item has a p factor, move one such item to p;
the remaining four fit capacity two on q,r because projected singleton
demands are at most two. If all five are p-free, use NF17. Assign the
outside items to their outside factors.

If g=6, at most one outside item remains. If at least five of the six
internal items are p-free, either all six are assigned by NF17 or the
single p-bearing item goes to p and the other five use NF17. Suppose
at most four are p-free. If any internal item is deep on p,q or r,
reserve it. The other five fit conservative capacities one at p and
two each at q,r: singleton demands fit, pairs containing p have demand
at most two by the projected-singleton assumption, and {q,r} demand
is at most four. Restoring the deep item costs at most 1/9. At p the
load is at most 13/27+1/3+1/9=25/27, and the other axes cost at most
7/9. Assign the outside item to an outside factor.

If all six internal items are squarefree, they must be exactly

    q,r,pq,pr,qr,pqr.

Select p,q,r and, if present, one outside factor of the seventh item.
The three core bases cannot all be three: the triple-plus-one-external
prime-chain observation would force both five and seven into the core.
But q and r occur as numerical items and so are neither five nor seven;
at most p could be one of them. Some core base is therefore at least
five. The actual capacities R_p-2,R_q-1,R_r-1 total at least seven;
singleton and pair demands fit as above. Apply Hall to the six internal
items and assign the outside item separately.

If g=7, select exactly p,q,r and use the same actual capacities. They
total at least seven. Singleton demands and pairs containing p fit by
the projected-singleton assumption. A failure on {q,r} gives at least
five p-free items, already closed by the recurring subcase. Otherwise
Hall applies directly.

Finally suppose no projected pair supports five items. A projected
Hall obstruction then places all seven non-pure-p items on three primes
U={q,r,t}. If any of those seven has a p factor, put that item at p;
the other six fit capacity two on U, since singleton and pair demands
are at most two and four. If none has a p factor, select U together
with p. If some U base is at least five, its total integer capacity is
at least eight and Hall assigns the seven U items. If all U bases are
three, the prime-chain observation forces five and seven into U.
Because their numerical values are absent, at most five different
squarefree values on U are available. Some of the seven items is deep.
Reserve one, assign the other six with capacity two and restore it for
at most 1/9. Leave the pure-p group at p in all these cases.

Every pure-group case therefore has a strict certificate.

### Auxiliary: nine items on a triple with two pure values absent

Let U={5,7,s} be a prime triple. Suppose nine different U-supported
values omit numerical5 and7, with pure demands at most2 and pair
demands at most5. They have a strict certificate even at conservative
base3 on all three axes.

There are at most five squarefree values, so at least four items are
deep. Call a pair critical if it supports five items. Removing at least
one deep item from each critical pair, and three items in total, leaves
six items satisfying two-slot Hall.

If all three pairs are critical, their total demand is15. If P is the
number of pure items, counting within the triple gives at most9+P<=15.
Equality forces exactly two pure items at each prime and one mixed
item on each pair, with no triple-supported item. Reserve one deep pure
power on each axis; these exist because each pure group has two distinct
values. The remaining six fit and the restoration loads are at most1/9
per axis.

Otherwise there are at most two critical pairs. Choose one deep item
in each; such items exist because a pair has only three squarefree
values. Complete these choices to three different deep reservations.
If not all available deep items are forced to the same receiving axis,
these three can be chosen and assigned so that no axis receives three:
only two reservations are needed to hit the critical pairs, leaving a
choice of a reservation with another available deep axis. The restoration
load is then at most2/9 per axis.

If all deep items have only one deep axis t, but some such item has
t-depth at least3, include it among the three reservations. The two
critical-pair obligations can still be met by the other two choices.
The total restored load is at most2/9+1/27<1/3 on t.

The remaining exceptional shape has every deep item forced to t at
exact depth2. Its other two exponents are zero or one, so there are at
most four such different items. There are therefore exactly four, and
the other five are exactly

    s,35,5s,7s,35s.

Assign all four deep items to t, at cost4/9. The five squarefree items
fit integer capacities one at t and two at the other axes: singleton
demand is at most one, any pair has at most two such items, and total
capacity is five. This gives load at most7/9 at t and2/3 elsewhere.
Every case is strict, proving the auxiliary lemma.

### A pair containing five or more items always permits a certificate

Let g>=5 be the maximum number of D items supported on any pair, and
choose a maximizing pair {p,q}. All g internal items have full support
there; every other item has a factor outside {p,q}.

For g=9 or10, select p,q and, if necessary, one outside factor. If one
core base is at least five, apply NF39's infinite pair envelopes. If
both core bases are three, the two-core-plus-one-external chain fact
forces one core prime to be five, whose numerical pure value is absent;
use the conservative11/12,3/4 envelopes. Put the possible outside item
at its selected outside factor.

For g=8, use NF58's conservative pair lemma internally and assign the
two outside items to outside factors, at cost at most2/3 per axis.

For g=7, the same internal lemma works whenever the three outside items
admit a two-slot assignment on outside factors. Otherwise all three
outside projected supports equal {r}. If all three are pure r-powers,
they cost less than1/2 at r. Otherwise project one outside item with a
nonunit p,q-part onto p,q. Together with the seven internal values this
is an eight-item list with at most one duplicate; NF58's pair lemma
assigns it at base3. Pull that projected assignment back to the actual
item, and put the other two outside items at r.

For g=6, four outside items remain. If outside two-slot Hall fails,
collect all t>=3 items whose projected support is the same singleton
{r}; t is3 or4. For t=3, use the previous projection trick on one of
these three non-pure-r items, producing seven pair items with at most
one duplicate; the two others go to r. If all three are pure r-powers,
put them all at r. The fourth outside item has a factor outside p,q,r.
For t=4 the whole list is supported on p,q,r. Their actual total capacity
is at least8, and every pair demand is at most6 by maximality of g.
Reserve two deep items, choosing enough from the only possible
capacity-four pair to bring its demand down to4. This is possible:
a pair with demand5 or6 has at least two or three deep values. If that
pair needs no reduction, there are at least three deep items globally,
since a triple has only seven squarefree values. The remaining eight
satisfy actual-capacity Hall; restore the two deep items. If outside
Hall did not fail in the first place, use the internal conservative
pair lemma and the outside assignment.

It remains g=5, with five outside items. If outside two-slot Hall
succeeds, combine it with the internal pair lemma. First suppose a
projected singleton {r} supports t>=3 outside items; collect all of
them. For t=3, the projection trick produces six internal pair items
with at most one duplicate, leaves two items at r, and the two other
outside items have factors outside p,q,r. Pure-r items can instead
all stay at r.

For t=4, nine items lie on U={p,q,r}, with one genuinely outside item.
Select U plus one factor of that outside item. If some U base exceeds3,
the U capacity sum is at least8. Reserve one deep U item, taking it
from the only possible capacity-four pair when that pair has demand5.
Such a deep item exists, and otherwise any deep item works. The remaining
eight U items fit actual capacities: other pair capacities are at least6,
whereas all pair demands are at most5. Restore the reservation and put
the outside item at its selected factor. If all three U bases are3,
then U contains5 and7. Its nine items satisfy the auxiliary lemma above;
use that conservative certificate and assign the outside item separately.

For t=5, all ten items lie on p,q,r and every pair demand is at most5.
The same two-deep reservation and actual-capacity Hall argument used
for g=6,t=4 applies.

Finally suppose there is no projected singleton with three items.
An outside Hall failure must put all five outside items on two projected
primes r,t. The entire support is contained in U={p,q,r,t}. Every
triple supports at most seven items: a triple containing p,q has the
five internal items plus at most two projected-singleton items; a triple
omitting p or q has at most two internal pure items plus all five outside
items. Select these four primes. Pair capacities below6 equal4; triple
capacities below8 equal6. A capacity-six triple has all bases3 and
therefore contains5 and7. Any demanded seven-item such triple has a deep
item because it has at most five allowed squarefree values.

At most one capacity-four pair can have demand5. If two did, their
union would be a triple supporting at least5+5-2=8 items, contrary to
the bound seven. If that critical pair exists, reserve one of its deep
items; it also lies in the possible capacity-six triple. If no pair is
critical but a capacity-six triple has demand7, reserve one deep item
there. Otherwise reserve nothing. All actual Hall conditions now hold:
singletons have demand at most2; capacity-four pairs now have demand
at most4, and all other pairs have demand at most5 with capacity at
least6; the possible capacity-six triple now has demand at most6,
and all other triples have demand at most7 with capacity at least8;
total capacity is at least10. Restore the possible reservation.
This closes every pair with g>=5.

### Remaining triple and four-axis obstructions

Assume every pure group has at most two items and every pair at most
four. Let g>=7 be the maximum number of items supported on any triple,
and choose U with that many items.

For g=10, select U, reserve two deep items and assign the other eight
by actual Hall. At least three deep items exist because U has only seven
squarefree values. Singleton and pair demands already meet capacities;
total capacity is at least8. Restore both reservations.

For g=9, select U and one outside factor. If one core base is at least5,
reserve a deep core item, fit the other eight with actual capacities,
and restore it. If all three bases are3, U contains5 and7; use the
nine-item auxiliary lemma. Assign the outside item to its chosen factor.

For g=8, choose one outside factor for each of the two remaining items.
If some core base is at least5, its total integer capacity is at least8,
so all core items fit. Otherwise all core bases equal3; with at most two
external primes selected this forces5 into U. At most six different
squarefree core values are then allowed. Reserve two deep core items,
assign the other six with two slots each, and restore the reservations.
The two outside items cost at most2/3 on any external axis.

For g=7, first test outside two-slot Hall. If it fails, all three
outside items have the same singleton projected support {r}; hence all
ten items use U union {r}. In the actual four-prime chain every proper
demand fits except possibly a triple of capacity6 and demand7. Such
a triple contains5 and7 and therefore has a deep item. Reserve that
item if necessary, apply actual Hall and restore it. Total capacity
is at least10, pair demands are at most4 and other triples have
capacity at least8. Thus this outside failure is always harmless.

When outside two-slot Hall succeeds, any deep core item can be reserved:
the other six use two slots each and the outside assignment supplies
at most two items per outside axis. Restore the deep item. Consequently
the only remaining possibility is that the seven core values are
exactly all nonempty squarefree products of U. Numerical5 and7 being
absent, every prime in U exceeds7.

If an outside item w has a factor in U, assign it together with the
seven core items to U. Choose one outside factor for each of the other
two items and select those with U. Some U base must be at least5:
otherwise the three core primes above7 would need three distinct
external predecessors, but at most two were selected. The core capacity
sum is therefore at least8. Its singleton and pair demands after adding
w are at most two and four. Hall fits these eight items, and the other
two outside items cost at most2/3 externally.

Thus any obstruction has seven squarefree core products of U and three
outside values w_1,w_2,w_3, all coprime to the primes of U. Their precise
form is determined in the next section.

If there is no seven-item triple, a two-slot obstruction has nine or ten
items on four primes. For ten, selecting the four primes gives capacity
at least10, while singletons, pairs and triples demand at most2,4,6.
For nine, select the four core primes and one outside factor. Four core
bases cannot all be3 in a chain of at most five primes; one is at least5.
The core capacity sum is therefore at least10 and the same proper-demand
bounds suffice. Assign the one outside item separately. If no four-prime
set contains nine items, two-slot Hall already succeeds on full support.

### The three outside values must be pure predecessor powers

We are left with the seven squarefree products of U={q_1,q_2,q_3}, all
q_i>7, and three outside values coprime to U.

Choose one dividing prime for each outside value whenever possible so
that no chosen prime receives more than two items. This fails only when
all three outside values are pure powers of the same prime; in that
case their distinct powers have total cost below1/2 and one external
axis suffices. Three core bases could not all be3 with only one external
axis, so that case has a strict certificate too.

For any successful choice of outside axes, if any core base exceeds3,
the seven core items fit their actual capacities, whose sum is at least8
and whose singleton and pair demands are only one and three. The outside
loads are at most2/3. Failure therefore requires all three core bases3.
No core prime can supply another core prime's predecessor: it would
itself need a prime predecessor two smaller, making three consecutive
odd primes above3. Hence each q_i has a different external predecessor
p_i=q_i-2. These three p_i must be prime, different and outside U. Any
chosen outside-prime set yielding failure is exactly P={p_1,p_2,p_3}.
In particular q_i>=13.

Every prime factor of every outside value must lie in P. To see this,
if w_1 has a factor z outside P, assign w_1 to z. Unless both other
values are pure z-powers, choose their factors so that no axis receives
three items. The chosen set includes z and cannot equal P, so some core
base exceeds3 and a strict certificate results. If both other values
are distinct pure z-powers, put all three outside items at z; their total
cost at conservative base3 is at most1/3+(1/3+1/9)=7/9. With one outside
axis the core again has capacity at least8.

Now all outside supports are subsets of the three-element set P. Start
from a successful outside assignment with at most two items per axis;
the case where all three values are pure powers of one prime was already
handled. If this assignment uses at most two axes, it omits a predecessor
and gives a certificate. Otherwise it uses all three axes, one item on
each. If any item has another prime factor, that factor is another one
of the three occupied axes; move the item there. The assignment now uses
only two axes, with counts two and one, so it again gives a certificate.
The only remaining case has each item supported on its own singleton
axis. Therefore the three outside values are precisely
p_1^b_1,p_2^b_2,p_3^b_3, with b_i>=1.

Conversely, for this displayed family, the pure q_i values and pure
p_i powers force all six primes to be selected. The base at each q_i is
at most3 because p_i=q_i-2 is selected. Extra selected primes cannot
increase these bases or receive any squarefree core item. Seven core
items each cost at least1/3 on one of three axes, whose strict capacities
allow at most two core items each. Thus no strict certificate exists.
This proves the classification (NF64).

### Squarefree original ternary labels and disjoint prime supports

For the actual N3=19 split let

    E={5,7,s,35,5s,7s,35s,u^a}, u=s-2,

and let F be its disjoint retained ten-value set. Both E union F and the
original numerical palette have their stated divisor closure. A strict
certificate for F would contradict the same minimum cover through the
existing single-source CRT transport, so F has the exceptional form.

Every predecessor exponent b_i equals one. Otherwise divisor closure
puts p_i in E union F, while p_i is not among F's other five distinct
prime axes and is not its sole p_i^b_i value. Thus p_i belongs to E.
Since p_i>=11, this means p_i=s or, when a=1, p_i=u. The former makes
u,s,s+2=q_i three consecutive odd primes; the latter makes q_i=s collide
with E. Both are impossible.

Similarly a=1. If a>1, divisor closure puts u in F. If u=p_i, then
q_i=s collides with E; if u=q_i, then p_i=u-2,u,s=u+2 are three consecutive
odd primes. Both are impossible.

Thus E and F are squarefree, and their prime supports are disjoint.
The primes5 and7 cannot appear in F. Equality of s or u with any of
F's upper or lower twin primes is excluded by the same collisions and
three-prime argument. The remaining cofactor palette therefore consists
of two squarefree cubes on disjoint triples, together with their four
separate lower-twin prime labels: one for E and three for F.

Consequently

    N_3=19 ==> every original three-bearing modulus is squarefree;
    a nonsquarefree original modulus divisible by3 ==> N_3>=20. (NF65)

The prime supports of E and F are disjoint. No squarefreeness assertion
is made for C0 labels outside E union F.

This is a numerical necessary structure for the ACTUAL same-source
configuration. The classification alone does not prove that phases
covering the same R3 exist or exclude that configuration. The compatible
numerical example s=43,u=41 and upper F primes13,19,31 attains this
numerical pattern. Section56 excludes the nineteen-label case by applying
the existing transport to the original extremal cover. The unrestricted
odd-covering problem remains unresolved. No new Lean verification is claimed.

## 56. The original cover needs enough small-prime labels to block compression

Keep the original distinct odd whole cover selected by EB1: first minimize
cardinality, then the sum of its numerical moduli. Let p>q be two of its
support primes, and write N_q for the number of original moduli divisible
by q. Divisor closure supplies the original pure classes A_p,A_q; use the
single EB3 translation so both have first root zero. Define

    h0 = #{d in D: p does not divide d, v_q(d)=1},
    h1 = #{d in D: p*q divides d}.

Then the same original inventory satisfies

    h0>=p-q+2  OR  h0+h1>=p,
    N_q>=p-q+2.                                      (NF66)

Every original prime height is unrestricted. The bound is asserted for
the selected extremal cover, not for every distinct family without the
pure-prime and minimum-cardinality hypotheses.

The reusable construction is section27's IC1 map and its numerical
collision analysis. That section applies them to BC2's residual cover
with repeated labels and already fewer than n classes. Those input
hypotheses are not asserted here. The interface below starts with the
original n distinct labels and obtains strict deletion from A_p instead.
Also A_q already covers one whole output root, so only q-1 roots need
transport. This is an application with a checked interface, not another
proof of Hall's theorem or of the complete-prime-chain obstruction.

### Reserve actual collision roots

There are no repeated input labels, so take S empty. For every pair of
original moduli p*u and q*u with gcd(u,p*q)=1, put the actual first-p
root of A_(p*u) into T. Each such pair has its own q*u label counted by
h0, whence |T|<=h0. In particular u=1 is a pair, so 0 belongs to T.
Put D0=(Z/pZ) minus T and d0=|D0|.

For b in Z/qZ, let F_b contain the actual first-p roots of the original
p*q-bearing classes whose first-q root is b. These sets and T refer to
one original configuration; no independent phase choices are made.
On the left take only B=(Z/qZ) minus {0}. On the right take D0, with
edge b--a exactly when a is not in F_b.

### A full matching would delete the pure p class

Suppose there is an injection sigma:B -> D0 avoiding every F_b.
Write the full old period as p^A*q^B0*M, where A,B0>=1 and
gcd(M,p*q)=1. The output carrier is p^(A-1)*q^B0*M. On its subset
z mod q !=0 use precisely the IC1 common witness

    y mod p^A = sigma(z mod q)+p*(z mod p^(A-1)),
    y mod q^B0 = z mod q^B0,
    y mod M = z mod M.

All p-free original classes are retained as whole classes, with their
original numerical moduli and residues. Their restricted pullbacks on
this subset lie in those same whole classes. In particular the retained
A_q covers every omitted output point with z mod q=0; no witness is
needed on that subset. This is a covering extension of the restricted
pullbacks, not an assertion that those restricted sets are whole APs.

By the existing IC1 verification, every p*q-bearing original has empty
pullback on the transported subset. A q-free p-bearing original of
modulus p^alpha*u has empty pullback or one whole CRT class, of modulus

    q*p^(alpha-1)*u,

on its unique first-q root b in B. Its high-p coordinate is still the
divided original tail. These new classes, together with the retained
p-free classes, cover every output point: outside A_q, use whichever
old class covers that point's single witness y.

The map p^alpha*u -> q*p^(alpha-1)*u is injective. As in IC1, a collision
with an unchanged p-free modulus can occur only at alpha=1 and an old
pair p*u,q*u; T has excluded the p-root of that class. Higher q digits
of every unchanged class are preserved and cannot create a collision
with the new q-height-one labels. All output moduli remain odd nonunits.
Since 0 is in T, A_p contributes no class. Thus there are at most n-1
distinct classes covering all integers, contrary to EB1.

### The existing Hall rectangle gives the joint charge

Consequently this graph has no matching of all q-1 left roots. If
d0<q-1, then p-h0<=d0<=q-2, giving h0>=p-q+2. Otherwise reuse IC2--IC3
with its left set restricted to B. There is a nonempty I subset B,
with t=|I|<=q-1, such that

    W = D0 intersect intersection_(b in I) F_b,
    |W|>=d0-t+1,
    h1>=t*|W|>=t*(d0-t+1)>=d0.

The last inequality uses d0>=q-1>=t. Each actual p*q-bearing original
has only one first-root pair, even at higher exponents, so different
points of I times W require different original labels. Since
d0=p-|T|>=p-h0, the second alternative is h0+h1>=p. Both counts are
disjoint parts of N_q, proving NF66. Separate pairs p,q do not supply
disjoint inventories; their inequalities cannot be added without a
further joint counting argument.

### Reuse the known support bounds

Let P be the largest original support prime. EB3 makes the support an
initial segment of the odd primes, in particular containing three.
Taking q=3 and p=P gives

    N_3>=P-1.                                        (NF67)

The existing ordinary seven-prime noncoverage result in
[problem detail33, sections1--2](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md#1-the-inherited-seven-coordinate-measure-and-its-joint-density)
already forces at least eight support primes. Hence P>=23 and N_3>=22.
This alone excludes N_3=19, without requiring the squarefree
classification or a new case analysis of its phases.

For the stronger numerical consequence, directly reuse Schroeder's
*Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1,
Theorem1.1 (`thm:main`), as recorded in the
[existing source entry](../../../../../../Library/Arith/schroeder2026nine.md).
It requires at least nine support primes in every finite distinct odd
whole cover, with arbitrary original exponents and residues. Therefore

    P>=29,
    N_3>=28.                                         (NF68)

This application uses the attributed ordinary source theorem. The source
entry records its archive identity and the completed finite-geometry
verification; no complete local kernel replay of its arbitrary-height
reduction is asserted. The conclusion concerns the EB1-selected cover.
It does not exclude covers with sufficiently many three-bearing labels,
bound their number from above, or settle unrestricted Erdős #7. These
are ordinary mathematical deductions with no new Lean verification.

## 57. Equal full residue classes may be merged after transport

The root reservation in NF66 forbids every possible numerical collision.
The same IC1 interface can retain a collision when the two output APs
are actually equal. This uses their full cofactor residues, not only
their common numerical label or first roots.

Use the same original extremal cover and support primes p>q. Let

    U={u>=1: gcd(u,p*q)=1 and p*u,q*u are original moduli}.

For u in U write c_u and e_u for the actual original residues of the
classes modulo p*u and q*u, respectively, and alpha_u=c_u mod p.
Let F_b retain its section56 meaning. For each nonzero first-q root b
define the incompatible-collision roots

    G_b={alpha_u: u in U and
                    (c_u != e_u mod u OR e_u != b mod q)}.

Take left vertices (Z/qZ) minus {0}, right vertices (Z/pZ) minus {0},
and allow the edge b--a precisely when a is in neither F_b nor G_b.
This graph cannot have a matching of every left vertex. Equivalently,
there is a nonempty I of size t<=q-1 for which

    W=((Z/pZ) minus {0}) intersect
                     intersection_(b in I)(F_b union G_b),
    |W|>=p-t.                                        (NF69)

All pairs sharing the same first-p root must pass the compatibility
test for an edge. It is not enough that one pair at that root passes.
The definition of G_b enforces this by excluding any root with even
one incompatible pair. F_b continues to exclude every mixed p*q
original with the specified first-q root.

To prove the assertion, suppose a matching sigma exists and apply the
restricted IC1 map of section56. Keep every p-free original whole class,
so A_q still covers the untransported zero root. The other output
moduli are q*p^(alpha-1)*u, injectively indexed by the original q-free
p-bearing moduli. The only possible numerical collision with an
unchanged p-free class is again at alpha=1, with original pair p*u,q*u.

For a transported p*u on branch b, its new complete residue is specified
by b modulo q and c_u modulo u. Since the edge avoids G_b, these are
exactly the two CRT coordinates of e_u modulo q*u. Thus the new AP and
the retained AP are the same set and can be identified. There is at
most one transported class and one unchanged class at that numerical
modulus. No collision between transported numerical labels is possible.
Merging equal copies preserves coverage and creates no repeated label.
The pure-p class still disappears because zero is not a right vertex.
The result is therefore a distinct odd whole cover with at most n-1
classes, contradicting EB1. Hall's theorem gives NF69 on a right set
of size p-1, since a failing t-element left set has at most t-1
neighbours.

### Equality in the label bound forces different cofactor phases

Suppose the lower bound in NF66 is attained:

    N_q=p-q+2.

The second NF66 branch is impossible because h0+h1<=N_q<p. Hence
h0=N_q: every original q-bearing modulus has q-height one and is
p-free; in particular h1=0. In the more restrictive graph of section56,
every F_b is empty. Failure to inject q-1 roots into the complement
of T gives

    |T|>=p-q+2=N_q.

But |T|<=|U|<=h0=N_q, so equality holds throughout. Thus every original
q*u has its paired original p*u, and their |U| first-p roots alpha_u
are all different. The pure pair u=1 has root zero. Exactly q-2 roots
lie outside T.

If any non-pure pair u>1 had c_u=e_u modulo u, its first-q root
b=e_u mod q would be nonzero, by disjointness from A_q. Its unique
first-p root alpha_u would be a right neighbour of b in the relaxed
graph: no other pair uses that root and F_b is empty. Match b there,
and match the other q-2 left roots to the q-2 roots outside T. All the
latter roots have no collision obligation at any branch. This is a
forbidden complete matching. Consequently equality forces

    every q-bearing original is q*u, with gcd(u,p*q)=1;
    each has a paired original p*u, with pairwise different p-roots;
    c_u != e_u mod u for every u in U minus {1}.       (NF70)

There are p-q+1 non-pure pairs. Their cofactor APs of modulus u are
disjoint for each individual pair. This is a statement about their
actual common cofactor coordinates; different pairs need not be
disjoint from one another.

As a consumer, N_3=28 and NF67--NF68 force P=29, so the original support
is exactly the first nine odd primes. NF70 then requires all 28
three-bearing originals to have three-height one and no factor29,
all their paired 29*u labels to exist with different first-29 roots,
and all 27 non-pure paired cofactor residues to differ. Other original
heights remain unrestricted. NF69 and NF70 supply necessary joint phase
conditions; section58 excludes this equality configuration directly
using an existing height-one theorem, without forcing one of those
paired residues to agree. The unrestricted problem remains unresolved.
No new Lean verification is claimed.

### The missing paired phases must be paid on the same cofactor fibre

There is an exact whole-cover consumer of NF70. Write the full carrier
as q*p^A*M and k=|U|=p-q+2; here gcd(M,p*q)=1 and every original
q-bearing label has height one and no p factor. Fix one complete
cofactor point z modulo M which avoids all originals containing neither
p nor q. Let

    A(z)=#{u in U minus {1}: z=e_u mod u}.

Suppose the q-coordinate family leaves some first-q root uncovered at
this same z. Since no original contains both p and q, whole coverage
then requires the p-coordinate family to cover its ENTIRE p^A fibre.
Such a z exists: project an original private point of A_p to M. It
avoids all p,q-free classes, and its q word is uncovered by the
q-bearing originals. This nonemptiness alone gives no uniform lower
bound for the cofactor domain's measure.
For each of the A(z) active q*u cofactors, NF70 says that the paired
p*u is inactive at z. Every other paired p*u occupies at most 1/p
of the p fibre. Thus the total contribution of all k paired classes,
including pure p, is at most (k-A(z))/p.

Let D_rest be the original p-bearing labels other than these k labels
p*u. Each d in D_rest is q-free. Applying the ordinary union bound
on this one complete p fibre gives the necessary pointwise charge

    sum_(d in D_rest) p^(-v_p(d)) *
           1_[z=a_d mod (d/p^v_p(d))]
        >= 1-(k-A(z))/p
         = (q-2+A(z))/p.                            (NF71)

All cofactor events in NF71 use the original residues at the same z.
It can be integrated against any one common measure on the specified
cofactor domain. For q=3,p=29 the right side is (1+A(z))/29. Separate
optimizations of the two coordinate families cannot pay this charge.

This is also the exact-separator issue already handled algebraically in
[problem detail17, section3](../../../problem-details/17-two-prime-separator-interfaces-and-exact-count-probes.md#3-the-exact-joint-kernel).
Assign common p,q-free labels once, let L0(z) indicate their avoidance,
and let V_q(z),V_p(z) count the surviving q and p^A words respectively.
The number of complete survivors is exactly

    sum_(z mod M) L0(z)*V_q(z)*V_p(z).

The existing separator identity is reused without a new declaration.
Noncoverage of each smaller-support side separately
does not imply that the two positive supports meet at the same z.
Neither a uniform upper bound violating NF71 on that domain nor a
positive common separator word has been established here.

## 58. Reuse the height-one source before resolving individual collision phases

Keep EB1's extremal original cover, let H_q be its maximum original
q-height, and take support primes p>q. Divisor closure supplies the
H_q-1 distinct original labels q^2,...,q^H_q. Each lies outside BOTH
of section56's inventories h0 and h1. Therefore NF66 directly implies

    N_q >= h0+h1+(H_q-1) >= p-q+1+H_q.              (NF72)

This is a count of one actual original inventory. It does not add
inequalities obtained from different choices of p or q. The second
branch of NF66 gives the stronger p+H_q-1 for that branch; the displayed
bound holds in either branch.

The existing height-one theorem is already sufficient to exclude
section57's N_3=28 consumer. Report707 SS4 gives positive survivor
mass for every original family on the first nine odd primes with
v3(m)<=1, arbitrary actual residues and arbitrary nonternary heights.
NF70's equality configuration has exactly these properties. No further
agreement of its paired cofactor phases, nor a new upper estimate for
NF71, is needed to exclude that configuration.

For the stronger general height-one consequence, directly use
[Report708 TH3](../700-749/708-a-shared-support-sign-bridge-closes-thirteen-height-one-primes.md#arbitrary-actual-primes-including-the-no3-branch).
It proves noncoverage for at most THIRTEEN actual support primes when
every original has v3(m)<=1. Its other original prime heights and
residues are unrestricted. Thus EB3's initial-segment support and NF67
give

    H_3=1  ==>  at least14 support primes,
                 P>=47 and N_3>=P-1>=46.            (NF73)

This uses the existing ordinary source proof and its retained exact
arithmetic. Neither its phase optimization nor its finite checks are
repeated here, and no additional Lean verification is claimed.

When H_3>=2, NF72 and Schroeder's attributed nine-prime-support theorem
give N_3>=P+H_3-2>=29. The remaining equality N_3=29 forces P=29 and
H_3=2. The original pure9 label is outside h0 and h1, so h0+h1<=28.
The second NF66 branch h0+h1>=29 is impossible; the first forces
h0=28. Consequently equality requires

    P=29, H_3=2, h0=28, h1=0;
    the only three-bearing label outside h0 is9.    (NF74)

In particular no original modulus contains both3 and29. This reduction
still permits every other prime-power height. The next section excludes
NF74 by transporting a complete surviving prefix, rather than by
enumerating those other heights or residues.

## 59. Pure-power guards permit depth-dependent original-cover transport

Keep the same original extremal cover and support primes p>q. Set

    c_h=#{d in D:p does not divide d, v_q(d)=h},
    t=#{d in D:p*q divides d}.

Thus c_1 and t are h0 and h1 of NF66. Every class, exponent and phase
in the following graph belongs to this one actual original family.
The new interface of IC1 uses complete surviving q-prefixes as its
left vertices and keeps all old higher q digits unchanged.

### The live q-prefixes and actual forbidden p-roots

Fix an integer h>=1. Let L_h be the set of q^h-prefixes not covered by
any actual pure-q original q^j with j<=min(h,H_q). These omitted
prefixes are already covered by the retained pure classes. All other
p-free original classes will also be retained whole.

Let T_h consist of the actual first-p roots of A_(p*u) for the original
pairs

    p*u, q^h*u, with gcd(u,p*q)=1.

Put R_h={0} union T_h. No hypothetical phase or nonexistent label is
inserted into T_h. For each b in L_h, let F_b^(h) consist of the
actual first-p roots of every original mixed label

    d=p^alpha*q^beta*u, alpha,beta>=1, gcd(u,p*q)=1,

whose actual q-coordinate is compatible with the prefix b:

    b == a_d mod q^min(beta,h).

Define a bipartite graph with left set L_h, right set (Z/pZ) minus R_h,
and an edge b--a exactly when a is not in F_b^(h). This graph cannot
have a matching covering its entire left set.                  (NF75)

### The single common witness retains all higher coordinates

To prove NF75, suppose such a matching gives an injection sigma. Write
the full old period as p^A*q^B*M, with A,B>=1 and gcd(M,p*q)=1. Here
B=H_q. Use the output carrier

    p^(A-1)*q^max(B,h)*M.

For any output point z whose prefix b=z mod q^h lies in L_h, choose
one old witness y by the same IC1 coordinate rule:

    y mod p^A = sigma(b)+p*(z mod p^(A-1)),
    y mod q^B = z mod q^B,
    y mod M = z mod M.                               (NF76)

Represent sigma(b) in {0,...,p-1}. All old q digits and all cofactor
coordinates are preserved. When h>B the additional q-prefix digits
are coordinates of the new output carrier; they are not asserted to
have existed in the old source. The formula still gives one witness
for each transported point, not different witnesses for different
original classes.

Retain every p-free original whole AP with its original modulus and
phase. On the transported subset, membership of y in such an original
implies membership of z in that same whole AP. Every omitted prefix
is covered by one of the retained pure-q guards. The restricted
pullback of a retained class need not itself be a whole AP; only its
containment in the retained AP is used.

No mixed p*q-bearing original can contain the witness. Indeed, its
q-condition would imply b == a_d mod q^min(beta,h), and its p-condition
would put sigma(b) in F_b^(h), contrary to the matching.

For a q-free p-bearing original d=p^alpha*u, let a=a_d mod p. If a
does not occur in the image of sigma, its pullback is empty. Otherwise
there is exactly one b in L_h with sigma(b)=a, and the pullback is the
one whole CRT class given by

    z == b mod q^h,
    z == (a_d-a)/p mod p^(alpha-1),
    z == a_d mod u.

Its numerical modulus is

    q^h*p^(alpha-1)*u.                               (NF77)

The full divided old p-tail is retained, including alpha>1. When
alpha=1 the p-tail condition is vacuous. Since b belongs to L_h,
this whole AP already lies in the transported subset.

The numerical map in NF77 is injective on all transported originals.
A collision with an unchanged p-free modulus can occur only at
alpha=1 and an actual pair p*u,q^h*u. That root lies in T_h and has
been excluded. Thus every output modulus is distinct, odd and greater
than one. Root zero is excluded by R_h, so the original pure class A_p
has empty pullback. There are at most n-1 output classes.

These classes cover the whole output carrier: pure guards cover the
omitted prefixes, and elsewhere any old class containing the single
witness in NF76 supplies either a retained or a transported class.
All output moduli divide that carrier, so they cover all integers.
This contradicts EB1 and proves NF75. The argument reuses the IC1
tail and collision mechanics; its new interface is the guarded
q^h-prefix domain, including h beyond the original q-height.

For h>1, a mixed label with beta<h may forbid several live prefixes.
Consequently the first-root rule “one original supplies at most one
Hall-rectangle cell” used in NF66 cannot be reused on this graph
without accounting for the multiplicity. NF75 retains the full
prefix incidence and makes no such unit-cell assertion.

### A direct layer bound that does not charge prefix cells

The original pure q-powers are pairwise disjoint: an intersection
between comparable original APs would make the finer AP redundant,
contradicting minimum cardinality. Therefore, for 1<=h<=H_q,

    ell_h=|L_h|=q^h-sum_{j=1}^h q^(h-j)
                   =((q-2)*q^h+1)/(q-1).

At h=H_q+1 there is no additional original pure guard, so

    |L_(H_q+1)|=q*ell_(H_q).

Let F be the union of the first-p roots of all t original mixed
labels, regardless of their q-prefixes. This stronger global
blacklist has size at most t. Avoiding F avoids every F_b^(h), so
all remaining right roots connect to every live prefix.

When h<=H_q, the pair p,q^h is present and puts root zero in T_h.
Each pair counted by T_h uses its own original q^h*u label counted
by c_h, giving |R_h|=|T_h|<=c_h. If p-c_h-t>=ell_h, there are enough
right roots outside R_h union F to inject L_h, contrary to NF75.
Hence the same original inventory satisfies

    c_h+t>=p-ell_h+1       (1<=h<=H_q).              (NF78)

At h=H_q+1, no original q^h*u exists, so T_h is empty and R_h={0}.
If p-1-t>=q*ell_(H_q), the same complete-graph injection exists.
Consequently

    t>=p-q*ell_(H_q).                                (NF79)

These inequalities can be vacuous when their right sides are
nonpositive. The same t is used in each NF78 inequality: it cannot
be treated as a different disjoint supply at every height. This
coarse count avoids the mixed-prefix multiplicity issue by deleting
each mixed first-p root globally rather than charging graph cells.

In particular, if no original is divisible by p*q, then t=0 and

    c_h>=p-ell_h+1   (1<=h<=H_q),
    p-1<q*ell_(H_q).                                 (NF80)

For q=3,p=29, the last condition excludes H_3=1 and H_3=2. If the
pair3*29 is absent, H_3>=3 and the first three layer bounds are
c_1>=28,c_2>=25,c_3>=16. These three c_h inventories are disjoint,
so in this missing-pair case N_3>=69. This is a conditional
consequence; no absence of the pair3*29 is inferred for general
extremal covers.

### The twenty-nine-label equality cannot cover

Section58 reduced N_3=29 to NF74: P=29, H_3=2, c_1=28, t=0,
with pure9 the sole original of ternary height two. Take h=3 in NF75.
The actual pure3 and pure9 guards leave27-9-3=15 live prefixes.
There is no original of ternary height three, so T_3 is empty, and
there is no mixed3*29 original, so every F_b^(3) is empty. Inject the
fifteen live prefixes into the twenty-eight nonzero29 roots. The
single witness NF76 then gives the forbidden smaller distinct cover.
Equivalently NF79 requires t>=29-15=14, contrary to t=0.

Together with NF72--NF73, this proves for the EB1-selected cover

    N_3>=30,
    H_3=1 ==> N_3>=46.                              (NF81)

The unrestricted lower bound uses the same attributed
nine-prime-support premise as NF68. Its arbitrary-height reduction
has not acquired a new local kernel replay here. Report708 and the
guarded transport are ordinary mathematical arguments; no new Lean
verification is claimed.

These inequalities do not bound N_3 from above or exclude every
extremal family. For example the crude counts alone still permit
N_3=30,H_3=2,P=29 with c_1+t=29,c_2=1,t>=14; they do not assert
that any such inventory has actual covering phases. Section60 uses
the full graphs on the same original family to exclude that count.
Unrestricted Erdős #7 remains unresolved.

## 60. The two first-root branches share one original label inventory

Let P be the largest support prime of the same EB1-selected cover,
and let s be its number of actual support primes. Retain the attributed
nine-prime-support premise, so s>=9 and P>=29. The guarded graphs give

    H_3=1  ==> N_3>=P+s-5>=56;
    H_3=2  ==> N_3>=P+s-7;
    H_3>=3 ==> N_3>=P+2.
    In every height case, N_3>=31.                  (NF82)

The height-one numerical bound also uses NF73's existing conclusion
s>=14 and P>=47. All counts refer to one actual original family;
no lower bounds optimized on different phase configurations are added.

### The fresh third level forces actual labels at height two

Assume H_3=2. For every actual support prime r>=17, NF79 applied to
(p,q)=(r,3) gives at least r-15>0 original labels divisible by3*r.
Divisor closure therefore supplies the actual numerical label3*r.
This is a direct application of the existing fresh-prefix inequality,
not another proof of its transport map.

Relative to the fixed largest prime P, define

    c1=#{d in D:P does not divide d, v3(d)=1},
    c2=#{d in D:P does not divide d, v3(d)=2},
    t =#{d in D:3*P divides d}.

Thus N_3=c1+c2+t and c2>=1, because pure9 is original. There are
exactly five support primes below17, namely3,5,7,11,13. Of the s-5
support primes at least17, remove P. Their s-6 distinct original
labels3*r, together with pure3, belong to c1. Hence

    c1>=s-5.                                        (NF83)

Only the existence of each actual label3*r is used. The separate
mixed-label counts for different r are not added.

### Five live words give a stronger shared charge

At depth h=2, the NF75 graph has five live words. They lie in the two
nonzero first-three-root branches, in groups of sizes three and two:
pure9 removes one second-level word in exactly one branch. Let T2 be
the collision-root reservation. Pure-P/pure9 puts zero in T2, and
each collision pair has its own P-free original9*u, so |T2|<=c2.
The number of right roots is therefore

    d=P-|T2|>=P-c2.

Suppose c2<=P-6, so d>=6. Hall failure supplies a nonempty left set I
of size k<=5 and a right-root set W forbidden at EVERY word of I,
with |W|>=d-k+1. If I lies in one first-root branch, k<=3, and each
root of W requires a different mixed original. Consequently t>=d-2.

If I meets both first-root branches, each root of W requires at least
two mixed originals: an original class has only one first-three root.
Different first-P roots again require different labels. Thus

    t>=2|W|>=2(d-4)>=d-2.

The last comparison uses d>=6. Both cases give the common charge

    c2<=P-6 ==> c2+t>=P-2.                          (NF84)

Mixed originals may have three-height TWO. Such a class forbids only
a subset of its own first-root branch and cannot serve the other
branch. The proof never assumes that pure9 is the only original of
three-height two.

### Combine the shared charges with the original two-case bound

NF78 already supplies c2+t>=P-4 without the small-c2 premise; reuse
that inequality directly. NF66 gives c1>=P-1 OR c1+t>=P. In the first
case, N_3=c1+(c2+t)>=2P-5. In the second case with c2>=P-5, also
N_3=(c1+t)+c2>=2P-5. Otherwise NF83 and NF84 give

    N_3=c1+(c2+t)>=P+s-7.

Since there are s distinct odd support primes at most P, P>=2s+1;
in particular 2P-5>=P+s-7. This proves the height-two part of NF82
for every actual original inventory, without a small-count assumption.

For H_3>=4, NF72 already gives N_3>=P+2. If H_3=3 and N_3<=P+1,
NF72 forces equality. Pure9 and pure27 lie outside c1 and t, so
c1+t<=P-1. NF66 can only use its first branch, forcing

    c1=P-1, t=0,
    the only other three-bearing labels are9 and27.

Then c2=1 contradicts NF78's c2+t>=P-4. Thus H_3=3 also requires
N_3>=P+2. With s>=9, the height-two result gives that same bound.

### The height-one case uses six fresh words

Now assume H_3=1 and define c1,t as above, so N_3=c1+t. Applying
NF79 to each support r>=7 forces an actual3*r label, because its
mixed count is at least r-6>0. There are s-2 such support primes.
Remove P and add pure3 to obtain c1>=s-2.

For the pair (P,3), use NF75 at the fresh depth h=2. No original has
three-height two, so the right side excludes only the pure-P root
zero and has P-1 vertices. The six live words form two first-root
branches of size three. A failing Hall set I of size k<=6 has at
least P-k commonly forbidden right roots.

If I lies in one branch, k<=3 gives t>=P-3. If I meets both, the
same two-label charge per right root gives t>=2(P-6)>=P-3, since
P>=29. Therefore

    N_3=c1+t>=P+s-5.

NF73 supplies s>=14 and P>=47 in this height-one case, yielding56.
Together with the other heights, this proves all of NF82. In
particular the thirty-label case is excluded by joint use of the
actual graphs, although section59's coarse scalar counts allowed it.

These are ordinary proofs using the stated source theorems, not new
Lean verification or a claim of literature priority. No upper bound
on the full three-bearing inventory has been established. Dense
mixed inventories at arbitrary heights remain, and unrestricted
Erdős #7 is unresolved.

## 61. Variable-depth guarded frontiers retain one common witness

The guarded IC1 interface permits the surviving q-domain to use
different leaf depths simultaneously. The collision test uses each
chosen leaf's actual depth. Every successful finite interface has a
successful representative of maximum depth at most H_q+1, where H_q
is the full original q-height. Section59 supplies the common witness,
literal high-coordinate tails and pure guards; sections13 and20 supply
the complete-prefix-cut counting identity used below.

### Selected actual guards and per-leaf forbidden roots

Fix the same EB1-selected distinct odd original whole cover. Let p>q
be support primes, normalize the pure-p root to zero, and write its
complete period as

    p^A*q^H*M, A,H>=1, gcd(M,p*q)=1.

Choose any subfamily G of the actual original pure-q classes, required
to contain A_q, and retain each chosen class with its actual phase.
These pure cylinders are pairwise disjoint by minimum cardinality.
Let U be the complement of these SELECTED guards on the q-coordinate.
The parameter H remains the maximum q-height of the ENTIRE original
family, not the greatest depth among selected guards.

Take a finite prefix antichain B whose q-cylinders partition U. A leaf
b is a residue modulo q^h(b), with h(b)>=1. Distinct leaf cylinders
are disjoint; their phases and depths describe this one actual domain.
Put D=max(H,max_b h(b)). The output carrier is p^(A-1)*q^D*M.

For a live leaf b, define F_b to contain the actual first-p root of
every original mixed label

    d=p^alpha*q^beta*u, alpha,beta>=1, gcd(u,p*q)=1,

whose q-prefix intersects that leaf:

    b == a_d mod q^min(beta,h(b)).

Define T_b from every actual original numerical pair

    p*u, q^h(b)*u, gcd(u,p*q)=1,

by inserting the actual first-p root of the original p*u. This set
depends only on h(b), but is applied only on leaves of that depth.
There is no need to exclude its roots at every other leaf depth.

Use right vertices R=(Z/pZ) minus {0} and allowed lists

    A_b=R minus (F_b union T_b).

There is no injection sigma:B -> R such that

    sigma(b) belongs to A_b for every b.             (NF85)

### Each original still produces at most one output AP

Suppose such an injection exists. On an output point z in U, let b
be its unique leaf and use the one old witness

    y mod p^A = sigma(b)+p*(z mod p^(A-1)),
    y mod q^H = z mod q^H,
    y mod M = z mod M.                               (NF86)

Represent sigma(b) in {0,...,p-1}. All p-free original APs are retained
whole. Outside U the selected pure guards cover the output, so no
witness is needed there. Inside U, old p-free membership implies
membership in the same retained AP. Mixed p*q originals have empty
pullback by F_b. All old q digits are kept, even when a leaf stops
before depth H or uses additional digits beyond H.

Consider a q-free original p^alpha*u, alpha>=1, gcd(u,p*q)=1. Its
first-p root occurs at at most one leaf because sigma is globally
injective, including between leaves of different depths. If the root
is absent from the image, its pullback is empty. Otherwise let b be
the assigned leaf and a=a_d mod p in {0,...,p-1}. Its pullback is the
one complete CRT class

    z == b mod q^h(b),
    z == (a_d-a)/p mod p^(alpha-1),
    z == a_d mod u,

whose numerical modulus is

    q^h(b)*p^(alpha-1)*u.                            (NF87)

This whole AP lies in U because its q-prefix is the live leaf b.
The divided old p-tail is retained literally at every original alpha.
Equality of two output numerical moduli forces, by their valuations,
h(b)=h(b'), alpha=alpha' and u=u'. The old numerical moduli would
then be identical. Original distinctness and the global injection
therefore rule out collisions between transported labels.

A collision with an unchanged p-free modulus requires alpha=1 and
the actual pair p*u,q^h(b)*u. Its p-root is excluded by T_b. Thus all
output labels are distinct odd nonunits. The pure-p class disappears
because sigma avoids zero; every other original supplies at most one
class. The total is at most n-1.

Pure guards cover outside U. Inside U, an old class covering the one
witness NF86 supplies a retained or transported output class. All
output moduli divide the new carrier, so these classes cover all
integers. This contradicts EB1 and proves NF85.

Section57's existing compatible-full-phase test may relax the collision
reservations when transported and retained APs are identical. NF85
uses the simpler exclusion of every possible numerical collision.

Every uniform-depth NF75 interface is included: for its depth h, take
G={A_(q^j):1<=j<=min(h,H)} and its live depth-h prefixes. The variable
interface permits those same guard domains together with nonuniform
leaf depths.

### The full original height gives an exact finite search horizon

Suppose a successful finite frontier and injection exist, with some
leaves deeper than H+1. Fix a live prefix v of depth H+1 subdivided
by that frontier. Every old q-condition has depth at most H, so its
compatibility with v is the same as with each descendant of v.
There are also no original labels of q-height H+1 or greater; T_v
and all descendant collision lists are empty.

Choose one descendant leaf and retain its assigned p-root. Replace
all frontier leaves below v by the single leaf v with this root.
Its mixed forbidden-root list is unchanged, its collision list is
empty, and deleting the other assigned roots preserves injectivity.
The cylinders still partition the same complement of the selected G.

Repeating this at every subdivided depth-(H+1) prefix gives

    a successful finite variable-depth frontier exists
    iff one exists with maximum depth <= H+1.         (NF88)

This statement uses the full original H, even when G contains only
shallow guards. Depth H alone is not supplied by this argument:
original q^H*u labels can still create numerical collisions. The
extra level is where every collision label is fresh.

### The actual guard tree can need fewer boundary leaves

Here choose ALL H original pure-q guards. Let B_can be the maximal
q-cylinders in their complement. This is a finite antichain of depths
at most H. Every live cylinder lies inside one of these maximal
cylinders, each of which must be covered, so B_can has the fewest
leaves among prefix antichains partitioning that complement. This
minimality concerns partition size, not matching.

Let I count the distinct proper prefix ancestors of the H guards.
They are the internal nodes of the full pruned q-ary tree with leaves
G union B_can. Directly applying sections13 and20's tree identity gives

    |B_can|=1+(q-1)*I-H.                             (NF89)

For q=3, guard words 0,10,110,... in lowest-digit-first order have
I=H and H+1 live leaves. The uniform depth-H representation instead
has (3^H+1)/2 live words. This is a pure-guard example, not a whole
cover. The actual I must be read from the given guard tree; that
chain layout is not substituted for arbitrary original phases.

Coarsening can enlarge F_b by meeting more mixed q-prefixes, while
changing depth also changes T_b. Fewer leaves alone therefore do not
imply a matching or a stronger uniform numerical bound. The interface
keeps both effects in the same actual graph.

### One finite actual family separates variable and uniform depths

Take p=5,q=3 and the following distinct odd APs, written as
(modulus,residue):

    (3,0),(9,1),(5,0),(7,0),(11,0),(13,0),
    (21,8),(33,23),(39,14),(35,16),(55,2),(65,28).

The numerical set is divisor-closed and every comparable pair of
original APs is disjoint. In the displayed order, private points are

    3,1,5,7,11,13,8,23,53,16,2,158.

Integer4 is uncovered. Thus this family is a control for the finite
interface, not a whole cover or an EB1 extremal example.

At uniform depth1 the pure3 guard leaves two roots. The actual pairs
5,3 and 5*r,3*r for r=7,11,13 give T_1={0,1,2,3}. Only p-root4
remains, so no matching exists. At depth2, five live words cannot
inject into four nonzero p-roots. At every uniform h>=3 the guards
leave5*3^(h-2)>4 live words. All uniform-depth graphs therefore fail.

The complement of both pure3 and pure9 instead has frontier

    2 mod3, 4 mod9, 7 mod9.

Assign these leaves p-roots4,1,2, respectively. There are no mixed3*5
originals, so F_b is empty. Root4 avoids T_1 at the depth-one leaf.
At depth2 the only collision pair is5,9, giving T_2={0}, so roots1,2
are allowed. This is a full variable-depth matching on the one actual
family. Together with the uniform embedding above, it strictly
separates the two interfaces. The uncovered point prevents this
control from contradicting NF85's whole-cover premise.

### An exact finite tree-cut and root-allocation recurrence

Use NF88 to set D=H+1. At a q-prefix node v, let C(v) be the collection
of subsets of R that can be used by an injectively labelled live
frontier inside v. A node wholly inside a SELECTED guard from G has
C(v)={empty set}. A node wholly outside G, with no selected-guard
ancestor or descendant, may stop using any singleton {a}, a in A_v.
At depth D those are the only live-node possibilities.

At a smaller depth a live node may instead split into all q children.
A node partly meeting G must split. The split option contributes

    union_i S_i, where S_i belongs to C(child_i)
    and the S_i are pairwise disjoint.               (NF90)

At depth D no partially guarded node remains. Induction on the
remaining depth proves this recurrence exact: pairwise disjoint masks
express precisely the global injection across child subtrees. At the
root, any feasible mask gives one of the matchings excluded by NF85.
Thus an extremal whole cover requires C(root) to be the empty
collection, not the singleton collection containing the empty mask.

There are at most2^(p-1) possible masks per node. This is a finite
exact test of one given family's interface, not an assertion of low
uniform complexity or successful matching for every possible family.
A general contradiction still requires controlling the actual guard,
collision and mixed-prefix incidence together. These are ordinary
mathematical arguments, with no new Lean verification or literature
priority claim; unrestricted Erdős #7 remains unresolved.

## 62. Weighted root reuse retains exact original-label budgets

Section61's transport can reuse a first-p root at different q-prefix depths. The resulting copies must be charged by the actual number and numerical sizes of original labels at that root. This section reuses the common-witness construction NF86--NF87 and the lexicographic replacement rule PH2. The fixed-frontier optimization is ordinary weighted assignment, not a new matching theorem.

### Actual root workloads and the distinctness contract

Keep section61's one EB1-selected original whole cover, support primes p>q, selected actual pure-q guards G, live finite q-prefix frontier B, and literal forbidden lists F_b,T_b. Let n_0 be the number of p-free original classes, let t be the number of mixed p*q-bearing original classes, and put

    D_mix = sum_{d:p*q divides d} d.

Partition the remaining original labels, which are q-free and p-bearing, by their actual first-p root a. For d=p^alpha*u, with alpha>=1 and gcd(u,p*q)=1, define

    R_a = number of these original labels at root a,
    S_a = sum of d/p over these same original labels.   (NF91)

Both quantities refer to the same original family; no branch separately chooses an inventory. They are nonnegative integers, and R_a=0 iff S_a=0. The normalized pure-p class gives R_0=S_0=1. Indeed, any other original p-bearing class at root0 would lie inside that pure-p class and contradict minimum cardinality.

For each leaf b, choose

    sigma(b) in (Z/pZ) minus (F_b union T_b).

Unlike NF85, this weighted interface permits root0 whenever its actual
collision list allows it. For h(b)<=H, divisor closure supplies the
original pure-q modulus q^h(b); the pair p,q^h(b) puts root0 in T_b.
For h(b)>H, T_b is empty. Also F_b never contains root0: an original
mixed class at that root would lie inside the pure-p class and be
redundant. Thus root0 is an additional allowed positive-workload
resource at fresh depths. Its transported pure-p class is the whole
leaf AP of modulus q^h(b), still an odd nonunit.

Require only the following capacity condition:

    for every a with R_a>0 and every depth h,
    at most one depth-h leaf is assigned root a.        (NF92)

The same positive-workload root may occur at different depths. Roots with R_a=0 may be reused at the same depth without limit: they copy no original labels. This distinction is necessary for the stated workload accounting.

### Coverage and numerical distinctness use the same witness

On a point z in the live q-domain U, use its unique leaf b and the one original witness NF86, with first-p root sigma(b). Retain all p-free original classes unchanged. The selected guards cover the complement of U; mixed originals have empty pullback by F_b. The old p-tail and complete cofactor residues remain exactly those in NF87.

Each q-free p-bearing original d at root a therefore supplies one whole AP for every leaf assigned a, with numerical modulus

    q^h(b)*d/p.

No other original supplies a transported AP. A zero-workload assignment supplies none, but the witness is still covered: if the old covering class were mixed it would violate F_b, and if it were q-free p-bearing it would belong to that empty workload. Hence an unchanged p-free class covers this witness and the corresponding output point.

Equality of two transported numerical moduli forces equal q-depth and equal quotient d/p, because each quotient is q-free. Thus it forces the same original d. Repeated copies of this same d at the same depth are ruled out by NF92; different depths have different numerical moduli. A transported/retained collision can occur only when alpha=1 and the original family contains the pair p*u,q^h(b)*u. Its first-p root is excluded by T_b. Consequently the output classes have pairwise distinct odd nonunit moduli and cover all integers. The output carrier may use q-height max(H,max_b h(b)); all original q-digits and cofactor coordinates remain literal.

These statements use strict collision reservation, without pruning or merging classes. Section57's compatible-full-phase relaxation can be treated separately; it is not included in the following exact unpruned count.

### Exact class and modulus-sum budgets

Let S_free be the sum of the original p-free moduli. The exact inventories are

    n_new = n_0 + sum_b R_sigma(b),
    n_old = n_0 + t + sum_a R_a,

    sum_new = S_free + sum_b q^h(b)*S_sigma(b),
    sum_old = S_free + D_mix + p*sum_a S_a.           (NF93)

All root sums include root0, and leaf assignments may use it subject to
the actual allowed list. In particular, if k_a is the number of leaves
assigned a, the new class-count difference is

    n_new-n_old = sum_a (k_a-1)*R_a - t,

Unused roots retain their negative credits. The nonzero-root restriction
of section61 is the special case k_0=0.

Apply PH2 to the changed original classes, or directly use EB1's two ordered objectives. Every feasible frontier and allocation must satisfy

    lex(sum_b R_sigma(b), sum_b q^h(b)*S_sigma(b))
      >= lex(t+sum_a R_a, D_mix+p*sum_a S_a).        (NF94)

Here lex first compares class count, then numerical modulus sum. Thus a strict improvement in the first coordinate alone contradicts EB1. At equal counts a strictly smaller second coordinate also contradicts EB1. A smaller modulus sum with a larger class count gives no contradiction to the stated objectives.

This recovers the already proved NF85 without a separate replacement
argument: a globally injective allocation restricted to nonzero roots
obeys

    sum_b R_sigma(b) <= sum_{a!=0} R_a
                       = sum_a R_a - 1
                       < t+sum_a R_a.

The additional interface is root reuse charged by its actual workload, rather than a second proof of the injection obstruction. Large q-depth can lower no class charge and increases the numerical charge of every positive-workload copy; neither charge is replaced by an unproved uniform scalar price bound.

### Fixed-frontier optimization separates by depth

Fix B and all its actual allowed lists. A leaf whose list contains a zero-workload root can be assigned such a root at price (0,0). Do this for every such leaf and remove it from the positive-workload assignment problem. These choices consume no positive-root capacity and impose no capacity on other zero-root choices.

For each depth h separately, match the remaining leaves at that depth injectively to allowed roots a with R_a>0, giving an edge the ordered price

    (R_a, q^h*S_a).

If one depth has no such matching, this fixed-frontier construction is infeasible. Otherwise the lexicographic minimum of the total two-coordinate price is

    sum_h [the lexicographic minimum matching price
           among remaining depth-h leaves].         (NF95)

This is a direct use of standard minimum-cost assignment with lexicographic costs. No root capacity links two different depths, so the feasible choices form a product of the per-depth matching choices. Addition preserves lexicographic comparison, which gives NF95. Conversely, any NF92 allocation gives one such matching at each depth after free leaves are removed. Hence the optimizer is exact for the declared unpruned fixed-frontier transport.

If the resulting minimum is below the old budget in NF94, its attaining matchings construct a forbidden distinct odd whole cover. If it is not below that budget, this transport supplies no extremal contradiction; no conclusion about alternative transports follows. Searching over variable frontiers remains a separate problem. NF88's H+1 cutoff was proved for global injection and is not transferred to repeated positive-workload roots.

The counts, weights, forbidden prefixes and phases all belong to the one actual original family. The arithmetic accounting adds a weighted noninjective interface to the earlier common-witness transport; weighted assignment is reused directly. These are ordinary mathematical arguments, not new Lean verification or a literature-priority claim. A uniform condition forcing NF94 to fail for every admissible extremal whole cover has not been proved, and unrestricted Erdős #7 remains unresolved.

## 63. Finite depth bounds retain the weighted replacement budget

Keep section62's actual batches (R_a,S_a), selected pure guards and
fixed original lexicographic budget, whose first coordinate is C_old.
Let H be the maximum q-height of the ENTIRE original family and put
D=H+1. The allowed root pool may be any declared subset of Z/pZ,
including literal residue zero. Each R_a is a nonnegative integer;
R_a=0 implies S_a=0, and all S_a are nonnegative. A positive-workload
root may occur at most once at each leaf depth. A zero-workload root
may occur repeatedly, even at the same depth. Zero workload is not
the same condition as literal p-root zero.

After the unchanged originals cancel, a frontier's replacement cost is

    (sum_b R_(a_b), sum_b q^h(b)*S_(a_b)).

The following bounds preserve strict improvement of this pair against
the same fixed original budget. They do not change the root lists or
the actual batches. In particular literal root zero, when admitted,
is treated with its positive batch (R_0,S_0)=(1,1).

### Remove free deep subtrees before counting leaves

Above H every numerical collision list is empty. The allowed root
list on descendants of a live H-prefix is therefore constant from
depth D onward: all original mixed q-conditions have depth at most H.
Use these DEEP lists, without the possible depth-H collisions.

Start with any successful finite frontier and keep its leaves of
depth at most H. Every remaining live H-prefix is subdivided. If its
deep list contains a zero-workload root, replace its descendant
frontier by its q children at depth D, all assigned that root. This
preserves the complete domain and cannot increase either cost.
Unlimited reuse of that root imposes no positive-root capacity demand.

The remaining hard forest begins at depth D. Each remaining H-prefix
contributes q roots of the same type A, its nonempty set of allowed
positive-workload roots. A successful candidate cannot leave such a
deep allowed list empty. If the hard forest is empty, depth D suffices.

### The original class budget already bounds the required depth

A successful strict lexicographic improvement has first cost at most
C_old, where C_old>=1. Each hard leaf contributes an integer R_a>=1,
so the number L of hard leaves is at most C_old. If the hard forest
has r>=1 roots at depth D and I internal nodes, directly reuse the
complete q-ary forest identity from sections13 and20:

    L=r+(q-1)*I.

Every path below D has length at most I. Thus the same folded
successful candidate satisfies

    max leaf depth <= D+floor((C_old-r)/(q-1))
                   <= H+1+floor((C_old-1)/(q-1)).     (NF96)

Together with the empty-forest case, this makes the strict replacement
test finite for one fixed original inventory. The additional bound
below depends on root resources instead of C_old.

### Actual deep types have bounded simultaneous width

Let k be the number of positive-workload roots in the declared pool,
so k<=p. If k=0, every successful candidate folds to depth D. Assume
k>=1 for the following bounds.

At a deep level let n be the number of hard nodes awaiting their
complete descendant cut. The finite forest Kraft identity gives

    n=sum_{j>=0} m_j*q^(-j),

where m_j counts leaves at relative depth j. Positive-root uniqueness
at each absolute depth gives m_j<=k. Since the sum is finite,

    n<k*q/(q-1).

Let n_A count the current nodes of type A and let m_A be the number
chosen as leaves there. Initially each n_A is a multiple of q, and
the next count is n'_A=q*(n_A-m_A), preserving that divisibility.
Writing z_A=n_A/q gives

    sum_A z_A<=B:=floor((k-1)/(q-1)),
    z'_A=q*z_A-m_A.                                 (NF97)

The chosen leaves must receive distinct roots at that level, each
in its own actual type A. No type is created by splitting a node.
If m_used types occur initially, each contributes at least one to
sum_A z_A, so m_used<=B. The number of possible count vectors,
including the terminal zero vector, is at most

    N=binomial(B+m_used,m_used)<=binomial(2B,B).

If B=0, a nonempty hard forest cannot have a successful finite cut.
These vectors count nodes of actual allowed-list types; they are not
independently chosen phase configurations.

### Equal count states can be removed without changing the source

Suppose a successful hard forest has the same type-count vector at
two depths d1<d2. Pair all live nodes at those depths within each
type. At every d1 node, replace the remaining subtree by the labelled
suffix subtree of its paired d2 node, copying only relative digits.

The replacement still partitions each receiving cylinder completely.
Its first H q-digits remain those of the receiving node. All new
depths are at least D, so the type's mixed exclusions are unchanged
and numerical collision lists remain empty. Every root copied into
a receiving node is therefore allowed there. At each new absolute
depth the labels come from one complete later level of the old
suffix, preserving positive-root uniqueness. Leaves at depths less
than d1 are unchanged and cannot collide at those new depths.

Apply section62's weighted transport to this admissible frontier.
Its single old witness still copies the receiving output point's
complete original q-coordinate and cofactor coordinates, with the
assigned p-root and literal divided p-tail. No donor source point
is substituted. Output q-heights exceed H, and the per-depth root
capacity still excludes numerical collisions. Each assigned root
uses the same original batch, so its R_a and S_a are unchanged.

The intervening leaves are removed. The first cost consequently
cannot increase. Each suffix leaf moves shallower by d2-d1, multiplying
its second cost by q^(-(d2-d1)); removed costs are nonnegative. Both
coordinates therefore decrease or stay fixed, preserving strict
lexicographic improvement against the original budget.

Repeating this deletion leaves no repeated count state. There are
at most N states, so the conservative depth bound D+N suffices.
Together with NF96, every successful candidate with k>=1 has a
successful representative satisfying

    max leaf depth <= H+1+
      min(floor((C_old-1)/(q-1)), binomial(2B,B)).     (NF98)

The candidate-specific binomial(B+m_used,m_used) may replace the
central binomial term. For odd primes p>q>=3, k<=p gives
B<=floor((p-1)/2)=(p-1)/2, yielding a bound in H and p alone for
the root-resource term. The k=0 case uses the direct depth D bound.

### Per-depth reuse does not inherit the injective H+1 cutoff

For an abstract allowed-list control, take q=3,H=1,p=7. The pure
guard is first root0, leaving roots1 and2. No leaf may stop at
depth1. At every greater depth allow positive-workload roots
{0,1,2,3,4}, each with R_a=S_a=1. Roots5,6 have zero workload but
are forbidden. Literal root0 is thus allowed at every deep node.

Depth2 has six live nodes and only five available positive roots,
so no frontier of maximum depth2 exists. At depth2 stop five nodes
with the five different roots; split the sixth into three depth3
leaves assigned roots0,1,2. The resulting cost is (8,126), strictly
better than any fixed abstract budget with first coordinate9.

No actual AP family realizing these lists and prices is asserted;
in particular unit prices on the nonzero roots are abstract. The
control shows that constant deep lists and per-depth capacities
alone do not imply the injective H+1 cutoff. It does not construct
an extremal odd cover or refute any stronger arithmetic condition.

NF96 already gives finite decision for a fixed original inventory;
the state argument adds a bound independent of that inventory's
class count. Neither supplies efficient search or a successful
replacement for every hypothetical cover. Additional absolute-depth
restrictions or costs that grow when leaves move shallower would
require another argument. These are ordinary mathematical results,
with no new Lean verification; unrestricted Erdős #7 remains open.

## 64. The common literal zero root makes deep feasibility a static Hall condition

The weighted all-root interface supplies one root allowed in every fresh-depth list: literal p-root zero. Its original batch is exactly the pure-p class, so R_0=S_0=1. This section reuses the ordinary capacitated Hall theorem, the complete-prefix Kraft identity and the rearrangement inequality. It supplies an exact criterion for finite deep-frontier existence and the cost of one explicit construction. It does not assert that this construction improves the original budget or minimizes all possible frontier costs.

### Actual deep jobs and the common root

Fix one actual original family with highest q-height H and set D=H+1. Fix all chosen live frontier leaves at depths at most H. Remove the deep obligations whose constant allowed list contains a zero-workload root by the existing free-folding rule. Each remaining live H-prefix is one actual parent job. Its entire cylinder must be partitioned by leaves of depths at least D. Its allowed root set A_i is constant throughout that subtree, contains literal root0, and consists entirely of positive-workload roots.

Write r_A for the number of remaining actual parents having allowed set A, and r=sum_A r_A. Types with r_A=0 are omitted. All lists retain their actual original mixed-phase restrictions. A positive root may be used at most once at each absolute depth; it may recur at different depths. There are no original collision labels at these fresh depths. Existing shallow leaves occupy different depths and impose no same-depth capacity restriction here.

When r=0 there is no hard continuation and its cost is zero. Suppose r>=1. Then a finite complete deep cut with permitted per-depth root assignments exists if and only if

    |union_(A in S) A| >= (q-1)*sum_(A in S) r_A + 1
      for every nonempty set S of occurring types.          (NF99)

### Necessity keeps all actual trees in each type collection

Fix a nonempty type set S, and put r_S=sum_(A in S)r_A and K_S=|union_(A in S)A|. Its parents supply exactly q*r_S nodes at depth D. The complete finite cut below those nodes satisfies the forest Kraft identity

    q*r_S = sum_(j=0..J) L_(S,j)*q^(-j),

where L_(S,j) is the number of their leaves at depth D+j. The root assignments are globally injective within each depth, and every such leaf uses a root in the same union of actual lists. Hence L_(S,j)<=K_S. Since the cut is finite,

    q*r_S <= K_S*sum_(j=0..J)q^(-j) < K_S*q/(q-1).

Thus (q-1)r_S<K_S, which is precisely the integer inequality NF99. This does not sum bounds from different sources: it counts the literal leaves of those actual parent subtrees.

### Sufficiency is a direct Hall allocation followed by comb completion

Because root0 belongs to every A, NF99 is equivalent to

    |union_(A in S)(A minus {0})| >= (q-1)*sum_(A in S)r_A.

Create q-1 labelled demand slots for each actual parent i, all with allowed set A_i minus {0}. The displayed inequalities imply Hall's condition for every subset of these slots: if its represented types are S, its size is at most (q-1)r_S and its neighbor union is exactly the displayed union. Ordinary finite Hall matching therefore supplies disjoint sets

    U_i subset A_i minus {0}, |U_i|=q-1,
    U_i intersect U_j=empty for i!=j.                      (NF100)

This is the same cloning use of capacitated Hall as Report386 PC13 and Report385's existing capacity assignments. The upstream finite theorem is Finset.all_card_le_biUnion_card_iff_existsInjective'; no new generic matching statement is needed.

Choose any completion order, giving each parent i a different completion stage ell_i in {1,...,r}. At stage ell=1, each unfinished parent exposes its q actual children at depth D. Stop q-1 of them, labelling those leaves by its reserved U_i. The remaining child is its continuing branch, except that the unique parent completing at this stage labels that child by root0 and stops it too. At each later stage split every continuing branch into q children and apply the same rule.

All nonzero roots used at a stage are distinct because the U_i are disjoint. Root0 is used exactly once at that stage. Every root belongs to the actual job's fixed allowed list. Each job completes its whole cylinder with a finite comb, and its actual H-prefix remains unchanged. The deepest resulting leaf has depth

    D+r-1.                                               (NF101)

At the count-vector level, a stage selects

    m_A=(q-1)r_A+1_(A is the completing job's type),
    r'_A=q*r_A-m_A=r_A-1_(A is that type).

Thus every type count weakly decreases, and the sum decreases by one. This also explains why all subset conditions remain valid; a separate polymatroid preservation theorem is unnecessary.

Applying the established weighted transport to this actual labelled cut preserves the one old witness rule, complete old q-coordinates, cofactor coordinates and divided p-tails. The common root0 copies pure p to a fresh q-power output; it is not claimed deleted. The explicit comparison with the original count and modulus-sum budgets remains necessary.

### Exact costs for fixed reserved root groups

For each parent put

    R_i=R(U_i)=sum_(a in U_i)R_a,
    S_i=S(U_i)=sum_(a in U_i)S_a.

The roots in U_i occur once at each stage1 through ell_i. The pure-p root0 occurs once at each parent's finishing stage. Therefore the deep construction has exact costs

    C_comb=r+sum_i ell_i*R_i,                             (NF102)

    W_comb=q^D*sum_i [ ((q^ell_i-1)/(q-1))*S_i
                       +q^(ell_i-1) ].                   (NF103)

Add the fixed shallow-leaf costs to NF102--NF103 before comparing with the original removed-class budget. The free folds contribute zero. These formulas use the original root batches, rather than a newly optimized arithmetic source.

For fixed disjoint groups U_i, the lexicographically best completion order sorts R_i in nonincreasing order and, within an equal-R_i block, sorts S_i in nonincreasing order. The count assertion is the standard rearrangement inequality between increasing completion times and descending weights. Any inversion of two unequal R_i strictly increases the count, so the remaining freedom at minimum count consists only of ties. On a tie block the coefficient (q^ell-1)/(q-1) is strictly increasing, and rearrangement again puts larger S_i earlier. The root0 sum sum_i q^(ell_i-1) is independent of the order. This is direct reuse of the rearrangement principle; Mathlib's Antivary.sum_mul_le_sum_mul_comp_perm provides the corresponding generic inequality.

The claim is only for the ordering of these fixed groups within this comb construction. It neither optimizes the Hall assignment nor says a comb is globally cost-minimal. For example, if every job permits all k roots and k>=q*r, all q*r children may stop already at depth D with distinct roots. That valid cut can use fewer leaves than sequential comb completion.

### The remaining budget obligation

NF99 is an exact static test for existence of some finite deep continuation of these forced actual parent jobs. It does not decide whether any continuation satisfies the strict original lexicographic budget: feasibility and affordable transport are different statements. NF102--NF103 give a computable sufficient candidate cost after a Hall allocation; failure of that candidate's cost does not rule out a cheaper noncomb cut. The existing weighted finite-horizon search and fixed-frontier minimum-cost assignment remain available for the full strict-budget question. No condition NF99 has been proved for every hypothetical odd cover, and no unrestricted Erdős#7 conclusion follows from this interface alone. These are ordinary mathematical applications and interface deductions, with no new Lean verification or literature-priority claim.

## 65. All-root injections charge every deleted mixed original

Keep the same EB1-selected original cover, support primes p>q and
section62's actual root batches. Let t count its mixed p*q-bearing
originals. A globally injective frontier allocation into ALL p roots,
respecting its actual lists F_b,T_b, satisfies

    sum_b R_sigma(b)<=sum_a R_a<t+sum_a R_a
      whenever t>0.                                (NF104)

By NF93--NF94 this would strictly reduce the original class count.
Such a matching is therefore forbidden when t>0. Literal root0 may
be used: the strict saving is supplied by the deleted mixed originals,
without requiring deletion of pure p. This directly reuses the
weighted transport and its exact inventory, not a new witness map.

### The fresh-level mixed-label bound gains one class

Let H be the full original q-height. Choose all actual pure-q guards
and use the uniform fresh depth H+1. Section59 gives

    ell_H=((q-2)*q^H+1)/(q-1),
    ell=q*ell_H

live words, with no numerical collision reservations. Then

    t>=p-q*ell_H+1.                                 (NF105)

If p-ell+1<=0, this follows from t>=0. Otherwise ell<=p. Since ell
is a positive multiple of q and p is a different prime, ell!=p.
The existing NF79 consequently gives t>=p-ell>=1.

Let F be the set of actual first-p roots of all t mixed originals,
so |F|<=t. If t<=p-ell, at least p-t>=ell roots lie outside F.
Every such root is allowed at every live word, because the fresh
collision lists are empty. A full injection into these roots would
contradict NF104. Thus t>=p-ell+1, proving NF105.

The count uses one global set of actual mixed roots. It does not
charge a deeper mixed original separately at every compatible prefix,
and it places no restriction on the other original prime heights.

### The height-one consumer retains both first-root branches

Assume H_3=1, let P be the largest support prime and let s be the
number of actual support primes. NF73 supplies s>=14 and P>=47.
For the pair (P,3), NF79 gives t>=P-6>0. Thus NF104 forbids a full
matching of the six fresh depth-two words into all P roots.

Reuse section60's Hall charge on the two first-three-root branches,
each containing three live words. A failing left set I of size k<=6
has a common forbidden-root set W with |W|>=P-k+1. If I stays in
one branch, k<=3 and distinct roots of W require different mixed
originals, giving t>=P-2. If I meets both branches, each root in W
requires two different originals, because an original has only one
first-three root. Therefore

    t>=2|W|>=2(P-5)>=P-2.

The last inequality holds here since P>=47. Literal root0 lies in
every allowed list; it cannot be a commonly forbidden root. This
rules out a singleton failing I, without changing the stated bound.

Section60 already supplies c1>=s-2 from the actual labels3*r with
r>=7 and pure3. These P-free labels and the mixed originals are
disjoint and exhaust the three-bearing inventory at height one.
Consequently

    H_3=1 ==> t>=P-2,
               N_3=c1+t>=P+s-4>=57.                 (NF106)

This consumer uses the same existing thirteen-prime source premise
as NF73. The general addition is NF104--NF105's full-root inventory
charge; no new phase enumeration or height truncation is used.
These are ordinary mathematical deductions with no new Lean
verification. They do not bound the full mixed inventory from above,
and unrestricted Erdős #7 remains unresolved.

## 66. Promoting unused roots bounds the depth without increasing either replacement cost

Fix the actual family and weighted all-root interface of sections62--65. Let H be the maximum original q-height and D=H+1. Keep one chosen shallow frontier at depths at most H. Apply the existing free-folding rule to every remaining live H-prefix whose constant deep allowed list contains a zero-workload root. The other actual live H-prefixes form r hard parent jobs, with type counts r_A. All roots allowed in a hard type have positive integer workload R_a>=1 and nonnegative divided-modulus weight S_a. In the arithmetic interface these are the literal original root-batch count and weight.

For depths at least D, each hard job's allowed list is constant and every original same-depth collision list is empty. Roots may recur at different depths but each positive root occurs at most once at any one depth. The following normalization uses precisely these conditions. It does not require the distinguished root0 to belong to every list; that common-root property is needed for the separate static feasibility criterion NF99.

Every finite feasible hard frontier has another feasible frontier whose two costs are individually no greater and, when r>=1, whose maximum leaf depth is at most

    D+r-1=H+r.                                          (NF107)

Thus the short depth bound preserves an actual strict lexicographic budget improvement. It concerns general frontiers, not only the comb construction. When r=0 there is no hard cost and the free folds have depth at most D.

### A future root absent from the present layer can be promoted

Take a finite feasible hard frontier. Suppose a root a labels a leaf at depth e>d>=D but labels no leaf at depth d. The ancestor v of that leaf at depth d has not already stopped: otherwise the original frontier antichain could not contain the deeper leaf. The descendant frontier inside v partitions its entire actual cylinder.

Replace that whole descendant frontier by the single leaf v labelled a. Its constant allowed list contains a because the old deeper leaf used a in that same subtree. No other depth-d leaf uses a, so the new same-depth assignment is injective. At deeper levels this operation only deletes leaves; it creates no new capacity conflict. It preserves the complete partition and changes no shallow leaf.

The deleted cut contains the old a-labelled leaf and at least q-1 other leaves: a nontrivial complete q-ary subtree has at least q leaves. Its old count cost is therefore strictly larger than R_a. The new modulus-sum contribution is q^d*S_a, whereas the deleted old a-leaf alone contributed q^e*S_a. All other deleted contributions are nonnegative. Consequently this promotion strictly reduces the class-count cost and does not increase the modulus-sum cost.                      (NF108)

This change preserves the receiving node's actual q-prefix. Applying the established transport to the modified frontier still copies the output point's full original q-coordinate and cofactor coordinates into its one old witness and retains the literal divided p-tail. The promoted root is checked against the actual constant list at v, not against a different source. All new output q-heights are greater than H; original-label collisions remain absent. Same-depth root uniqueness retains the existing injectivity argument for transported numerical labels.

Repeat promotions while possible. The finite leaf count decreases at every step, so the procedure stops. Both accumulated costs never increase. In the resulting frontier, every root used at any later layer must already be used at each earlier active layer. In particular, if U_j is the set of roots used at depth D+j, then

    U_(j+1) subset U_j.

No optimal frontier has to be selected abstractly for this conclusion: the normalization starts from the supplied finite candidate.

### Nested root use forces the complete forest width to decrease

Let n_j be the number of hard nodes awaiting a stopping decision at depth D+j, and u_j=|U_j|. Since all remaining workloads are positive and same-depth labels are injective, u_j is exactly the number of leaves selected at that layer. The actual full q-ary expansion gives

    n_0=q*r, n_(j+1)=q*(n_j-u_j).

Every positive n_j is a multiple of q. The preceding normalization makes u_j nonincreasing. If at any nonterminal layer n_(j+1)>=n_j, then

    q*u_j <= (q-1)*n_j.

At every subsequent layer, the available selected-leaf count is at most u_j. Inductively the live-node count stays at least n_j and never decreases, so the finite frontier could not terminate. This contradiction shows that n_(j+1)<n_j at every active layer of the normalized frontier. Starting at q*r and decreasing in positive multiples of q, the forest completes in at most r layers. This proves NF107.

Reuse the earlier complete-forest Kraft bound. If k is the number of positive-workload roots, finite feasibility gives

    (q-1)*r<k,
    r<=floor((k-1)/(q-1)).

For the actual all-root interface, k<=p. Because p>q, floor((p-1)/(q-1))>=1 also accommodates the r=0 free-fold case. Every finite feasible candidate therefore has a cost-dominating representative with maximum depth

    H+floor((p-1)/(q-1)).                              (NF109)

At q=3 and odd p this is H+(p-1)/2. The bound is independent of the original class-count budget and is substantially smaller than the earlier general loop-erasure horizon. It preserves both costs, rather than merely asserting the existence of some feasible shallow replacement.

### The exact deep minimum uses a strictly decreasing count-state recurrence

For the fixed shallow choice and fixed free folds, collect hard nodes by their actual constant allowed-root type A. A state z=(z_A) means that the current layer has q*z_A pending nodes of type A. Initially z_A=r_A. An admissible stage chooses a subset of positive roots and injectively assigns each chosen root a to one pending node of a type A containing a. Write m_A for the number assigned to type A, so

    0<=m_A<=q*z_A,
    z'_A=q*z_A-m_A.

Restrict to assignments satisfying |z'|<|z|, where |z|=sum_A z_A. This restriction includes every stage of a normalized frontier. The layer costs are

    c=sum_(used roots a)R_a,
    s=sum_(used roots a)S_a.

The state retains all future constraints needed in this deep regime: actual nodes within one type have the same allowed list, original collision labels are absent, and root capacity resets at the next depth. Actual cylinders are still retained for reconstruction; the count state does not replace their source coordinates.

Let V(z) be the lexicographically minimum pair of remaining costs, with its second coordinate measured relative to the current depth. Use V(0)=(0,0), and the usual infeasible value if no completion exists. The standard finite-horizon Bellman principle gives the exact recurrence

    V(z)=min_lex [ c+V_C(z'), s+q*V_S(z') ],              (NF110)

over all admissible strict-width-decreasing assignments with a feasible successor. Its actual initial deep modulus-sum cost is q^D*V_S((r_A)); its deep class-count cost is V_C((r_A)). Add the previously fixed shallow costs before making the original lexicographic comparison. Free folds contribute zero.

Every recurrence path constructs an actual complete prefix cut: assign its roots to distinct literal pending nodes of their indicated types, stop those nodes, and split all others into their q children. When r>=1 its depth is at most D+r-1; for r=0 the hard cut is empty. Conversely, NF107 normalizes every arbitrary finite feasible candidate to such a path while increasing neither coordinate. The restricted recurrence therefore attains the same global minimum as the unrestricted finite deep-cut problem; it is not merely the minimum over combs or a newly imposed approximation. The multiplication by q in the second coordinate accounts for moving the remaining decisions one depth later.

NF110 is an application of the ordinary Bellman principle. The additional arithmetic interface is the proved cost-preserving normalization and the sufficiency of these actual deep type counts. No new generic dynamic-programming theorem, literature-priority claim or Lean verification is asserted. A hypothetical extremal odd cover must still be shown to admit some shallow choice and resulting minimum satisfying the strict original budget. This section makes that remaining price comparison a finite exact search with the stated depth bound for each fixed original family; it does not supply the missing uniform inequality or resolve unrestricted Erdős#7.

## 67. Residual subbatches use original-label capacity instead of whole-root capacity

These ordinary deductions and the finite local control carry no Lean verification or priority claim. They apply PH1–PH2 of report385 §1 to the exact original-label transport in §§61–62. Report350 §3 already supplies the relevant private-point indispensability principle; report354 SM3–SM5 retains the full prime tail on one common cofactor source. Reports378–379 supply actual residual laws and root-sensitive reciprocal prices, not upper bounds for the output-label inventories below. No generic set-cover or dynamic-programming theorem is proposed as new content.

### Exact residual and selected original labels

Keep one actual original family of distinct odd APs A_d=c_d mod d, with complete period p^A q^H M, p>q odd primes, A,H≥1 and gcd(M,pq)=1. Retain every p-free original unchanged. Select actual pure-q guards G including A_q and a finite q-prefix frontier B partitioning their complement U, exactly as in report385 §61. Write h_b for the depth of b. Put T=Z/p^(A−1) and X=T×Z/M. A larger output q-height is used when B extends past H; membership in retained originals always reads the original q digits.

For each leaf b define

    E_b={m mod M : some actual q-coordinate z_q in [b]
                     makes (z_q,m) miss every retained p-free original}.

This is an existential projection in the actual finite common carrier. In particular it is not the residual at one conveniently chosen q point, the intersection of all residual sections, or a residual recomputed with different phases. Every retained original is independent of the p coordinate, so the exact projected demand is T×E_b.

For each q-free p-bearing original d=p^alpha u, gcd(u,pq)=1, let a_d=c_d mod p, represented in {0,...,p−1}, and let C_d be the literal divided-tail AP on X:

    t=(c_d−a_d)/p mod p^(alpha−1),   m=c_d mod u.

Let D_a={d:q∤d, p|d, a_d=a}. For each leaf fix ONE root a_b, and select a subset J_b⊆D_(a_b). The exact local requirement is

    T×E_b ⊆ union_(d in J_b) C_d.                    (RS1)

Every selected pair (b,d) supplies the complete CRT AP

    z_q=b mod q^h_b,
    z_p=(c_d−a_b)/p mod p^(alpha−1),
    z_M=c_d mod u,

of numerical modulus q^h_b d/p. It is an entire AP, not its intersection with an uncovered set. All these residues come from that same original d.

For the declared frontier and selected subsets, RS1 at every leaf is NECESSARY AND SUFFICIENT for the retained originals plus these transported APs to cover the entire output carrier. Sufficiency takes an output point not covered by a retained original, reads its unique leaf, and applies RS1 to its actual (t,m). Necessity fixes any (t,m) in T×E_b, uses the q point in the definition of E_b, and notes that no transported AP attached to a different leaf can cover this point.

The same witness as NF86 is available: first-p root a_b, literal divided p-tail t, and unchanged q and M coordinates. RS1 says that at least one selected q-free original covers this witness. It is not enough merely to exclude mixed originals if some of the q-free originals are then omitted.

If a_b avoids the original mixed forbidden list F_b, whole original coverage supplies RS1 for J_b=D_(a_b), as in §62. One may keep this old cleanliness requirement and obtain a smaller-interface extension already. RS1 itself also permits a root meeting F_b when the chosen q-free originals nevertheless cover the complete projected demand; no claim is made that this additional possibility is always present.

### Numerical distinctness and the exact price

For strict collision reservation impose only these conditions:

    For every original d and depth h,
    #{b:h_b=h and d in J_b} ≤ 1.                     (RS2)

    For every selected (b,d), q^h_b d/p is not
    a numerical modulus of a retained p-free original. (RS3)

Equality of two transported numerical moduli first forces equal q-height because d/p is q-free, and then forces the same original numerical d. Thus RS2 is the exact transported-label distinctness condition. It is weaker than allowing a positive-workload root only once per depth: two same-depth leaves may use the same root if their selected subsets are disjoint. Original distinctness ensures that the same d has only one original phase and one original first-p root.

RS3 needs to be checked only for selected d. It can occur only at alpha=1 and an existing original label q^h_b u. A numerical collision arising from an OMITTED d is immaterial. Equal-complete-AP merging from §57 may be added separately; the formulas here use strict reservation and no merging.

Let P be all original q-free p-bearing labels, let t_mix be the number of original p*q-bearing labels, and let D_mix be their modulus sum. After the unchanged p-free originals cancel, the exact new cost is

    C_new=sum_b |J_b|,
    W_new=sum_b q^h_b sum_(d in J_b) d/p.              (RS4)

The exact old cost is

    C_old=t_mix+|P|,
    W_old=D_mix+sum_(d in P) d.                       (RS5)

For an EB1 extremal whole cover, PH2 therefore forces

    (C_new,W_new) ≥_lex (C_old,W_old)                 (RS6)

whenever RS1–RS3 hold. A strict reverse inequality supplies a legal distinct odd whole-cover descent. This is PH2's existing replacement argument applied to a more selective actual output family, not a newly forced arithmetic inequality.

The full-batch interface is the special case J_b=D_(a_b), with its old mixed exclusions and whole-root collision reservations. On a whole-cover input, every one of its feasible frontiers remains feasible here at exactly the same price. The new admissible choices include finer collision reservations and same-depth reuse with disjoint original subsets. The example below only separates these LOCAL choices; it does not compare the global optima of two complete frontiers on a whole-cover input.

### What the original private points do and do not force

Assume whole coverage and that a avoids F_b. For d∈D_a let P_d be its complete original private region, lifted to the common q-height used by the frontier. Then

    d is indispensable in D_a for demand T×E_b
    iff the q-projection of P_d meets [b].            (RS7)

Indeed, indispensability is exactly the nonemptiness of

    (T×E_b) intersect
      (C_d minus union_(e in D_a, e≠d) C_e).

Choose the q witness in E_b. The associated original point at root a misses every p-free original, every other q-free original at that root, every p-bearing original at another root, and every mixed original by the F_b hypothesis. It is private to d. The converse uses any such original private point and the same coordinate map.

Thus original irredundancy does not authorize deleting a label from every cylinder at its root: it forces a nonempty private q-projection somewhere. It also does not force that label into EVERY copy of the root batch. A label can be redundant on one actual q-cylinder and indispensable on another. This localizes the same private-point obstruction used in report350 §3 to a cylinder avoiding the actual mixed originals.

RS7 tests deleting ONE member of a complete root batch. Multiple deletions must satisfy RS1 jointly. Empty individual private regions do not justify deleting all those labels simultaneously: points covered only by two deleted labels are a joint obligation. This is exactly the distinction already present in PH1.

No estimate forcing the savings in RS4 to exceed the full-batch budget deficit follows here. Equivalently, with k_d=#{b:d∈J_b}, the count comparison is

    C_new−C_old=sum_(d in P)(k_d−1)−t_mix.

The missing result is an upper bound for these jointly feasible, phase-sensitive multiplicities for some complete actual frontier. Private-point existence alone provides indispensability constraints, not that upper bound.

### An 18-label actual local control

Take q=3, p=11, A=1, H=5 and M=35. Write a full CRT point as (z,r,s,a) modulo (243,5,7,11). The numerical palette is

    {3^j:1≤j≤5} union {5,7,11}
    union {3^j·5:1≤j≤3}
    union {3^j·7:1≤j≤5} union {55,77}.                (RS8)

It consists of 18 distinct odd nonunit labels, is divisor-closed above one, and has the initial odd-prime segment {3,5,7,11}. Its full period is 93555. Specify its actual phases as follows:

| Original label | Literal phase |
| --- | --- |
| 3,5,7,11 | zero modulo its prime |
| 3^j, 2≤j≤5 | 1+3^(j−1) modulo 3^j |
| 3^j·5, 1≤j≤3 | z=1 mod3^j, r=j mod5 |
| 3^j·7, 1≤j≤5 | z=2 mod3^j, s=j mod7 |
| 55 | a=1 mod11, r=4 mod5 |
| 77 | a=1 mod11, s=6 mod7 |

Every comparable pair of these original APs is disjoint. Their irredundancy can be verified without enumerating the full period. The following full CRT points are private witnesses; unspecified prime powers are read in the indicated full coordinates:

| Original label | Private point (z,r,s,a) |
| --- | --- |
| 3 | (0,1,1,2) |
| 3^j, j≥2 | (1+3^(j−1),4,6,2) |
| 5 | (1,0,6,2) |
| 7 | (2,4,0,2) |
| 11 | (1,4,6,0) |
| 3^j·5 | (1,j,6,2) |
| 3^j·7 | (2,4,j,2) |
| 55 | (1,4,1,1) |
| 77 | (2,1,6,1) |

The integer244 has coordinates (1,4,6,2) and is uncovered. This family is therefore a NONCOVER. It does not satisfy whole-cover EB1, the EB8 requirement of an exponent-one child at every nonzero p-root, or the known at-least-nine-primes whole-cover condition. Here only root1 has nonpure 11-bearing originals. The control tests local interface distinctions under the listed, verified structural conditions; it cannot refute a claim restricted to whole covers.

Retain all 11-free originals and select all five actual pure3 guards. The actual live cylinders

    b_1=1 mod3^6,   b_2=2 mod3^6

miss all these guards. Their retained residual projections are exactly

    E_(b_1)={(r,s):r=4, s≠0},
    E_(b_2)={(r,s):r≠0, s=6}.                        (RS9)

At b_1 the pure5 class and the three active 3^j·5 classes cover r=0,1,2,3, while pure7 removes s=0. At b_2, pure7 and the five active 3^j·7 classes cover s=0,1,...,5, while pure5 removes r=0. The other mixed row has the different first3 digit and is inactive.

Both 55 and77 have first11 root1. The selections

    a_(b_1)=a_(b_2)=1,
    J_(b_1)={55}, J_(b_2)={77}

satisfy RS1 locally, and RS2 because the subsets are disjoint. They produce the distinct fresh APs

    1459 mod3645,   2918 mod5103.

The old positive-root-per-depth condition rejects this fixed pair of root assignments. Copying both complete batches would instead repeat each numerical label3645 and5103 on two different, disjoint q cylinders. Thus original-label capacity is strictly less restrictive than root capacity on this actual local input. The union of b_1 and b_2 is only a small part of U; these two repairs are not a complete replacement frontier.

There is also a strict minimum-count comparison for this FIXED TWO-LEAF local problem, with one root per leaf, no further splitting, and coverage required only on these two actual residuals. Only roots0 and1 have nonempty batches; their full batches are{11} and{55,77}. Both cover either local residual. The old same-depth root capacity forces one use of each, giving minimum local class count3 and modulus sum9477. The selected-subset interface has minimum local class count2: each nonempty leaf requires a class, and the displayed split attains2. The split has sum8748, but it is not the smallest modulus sum at count2. Taking{55} at b_1 and{11} at b_2 instead gives(2,4374). This local minimum-count separation says nothing about optimizing a complete frontier on a whole-cover input.

The same family also separates selected-label collision checks. For this separate shallow comparison choose G to contain just the original pure3^j guards with1≤j≤4; every p-free original, including pure3^5, is still retained. The cylinder b=1 mod3^4 is then a live leaf. Its existential projected demand is still {(4,s):s≠0}; one old q lift is covered by the retained pure3^5 class but the other lifts retain that demand. Selecting only55 gives the fresh AP244 mod405. Copying77 as well would create modulus567, already occupied by the original3^4·7 with a different complete phase. Thus the whole-root collision list forbids root1 there, whereas the selected subset{55} legally covers the actual local demand.

For a local price comparison with the old root-reuse capacity satisfied, instead use b_1=1 mod3^6 and b_2=2 mod3^7. The two complete root1 batches have local cost(4,34992), while subsets{55} and{77} have local cost(2,18954). All four unpruned numerical labels are then distinct and fresh. This compares the displayed local assignment only, not full-frontier minima.

### Finite scope and the boundary of the existing normalization

Beyond original height H, every H-prefix has a constant retained residual projection; its selected-subset menus are therefore constant. At depths at least D=H+1 all numerical output labels are fresh relative to the retained originals. This supplies an actual finite type description, but not by itself a uniform depth bound.

The earlier count-budget horizon argument in §63 DOES reuse directly. Collapse every residual-empty depth-D subtree to a single empty-subset leaf at depth D. For a lexicographically successful candidate C_new≤C_old. In a nonempty residual type every remaining leaf has |J_b|≥1. A leaf of depth D+e forces at least1+(q−1)e leaves below its depth-D ancestor, hence

    maximum depth ≤ H+1+floor((C_old−1)/(q−1)).        (RS10)

This follows from the existing complete q-ary cut count. Deleting an empty subtree creates no label collision, and no assumption about root batch weights is needed. It is an existence-preserving finite bound under the same count budget, not a proposal to enumerate all candidates.

The sharper §66 bound H+floor((p−1)/(q−1)) is NOT established for these selected-subset interfaces. Its proof promotes an entire future root batch whenever that root is unused in the present layer, then obtains nested root use. Here promotion is valid when every original label in the future selected subset is unused in the present layer, but a future subset may partly intersect labels already used there. The old nesting proof consequently does not transfer merely by changing R_a to a local price. No failure or replacement sharp bound is claimed.

### The unresolved whole-cover comparison

The useful refinement is exact retained-residual demand with selected original-label capacities and selected-only numerical collision checks. The general replacement and single-private-point logic are existing results. The missing global step remains to force a complete frontier satisfying RS1–RS3 below the original two-coordinate budget on a hypothetical extremal whole cover. The local control and finite bound do not supply that inequality or resolve unrestricted Erdős#7.

## 68. Private-prefix concentration forces distinct mixed inventory at all heights

This is an ordinary consumer of Report385 PH3–PH5, its stronger descendant-assisted DR3–DR4, and the original private-point map in Report350. It does not supply the unrestricted price-descent theorem, new generic set-cover mathematics, Lean verification, or a literature-priority claim.

Fix one EB1-selected whole distinct odd cover with original numerical set D, complete period Q=p^A q^H M, p>q, A,H≥1 and gcd(M,pq)=1. Keep the actual original phases, with the prime classes simultaneously normalized to residue zero. Let P_d be the complete original private region of d and let W_d be its projection to Z/q^H. Every W_d is nonempty. For a q-free p-bearing original write d=p^alpha u, gcd(u,pq)=1. All inventory counts below refer to this one original family.

### At original q-height one the mixed-root obstruction is exact

First suppose H=1. For each nonzero original q-root j, every receiving leaf b contained in j has the same actual residual Γ_j=T×E_j, whatever its new depth. For a fixed original p-root a let D_a be its q-free p-bearing batch. Then

    union_(d∈D_a) C_d covers Γ_j
      iff no original p*q-bearing label has roots(a,j). (PI0)

This ignores numerical output collisions, which remain a separate condition. For the forward implication, a mixed original in cell(a,j) has an original private point. Its divided p-tail and cofactor belong to Γ_j, and no q-free original at root a covers them. At H=1 the q coordinate j is complete, so this same obstruction persists in every new receiving descendant of j. For the reverse implication, whole coverage of the common original witness supplies a q-free p-bearing owner at root a whenever the retained originals miss the output. Thus its entire batch covers Γ_j. This reuses the original private-point witness and the existing common source; it does not extend to a lower-height mixed prefix inside an arbitrary larger original H without checking its actual private projection.

### A common injective charge at all original heights

Let M_d be the largest original numerical multiple of d. Say d has a crowded descendant phase when some actual proper-descendant residue group J_c from §10 contains at least two labels. Define

    L_d={h:1≤h≤H, W_d is contained in one actual
             residue class modulo q^h, and
             [q^h d/p<M_d or d has a crowded descendant phase]}.

The residues witnessing containment are coherent prefixes because they concern the same nonempty W_d. Thus L_d is an initial segment, possibly empty. No private witness is chosen separately for different h.

For every h∈L_d, DR3 or DR4 forces the original numerical label

    g(d,h)=q^h d/p                                    (PI1)

to be present. Indeed all of P_d has the original residue modulo d and one residue modulo q^h. Since gcd(d,q)=1, it lies in a single AP modulo q^h d, so g(d,h) divides its complete private congruence hull Γ_d. Also g(d,h)|Q and g(d,h)>1. DR3 applies below M_d, and DR4 applies without a size threshold when its actual crowded-group premise holds. The simpler sufficient condition q^h<p gives g(d,h)<d≤M_d and is exactly the old PH5 route. No new private-hull closure theorem is asserted.

The map (d,h)↦g(d,h) is injective: q valuation recovers h and multiplying the remaining q-free quotient by p recovers d. This is a count of actual labels in this one original family, rather than one independently selected repair for each pair.

If alpha≥2, every image is a p*q-bearing original, so the SAME mixed inventory supplies both bounds

    sum_(d:q∤d, v_p(d)≥2) |L_d| ≤ t_mix,

    sum_(d:q∤d, v_p(d)≥2) (d/p) sum_(h∈L_d) q^h
           ≤ D_mix.                                  (PI2)

For L_d={1,...,ell_d}, the inner weight is q(q^ell_d−1)/(q−1). All terms are simultaneously realized by the injective map PI1; count and weight are not obtained from separate optimizers. Original g phases need not agree with the hull phase and are not used as replacement covers.

If alpha=1, the image q^h u is p-free and therefore belongs to the RETAINED inventory. It cannot be charged to t_mix or D_mix. Moreover it creates a strict numerical collision for any attempted depth-h copy of that same original d, irrespective of the copied residue. Thus a selected collision-safe depth-h exponent-one copy, whenever the stated DR3 or DR4 threshold applies, requires W_d to meet at least two q^h prefixes. This conclusion concerns the complete original private region, not only an individual private witness or the private region of a selected subcover.

### Ternary height-one consequence for the current subbatch interface

Suppose q=3,H=1. Every W_d for q-free d misses root0 because the original pure3 class is retained and disjoint from every original private point. Hence W_d is one of {1},{2},{1,2}.

For d=pu, if original label3u is absent, PI1 excludes the singleton cases, so

    W_(pu)={1,2}.                                    (PI3)

Every valid q-free subbatch at the first-p root of d, on ANY descendant of either original nonzero3-root, must then include d. The original private point at that3-root gives an element of the constant demand Γ_j=T×E_j covered by no other q-free label at that p-root. This necessity does not require excluding mixed originals; if mixed originals block the entire demand, no valid subbatch exists in the first place.

Consequently every strict-collision-safe exponent-one label available to a depth-one subbatch is compulsory at BOTH original3-roots whenever that same p-root is used. All such selected shallow labels therefore remain compulsory if that root is reused at deeper leaves elsewhere. This is stronger than treating the shallow copy as an arbitrary freely replaceable set-cover column.

More generally, whenever original3d/p is ABSENT for a q-free p-bearing d of any p-height, PH5 excludes a singleton W_d, so that d is compulsory in every valid subbatch at its p-root on either ternary branch. Thus any same-depth reuse of a positive-demand p-root, even across the two different original ternary branches, requires3d/p∈D for every d of that root batch. This is a necessary condition, not a sufficiency test: an already present crossed label does not imply absence of private demand.

There is a second consequence for same-depth root reuse. If one p-root a is assigned at least two receiving leaves at the same depth, even in DIFFERENT original ternary branches, then

    W_d is a singleton for every d∈D_a.               (PI4a)

For otherwise a d whose W_d={1,2} is compulsory at both leaves, violating RS2. If the two leaves are in the SAME original3-root j, the stronger conclusion is that no d∈D_a can have a private q-projection meeting j, and hence

    W_d={other root} for every d∈D_a.                 (PI4)

Either PI4a or PI4 supplies original3d/p for EVERY d in that actual root batch, using PI1 at h=1. Its exponent-one members have retained collision labels, and its higher-p members have pairwise distinct mixed labels. In particular

    #{d∈D_a:v_p(d)≥2} ≤ t_mix,
    3 sum_(d∈D_a:v_p(d)≥2) d/p ≤ D_mix.              (PI5)

If several roots admit such same-depth reuse, their original D_a are disjoint, so PI5 holds with their UNION in place of a single D_a. The injective map gives one shared budget; it is not legitimate to add separate copies of t_mix for those roots.

If this same p-root were also used in the other original3-root, every member of D_a would be compulsory there by PI4. A strict-collision-safe depth-one subbatch in that other root therefore cannot coexist with even one exponent-one member of D_a. This last condition becomes useful only after independently checking that such a member exists; EB8 alone may supply a mixed exponent-one child instead of a q-free one, so it must not be silently upgraded.

### Nonmaximal concentrated labels also have full mixed children

Now take q=3 and allow ANY original height H≥1. Write V_d for the projection of the complete P_d modulo3, equivalently the first-root projection of W_d. If a3-free original d has singleton V_d and ANY proper original multiple, then

    3d∈D.                                            (PI6)

Here d may have p exponent one. Since P_d is concentrated in one ternary root,3d divides Γ_d. The largest original multiple M_d has odd quotient M_d/d≥3. If M_d=3d then the claimed label is already present. If M_d>3d, apply the existing DR3 with e=3d. This proof uses the smallest odd prime3; a proper multiple at ratio3 would not imply the analogous q-child statement for an arbitrary larger q.

The map d↦3d is injective. Therefore for the single set N of ALL3-free p-bearing originals with singleton V_d and a proper original multiple,

    |N|≤t_mix,       3 sum_(d∈N)d≤D_mix.              (PI7)

This supplies actual mixed payers for concentrated exponent-one labels as well, provided the original descendant exists. In particular, if pu is concentrated and p^2u is original, its mixed child3pu is forced. More generally the proper multiple can have any odd composite ratio and any original phases.

PI2/PI5 and PI7 are TWO separately valid injections into the same inventory. Their right-hand sides cannot simply be added. For example the payer3d from PI7 coincides with the PI1 payer3d'/p when d'=pd. Both are actual original q-free labels in such a case; phase or root distinction does not make their common numerical payer two labels.

Every concentrated q-free p-bearing label is therefore in one of these classes: nonmaximal labels have the PI7 mixed payer; divisibility-maximal labels of p-height at least two have the PI1 mixed payer; divisibility-maximal exponent-one labels pu have only the proved retained payer3u. This classification provides actual possible payers, not a collision-free joint allocation between the two mixed-payer maps.

### The two mixed-payer maps can be combined column by column

The preceding collision can be resolved except for one explicit case per actual p-column. Keep q=3, ANY H≥1, and FIX the same p throughout. Concentration in this section means singleton V_d modulo3; W_d need not be a singleton modulo3^H. For each u with gcd(u,3p)=1 for which p*u is original, define

    A_u=max{alpha≥1:p^alpha*u∈D},
    S_u={alpha:1≤alpha≤A_u, V_(p^alpha*u) is a singleton}.

Divisor closure supplies every actual q-free level1,...,A_u. A label at level alpha in S_u has the following proved mixed-payer choices:

    alpha≥2:        3*p^(alpha−1)*u;
    nonmaximal d:   3*p^alpha*u.                     (PI8)

Here nonmaximal means that d has a proper ORIGINAL numerical multiple, which may have another cofactor. Every level alpha<A_u is nonmaximal. The right-hand levels are numbered by the p exponent of the mixed payer, and are at least one.

Choose the payers simultaneously by this explicit rule.

- If1∉S_u, give every alpha∈S_u its lower payer at level alpha−1.
- If1∈S_u and the initial consecutive run is1,...,r with r<A_u, give this initial run the same-level payers1,...,r. Those originals are nonmaximal because their next q-free p-level exists. Give every remaining alpha∈S_u its lower payer at alpha−1; since alpha≥r+2, these right-hand levels exceed r.
- If S_u is the whole column and the top p^A_u*u is nonmaximal, give every level its same-level payer.
- If S_u is the whole column and its top is divisibility-maximal in D, give alpha<A_u their same-level payers and leave precisely the top unpaid.

Within each case the payer levels are different. Between different u, their numerical3-free and p-free parts recover u, so their mixed labels cannot collide. Every payer exists by PI8. Thus there is one common injection from all concentrated q-free p-bearing originals EXCEPT those declared unpaid top labels into the original mixed inventory.

More precisely, let L be the set of all3-free p-bearing originals with singleton V_d and let K be the set of columns satisfying the last case. Let U_top={p^A_u*u:u∈K}. Write t_mix,1 and D_mix,1 for the count and modulus sum of original p*3-bearing labels with v_3=1. The explicit payer map χ obeys

    χ:L minus U_top → {d∈D:p divides d, v_3(d)=1} injectively,

    |L|−|K|≤t_mix,1≤t_mix,
    sum_(d∈L minus U_top) χ(d)≤D_mix,1≤D_mix.                (PI9)

These count and weight statements use the SAME payer map. In a bad column, its mixed levels1,...,A_u−1 are all forced by the lower map. A mixed level A_u or greater with this same u cannot occur: it would be a proper original multiple of the declared maximal top. Consequently the column has exactly A_u−1 possible mixed payers of3-height one with this cofactor for its A_u concentrated labels. The one-label shortage is exact for these same-cofactor,3-height-one inventory payers; it is not a proof that another global payment or cover transformation cannot handle the top.

When H=1, the union of root batches admitting the same-depth reuse in PI4a is a subset of L. Restricting this one χ pays that union except for the bad top labels actually belonging to it; no second inventory budget is created.

When u>1, the original divisor u is p-free and retained, so it cannot be counted as an unused DELETED label. When u=1, it is not an admissible nonunit label. The one pure-p label also supplies at most one actual credit if it is unused, not one credit for each bad column. No argument here shows that U_top is unused in a constructed frontier.

### Full mixed children have separate actual private obligations

Keep q=3 and arbitrary original height H. Fix one p-column x_alpha=p^alpha*u, 1≤alpha≤A_u, from PI8. Select any set I of levels for which V_(x_alpha) is a singleton and the full mixed child y_alpha=3*x_alpha is original. PI6 supplies that child whenever the parent has a proper original multiple. Then all the actual original classes

    {A_(x_beta):1≤beta≤A_u}
       union {A_(y_alpha):alpha∈I}

are pairwise disjoint. This is an application of the existing crowded-phase prohibition DR5, with the original phases unchanged; the selected parents need not have the SAME private ternary root.

For beta≤alpha, x_beta divides y_alpha, so original comparable-class disjointness applies. If beta>alpha and A_(y_alpha) meets A_(x_beta), the two proper original multiples y_alpha and x_beta belong to the same residue group modulo x_alpha. That group has at least two members. But concentration gives y_alpha|Γ_(x_alpha), and DR5 forbids a member of such a crowded group from dividing the parent's complete private hull. This contradiction handles every cross pair. The x labels form one divisibility chain and the y labels form another, so all pairs within each chain are already disjoint.

For a bad column in PI9, take I={1,...,A_u−1}. The resulting2*A_u−1 original classes are therefore pairwise disjoint, at arbitrary ternary height and even when their private roots differ. For ANY subset J of these labels, PH1 simplifies exactly to

    E_J = union_(d∈J) P_d.                           (PI10)

Indeed, whole original coverage ensures that a point missing every retained class lies in some removed class; disjointness means it belongs to exactly one removed class and hence to that class's COMPLETE original private region. The converse follows from privacy. This equality concerns this proved disjoint subfamily; it does not replace PH1 by a union of private regions for general deletion sets.

When A_u≥2, moving the parent x_(A_u−1) to the top x_(A_u)'s residue does not free the already matched child y_(A_u−1). Their original APs are disjoint and their gcd is x_(A_u−1), so their residues modulo that parent differ. In DR2's notation, y_(A_u−1) is not in the removed phase group J_c. The lower y levels are not multiples of this adjacent parent, so that group frees none of the matched ternary-height-one y labels from this column. Higher ternary-height mixed originals are not excluded by this argument. The top itself has no proper original multiple and cannot directly serve as a DR2 parent.

Deleting an additional matched mixed original is legal only with its own nonempty private region included in the joint repair obligation. PI10 makes that extra obligation exact; it does not prove that no different global replacement can repair it. Thus these original mixed labels are inventory witnesses, not unoccupied labels whose phases can be reassigned without paying for their old private points. No free elimination of the exceptional top follows.

### Boundary of the payment

PI2, PI5 and the deduplicated PI9 are actual original-inventory bounds and may pay for suitably identified copies. They do not yet prove the count-saving inequality

    sum_d(k_d−1)<t_mix

for a complete feasible frontier. Existence is itself unresolved: no result here forces the §64 Hall criterion for every whole cover or guarantees a complete frontier satisfying RS1–RS3. In particular, at original ternary height one, a required deep branch with at most two allowed roots has no finite complete frontier under the original per-depth root capacity; the broader subbatch capacity requires its own existence argument. No argument here puts EVERY repeated label into the concentrated class above, or bounds each such label to one extra occurrence. In particular a label whose private projection meets both ternary roots may recur at different depths; PI1 supplies no mixed payer for that recurrence. Concentrated divisibility-maximal exponent-one labels have only the proved retained payer unless another global argument supplies a distinct credit. A payer cannot be charged once for each appearance of the same original label. Nor are the payer sets for different observing primes p automatically disjoint.

The old theorem interface is PH5 or the stronger DR3–DR4 on the actual complete private hull, followed by an injective numerical map into the same deleted or retained inventory. Depths with q^h≥p are available when the verified descendant threshold or crowded phase permits them; they are not an absolute exclusion. The remaining bridge is to construct a complete source-preserving frontier satisfying RS1–RS3 whose extra occurrences can be injected into a properly deduplicated choice of the PI2/PI9 payers plus unused original labels, with an unspent class credit or a strict common weight saving. That global construction has not been obtained.

## 69. Cross-cofactor divisor payment reduces exactly to nonconcentrated ancestors

Keep section68's one EB1-selected original whole cover, a fixed support prime p>3, and arbitrary original ternary height H≥1. Let V_d be the projection of the COMPLETE original private region P_d modulo3. Define

    P={d∈D: p divides d and 3 does not divide d},
    L={d∈P: V_d is a singleton},
    G={d∈L: d has no proper numerical multiple in D}.

All sets retain the original numerical labels and actual private regions. This section reuses PH5, PI6, finite Hall matching, and Report357's actual first-prime reset. It supplies an exact reduction of the inventory-payment deficit, not a new Hall theorem, a legal replacement cover, or new Lean verification.

### Proper divisors supply actual payers across cofactor columns

If d∈L and e is a proper p-bearing divisor of d, then3e divides Γ_d. Since d is odd and3-free, d/e≥5, so3e<d. PH5 therefore supplies the ORIGINAL label3e. If d∈L\G, PI6 also supplies3d. Thus the available divisor-payment relation is

    d → 3e  when e∈P, e|d, and [e<d or d∉G].       (DP1)

Every right label has ternary height exactly one and still contains p. In particular, removing a prime from the cofactor of d does not turn this payer into a retained p-free label when the divisor e still contains p. The crossed-divisor closure itself is already PH5/PH7; its simultaneous inventory matching is the present consumer. Actual payer phases are not prescribed and these labels are not asserted to cover any transported demand.

For S⊆L write

    down_p(S)={e∈P: e divides some d∈S}.

Identify a right label3e by its unique index e. The EXACT neighbor set is

    N(S)=down_p(S) minus (S∩G).                     (DP2)

Every proper divisor is supplied by DP1; each nonglobal-maximal member has its self index. A globally maximal member of S can be neither its own neighbor nor a proper divisor of another member. This proves both inclusions without adding hypothetical numerical labels.

### Only maximal concentrated labels need nonconcentrated ancestors

Finite Hall deficiency, applied to this one graph, now becomes

    δ=max_(T⊆G) [ |T|−|down_p(T)\L| ],             (DP3)

with T=empty contributing zero. To obtain this exact reduction, start with S⊆L and add all its concentrated ancestors, replacing it by L∩down_p(S). This keeps down_p(S) and S∩G unchanged and cannot reduce its deficiency. Put T=S∩G after this completion. Deleting the elements outside down_p(T) leaves the same globally maximal labels and can only shrink the nonconcentrated ancestor set. The resulting deficiency is precisely the expression in DP3. Conversely each T realizes that expression with S=L∩down_p(T).

Consequently the maximum number of concentrated labels receiving DISTINCT DP1 payers is exactly |L|−δ. Equivalently, all of L can be paid if and only if the globally maximal labels G can be matched injectively to NONconcentrated proper p-bearing divisors:

    d∈G → e_d∈P\L,  e_d|d,  e_d different.        (DP4)

Indeed, match as many elements of G as possible by DP4, and pay every d∈L\G by its self label3d. These images are disjoint because their indices lie respectively outside and inside L. The Hall deficits of the two graphs agree by DP3, so this construction attains |L|−δ, not merely a sufficient submatching.

For the resulting single matching χ, let L_paid be its domain. With section68's actual ternary-height-one inventory,

    |L_paid|=|L|−δ≤t_mix,1,
    sum_(d∈L_paid) χ(d)≤D_mix,1.                   (DP5)

Count and weight use the SAME actual labels. The earlier column matching is contained in DP1, so δ≤|K| for section68's bad-column set K. Cross-cofactor divisors can remove an earlier column deficit only through these shared nonconcentrated ancestor slots; neither a retained cofactor nor repeated use of one slot supplies another credit. DP3 restricts deficient sets to ideals generated by selected maximal labels. It does not identify each such ideal with the entire original p-bearing palette.

### The actual private reset gives two different whole-cover branches

Report357's first-p reset sends every original P_d with p|d, d≠p into P_p while preserving ALL other prime coordinates, including the full ternary coordinate. Hence

    V_d⊆V_p  for every original p-bearing d.         (DP6)

The case d=p is the identity. This is a direct consumer of that existing map; it is not an inference from a marginal bound.

If p∈L, DP6 gives L=P. There are then NO nonconcentrated ancestors and

    p∈L ==> δ=|G|.                                 (DP7)

In this branch every q-free p-column is concentrated. Its unpaid top in section68 is precisely a member of G, so DP7 equals the old column deficit: the enlarged divisor graph gives no improvement here.

The whole-cover condition used in the other branch is explicit. EB8 supplies an original exponent-one child pm with m>1 on every nonzero first-p branch. Thus p has a proper original multiple and is never in G. Consequently if p∉L, the numerical label p is a nonconcentrated PROPER divisor of every member of G. Every nonempty T⊆G has at least this one common neighbor, giving

    p∉L ==> δ≤max(|G|−1,0).                        (DP8)

This is only one shared slot, represented by the actual deleted mixed label3p whenever G is nonempty. It cannot be counted once per top or once per cofactor column. Other nonconcentrated divisors may strengthen DP8 through DP3, but their required simultaneous abundance has not been proved.

The p∈L branch also has an exact existing source interpretation. Write R_p for the actual cofactor region avoiding ALL p-free originals. Then P_p={0}×T_p×R_p, so p∈L means that R_p lies in one nonzero ternary first-root class. EB8 and PI6 supply3p; its actual private witness fixes that same ternary residue. Report364 SI1 therefore identifies

    p∈L iff 3 is an original singleton cofactor color in F_p. (DP9)

Report364's singleton-root capacities allow this color; the associated prime-parent swap is a whole-family first-p-root permutation and preserves the numerical inventory, class count and modulus sum. Those existing results do not exclude DP7 or produce an extra payment.

### Nonconcentrated pure powers pay additional bad columns without collisions

The original pure p-powers cannot be globally maximal numerical labels. This reuses the existing original top-fan argument, not a new essential-modulus theorem. Write A_*=v_p(Q). If a<A_*, divisor closure supplies the proper original multiple p^(a+1). For a=A_*≥2, [Report371, section2](371-private-top-fans-and-ancestor-cuts.md#2-the-private-top-fan-has-an-escaping-first-ancestor) supplies actual top mixed labels p^A_*u with u>1 from the pure top's private point. For A_*=1, Report350 EB8 supplies an original child pu with u>1. Consequently

    p^a∉G for every original pure p-power.            (DP10)

Let B=U_top be section68's set of bad column tops, so |B|=|K| and B⊆G. For each t=p^A_u*u in G\B, its p-column is not entirely concentrated. Choose a nonconcentrated original layer e_t=p^beta*u in that same column. Since t is concentrated, beta<A_u. Different tops here have different u, and DP10 ensures u>1. Hence these chosen e_t are distinct NONPURE members of P\L, and DP1 supplies their actual mixed payers3e_t.

Pay every nonmaximal d∈L\G by its self label3d. Those payer indices are in L, while all e_t are outside L, so this assignment has no collision. It pays every concentrated label except B without using any nonconcentrated PURE p-power as a payer index.

If L≠P, DP6 gives p∉L. For any t∈B, DP10 ensures p is a proper divisor of t. Give one such top the additional payer3p. It is supplied by DP1, differs from all nonpure3e_t, and cannot equal a self payer since p∉L. Thus the same original family satisfies the sharper bound

    L≠P ==> δ≤max(|K|−1,0).                         (DP11)

Unlike DP8, this retains section68's bad-column count |K| rather than the potentially larger |G|. In particular a solitary bad column is fully paid whenever p is nonconcentrated. There is one3p slot in this injection, not one per bad column.

More generally retain the full set of nonconcentrated pure-power indices

    I_0={a:1≤a≤A_*, p^a∈P\L}.

After paying G\B and L\G as above, a bad top t can use a slot a∈I_0 precisely when a≤v_p(t). Its actual payer is3p^a; DP10 makes p^a a proper divisor of t, so DP1 supplies it. Slots which neighbor no top need not give original mixed labels and are not used. All used pure-power payers are distinct and disjoint from both earlier image groups.

These remaining neighborhoods are nested initial segments. The existing finite Hall deficiency formula therefore gives their exact unmatched count

    ε_0=max_(0≤h≤A_*)
        [ #{t∈B:v_p(t)≤h} − #{a∈I_0:a≤h} ],

    δ≤ε_0.                                           (DP12)

The h=0 term is zero. Indeed any nonempty set of bad tops has a largest p-height h and has exactly the eligible slots I_0∩[1,h]; including all bad tops of height at most h can only increase its deficiency. Conversely, if a threshold h contains no top of height exactly h, lowering it to the largest present top height preserves its top set and can only remove slots. Thus the threshold maximum is the exact deficiency of this restricted pure-power assignment. A matching can be obtained by processing tops in increasing p-height and using the smallest unused eligible exponent.

DP12 is an upper bound for the FULL divisor-graph deficit δ; other nonconcentrated cofactors can improve it further. The formula also applies when L=P: then I_0 is empty, B=G, and it recovers ε_0=|K|=δ. If L≠P, the available index1 pays at least one nonempty bad-top set and recovers DP11.

This constructs one common injection paying |L|−ε_0 labels, so its actual count and modulus-sum bounds are those of DP5 restricted to this injection. It does not pay repeated occurrences of a label repeatedly. In particular, a depth-h transported copy of d costs3^h*d/p, whereas a payer3e dominates it termwise only if d/e≤p/3^(h−1). The divisor edge alone supplies no such price comparison. Numerical inventory payment also leaves each occupied payer's original private liability intact.

### The remaining bridge is a source constraint on ancestor expansion

The exact unpaid amount for this divisor relation is DP3. Closing it requires enough DISTINCT nonconcentrated ancestors for every selected set of concentrated maximal labels, or a different actual inventory payment or legal whole-family transformation. PH5 supplies the candidate labels and the private reset supplies DP7–DP9, but neither forces that expansion. In particular the concentrated-prime branch has no such ancestor at all unless G is empty; G=empty has not been proved in that branch.

Even δ=0 would only settle this inventory payment for one copy of each concentrated label. It would not construct a complete frontier satisfying RS1–RS3, put every repeated label in L, control multiple extra occurrences of one label, or establish the required strict joint count/weight descent. These remain separate obligations for the same actual original family.
## 70. Concentrated prime-private roots require both ternary colors

Keep one EB1-selected original whole distinct odd cover with full period Q=3^H M, H≥1 and gcd(3,M)=1. Normalize the original prime classes by the existing common translation. For every original label d, let V_d be the projection modulo3 of its COMPLETE original private region. It is nonempty. For each support prime p>3, V_p is a nonempty subset of {1,2}; call p concentrated of color i when V_p={i}. No assumption makes the complete projection modulo3^H a singleton.

The private reset is Report357's actual coordinate map, already used in DP6. The separator identity below is reused from section57 and problem detail17. The new consumer is that concentration of every nonternary prime cannot have only one color. It does not settle unrestricted Erdős#7, give a new separator theorem, or provide Lean verification.

### Different concentrated colors cannot occur in one original label

Let p,r>3 be two concentrated support primes of different colors. If an original d were divisible by both, its actual private witness could be reset at p and, separately from the same witness, at r. Each reset preserves the complete ternary coordinate. Hence

    V_d ⊆ V_p ∩ V_r = empty,

contrary to irredundancy. Therefore

    V_p∩V_r=empty ==> no original d is divisible by pr. (CP1)

This includes originals divisible by3 and every higher prime power. The two resets are separate applications to the same private source, not a claim that a successive reset remains private to the second prime. Unconcentrated primes may still occur in the family and share labels with concentrated primes. Thus CP1 alone does not split the full nonternary support when unconcentrated primes remain.

### A single concentrated color would make the original pure3 class redundant

Suppose every support prime p>3 is concentrated and all have color i. Every original d which contains both3 and some nonternary prime then has actual first-three root i: reset its private witness at that prime. Its AP fixes that same first root.

Let j be the other nonzero ternary root. No such mixed original meets j. The original pure3 class lies at root0. The remaining pure-three labels have heights h≥2. In the full ternary carrier their total number of covered words is at most

    sum_(h=2..H) 3^(H-h)
       = (3^(H-1)−1)/2 < 3^(H-1).                  (CP2)

There is therefore a COMPLETE ternary word z of first root j covered by no original pure-three class. At this word no3-bearing original is active. Whole coverage forces the original3-free subfamily to cover every remaining cofactor coordinate. Because that subfamily is independent of the ternary coordinate, it already covers the entire original carrier, contradicting the private point of A_3.

The empty nonternary-support case is also impossible: finitely many distinct pure-three powers cannot cover, by the same bound. Consequently

    every p>3 concentrated ==> both colors occur.     (CP3)

This argument retains arbitrary original ternary height and does not move phases or replace the original family by separately chosen completions.

### Both colors give two actual conditional quotient covers

In the all-concentrated branch write S_1,S_2 for the two nonempty sets of support primes. CP1 implies that every original modulus with a nonunit3-free cofactor has that cofactor supported entirely in one S_i. Put

    X_i=product_(p∈S_i) Z/p^H_p,

using the complete original heights. Let C_i⊆X_i be the union of the original3-free classes supported in S_i. A private point of the original A_3 avoids all3-free originals, so BOTH complements X_i\C_i are nonempty.

For a complete ternary word z, let B_i(z) be C_i together with the actual cofactor classes of all group-i3-bearing originals whose full ternary prefix contains z. Assign each pure-three original to the common guard set Z_pure. The existing exact-separator identity gives the literal uncovered set at each z∉Z_pure as

    (X_1\B_1(z)) × (X_2\B_2(z)).                   (CP4)

If z has first root i, every group-(3−i) mixed original is inactive, so B_(3−i)(z)=C_(3−i). Its complement is nonempty. Whole coverage in CP4 therefore forces

    B_i(z)=X_i
      for every z∉Z_pure with first-three root i.     (CP5)

CP2 ensures that each root supplies at least one such complete z. Thus the two conditional quotient covers are forced by this ONE original family. They use different ternary words and are not two independent candidate families which may be combined freely.

CP5 is not yet a smaller distinct odd cover. On fixing the complete3-coordinate, original labels m and3^h m can project to the SAME cofactor modulus m with different actual residues. Even retaining the ternary tail and only restricting to one first root sends m and3m to two classes of modulus m. Divisor closure supplies the original parent m whenever3m occurs with m>1; comparable disjointness makes their two phases different rather than deleting either one. Removing the opposite group instead leaves its other ternary branch uncovered. The established separator identity therefore identifies the required conditional covers but does not supply the missing legal numerical-label transformation.

### At ternary height one the two colors must separate5 and7

Now additionally assume H=1. Fix the complete ternary word i for each color group. The quotient family in CP5 has odd moduli greater than one, all coprime to3, and at most TWO classes for each numerical cofactor m: only the original labels m and3m can project to it. Its nonternary prime-power heights remain arbitrary.

[Report348, section3](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#a-two-copy-seed-coprime-to-6-must-use-5-or-7) already proves that a finite family with each numerical modulus used at most twice cannot cover when its period is coprime to210. Applying that existing result to each actual quotient cover shows that each S_i contains5 or7. Because S_1 and S_2 are disjoint,

    H=1 and every p>3 concentrated
       ==> 5 and7 have opposite concentrated colors.  (CP6)

This directly reuses Report348's unrestricted-height multiplicity-two result and its existing arithmetic evidence; no sieve or endpoint computation is repeated. At H>1, fixing a complete ternary word can retain more than two original3-heights at one cofactor modulus, so the same application is not justified. CP3–CP5 retain their arbitrary-H scope.

### The existing flat construction constrains both original group budgets

Still assume H=1 and all nonternary primes concentrated. For group i let f_i count its original3-free labels and b_i count its original3-bearing labels. Divisor closure supplies a distinct parent m for every original3m, so b_i≤f_i. Let n_i=f_i+b_i. The original whole family contains exactly1+n_1+n_2 labels, including pure3.

Use the actual group-i quotient from CP5 as Report348 section3's two-copy seed. In CRT coordinates, retain the original3-free classes, place each original3m class at first-three root2 with its original mod-m residue, and add0 and1 mod3. The quotient-cover identity CP5 verifies the remaining root2. This is the existing seed interface with only numerical3 repeated exactly twice, so Report348 section2 applies.

Any prime ell in the opposite group is fresh for this seed. In the four output families of that existing construction there are respectively ell−1 pure3 labels, ell fresh-ell closing labels, f_i retained3-free labels, and (ell−1)b_i transported mixed labels. All distinctness and coverage conditions are those already proved in Report348; the opposite color supplies its freshness hypothesis. Thus EB1 requires

    n_(3−i) ≤ (ell−2)b_i+2ell−2
      for every ell∈S_(3−i).                         (CP6a)

A strict reverse inequality would give an actual smaller distinct odd cover, not only a projected collision count. In particular, name the two groups by which of5 and7 they contain, as CP6 permits. Choosing the smallest prime in each opposite group gives

    n_7 ≤ 5*b_5+12,      n_5 ≤ 3*b_7+8.              (CP6b)

These two necessary inequalities concern the SAME original cover. They do not assert that both alternative output covers are produced simultaneously.

The existing construction also gives an exact modulus-sum comparison in the equality-count case. Set

    F_i=sum_(m original3-free in group i) m,
    B_i=sum_(3m original in group i) m,
    W_(3−i)=sum_(d original in the opposite group) d,
    C_ell=(3^ell−3)/2,      D_ell=ell*(3^ell−1)/2.

Its output modulus sum is F_i+C_ell*B_i+C_ell+D_ell, whereas the original sum is3+F_i+3*B_i+W_(3−i). Therefore if equality holds in CP6a, the second EB1 objective requires

    W_(3−i) ≤ (C_ell−3)B_i+C_ell+D_ell−3.             (CP6c)

All counts and weights are taken from one chosen group and one fresh opposite prime. No optimization over unrelated phases is combined. These are direct consumers of the HSW-based construction already retained in Report348; they supply conditional strict descent but do not force a violated inequality. At arbitrary H the flat seed premise remains missing.

### A repeated-label odd cover realizes the source relations

The following finite family illustrates exactly why concentration and the separator relations alone cannot exclude the two-color branch. It has odd moduli and covers all integers, but intentionally repeats numerical labels:

    0 mod3, 0 mod5, 0 mod7;
    1,4,7,13 mod15;
    2,5,8,11,17,20 mod21.                            (CP7)

There are13 classes on the complete period105. At first-three root0, A_3 covers. At root1, A_5 together with the four15-classes covers all five residues modulo5. At root2, A_7 together with the six21-classes covers all seven residues modulo7. This proves whole coverage without enumeration.

Every class has an actual private point. For A_3 choose both the5 and7 coordinates nonzero. For A_5 choose root1 and a nonzero7-coordinate; for A_7 choose root2 and a nonzero5-coordinate. For each15-class choose a nonzero7-coordinate, and for each21-class choose a nonzero5-coordinate. These choices also show the COMPLETE prime-private projections are

    V_5={1},       V_7={2}.                           (CP8)

The example keeps the actual common CRT source, oddness, private points, and the normalized prime classes. Its numerical palette is divisor-closed. Numerical distinctness fails explicitly: label15 occurs four times and label21 six times. It is neither an extremal distinct cover nor a counterexample to Erdős#7. Its role is solely to demonstrate that the private-reset and separator relations, even with both forced colors, require an additional use of distinctness before they can yield a contradiction.

### The actual color seed forces a collision in direct first-exit closing

Keep the all-concentrated, two-color branch at arbitrary H. Fix one color i and retain every original label whose NONEMPTY nonternary support lies in S_i, together with every original pure-three class of height at least two whose first root is i. Add two pure-three classes at the other two first roots. On root i, CP5 covers every complete ternary word outside the retained pure-three guards; those guards cover the rest. The two added classes cover the other roots. This is therefore an actual finite odd WHOLE cover on the original3-coordinate and X_i, in which only numerical modulus3 is repeated, exactly twice. All other numerical labels are the retained distinct originals.

Every retained group label has all its original private points on root i, by the actual prime reset. A retained pure-three class has its private points there because its own first root is i. Project any such original private point to the3-coordinate and X_i. Membership in every retained class is preserved, while the two new closing classes lie at other roots. The projected point is consequently still private to that retained label in this ONE seed. Conflicting originals cannot simply be deleted from the seed.

Normalize the two pure-three closing classes to roots0 and1 by one first-digit permutation, making the live color root2. In the direct extension of [Report348, section2](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#2-two-repeated-prime-classes-with-a-prime-flat-input), an original class of modulus3^a m, with3 not dividing m, is copied at first-exit depth h to modulus

    3^(a+h)m,

with its original cofactor phase and ternary residue multiplied by3^h. Its first nonzero ternary digit is at position h, counting positions from zero, because the original first digit is2. Continuous exit depths include both h=0 and h=1 in that construction.

Suppose this actual color group has any original mixed label3^a m with a≥2 and m>1. Divisor closure supplies both ORIGINAL labels3m and9m. Every nonternary prime dividing m has color i, so resetting their actual private points forces both originals to have first-three root i. Both therefore belong to this same seed, regardless of their higher ternary digits and cofactor phases. The direct closing now produces

    old9m at exit0  → numerical9m, first nonzero position0;
    old3m at exit1  → numerical9m, first nonzero position1. (CP9)

These two output APs have the same modulus and different ternary residues; they cannot be identified as one class. This obstruction holds for every fresh odd prime used for Report348's finite terminal closing. It uses actual original labels and private points, not an abstract tree or a separately chosen quotient.

Post-copy pruning cannot remove the collision either. For a copied original at exit h, take its old private point, multiply the COMPLETE old ternary coordinate by3^h, preserve every nonternary coordinate, and set the fresh-prime coordinate to ell−1. The retained3-free originals and other copies at the same exit are absent by the old private-point property. Copies at other exits have a different ternary valuation; the pure first-exit guards require first nonzero digit1, while this point has digit2. A terminal class indexed by k≤h requires fresh-prime residue k rather than ell−1>h; for k>h it requires divisibility by3^k, contradicting valuation h. Thus every copied original still has a private point in the constructed family, including both9m copies in CP9.

For a general input, separating the shifted height sets could avoid this particular collision. Here divisor closure and the common concentrated color already force consecutive positive heights1 and2 whenever a deep mixed label exists. Thus that sparse-height escape is unavailable for the actual color seed. A construction changing the source map or replacing the conflicting originals would need a new coverage and numerical-distinctness argument.

[Report536](../500-549/536-ternary-conditioning-preserves-a-joint-query-and-entropy-boundary.md) already explains the other direct failure: removing all ternary digits can project several distinct original heights to more than two cofactor classes. CP9 adds the same-source obstruction to repairing that loss by the literal first-exit closing. Neither statement rules out another legal transport, and neither supplies an all-height flat or multiplicity-two seed. That bridge remains unproved.

The remaining all-concentrated branch therefore has two nonempty color groups, no original label mixing their nonternary supports, and both complete-word quotient-cover obligations CP5. A useful next bridge must exploit the distinct original labels to resolve those quotient collisions, or give a jointly legal replacement with strict count or modulus-sum descent. The existing singleton-color root permutations preserve those budgets and do not provide that bridge.

### One flat color gives the existing budget comparison at arbitrary global height

Retain the all-concentrated two-color branch, with arbitrary global ternary height H. Suppose one color i has NO mixed original3^a m with a≥2 and m>1. Choose a complete ternary word in root i outside every original pure-three guard, as CP2 permits. Its group quotient is a whole cover by CP5. All its mixed originals have height one, so this same group quotient is independent of the higher ternary digits throughout root i. Every hypothetical original pure-three class of height at least two in root i would then be covered by these group originals and have no private point. Thus none exists, and the actual color-i seed is3-flat even when the opposite group has arbitrary height.                    (CP10)

Reuse Report348's flat construction and the unchanged output prices C_ell,D_ell from CP6c. Let f_i,b_i,F_i,B_i have their CP6 meanings for this flat group. Let n_op,W_op count and sum ALL original non-pure-three labels in the opposite group, at every original height. Let g_op,T_op count and sum its original pure-three guards of height at least two. The full original count and weight are exactly

    n_old=1+f_i+b_i+n_op+g_op,
    W_old=3+F_i+3B_i+W_op+T_op.

For any prime ell in the opposite group, freshness holds for this one flat seed. The existing construction has

    n_new=f_i+(ell−1)b_i+2ell−1,
    W_new=F_i+C_ell B_i+C_ell+D_ell.

Consequently the two EB1 objectives give

    n_op+g_op≤(ell−2)b_i+2ell−2;                    (CP11)

    equality in CP11 ==>
      W_op+T_op≤(C_ell−3)B_i+C_ell+D_ell−3.         (CP12)

A strict reversal supplies an actual count descent, or a strict weight descent at equal count. These bounds compare one actual source and one output. No high pure-three guard is omitted from the old budget. Divisor closure supplies every pure-three power through H, and CP10 puts all higher ones in the opposite root, so g_op=H−1 and T_op=(3^(H+1)−9)/2. At H=1 these formulas recover CP6a and CP6c exactly. No new HSW proof or arithmetic computation is required.

For H≥2, directly reuse [Report371, section2](371-private-top-fans-and-ancestor-cuts.md#2-the-private-top-fan-has-an-escaping-first-ancestor): the private point of the original pure3^H class supplies two different nonunit cofactors m_1,m_2 at that same first-three root. CP10 places this root opposite the flat group, and concentration places both cofactors' nonternary supports there. Divisor closure supplies3^a m_j for a=0,...,H and j=1,2, all with distinct numerical labels. Therefore n_op≥2(H+1), and CP11 implies the additional necessary budget

    3H+1≤(ell−2)b_i+2ell−2.                        (CP12a)

This is a consumer of the existing top fan, not another proof of it.

### Switching entire color seeds at successive exits does not enlarge that domain

Consider ONLY this specified extension of the existing closing construction. Keep its standard first-digit1 pure guards with exponents1 through ell−1 and its standard terminal closing classes for one odd prime ell fresh for BOTH groups. At each exit h=0,...,ell−2, one may choose either color and copy ALL of that seed's positive-three-height classes in its normalized live root2 by the literal map of CP9. Retain the3-free originals of every color actually used. Changing the guards, splitting a seed, or making a joint replacement is outside this constructor.

For H≥2 the actual original pure9 exists and lies in one nonzero root j. If color j were chosen at exit0, its9-copy would collide numerically with the standard modulus9 guard: their ternary valuations are0 and1. If chosen at exit1, its27-copy would collide with the standard modulus27 guard: their valuations are1 and2. Since ell≥5, both guards and both exits are present. Thus exits0 and1 must BOTH use the other color k.

If k contains any deep mixed original, divisor closure and concentration supply its original3m and9m in the same seed. Copying at these two exits produces precisely the nonmergeable collision CP9. Therefore a distinct output in this constructor requires a color with no deep mixed original. Conversely CP10 makes such a color's seed genuinely flat, and selecting it at every exit is exactly the existing valid Report348 construction. The H=1 case is already flat. Hence, within this specified constructor,

    a distinct output exists
       iff at least one color has no deep mixed original.    (CP13)

The freedom to switch whole seeds at successive exits supplies no new all-height case beyond CP10. This is not a prohibition on other HSW variants, changed closing families, selected subbatches, or another common source map. CP11–CP12 are conditional descent criteria; no result here forces their violation when a flat color exists or supplies a construction when both colors have deep mixed originals.

## 71. Only nonconcentrated prime support can supply nonconcentrated ancestors

### Nonconcentrated ancestors are supported only on nonconcentrated primes

Keep the one original EB1 family, arbitrary original ternary height, and the complete private projections V_d used in sections69--70. Let

    R={q>3: q is an original support prime and V_q={1,2}}.

Report357's actual first-q reset gives V_e subset V_q whenever q divides the original e. Therefore every nonconcentrated 3-free original e has ALL its prime divisors in R. For a fixed nonconcentrated prime p and a top t in G, all its eligible nonconcentrated ancestors consequently divide

    t_R=product_(q in R) q^(v_q(t)).

This is a direct consumer of the existing private reset, not a converse: an original supported entirely on R may still be concentrated. It identifies the only part of a top from which additional DP4 slots can come.

If R={p}, the set P minus L is exactly the original nonconcentrated pure p-powers. Every top in G is nonpure by DP10; its nontrivial p-free cofactor contains a concentrated prime. The private reset at that prime makes EVERY original level in this cofactor column concentrated. Hence B=G and section69's pure-power assignment is the FULL maximal-top ancestor graph. With the existing I_0 and A_*, the exact deficit is therefore

    delta=epsilon_0
      =max_(0<=h<=A_*)
        [ #{t in G:v_p(t)<=h} - #{a in I_0:a<=h} ].

No fresh matching theorem is used: DP3 and the already justified DP12 threshold calculation apply to this identified full graph. In particular, if also A_*=1 then I_0={1} and delta=max(|G|-1,0). These identities do not construct a legal frontier or rule out this whole-cover branch. They show that searching for nonpure nonconcentrated ancestor slots cannot improve it.

### The pure-power concentration pattern has no supplied monotonicity law

The existing first-p reset reaches P_p and preserves the whole p-tail. It does not supply a map from P_(p^a) to P_(p^b) for 1<b<a. Replacing the lower p-prefix may activate original mixed classes of smaller p-height. The threshold formula must retain the actual set I_0; no initial-segment assumption is justified by that map.

The distinction already occurs in a partial actual AP family on period375:

    (modulus,residue)=
      (3,0),(5,0),(15,1),(25,1),(75,8),(125,2),(375,4).

The numerical palette is divisor-closed above one; comparable original classes are disjoint. Private witnesses for these seven labels are respectively3,5,16,26,8,2,4. The complete private regions relevant to the pure powers are

    5,10 in P_5,
    P_25={26,101,176,251,326} mod375,
    P_125={2,127} mod375.

The pure-five projections are thus V_5={1,2}, V_25={2}, V_125={1,2}, giving I_0={1,3}. These identities follow directly from the listed congruences: A_15 removes root1 inside A_25, A_3 removes root0, and all other listed moduli have incompatible first-five phases there. The two nonzero-root lifts of A_125 avoid every other class.

This is a NONCOVER: integer7 is uncovered. It does not refute an additional theorem under the full EB1 whole-cover hypothesis. The whole-cover question about I_0 remains unproved; the example only identifies which existing local premises cannot establish it. No numerical enumeration or Lean verification is asserted.

## 72. Small-prime overlap excludes the height-one all-concentrated branch

[Report348, SO1](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#two-multiplicity-two-covers-share-a-small-prime)
combines the published KKL bounded-multiplicity moment estimate with
BBMST's continuation criterion and Table1. It proves that two finite
whole AP covers whose moduli are greater than one and coprime to6,
each with numerical multiplicity at most two, must have prime supports
intersecting within {5,7,11,13}. The moment and continuation interfaces,
published threshold direction, and three exact rational substitutions
are checked there. No new moment theorem, recomputation of the published
table, literature priority or Lean verification is claimed here.

### The two actual quotients satisfy every overlap hypothesis

Keep CP1--CP5's one actual all-concentrated family and its disjoint
nonempty support groups S_1,S_2. Suppose H=1. For i=1,2, retain the
actual group-i originals and restrict by the single map x=i+3t.
The original pure3 class at root0 is inactive. The only original labels
with a given nonunit3-free cofactor m are m and3m; each occurs at most
once. Both images have numerical modulus m, and their actual phases are

    t = 3^(-1)(a_d-i) mod m.

The same affine map is used on every complete nonternary coordinate;
there is no separate choice of phases for different labels. CP5 makes
each image a whole cover of its carrier, equivalently of all integers.
Every image modulus is greater than one, coprime to6, and occurs at most
twice. All original nonternary heights are retained. Its prime support
is contained in S_i.

The two image supports are disjoint, contradicting SO1. Thus

    every p>3 concentrated ==> H>=2.                  (CP14)

This excludes the COMPLETE H=1 all-concentrated branch, regardless of
the number or heights of the other primes. The earlier CP6 and CP6a--c
remain necessary implications, but that branch no longer requires a
separate search for a count-budget violation. The result does not say
that all H=1 odd covers are excluded: some nonternary prime may be
nonconcentrated.

### One flat color forces actual high-level activity in the other

CP10--CP13 retain their stated all-height scopes. If both colors had
no deep mixed original, CP10 would exclude every higher pure-three
guard in both live roots. Such a guard at root0 is also impossible
by disjointness from A_3. Divisor closure supplies pure9 whenever H>=2,
so both colors flat would force H=1, now excluded by CP14.

Suppose just one color i is flat. Its quotient is a whole cover with
numerical multiplicity at most two. At ANY complete opposite-root word
outside the original pure-three guards, CP5 supplies another whole
quotient, on disjoint nonternary support. SO1 implies that this quotient
must have at least three originals with a common cofactor m. Their
original numerical labels are comparable powers3^a m. With the common
ternary word active in all of them, comparable-original disjointness
forces their mod-m phases to be pairwise different. Thus

    every guard-free opposite word has at least three
      DISTINCT active phases at some cofactor m>1.    (CP15)

This is a necessary multiplicity obstruction, not a distinct-cover
construction or an all-height contradiction.

There is also one cofactor point that must use higher mixed levels
across the entire opposite root. Take the opposite group's actual
3-free originals and its originals3m, and project their original phases
to m. This low-level family has multiplicity at most two and support
disjoint from the flat cover. By SO1 it cannot itself cover. Choose
one full opposite-group cofactor v avoiding ALL of these actual phases.
For every complete ternary word in that root outside the pure guards,
CP5 at this SAME v must therefore use an original3^a m with a>=2 and
v=a_(3^a m) mod m.

The pure-three guards have total relative root measure
sum_(a=2..H)3^(1-a)=(1-3^(1-H))/2, since CP10 puts all of them in
the opposite root and comparable pure classes are disjoint. The union
bound on the remaining actual prefixes gives

    sum_(3^a m original in opposite group, a>=2, m>1,
         v=a_(3^a m) mod m) 3^(1-a)
      >= (1+3^(1-H))/2.                              (CP16)

Both the common v and every prefix are from the original family. This
retains their joint source instead of optimizing a different cofactor
at each ternary word. CP16 supplies a necessary high-level coverage
obligation. It does not show that the available originals violate it,
resolve their copied-label collisions, or force the CP11--CP12 descent.

## 73. A nonconcentrated small prime is forced at ternary height one

Keep one EB1-selected original whole distinct odd cover with ternary
height H=1. Normalize its prime classes by the existing common
translation, retaining all original nonternary heights and phases. Put

    R={q>3: V_q={1,2}},
    S_i={q>3: V_q={i}} for i=1,2.

These sets partition the nonternary support; either S_i may be empty.
No all-concentrated hypothesis is imposed. Then

    R intersect {5,7,11,13} is nonempty.               (CP17)

### One common root assignment removes the opposite concentrated primes

DP9 and [Report364, SI1](../../321-384/364-singleton-cofactor-ideal-and-forced-colors.md#1-actual-singleton-roots-and-a-common-cofactor-ideal)
supply the needed source statement. For each q in S_j, the ORIGINAL
class A_(3q) exists, has first-three root j, and is the unique q-bearing
original at its own first-q root r_q=a_(3q) mod q. Every other original
divisible by q has a different first-q residue. This quantifies over
actual original classes at arbitrary q-height, not only their private
projections.

Fix i in {1,2}. Simultaneously set the first-q coordinate to r_q for
every q in S_(3-i), and the ternary coordinate to i. CRT permits these
choices at the SAME source point, independently of all full coordinates
at primes in R union S_i. The higher digits at the fixed primes are
arbitrary. An original containing any q in S_(3-i) cannot cover this
point: its only possible representative at r_q is A_(3q), whose ternary
root is the opposite one. All originals involving those primes vanish
simultaneously.

Consequently the actual subfamily with nonternary support contained in
R union S_i covers the WHOLE ternary branch i. Indeed, prescribe any
full coordinates at R union S_i, complete them with the preceding
common root assignment, and apply original whole coverage. Every
surviving original is independent of the discarded coordinates, so
these same surviving classes cover every extension of the prescribed
retained coordinates. No phase or numerical label is reassigned.

### The surviving two covers share a nonconcentrated small prime

Restrict this retained subfamily by the ONE affine map x=i+3t,
discarding originals incompatible with that branch. The pure3 class
at root0 is inactive. Every surviving quotient modulus m is greater
than one and coprime to6. Since H=1, only original labels m and3m can
map to m; numerical multiplicity is at most two. Their actual image
phases are

    t = 3^(-1)(a_d-i) mod m.

All retained nonternary exponents are unchanged. This gives a whole
AP cover B_i with support contained in R union S_i. The common support
of B_1 and B_2 is therefore contained in

    (R union S_1) intersect (R union S_2) = R.

Apply the already established Report348 SO1: those two whole covers
share a prime in {5,7,11,13}. That prime lies in R, proving CP17.
Empty S_i cause no exception; the argument uses no witness from S_i.

If p is the only nonconcentrated prime, CP17 forces
p in {5,7,11,13}, with arbitrary original p-height and arbitrary other
nonternary heights. If a nonconcentrated prime p>=17 occurs, some
different prime among5,7,11,13 must also be nonconcentrated.

CP17 strengthens CP14 by reusing the same arithmetic input and the
existing singleton-root theorem. It does not force two nonconcentrated
primes when the unique one is in {5,7,11,13}, establish monotonicity of
pure-power private colors, create additional Hall slots, or supply
strict descent in those remaining cases. Section71 retains the full
ancestor deficit there. No new sieve computation, squarefree-shadow
argument or Lean verification is asserted.

## 74. At arbitrary height one root must retain actual prefix collisions

Keep the one EB1 original cover, its full period Q=3^H M, and arbitrary
H>=1. Let R,S_1,S_2 partition its original nonternary support primes as
in section73, and put K={5,7,11,13}. Then either R intersects K, or
one complete ternary root satisfies the actual prefix-cover and
common-cofactor obligations below. No color is assumed flat.

### Complete-word multiplicity is an actual prefix test

The singleton-root CRT elimination in section73 does not use H=1.
For root i, fix every q in S_(3-i) at its original singleton3q root.
All originals involving any such prime disappear throughout the
complete root i. The retained originals with nonternary support in
R union S_i cover that WHOLE root, with every ternary tail retained.
Keep its actual pure-three guards. At any complete ternary word z
outside these guards, the active cofactor quotient B_i(z) is a whole
cover with nonunit moduli coprime to6 and support in R union S_i.

For each occurring retained nonunit cofactor m, divisor closure supplies
the original m. Its exact quotient multiplicity at z is

    1 + #{a>=1: 3^a m is original,
                 z=a_(3^a m) mod3^a}.                (CP18)

All the counted originals, including height zero m, have different
actual mod-m phases. Their numerical labels are comparable; equality
of both their cofactor phases and active ternary prefixes would make
two original APs intersect. Thus identical-AP merging cannot reduce
this multiplicity.

Write G_i for the union of the actual pure-three prefixes of heights
2,...,H in root i. Let C_i be the set of retained actual labels3^c m,
with m>1, c>=2 and first-three root i, for which some ORIGINAL lower
positive height3^b m, 1<=b<c, satisfies

    a_(3^c m)=a_(3^b m) mod3^b.

Let T_i be the union of the ternary prefixes of labels in C_i. By CP18,
outside G_i, membership in T_i is equivalent to a quotient modulus
having multiplicity at least three. This tests the original phases;
it does not presume that every deep mixed prefix agrees with its3m
ancestor. That agreement follows from the private reset when m contains
a concentrated prime in S_i. For m supported only on R, the explicit
lower-prefix test remains necessary.

Suppose R intersects K trivially. If each root had a word outside
G_i union T_i, the two whole quotients at those words would have
multiplicity at most two. SO1 would give a common prime in K, while
their common support is contained in R. This contradiction proves that
for ONE i,

    G_i union T_i = the complete ternary root i.       (CP19)

This is an all-height phase condition, allowing arbitrary nonconcentrated
primes outside K and preserving their full exponents. At H=1 both
prefix families are empty, recovering CP17 by the existing input.

### The same root admits one cofactor avoiding every low class

For the root selected by CP19, let L_i consist of the actual cofactor
phases of retained originals m and originals3m at root i. It cannot
cover: otherwise these actual low originals cover the entire root,
independently of its tail, and every original of ternary height at
least two there has no private point. This excludes every guard and
every member of C_i, contradicting CP19.

Choose one full retained cofactor v avoiding ALL of L_i. The same CRT
elimination preserves this v at every tail. Original coverage therefore
requires, at every word outside G_i, an actual retained3^a m with
a>=2, m>1 and v=a_(3^a m) mod m.

Let beta_i be the exact relative root measure of G_i. The two necessary
charges at this SAME root are

    sum_(3^c m in C_i) 3^(1-c) >= 1-beta_i;            (CP20)

    sum_(retained original3^a m at root i, a>=2, m>1,
         v=a_(3^a m) mod m) 3^(1-a) >= 1-beta_i.       (CP21)

The actual pure-three classes are comparable and disjoint, so

    beta_i=sum_(original pure3^a at root i,a>=2)3^(1-a)
          <= (1-3^(1-H))/2.

Thus both right sides are at least (1+3^(1-H))/2. CP19 retains the
complete prefix-cover condition, which is stronger than its union
bound CP20. CP21 holds at one fixed v across every ternary tail,
extending CP16 without requiring an opposite flat color. The labels
in CP20 and CP21 need not coincide; these two inequalities cannot be
charged against two copies of one inventory budget.

At least two different cofactors occur among C_i. For one fixed m,
numerical distinctness permits at most one label at each height c;
their total prefix mass is at most (1-3^(1-H))/2. Even adding every
pure guard gives at most1-3^(1-H)<1, contrary to CP19. This is a direct
consumer of the original height inventory, not a new top-fan theorem.

The remaining alternative is exact: R meets {5,7,11,13}, or one root
has CP19 and the common-cofactor obligation CP21. Neither obligation
has been shown impossible, and neither supplies an extra nonconcentrated
ancestor or strict count/weight descent. The argument reuses SO1,
DP9/SI1, comparable-class disjointness, divisor closure and irredundancy.
No published sieve calculation, old experiment or Lean proof is repeated.

## 75. One nonconcentrated prime gives a common two-root private source

Keep one EB1 family with H=1 and R={p}; CP17 places p in {5,7,11,13}.
Let X_i be the complete carrier of its concentrated support group S_i,
and let A=v_p(Q). Every original p-height and phase is retained.
The private reset excludes an original label involving primes from
both S_1 and S_2, since its nonempty private projection would have to
lie in both singleton colors.

Choose an ORIGINAL private point w_i of A_p at ternary root i, for
i=1,2; V_p={1,2} provides both. Its full X_i coordinate v_i avoids
every p-free original cofactor phase supported in S_i, both the
3-free phases and those of3m. Such an original3m has first-three root i
by the private reset. Hence the one CRT combination

    v=(v_1,v_2)

simultaneously avoids ALL p-free originals at BOTH live ternary roots.
A p-free non-pure-three label involves just one concentrated color:
its 3-free phase is avoided by that color's v_i, while its 3-bearing
phase is avoided there or has the wrong ternary root. The only pure
three class is A_3 at root0.

Thus the SAME nonternary, non-p cofactor v belongs to the actual R_p
source at both roots. At first-p root0 and ANY higher p-tail, both
lifts are private to A_p. This joint source uses the proved factor
supports; it does not combine arbitrary unrelated private records.

### Both colors occupy almost every nonzero p-root at that source

Section73's pruning gives, for each i, whole coverage of root i by
originals with nonternary support in {p} union S_i. This surviving
union is independent of the other color's coordinates, so it remains
a whole cover when they are set to the chosen v_(3-i). Both covering
statements therefore hold at the common v.

Fix a nonzero first-p root r. Originals in this surviving family that
contain no S_i factor are pure p^a or3p^a. The original p is absent.
Unless original3p has ternary root i AND first-p root r, every active
class of those two types has a>=2. Their total relative p-tail measure
over r is at most

    2 sum_(a=2..A) p^(1-a)
      =2(1-p^(1-A))/(p-1)<1.

This includes the actual finite heights and allows overlaps. Whole
coverage thus requires an actual original containing p and a prime
of S_i, with first-p root r and its S_i cofactor phase equal to v_i.
This holds simultaneously at the SAME v for both colors and every
nonzero p-root, with at most one exceptional (i,r) cell supplied by
the single original3p if present. In particular, both S_i are nonempty.

The forced mixed original may have any actual p-exponent; exponent one
has not been forced. Different roots require different originals, but
no new numerical inventory or Hall slot is created. The shared pure-p
classes have not been charged twice.

The existing Report364 SI2 also gives F_p empty. A hypothetical m in F_p
would satisfy V_(pm)=V_p={1,2}. A factor3 in m fixes a ternary root,
and any concentrated prime factor forces a singleton private projection.
Since p does not divide m and every other nonternary prime is
concentrated, no such m>1 exists. This is a direct SI2/reset consumer,
not another singleton-root theorem.

### Pure-power private points survive exactly on their original colors

Use the labelled surviving family in root i, before the affine
coordinate change, keeping its original provenance. For every original
pure p^a, its private set in this family equals

    projection_(p,X_i)[P_(p^a) intersect {three root i}].

Projection preserves absence of all retained originals. Conversely,
lift a private point of the surviving family by setting every
opposite-color q at its singleton3q root. All discarded originals
vanish, while membership in retained originals is unchanged. The lift
is an original private point of p^a at root i. Consequently

    p^a is private in quotient i iff i belongs to V_(p^a).

Every pure p^a concentrated only in the opposite color can be removed
from this quotient SIMULTANEOUSLY. The removed APs are pairwise disjoint
by comparable-original disjointness. A point losing coverage would
therefore belong to exactly one removed class and be private to it,
contrary to the displayed equivalence. The resulting quotient covers.

This cannot delete original p, whose private points project to both
quotients. An original3p^a active in root i also retains an original
private point. Neither quotient becomes numerically distinct: S_i is
nonempty, and for any q in S_i, DP9 supplies the actual q and3q pair;
neither is a pure-p deletion, so their two quotient classes remain.
Thus these certified deletions do not make the two supports disjoint
or remove every repeated numerical modulus. Section71's exact deficit
still uses the actual nonmonotone I_0, with no nonpure nonconcentrated
ancestor in this branch. A further operation or estimate is required
for strict descent. No experiment, new sieve bound or Lean verification
is asserted.

## 76. Existing Simpson cuts constrain each actual color seed

Keep CP1--CP5's all-concentrated two-color EB1 family at arbitrary H.
Let D_i consist of its original labels with nonempty nonternary support
in S_i, and n_i=|D_i|. Define

    Q_i=product_(p in S_i)p^H_p,
    E_i=sum_(p in S_i)H_p(p-1),

using every full ORIGINAL height H_p. Both S_i are nonempty by CP3.
Let g_i count the owned original pure-three guards of height at least
two, and h_i be the ternary height of CP9's actual seed: the maximum
of1 and the ternary heights in D_i and its owned guards. Its exact
period is3^h_i Q_i. In particular, every original pure p^H_p is
retained, so no nonternary height has disappeared.

### Both closing classes also satisfy the minimal-cover hypothesis

CP9 gives whole coverage and a private point for every retained
original. For either added modulus3 closing class, take the S_i
projection of the cofactor of an original private point of A_3.
It avoids every retained3-free original. At that closing root, all
retained3-bearing originals, owned pure guards and the other closing
class are inactive. Thus both added classes also have private points,
and the whole seed is inclusion-minimal despite its repeated modulus3.

Reuse Simpson's Theorem2 exactly as retained in
[Report343, section2](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md)
and [the existing divisor-cut citation](../../../../../../Library/Arith/mcnewsetty2026covering.md#4-lemma-31-is-already-supplied-by-the-existing-divisor-cut):

    Dcut|Qseed, Dcut!=Qseed
      ==> #{seed classes whose modulus does not divide Dcut}
            >=1+f(Qseed/Dcut),
    f(u)=sum_p v_p(u)(p-1).

Numerical multiplicity one is not a hypothesis. For1<=a<=h_i and
0<=c_p<=H_p, choose Dcut=3^a product_(p in S_i)p^c_p. Let K_i(a,c)
count the UNION of actual d in D_i satisfying v_3(d)>a or v_p(d)>c_p
for at least one p in S_i. A label crossing several thresholds is
counted once. Let G_i(a) count owned pure guards above height a.
The two closing classes divide Dcut since a>=1. Whenever

    2(h_i-a)+sum_(p in S_i)(H_p-c_p)(p-1)>0,

the cut is proper and gives

    K_i(a,c)+G_i(a)
      >=1+2(h_i-a)+sum_(p in S_i)(H_p-c_p)(p-1).      (SC1)

Taking a=1 and all c_p=0 is proper because S_i is nonempty. Every
label in D_i is counted, yielding

    n_i+g_i >=2h_i+E_i-1.                            (SC2)

The period here belongs to the actual minimal seed; no single
original modulus is assumed to contain all of Q_i.

### An existing cut gives an additional flat-construction budget test

If color i is flat in CP10's sense, its opposite seed has h_op=H
and g_op=H-1. SC2 gives

    n_op >=H+E_op.                                  (SC3)

This also follows DIRECTLY from the original family's Simpson cut
Dcut=3Q_i. Its counted labels are exactly the n_op opposite nonpure
originals and H-1 higher pure-three originals, and Q/Dcut=3^(H-1)Q_op.
SC3 is a consumer of the retained full divisor-cut theorem, not a new
Simpson inequality.

For ell in S_op put B_ell=(ell-2)b_i+2ell-2, using CP11's actual flat
count b_i. The unchanged HSW output has

    n_old-n_new=n_op+H-1-B_ell.

Together with the existing top-fan bound n_op>=2(H+1), SC3 supplies
the necessary no-descent condition

    max{3H+1, 2H+E_op-1} <= B_ell.                   (SC4)

The second term is stronger exactly when E_op>H+2. If either lower
bound exceeds B_ell, the already established HSW construction has
strictly fewer classes than the original cover. If the ACTUAL counts
satisfy n_op+H-1=B_ell, CP12's modulus-sum comparison remains necessary.
Equality of a lower bound with B_ell alone does not imply equal actual
counts or justify switching to the weight objective.

### The two seeds count each shared pure guard once

Write N for the original class count. Divisor closure and comparable
disjointness give

    N=H+n_1+n_2,
    g_1+g_2=H-1,
    max(h_1,h_2)=H.

Every pure-three power through H is original, and no higher guard can
lie at A_3's root0. Each belongs to exactly one seed. Adding the two
SC2 inequalities therefore yields

    N >=2(h_1+h_2)+E_1+E_2-1
       =1+2H+E_1+E_2+2(min(h_1,h_2)-1).             (SC5)

The first four terms on the second line are the original cover's
aggregate Simpson bound. If both seeds reach height two or above,
SC5 strengthens that aggregate bound by at least two classes. This
does not assert independence from every other existing divisor cut.

More generally, take1<=a<=min(h_1,h_2) with both cuts in SC1 proper.
All pure guards above a are assigned once, so G_1(a)+G_2(a)=H-a.
Adding SC1 gives

    K_1(a,c_1)+K_2(a,c_2)
      >=2+2(h_1+h_2-2a)
         +sum_(p in S_1 union S_2)(H_p-c_p)(p-1)
         -(H-a).                                   (SC6)

The D_i are disjoint actual inventories. No independent optimization
or duplicated guard budget enters these inequalities. They do not
force their own violation, establish all-height support intersection,
or prove unrestricted noncoverage. These are ordinary applications
of the existing Simpson and source/HSW results, with no new numerical
computation or Lean verification.

## 77. Independent color permutations force every nonzero private p-root of3

Keep one EB1 family with H_3=H_p=1 and R={p}. Section73 gives
p in {5,7,11,13}, and section75 gives both nonempty concentrated
support groups S_i and their complete carriers X_i. All other original
heights, cofactor phases and numerical labels remain fixed. The
private reset excludes any original involving both color groups.

### A separate nonzero-root permutation in each color preserves coverage

For i=1,2 choose a permutation sigma_i of F_p fixing zero. For every
p-bearing original whose modulus has a prime factor in S_i, replace
only its p-residue r by sigma_i(r). If the pure original3p exists,
apply sigma_i to its p-residue, where i is its original ternary root.
Keep original p and every p-free original unchanged. There are no
higher p-digits; CRT gives one AP with the SAME modulus for each
changed original. Its complete cofactor phase and any ternary root
stay unchanged.

This transformed family covers. Original3 covers ternary root0 and
original p covers p-root0. At a point with nonzero roots i,r, choose
one original source with p-coordinate sigma_i^(-1)(r), the same full
X_i coordinate, and the opposite-color singleton-root choices from
section73. The latter theorem removes all opposite-color originals
and supplies whole coverage by the retained family on {p} union S_i.
An active p-bearing owner in that family was transformed by sigma_i;
an active p-free owner is unchanged. It therefore covers the output
point after the indicated transformation.

The number and numerical moduli of classes are unchanged. The new
whole family has the same EB1 objectives and hence is irredundant.
This holds for every pair of independent permutations. It does not
assert that a single global coordinate permutation transports all
original private sets or their cross-color intersections.

### No color's complete3-free section can cover at any p-root

For r in F_p let C_i(r) be the union on X_i of all ORIGINAL3-free
classes with nonempty concentrated support in S_i, after fixing p=r.
This includes every p-free original supported in S_i; a p-bearing
original contributes only at its actual p-root. The pure original p
is excluded. Then

    C_i(r) != X_i for i=1,2 and every r in F_p.

At r=0, section75's private cofactor v_i avoids all the p-free
originals in question, and comparable disjointness from original p
excludes every other p-bearing original.

Suppose C_i(r)=X_i at a nonzero root. Section75 supplies a p-bearing
original d with a factor in the opposite group S_j. Its actual p-root
s is nonzero. Keep sigma_i the identity and choose sigma_j with
sigma_j(s)=r. The preceding operation preserves whole coverage and
all numerical labels. Every point of transformed A_d is now covered
by the unchanged color-i3-free classes: they cover X_i at p=r and
are independent of the ternary and X_j coordinates. None has label d,
since the two nonempty concentrated supports are disjoint. Deleting
transformed A_d yields a whole distinct odd cover with fewer classes,
contrary to EB1. The argument uses one transformed whole cover, not
private witnesses chosen from different families.

### The original private region of3 has an exact product description

Put E_i(r)=X_i minus C_i(r). Every E_i(r) is nonempty. At ternary
root0 all other3-bearing originals are absent by comparable
disjointness. At p-root0 original p prevents privacy for original3.
At every nonzero p-root, all remaining3-free originals split into
the two color families just defined. Thus in ORIGINAL full coordinates,

    P_3={0}_3 x disjoint_union_(r!=0)
          ({r}_p x E_1(r) x E_2(r)).

In particular the projection of the complete original P_3 to F_p is
exactly F_p minus {0}. The complements can depend on r: no common
cofactor avoiding every r-section is inferred. This also gives no
root free of3p-bearing originals, since those originals are absent
from the definitions of C_i(r). The source statement does not give
an uncovered original point or exclude this entire flat branch.

The operation reuses section73's retained whole-branch cover and
section75's color support and occupancy. Its new consequence is the
full original private p-projection of3. No new numerical experiment,
sieve estimate or Lean verification is asserted.

## 78. Six receiving leaves exclude two sufficiently clean color roots

Keep H_3=H_p=1 and R={p}, with the complete original color carriers
X_i from section75. Define actual blocked and clean root sets

    B_i={r in F_p minus {0}: some ORIGINAL3p-bearing d
          has a_d=i mod3 and a_d=r modp},
    W_i=(F_p minus {0}) minus B_i.

The pure original3p, when present, blocks its actual cell. Every
3p-bearing original has height one at both primes, and comparable
disjointness excludes either zero root. These are actual incidence
sets, not independently selected phases. Then EB1 requires

    min(|W_1|,|W_2|)<=1 OR |W_1|=|W_2|=2.          (FL1)

Equivalently, some |B_i|>=p-2, or both |B_i|=p-3.

### Three clean roots per color give a complete count-saving transport

First suppose |W_i|>=3 for both colors. Choose three distinct clean
roots r_(i,0),r_(i,1),r_(i,2) within each color. The two colors may
reuse p-roots. Retain every original p-free AP unchanged. For every
original pm with m>1 supported in S_i, whose p-root is r_(i,j),
insert the complete CRT class

    x=i+3j mod9,  x=a_(pm) mod m,

of modulus9m. Delete every other p-bearing original, including p
and all3p-bearing originals. Original3 covers root0; the six receiving
leaves partition both remaining ternary roots.

Take an output point missed by all retained p-free originals and
read its receiving leaf i+3j mod9. Choose ONE original source with
ternary root i, p-root r_(i,j), the output's complete X_i coordinate,
and the opposite-color singleton-root choices from section73. Every
opposite-color original disappears at that source. All retained
originals supported on S_i, with or without3, test the same retained
coordinates as at the output and hence are absent. Pure3 and p are
absent at the chosen nonzero roots, and all3p-bearing originals are
absent by the clean-root condition. Whole original coverage therefore
supplies an original pm with m>1 in the selected color and p-root.
Its complete cofactor phase matches the output, so its inserted9m
class covers that point.

This is the required JOINT residual coverage RS1, not separate
redundancy tests for omitted originals. The source changes the
opposite-color coordinates only through their proved simultaneous
elimination; it keeps every tested full coordinate unchanged.

No retained modulus has ternary height two. Two inserted9m labels
coincide only when their original pm labels coincide. Each original
is used once, at its one actual p-root and its unique concentrated
color. Nonunit cofactors from the two disjoint colors cannot be equal.
Thus RS2--RS3 hold, and the output is a whole distinct odd cover.

Let n_0 count p-free originals, n_p count3-free p-bearing originals
INCLUDING p, and t count3p-bearing originals. Its count satisfies

    n_new<=n_0+n_p-1 < n_0+n_p+t=n_old.

This contradicts EB1. The output carrier can be9 times the product
of the original complete color carriers: p is removed, every other
original nonternary height is retained, and the ternary height grows
from one to two.

### One use of p covers the case of three and two clean roots

If one color has at least three clean roots and the other has exactly
two, use three clean roots for the first color. In the second color,
assign its two clean roots and original p-root0 to its three leaves.
Transport the nonzero-root classes exactly as above. At the root0
leaf insert ONE pure9 class: original p supplies its whole old source,
independently of all cofactor coordinates.

The pure9 label is distinct from all9m with m>1 and all retained
originals. Every nonpure original pm is still used at most once, so

    n_new<=n_0+n_p=n_old-t.

The color with exactly two clean roots has p-3 blocked roots. Thus
t>=p-3>=2, since p is in {5,7,11,13}, and the descent is strict.
Together with the preceding case this proves FL1.

Two clean roots in each color would use pure p twice at the SAME
receiving depth and create two numerical9 labels. That arrangement
is illegal. Different receiving depths can avoid this collision but
repeat other source classes; RS4--RS6 must charge their actual cost.
If one color has at most one clean root, the six-leaf construction
above is unavailable. FL1 does not exclude all flat shared-prime
sources or any arbitrary-height branch.

The construction reuses the transport in section67 and source
elimination in section73. Fixing both old3 and p coordinates can
instead merge m,3m,pm,3pm into FOUR quotient classes of modulus m;
it does not preserve SO1's multiplicity-two hypothesis. The present
replacement retains the p-free labels and checks the fresh9m labels
directly. No numerical search or Lean verification is asserted.

## 79. Height-two singleton branches force an original lcm ancestor

Keep one all-concentrated EB1 family with H_3=2 and the actual color
seeds of section76. Fix a deep color i. Let L_i be the union on its
complete carrier X_i of the cofactor phases of all its original
3-free m and original3m classes, and put R_i=X_i minus L_i.
A private point of any original height-two class at root i projects
into R_i, so R_i is nonempty. CP5's whole-root coverage holds at
every point of this SAME cofactor remainder.

At each of the three second-three digits, collect all original
height-two classes in that branch. Call a branch singleton if its
collection has exactly one member. If that member is9m with m>1,
its actual cofactor AP contains ALL of R_i: at that word every low
original is absent on R_i and the sole high original must cover.
A pure9 singleton imposes no cofactor restriction.

Select any nonempty collection of singleton mixed branches with
actual cofactor moduli m_1,...,m_k, and put

    L=lcm(m_1,...,m_k).

Their actual phases are jointly compatible, since their cofactor
APs all contain the same nonempty R_i. Their intersection is one
class alpha modL and contains R_i. Then

    numerical3L is ORIGINAL.                       (LC1)

### An absent label would give a strict whole-cover descent

Suppose3L were absent. Delete ALL original height-two classes at
root i, including its pure9 guard if owned, and add the one CRT
class with ternary root i and cofactor phase alpha modL. Outside
root i nothing is removed. Inside it, retained low originals cover
every cofactor outside R_i, and the new3L covers R_i across all
three second-digit branches. This is a whole cover.

The new modulus is odd, nonunit and distinct from every retained
label by its assumed absence. Its nonternary exponents are original
ones, since L divides the complete color period Q_i. Each of the
three second-digit branches has at least one original high class;
otherwise it misses every point of R_i. Thus at least three labels
were removed and only one added, contradicting EB1. This proves LC1
by the existing joint replacement and singular-digit elimination
interfaces, not by a new general covering theorem.

Divisor closure now supplies original d and3d for every nonunit
d dividing L. These include cross-cofactor joins that need not
divide any one original9m_j. If the top-digit Simpson cut is tight
at this deep seed, its high-class count is exactly three, so all
three second-digit branches are singleton. The guard-owning seed
then forces3 times the lcm of its two mixed top cofactors; a seed
without a pure guard forces3 times the lcm of its three mixed top
cofactors. This is more than the count bound alone, but does not
assert that those labels were absent in every possible source.

### An occupied ancestor has a real private obligation

When3L is already original, its ternary root is i by concentration.
Its old cofactor phase beta differs from alpha modulo L: R_i is
nonempty, avoids every original low class, and lies in alpha modL.
Reassigning this occupied3L to alpha while deleting the high batch
does NOT preserve coverage. An original private point of3L lies in
beta, misses every other original, and also misses the new alpha
phase. The proposed output leaves that same point uncovered.

Consequently LC1 is an actual numerical-availability consequence.
It neither repairs the occupied ancestor's private region nor
excludes all tight-cut configurations. The argument reuses PH1--PH2,
CP5, SC1 and the elimination interface in
[Report343, section4](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md).
No new cut theorem, enumeration or Lean verification is asserted.

## 80. Existing Simpson cuts control the shared-prime column deficit

Keep H_3=1 and R={p}, but allow arbitrary original p-height A.
Use section75's irredundant whole quotient C_i with original label
set D_i={d:i in V_d}. Its pruning and original private witnesses
are already established there. Section71 gives the exact overlap

    D_1 union D_2=D minus {3},
    D_1 intersect D_2={p^a:a in I_0}.

This counts original labels, not equality of quotient moduli.
Put A_i=max_(d in D_i)v_p(d). Each quotient keeps the full original
height H_q of every q in S_i, since original q^H_q has private color
i. Its period is p^A_i product_(q in S_i)q^H_q, and

    max(A_1,A_2)=A,  I_0 subset [1,min(A_1,A_2)].

### The published cut applies to each actual irredundant quotient

Reuse [Report343, section2](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md)
and the geometric form in Balister--Bollobas--Morris--Sahasrabudhe--Tiba,
[*The structure and number of Erdős covering systems*, Appendix
Theorem A.1](https://arxiv.org/pdf/1904.04806v2), page31. In a minimal
coordinate-hyperplane cover, the number of members touching a nonempty
selected coordinate set is at least one plus the sum of its coordinate
alphabet sizes minus one. Numerical multiplicity one and disjointness
are not hypotheses.

Select exactly the p-digits h,...,A_i in the quotient's prime-digit
coordinates. An AP touches them exactly when its original label is
divisible by p^h. Consequently

    N_i(h):=#{d in D_i:p^h divides d}
           >=1+(p-1)(A_i-h+1),  1<=h<=A_i.          (FC1)

Let Theta_i(h) be that right side for h<=A_i and zero otherwise.
With N(h)=#{d in D:p^h divides d} and I(h)=|I_0 intersect [h,A]|,
the original-label intersection gives

    N(h)+I(h)=N_1(h)+N_2(h)>=Theta_1(h)+Theta_2(h). (FC2)

Using every coordinate in each quotient gives, by the same exact
overlap accounting,

    |D|>=3+(p-1)(A_1+A_2)
           +sum_(q in S_1 union S_2)H_q(q-1)-|I_0|. (FC3)

Compared with the original cover's aggregate Simpson bound, this
adds (p-1)min(A_1,A_2)-|I_0|, at least (p-2)min(A_1,A_2). These
are applications of the existing theorem to the proved quotients.

For the actual nonpure columns let

    U_i={u>1:gcd(u,3p)=1, pu in D, supp(u) subset S_i},
    a_u=max{b:p^b u in D},
    T_i(h)=sum_(u in U_i)(a_u-h+1)_+,
    g_i(h)=#{u in U_i:p^a_u u in G, a_u>=h},
    c_i(h)=#{b>=h:i in V_(p^b)},
    j_i(h)=#{b>=h:3p^b in D, a_(3p^b)=i mod3}.

Here G is section69's set of globally maximal concentrated3-free
p-bearing originals. PI6 supplies the original3-child of every
column level below a_u. Its top has that child exactly when it is
not globally maximal. Thus the count is exact:

    N_i(h)=c_i(h)+j_i(h)+2T_i(h)-g_i(h).

Together with FC1 this gives

    g_i(h)<=c_i(h)+j_i(h)+2T_i(h)
                  -1-(p-1)(A_i-h+1), h<=A_i.      (FC4)

These are tail-height constraints. The Hall deficit of section71
uses prefix demands; FC4 alone does not make it vanish.

### At p-height one the minimum inventory has rigid actual phases

Now set H_p=1. Section75 supplies a nonpure p-bearing original in
each color. Divisor closure supplies a concentrated original pu,
and the proper-divisor payer DP1 supplies original3p. Let j be its
actual ternary color, k the other color, and e_i=1_(i=j). Write
u_i=|U_i|, u=u_1+u_2 and g_i=|G intersect {pu:u in U_i}|.
Here I_0={1}, A_1=A_2=1, and

    N_i(1)=1+e_i+2u_i-g_i>=p,
    2u_i-g_i>=p-1-e_i.

Since p is odd, these imply

    u_i>=(p-1)/2,  u>=p-1,
    |G|<=2u-2p+3,
    delta=max(|G|-1,0)<=2(u-p+1).                  (FC5)

The deficit formula is the existing specialization from section71.
If u=p-1, put h=(p-1)/2. Then

    u_1=u_2=h,  g_k=0,  g_j<=1,  delta=0.

The quotient C_k has exactly p p-bearing originals: p and p-1
nonpure labels. Let E_k be its cofactor region avoiding all p-free
quotient classes. It is nonempty because p retains a private point.
At each point of E_k the p-bearing originals cover every p-root.
Original p occupies0, and all others avoid0 by comparable
disjointness. The p-1 other labels therefore occupy the nonzero
roots bijectively, and EVERY one of their cofactor APs contains
E_k. In particular each original pair pu,3pu has the SAME cofactor
phase modulo u and different actual p-roots. This phase conclusion
uses one nonempty E_k and all its actual coverage requirements.

Zero Hall deficit is an inventory statement. Its payers are occupied
original classes with actual private obligations. The next section
uses explicit whole-cover transports to turn this minimum-column
case into further exclusions; FC1--FC5 by themselves do not prove
unrestricted noncoverage or any new Lean result.

## 81. Minimum shared-prime columns force a narrow p=5 phase layout

Keep H_3=H_p=1, R={p} and section80's MINIMUM total nonpure column
count u=p-1. Let j own original3p and let k be the other color.
Put h=(p-1)/2. The established counts give u_j=u_k=h,
g_k=0 and g_j<=1. All other original prime heights are unrestricted.

### For p at least7 the minimum inventory gives strict descent

The actual number of3p-bearing originals in color i is
u_i-g_i+e_i, with e_j=1 and e_k=0. Each blocks at most one root,
so section78's clean sets satisfy

    |B_i|<=h-g_i+e_i,  |W_i|>=h+g_i-e_i.

Consequently |W_k|>=h and |W_j|>=h-1. For p>=7 these bounds
supply at least three and two clean roots, respectively. Section78's
complete six-leaf replacement contradicts EB1. Thus

    H_3=H_p=1, R={p}, p in {7,11,13} ==> u>=p.     (FL2)

This uses an actual whole-cover descent beyond FC5's zero inventory
deficit. It does not impose a bound on any other prime's height.

### For p=5 a two-depth frontier eliminates another minimum case

Now p=5 and u=4, so u_j=u_k=2. Section80's equality phases give
exactly two clean roots in color k. Each contains ONE original pm;
call the two cofactors a,b. The other two nonzero roots contain
their original3pm partners. Both cofactor APs contain the same
nonempty residual E_k that avoids all color-k p-free quotient classes.

Suppose |W_j|>=2. Retain every original p-free AP and use this
complete ternary frontier for the replacement of the p-bearing classes:

- Root j has three depth-two leaves, assigned p-root0 and two
  distinct clean nonzero roots of color j.
- Two depth-two leaves of root k are assigned its two clean roots.
  Its third depth-two cylinder is internal.
- The three depth-three children of that cylinder are assigned
  p-root0 and the same two clean roots of color k.

At each nonzero receiving leaf use its own color's original pm
subbatch, with the complete original cofactor phases. Section78's
same-source proof supplies RS1 at every such leaf; old p-height one
and old ternary height one mean no hidden old tail is dropped.
Each root0 leaf is covered by one pure guard from original p.

The two color-k originals are each used once at depth two and once
at depth three, giving9a,9b,27a,27b. At most two color-j originals
are used, each once. The two pure guards have moduli9 and27. Thus
at most EIGHT classes replace the entire p-bearing inventory.
At a fixed depth an original is used once. Different depths cannot
collide since every cofactor is3-free; cofactors from opposite colors
have disjoint nonempty prime supports. The pure guards are unique,
and every retained original has ternary height at most one. These
are actual distinct odd output labels, with no retained collision.

The original p-bearing count is

    1+4+(4-g_j+1)=10-g_j>=9.

The replacement therefore strictly decreases the total class count.
An EB1 source at p=5,u=4 must instead satisfy

    g_j=g_k=0,
    |B_j|=3, |W_j|=1, |B_k|=2, |W_k|=2.           (FL3)

Indeed |W_j|>=1, and its being exactly one requires
3=|B_j|<=3-g_j. No equal-count weight comparison is needed.

### Original privacy determines the remaining doubled cell

Let E_j be the nonempty region of X_j avoiding ALL p-free quotient
classes. It is independent of p. In FL3, original3p and the two
original3pm labels occupy three distinct nonzero p-roots in color j.
Its fourth root is the only clean root and must contain a3-free pm.

It cannot contain BOTH such originals. If it did, each of the two
nonpure3pm roots would be singleton. Whole coverage forces E_j into
both of their cofactor APs. A pm cofactor phase of the SAME modulus
as its own3pm partner then either misses E_j or contains all of it.
Coverage at the clean root forces one to contain E_j, preventing
the other's privacy at ternary root j. That other's only possible
private color is j by the original reset, a contradiction.

Name the single clean-root original pu and the other3-free original
pv. The latter cannot occupy the original3p root, since original3p
covers its entire possible private region at root j. Nor can pv
occupy the root of3pu. In that case its own3pv root is singleton,
forcing E_j into the3pv cofactor AP. The pv phase then either misses
E_j, destroying its own privacy, or contains E_j, destroying the
privacy of3pu at their shared root. Both contradict original
irredundancy.

Thus the only remaining p-root layout in color j is

    pu and3pu: different singleton roots, equal u-cofactor phase;
    3p:        a third singleton root;
    pv and3pv: the fourth root, distinct v-cofactor phases.

The singleton roots force E_j into the common u phase. Privacy of
pv and3pv supplies points of E_j in EACH of their two v phases;
coverage at the shared root gives

    nonempty E_j subset (alpha mod u)
                     intersect ((beta mod v) union (gamma mod v)),
    beta!=gamma mod v,  E_j meets both v classes.   (FL4)

In particular v does not divide u: otherwise the one u phase fixes
one v phase and cannot meet both. The two nonunit cofactors are a
divisor-closed numerical set, by original divisor closure. Hence
either u,v are distinct primes, or u=q and v=q^2 for one prime q.
The statement concerns these two p-bearing columns; it does not
truncate the full color carrier or bound p-free original heights.

FL4 is a necessary actual-source layout, not an uncovered point.
Larger column inventories and higher p or ternary heights remain
outside these minimum-column descents. These constructions use the
existing PH/RS interfaces and FC5; no new enumeration, generic
covering theorem or Lean verification is asserted.

## 82. Actual phase intersections exclude distinct-prime guarded columns

Keep section81's final p=5,u=4 layout, including its actual nonempty
residuals E_j,E_k. Let A_u be the common cofactor phase of guarded
color j's singleton pair, and B_v,C_v the two different phases of
its doubled cell. Write A_a,A_b for the two cofactor phases in
color k. FL4 and section80's equality phases give

    E_j subset A_u intersect (B_v union C_v),
    E_k subset A_a intersect A_b.

Suppose u and v are distinct primes. The opposite-color cofactors
a,b are distinct but need not be coprime; their nonempty prime
supports lie in S_k, disjoint from S_j. Every cofactor is coprime
to15. Retain every original5-free AP unchanged, delete the ten
original5-bearing classes, and insert these NINE complete APs:

| Receiving ternary residue | Cofactor condition | Modulus |
| --- | --- | --- |
| j mod9 | none | 9 |
| j+3 mod9 | A_u | 9u |
| j+6 mod9 | B_v | 9v |
| j+6 mod9 | A_u and C_v | 9uv |
| k mod9 | A_a | 9a |
| k+3 mod9 | A_b | 9b |
| k+6 mod27 | none | 27 |
| k+15 mod27 | A_a | 27a |
| k+24 mod27 | A_b | 27b |

The last three leaves partition k+6 mod9. Since u,v are coprime,
A_u intersect C_v is ONE actual CRT class modulo uv. The fourth
row uses PH1's direct joint-repair rule; it does not assert that5uv
was original or that every output comes from an RS1 single-label
transport. All its phase data belong to this same original source.

An output point missed by retained5-free originals has nonzero
ternary root i, since original3 is retained. Its complete X_i
coordinate lies in E_i. In root j, pure9 covers the first leaf,
9u covers the second, and9v or9uv covers the third according to
which v phase occurs. The added u condition on9uv holds throughout
E_j. In root k each of the five receiving leaves is covered because
both A_a and A_b contain E_k. This proves whole output coverage.

All labels are odd and greater than one. Every retained label has
ternary height at most one. The height-two cofactor list

    1,u,v,uv,a,b

has no repetition: u,v are distinct primes; a!=b; and the two
nonempty color supports are disjoint. At height three the cofactors
1,a,b are distinct. Different ternary heights cannot collide. The
output carrier may retain every complete original nonternary height
apart from5, and extend the ternary height to three; uv already
divides the original carrier.

Nine new classes replace ten old classes, with all5-free originals
unchanged, contradicting EB1. Therefore the minimum four-column
flat-five branch must have guarded cofactors

    u=q, v=q^2 for one original concentrated prime q. (FL5)

This constructor does not cover FL5. There A_q intersect C_(q^2)
is still a modulus-q^2 AP and repeats the third row's numerical
label. Replacing it by a single q^3 AP would drop most of that
original phase; the exact refinement would require all q lifts.
The remaining power-column case, larger inventories and arbitrary
heights are unresolved. No finite search, priority claim or Lean
verification is asserted.

## 83. A distinct-prime opposite palette also gives nine-for-ten descent

Keep section82's surviving guarded palette u=q,v=q^2, together with
the SAME original phases and residual sets. Thus

    E_j subset A_q intersect (B_(q^2) union C_(q^2)),
    E_k subset A_a intersect A_b.

Suppose the opposite cofactors a,b are distinct primes. Their
intersection is one complete actual AP modulo ab. Retain all
original5-free classes and replace the ten5-bearing classes by:

| Receiving ternary residue | Cofactor condition | Modulus |
| --- | --- | --- |
| k mod9 | A_a | 9a |
| k+3 mod9 | A_b | 9b |
| k+6 mod9 | A_a and A_b | 9ab |
| j mod9 | none | 9 |
| j+3 mod9 | A_q | 9q |
| j+6 mod9 | B_(q^2) | 9q^2 |
| j+6 mod27 | none | 27 |
| j+15 mod27 | A_q | 27q |
| j+24 mod27 | C_(q^2) | 27q^2 |

The first three classes cover E_k at all three root-k leaves. In
root j, the first two depth-two leaves are covered outright. On
its third leaf the9q^2 class already covers the B phase. Any
remaining demand belongs to C and also to A_q. Its three depth-three
children are covered respectively by pure27,27q and27q^2. This
checks the entire retained complement, because a point missed by
all retained originals has its own color coordinate in E_i.

The height-two cofactor list is1,q,q^2,a,b,ab, all distinct;
the height-three list is1,q,q^2. The two colors have disjoint
nonempty supports and all cofactors are3-free. None of these
labels collides with a retained original of ternary height at
most one. All added conditions are complete APs with phases from
the actual common source, and every original non-5 height can
remain in the output carrier. Nine classes replace ten, yielding
a strict EB1 count descent.

Each original two-column palette is divisor-closed. Having excluded
distinct-prime palettes in either color, the minimum u=4 source at
p=5 must therefore have

    U_j={q,q^2}, U_k={r,r^2}, q!=r.                (FL6)

The primes q,r are concentrated in opposite colors. This does NOT
say S_j={q} or S_k={r}: other primes and arbitrary larger heights
can occur in the retained5-free inventory. For the remaining
prime-power palette, A_r intersect A_(r^2) still has modulus r^2,
so the third row above would repeat the second row's label.
FL6 remains an unexcluded layout, not a full covering example.
No additional experiment or Lean verification is asserted.

## 84. The actual low-cofactor complement imposes a colorwise reciprocal threshold

Keep CP1–CP5's one all-concentrated two-color EB1 original cover, with full ternary height H≥2. For i∈{1,2}, use the complete original cofactor carrier

    Q_i=product_(p∈S_i)p^H_p,   X_i=Z/Q_i,
    R_i=sum_(m|Q_i,m>1)1/m,
    theta_H=sum_(a=2..H)3^(1−a)=(1−3^(1−H))/2<1/2.

Write Ω_i for the complete first-three root i in Z/3^H, with normalized counting measure, and give X_i normalized counting measure. Let G_i⊆Ω_i be the union of the actual original pure-three guards owned by this root, and put beta_i=mu(G_i). Every pure-three power through H is original. Comparable-class disjointness makes these guards disjoint and excludes root0, so

    beta_1+beta_2=theta_H,   0≤beta_i≤theta_H.       (CM1)

Let L_i⊆X_i be the union of the actual cofactor classes of the group-i low originals m and3m, with m>1, and put U_i=X_i\L_i. Numerical distinctness permits at most two such classes for each cofactor divisor m. Thus

    mu(U_i)≥max{0,1−2R_i}.                          (CM2)

The same set U_i is retained at every complete ternary word. By CP5, every point of (Ω_i\G_i)×U_i must be covered by an actual group-i original3^a m with a≥2 and m>1. For each numerical pair(a,m), at most one such original exists. Its mass under this one product measure is exactly3^(1−a)/m. Summing over every possible pair only enlarges the actual inventory, giving

    (1−beta_i)mu(U_i)
      ≤sum_(actual group-i3^a m,a≥2,m>1)3^(1−a)/m
      ≤theta_H R_i.

Consequently

    (1−beta_i)max{0,1−2R_i}≤theta_H R_i,

    R_i≥(1−beta_i)/(2(1−beta_i)+theta_H)
       ≥(1−theta_H)/(2−theta_H)>1/3.                (CM3)

For R_i≥1/2 the second line is automatic; for R_i<1/2 it is the rearrangement of the first. All masses are relative to a single ternary root, which accounts for the factor3^(1−a). No conditional cofactor law or separately selected tail witness is used.

### The color not owning the original9 has a stronger threshold

Let j be the first-three root of the original pure9 class, and let k be the other nonzero root. The9 guard has relative root mass1/3, so CM1 gives beta_k≤theta_H−1/3. Substitution in CM3 yields

    R_k≥(4/3−theta_H)/(8/3−theta_H)>5/13.           (CM4)

At H=2 the exact guard masses are beta_j=1/3 and beta_k=0. Hence

    R_j≥2/5,   R_k≥3/7.                            (CM5)

These are necessary inequalities for the same original family. They do not assert that arbitrary choices of the two color inventories can be realized jointly.

### Restrictions on two-prime color supports

For a single prime p≥5, finite original height gives R_i<1/(p−1)≤1/4, contradicting CM3. If S_i={p,q}, with p<q, then

    R_i< p*q/((p−1)(q−1))−1.

The strict inequality retains the finite original heights. For p≥7 the right side is at most17/60, attained at p=7,q=11. For p=5 and q≥17 it is at most21/64. Thus CM3 leaves only

    {5,7}, {5,11}, {5,13}

as possible two-prime supports. For the color k not owning9, CM4 leaves only{5,7}: the next largest two-prime Euler limit is3/8 for{5,11}, below5/13. At H=2, CM5 leaves only{5,7} for either color. The supports are disjoint, so they cannot both be two-prime supports. These restrictions do not imply that each color has at least three primes; the finite-height Euler masses on{5,7} can exceed both thresholds in CM5. No new lower bound on the total number of support primes is claimed.

The deduction uses CP5's actual complete-root cover and the same low-cofactor complement as section74, now measuring the entire complement instead of selecting one point. Its measure estimates are elementary product counting and the union bound; it is not another Simpson cut or HSW construction. The HSW budget conditions CP11–CP12 and SC4 remain the existing conditional descent criteria. Arbitrary color supports can have larger divisor reciprocal mass, so CM3–CM4 alone do not exclude the remaining all-concentrated branch or establish a strict count or modulus-sum descent. These are ordinary deductions, with no Lean verification or priority claim.

### The same threshold applies with arbitrary nonconcentrated support

The all-concentrated hypothesis is unnecessary for the measure
inequality. Keep section73's partition R,S_1,S_2 of the nonternary
support, with arbitrary H>=1, and set

    P_i=R union S_i,
    Qhat_i=product_(p in P_i)p^H_p,
    Rhat_i=sum_(m|Qhat_i,m>1)1/m.

Section74's singleton-root elimination gives whole coverage of root
i by the actual originals whose nonternary support is contained in
P_i. This statement precedes, and does not require, the additional
small-prime condition used for CP19. Every retained coordinate keeps
its full original height. Form the low union from the surviving
originals m and the surviving3m classes active at root i; retain
every actual pure-three guard there. The same fixed-complement
argument gives

    Rhat_i>=(1-beta_i)/(2(1-beta_i)+theta_H).         (CM6)

Only numerical distinctness bounds the low inventory by2Rhat_i
and the high product inventory by theta_H Rhat_i. Originals
supported entirely on R can occur in both retained families. Each
inequality is proved separately on its actual retained carrier;
no disjointness or irredundancy of these families, and no duplicated
joint inventory budget, is asserted.

For H>=2, CM1--CM5 remain valid with Rhat_i in place of R_i.
In particular each Rhat_i>1/3, and the root not owning9 has
Rhat_i>5/13. For H=1, theta_H=beta_i=0, giving Rhat_i>=1/2.

If R={p} and S_i were empty, its retained carrier would be p^H_p
and

    Rhat_i=sum_(a=1..H_p)p^(-a)<1/(p-1)<=1/4,

contrary to CM6 at every H>=1. Thus a unique nonconcentrated prime
forces BOTH concentrated color groups to be nonempty at arbitrary
ternary height. This extends section75's nonemptiness conclusion,
not its height-one common private-source construction.

The individual two-prime tests apply to P_i, not to S_i. At H=1
every P_i has at least three primes: the largest two-prime Euler
limit is11/24<1/2. Hence R={p} further gives |S_i|>=2 at H=1.
When R is nonempty the P_i overlap, so disjoint-support consequences
from the all-concentrated case cannot be carried over. Larger
reciprocal inventories remain possible under these necessary bounds;
unrestricted noncoverage is not established.

## 85. The three actual square residuals have no further congruence concentration

Keep section83's surviving layout, including the complete original
color carriers X_j,X_k and their periods M_j,M_k. Put

    E_j^B=E_j intersect B_(q^2),
    E_j^C=E_j intersect C_(q^2).

Both sets are nonempty by FL4, and E_k is nonempty by section80.
Use PH3--PH4's congruence-hull construction on any nonempty Y in
X_i: choose y_0 in Y and set

    Gamma_i(Y)=gcd(M_i,{y-y_0:y in Y}).

The construction is independent of representatives and base point.
For each divisor t of M_i, Y lies in one residue modulo t exactly
when t divides Gamma_i(Y). The remaining minimum-column source must
satisfy

    Gamma_j(E_j^B)=Gamma_j(E_j^C)=q^2,
    Gamma_k(E_k)=r^2.                              (FL7)

These equalities concern the actual residual sets with every
original higher prime digit retained.

### Additional concentration of a guarded square branch gives strict descent

Suppose Gamma_j(E_j^C)>q^2. Since q^2 divides this hull, it has a
divisor t distinct from1,q,q^2. Choose the actual class T modulo t
containing E_j^C. Retain all5-free originals, delete the ten5-bearing
originals, and insert:

| Receiving ternary residue | Cofactor condition | Modulus |
| --- | --- | --- |
| j mod9 | none | 9 |
| j+3 mod9 | A_q | 9q |
| j+6 mod9 | B_(q^2) | 9q^2 |
| j+6 mod9 | T | 9t |
| k mod9 | A_r | 9r |
| k+3 mod9 | A_(r^2) | 9r^2 |
| k+6 mod27 | none | 27 |
| k+15 mod27 | A_r | 27r |
| k+24 mod27 | A_(r^2) | 27r^2 |

The root-k rows are section82's complete five-leaf repair. On root
j, the first two leaves cover E_j because E_j is contained in A_q.
On its third leaf the B portion is covered by9q^2 and the C portion
by9t. Every point missed by the retained originals has its own
color coordinate in E_i, so all such points are covered. Root0 is
still covered by the retained original3.

At height two the cofactors are1,q,q^2,t,r,r^2. They are distinct:
t differs from1,q,q^2 and is supported in S_j, while r,r^2 have
support in the disjoint S_k. At height three the cofactors are
1,r,r^2. All are3-free, so different heights cannot collide. All
labels are fresh because retained originals have ternary height
at most one. Each row defines one actual AP by CRT, and all
original non-5 heights may remain in the output carrier.

Nine classes replace ten, contradicting EB1. Interchanging B and C
proves both guarded equalities in FL7. In particular t=q^3 is
legitimate only when the actual residual branch is already in one
q^3 prefix; no complete q^2 cylinder is replaced by a single lift.

### Additional concentration of the opposite residual gives strict descent

Suppose Gamma_k(E_k)>r^2. Choose a hull divisor t distinct from
1,r,r^2 and its actual phase T containing E_k. Use section83's six
guarded-root rows unchanged, and replace its three root-k rows by:

| Receiving ternary residue | Cofactor condition | Modulus |
| --- | --- | --- |
| k mod9 | A_r | 9r |
| k+3 mod9 | A_(r^2) | 9r^2 |
| k+6 mod9 | T | 9t |

Every root-k leaf covers E_k. The guarded-root repair remains
valid. The height-two cofactors are1,q,q^2,r,r^2,t and the
height-three cofactors are1,q,q^2; disjoint color supports and
the choice of t give distinct labels at each height. The same
freshness and complete-source coverage checks give nine classes
in place of ten, proving the last equality in FL7.

Consequently Gamma_j(E_j)=q. Indeed E_j is the union of its B and C
pieces, each with hull q^2, and their two different q^2 residues
have the same reduction modulo q. The hull of their union is the
gcd of the two piece hulls and one difference of base points, whose
q-depth is exactly one.

Every additional prime s in S_j other than q therefore takes at
least two first-root values on EACH guarded square residual.
Likewise every s in S_k other than r takes at least two first-root
values on E_k. When H_q>=3, neither guarded piece fits inside one
q^3 lift; when H_r>=3, E_k does not fit inside one r^3 lift.

These are necessary congruence-spread constraints. They give no
product structure, uniform density lower bound or exclusion of
the remaining layout. The arguments reuse PH3--PH4 and the actual
repairs of sections82--83; no Lean verification or priority claim
is asserted.

## 86. Irredundancy makes the square residuals exact products

Keep FL6's actual minimum-column source. Split the full color carriers as

    X_j=(Z/q^H_q) times Y_j,
    Y_j=product_(s in S_j, s!=q) Z/s^H_s,

and analogously X_k=(Z/r^H_r) times Y_k. Let C_beta,C_gamma be the
complete q-coordinate cylinders at the two original q^2 phases B,C,
and let C_delta be the complete original r^2 cylinder of E_k. All
higher q- and r-digits remain in these cylinders. There are nonempty
actual auxiliary residuals F_j in Y_j and F_k in Y_k such that

    E_j=(C_beta union C_gamma) times F_j,
    E_k=C_delta times F_k.                         (FL8)

In particular, the two guarded square pieces have the SAME auxiliary
residual. This strengthens their common first-q phase and separate
congruence-hull constraints.

### An active high-depth original cannot meet a filled square cylinder

On either C_beta or C_gamma, the original5-bearing classes in the
root-j quotient already cover every5 root, independently of all
auxiliary coordinates. The original5 covers root0;5q and15q cover
their two singleton roots;15 covers the third nonzero root; and
the corresponding5q^2 or15q^2 covers the remaining root. The
root-k cylinder C_delta similarly fills all five roots using5
and the four nonpure originals.

Section75 preserves original privacy in these actual quotients.
If an active5-free original had q-depth at least two and met
C_beta or C_gamma, its whole quotient AP would lie inside that
cylinder. It would already be covered by the5-bearing originals,
contradicting its private point. Thus its q^2 phase avoids BOTH
beta and gamma. The analogous r-depth condition excludes delta
for every active5-free original in the other quotient.

The5-free originals that can meet the square cylinders therefore
have q-depth zero or one, or r-depth zero or one respectively.
In color j their membership predicates are identical on C_beta
and C_gamma, since both have the same first-q coordinate alpha.
They also ignore all higher q-digits. Define F_j as the complement
of this actual common trace on Y_j. The existing containment of
E_j in the two square cylinders now gives the first equality in
FL8. The same argument gives F_k and the second equality.
Nonemptiness follows from the already nonempty original residuals.

Each F_i is the complement of an actual auxiliary AP family with
numerical multiplicity at most FOUR. For a fixed auxiliary modulus
m, only the original labels m,3m,qm,3qm can contribute to the
root-j trace; use r instead of q in root k. A modulus-one trace
cannot occur, since it would make F_i empty. The relevant phases
come from the original source. This family need not be a whole
cover and need not have multiplicity at most two.

### Reuse singular elimination with its exact numerical collisions

[Report343, section4](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md#4-奇异-dp-保真到哪一层)
already supplies Kullmann's generalized singular Davis--Putnam
elimination, arXiv:1103.3693v1, Lemma1.6.1. Apply it to the sole5
digit in each actual irredundant quotient. Its value-occurrence
counts are(1,1,1,1,2) in color j and(1,1,1,1,1) in color k.
All other prime digits remain untouched, so the actual resolvents
are respectively the two q^2 phases beta,gamma and the single
r^2 phase delta. Thus

    G_j=(actual5-free quotient classes) union {beta modq^2,gamma modq^2},
    G_k=(actual5-free quotient classes) union {delta modr^2}

are irredundant whole AP covers on the disjoint supports S_j,S_k.
Each quotient loses exactly four labels. This is a direct use of
the published theorem, not a new general elimination result.

The numerical collision is explicit. Original q^2 and3q^2 both
exist by divisor closure and contribute different q^2 phases to
the root-j quotient. The high-depth exclusion above makes both
different from beta,gamma. Thus G_j has exactly FOUR classes of
modulus q^2, while every other numerical modulus has at most two.
Likewise G_k has exactly THREE classes of modulus r^2 and at most
two at every other modulus. All moduli are greater than one and
coprime to30; all other original heights are retained.

These are actual whole covers, but their exceptional numerical
repetitions prevent direct use of SO1's multiplicity-two premise.
The two quotient count decreases cannot be added as a decrease of
the original family, because original5 belongs to both quotients.
No distinct-modulus descent or Lean verification follows from this
elimination alone.

## 87. Shared ternary labels impose a joint reciprocal constraint at every height

Return to section84's arbitrary-height source, with nonternary support
R,S_1,S_2 and the same retained root families. Keep every original
height, and set

    Q_R=product_(p in R)p^H_p,
    rho=sum_(m|Q_R,m>1)1/m,
    Rex_i=Rhat_i-rho,
    theta=theta_H, tau_i=1-beta_i,
    s_i=(2*tau_i+theta)*Rhat_i-tau_i.

Here Rex_i is the reciprocal divisor inventory whose support meets
S_i, not an actual residual measure. CM1 gives beta_1+beta_2=theta,
including theta=0 at H=1, and CM6 gives s_i>=0. Original numerical
label ownership additionally requires, for ALL nonnegative real
lambda_1,lambda_2,

    lambda_1*s_1+lambda_2*s_2
      >=rho*[min(lambda_1*tau_1,lambda_2*tau_2)
             +theta*min(lambda_1,lambda_2)].         (CM7)

In particular,

    s_1+s_2>=(1+min(beta_1,beta_2))*rho.            (CM8)

If R is nonempty, simultaneous equality in the two separate CM6
thresholds is impossible. The correction comes from labels that
cannot belong to both ternary roots.

### Count the same shared originals once where they have one owner

Let ell_i be the SUM of cofactor reciprocal weights of the actual
low originals m,3m in root i, with m>1. Let h_i be the sum of
3^(1-a)/m over its actual retained high originals3^a m, a>=2,m>1.
Section84's complement inequality and the low union bound give

    tau_i<=tau_i*ell_i+h_i.                         (CM9)

This remains valid when the low reciprocal sum exceeds one; no
assumption that Rhat_i<1/2 is needed.

Separate the shared and exclusive numerical inventories. Let f be
the reciprocal sum of actual3-free originals m>1 supported only
on R. Let a_i be the reciprocal sum of actual3m supported only
on R and owned by first-three root i. Let b_i be the high sum
of3^(1-a)/m for actual3^a m supported only on R and owned by i.
Write ell_i^ex,h_i^ex for the corresponding inventories whose
cofactor support meets S_i. Then exactly

    ell_i=ell_i^ex+f+a_i,
    h_i=h_i^ex+b_i.

A3-free shared original really occurs in both retained families.
A3-bearing shared original has only ONE first-three root. The
retained original3 and comparable-class disjointness exclude root0
for every other3-bearing original. Numerical distinctness therefore
gives the joint bounds

    f<=rho, a_1+a_2<=rho, b_1+b_2<=theta*rho,
    ell_i^ex<=2*Rex_i, h_i^ex<=theta*Rex_i.          (CM10)

The divisor inventories permit every possible label and height
pair. Missing original labels only improve these upper bounds;
no saturated inventory or maximizing root allocation is asserted
to be realizable.

Multiply CM9 by lambda_i and sum. CM10 gives

    sum_i lambda_i*tau_i
      <=sum_i lambda_i*(2*tau_i+theta)*Rex_i
        +rho*[lambda_1*tau_1+lambda_2*tau_2
               +max(lambda_1*tau_1,lambda_2*tau_2)
               +theta*max(lambda_1,lambda_2)].

For example, the shared low mixed contribution is at most
rho*max(lambda_1*tau_1,lambda_2*tau_2), because there is one
shared3m pool. The high shared pool similarly pays only the
maximum weight. Substitute Rex_i=Rhat_i-rho and rearrange to
obtain CM7. Equal weights and beta_1+beta_2=theta give CM8.

Each inequality concerns the same original family. The two
normalized retained carriers can differ: the same numerical
cofactor m has weight1/m in either full carrier. This accounting
does not combine unrelated phase choices or conditional laws.

### Two breakpoints suffice for the weighted condition

Exchange the root names if necessary so tau_1>=tau_2>0. CM7 is
equivalent to s_1,s_2>=0 together with

    s_1+s_2>=rho*(tau_2+theta),
    tau_2*s_1+tau_1*s_2>=rho*tau_2*(tau_1+theta).   (CM11)

For lambda_2>0 set x=lambda_1/lambda_2. The difference between
the two sides of CM7 is affine between its only two breakpoints
x=tau_2/tau_1 and x=1. CM11 checks those points; the individual
nonnegative slacks control the end directions. Zero weights add
only those individual inequalities.

At H=1, tau_1=tau_2=1 and theta=0. Alongside CM6, this reduces to

    Rhat_1+Rhat_2>=1+rho/2.                         (CM12)

SO1 remains a separate support constraint at height one; no sieve
calculation is repeated here. At higher heights the argument uses
the actual root complement and full inventory, without assuming
multiplicity two after removal of the ternary coordinate.

These are necessary joint inventory bounds, not phase-realization
criteria or strict EB1 descents. Larger reciprocal inventories can
satisfy them. No unrestricted noncoverage or Lean verification is
asserted.

## 88. A reserved distortion margin excludes the remaining flat-five minimum

The exceptional square multiplicities in section86 can be paid from
the existing distortion continuation margin. The reusable input is
[Report348, SO1](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#two-multiplicity-two-covers-share-a-small-prime):
the KKL repeated-label moment bound and the BBMST continuation
criterion, with arbitrary finite prime heights. No sieve table is
recomputed.

### Two additional prime-square classes cannot fill the reserved mass

Let B be any finite labelled AP family whose moduli are greater
than one and coprime to210, each used at most twice. Include any
additional square moduli in one complete ambient period. Construct
the actual BBMST distortion measures P_i from B; unused coordinates
are uniform. Number all ordinary primes, including absent primes,
so p_4=7 and the first four bad sets B_i are empty. Put

    a_i=(3*p_i-1)/(p_i-1)^2,
    b_i=1/[4*(p_i-1)^2],
    C_i=product_(4<j<=i)[1+a_j/(1-delta_j)].

The existing labelled second-moment estimate gives, for every later
allowed distortion sequence,

    M_i^(2)<=4*C_(i-1)/(p_i-1)^2.

Absent-prime factors in C_i only enlarge this bound. Reserve one
fifth by defining the SCALAR accounting quantities

    nu_i=4/5-sum_(4<j<=i)P_j(B_j),
    F_i=4*C_i/nu_i when nu_i>0.

The probability measures are unchanged; no conditioning or
renormalization is performed. Initially nu_4=4/5 and F_4=5.
BBMST Lemma3.3 and the moment estimate imply

    nu_(i-1)-nu_i=P_i(B_i)
      <=nu_(i-1)*b_i*F_(i-1)/[delta_i*(1-delta_i)].

Whenever b_i*F_(i-1)<delta_i*(1-delta_i), this proves nu_i>0 and

    F_i<=[1+a_i/(1-delta_i)]
          *[1-b_i*F_(i-1)/(delta_i*(1-delta_i))]^(-1)*F_(i-1).

This is precisely BBMST Lemma6.2's recurrence(23). Its proof uses
the displayed loss difference, moment bound and nu_i*F_i=4*C_i;
it does not require the initial accounting mass to equal one.
The positive-denominator induction in Theorem6.1 uses the same
scalar recurrence. Table1 of arXiv:1811.03547v1, p.19, gives
g_4>=5.860938>5. The definition of g_4 before Corollary6.3
therefore supplies a successful scalar continuation from F_4=5,
followed by that analytic tail. Monotonicity of the recurrence
on its positive-denominator domain bounds the actual F_i by this
continuation, proving nu_n>0 at every finite final stage.

This uses the PROOF of the continuation criterion with a reserved
accounting mass. Corollary6.3's noncoverage statement by itself
would not supply the quantitative margin. All measures still
belong to the one actual base family B.

BBMST Lemma2.1 preserves earlier-coordinate marginals. Thus under
the SAME final probability P_n,

    P_n(union of the base classes)<=sum_i P_i(B_i)<4/5,
    P_n(R_base)>1/5.                               (RM1)

Lemma3.4, equation(11), applies to every residue class whose modulus
divides the ambient period, including omitted classes. An extra
pure-square class A=(c modq^2) therefore satisfies

    P_n(A)<=1/[q^2*(1-delta_q)]<=2/q^2.

The whole q-primary coordinate is processed once; the square does
not create a second distortion factor. Hence adding at most two
prime-square classes, with their primes at least11, gives

    P_n(R_base minus the extra classes)
      >1/5-4/121=101/605>0.                        (RM2)

This is a bound in the actual distorted probability, not in uniform
counting measure. Its positivity proves that the augmented family
cannot cover. More generally the same argument allows any finite
list of extra pure-square classes with sum_A 2/q_A^2<1/5.

### Apply the margin to the actual singular-elimination outputs

The two whole covers G_j,G_k of section86 have disjoint supports
S_j,S_k and all moduli coprime to30. At least one omits7. In that
cover remove enough occurrences of its exceptional square modulus
to leave numerical multiplicity at most two: two removals suffice
for G_j, and one suffices for G_k. The resulting base is coprime
to210. Its exceptional prime is at least11, so RM2 contradicts
whole coverage after the removed classes are restored.

Thus FL6 is impossible. Combining this with sections81--83 excludes
ALL minimum-column configurations at p=5. Together with FL2 and
CP17, the flat unique-nonconcentrated-prime branch satisfies

    H_3=H_p=1, R={p}
      ==> p in {5,7,11,13} and |U_1|+|U_2|>=p.    (FL9)

This retains every other original prime height. The argument
closes the minimum |U_1|+|U_2|=p-1 case; it does not exclude larger
column inventories, larger p or ternary heights, or several
nonconcentrated primes. Unrestricted Erdos7 remains unresolved.
The deductions reuse published moments, AP-mass bounds and the
published continuation threshold; no Lean verification is asserted.

## 89. Actual root capacity requires at least six flat-five columns

Keep H_3=H_5=1 and R={5}, but impose NO minimum-column equality.
Retain the complete original color supports and all their prime
heights. Let j own the original15, let k be the other color, and
write u_i=|U_i| as in section80. For every color i with7 not in S_i,

    u_i>=5-e_i, where e_i=1 if i=j and e_i=0 if i=k. (FL10)

In particular,

    u_j+u_k>=6.                                    (FL11)

If7 is in S_j the stronger total is at least7. If7 is in neither
color, it is at least9. These are original nonpure5-column counts,
not counts of independent optimized quotient sources.

### Reserve mass for the actual5-free cofactor remainder

Fix a color omitting7. Its retained5-free cofactor classes have
moduli coprime to210, with numerical multiplicity at most two:
only original m and3m can contribute to the same cofactor m.
Construct section88's distortion law for this actual family.
Use reserve3/10, so the initial accounting mass is7/10 and
the initial scalar is40/7<5.860938. The same published threshold
and reserved-mass proof give, under the resulting full-cofactor
probability P,

    P(E_i)>3/10,                                   (FL12)

where E_i avoids exactly this actual5-free family. No measure is
conditioned on E_i. For ANY original mixed cofactor phase modulo m,
BBMST Lemma3.4 in this same law gives

    P(a modm)<=2^omega(m)/m.

All prime factors of m are at least11. Hence every such bound is
at most2/11. Except for m=11 or m=13, it is at most2/17. Indeed
a different prime is at least17; a prime power of exponent at
least two gives at most2/121; and a cofactor with two distinct
prime factors gives at most4/(11*13)<2/17. Further factors only
decrease the product.

### Every required5 root spends its own original labels

There are t_i=4-e_i nonzero5 roots not covered by the possible
original15 at root i. The original5 occupies root0, and no other
pure5 power is present since H_5=1. At each of these t_i roots,
the actual mixed originals5m,15m of color i must cover EVERY
point of E_i. This follows from section73's whole-root pruning:
opposite-color originals have been removed by the same legal
source assignment, and the5-free originals all miss E_i.

A single mixed original covers P-mass at most2/11<3/10, so each
required root needs at least two such originals. Every original
has one fixed5 root. There are at most2u_i mixed originals in
total, since each column offers only5m and15m.

Suppose u_i<=t_i. The root demands force equality throughout:
exactly2t_i mixed originals, with exactly two at every required
root. A pair involving any cofactor other than11,13 has total
P-mass at most

    2/11+2/17=56/187<3/10,
    3/10-56/187=1/1870>0.

It cannot cover E_i. Thus all2t_i required originals would have
cofactor11 or13. Only four numerical original labels are available
with these cofactors:55,165,65,195. But2t_i>=6. This contradiction
proves u_i>=t_i+1=5-e_i, without assumptions on the other columns'
phases or on whether every potential original actually occurs.

The supports S_j,S_k are disjoint, so at least one omits7. FC5
already supplies u_i>=2 for either color. If j omits7, FL10 gives
u_j>=4 and hence the total at least6. If k omits7, it gives
u_k>=5 and hence the total at least7. Applying both when both
omit7 gives the stated total9.

This closes the four- and five-column cases under the stated flat
unique-shared-five hypotheses. It does not rule out six or more
columns, nonflat5 or3 heights, or more than one nonconcentrated
prime. The proof reuses the same continuation and actual AP-mass
interface; no new sieve computation or Lean verification is claimed.

## 90. A distorted actual-source budget retains every shared-prime height

Scope: one original EB1 source, H_3=1, R={p}, full shared-prime height A=H_p, and disjoint concentrated supports S_1,S_2. Nothing bounds A or the other original prime heights. Use the actual pruned whole quotients of Report385 section75 and the actual column data of section80. This is a consumer of existing source integration and the reserved distortion measure, not another moment theorem or a new sieve table.

### Existing suppliers and the new interface

The closest existing integration interfaces are Report378 SF8--SF9/NS10 and Report379 RF7--RF9. Report385 sections75/80 supply the actual own-color quotient, the pure-power deletions, original-private witnesses and exact column counts. Section89 supplies the cofactor distortion price. The additional interface puts the unconditioned cofactor law on the actual full product with the p-coordinate and retains the common original pure-power ownership when the two color inequalities are combined.

Let X_i be the full S_i carrier. Let E_i avoid ALL actual p-free quotient classes in color i, both original m and active3m. It is nonempty by section75. For any probability P_i on X_i with mu_i=P_i(E_i)>0, work on

    Haar_(Z/p^A) times P_i.

The probability is not conditioned on E_i.

Put

    S_A=sum_(a=1..A)p^(-a),
    I_i={a:i belongs to V_(p^a)},
    I_0=I_1 intersect I_2,
    J_i={a:original3p^a has ternary root i}.

All these sets describe one fixed original source. I_0 is not assumed to be an initial segment.

### Pure-power mass is exact after the established private-preserving pruning

In color i, section75 retains exactly the original pure p^a with a in I_i and the active original3p^a with a in J_i. Each retained class has a private point in that whole quotient. After fixing the ternary root, they are pure p-power cylinders on the full p-coordinate. Two such cylinders either are disjoint or one contains the other; containment would destroy privacy of the contained quotient class. Thus they are pairwise disjoint, including a p^a original against a3p^b original with a>b. This last case uses quotient privacy, not an incorrect claim that the two original numerical moduli are comparable.

Consequently their union mass is EXACTLY

    beta_i=sum_(a in I_i)p^(-a)+sum_(a in J_i)p^(-a).

Every original3p^a, 1<=a<=A, is present in this branch. For A>=2, reuse Report371 section2's actual top fan of a private point of p^A: it supplies a proper original multiple p^A m, m>1. For A=1, Report350 EB8 supplies an actual exponent-one child. If this child contains3, divisor closure supplies3p^A. Otherwise m contains a concentrated prime because R={p}; its original p^A m is concentrated, and DP1 with proper divisor e=p^A supplies3p^A. Divisor closure supplies all lower3p^a. This argument does not infer a proper multiple from the weaker statement p^A not in G.

Hence J_1 and J_2 partition{1,...,A}. Since I_1 union I_2 is the same full set,

    beta_1+beta_2=2S_A+sum_(a in I_0)p^(-a).        (PS)

There is no proved requirement that a singleton V_(p^a) agrees with the owner of3p^a; no such simplification is used. Individually,

    beta_i<=2S_A,
    1 not in J_i ==> beta_i<=2S_A-1/p.

These are inventory bounds on the exact masses, not claims that maximizing assignments are realizable.

### Actual mixed mass and a finite column upper bound

Write

    U_i={m>1:gcd(m,3p)=1, pm original, supp(m) subset S_i},
    a_m=max{a:p^a m is original},
    epsilon_m=1 if p^a_m m belongs to G, and0 otherwise.

Section80 already supplies the exact list of mixed labels: p^a m for every1<=a<=a_m and its3-child at all those heights except the globally maximal top when epsilon_m=1. Let

    c_m=2 sum_(a=1..a_m)p^(-a)-epsilon_m p^(-a_m).

For any cofactor prices w_i(m) bounding P_i of every residue class modulo m, define

    C_i=sum_(m in U_i)c_m w_i(m).

The actual mixed union on E_i times the full p-coordinate must cover the complement of the pure cylinders. Summing its actual original class masses gives

    (1-beta_i)mu_i
      <=sum_(actual mixed d=p^a m or3p^a m in color i)
           p^(-a) P_i(actual cofactor AP of d)
      <=C_i.                                      (MS)

Each summand uses its own actual phase in one product law. The final bound forgets those phases only in the upper direction. It retains every original p-height, and retains the missing-top correction. It neither changes the source nor asserts that the class bounds can be attained jointly.

### Coupling the same original pure-power inventory

Set

    L=2-2S_A-C_1/mu_1-C_2/mu_2.

Combining MS with the exact PS gives

    sum_(a in I_0)p^(-a)>=L.                       (CS)

No common probability on unrelated quotient candidates is introduced: both inequalities concern the two actual quotients of the same original source, and their pure-power terms share the exact original inventory.

This can feed the existing DP12 threshold, rather than only producing a scalar display. For1<=h<=A and0<=k<h, if

    L>sum_(a=1..k)p^(-a)+sum_(a=h+1..A)p^(-a),

then at least k+1 members of I_0 lie at depths at most h. Indeed the right side is an upper bound for any subset with at most k members in the first h positions, even after granting it every deeper position. This does not assume that I_0 itself is an initial segment. Such a consequence supplies actual pure-power ancestors to the already proved DP12 matching criterion; it does not show that all its inequalities hold or that a legal strict descent follows.

### Distortion consumers without a shared-prime height restriction

If S_i avoids5 and7, the actual p-free cofactor base has numerical multiplicity at most two and moduli coprime to210. Reuse section89's reserve3/10 with initial value40/7<5.860938. It gives

    mu_i>3/10,
    w_i(m)=2^omega(m)/m.

Let W_i=sum_(m in U_i)w_i(m). Since c_m<2/(p-1), MS yields the height-independent necessary tests

    W_i>3(p-3)/20,
    1 not in J_i ==> W_i>3(p^2-2p-1)/(20p).        (DT)

For p=5, choose a color without7; for p=7, choose a color without5. At least one exists because S_1,S_2 are disjoint. No reserve is granted to the other color unless its own support permits it. If both supports avoid5,7, both laws are available and CS also has the explicit strict lower bound

    sum_(a in I_0)p^(-a)
       >2-2S_A-(10/3)(C_1+C_2).

For p=5, DT is W_i>3/10, or W_i>21/50 when i does not own15. If U_i has two members, divisor closure makes it either{q,q^2} or two primes. The first has W_i<=24/121<3/10. Any pair of primes other than{11,13} has W_i<=2/11+2/17=56/187<3/10. Thus a no7 color with only two columns must own15 and have EXACTLY U_i={11,13}. A no7 color not owning15 has at least three columns, since the largest two-column weight is48/143<21/50.

For p=7, DT is W_i>3/5, or W_i>51/70 when i does not own21. All cofactor primes are at least11. The four largest possible distinct weights occur at11,13,17,19, and

    2/11+2/13+2/17+2/19=25800/46189<3/5.

Thus the no5 color has at least five columns. In the non-owning case, the six largest weights occur at11,13,17,19,23,29, and

    sum 2/q=22012256/30808063<51/70.

It therefore has at least seven columns. Composite weights are at most4/(11*13), below even2/29, so no composite displaces a displayed maximizer. These are a few exact rational comparisons, not a rerun of the published continuation or an enumeration of cover candidates.

### The general per-color column lower bound is already available

No new proof of u_i>= (p-1)/2 is needed. In section80, apply FC1 and its exact column identity at the actual quotient height A_i:

    p<=N_i(A_i)=c_i(A_i)+j_i(A_i)+2T_i(A_i)-g_i(A_i)
      <=2+2u_i.

Integer parity gives u_i>=(p-1)/2, at every full original height A; A_i need not equal A. Consequently, at p=7, the preceding no5 color bound gives total u>=8, strengthened to u>=10 if that color does not own21. At p=5, a no7 color not owning15 gives total u>=5. The separately proved flat-five result remains stronger when A=1.

The main new bridge is MS plus the exact shared-owner relation PS, not these few numerical consumers. Arbitrary A, actual I_0, original phases and the finite column coefficients remain visible. No proof that the coupled capacities are jointly attainable, no unrestricted noncoverage result, and no new Lean verification is asserted.

## 91. A complete initial ternary block gives finite-height distortion bounds

Keep section74's one EB1 original family, its complete ternary height H>=1,
and its actual retained family on a nonzero first-three root i. Its
nonternary support is P_i=R union S_i. Every original coordinate keeps its
full height. Section74's singleton-root elimination gives a whole cover
of this root by these retained originals, including its actual pure-three
guards. No multiplicity-two assertion is made after forgetting ternary
digits.

Write Omega_i for the complete root i in Z/3^H, with normalized counting
law lambda, and X_i for the full retained nonternary carrier. Let G_i be
the union of the actual pure-three guards in this root and put

    beta_i=lambda(G_i),  tau_i=1-beta_i,
    theta_H=(1-3^(1-H))/2.

The original pure-three classes are comparable and disjoint. Thus
beta_1+beta_2=theta_H and tau_i>0, as in CM1. Pure-three guards will not
participate in the nonternary bad sets below.

For the remaining originals, write d=3^a m with m>1 and 3 not dividing m.
At a=0 the class imposes no ternary restriction. At a>=1 it is retained
only if its actual first-three root is i. Its remaining ternary prefix
has relative depth a-1 in Omega_i. In particular an active a=1 class
also imposes no restriction within Omega_i. For every numerical pair
(a,m), there is at most one original label. Classes at the wrong first
root are absent; this only improves every upper bound below.

### Preserve the initial block in the actual distortion process

Start the BBMST distortion construction with the initial product law

    P_0=lambda times Haar_X_i.

Treat the ENTIRE finite block Omega_i as already read. Expose the
nonternary prime-power coordinates in increasing prime order. At a
nonternary prime p, its actual bad set is the union of the retained
non-pure-three originals whose largest nonternary prime is p, with their
original ternary prefixes and complete other phases. This is one process
on Omega_i times X_i, not separate choices of a law on individual tails.

The proofs of BBMST marginal preservation and cylinder domination work
with this initial product block. The row distortion is performed only
on the newly exposed prime coordinate and preserves the complete old
marginal, including Omega_i. In particular, if u uses already exposed
nonternary primes, then for every Z subset Omega_i,

    P_l(Z intersect [c mod u])
      <=lambda(Z)*nu_l(u)/u,

    nu_l(u)=product_(p|u)(1-delta_p)^(-1).             (TB1)

Here the event on the left means Z times the cofactor cylinder, with all
remaining coordinates free. To check TB1 directly, begin with product
Haar on the unexposed coordinates. At each exposed prime dividing u,
the same conditional row-density bound used in BBMST Lemma3.4 costs at
most (1-delta_p)^(-1); expose coordinates not dividing u using marginal
preservation. The initial event Z contributes exactly lambda(Z).
This is the published proof applied to an initial product block, not a
claim that the paper separately states a theorem for this new model.

Consequently, if T_a,T_b are two actual ternary prefixes from original
heights a,b, then under the SAME current distorted law,

    P_l(T_a intersect T_b intersect [c mod u])
      <=w(a,b)*nu_l(u)/u,

    w(a,b)=3^(-max((a-1)_+,(b-1)_+)).                 (TB2)

Incompatible prefixes give zero. Compatible prefixes have the indicated
relative intersection mass, with heights zero and one both contributing
the complete initial block. For max(a,b)>=1 this is
3^(1-max(a,b)); the a=b=0 contribution is one. Thus TB2 does not replace
a distorted expectation by a Haar expectation.

### One finite prefix-pair constant pays every original height

Summing TB2 over the allowed height pairs gives exactly

    K_H=sum_(0<=a,b<=H) w(a,b)
       =4+sum_(h=1..H-1)(2h+3)/3^h
       =7-(H+2)*3^(1-H)<7.                          (TB3)

The four height pairs in {0,1} squared contribute four. For maximum
relative depth h>=1, there are (h+2)^2-(h+1)^2=2h+3 ordered height
pairs. In particular K_1=4. The constant remains finite independently
of H; it does not bound the actual multiplicity at any selected tail.

For a stage prime p, decompose an original nonternary cofactor as p^e u,
with e>=1 and u supported on earlier primes. The usual union bound for
the actual fibre fraction alpha_p is

    alpha_p <=sum_(actual (a,e,u))
                    p^(-e)*1_(T_a intersect actual u-phase).

Expand the square over ordered ORIGINAL labels. For each fixed
(a,e,u), numerical distinctness permits at most one label. Each compatible
pair uses TB2 for the same distorted old law and the actual intersection
modulo lcm(u,v). Summing a,b costs K_H. Extending the finite e,f sums
costs at most (p-1)^(-2). The remaining cofactor-pair Euler sum is the
existing BBMST/KKL sum. Hence

    M_p^(2)<=K_H*C_previous/(p-1)^2,

    C_previous=product_(earlier allowed primes s)
        [1+(3s-1)/((1-delta_s)*(s-1)^2)].            (TB4)

Absent-prime factors may be padded into C_previous as usual. No higher
digit, original phase, or projected numerical repetition was deleted.

### Reserve the actual pure-guard mass

Number all ordinary primes, including absent primes, and suppose every
prime in P_i exceeds p_k. Use the published continuation threshold g_k.
Define the scalar accounting mass and scalar ratio by

    eta_l=tau_i-sum_(k<t<=l)P_t(B_t),
    F_l=K_H*C_l/eta_l,
    eta_k=tau_i, F_k=K_H/tau_i.

The probability laws are unchanged. BBMST Lemma3.3 and TB4 give precisely
the loss estimate and scalar recurrence used in section88, now with
K_H in place of its leading constant four. Thus the published successful
continuation applies whenever

    K_H/(1-beta_i)<=g_k.                            (TB5)

It gives eta_n>0 at every finite final stage. The final law preserves
the initial ternary marginal, so P_n(G_i)=beta_i EXACTLY. It also
preserves each earlier bad-set marginal. Therefore

    P_n(G_i union union_t B_t)
      <=beta_i+sum_t P_t(B_t)<1.

This contradicts the actual whole-root cover supplied by section74.
Consequently TB5 is impossible when all primes of P_i exceed p_k.
This is a test on P_i=R union S_i, not on S_i alone.

### Two consequences at arbitrary ternary height

The source record for BBMST Table1 gives the downward-rounded bounds

    g_5>=9.032082,   g_6>=13.30344.

First assume H>=2 and let kappa be the nonzero root NOT owning original9.
Its guard mass satisfies beta_kappa<=theta_H-1/3<1/6. If P_kappa avoided
{5,7,11}, all its primes would exceed p_5=11, but

    K_H/(1-beta_kappa)<42/5=8.4<9.032082.

TB5 would contradict its whole-root coverage. Therefore

    P_kappa intersects {5,7,11}.                   (TB6)

Second, suppose one P_i avoids {5,7,11,13}. Then

    H>=5, and original9,27,81 all have root i.       (TB7)

Indeed, if H<=4, then K_H<=K_4=61/9 and beta_i<=theta_4=13/27,
so

    K_H/(1-beta_i)<=183/14<13.30344,

contradicting TB5 at k=6. Thus H>=5 and all three named pure labels
exist. If any one of9,27,81 were owned by the opposite root, then

    beta_i<=theta_H-1/27<25/54,
    K_H/(1-beta_i)<378/29<13.30344,

giving the same contradiction. Their first-root ownership is necessary;
no common deeper path or additional phase alignment is inferred.

These conclusions retain all other original heights and use the full
original source. They do not require a bound on the deep inventory.
They do not exclude R={5}, where each P_i already contains5, and do not
give unrestricted noncoverage. They are ordinary deductions from the
published distortion proof and thresholds; no new sieve table or Lean
verification is asserted.

## 92. One controlled distortion step excludes two no-seven columns at every five-height

Keep the actual source and notation of the full-height column budget: H_3=1, R={5}, arbitrary finite A=H_5, and a concentrated color i with7 absent from S_i. All other original heights remain arbitrary. The previously established column-budget consumer already shows that u_i<=2 could only occur when i owns original15 and

    U_i={11,13}.

That last case is impossible. Consequently every such no7 color satisfies u_i>=3 at every A, and the total original nonpure5-column count is at least5 by the existing other-color bound u_(3-i)>=2. This statement does not replace the stronger flat-height result when A=1.

### Choose the first distortion parameter and reuse the existing continuation

Construct one BBMST law for the actual5-free color-i cofactor base, with reserve3/10. This base has numerical multiplicity at most two, is coprime to210, and retains every original cofactor height. Its first four ordinary-prime stages are empty, so

    eta_4=7/10,  K_4=4,  F_4=40/7.

At prime11 choose delta_11=1/5. The existing SO2 recurrence has

    a_11=8/25, b_11=1/400,
    1-b_11*F_4/[delta_11(1-delta_11)]=51/56>0,
    1+a_11/(1-delta_11)=7/5,
    F_5<=T_(11,1/5)(40/7)=448/51<9<=g_5.

Use the published continuation from this checkpoint. Its input is the actual ratio K_5/eta_5; the accounting mass is NEVER reset to one:

    eta_t=7/10-sum_(s<=t)P_s(B_s).

The previously proved reserve argument gives P(E_i)>3/10 under the resulting SAME final probability P. This is one specified finite step followed by an existing successful continuation; no published threshold is recomputed.

### The same law gives a cheaper eleven-class price

BBMST Lemma3.4 and preservation of earlier marginals give, for every actual or potential cofactor phase,

    P(c mod11)<=1/[11(1-delta_11)]=5/44,
    P(c mod13)<=2/13.

The second bound uses the continuation's delta_13<=1/2. Later stages preserve the11 marginal, so no later distortion factor is paid on the first bound. These are prices in the law constructed above, not a combination with a different law giving the surviving mass.

For the two-column palette their total price is

    W=5/44+2/13=153/572<3/10,
    3/10-W=93/2860>0.

Reuse the established actual full-height source inequality

    (1-beta_i)P(E_i)<=C_i.

Finite A gives beta_i<1/2. Each finite column coefficient c_m, including its missing-top correction, is strictly below1/2. Therefore

    3/20 < (1-beta_i)P(E_i)
           <=C_i
           <(1/2)(5/44+2/13)
           <3/20,

a contradiction. Every p-prefix and cofactor phase remains the original one; their possible overlaps can only lower the upper capacity. No phase realization, additional Hall matching, or private-region reassignment is assumed.

This excludes the entire two-column no7 case at arbitrary five-height, and hence the previously minimal total u=4 inventory at all those heights. Larger original inventories remain open. It is an ordinary consumer of the established full-height source, BBMST cylinder bound and published continuation, with no new Lean verification.

## 93. Every root retains a small prime at arbitrary ternary height

Keep the full-height source and actual root pruning of the initial-block
argument. For a nonzero first-three root i, write

    P_i=R union S_i,
    Omega_i=the complete root i in Z/3^H,
    X_i=the complete retained nonternary carrier.

The retained ORIGINAL family covers Omega_i times X_i. Its pure-three
guards form the actual set G_i subset Omega_i. With normalized counting
measure lambda on Omega_i, retain

    beta_i=lambda(G_i),  tau_i=1-beta_i,
    beta_i<=theta_H=(1-3^(1-H))/2<1/2.

For H=1 the guard set is empty. All nonternary prime-power heights and
all original phases remain unchanged.

The new conclusion is

    P_i intersects {5,7,11,13}, for BOTH roots i,
    at every finite ternary height H>=1.                 (GM1)

The statement concerns P_i, not S_i. It does not assert that the two
intersections contain the same prime or that R meets this set.

### One actual conditioned initial block

Define a probability on the complete original ternary block ONCE,
before starting the distortion process:

    lambda_i(Z)=lambda(Z minus G_i)/tau_i.

Start the nonternary-prime distortion construction from

    P_0^G=lambda_i times Haar_X_i.

Thus the initial law is supported on the actual pure-guard complement.
No assertion of uniformity on Omega_i is made for lambda_i. The guards
have zero mass from the start, and every point in this initial support
still has to be covered by an original non-pure-three class.

Expose nonternary prime coordinates in increasing prime order, using
the original APs and the complete original ternary prefixes as before.
There is one law at every stage on the whole product. No later law is
conditioned, and no separately optimized laws are selected on ternary
tails.

The initial-block proof applies with lambda_i in place of the old
uniform lambda: its induction only needs the product between the
already read block and the unexposed prime coordinates. For every
Z subset Omega_i and every cofactor cylinder using exposed primes,

    P_l^G(Z intersect [c mod u])
      <=lambda_i(Z)*nu_l(u)/u,

    nu_l(u)=product_(p|u)(1-delta_p)^(-1).              (GM2)

This is the same conditional row-density argument and old-marginal
preservation as TB1. All subsequent moment and loss estimates refer to
this SAME distortion process. Its final ternary marginal is lambda_i,
so the pure-three guards remain null exactly.

### The four low-prefix pairs do not pay a conditioning factor

As before, original d=3^a m with m>1 contributes at most one numerical
label for each (a,m). At a=0 its ternary event is the whole block. At
a=1 an active original has root i and also contributes the whole block.
Classes at another first root are absent. Consequently the four ordered
height pairs in {0,1} squared have intersection probability exactly one
under lambda_i.

For any remaining height pair a,b, put h=max(a,b)-1>=1. Incompatible
ternary prefixes give zero. A compatible intersection is one complete
relative-depth-h cylinder, so

    lambda_i(T_a intersect T_b)
      =lambda((T_a intersect T_b) minus G_i)/tau_i
      <=3^(-h)/tau_i.

Combining this with GM2 bounds the ACTUAL distorted old-law intersection
by the same quantity times nu_l(u)/u. No Haar expectation is substituted
for a distorted expectation.

Reuse the already established finite pair count

    K_H=4+sum_(h=1..H-1)(2h+3)/3^h
       =7-(H+2)*3^(1-H).

The conditioned process therefore has leading moment constant

    L_i=4+(K_H-4)/tau_i<10.                          (GM3)

Indeed K_H<7 and tau_i>1/2. The old unconditioned guard-reserve cost
was K_H/tau_i; GM3 lowers this by exactly4*beta_i/tau_i. This reduction
comes from retaining the exact unit probability of the four low-prefix
pairs. There is no additional reserve for G_i, whose mass is already
zero under the initial law.

The sharper finite bound from beta_i<=theta_H is

    L_i<=10-2*(H+5)*3^(1-H)/(1+3^(1-H))<10.

The displayed expression also gives L_i=4 at H=1. No bound on the
number of high originals or on any nonternary exponent is imposed.

### Reuse the same published continuation

Expanding the actual nonternary fibre fraction over ordered original
labels, applying GM2, and summing the ternary height pairs as above
gives exactly the previous cofactor Euler estimate with L_i replacing
K_H:

    M_p^(2)<=L_i*C_previous/(p-1)^2.

The factors C_previous, numerical-label injection, prime-power sums,
and checkpoint continuation are unchanged from TB4. Only the declared
initial block law and the prefix-pair constant changed.

Suppose P_i avoids {5,7,11,13}. Every nonternary prime in this actual
retained family then exceeds p_6=13. Initially the accounting mass is
ONE, the cofactor Euler product is one, and the scalar continuation
state is f_6=L_i<10. The published lower bound

    g_6>=13.30344>10

therefore gives positive final uncovered probability for all the
non-pure-three originals in this same process. Pure-three originals
have zero mass because the final law preserves lambda_i. This
contradicts whole coverage of the original retained root and proves
GM1.

GM1 removes the earlier large-H alternative for a root avoiding these
four primes. Such a root cannot occur, including the previous case
where9,27,81 were all assigned to it. The earlier non9-root consequence
requiring a prime in {5,7,11} remains valid.

These are ordinary deductions using the published distortion proof
with one initial product block. The paper is not claimed to state this
model extension as a separate theorem. No new continuation table or
Lean verification is asserted. Arbitrary-height common support between
the two roots, and unrestricted Erdos7, remain unresolved.

## 94. A finite exact obstruction to the uniform prefix-supremum envelope

Keep the actual single-root initial-block construction of section93.
One possible refinement replaces conditioned Haar measure by an arbitrary
probability lambda supported on the complete pure-guard complement, and
then bounds every compatible pair of original ternary prefixes by the
largest lambda mass of a cylinder at its intersection depth. This refinement
has an exact finite limitation, even when lambda is allowed to vanish on
any of the surviving leaves.

Fix ternary height H=4. Inside one nonzero first-three root, represent the
remaining three ternary digits as words over {0,1,2}. Take the actual local
pure-three guard prefixes to be

    1, 01, 001.                                      (PE1)

They have relative depths1,2,3 and represent the original pure labels
9,27,81, respectively. They are pairwise disjoint, as required by
comparable-class disjointness. Their complement contains14 of the27
complete relative-depth-three words:

    {2ab : a,b in {0,1,2}}
      union {02b : b in {0,1,2}}
      union {000,002}.

This is a locally admissible guard configuration. Its occurrence in an
entire EB1 covering family is not asserted or required for the finite
optimization below.

Let lambda be ANY probability supported on this complement. Full support
on all14 leaves is not an assumption. For h=1,2,3 define

    M_h(lambda)=max_(word w of length h) lambda([w]).

The depth-zero bound is exactly one. The same ordered-height-pair count
used in section93 therefore gives the prefix-supremum envelope

    E(lambda)=4+5*M_1(lambda)+7*M_2(lambda)+9*M_3(lambda).

Its exact optimum is

    min_lambda E(lambda)=93/10.                     (PE2)

### Exact lower bound for every probability

Write

    x=lambda([2]),  y=lambda([02]),  z=lambda([00]).

These are nonnegative and x+y+z=1. Five immediate prefix constraints are

    x<=M_1,
    x<=3*M_2,
    y<=M_2,
    z<=M_2,
    z<=2*M_3.

The second constraint splits [2] into its three depth-two children. The
last uses the exclusion of001, so [00] has only000 and002 in the allowed
support. Multiply these five inequalities, in order, by50,3,53,8,45 and
add. This gives

    53=53*(x+y+z)<=50*M_1+70*M_2+90*M_3,

and hence

    E(lambda)>=4+53/10=93/10.

The argument uses no positivity assumption on individual surviving leaves
and no numerical optimization.

### A probability attaining the bound

Assign mass1/15 to each of the nine words2ab and each of the three
words02b. Assign mass1/10 to each of000 and002. The total mass is

    12/15+2/10=1,

and the three maximal prefix masses are

    (M_1,M_2,M_3)=(3/5,1/5,1/10).

They give E=93/10, proving attainment in PE2. Conditioned Haar measure on
the same guard complement instead gives

    (M_1,M_2,M_3)=(9/14,3/14,1/14),
    E=131/14=93/10+2/35.

Thus choosing a different initial law strictly improves this particular
envelope, but its exact optimum remains9.3.

### Scope of the obstruction

The currently reused BBMST Table1 certificate is

    g_5>=9.032082,

and93/10 exceeds that certified lower threshold by0.267918. Consequently,
a method that uses only local pure-guard legality, chooses any initial
lambda, and then replaces each prefix intersection by the separate
depth-wise supremum cannot uniformly supply an initial scalar at most
9.032082 for every such guard configuration. PE1 already obstructs that
specific sufficient route to the five-prime checkpoint.

PE2 is the optimum of the stated envelope, not a lower bound for the
actual original-family second moment. Actual prefixes, cofactor phases,
shared numerical-label ownership and private-point relations may prevent
the separate maxima from being realized jointly. A restriction supplied
by a whole covering family may also exclude PE1; no such restriction is
proved here. The local guard configuration is not a covering counterexample.

Nor does PE2 give an upper bound on the true continuation threshold g_5.
The published number9.032082 is a lower bound for g_5, so PE2 does not
exclude a stronger continuation certificate reaching9.3. The conclusion
only identifies the exact limitation of this prefix-supremum envelope
when paired with the currently cited numerical certificate. No Lean
verification or new continuation table is asserted.

## 95. The standard sieve at three forces global five-or-seven support

Directly reuse the published BBMST distortion sieve for a finite family
of APs with distinct odd moduli greater than one. If this family covers
the integers, its period Q must satisfy

    5 divides Q or7 divides Q.                       (GS1)

All original prime-power heights and phases are unrestricted. This is
a direct application of the published tools, not a new initial-block
theorem or an assertion about shared support between two roots.

Suppose instead that5 and7 do not divide Q. If3 does not divide Q,
BBMST Theorem7.1 already gives noncoverage. Otherwise number all ordinary
primes as in its section6, so p_2=3 and p_4=7, and choose

    delta_2=1/2,  delta_1=delta_3=delta_4=0.

At the3 stage, the only new originals have pure-three moduli. Numerical
distinctness alone gives, for H=v_3(Q),

    alpha_2<=sum_(a=1..H)3^(-a)<1/2=delta_2.

The positive-part loss formula in the proof of BBMST Lemma3.3 therefore
gives P_2(B_2)=0. The2,5,7 bad sets are empty, so the original accounting
masses satisfy mu_2=mu_3=mu_4=1. No auxiliary reserve or reset is used.

BBMST Lemma3.4 has the ordinary cylinder factor nu(3)=2. Its resulting
Euler estimate in Theorem3.2, equivalently section6 equation(21), permits
the checkpoint i_0=4 with

    kappa=1+(3*3-1)/[(1-1/2)*(3-1)^2]=5.

Only3 occurs in that initial Euler product; absent primes contribute
no factor. Thus section6 equation(19) gives f_4=kappa/mu_4=5. The published
Table1 bound g_4>=5.860938 and Corollary6.3 imply noncoverage, proving GS1.
The referenced source is arXiv:1811.03547v1, Lemmas3.3--3.4, Theorem3.2,
section6 equations(19)--(21), Table1 and Corollary6.3.

For the actual EB1 source partition used here, GS1 says precisely

    (R union S_1 union S_2) intersects {5,7}.          (GS2)

It does not assert that R intersects this set, that each P_i=R union S_i
does, or that the two pruned roots share a prime. Shared support still
requires a relation using the actual common source. No Lean verification
is asserted.

## 96. Different concentrated colors force ternary height at least twelve

Keep the one EB1 original cover in the all-concentrated branch R=empty.
Write H=H_3 and retain the disjoint nonempty color supports S_1,S_2.
Every original prime-power height and every actual phase remains
unrestricted. The combined necessary condition is

    R=empty ==> H_3>=12.                            (CG1)

### Reuse the existing complete-tree collision reservation

For opposite-color support primes p<q, use the single-source construction
proved in BC12 with retained smaller coordinate p, selected chain {q},
and no repeated bases. Apply this construction to the original family
itself; the strict class saving here comes from its reserved originals.
CP1 gives no original divisible by pq, so every mixed-root blacklist is
empty. The only possible cross-group numerical collision is between

    3^c*q^a and3^c*p^a, with0<=c<=H and a>=1.

Indeed a common nonternary cofactor would have to belong to both colors.
Reserve the actual complete q-prefix of the first original in every
such pair, exactly as in BC12. With r=q-p+1, the antichain reservation
cost of BC14 satisfies

    Delta <= (H+1)*sum_(a=1..min(H_p,H_q))r^(-a)
          < (H+1)/(q-p).

Thus q-p>=H+1 gives Delta<1. BC14 supplies at least p good q-roots,
and the empty blacklists permit the BC12 matching and full-depth tree.
Its source-map construction gives a whole distinct odd cover with no
increase in classes. Original p,q,3p,3q are all present: divisor closure
supplies the primes, and DP9 supplies the concentrated primes' mixed
children. The reserved q and3q classes have empty pullbacks, so at
least these two originals disappear. This contradicts EB1. Consequently

    |p-q|<=H for every p in S_1 and q in S_2.        (CG2)

Only the established tree construction and capacity bound are reused;
no fresh-coordinate independence or bounded-height substitution is made.

### The two colors cannot fit when H is at most eleven

The existing height-one exclusion permits H>=2. Reuse CM3 and its
two-prime-support consequence: each S_i has at least two primes, and
if it has exactly two, it is one of

    {5,7}, {5,11}, {5,13}.

Since the supports are disjoint, they cannot both have exactly two.
Suppose H<=11. All support primes exceed3 and are odd, so CG2 sharpens
to an opposite-color gap at most10.

If one color is {5,t}, the other has at least three primes. Their
distance from5 puts every one in {7,11,13}; exclusion of the same-color
prime t leaves at most two choices, a contradiction.

It remains to consider two colors each having at least three primes.
Let r be the smallest prime in their union and name its color S_1.
Every prime of S_2 lies in (r,r+10]. Because r>3, there are two cases.

If r=2 modulo3, the only possible offsets of S_2 from r are2,6,8:
the other positive even offsets at most10 yield multiples of3.
All three offsets must occur. Hence min(S_2)=r+2, and the opposite-color
gap puts S_1 below or equal to r+12. The only even offsets from r in
that range which avoid multiples of3 are0,2,6,8,12. Removing the three
offsets already in S_2 leaves only0 and12 for S_1, a contradiction.

If r=1 modulo3, the only possible offsets of S_2 are4,6,10, so all
three occur and min(S_2)=r+4. Now S_1 is at most r+14. Its possible
even offsets avoiding multiples of3 are0,4,6,10,12. Removing S_2 again
leaves only0 and12, the same contradiction. Composite candidates among
these lists only decrease the number of available primes.

This excludes every H<=11 and proves CG1. The argument uses the same
original source throughout and imposes no restriction on nonternary
heights, total prime support, or phases. It does not exclude the
remaining all-concentrated configurations with H_3>=12 or settle the
branches with nonconcentrated support. Unrestricted Erdos7 remains
unresolved. No new Lean verification is asserted.

## 97. Opposite-color gaps force actual mixed prime labels

Keep the one EB1 original family with R=empty, original numerical
palette D, and disjoint nonempty concentrated supports S_1,S_2.
For every nonternary support prime p and 1<=a<=H_p define the actual
mixed-height profile

    h_p(a)=max{c>=0:3^c*p^a is in D},
    t_p=h_p(1).

The set is nonempty because the pure p-powers are original. Divisor
closure makes its c-values an initial segment and gives h_p(a)<=t_p.
All these profiles refer to the same original family.

The new original-label requirement is

    p,q in opposite colors, g=|p-q|
      ==> t_p>=g and t_q>=g
      ==> 3^g*p and 3^g*q are ORIGINAL labels.        (MHG1)

This does not create labels by transport or require bounded nonternary
heights. In particular, because opposite odd primes differ by at least
two and both colors are nonempty,

    9p is original for EVERY nonternary prime p.     (MHG2)

### Use the existing collision-reservation construction

Fix opposite-color p<q and put r=q-p+1. Reuse exactly section96's
BC12--BC14 single-source construction, preserving the original p
coordinate and compressing the entire q coordinate into it. There
are no pq-bearing originals. Its only numerical collision pairs are

    3^c*q^a and 3^c*p^a.

At each a<=min(H_p,H_q), the number of actual pairs is precisely
1+min(h_p(a),h_q(a)). Reserve their actual complete q-prefixes as
before, deduplicating them and removing descendants of retained
ancestors. If Delta_pq is the resulting BC14 antichain cost, then

    Delta_pq
      <=sum_(a=1..min(H_p,H_q))
            [1+min(h_p(a),h_q(a))]/r^a.             (MHG3)

The established source construction gives a smaller whole distinct
odd cover whenever Delta_pq<1: the mixed blacklists are empty, and
the actual reserved q and 3q originals disappear. Hence the same
original family must satisfy the coupled profile restriction

    1<=Delta_pq
      <=sum_(a=1..min(H_p,H_q))
            [1+min(h_p(a),h_q(a))]/r^a              (MHG4)

for EVERY opposite-color pair p<q. These are conditions on one set
of original labels and phases. They must not be added as disjoint
inventory charges: one original may occur in several pair tests.

Let t=min(t_p,t_q). The finite sum in MHG3 is strictly less than

    (t+1)*sum_(a>=1)r^(-a)=(t+1)/(q-p).

If t<=q-p-1 this is at most one, contradicting MHG4. Therefore
t>=q-p, which proves MHG1 by divisor closure. No tree theorem or
prime-set enumeration is repeated.

### The former flat-color HSW branch is excluded

CP10's flat-color premise says that one color has no original
3^c*m with c>=2 and m>1 supported there. Choosing any prime p in
that color contradicts its actual original 9p from MHG2. Thus neither
color of a remaining R=empty family is flat.

The conditional HSW comparisons CP11--CP12 and SC4 retain their stated
validity, but their flat-color premise cannot occur in this branch.
Likewise CP13's specified constructor, which switches entire seeds
at successive exits, has no distinct output in the remaining branch.
This is the existing constructor's proved limitation, not a claim
that other HSW variants or other source maps fail.

### An attained terminal gap prevents singular elimination

Suppose some opposite-color pair has |p-q|=H_3=H. MHG1 supplies
original 3^H*p and 3^H*q in different first-three roots. At a private
point of either original, retain every other coordinate and the first
H-1 ternary digits, and vary only the highest ternary digit. The
existing private-sibling argument says that none of the three points
is covered by any lower-height original. Every one therefore requires
a highest-height original in that same first-three root.

Applying this argument in the two distinct roots gives at least two
highest-height originals at EACH of the three highest-digit values.
Consequently the global terminal occurrence counts are all at least
two, the highest-three batch has at least six classes, and the
terminal digit is not singular. In particular it cannot have the
singular-elimination pattern(1,1,t).

At H=12 this obstruction is automatic. Section96's color-support
argument already excludes opposite-color gaps all at most10; since
the gaps are even, their maximum is at least12. CG2 bounds that same
maximum by H=12, so an opposite-color gap12 is attained. Thus every
remaining H_3=12, R=empty family has at least six top-three classes
and a nonsingular terminal digit. The singular reduction does not
automatically handle this lowest remaining height.

This does not exclude the H_3=12 branch. At larger H the largest
opposite-color gap may be below H, and MHG2 alone puts9p at height
two rather than at the global terminal height. No general terminal
singularity or nonsingularity is asserted in that case.

MHG1--MHG4 strengthen the original inventory conditions. They do not
force a contradiction for arbitrary nonflat profiles, or settle
R!=empty or unrestricted Erdos7. They are ordinary deductions from
the already established source-map construction; no Lean verification
or literature-priority claim is asserted.

## 98. Terminal singularity forces a prime singleton and one occupied ancestor

Reuse [Report343, section4](../../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md#4-奇异-dp-保真到哪一层)
(Kullmann, arXiv:1103.3693v1, Lemma1.6.1), section79
(joint singleton-branch coarsening and occupied-ancestor liability),
and section86 (numerical collision accounting).
The additional arithmetic bridge is the prime singleton classification
at arbitrary GLOBAL terminal ternary height. No Lean claim is made.

Let C be one EB1 original whole cover with N distinct odd labels, full
period Q=3^H M, H>=2, and gcd(M,3)=1. Let T contain ALL original labels
of ternary height H. Assume the global last-digit occurrence counts are

    (1,1,t), t>=1.                                  (TS)

This counts every original involving X_(3,H). Selecting one covering
supplier at each sibling of a private point does not establish TS.

### Prime singleton: the new arithmetic part

Original private points make the full clause family minimally
unsatisfiable. Report343 section4 therefore gives nondegenerate singular
elimination and a minimally unsatisfiable output. Exactly t parent
tuples exist and all t yield distinct compatible resolvents.

Each parent specifies its complete lower ternary prefix. Compatibility
of every tuple forces ONE common u mod3^(H-1) for all top parents.
Divisor closure supplies original G=A_(3^H). No other top parent can
share its final digit: it would lie inside G. Hence G occupies a
singleton branch. Write the other singleton initially as A_(3^H c),
with c>1 and gcd(c,3)=1.

If c is composite, choose a prime p|c with p<c. The original 3^H p
exists by divisor closure and must lie in the remaining branch.
Compatibility with the c-parent makes its p-phase agree. Its resolvent
is therefore the entire projection of the c-parent after erasing the
last ternary digit. Every other resolvent is contained in that AP.
Minimality of the eliminated cover forces t=1. The top cofactor palette
is now exactly{1,p,c}; divisor closure implies c=p^2. Exchange the
two nonpure singleton roles and take p as the singleton cofactor.
If c was prime already, take p=c directly. Consequently the top batch is

    A_(3^H), A_(3^H p), {A_(3^H m):m in Mtop},
    |Mtop|=t, 1,p notin Mtop,

with the first two parents singleton and all remaining parents in the
third final-digit branch. The symbol Mtop is a set of actual cofactors,
not the full nonternary period M.

### Coarsen the entire top batch on its exact joint obligation

Put n0=3^(H-1)p. Let b modp be the actual singleton parent's p-phase.
Let C0 be the single AP with prefix u mod3^(H-1) and p-phase b.
Retain every original of ternary height less than H, unchanged.

Their exact complement in the full digit carrier is U times{0,1,2},
with U nonempty because original top parents have private points.
At the final digit of A_(3^H p), its singleton status and whole
coverage imply U subset C0. Thus the retained originals plus C0 form
a WHOLE cover. This covers the simultaneous deletion region, not just
a union of individually selected private witnesses.

The output has exactly N-(t+2)+1=N-t-1 classes. Original A_(n0)
is retained by divisor closure. It is disjoint from C0: an intersection
would lift at the singleton's final digit to an intersection with
A_(3^H p), contrary to comparable-class disjointness. Thus precisely
one numerical modulus, n0, occurs twice, in two distinct phases.
Both phases have actual liabilities: an old private point of A_(n0)
survives outside C0, and every point of U requires C0.

The output period is exactly Q/3. Original pure3^(H-1) remains, as
does each original nonternary pure prime power at its maximum height.
Neither divisor closure of the output nor privacy of all its other
retained members is asserted. The coarsening is not exact DP elimination.

### Exact DP has a different, localized multiplicity profile

Each m in Mtop instead produces an actual compatible resolvent R_m,
with numerical modulus 3^(H-1)lcm(p,m). For each 3-free k, its multiplicity is

    s(3^(H-1)k)=1_[3^(H-1)k original]
                + #{m in Mtop:lcm(p,m)=k}.

If v_p(k)>=2, only m=k is possible. If k=pv with p notdividing v,
only m=v or m=pv is possible. Multiplicity is therefore at most three,
and is exactly three precisely when v,pv both belong to Mtop; their
retained lower ancestor is then forced by divisor closure. All three
phases differ by nondegeneracy of the eliminated minimal cover.

Equivalently, a triple occurs somewhere iff some original top label
contains p and a different nonternary prime. For the nontrivial forward
direction v>1 because1,p are excluded; for the reverse direction use
divisor closure to obtain top labels3^H v and3^H pv with p notdividing v.
High pure p-powers alone do not produce triples. Exact DP has N-2
classes and remains irredundant, unlike the possibly redundant coarsening.

### The occupied ancestor has an exact remaining repair budget

Delete the original top batch AND its old ancestor A_(n0). The retained
family B has N-t-3 classes. Its actual complement E* satisfies

    E* subset A_(n0) union C0, A_(n0) intersect C0=empty.

A repair by at most t+2 odd nonunit APs with distinct numerical moduli
absent from B would give at most N-1 classes, contradicting EB1.
The t+3 deleted original classes supply only the old budget, not this
strict saving. Reassigning the occupied ancestor loses its old private
point and is not a repair. No repair of size t+2 is supplied here.

Under R=empty, the shared prefix u places every top mixed parent and
both ancestor phases in one actual nonzero ternary root. The opposite
color is untouched. Neither terminal singularity nor its affordable
repair follows from the all-concentrated hypothesis. Counts |T|<=4
would imply TS, because every terminal value must occur; no bound
|T|<=4 for the remaining EB1 sources has been proved.

Section97 excludes TS in the remaining R=empty, H=12 branch: each
terminal digit occurs at least twice there. At larger H, neither TS
nor an affordable occupied-ancestor repair is established. These
conditional reductions do not settle unrestricted Erdos7.

## 99. Fiberwise collision avoidance need not admit a common single-AP source

This is a finite source-shape obstruction to replacing the uniform
q-prefix reservation in sections96--97 by its ternary-weighted cost.
It is NOT an extremal whole-cover example or a counterexample to E7.
It permits the output APs to acquire extra ternary powers; even that
freedom does not suffice in this control.

### Existing interfaces

Report375 LA2--LA3 permits a tree to depend on a retained coordinate
only because every retained transported label fixes that FULL coordinate.
section38 (BC17--BC19) merges equal COMPLETE output phases,
not different phases of the same numerical modulus. For opposite colors,
the two original 3^c p^a and 3^c q^a phases have different first-three
roots when c>=1; preserving that coordinate prevents their merger.
PH5 concerns the complete PRIVATE region, not the entire original AP.
Dropping parts of several classes instead requires PH1 and RS1--RS3.

### A literal conditional reservation

Take p=7, q=11 and the retained ternary coordinate t in Z/81. The
q-tree has depth one. Reserve q-root0 at every t, and additionally

    root1 when t=2 mod3,
    root2 when t=2 mod9,
    root3 when t=5 mod27,
    root4 when t=8 mod81.

The last three ternary cylinders are disjoint, since their second
ternary digits are respectively0,1,2. Thus at every t at most three
q-roots are forbidden: root0, possibly root1, and at most one more.
There are at least eight available q-roots, so every t separately
admits a complete seven-ary tree avoiding its actual reservations.

These are precisely the collision shapes q vs p and3^c q vs3^c p,
1<=c<=4. On the q-side assign the four displayed ternary prefixes
and q-root c. On the p-side give each counterpart first-three root1
and any full extension, with p-root c. Comparable members on either
side are disjoint because their prime roots differ. There is no pq-label.
Only this partial inventory is specified; whole coverage, private-color
concentration, divisor closure and EB1 are not inferred from it.

With r=q-p+1=5, the proposed joint prefix cost is

    (1+1/3+1/9+1/27+1/81)/5 = 121/405 < 1.

Nevertheless no conditional source of the following permitted form
can keep all the specified original tests as single APs.

### Expose the q-roots through distinct three-free original labels

Choose ten distinct primes ell_j outside {3,7,11}. Include the ten
literal three-free classes d_j=11*ell_j, 1<=j<=10, whose conditions
are q-root j and ell_j-root1. Keep all these cofactor coordinates
and the ternary coordinate unchanged. For each t choose an injection

    theta_t: Z/7 -> Z/11

avoiding the reservations above. The one common source is

    y_3=t, y_p=x, y_q=theta_t(x), y_other=z_other.

The pullback of d_j is its unchanged ell_j condition times

    E_j={(t,x):theta_t(x)=j} subset (Z/81)x(Z/7).

If this pullback is empty or ONE entire AP, E_j must be empty or
one ternary prefix cylinder times one p-root. Indeed its period
divides 81*7, and injectivity gives at most one p-root over each t.
Its extra ternary height may be any integer from0 through4.

The E_j partition all 81*7 output points: q-root0 is always excluded.
Thus they form at most ten labeled prefix rectangles partitioning
seven complete ternary columns. Each label j occurs in at most one
rectangle and hence in only one p-column.

Only q-roots5,...,10 are never forbidden. There are six of these,
so at least one of the seven p-columns uses none of them. This column
must be partitioned using roots1,...,4. Each of those four is forbidden
at some point of the first-three root2. No rectangle in that column
can therefore contain all of that root. A complete ternary prefix
partition with the root2 branch subdivided has at least FIVE leaves:
at least one in each other first root and at least three under root2.
The other six p-columns each require at least one rectangle. Hence
the source would need at least 5+6=11 rectangles, exceeding the ten
available nonzero q-root labels. This is impossible.

The obstruction persists on every higher ternary carrier by lifting
these cylinders; deeper subdivision cannot reduce the prefix-leaf
count. It already fails before numerical collisions among the output
APs are checked. Therefore separate fiberwise trees and joint cost
below one do not imply a legal single-AP transport, even with arbitrary
extra ternary powers. A successful whole-cover argument must use more
than these premises: it must prove actual unobserved prefix freedom,
or pay for discarded/split tests through one common RS1--RS3 replacement.

No enumeration, Lean verification or assertion of a whole-cover
realization is used in this finite argument.

## 100. A vacant cross-color palette repairs large terminal-singular batches

Keep one EB1 original distinct odd cover with R=empty and ternary height
H. Assume the GLOBAL highest-three-digit occurrence counts are(1,1,t),
with t>=1. This is the terminal-singularity hypothesis, not a consequence
of choosing a few private-point suppliers. Write k=t+2 for the number
of original highest-three-height classes.

Reuse section98's terminal-singularity interface: the batch consists of

    A_(3^H), A_(3^H*p), {A_(3^H*m):m in Mtop},
    |Mtop|=t, p>3 prime, 1,p notin Mtop,

all at one actual lower ternary prefix u modulo3^(H-1). If b is the
actual p-phase of A_(3^H*p), the exact joint deletion obligation after
removing this ENTIRE batch lies in the single AP

    C={x:x=u mod3^(H-1), x=b modp}.                  (TR1)

Every top nonternary cofactor belongs to the same color as p. Let q be
the smallest prime in the opposite color. GM1 gives

    q in {5,7,11,13}.

The new necessary restriction is

    terminal singularity and R=empty
      ==> 3<=k<=q-2.                               (TR2)

In particular, if the opposite color contains5, then k=3. With opposite
minimum7,11,13, the respective upper bounds are5,9,11. This constrains
terminal-singular families only; it neither establishes singularity nor
rules out the remaining small batches.

### Repair the whole coarsened cylinder while retaining its old ancestor

The prime classes are normalized as before, so original A_q is0 modq.
For each a=0,...,q-2 define one new AP by the compatible CRT conditions

    B_a={x:x=u mod3^a, x=b modp, x=a+1 modq},
    modulus(B_a)=3^a*p*q.                           (TR3)

At a=0 the ternary condition is empty. CG1 gives H>=12, and q<=13,
so a<=q-2<=H-1. Every point of C has its prescribed prefix modulo3^a.
Its q-root is either zero, when the retained A_q covers it, or the
unique value a+1 in{1,...,q-1}, when B_a covers it. Thus

    C subset A_q union UNION_(a=0..q-2) B_a.         (TR4)

The q-1 new numerical labels are pairwise distinct. CP1 makes every
one absent from the entire original palette, since it contains the
opposite-color primes p and q. Every other original is retained;
in particular the occupied ancestor A_(3^(H-1)*p) is unchanged.
The new labels divide the original complete period. No new coordinate,
height restriction, or independently chosen original phase is used.

TR1 and TR4 therefore give a WHOLE distinct odd cover with

    N_new=N-k+(q-1),
    W_added=p*q*(3^(q-1)-1)/2.                      (TR5)

If k>=q this strictly lowers class count, contradicting EB1. The
construction covers the full C, so it automatically covers the actual
joint obligation, including its portions with multiple old owners.

### The equal-count case also lowers the modulus sum

Suppose k=q-1, equivalently t=q-3. The actual deleted modulus sum is

    W_deleted=3^H*(1+p+sum_(m in Mtop)m).             (TR6)

For q=5, H>=12 gives

    W_added < (5/[2*3^(H-4)])*3^H*p < 3^H*p
            < W_deleted.

For q>=7, the t=q-3 distinct odd nonunit cofactors in Mtop are all
at least5. In increasing order their sum is at least

    5+7+...+(2t+3)=t*(t+4).

Excluding p from that list can only increase this lower bound. Put

    C_q=q^2-2*q-2.

Then 1+p+sum_m m >= p+C_q. The opposite-color gap bound CG2 gives
p<=H+q. For H>=q-1 define

    F(H)=3^(H-q+1)*(1+C_q/(H+q)).

This function is strictly increasing on integer H: its successive
ratio is greater than 3*(H+q)/(H+q+1)>1. At the first possible value,

    F(q-1)-q/2=(q-6)/(2*(2*q-1))>0.

Since H>=12 and q<=13 imply H>=q-1, it follows that

    W_deleted/(3^(q-1)*p)
      >=3^(H-q+1)*(1+C_q/p)
      >=F(H)>q/2
      >W_added/(3^(q-1)*p).

Thus every equal-count case strictly lowers the second EB1 objective.
This excludes k=q-1 and proves TR2 without assuming a bound on any
nonternary height.

This repair is a direct CRT allocation using an entirely vacant
cross-color palette. The earlier repair forests remain applicable in
their own domains; no fresh-prime-height assumption is borrowed here.
The occupied ancestor needs no movement because its old private
liability remains covered by that same retained original class.

The remaining difficulty is the genuinely small terminal-singular
batch, or a nonsingular terminal digit. TR2 does not provide an
affordable repair for those cases or settle arbitrary-height R=empty,
shared support, or unrestricted Erdos7. No Lean verification or
literature-priority claim is asserted.
