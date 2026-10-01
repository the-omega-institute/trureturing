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
