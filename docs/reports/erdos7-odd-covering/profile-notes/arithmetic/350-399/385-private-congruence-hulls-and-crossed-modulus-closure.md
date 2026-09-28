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
