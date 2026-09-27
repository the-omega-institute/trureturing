# Near-maximal mixed packing need not improve the anchor query hinge

The nested pure-5 geometry of
[report537](537-two-copy-lower-witnesses-require-nested-pure-five-prefixes.md)
and mixed raw mass approaching1/12 do not force any positive saving in
the maximal raw old-query hinge at the first11 stage. A single globally fixed complete query layout
attains every numerical-label cylinder maximum under the actual initial
survivor law, attains the pure-source PA2 comparison envelope, and has
zero hinge throughout the mixed deleted region for every threshold t>=1.

This is an ordinary mathematical counterexample to that specific
anchor-hinge/deletion-overlap estimate. It does not establish sharpness
of the actual CP5 stage loss, rule out later-prime compensation, construct
an all-laws lower witness, or settle Erdős#7. No Lean verification is
claimed.

## 1. One actual family and its actual CP anchor law

Use product Haar H on the 5-adic and 7-adic coordinates. Every family
below has finitely many original classes; equivalently all its original
events live on one finite CRT carrier, with independent Haar tails for
queries beyond the original heights.

Fix H5>=3, H7>=2 and positive finite A,B. At each pure p-depth
1<=e<=Hp, for p=5,7, take the two classes

    p^(e-1) mod p^e,   2*p^(e-1) mod p^e.

Their prefixes, with least significant digits first, are 0^(e-1)1 and
0^(e-1)2. All pure forbidden cylinders within one coordinate are disjoint.
The complete pure survivors S5,S7 have masses

    w5=(1+5^(-H5))/2,   w7=(2+7^(-H7))/3.             (AH1)

Both25 classes lie in root0 mod5; both125 classes lie in the live cell
0 mod25 within that root. Roots3 and4 have no pure-5 deletion. Thus this
is precisely the remaining nested geometry of report537.

For each mixed numerical label 5^a*7^b, 1<=a<=A and 1<=b<=B, take the
two CRT classes

    (3*5^(a-1) mod5^a, 3*7^(b-1) mod7^b),
    (3*5^(a-1) mod5^a, 4*7^(b-1) mod7^b).             (AH2)

The two-copy allocation is transposed relative to report537 NP6: here
the two distinct terminal digits are on7, leaving root4 mod5 untouched
by both the pure and mixed originals. All numerical labels are odd and
nonunit, every listed label occurs exactly twice, and all phases are
fixed independently of the observer point or any query.

Two distinct first-nonzero-digit prefixes on one coordinate are disjoint.
Consequently the mixed rectangles in(AH2) are pairwise disjoint and
avoid every pure original, regardless of the relative sizes of A,H5
and B,H7. Their union D is the product D5 times D7, where D5 records a
first nonzero5 digit3 by depthA and D7 a first nonzero7 digit3 or4 by
depthB. Hence

    u=H(D)=(1/12)*(1-5^(-A))*(1-7^(-B)) ->1/12.       (AH3)

Keep exactly the raw source and actual anchor used in
[report348 CP/PA](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md):

    mu=H restricted to(S5 times S7),
    lambda0=H restricted to((S5 times S7) minus D),
    Z=lambda0(1)=w5*w7-u>0,
    nu57=lambda0/Z.                                   (AH4)

There is no replacement with a query-dependent or independently
optimized source law. Letting all four finite heights increase gives
Z->1/4 and pure deficits tending to zero.

## 2. A single query layout simultaneously maximizes every label

For every positive 5-query exponent a choose residue4 mod5^a, and for
every positive 7-query exponent b choose residue5 mod7^b. For an absent
coordinate take its whole space. Write these complete CRT queries Q_ab,
including Q_00=the whole space.

Every positive5 query lies within root4 and every positive7 query within
root5. These roots avoid all relevant pure originals. Every mixed point
has5 root0 or3 and7 root0,3 or4. Therefore

    Q_ab intersect D is empty whenever a+b>0.          (AH5)

This is one phase choice for the entire countable query inventory.
It simultaneously attains the maxima for the actual normalized law:

    q_(5^a)(nu57)=w7/(Z*5^a),                    a>=1,
    q_(7^b)(nu57)=w5/(Z*7^b),                    b>=1,
    q_(5^a*7^b)(nu57)=1/(Z*5^a*7^b),             a,b>=1. (AH6)

To prove maximality, use lambda0<=mu. Under mu, any positive5 cylinder
has mass at most w7/5^a, any positive7 cylinder at most w5/7^b, and any
mixed cylinder at most 1/(5^a*7^b). The selected queries have exactly
these masses under mu and, by(AH5), lose none under lambda0. Division
by the same positive Z proves(AH6). No enumeration over query phases
and no change of law is needed.

Summing(AH6), with one query per numerical label rather than two, gives
the exact same-law complete anchor norm

    R_{5,7}(nu57)
      =(w7/4+w5/6+1/24)/(w5*w7-u) ->7/6.            (AH7)

The raw numerator is unchanged by deleting D. Since u>0, normalizing
the actual survivor strictly increases this norm compared with the
normalized pure-product law, whose norm has denominator w5*w7 and
limit7/8. These facts concern this actual anchor law; they are not an
all-laws lower bound.

## 3. Exact attainment of the pure-source hinge envelope

For finite query depths m,n>=1 define

    N5_m=1+sum_(a=1..m) 1_[4 mod5^a],
    N7_n=1+sum_(b=1..n) 1_[5 mod7^b],
    L_mn=N5_m*N7_n=sum_(a=0..m,b=0..n) 1_Q_ab.

The positive query cylinders are nested in each coordinate. Under the
raw pure-p survivor restriction, the count Np_h has masses

    pi_p,h(1)=w_p-1/p,
    pi_p,h(k)=(p-1)/p^k,      2<=k<=h,
    pi_p,h(h+1)=p^(-h).                              (AH8)

They sum to w_p. Since mu is the product of these two raw coordinate
restrictions, L_mn has exactly their product count distribution.

These are the finite versions of PA2, not merely a convenient low-load
query law. Under normalized Haar on S_p, every depth-e cylinder has
probability at most1/(w_p*p^e), and the selected nested cylinders attain
each bound. The conditional comparison recorded in
[the source note](../../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound)
permits these exponent-dependent
caps and uses the same auxiliary uniform for every label within one
coordinate. Thus, for any complete query with this finite inventory and
any increasing nonnegative convex payoff, its raw mu expectation is
bounded by the corresponding distribution(AH8). The selected layout
attains that comparison exactly.

On the entire mixed union D, both positive coordinate counts vanish:

    L_mn=1 on D.

Consequently, for every real t>=1,

    integral_D (L_mn-t)_+ dH=0,
    integral (L_mn-t)_+ dlambda0
       =integral (L_mn-t)_+ dmu.                     (AH9)

For any other query, domination lambda0<=mu followed by the cited
convex comparison supplies the same upper bound. Thus(AH9) attains the
maximum raw lambda0 hinge, which is exactly the original pure-source
comparison value, simultaneously for every t>=1 and every finite
complete rectangular inventory. In particular it attains the t=2
old-query hinge used at the first11 stage.

The means remain finite:

    integral Np d(H_p restricted to S_p)=w_p+1/(p-1).

Therefore monotone convergence passes these identities and bounds to
the complete countable query inventory. The missing mixed mass always
comes solely from load1; there is no positive anchor-hinge rebate even
as its raw mass tends to1/12.

## 4. Legal first11 originals can realize the same active slot counts

The old query layout is compatible with actual original labels, rather
than being prohibited by a hidden phase constraint. Fix finite m,n,J.
For every d=5^a*7^b with0<=a<=m,0<=b<=n, and every1<=e<=J, add two
originals at modulus d*11^e. Use Q_ab's fixed old CRT phase and choose
11-coordinate residues11^(e-1) and2*11^(e-1), respectively. For d=1
there is no old-coordinate condition, so these include pure11 originals.

Every full numerical modulus receives exactly two distinct classes;
none equals an earlier anchor label. For each old point x and each
e<=J, the active-original count is precisely2*L_mn(x), and each of the
two CP5 slots has old count L_mn(x). Thus the maximal old-query hinge
above is realized by legal actual slot phases at the first11 stage.

This does not make the actual forbidden-fibre union attain its counting
bound. Indeed, in this explicit extension every mixed11 event is inside
one of its corresponding pure11 cylinders. The actual forbidden11
fraction is independent of x and equals

    b11=2*sum_(e=1..J)11^(-e)=(1-11^(-J))/5<1/5.

At the retained first11 threshold t=2 and cap C=5/3, g=1-b11>4/5, so
the actual CP2 row has mass min(1,C*g)=1. Its actual mass loss is zero.
This exhibits why saturation of the old-query hinge alone cannot imply
saturation of CP5: the fibre union bound remains a separate inequality.

## 5. Exact boundary of the refutation

The result rules out a positive uniform saving obtained solely by
subtracting the mixed deleted region from the maximal pure-source old
hinge, even after imposing the remaining nested pure5 geometry and
arbitrarily small pure deficits. It also shows that the same fixed
query phases simultaneously maximize all anchor numerical labels under
the actual normalized anchor survivor.

It leaves unresolved compensation through a different initial law,
actual forbidden-fibre overlap, later11/13/17/19 transport, or a joint
final numerator/denominator estimate. A clipped stage-loss payoff is
not an increasing convex function on its full extended load domain;
the cited convex comparison cannot be applied to it without another
argument. No claim about its maximum or about sharpness of actual CP5
follows from(AH9).

Adding arbitrarily deep nonzero pure originals on13,17,19, together
with the displayed finite11 extension, gives a six-prime actual family
while preserving all5/7 anchor statements and a surviving all-zero
point. This supplies the carrier if needed; it is not a lower witness
and says nothing against later-stage compensation.

## 6. Fixed finite verification

The fixed prefix-intersection program
[anchor_hinge_compensation.py](../../frontier/cover-geometry/anchor_hinge_compensation.py)
and its [JSON result](../../frontier/cover-geometry/anchor_hinge_compensation.json)
use H5=H7=A=B=4 and m=n=6. The recorded execution with
`python3 -I -S -B -O` exited0 and all24 checks passed. No full-period
enumeration or old constant-cap search was used. The test covers:

- 48 original classes on24 numerical labels, exactly two per label;
- 32 mixed rectangles and496 pairwise disjointness checks;
- 512 mixed/pure and1536 mixed/query intersection checks;
- exact pure masses313/625 and1601/2401;
- mixed raw union4992/60025 and actual anchor mass53759/214375;
- exact complete anchor norm10510427/9031512;
- zero raw hinge saving at t=1,2,3,4,6.

The general maximality proof(AH6), all-threshold equality(AH9), arbitrary
finite heights, countable completion, and actual11 label construction
are the ordinary proofs above. The finite checks support that proof's
specific control instance and do not replace its quantifiers.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/anchor_hinge_compensation.py
```

[Report544](544-missing-original-slots-restore-a-common-law-debit.md) extends this packing with four disjoint later loss regions. A fixed zero-debit completion remains insufficient even with the best labelwise maximizing final queries, but another legal completion gives a first11 debit1/35 and certifies the same actual law at every finite height in the construction. Its general weighted missing-slot criterion and actual-phase refinement also exclude further arbitrary two-copy families. Thus the obstruction concerns the specified completion, not all completion choices or the existence of a good law.
