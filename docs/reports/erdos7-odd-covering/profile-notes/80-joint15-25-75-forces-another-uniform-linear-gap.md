[Index](../marked_head_profile.md) · [Complete pure3 deletion](77-complete-pure3-deletion-gives-a-uniform-linear-gap.md) · [Endpoint source geometry](59-endpoint-linear-source-deletion-bound.md)

# Three original test cylinders bound the endpoint mean by238/375

At the actual source404 endpoint, carrier(0,1) and S=D=3/20, any
independently chosen original test cylinders T15,T25,T75 satisfy

    mu(T15)+mu(T25)+mu(T75)<=49/750
        =1/25+13/750+1/75-2/375.                    (J1)

Replacing precisely these three contributions in profile77 gives, for
every complete independently labelled original357 load A,

    integral A dmu<=238/375,
    6*D-integral A dmu>=199/750.                    (J2)

The same statements hold with limsup and liminf for arbitrary actual
finite families approaching this endpoint. The mean improves16/25
by2/375, and profile59's1157/1800 by73/9000. This is an ordinary
endpoint proof; no finite neighborhood, global K, improved survival
denominator or Lean verification is asserted.

The gain couples three tests on one actual source. Forbidden cofactors25
and75 cannot independently avoid all tests in the remaining tight
case. Their residues may differ at every seven depth; the argument
keeps all those choices and the complete exponent tails.

## 1. The retained source and deletion measures

Use the notation and actual endpoint saturation of profiles59 and77.
The pure3 masses are h=1/2, h0=1/6, h1=1/3 and eta2=1/9. The
five first slots P,A_s,B,Q,H contain respectively the first pure5,
alpha, beta, higher source labels, and the unique source-free slot.
Write U_P,U_A,U_B for the complete five-coordinate unions of the
pure5, alpha and beta source families. Saturation makes their
cylinders pairwise disjoint, including between families and depths.
Alpha deletion is on root1, beta on cell2; late source deletion is
on cell3 and is additional to these three unions.

For any five-coordinate set F put

    q(F)=Haar5(F minus U_P),
    a(F)=Haar5(F intersect U_A),
    b(F)=Haar5(F intersect U_B).

Let delta be actual deleted old-coordinate measure. Saturation gives
delta=V, the sum of all complete virtual forbidden-cofactor measures.
In particular each forbidden cofactor25 has a source-free depth2
five cylinder. A forbidden cofactor75 must use root1 and attain
h1/25; its five cylinder is source-free there and hence globally
source-free, because all other five-dependent source deletion is
pure5 and would also remove positive source mass on root1.

Retain the baseline forbidden families3,9 for T25, and the complete
pure3 families3^a with a>=3 from77. The former multiply the source
by

    w0=1-(1_root0+1_cell1)/5.

Its pure3 integral is4/9; its value is1 on root1. The latter delete
exactly q(F)/90, by77. Consequently the stronger version of its
pure5-cylinder estimate is

    mu(full ternary times F)
      <=(13/30)*q(F)-(1/3)*a(F)-(1/9)*b(F).          (J3)

Indeed integrate w0 against the source: the pure5 complement
contributes(4/9)*q(F), alpha deletes a(F)/3, and beta deletes b(F)/9.
Any additional late loss is nonnegative and can be dropped. Subtract
the same q(F)/90 only afterwards. The pure5 and alpha losses are
disjoint source losses, so retaining both does not subtract an
already removed region twice. Crucially q(F) remains in both terms
until their coefficients combine to13/30.

The families5,15,25,75 were not used in(J3). Their virtual measures
may still be subtracted where needed. The T15 baseline from59 uses
only3,9,5,15; it has not used25 or75 either. For T75 retain its raw
source cap h1/25=1/75, which uses no forbidden deletion. Thus the
extra25/75 deletion can be evaluated against the sum of the three
test indicators. Any overlap of their test supports is counted with
its actual multiplicity in that sum.

## 2. All nontight placements already have a gap

Profile59's affine root-slot table, over its complete late-deletion
interval, gives

    mu(T15)<=1/25,
    T15 not equal to root1 times H =>mu(T15)<=1/30.  (J4)

The removed third ternary root has zero source mass. Thus outside
root1 times H the gap is at least1/150>2/375, and the uniform
T25 bound13/750 and T75 bound1/75 finish(J1). It remains to fix
T15=root1 times H and write T25=full ternary times F, with F a
depth2 five cylinder.

Every F lies within one first slot. The easy cases give these losses
against its baseline13/750:

| Position of F | Additional loss |
| --- | ---: |
| Within P, or F=P2 | 13/750, because q(F)=0 |
| Within A_s, or F=A2 | 1/75, from a(F)=1/25 |
| Within B, or F=B2 | 1/225, from b(F)=1/25 |
| Within H | 1/150, from the still unused forbidden5 and15 families |

For the last entry, H is wholly source-free. Its extra deletion is
(1/5)*(h+h1)/25=1/150, while the pure3 baseline of(J3) remains
unchanged. The entries P2,A2,B2 denote the three distinct depth2
source cylinders inside Q. These exhaust all children of Q except
two, called R and S. Each easy loss is at least1/225; section4
combines that loss with the third test when necessary.

## 3. The two remaining children cannot both be source-free

All source cylinders P_b,A_b,B_b with b>=3 avoid P2,A2,B2 and the
other first slots. They lie in R union S. For each family their
complete five mass is

    sum_(b>=3)5^-b=1/100>0.                         (J5)

They are disjoint as five-coordinate sets. Hence R and S cannot
both be source-free. There is either no globally source-free child
of Q or precisely one, denoted K. Late source deletion can only
remove further candidates for K.

Every saturated forbidden25 or75 label therefore has its five
cylinder either in H or equal to K, when K exists. This statement
holds label by label, independently at every seven depth e. No
common residue or nesting is imposed.

If neither R nor S is source-free, all these labels lie in H.
Each has source intersection1/75 with T15=root1 times H. Since the
complete normalized seven caps satisfy sum_(e>=1)u_e=1/5, the two
families give an additional combined loss2/375 on T15 alone. This
proves(J1) in the no-K case with the other two original caps unchanged.

Suppose instead that K exists. If F=K, a forbidden25 label in H
has intersection1/75 with T15; if it uses K, its intersection with
T25 is h/25=1/50. A forbidden75 label has intersection1/75 with
T15 or T25 according as it lies in H or K. Thus for either family
and every independently chosen label,

    source integral of 1_cofactor*(1_T15+1_T25)>=1/75.

After multiplying by u_e and summing both complete families, the
joint gain is at least

    2*(1/75)*sum_(e>=1)u_e=2/375.                   (J6)

Together with the unchanged T75 cap, this proves(J1) when T25 uses K.

Finally suppose F is the other child, different from K. Every
P_b,A_b,B_b with b>=3 must then lie in F. In particular

    q(F)=1/25-1/100,
    a(F)=1/100.

By(J3), even discarding the beta loss, the loss from13/750 is at
least

    (13/30)*(1/100)+(1/3)*(1/100)
       =13/3000+1/300=23/3000>1/225.                (J7)

The first term is the decrease of the retained pure5-complement
factor. The second is the separate alpha source loss on root1;
disjointness of U_P and U_A ensures it survives after removing U_P.
Therefore every T25 placement other than K loses at least1/225
against its individual13/750 cap.

## 4. The third test either captures K or adds its own loss

Assume K exists. If T75=root1 times K, every forbidden25 or75
label has source intersection1/75 with T15 when its five cylinder
lies in H, or with T75 when that cylinder equals K. Thus the same
complete two-family gain(J6) applies to T15+T75, with T25 bounded
by13/750. This covers the second way a test can capture K.

It remains that neither T25 nor T75 captures K. The preceding
sections give a loss of at least1/225 on T25. Independently write
T75=root times F75. Every remaining placement loses at least1/225
against its raw1/75 cap:

| T75 placement | Additional loss |
| --- | ---: |
| Root0, any F75 | At least1/150, since h0/25=1/150 |
| Removed third root | 1/75 |
| Root1 with F75 in P,A_s, or equal to P2,A2 | 1/75, since the source vanishes |
| Root1 with F75 in B, or F75=B2 | 1/225, from the complete cell2 beta deletion |
| Root1 with F75 in H | 2/375, from the unused forbidden5 and15 families |
| Root1 with F75 the other residual child of Q | 1/150, from the disjoint complete higher pure5 and alpha source tails |

For the H entry, the source mass1/75 is multiplied by the extra
deleted fraction2/5. For the other residual child, each of the
pure5 and alpha tails has five mass1/100, and both remove root1
source mass h1/100; their sum is1/150. Beta and late losses may be
discarded. The only omitted root1 placement is F75=K, handled above.

Adding the two bad-placement losses gives2/225>2/375. The measures
used in the T25 and T75 bounds can overlap: their sum bounds the
sum of the two test indicators, including multiplicities. They
are never subtracted twice from one occurrence of the test load.
All cases now prove(J1).

## 5. Complete load and limiting families

In77, test15 contributes1/25. The pure5 test tail b>=2 contributes
13/600, consisting of the test25 bound13/750 and the complete
b>=3 tail13/3000. The3*5^b test tail contributes1/60, consisting
of the test75 bound1/75 and complete b>=3 tail1/300. Replace only
test15,test25,test75 by(J1), retaining every other original label
and every exponent tail. The resulting sum is

    16/25-2/375=238/375,
    6*(3/20)-238/375=199/750.                       (J8)

If any of the three test labels is absent, adding an arbitrary
residue only increases the nonnegative load, so the same estimate
applies. All other test residues remain independent.

For finite families approaching this source and carrier, use the
joint labelwise diagonal passage in59 and77. Each fixed source,
forbidden or test cylinder stabilizes. Their complete geometric
tails give source-measure convergence and uniform first-moment
tail control; pure7 normalizers stay at least5/6. The limiting
endpoint therefore satisfies(J1)--(J8), proving the stated limsup
and signed liminf without assuming any finite family attains an
infinite source budget.

## 6. Exact arithmetic reproduction

The [checker](../frontier/endpoint_linear_joint15_25_75.py) verifies
the inherited77 data, both affine source tables behind(J4), every
T25 and T75 placement margin, the complete five and seven tails,
both per-label intersection minima and the full revised original-test
sum. The
[certificate](../certificates/source_norms/endpoint_linear_joint15_25_75.json)
records these exact rational outputs. The ordinary proof above
supplies the source geometry and arbitrary-family quantifiers;
the checker does not claim to enumerate all original families.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_linear_joint15_25_75.py --check
```

Execution is read-only unless an explicit --output path is supplied.
