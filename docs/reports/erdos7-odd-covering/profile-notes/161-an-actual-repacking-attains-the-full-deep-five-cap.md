[Index](../marked_head_profile.md) · [Actual source families](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Complete deep-three subtraction](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md)

# An actual repacking attains the full deep-five cap

The coefficient2/5 for an arbitrary deep pure-five test cylinder on
the saturated K face cannot be uniformly decreased, even when every
original mixed-seven cofactor and the complete union compatibility
are retained. There is an explicit sequence of finite families with
one residue at each distinct odd nonunit modulus3^a5^b7^e,
0<=a,b,e<=N, for which

    source ->398, survivor mass S_N ->53/360,
    5^b*mu_N(F_(4,b)) ->2/5 for every fixed b>=2.       (FC1)

All these cylinder limits hold for the same sequence of families.
The projected density is also exactly this coefficient on the full
source-free ball[20]_25, so nested deeper tests and their pair
intersections can attain their corresponding caps simultaneously.
An independently labelled complete pure-five test simultaneously
attains the first-cylinder cap14/225 and deep-tail mass1/50, hence

    lim integral_mu_N sum_(b=1..N)1_(test_b)=37/450.    (FC2)

Here test_1=F_(3,1) and test_b=F_(4,b) for b>=2. These are original
independent test labels, not a demand that residues be nested.

This is sharpness of the specified marginal cap and its pure-five
sum. It neither establishes sharpness of the full52-cost objective
nor gives a covering system or a new global K bound. It excludes a
strict uniform improvement of2/5 based only on adding more actual
forbidden carriers to that marginal estimate. A gain in a joint
objective can still use incompatibility between different tests.

## 1. Keep the entire original398 source

Use the cells C0=[0]_9, C1=[3]_9, C2=[1]_9, C3=[4]_9,
C4=[7]_9, and the cylinders from48:

    T_a(c,j)=[c+j*3^(a-1)]_(3^a), a>=3, j=1,2,
    F_(j,b)=[j*5^(b-1)]_(5^b), b>=1, j=1,2,3,4,
    G_(j,e)=[j*7^(e-1)]_(7^e), e>=1, j=1,...,6.

The source residues are [2]_3, [6]_9 and, for the remaining labels,

| Original source modulus | Old-coordinate cylinder |
| --- | --- |
| 3^a, a>=3 | T_a(0,1) x Z5 |
| 5^b | Z3 x F_(1,b) |
| 3*5^b | [1]_3 x F_(2,b) |
| 9*5^b | C2 x F_(3,b) |
| 3^a5^b, a>=3 | T_a(0,2) x F_(2,b) |
| 7^e | G_(6,e) |

Truncate every exponent at N>=3. As already proved in48, put

    t_N=(1-3^(2-N))/18,
    q_N=(1-5^-N)/4,
    h_N=5/9-t_N,
    s_N=h_N-q_N.                                  (FC3)

Here h_N is the ternary survivor mass before five-coordinate
source deletion; s_N is the complete old source mass. The source
parameters converge to398 and are not changed below.

The first-five slot H=F_(4,1)=[4]_5 contains no five-coordinate
source deletion, for any surviving ternary coordinate. All source
five cylinders have first nonzero digit1,2 or3. Define four new
families entirely inside H:

    B_(j,b)=[4+j*5^(b-1)]_(5^b), b>=2, j=1,2,3,4. (FC4)

Their first digit is4. Above that digit their first nonzero digit
is j at position b-1, so all B_(j,b) are pairwise disjoint in(j,b).
Each fixed-j family has mass sum_(b>=2)5^-b=1/20. Their four
complete families occupy H up to its measure-zero all-zero tail.
In particular they avoid every F_(4,k), k>=2, which lies in the
first-five slot [0]_5.

## 2. Repack the actual forbidden carriers, keeping every label

For each original mixed modulus3^a5^b7^e, a+b>0 and e>=1,
use the following old-coordinate cylinder and seven class j.
The seven cylinder is always G_(j,e), with no deletion or
identification of original labels.

| Original cofactor | Old-coordinate cylinder | j |
| --- | --- | ---: |
| 3 | [1]_3 x Z5 | 1 |
| 9 | C1 x Z5 | 1 |
| 3^a, a>=3 | T_a(3,1) x Z5 | 4 |
| 5 | Z3 x H | 3 |
| 15 | [1]_3 x H | 4 |
| 45 | C1 x H | 5 |
| 3^a*5, a>=3 | T_a(3,2) x H | 4 |
| 5^b, b>=2 | Z3 x B_(1,b) | 2 |
| 3*5^b, b>=2 | [1]_3 x B_(2,b) | 2 |
| 9*5^b, b>=2 | C1 x B_(3,b) | 2 |
| 3^a5^b, a>=3,b>=2 | T_a(3,2) x B_(4,b) | 2 |

Every row is a legal CRT residue of the stated original modulus.
Together with the source rows this supplies exactly(N+1)^3-1
pairwise distinct odd nonunit moduli at finite N.

The mixed rectangles are pairwise disjoint before source restriction:

- Class1 has two disjoint ternary carriers, root1 and cell C1.
- Class2 uses four pairwise disjoint B families. In the fourth
  family, different ternary depths a have disjoint T_a(3,2).
- Class3 and class5 each contain one old cofactor.
- In class4, the [1]_3 carrier lies outside C1. Inside C1, all
  T_a(3,1) and T_a(3,2) are pairwise disjoint, even at unequal a.
- Distinct seven classes and distinct e have disjoint G cylinders.
  All avoid the pure-seven source class6.

The reuse of a seven class is justified by this explicit old-space
disjointness. It is a property of the witness, not a restriction on
arbitrary original families.

## 3. Every old cofactor mass survives the repacking

The old mass of each row equals its mass in48's original398 family.
The unchanged three/nine rows and deep pure-three rows retain their
previous masses. A pure-five row has mass h_N*5^-b; an alpha row
has mass(1/3)*5^-b; a beta row has mass(1/9)*5^-b; a deep mixed row
has mass3^-a*5^-b. The new five cylinders are source free, and the
new ternary cylinders lie in the unaffected cell C1. Thus replacing
the old F_(4,b) carriers or the old C3 deep carriers changes none
of these labelwise masses.

In particular the complete old cofactor sum remains

    H_N=4/9+t_N+q_N/9-t_N*q_N.                    (FC5)

The physical pure-seven survivor normalization and the mass of
any one seven class after normalization are

    u_N=(5+7^-N)/6,
    kappa_N=(1-7^-N)/(5+7^-N).                    (FC6)

Disjointness, not just a union bound, therefore gives

    S_N=s_N-kappa_N*H_N ->53/360.                 (FC7)

This proves that the modified actual families approach the same
saturated K face. There is no limiting surplus mass that could pay for a
smaller cylinder coefficient; finite N need not lie exactly on the
saturated face.

## 4. All deeper five tests see only the already-retained deletion

Fix 2<=b<=N and let F=F_(4,b). It avoids every source five cylinder,
every mixed cylinder contained in H, and all B families. Its raw
old source mass is h_N*5^-b. Only the following forbidden old
cofactors meet it:

    3 and9: total old mass(1/3+1/9)*5^-b,
    all3^a, 3<=a<=N: total old mass t_N*5^-b.

Consequently the complete actual survivor, including every
original mixed-seven label, is exactly

    mu_N(F_(4,b))
      =[h_N-kappa_N*(4/9+t_N)]*5^-b.             (FC8)

Letting N tend to infinity gives(FC1), since h_N->1/2,
t_N->1/18 and kappa_N->1/5. The coefficient tends to

    1/2-(1/5)*(4/9+1/18)=2/5.

In fact, any measurable five-coordinate subset E of F_(4,2)=[20]_25
is source free and avoids all H-supported mixed carriers. The same
calculation, with Haar5(E) in place of5^-b, gives

    mu_N(Z3 x E)=[h_N-kappa_N*(4/9+t_N)]*Haar5(E). (FC10)

Thus the nested alternative test_b=[20]_(5^b), b>=2, also attains
these caps. For2<=b<=c, the test intersection is test_c and attains
the same coefficient times5^-c. A uniform reduction of a deep/deep
intersection cap cannot follow merely by requiring actual common
carriers either. This does not make the first-five test, which lies
in[3]_5, overlap the nested deep tests, nor does it settle mixed-test
or complete quadratic sharpness.

The forced27 cofactor belongs to this single complete deep-three
family. It has not been subtracted a second time.

For a fixed b, use all N>=max(3,b). Thus for every c<2/5, this
actual finite sequence eventually contradicts a proposed uniform
limiting bound with coefficient c. The same construction handles
all fixed b simultaneously; no source state is changed to optimize
a different test.

The first test F_(3,1)=[3]_5 loses the beta source cell C2, but
avoids all H-supported mixed carriers. Its exact surviving mass is

    (1/5)*[h_N-1/9-kappa_N*(1/3+t_N)] ->14/225.  (FC9)

Summing(FC8) for b=2,...,N adds

    [h_N-kappa_N*(4/9+t_N)]*(q_N-1/5) ->1/50.

This proves(FC2) directly from complete finite geometric sums.
The matching upper bounds14/225 and2/5 are the corresponding
cylinder bounds of75; the ordinary limit therefore establishes
sharpness of their pure-five sum37/450. It does not establish
simultaneous sharpness with other ternary, mixed or quadratic tests.

## 5. Exact checks and scope

The [helper](../frontier/full_family_five_cap_sharpness.py) reuses
48's source-label and CRT constructors, builds the new original
residues, and independently checks the old-coordinate bit masks
at heights3,4,5. At each height it verifies pairwise disjointness
within seven classes, uniqueness of every original modulus, and
equality of each old cofactor's mass before and after repacking.
It checks the full mass, both separated and nested test cylinders,
the exact nested pair intersections, and every finite test formula
above.

At height3 it also constructs the entire CRT union on all1,157,625
residues, independently recovering both the total survivor and the
first/deep-five cylinder masses. The
[certificate](../certificates/source_norms/full_family_five_cap_sharpness.json)
records exact rational results and the original-label digests.

Finite checks support the explicit construction; the disjoint-ray
proof and exact geometric limits supply its arbitrary-height scope.
No finite computation is promoted to a universal covering proof,
and no Lean verification or frozen theorem is claimed.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/full_family_five_cap_sharpness.py --check
```
