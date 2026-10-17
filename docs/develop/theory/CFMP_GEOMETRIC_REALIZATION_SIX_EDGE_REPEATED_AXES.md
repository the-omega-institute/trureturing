# CFMP geometric realization: repeated-axis two-flat obstructions

This volume continues Sections 459-475 of the
[six-edge high-axis volume](CFMP_GEOMETRIC_REALIZATION_SIX_EDGE_HIGH_AXES.md).
The paired response formulas and source framework are in the
[paired-reservoir volume](CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md);
the six-reservoir witness and at-most-two-flat reductions are in the
[five-reservoir return volume](CFMP_GEOMETRIC_REALIZATION_FIVE_RESERVOIR_RETURN.md).
Section numbers cited below refer to these linked volumes when they
are outside the present range.

The result here is restricted to exactly two flat owners in the stated
six-actual-edge repeated-frame class. Its upper sixth-label branch is
excluded. The one-flat and low sixth-label two-flat branches remain open.

## 476. Direct hypotheses and conclusion

Use a finite actual ideal face pairing with fixed-point-free involution on original face occurrences, vertex-induced fixed frames (R,A,B,O,A,B) in edge order (12,13,14,34,24,23), and distinct transverse actual labels A,B. Axes may repeat transverse labels. Retain every original slot, face map and normal interval. Use one common positive generalized length field with all original angle equations 2*pi.

Assume exactly six actual labels E={M,C,D,Z,U,V}, with distinct names and values greater than one. Suppose:

1. Every actual label has a genuine occurrence; every flat owner selects its two axial slots, each contributing pi.
2. M is a maximal-valued label selected by a flat pi slot. There is a source flat sigma of fixed pair {C,D} and one M axis, and a genuine source tau=(Z,M,C,D,M,C).
3. m>=1+c+d, z>=1+m+c and u>m. Thus c,d<m-2 and z,u>m.
4. No flat has a transverse occurrence of any label with value greater than m-2.
5. There are exactly two actual flat owners.

**Theorem 476.1.** These hypotheses imply p_M=p_C=p_D=p_V=1 and p_Z=p_U=0, where p_e counts original flat pi slots. In particular v<=m. The source has axes {M,Q} for exactly one Q in {C,D,V}; its other axis cannot repeat M. The second flat phi has the other two members of {C,D,V} as its distinct axes.

Let A be the larger-valued axis of phi and B its other axis. Then Q,A,B are exactly C,D,V, A is the unique numerically largest member of that three-label set, and phi has fixed pair {B,Q}. Its necessary flat inequality is

    (a-1)*(b-1)>=(b+q)^2.                     (476.1)

Consequently

    a>=b+2*q+2+(q+1)^2/(b-1)>b+2*q+2.        (476.2)

All six possibilities, up to vertex-induced exchanges of the two axes and of the transverse pair, are listed below. A word lists the fixed six slots, not merely a multiset.

| Q | A | B | sigma | phi | strict consequence |
|---|---|---|---|---|---|
| C | D | V | (M,C,D,C,C,D) | (D,V,C,V,V,C) | d>v+2*c+2 |
| C | V | D | (M,C,D,C,C,D) | (V,D,C,D,D,C) | v>d+2*c+2 |
| D | C | V | (M,C,D,D,C,D) | (C,V,D,V,V,D) | c>v+2*d+2 |
| D | V | C | (M,C,D,D,C,D) | (V,C,D,C,C,D) | v>c+2*d+2 |
| V | C | D | (M,C,D,V,C,D) | (C,D,V,D,D,V) | c>d+2*v+2 |
| V | D | C | (M,C,D,V,C,D) | (D,C,V,C,C,V) | d>c+2*v+2 |

These rows are necessary role cases, not six constructed quotients. Distinct actual labels with equal numerical lengths are retained; a tie for the largest of C,D,V is ruled out by (476.2), not by identifying labels.

## 477. Proof from original pi slots

The genuine witness of e contributes a strictly positive angle. Its complete 2*pi equation therefore permits at most one original flat pi slot: p_e<=1. Each of the two flat owners has two original axial pi slots. Thus all four selected labels are distinct, even within one owner. Since z,u>m, maximality of M excludes Z and U from selection. Exactly the four remaining labels M,C,D,V are selected, each once. This proves their p values and v<=m.

The source's M slot is unique, so its other axis Q is C,D or V. The second flat must select precisely the remaining two low labels; it cannot select M or Q again. Every flat transverse pair lies in {C,D,V}, since M,Z,U all have value greater than m-2.

Write phi's axis values as a>=b. The axial-flat test gives

    (a-1)*(b-1)>=(h+k)^2

for its transverse pair {H,K}. Because b<=a, this implies a>=1+h+k. Therefore A is neither H nor K: if A were H, the inequality would give a>=1+a+k, which is impossible, and likewise for K. The pair has two distinct labels among C,D,V, so it is precisely {B,Q}. Formula (476.1) follows. Finally

    (b+q)^2=(b-1)*(b+2*q+1)+(q+1)^2

proves (476.2). In particular a>b and a>q. This proves the claimed strict ordering, the exhaustion by the six rows, and the handling of equal numerical values.

No owner identifications, face maps or normal intervals are contracted in this argument. It counts original axial pi slots only. Additional genuine occurrences and repeated visits cannot increase the available pi-slot capacities. No degree or normal-circle hypothesis is needed beyond the direct premises above.

## 478. Exact binding to the existing six-edge repeated-frame ambient

The full hypotheses of Section 466 of the six-edge volume supply the ambient face pairing, six actual labels, distinct transverse frames, common positive field and complete equations. Sections 132-134 of the paired-reservoir volume supply the source M,Z,C,D,tau, its weak inequalities, and maximal selected M. Sections 304-307 of the five-reservoir return volume supply genuine witnesses of all six labels and axial selection of every flat. Sections 296-298 exclude flat transverse occurrences above m-2. Corollary 466.1 gives a second label U with u>m. The remaining actual label is V.

The at-most-two-flat theorem of Sections 309-313 leaves the one-flat and two-flat alternatives. Conditional on the latter, all direct hypotheses in Section 476 hold. Minimum original degree six and connected circular normal links remain necessary for these cited reductions; Section 477 does not independently weaken their ambient scope.

## 479. The upper sixth-label subcase

If v>m-2, V cannot occur transversely in any flat. Since phi has pair {B,Q}, its largest axis A must therefore be V. Only the second and fourth rows remain:

    sigma axes {M,C}, phi axes {V,D}, both fixed pair {C,D};
    sigma axes {M,D}, phi axes {V,C}, both fixed pair {C,D}.

The exact source and second-flat products are respectively

    (m-1)*(c-1)>=(c+d)^2, (v-1)*(d-1)>=(c+d)^2,

or the same display with C,D exchanged. No exchange of the genuine source tau is made: it retains transverse pair {M,C} and other axis D. Thus C/D symmetry here belongs only to the two flat products.

There is a further useful restriction on genuine CD-pair owners. In the first case, any such owner's unordered axes must be among

    {C,C}, {C,D}, {D,D}, {V,C}.                (479.1)

In the second case the list is

    {C,C}, {C,D}, {D,D}, {V,D}.                (479.2)

The lists are necessary possibilities, not sufficient genuine tests. To prove (479.1), put T=(c+d)^2. Every pair containing M and another label is flat: the other axis C gives the source product; the other axis D gives (m-1)*(d-1)>=(v-1)*(d-1)>=T; every other value is at least min(m,v), and m>=v>c,d by the two flat inequalities, so the product is also at least T. Replacing M by Z or U only increases that product. Thus no genuine CD-pair owner has an M,Z,U axis. Among C,D,V axes, {V,D} is flat by the second product and {V,V} is flat because v>d+2*c+2>c+d+1. The four remaining unordered pairs give (479.1). The proof of (479.2) interchanges C,D only in these product comparisons.

A genuine owner of pair CD can therefore remain; uniqueness of the source CD owner is not a consequence. No scalar counterexample or compatible face quotient is asserted. This role reduction alone leaves the global exclusions unresolved. Sections 480-494 exclude the upper-v two-flat branch; the one-flat and low-v two-flat branches remain open.

## 480. Hypotheses and conclusions

Retain the full six-actual-edge repeated-frame ambient of Section 466 and suppose there are exactly two flat owners. Use the source labels M,C,D,Z,U,V, with the source tau=(Z,M,C,D,M,C), m>=1+c+d, z>=1+m+c, u>m. Assume v>m-2. Sections 476-479 then give distinct labels Q,B with {Q,B}={C,D} and

    sigma=(M,C,D,Q,C,D),
    phi has axes {V,B} and pair {C,D},
    m>=v>m-2,
    T=(q+b)^2,
    (m-1)*(q-1)>=T, (v-1)*(b-1)>=T.             (480.1)

The source tau is unchanged when Q=D. Only the two flat products are expressed with Q,B. Put H={M,V,Z,U}; all its values are at least v. Let h(rho) count an actual genuine owner's original slots labeled in H, and E_H(rho) sum their actual angles. H has genuine capacity 6*pi. Its individual original degrees satisfy

    deg(M),deg(V),deg(Z),deg(U)>=6,
    genuine H-slot deficits (5,5,6,6),            (480.2)

because the two flats supply precisely one M and one V slot, and no Z or U slot.

**Theorem 480.1.** Exactly five genuine owners meet H. One is tau, with h=3. Their only possible high-slot count profiles (n_3,n_4,n_5,n_6) are

    (1,0,4,0), (1,1,3,0).                        (480.3)

There are no genuine owners with h=1,2 or 6. Any additional genuine owner uses only C,D and is not counted in (480.3). This is not a bound on the whole genuine-owner count.

The four owners other than tau have individual H-slot requirements, in order M,V,Z,U,

    (3,5,5,6).                                  (480.4)

In profile (1,1,3,0), their vector is exactly (3,5,5,6), so all four original H degrees equal six. In profile (1,0,4,0), their vector is (3,5,5,6)+e_X for exactly one H label X, so exactly one original H degree is seven and the other three are six. Repeated copies of a role remain separate actual owners.

## 481. Strong high/low separation

The exact identity

    (q+b)^2-4*(q+1)*(b-1)=(b-q-2)^2

and its Q/B exchange give, from (480.1),

    v>=4*q+5, m>=4*b+5, v>4*b+3.

Consequently, for w=max(c,d)=max(q,b),

    v>4*w+3, v>9, c,d<v-2.                         (481.1)

Here v>9 follows separately from v>=4*q+5 and q>1.
In particular v>1+2*w. No strictness of the two flat inequalities is assumed.

## 482. Owners with one or two H slots

The upper-V CD-axis lists in Section 479 show that an h=1 owner can only have pair CD and axes {V,Q}. If genuine, put

    L=T-(v-1)*(q-1)>0,
    J=(v+1)*(q+1)-(q-b)^2>0.

Since m<v+2, (480.1) gives T<(v+1)*(q-1). Thus

    0<L<2*(q-1),
    J>2*(v+1)+4*q*b,
    tan(theta_V/2)^2=(v-1)*J/((v+1)*L)
                     >(v-1)/(q-1)>4.           (482.1)

For the last inequality, (v-1)*(b-1)>=T and
T-4*q*(b-1)=(q-b)^2+4*q>0 give v-1>4*q. Therefore

    E_H=theta_V>2*atan(2)>2*pi/3.                (482.2)

The genuine V capacity is pi, so at most one such owner exists; denote its count by epsilon in {0,1}.

There is no genuine h=2 owner. If its two axes are high and its pair CD is low, its L is negative because (v-1)^2>T. Otherwise its transverse pair has one high value p>=v and one low value a<=w, and both axes r,o<=w. Then p-a>w+1, so

    J=(r+1)*(o+1)-(p-a)^2<0.

These are all ways to have exactly two high slots in a paired frame. No four-distinct-frame hypothesis is used.

## 483. Complete scalar charge table for h>=3

Every genuine high-incident owner other than the optional owner in Section 482 has h=3,4,5 or 6. The following strict charges apply with s=v>9:

    h=3: E_H>pi;
    h=4: E_H>4*pi/3;
    h=5: E_H>pi;
    h=6: E_H>11*pi/6.                           (483.1)

For h=3, there is one high axis r, one high transverse value p, and two low roles a,b (possibly the same actual label). Since p>=v>a+b, scalar Theorem 431.1 gives theta_r+2*beta_p>pi.

For h=4 with both axes high and one high transverse value, the scalar theorem of Sections 395-399 applies to r,p,o>=s>3 and 1<q<=s-2; it gives E_H>4*pi/3. Its proof is a formula in the four numerical inputs and does not require the axial actual labels to be distinct from one another or from p. We use that scalar statement, not the old four-distinct global census. For h=4 with both transverse values p,q high and both axes low, Section 392's calculation applies directly:

    L>=3*(s+3)*(s-1), J<=(s-1)^2,
    K=(sqrt(p^2-1)+sqrt(q^2-1))/(p+q),
    K^2*L/J>=3*(s+1)*(s+3)/s^2>3.

Thus E_H=4*atan(K*sqrt(L/J))>4*pi/3. The two transverse labels remain distinct actual labels, but their numerical values may coincide.

For h=5, write r,p,q>=s for the high axis and high pair, and theta=theta_r. The exact response is

    E_H=theta+4*atan(lambda*cot(theta/2)),
    lambda=K*sqrt((r-1)/(r+1))>8/9.              (483.2)

Scalar Section 441 proves E_H>pi, since lambda>1/2. The same formula counts all actual slots if r repeats one of the transverse labels.

For h=6, all six numerical values exceed nine. At each vertex with axial angle theta, the other two angles sum to 2*atan(lambda*cot(theta/2)), where lambda>8/9. The elementary AM--GM angle inequality in Section 157 of the paired-reservoir volume gives each vertex sum at least 4*atan(sqrt(lambda)). Hence the total six-angle sum is greater than 8*atan(sqrt(8/9)). To check the stated rational-pi bound, sqrt(8/9)>9/10, and

    pi/4-atan(9/10)=atan(1/19)<1/19.

Thus E_H>2*pi-8/19>11*pi/6, using pi>3. This proves the last row of (483.1) for repeated labels too.

## 484. Exactly five multi-high owners and six intermediate profiles

Let n=n_3+n_4+n_5+n_6. Tau is an h=3 owner and has E_H>pi. Every owner counted by n costs more than pi, so H capacity 6*pi gives n<=5.

The genuine H degree is at least 22. If n<=4, the largest possible high-slot count, using tau's three slots, is

    3+6*(n-1)+epsilon<=22.

It reaches 22 only if n=4, epsilon=1, and the three owners other than tau all have h=6. Their expense, together with tau, is greater than

    pi+3*(11*pi/6)>6*pi,

which is impossible. Therefore n=5.

The degree and expense inequalities give

    n_4+2*n_5+3*n_6+epsilon>=7,
    n_4+2*n_6+2*epsilon<3,                     (484.1)

where the second uses the weaker h=6 bound 5*pi/3 and the strict exceptional charge 2*pi/3. Along with n_3>=1 and sum n_j=5, these exhaust to six possible intermediate profiles:

| epsilon | n_3 | n_4 | n_5 | n_6 |
|---|---|---|---|---|
| 1 | 2 | 0 | 3 | 0 |
| 1 | 1 | 0 | 4 | 0 |
| 0 | 2 | 0 | 2 | 1 |
| 0 | 1 | 0 | 3 | 1 |
| 0 | 1 | 0 | 4 | 0 |
| 0 | 1 | 1 | 3 | 0 |

These integer inequalities are necessary only. No scalar sampling enters them.

## 485. The largest high label cannot be transverse in an h=3 owner

Choose an actual largest-valued label X. It belongs to {Z,U}, since both exceed m>=v>c,d. Numerical ties between Z,U are allowed; choose either tied actual label. Write x=x_X.

If an h=3 owner had transverse X, its other transverse value a and low axis b satisfy a,b<=w, while its high axis r<=x. Hence

    J<=(x+1)*(w+1)-(x-w)^2<0.

For the last strict inequality write x=4*w+3+t with t>0; its right side equals

    -5*w^2-10*w-5-(5*w+5)*t-t^2.

This contradicts genuineness.

A five-high-slot owner transverse at X costs more than 4*pi/3. Indeed its high pair p,q contains x, its high axis r<=x, and its low axis t<=s-2. Thus r<p+q+1. The acute-angle calculation in Section 393 applies without any assumed one-sided maximum gap:

    theta_r<pi/2, lambda>8/9>4/5,
    E_H>pi/2+4*atan(4/5)>4*pi/3.                (485.1)

The numerical inequality r<p+q+1 follows here from actual maximality, even when r repeats X. It is not an application of the four-distinct maximum-gap theorem.

## 486. Exclusion of epsilon=1

In either epsilon=1 profile, all five multi-high owners have h=3 or h=5. An axial-only X occurrence contributes at most one original X slot per such owner. The exceptional h=1 owner uses V, not X, and the two flats have no X slot. Since the original degree of X is at least six, at least one of the five owners has transverse X.

Section 485 excludes h=3 there, so it is an h=5 owner, with expense greater than 4*pi/3. The other four multi-high owners cost more than pi each, and the exceptional owner costs more than 2*pi/3. Their disjoint actual H slots would cost more than

    4*pi+4*pi/3+2*pi/3=6*pi.

This contradiction proves epsilon=0.

## 487. A six-high-slot owner would be the only transverse X owner

Consider either remaining intermediate profile with n_6=1, and call its six-high owner rho. Its charge exceeds 11*pi/6, while each of the other four multi-high owners costs more than pi. If a five-high owner had transverse X, (485.1) would give total H expense greater than

    11*pi/6+4*pi+pi/3>6*pi.

Thus no five-high owner is transverse at X. There is no h=4 owner in these profiles, and Section 485 excludes transverse X in h=3 owners. Therefore rho is the only possible transverse X owner.

There must be a transverse X occurrence. If X=U and the whole X circle were axial, tau contributes no X and the other owners supply at most n_3-1+n_5+2<=5 X intervals. If X=Z and its circle were wholly axial, actual face transport preserves tau's fixed pair {M,C} around that connected circle. No h=5 or h=6 owner has this pair, since both transverse labels of such owners are high. The remaining h=3 owners number at most two and supply at most one X axis each, again below degree six. This also handles a numerical tie z=u if X=Z is chosen.

Consequently rho is the unique actual transverse X owner. Every other X interval is axial. Each maximal axial run is proper and its fixed pair is read from a boundary face of rho. All labels of rho belong to H, so every such pair is contained in H. Tau's axial Z interval has fixed pair {M,C}, with C outside H. Connectedness therefore excludes X=Z. It follows that X=U, u>z, and no h=3 owner contributes an X interval: an axial h=3 owner has a high/low pair, incompatible with the boundary-pair conclusion.

## 488. Four repeated X slots close within rho

If rho has four X slots, its two axes are X and its pair is {X,A}, A!=X. Every face has labels X,X,A. Track any X corner across such a face. An axial X receiver would have fixed pair {X,A}; a transverse X receiver must also have pair {X,A}, since the other possible companion X is forbidden by distinct transverse labels. Either way the receiving owner is transverse at X and hence is rho.

All endpoints of rho's four original X intervals are therefore paired within those four intervals. A union of several components violates the connected actual X-circle hypothesis. A single component would have original degree four, below six. No interval is collapsed by a self-gluing or an orientation reversal. Thus rho has at most three X slots.

For the profile (n_3,n_4,n_5,n_6)=(2,0,2,1), only its two five-high owners can contribute further X intervals, one axial interval each. The full degree is at most 3+2=5, a contradiction.

## 489. The last six-high profile exceeds H capacity

In profile (1,0,3,1), degree(X)>=6 forces rho to have exactly three X slots and each of the three five-high owners to have one axial X slot. Thus deg(X)=6. Their three axial angles have sum strictly below 2*pi because rho's three X angles are positive. At least one of these axial angles theta is at most 2*pi/3.

For that owner's formula (483.2), the function

    f(theta,lambda)=theta+4*atan(lambda*cot(theta/2))

strictly decreases in theta and strictly increases in lambda on the actual paired domain 1/2<lambda<1. Here K<1 and sqrt((r-1)/(r+1))<1 give lambda<1. Indeed

    partial_theta f=1-2*lambda/
       [sin(theta/2)^2+lambda^2*cos(theta/2)^2]<0.

Therefore, using lambda>8/9,

    E_H>2*pi/3+4*atan(8/(9*sqrt(3)))>7*pi/6.     (489.1)

The last comparison follows from 8/(9*sqrt(3))>1/2>sqrt(2)-1=tan(pi/8). Both inverse tangents use their positive principal branch.

Tau costs more than pi, the two other five-high owners each more than pi, the owner in (489.1) more than 7*pi/6, and rho more than 11*pi/6. These disjoint actual H slots sum to more than 6*pi, a contradiction. This excludes every n_6=1 profile.

Only the two profiles (480.3) remain. The individual degree statements follow by subtracting tau's vector (2,0,1,0) from (480.2), and using the exact total high-slot count of the four remaining owners: 20 in the four-five-slot profile, and 19 in the three-five/one-four-slot profile. QED.

## 490. Scope

This theorem requires v>m-2 and exactly two flats in the stated six-actual-edge repeated-frame ambient. It does not remove the four-distinct requirement from the previously published full flat-exclusion theorem. The high-owner reduction alone does not exclude its two surviving profiles; Sections 491-494 supply their face obstruction. It does not control low-only genuine owners, establish compatible face gluing for a scalar inventory, or settle the one-flat branch. The normal-circle arguments use original degrees and retain loops, repeated owners, self-gluings and both orientation choices. The largest-edge argument invokes no unproved global gap for repeated frames.

## 491. Exact scope

Retain the full inherited six-actual-edge repeated-frame ambient of Section 466: the connected orientable compact 3-manifold with nonempty closed genus-at-least-two boundary, its finite actual ideal tetrahedron pairing with a fixed-point-free involution on original face occurrences, connected actual normal circles of original degree at least six, distinct transverse labels in every fixed paired frame, common positive generalized lengths, and every original angle equation 2*pi.

Suppose there are exactly two actual flat owners. Choose the same maximal-selected source data M,C,D,Z,U,V and tau=(Z,M,C,D,M,C), with m>=1+c+d, z>=1+m+c and u>m, supplied by the published reductions and Corollary 466.1. The second label U is named before V, so V is the remaining sixth actual label.

**Theorem 491.1.** These hypotheses are incompatible with v>m-2. Thus in this exact two-flat branch one necessarily has v<=m-2.

This does not exclude the low-V two-flat cases, the one-flat branch, or repeated-frame flats in general.

## 492. The input inventories

Section 479 gives, when v>m-2, exactly the alternatives

    sigma axes {M,C}, phi axes {V,D}, both pair {C,D};
    sigma axes {M,D}, phi axes {V,C}, both pair {C,D}.

In both alternatives sigma has no V slot, and phi has exactly one V slot, its axial slot. Let H={M,V,Z,U}. Theorem 480.1 proves:

- there are exactly five genuine owners meeting H;
- the only owner with exactly three original H slots is tau;
- every other H-incident genuine owner has four or five original H slots;
- there is no genuine owner with one or two original H slots;
- all remaining genuine owners have no H slot.

Only these conclusions are used below. There is no restriction on the number of low-only genuine owners.

## 493. Face-count obstruction

In a fixed frame (R,A,B,O,A,B), each original face has one axial role and both transverse roles. If a paired-frame owner has at least four H slots, every one of its faces has at least two original H slots:

- if both transverse roles are in H, they already supply two on each face;
- if exactly one transverse role is in H, reaching four total H slots requires both axes to be in H, so each face again has two;
- if neither transverse role is in H, there are at most two H slots in the owner, which is outside this case.

This counts slots, including repeated labels. It does not require four distinct actual labels or distinct numerical lengths.

The two original faces through phi's V axis both have actual edge-label multiset {V,C,D}, with exactly one H slot. Such a face cannot pair to a face of any genuine owner with four or five H slots. The only three-H-slot genuine owner tau contains no V label. A zero-H-slot owner also contains no V. The remaining flat sigma contains no V. Therefore the two VCD face occurrences of phi have no target outside those two face occurrences.

The face pairing is a fixed-point-free involution on original face occurrences. It consequently pairs these two distinct faces to each other. Their unique V edge is phi's single original axial V slot on both sides. Thus both endpoints of that one original V normal interval are paired to each other, giving a closed normal-circle component consisting of precisely one original interval.

The actual normal link of V is connected, so this component would be the whole normal circle. Its original degree would be one, contradicting the required degree at least six. This proves the theorem.

## 494. Explicit self-gluing map and orientation

For completeness choose phi's vertex-induced frame as

    (V,C,D,B,C,D), B in {C,D},

in edge order (12,13,14,34,24,23). The V faces are 123 and 124. Because V,C,D are distinct actual labels, the unique label-preserving map from 123 to 124 is

    (1,2,3) -> (2,1,4).

It sends edge 12 to edge 21, edge 13 to edge 24, and edge 23 to edge 14. The inverse is retained as part of the face involution. In particular, the map reverses the V-edge direction; no argument discards that possibility or assumes an orientation-preserving edge map. The normal interval still has its two original endpoints identified, so it is an isolated one-interval component. If a chosen manifold formalism additionally forbids the resulting edge inversion, that is an extra obstruction, not a premise used here.

Exchanging transverse labels or the two axes merely changes this vertex description. The unique V slot and its two actual faces remain the same slot-level configuration. Self-gluing is admitted and then contradicted by connected original degree, rather than excluded from the input class.
