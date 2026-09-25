# All mixed supports containing three admit one complete-query law

Let P={3,5,7,11,13,17,19}. For every finite family of pairwise distinct
nonunit P-smooth numerical moduli, allow arbitrary pure prime-power
originals and require only that every mixed modulus is divisible by3.
All original residues are arbitrary and globally fixed, and every finite
exponent is allowed. There is one law rho on the actual full survivor U
such that

    R_P(rho)<=39957777861146009857190035233621514
                /3643308211616468584193048268731777
             =10.967443746247723...<11<565/51.           (AR1)

In particular a mixed original may contain all seven primes. The law
is obtained by normalized sequential reweighting and one final
conditioning; it is not asserted to be uniform Haar on U.

Section7 transports the same constants to any ordered seven odd
primes, with the smallest prime taking the role of3.

The same construction gives

    H(U)>41503/3686400.

Arbitrary additional distinct originals touching23 or29, with arbitrary
P-smooth cofactors and arbitrary fixed phases, still leave Haar mass
strictly greater than539/7372800. Exact larger bounds are given below.

This removes the restrictions on mixed support size and on phases for
the all-three-divisible case left open in
[report557](557-complete-query-comparison-allows-three-more-old-pair-towers.md).
The proof uses existing normalized distortion and conditional convex
comparison, with a support-specific cofactor count. It is ordinary
mathematics and exact rational computation, not new Lean verification.
Section6 also treats all fifteen rooted triangle towers together with
three specified non-3 pair towers. [Report570](570-rooted-triangles-and-nine-old-pairs-share-a-query-law.md)
extends that triangle support class to nine specified non-3 pair towers,
with a weaker query constant that still passes the actual pure23/29
continuation threshold. The stronger constants here remain valid on
their original classes. Unrestricted mixed supports and
Erdős #7 remain unresolved.

## 1. A single normalized construction retains the actual pure source

Let S_p be the complement of the complete actual pure-p forbidden union,
including every original height. Its Haar mass and normalized law obey

    w_p=H_p(S_p)>=(p-2)/(p-1),
    nu_p=H_p(.|S_p),
    nu_p([r]_(p^e))<=1/(w_p*p^e)
                    <=(p-1)/((p-2)*p^e).              (AR2)

The mass bound uses at most one original for each numerical p^e and
the full geometric sum. Pure cylinders need not be disjoint; no core
selection, phase alignment or discarded-source replacement is needed.

Begin with nu_3 and process q=5,7,11,13,17,19. Assign each mixed original
to its largest prime q. Because every such label contains3, its old
cofactor contains a positive power of3. Let A_q(h) be the union of the
assigned q-coordinate cylinders whose actual old projections match the
complete previous history h. Write alpha_q(h)=nu_q(A_q(h)).

For a fixed0<=delta_q<1, use the existing normalized distortion kernel
relative to nu_q. Suppress the forbidden part entirely when
alpha_q<=delta_q and rescale its complement by1/(1-alpha_q). When
alpha_q>delta_q, use density

    1/(1-delta_q) on the allowed part,
    (alpha_q-delta_q)/(alpha_q*(1-delta_q))
        on the forbidden part.                         (AR3)

The first case has alpha_q<1, so its denominator is nonzero. At
alpha_q=0 it gives the original law; at alpha_q=1 the second case is
the original law on the entirely forbidden fibre. Thus every history
has a normalized row, including these endpoints. Each row density is
at most1/(1-delta_q) relative to nu_q, and its assigned forbidden mass is

    (alpha_q-delta_q)_+/(1-delta_q).                   (AR4)

Let mu be the resulting normalized joint law. Each later row has mass
one, so it preserves the entire previous marginal and the probability
of every previously assigned event. All pure forbidden sets have mu
mass zero. The final law has full-past conditional cylinder bounds

    mu(X_q in[r]_(q^e) | X_<q)<=C_q/q^e,
    C_q=(q-1)/((q-2)*(1-delta_q)), C_3=2.              (AR5)

These bounds are asserted for mu, not for its later survivor
conditioning. The original cylinders, conditional rows and every event
probability in the proof belong to this same construction.

The supplier is the existing
[conditional comparison and distortion framework](../../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound).
The finite generic comparison is also present as
`Erdos7.ThreePrime.convex_load_comparison`; its namespace does not impose
a three-coordinate restriction. Here the rows are applied to the actual
pure-conditioned bases. No new declaration or build is needed for this
ordinary application.

## 2. Numerical distinctness gives the rooted cofactor count

Set t_q=(q-2)*delta_q. At each current exponent e, let L_(q,e)(h) count
the assigned originals q^e*d whose old projections match h. For this
fixed q and e, numerical distinctness means each complete old numerical
cofactor d appears at most once. Its residue may depend on its entire
label q^e*d, including e. There is no phase consistency assumption
between different original labels or different current exponents.

The actual union and AR2 give

    alpha_q(h)<=1/(q-2)*sum_(e>=1) lambda_e L_(q,e)(h),
    lambda_e=(q-1)/q^e, sum_(e>=1)lambda_e=1.           (AR6)

Only finitely many loads are nonzero. The infinite weight sum retains
the absent-exponent tail without inserting any actual original.
Combining AR4 with monotonicity and convexity of the hinge gives

    mu(A_q | h)
      <=(sum_e lambda_e L_(q,e)(h)-t_q)_+/(q-2-t_q)
      <=sum_e lambda_e(L_(q,e)(h)-t_q)_+/(q-2-t_q).
                                                               (AR7)

For each e, apply the existing conditional convex comparison to the
actual labelled cylinders under the SAME previous marginal. Only after
that comparison enlarge the auxiliary label inventory to all old
cofactors containing3. With independent auxiliary heights

    Pr(K_p>=j)=C_p/p^j, j>=1,

that complete rooted inventory has exactly

    M_q=K_3*product_(5<=p<q, p in P)(1+K_p)             (AR8)

active labels. Positive3-exponents supply K_3 choices, and every other
preceding prime supplies either exponent zero or one of K_p positive
choices. This differs from the unrestricted complete query precisely
in the first factor. No projected residues have been merged.

The comparison and AR7 therefore prove the absolute original-event bound

    mu(A_q)<=b_q,
    b_q=E(M_q-t_q)_+/(q-2-t_q).                         (AR9)

Every mixed original belongs to exactly one assigned event. Later normalized
kernels retain that event's probability, so the actual full survivor
satisfies

    mu(U)>=1-beta, beta=sum_q b_q.                     (AR10)

The auxiliary K_p are independent. The original events under mu need
not be independent, and AR10 only uses the union bound.

## 3. A rational schedule with a positive survivor reserve

Use the following fixed parameters:

| p | t_p | delta_p | C_p | E K_p |
| --- | ---: | ---: | ---: | ---: |
|3|—|0|2|1|
|5|0|0|4/3|1/3|
|7|1|1/5|3/2|1/4|
|11|2|2/9|10/7|1/7|
|13|4|4/11|12/7|1/7|
|17|4|4/15|16/11|1/11|
|19|6|6/17|18/11|1/11|

Every C_p/p is less than one, so these are valid height tails. For an
integer threshold t and nonnegative integer M, use the full-tail identity

    E(M-t)_+=EM-t+sum_(m<t)(t-m)Pr(M=m).              (AR11)

It retains every high value through the exact complete mean. The exact
rooted charges are

| q | b_q |
| --- | ---: |
|5|1/3|
|7|1/6|
|11|557/6615|
|13|318753584/5615638875|
|17|7068287929784/135713144692125|
|19|2319982374257978077418097494/53096680365671597133538434375|

Their sum and the resulting reserve are

    beta=78236943794575761664556566813
           /106193360731343194267076868750
         =0.7367404445604288...<7369/10000<59/80,
    s0=1-beta=27956416936767432602520301937
                  /106193360731343194267076868750>21/80.
                                                               (AR12)

The simple charge enclosure uses b11<843/10000, b13<568/10000,
b17<521/10000 and b19<437/10000. It suffices to establish positive
survival independently of the long exact fraction.

## 4. All maximizing queries use this one final survivor law

Define rho=mu(.|U), with s=mu(U)>=s0>0. For any finite exponent box,
choose one cylinder for every numerical label maximizing its mass under
THIS rho, and include the unit cylinder. Let their sum be L. For tau=5,

    E_rho(L-1)<=5+(1/s)E_mu[1_U*(L-6)_+]
               <=5+(1/s)E_mu(L-6)_+.                  (AR13)

Apply conditional comparison using mu's full-past caps AR5 to these
fixed label-dependent phases. Complete the auxiliary exponent box to

    V=product_(p in P)(1+K_p).

This is the complete query, so its3-factor is1+K_3, in contrast to the
rooted original inventory AR8. Finite maximizing choices suffice; take
increasing boxes afterward. The full auxiliary mean is finite, and
monotone convergence yields

    R_P(rho)<=5+B/(1-beta), B=E(V-6)_+.                (AR14)

No infinite maximizing phase choice is assumed, and no conditional cap
is falsely carried through the conditioning rho=mu(.|U).

For this schedule,

    EV=30720/5929,
    B=EV-6+sum_(v=1,...,5)(6-v)Pr(V=v)
     =7247078934354555645408264629987543
        /4613074987956458806693241537456250
     =1.5709865877478248...<63/40.                      (AR15)

Consequently R_P(rho)<5+(63/40)/(21/80)=11. The unrounded AR12 and
AR15 give AR1. This is a coupled source/query estimate: the deletion
charges and query numerator are both evaluated under mu. It does not
prove that the mixed loss under the original unmodified pure product
source is below33/40.

## 5. Haar mass and arbitrary23/29 extensions

AR3 and AR2 give a global density bound relative to product Haar:

    dmu/dH<=Lambda=product_p C_p=138240/5929.

Thus H(U)>=s0/Lambda, specifically

    H(U)>=27956416936767432602520301937
            /2475994297099153849802784000000
          >41503/3686400.                             (AR16)

Tensor rho with independent Haar at23 and29. Every additional label is
uniquely d*23^j*29^k with d P-smooth and j+k>0. Numerical distinctness
and the SAME complete query norm give added mass at most

    (1+R_P(rho))*sum_(j+k>0)23^(-j)29^(-k)
      =(1+R_P(rho))*51/616.

Since R_P(rho)<11, the relative reserve is greater than1/154. The
density of rho is at most Lambda/s0, so extended Haar survival is
strictly greater than

    (41503/3686400)/154=539/7372800.

Using AR1 and AR16 instead gives the stronger exact bound

    H(extended survivor)>=20622468644858247352380474918756791
                /198767216520031438577851546017024000000
              =0.00010375186112635405... .             (AR17)

All additional original residues and finite heights are arbitrary,
including the unit old cofactor. The old query bound is not asserted
after conditioning on these new survivors. No entropy-class G claim
or arbitrary further-prime continuation follows from this calculation.

## 6. All fifteen rooted triangle towers also permit three old pair towers

A complementary family allows every mixed modulus of the forms

    3^a*q^b, q in P\{3};
    3^a*p^b*q^c, distinct p,q in P\{3};
    5^b*7^c, 11^b*19^c, 17^b*19^c,

with all displayed exponents positive. Pure originals, phases and
finite heights remain arbitrary. Its one supported law satisfies

    R_P<=80283967152992661772129184071574303
             /7360298709373065579935919258329809
        =10.9077050162...<565/51.                       (AR18)

To prove this, first construct AR3 on the base consisting of all actual
pure originals, rooted stars, all fifteen rooted triangles and old5/7
originals. Use the SAME fixed parameter schedule. At current q, the
comparison is still applied before cofactor completion. The corresponding
completed cofactor count is now

    M_q=K_3*(1+sum_(5<=p<q)K_p)+1_(q=7)*K_5.          (AR19)

A star supplies K_3; each triangle supplies K_3*K_p. Old5/7 labels
supply K_5 only in the7-stage and have zero3-exponent, so they are
numerically disjoint from the rooted inventories. Their residues are
not merged. In particular M_7=(1+K_3)*(1+K_5)-1, giving charge41/180.
Applying AR7 to these counts gives the following full-tail charges:

| q | Charge |
| --- | ---: |
|5|1/3|
|7|41/180|
|11|1913/26460|
|13|801519881/22462555500|
|17|15294757690991/542852578768500|
|19|3304883745940030405587362321/212386721462686388534153737500|

Their sum is

    beta_triangle=151394965582137942235816821971
                     /212386721462686388534153737500
                 =0.7128268873849352...<143/200.       (AR20)

For q other than7, the full mean is1+sum_(5<=p<q)C_p/(p-1), the zero
atom is Pr(K_3=0), and positive low atoms follow from the additive
convolution of sum K_p with the scalar factor K_3. At7 the mean is5/3
and its zero atom is11/45. AR11 retains all high tails.

The auxiliary COMPLETE query V and its hinge B in AR15 are unchanged.
Without the last two old pair towers, the exact bound is

    R_P<=83225006696672104222677413623199303
             /7948506618108954070045565168654809
        =10.4705211551...<21/2.

Additional originals are charged under this SAME preconditioning mu.
Full-past caps imply for each additional old label d

    mu([a]_d)<=product_(p|d) C_p/p^(v_p(d)).

This follows by conditioning successively on the largest constrained
coordinate; unconstrained coordinates are integrated out, using their
normalized rows. Thus any disjoint additional mixed inventory of total
cap at most eta has full survivor probability at least
1-beta_triangle-eta. Condition only once on the complete actual survivor.
The complete query numerator is still B, so eta<=1/40 suffices:

    R_P<=5+B/(1-beta_triangle-eta)
        <5+(63/40)/(13/50)=575/52<565/51.              (AR21)

The entire old11/19 and17/19 towers have caps

    [C_11/(11-1)]*[C_19/(19-1)]=1/77,
    [C_17/(17-1)]*[C_19/(19-1)]=1/121,
    eta=18/847<1/40.

They have supports distinct from each other and from the base, so each
numerical original is charged once. Substituting this eta proves AR18
and gives Haar survivor at least

    56478224609794780426300590529
      /4951988594198307699605568000000.

After arbitrary further23/29-touching originals, the same density and
query argument as Section5 gives Haar mass at least

    8010805749144537785650749163256579
      /49691804130007859644462886504256000000>0.        (AR22)

The two classes in this report are alternatives. This triangle class
allows the three stated full non-3 pair towers, while the first theorem
allows arbitrary rooted support size. Neither class contains the other.
The weighted extra allowance AR21 also applies beyond the two displayed
pair towers, provided its actual numerical cap sum is certified; it is
not a free allowance for arbitrary omitted supports.

## 7. The same constants hold on any ordered seven-prime carrier

Let r_0<r_1<...<r_6 be any seven odd primes. Replace the reference
primes3,5,7,11,13,17,19 by these slots, and require every mixed modulus
to contain r_0. All conclusions AR1, AR16 and their Haar constants
remain valid for this carrier's complete query norm. In the alternative
triangle class, replace the old57, old1119 and old1719 supports by
r_1/r_2, r_3/r_6 and r_5/r_6 respectively; its same constants also hold.

Here the number of coordinate slots is still seven. To prove the
extension, retain the fixed thresholds by slot. For each later slot,

    C(r)=(r-1)/(r-2-t)=1+(t+1)/(r-2-t),
    g(r)=C(r)/(r-1)=1/(r-2-t).

Both decrease as r increases within the allowed range, as does
C(r)/r^e for every positive e. At the root, use
C(r_0)=(r_0-1)/(r_0-2), which has the same monotonicity. Each actual
ordered prime is at least its reference prime, so one independent
uniform variable per slot couples every actual auxiliary height below
its reference height.

The rooted cofactor count AR8, triangle count AR19 and complete query
product are nondecreasing in these heights. Consequently every original
hinge decreases, its coefficient g(r) decreases, the query hinge B
decreases, and the Haar density bound product C(r) decreases. Thus the
reference beta, B and Lambda simultaneously bound the one construction
for the new actual prime carrier. The two extra pair inventory costs
are products of the corresponding g(r), so18/847 remains an upper
bound. No new phase or height restriction enters this coupling.

For the extension, any two additional primes s>=23 and t>=29 suffice,
provided they are distinct from each other and from the chosen carrier.
They need not exceed all carrier primes. The CRT/tensor argument only
uses disjoint coordinates and

    s/(s-1)*t/(t-1)-1<=51/616.

This does not permit an arbitrary number of original prime coordinates;
it transports the same seven-slot theorem and its stated two-prime
extension.

## 8. Exact calculation and remaining obligation

The standalone producer uses exact fractions. For each factor1+K_p,

    Pr(1+K_p=1)=1-C_p/p,
    Pr(1+K_p=n)=C_p*(p-1)/p^n, n>=2.

For M_q, its zero atom is Pr(K_3=0); each positive low atom is a divisor
convolution of the preceding product with K_3. AR11 and AR15 use the
complete means, so the finite low-atom calculations do not truncate
any positive tail. The program also retains the exact surplus available
for additional original events charged under this SAME mu; costs from
another source may not be substituted.


The [all-rooted producer](../../frontier/cover-geometry/all3_normalized_conditioning.py)
and [exact results](../../frontier/cover-geometry/all3_normalized_conditioning.json)
pass35 checks. The data SHA256 is
`01a17e330dbad95e2dd6f20246e2ba168b6944b71c81981df46d22bd8e98c368`.
A separately written calculation reconstructs all six rooted hinges,
the query hinge, density and both Haar bounds using explicit low-product
formulas; its78 comparisons pass without importing the producer.

The [triangle producer](../../frontier/cover-geometry/all_triangles_old57_normalized.py)
and [exact results](../../frontier/cover-geometry/all_triangles_old57_normalized.json)
pass50 checks. Additive convolution is independently checked against166
contributing low-event tuples; the zero K_3 event is integrated exactly.
The exact-data SHA256 is `42f4acdde30ad22ac5708aa1d7c1d3c25d7c9583db7758ec584b91f329e8a104`.

Both scripts use only the Python standard library, retain explicit
failure checks under Python -O, and accept --output. Copies run from
another working directory with spaces in their paths reproduce identical
JSON bytes on the tested host. The general all-height conclusions rely
on the displayed kernel and comparison arguments, independently reviewed
as ordinary mathematics; finite arithmetic checks are not Lean proofs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all3_normalized_conditioning.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_triangles_old57_normalized.py
```

The proof establishes the all-three-rooted class and the complementary
triangle/old-pair class of Section6. For further arbitrary
mixed originals omitting3, their assigned cofactors need not contain3,
so AR8 must change. Paying them or reconstructing a law that supports
the needed stronger joint estimates remains necessary. Unrestricted
Erdős #7 is not resolved here.

[Report563](563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md) gives a complementary uniform-survivor law: under per-cofactor disjoint root prefixes, every rooted support and the complete mixed inventory on the four later primes may coexist. This does not remove that added prefix condition or enlarge AR1 without it.
