# The outside-square extension leaves an eighty-label pair core

Let P={3,5,7,11,13,17,19}, V={7,11,13,17,19}, and define the
eighty numerical labels

    B={3^a 5^b q^2 r : a,b in {0,1}, q,r in V, q!=r}. (OP1)

Consider any finite family of pairwise distinct odd numerical moduli
greater than one, supported on P together with 23,29,31. Every residue
is arbitrary and globally fixed. Pure powers and every original touching
23,29 or31 are unrestricted. Require each mixed P-supported original m
to satisfy at least one of

    some prime exponent of m is at least 3;
    v_3(m)<=1, v_5(m)<=1, and m notin B.             (OP2)

Then its complete survivor satisfies

    H(U)>=29425883435629461/290078064640000000000
         >1/10000.                                  (OP3)

All squarefree mixed originals are included by the second condition.
There is no cutoff on original or query heights. On the slice where
the central 3/5 exponents are at most one, this permits every remaining
outside-square label except OP1. Core mixed originals with maximum
exponent two and a squared central prime remain a separate restriction;
the eighty labels are not the entire unrestricted Erdős #7 frontier.

The same statement transports to any ten ordered odd primes, preserving
the exponent conditions and the first-two/next-five/last-three roles.
This extends
[Report594](594-five-joint-blocks-admit-ten-mixed-square-labels.md)
by 749 numerical labels on its seven-prime core. It is ordinary
mathematics with an exhaustive integer certificate, not a new Lean
result or a resolution of unrestricted Erdős #7.

## 1. An exact partition of the newly relevant numerical labels

Write e=(e_q)_(q in V), with each e_q in {0,1,2}, and require that
at least one e_q equals two. There are

    4*(3^5-2^5)=844

labels 3^a5^b product_q q^e_q with a,b in {0,1}. Unique prime
factorization makes all these numerical moduli different. Partition
them into four disjoint sets:

| Set | Numerical condition | Count |
| --- | --- | ---: |
|Already pure|q^2|5|
|Already in the joint block|3q^2 or5q^2|10|
|Excluded pair core|3^a5^b q^2 r, q!=r|80|
|New originals E|All other labels in the 844-element set|749|

The pure and ten joint-block labels were already admitted in Report594.
Every new label in E is mixed, has maximum exponent exactly two, and
has a squared outside prime. It was neither squarefree nor a member of
the previous height-three tail. Thus it receives a new loss charge
exactly once, with no charge removed from the complete future-query
inventory.

Together with Report594's pure, squarefree and complete height-three
families, this partition is exactly the condition OP2. It is not a
claim that different original residues can be chosen separately in
different branches of an estimate.

## 2. Restrict one actual boundary by the additional original cylinders

Let rho, zeta and eta_base be the actual common source, thinned joint
block and full old survivor submeasure of Report594. Its five retained
blocks have labels 3q,5q,15q,3q^2,5q^2. All active original phases stay
fixed. The density constant is D=3458/405.

Write a for the exact thinned block mass, L_old for the old complete
original-loss envelope, and Wbar for the complete weighted query
envelope. Thus eta_base(1)>=s_0=a-L_old and the actual all-height
query caps are bounded by Report594's six screens A_T,...,F_T.

Let E_actual be the new labels actually present, with their actual
original cylinders C_m. Define

    eta=1_(intersection_(m in E_actual) C_m^c) eta_base,
    s=eta(1),
    L_E=sum_(m in E) qhat_m,
    s_E=a-L_old-L_E.                                (OP4)

The nonnegative qhat_m are the old six-screen upper bounds, so

    s>=s_E,              eta<=eta_base<=zeta<=rho<=D H_P. (OP5)

Bounding the actual finite subset by all 749 labels only enlarges its
loss estimate. Restriction cannot increase a cylinder mass. Therefore
the complete weighted query bound Wbar still applies to this same eta,
including queries at occupied labels, unoccupied labels and every height.
No renormalized marginal or different source is substituted during the
loss estimate.

## 3. Closed support coefficients for all 749 additional losses

Put r_q=1/(q-1), a_q=1/[q(q-2)]. Let T be the nonempty outside
support of a new original. Its 3/5 exponents choose one of the screens

    (a,b)=(0,0),(0,1),(1,0),(1,1)
        -> A_T, B_T, C_T, E_T,

respectively. The coefficient contains a factor 1/4 when b=1; the
ternary first-root mass is already inside C_T and E_T.

For |T|=1, the only new label is 15q^2, giving

    (a_q/4) E_{ {q} }.

For |T|=2, the two configurations with exactly one square belong to B.
Only the configuration with both outside coordinates squared remains,
so put K_T=product_(q in T)a_q. For |T|>=3, no such pair-core label is
present, and summing every exponent choice containing at least one two
gives

    K_T=product_(q in T)(r_q+a_q)-product_(q in T)r_q.

Consequently the complete additional loss is

    L_E=sum_(q in V)(a_q/4) E_{ {q} }
          +sum_(|T|>=2)K_T[A_T+B_T/4+C_T+E_T/4].    (OP6)

These are 109 nonzero entries in the inherited 192-entry coefficient
array; all other entries vanish. A separate enumeration of the 749
distinct numerical labels gives precisely the same coefficients.
The full old original and query series remain unchanged; OP6 adds
only the formerly excluded height-two labels.

## 4. The direct continuation criterion retains layout correlation

Keep the controls delta_23=2/5, delta_29=9/20, delta_31=1/2 from
Report594. Their total linear charge coefficient and density factor are

    c=1084133/201247200,       density multiplier=200/33. (OP7)

The quantity to certify on each common boundary is

    K=(1-c)s_E-c Wbar
     =(1-c)(a-L_old-L_E)-c Wbar.                    (OP8)

If K>0, then s_E>0, since Wbar>=0 and 0<c<1. Normalize just the
actual complete head, mu=eta/s. For every finite head resolution Q,
the ordered-pair query bound of Report592 gives

    Gamma_Q(mu)<=1+Wbar/s<1/c.

The three physical-law capped kernels are therefore legal and leave
positive survivor mass at every stage. Indeed their total charge is
c Gamma_Q(mu), and each intermediate charge is a nonnegative partial
sum of this same total. The later kernels preserve the preceding full
joint law, while charging every actual new-prime original with its
numerical cofactor, residue and complete exponent vector.

The final normalized survivor lower bound is at least

    1-c(1+Wbar/s).

Multiplying by the head mass and converting the density D/s followed
by 200/33 back to Haar yields

    H(U)>=33/(200D)[(1-c)s-cWbar]>=33K/(200D).       (OP9)

This argument does not reimpose Gamma<180. The old seed-180 bound was
a sufficient condition for Report594, not a necessary hypothesis of
these kernels. The actual threshold for their fixed controls is 1/c.

It is also essential to keep the correlation in OP8. For example, the
separate uniform raw-cap sum for E is

    E_raw=32454256285861/2031038730040320.

Subtracting (1-c)E_raw from Report594's already minimized raw-tail
constant gives

    -345120543988156112187668703247
      /1287848117207576535367680000000000<0.         (OP10)

Thus those two separate uniform estimates do not certify the extension.
OP8 instead uses the old loss, the added loss and the future queries
on each one shared boundary before taking the minimum. Failure of
OP10 is a limitation of that sufficient estimate, not a covering.

## 5. The same finite comparison family gives a positive global bound

For each q, Report594's actual thinned factor b_q is a convex combination
of the 64 aligned templates

    1-(r_q+a_q)[1_(row=I_q)+1_(column=J_q)]
       -r_q 1_(cell=K_q).

In OP8 the positive block-mass coefficient is 1-c. Every subtracted
screen coefficient is nonnegative and equals

    (1-c)(old_loss_coefficient+extra_loss_coefficient)
       +c*weighted_query_coefficient.

Hence OP8 is concave in each q-vector separately, and in the ternary
root mass t. The 64-template reduction and t endpoints 1/3,2/3 therefore
remain valid. The additional coefficient array depends on outside
support and central presence, and is invariant under the same global
permutations of the three nonzero central columns. The complete number
of representative cases is again

    [(4^10+3*2^10+2)/6]*2^10*2=358963200.

The existing engine uses factor intervals at scale 2^20 and product
rounding in the outward directions. Round the positive gain down and
all subtracted coefficients up at scale 10^9. On all cases the integer
certificate gives

    K>=delta=33025682868271/6291456000000000>0.       (OP11)

The minimum has t=2/3 and template codes (9,18,27,27,27), in q order.
Summing the old 127 nonempty supports and then every one of the 749
new numerical labels independently gives the unrounded value

    278187858904534348637019289/52972815133577269208678400000.

Reconstructing the 32 directed support tables gives exactly OP11.
The full scan, rather than the single witness, supplies the uniform
lower bound. Substitution in OP9 proves OP3.

At this witness, the new envelope 1+Wbar/s_E equals

    44699561919219359585735/247711319495087204736>180.

This explains why the direct criterion is used. It does not assert
that the actual optimal joint moment exceeds 180.

## 6. Reproducibility and the remaining interactions

The [producer](../../frontier/cover-geometry/outside_square_pair_core_profile.py)
retains both the exponent enumeration and independent closed formula
OP6. The [data](../../frontier/cover-geometry/outside_square_pair_core_profile.json)
record all 749 admitted and 80 excluded numerical labels, coefficients,
source and input fingerprints, complete coverage, directed-rounding
bounds and exact witness reconstructions. The shared
[engine](../../frontier/cover-geometry/multi_joint_square_scan.cpp)
accepts one or three profiles; its factor, support-mask and symmetry
enumeration are unchanged. The Report594 three-profile certificate is
rechecked against this extension.
All 20 producer checks pass. Independent label enumeration and direct
rational reconstruction agree with the new certificate; the 41 checks
of Report594 also pass, with its three bounds unchanged.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/outside_square_pair_core_profile.py

Applying the same simple union envelope to all 829 formerly remaining
outside-square labels is negative at the displayed witness. The result
therefore does not infer OP3 for that larger inventory. The eighty
constraints OP1 couple a second digit in one outside coordinate to a
first digit in another. Their joint effect remains a mathematical
obligation, together with the central-square classes and unrestricted
additional prime support.

The digit-injection averaging of Report592 transports OP2--OP3 to any
ten ordered odd primes. It preserves every exponent vector, numerical
distinctness and the unrestricted last-three-coordinate inventory;
it does not identify first-root agreement with compatibility of the
second digits.
