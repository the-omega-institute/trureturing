[Index](../marked_head_profile.md) · [Fractional hinge](41-a-source-hinge-deficit-improves-actual-ap45-survival.md) · [Whole-hinge source](42-whole-hinge-absorption-sharpens-actual-survival.md) · [Deeper-cofactor gain](45-two-deeper-cofactors-give-a-uniform-survival-gain.md)

# One forbidden-carrier mixture strengthens survival

The three survival costs h_(5/2), h4 and h5 admit simultaneous
carrier-conditioned bounds on the same actual surviving mass S.
Their original test residues remain independent. What is common is
the forbidden family: at each positive7 depth its cofactor3 and
cofactor9 deletion labels are the same in every test inequality.

Retaining that common pair until after the three margins are combined
gives one minimum over18 carrier choices. The same mixture also
controls the lower bound for S. In addition, profile45's27/81 gain
holds conditionally on each of these shallow carriers, so its constant
14/4640625 can be added before the common minimum is taken.

This note proves these three-hinge and mass statements by ordinary
mathematics. It does not condition the41 linear numerator directions,
the five exceptional quadratic directions, or the square deficit on
this carrier. Their previously proved independent bounds may still
be used in the numerator. No Lean verification, negative-Q conclusion,
or resolution of unrestricted Erdős #7 is asserted.

## Actual measures and a single common carrier mixture

Fix an arbitrary finite original forbidden family in the effective9
branch, and any complete original357 tests used in the AP11/T4,AP13/T5
survival comparison. Use the actual measures of profiles31,39 and42:

    eta = raw pure3 survivor measure,
    nu5 = raw pure5 survivor measure,
    Lambda = raw actual35 survivor measure,
    lambda = its3-coordinate marginal,
    Lambda <= eta tensor nu5 <= eta tensor Haar5.

On the five surviving mod9 cells, with ROOT=(0,0,1,1,1), write

    eta_l=eta(cell l), n_l=lambda(cell l), s=sum_l n_l,
    0<=d lambda/d eta<=d_l pointwise, d_l>=1/4,
    eta(C_a)<=3^-a for every depth-a ternary cylinder C_a.

The product domination and pointwise density bound are hypotheses
provided by the actual survivor construction. Cell masses alone do
not imply them. Let M=(Lambda/s) tensor normalized actual pure7,
let V be the complement of the actual mixed7 forbidden union, and put

    S=s*M(V), D<=S<=s, D>0, nu357=M(.|V).

For an original test i with its own complete load A_i, cost f_i and
barrier C_i, define its actual signed deficit

    d_i=C_i*S-s*E_M[f_i(A_i)*1_V].                 (JC1)

The tests and their internal source layouts need not agree.

At positive original7 depth e, let r_e be the actual forbidden
cofactor3 root and j_e the actual forbidden cofactor9 cell. An absent
or killed carrier is represented by empty. Thus

    c_e=(r_e,j_e) in C,
    C={empty,0,1} x {empty,0,1,2,3,4}.

There are10 full and8 partial/empty carriers. The complete normalized
pure7 cylinder caps are

    u_e=6/(5*7^e), sum_(e>=1)u_e=1/5.

Pad absent large depths with empty carriers and define

    pi_c=5*sum_(e>=1)u_e*1_(c_e=c),
    pi_c>=0, sum_c pi_c=1.                         (JC2)

These are cap-mixture weights, not actual carrier probabilities.
They are nonetheless one common set of weights for all the tests
and the mass inequality below. Distinct original7 residues can have
different actual pure7 masses; each is bounded by its corresponding
u_e before the weights in(JC2) are used.

Every such cap enlargement is applied to a nonnegative deleted
integrand. Signed carrier coefficients are retained only after that
step. Enlarging weights directly on a signed expression would not
be valid.

## The fractional hinge keeps its signed shallow carriers

Take f(v)=(v-5/2)_+, C25=7/2 and the independently labelled source
layouts b,c5 in the ten-element baseline set of profile41. Put

    v_l=Delta f(b_l), k_l=C25-f(b_l), t_l=c5_l*v_l,
    a_l=k_l*n_l-t_l*eta_l/5,
    z_l=k_l*d_l-t_l/5, w_l=9*eta_l*k_l.

The three original5,15,45 events have ternary supports given by the
whole carrier, c5's root and c5's cell. Their mod5 residues are their
own original residues. If N is their active count, convexity gives

    (C25-f(A))_+<=k_l-v_l*N,  k_l-v_l*N>=0,
    0<=t_l<=k_l, z_l>=k_l/20>=0.                   (JC3)

The complete zero7 source cost psi of profile41 satisfies
Delta psi(b_l)>=v_l. For one of the three selected events, let h<=1/5
be its actual raw pure5 event mass, let Dtest be its ternary support
and Itest its full35 event. Define positive measures on ternary sets E:

    K(E)=integral_eta v*1_(Dtest intersect E),
    R(E)=h*K(E)-integral_Lambda v*1_(Itest intersect E)>=0.

The original selected-source comparison loses at least

    (1/5-h)*K(Omega)+R(Omega)                       (JC4)

for this event, once. The R term is the loss in enlarging Lambda to
the actual pure product; the other term is the loss in enlarging h
to1/5. The source increment available for each selected event is at
least v. After its linear event term is subtracted, the residual
increment remains nonnegative and increasing, so the original convex
source comparison still applies. Thus(JC4) is the existing profile41
source payment, not an additional budget or a new independence
assumption. The three events have three distinct payments.

For the five selected pure3 cofactors3,9,27,81,243, let alpha index
their actual deleted cylinders E_alpha at all7 depths and let
b_alpha=u_e. Their total cap multiplicity is5*(1/5)=1. Consequently,
with B=sum_alpha b_alpha*K(E_alpha),

    B<=K(Omega),
    sum_alpha b_alpha*R(E_alpha)<=R(Omega).

After(JC3) has allowed the cap enlargement on the nonnegative floor,
the part involving this selected event, including its source payment,
obeys

    -h*B+sum_alpha b_alpha*R(E_alpha)
       -[(1/5-h)*K(Omega)+R(Omega)]
      <=-h*B-(1/5-h)*B=-B/5.                       (JC5)

This proves the correction without using the payment twice. Summing
(JC5) over the three test events leaves, on each selected cylinder E,

    integral_E k d lambda-integral_E (t/5) d eta.   (JC6)

At depths1 and2 retain this signed expression exactly. For
c=(r,j) define

    A_c(a)=1_(r!=empty)*sum_(ROOT(l)=r)a_l
                              +1_(j!=empty)*a_j,
    R(w)=max(w_0+w_1,w_2+w_3+w_4).

Empty carriers contribute zero; negative entries of a are not
replaced by positive ones at a fixed carrier. At depths3,4,5 the
pointwise density bound makes(JC6) at most3^-a*max_l z_l. Its cap
extension is safe because z_l>=0. The remaining pure3 depths a>=6
are bounded by3^-a*max_l(k_l*d_l). Their complete coefficients are

    sum_(a=3..5)3^-a=13/243,
    sum_(a>=6)3^-a=1/486.

All positive5 forbidden cofactors are bounded without this source
payment. The sum of their5 caps is1/4. Old3 depths0,1,2 contribute
respectively sum(w)/36,R(w)/36,max(w)/36; depths>=3 contribute
max(k)/72, by product domination and the cylinder caps. Hence put

    T25(k,t)=(13/243)*max(z)+(1/486)*max(k*d)
                +(sum(w)+R(w)+max(w))/36+max(k)/72. (JC7)

Every term in(JC7), as well as A_c, still receives the complete
outer7 factor1/5. Let U25(theta;b,c5) be profile41's retained complete
source envelope with its original first-positive5 layout kept through
the complete positive5 tail, including the unchanged other7 blocks.
Define

    Q25(theta;c)=max_(b,c5)[U25(theta;b,c5)
                                      +(A_c(a)+T25(k,t))/5],
    m25(theta;c)=(7/2)*s-Q25(theta;c).              (JC8)

Before the independent test-layout maximum, the actual deficit is
at least

    (7/2)*s-U25-T25/5-sum_e u_e*A_(c_e)(a).

Using(JC2) and then taking the layout maximum separately in every
carrier yields

    d25>=sum_c pi_c*m25(theta;c).                  (JC9)

In particular

    max_c A_c(a)=max(0,R(a))+max(0,a_0,...,a_4).

Thus minimizing m25 over the18 carriers recovers the individual
profile41 bound exactly. The conditioning has not changed its
source budget or discarded any signed term.

## The two absorbed hinges and partial-carrier completion

For t=4,5 write h_t(v)=(v-t)_+, chi_t=min(1,h_t), and let psi_t,
P_t and F_theta be the complete zero7 cost, positive7 complement
and cell-dependent source operator of profile42. The source operator
uses each test's own complete35 load Z0,t and its own source labels.

Set w_l=9*eta_l and retain the complete unweighted remainder

    T2=(max(d)/18+(sum(w)+R(w)+max(w))/36+1/72)/5.

For any carrier c=(r,j), including partial carriers, put

    omega_(c,l)=(1_(r!=empty and ROOT(l)=r)
                                      +1_(j!=empty and l=j))/5,
    h(c)=sum_l n_l*omega_(c,l).

For a full carrier define

    H_t(c)=h(c)+F_theta((psi_t-omega_(c,l)*chi_t)_l).

For a partial carrier use the completion envelope

    H_t^+(c)=max_(c' full extending c)H_t(c'),
    m_t(theta;c)=s-P_t-T2-H_t^+(c).                 (JC10)

For a full carrier this definition gives H_t^+(c)=H_t(c). Every
partial carrier has a full completion. The justification precedes
the application of F_theta: for the actual test load,

    psi_t(Z0,t)+omega_c*(1-h_t(Z0,t))_+
      <=psi_t(Z0,t)+omega_c'*(1-h_t(Z0,t))_+.

The multiplier of omega is nonnegative. No monotonicity of the
numerical envelope as a function of omega is being assumed. Different
tests may use different completing carriers in this upper bound.

The actual signed deletion identity and its nonnegative union bound
give

    d_t>=s-P_t-T2
       -sum_c pi_c*integral_Lambda[
              psi_t(Z0,t)+omega_c*(1-h_t(Z0,t))_+].

Here the single source integral has been distributed over pi using
sum pi=1; it has not been duplicated. The absorption identity

    psi_t(v)+omega*(1-h_t(v))_+
       =omega+psi_t(v)-omega*chi_t(v)

and the complete source bound imply

    d_t>=sum_c pi_c*m_t(theta;c), t=4,5.            (JC11)

The costs are admissible because their native h_t coefficient is
29/35-omega>=29/35-2/5>0 and their other hinge coefficients are
nonnegative. Taking the maximum of H_t^+ over all18 carriers equals
the old maximum of H_t over the10 full carriers. Thus(JC11) also
recovers exactly the preceding individual absorbed margin.

## The same mixture bounds the actual source mass

Apply the identical complete deletion caps to the nonnegative
integrand1. The two shallow cofactors contribute

    sum_e u_e*[lambda(C3,e)+lambda(C9,e)]
       =sum_c pi_c*h(c).

The other cofactors contribute at most T2. Therefore, with

    D_c=s-T2-h(c),

one has

    S>=sum_c pi_c*D_c.                             (JC12)

The empty entries in h(c) contribute zero. No conditional actual
measure or hypothetical family is defined by D_c. The unconditioned
minimum is the existing D because the maximum shallow mass is
(R(n)+max(n))/5. The upper bound S<=s remains available independently.

## The27/81 gain holds with this same shallow mixture

The unconditional conclusion of profile45 alone would not imply a
carrier-conditioned improvement. Its fixed-carrier proof gives the
stronger statement needed here.

At every7 depth retain the actual quadruple

    gamma_e=(C3,e,C9,e,C27,e,C81,e),
    xi_gamma=5*sum_e u_e*1_(gamma_e=gamma).

All four entries can be empty. Complete the unused depths with the
empty quadruple. Then sum xi=1 and the shallow marginal of xi is
exactly pi in(JC2).

First fix a full shallow carrier c and any pair of deeper carriers.
On the actual mod81 refinement set

    omega2=omega_c,
    epsilon=(1_C27+1_C81)/5,
    f=psi_t-omega2*chi_t,
    g=f-epsilon*chi_t,
    a_t=5^-t, d_*=max_l d_l.

The unperturbed f is constant on each mod9 parent. The refined g
remains admissible because omega2+epsilon<=4/5, leaving native
hinge coefficient at least29/35-4/5=1/35>0.

Profile45's source perturbation and refinement inequalities, applied
before maximizing the deeper pair, give

    F4(g)+integral_lambda epsilon
       <=F4(f)+integral_eta(d-a_t)*epsilon
       <=F2(f)+(d_*-a_t)*(1/27+1/81)/5.            (JC13)

The first inequality retains the signed initial coefficient
n_child-eta_child/5. Its nonnegative slack is

    (1-chi_t(v))*(d_child*eta_child-n_child)
       +chi_t(v)*(d_child-1/5)*eta_child
       +eta_child*kappa_t(v),

where kappa_t(v)=sum_(n>=2)(4/(n*5^n))*[chi_t(n*v)-chi_t(n)]>=0.
Thus(JC13) remains valid when the refined source baseline exceeds t;
one cannot simply discard the signed baseline term. The second step
uses F4(f)<=F2(f) for parent-constant f and the cylinder caps. It does
not average the fine perturbed cost g back into its parent cells.

Removing the two full caps from the old deletion remainder gives

    T4=T2-(d_*/5)*(1/27+1/81),
    sum_(a>=3)3^-a-sum_(a>=5)3^-a=1/27+1/81.

Combining this identity with(JC13) shows that every fixed deeper pair
over the fixed full shallow c has source/deletion upper bound at most

    P_t+T2+H_t(c)-delta_t,
    delta_t=a_t*(1/27+1/81)/5=4/(405*5^t).          (JC14)

For a partial shallow c, complete it to any compatible full c' in
the nonnegative deleted integrand before the source bound. The same
delta_t works for every such completion; their maximum is therefore
P_t+T2+H_t^+(c)-delta_t. A missing or empty deeper label also causes
no problem. Its perturbation integral is zero, while T2 had charged
its complete cap; removing that cap leaves additional slack. No
positive actual occupation of C27 or C81 is required.

Apply this bound separately to each quadruple in xi and sum. Its
shallow marginal is pi and its total mass is1, so the result is

    d_t>=sum_c pi_c*[m_t(theta;c)+delta_t], t=4,5,
    delta4=4/253125, delta5=4/1265625.              (JC15)

This proves the conditional extension. Adding the uniform credit to
a common minimum is justified by(JC15), rather than by distributing
an already maximized unconditional bound.

## Joint survival and fixed-target consequences

Define the carrier-conditioned three-hinge margin

    M_c=m25(theta;c)/22+m4(theta;c)/6+4*m5(theta;c)/33,
    delta=delta4/6+4*delta5/33=14/4640625,
    M_c^+=M_c+delta, q=23/42.

Multiplying(JC9) and(JC15) by their nonnegative survival weights and
adding yields

    d25/22+d4/6+4*d5/33>=sum_c pi_c*M_c^+.

Together with the original AP bad-mass union inequality this gives

    rho_actual*S>=q*S+sum_c pi_c*M_c^+.            (JC16)

Only the forbidden carriers and actual S are shared. No identity
between loads A25,A4,A5, no shared internal maximizing layout and
no overlap of the AP11/13 bad events is assumed.

For a proposed survival lower bound r, put a=q-r. A sufficient
condition is the following sign-selected expression being nonnegative:

    min_c[a*D_c+M_c^+],        if a>=0,
    a*s+min_c M_c^+,          if a<0.              (JC17)

For a>=0 this follows by inserting(JC12) in(JC16); for a<0 use
S<=s. In particular, a positive r proves actual survival and
justifies subsequent conditioning divisions.

More generally suppose an existing numerator bound has the form

    N_actual<=H*S+R(theta)

and the cost target after an offset c0 is k=target-c0>=0. Here
R(theta) may contain the already proved separate signed numerator
margins; those need not be conditioned in this note. With a=q*k-H,
a sufficient fixed-target condition is

    min_c[a*D_c+k*M_c^+]-R(theta)>=0,  if a>=0,
    a*s+k*min_c M_c^+-R(theta)>=0,     if a<0.     (JC18)

Indeed the actual target margin is at least
a*S+k*sum pi*M_c^+-R(theta). The numerator's own raw-s terms remain
inside R(theta); they are not replaced by S.

The credit delta is used directly in(JC17)--(JC18). The conservative
5/9 rescaling of profile45 is not required. Keep D_c unchanged:
removing the27/81 caps from its mass bound without retaining their
actual deleted masses would not follow from this argument.

## Separate concavity and finite verification scope

For fixed c,b,c5, U25 is the previously proved complete separately
convex source expression. A_c(a) is separately affine in the five
parameter blocks. Every coefficient of a maximum in T25 is
nonnegative, so T25 is separately convex. Thus Q25 is separately
convex after its finite layout maximum, and m25 is separately
concave. Negative entries of a do not affect that affine argument.

For each full c, the fixed costs psi_t-omega_c*chi_t are independent
of theta. F_theta and P_t are separately convex; so is T2. The
finite completion maximum defining H_t^+ preserves convexity. Hence
m4,m5 are separately concave for every one of the18 carriers. Also
D_c is separately concave. All of these assertions concern the
actual formulas, not an interpolated table.

Consequently M_c^+ and its finite minimum are separately concave.
For a>=0 and k>=0 the same is true of the common-mass expressions
in(JC17)--(JC18), provided R is separately convex as in the existing
numerator interfaces. For a<0, a*s is separately affine, so the
upper-mass endpoint expressions retain that property. Checking each
fixed-target expression on the1296 product vertices therefore
extends it to the full continuous parameter domain. All other source
branches and finite-core interfaces must still be checked separately.

Every exponent tail in these expressions is complete. In particular,
the fractional-hinge selected/deep sums in(JC7), the geometric7 weights
in(JC2), and the refined27/81 subtraction in(JC14) are exact. F_theta
uses the finite-plus-geometric affine tails of profiles42--43, not
an exponent-height cutoff.

The exact evaluator and verifier for this comparison are
[joint_survival_carriers.py](../frontier/joint_survival_carriers.py) and
[verify_joint_survival_carriers.py](../frontier/verify_joint_survival_carriers.py).
Their reconstructed vertex values and target checks are distinct
from the ordinary universal proof above. A successful finite scan
does not establish the broader common-carrier numerator theorem or
close the remaining negative-Q and later-prime continuation gaps.

## Reconstructed exact comparison

The [logical certificate](../certificates/source_norms/joint_survival_carriers.json)
gives the following bounds. Displayed decimals are approximations to
the exact rational values in that certificate.

| Quantity | Bound |
| --- | ---: |
| J | at most418.63480769431646 |
| Gamma13 | at most146.82113118517492 |
| T13(81) | at most92.78830044564268 |
| K=J+T13(81) | at most510.7608632768615 |
| Actual AP45 survival | at least0.504986203460243 |

The combined K bound is optimized directly on the common source
parameters; adding the independently maximized J and T13 bounds is
weaker. The box20/current8 complete-core error is
0.0005761681583854509, leaving combined gap107.76143944501992
above403. The second complete core leaves gap107.98183507775593.
Both gaps remain positive.

The carrier combination strictly improves the sum of the three
independent survival minima at401 of the1296 vertices and leaves it
unchanged at895. Before the conditional27/81 credit, the joint
comparison gives K at most510.7803462396483. Thus the credited
result uses both changes in the proof.

The verifier reconstructs all1296 source rows from the canonical
source formulas and checks their inherited digest. It checks23328
conditional rows,46656 endpoint denominators,116640 sign-selected
target margins and233280 margins over both mass endpoints, followed
by eight fallback branches and two complete cores. An independent
positive-hinge/uncentered-tail calculation agrees on all93312
conditional values for the three uncredited margins and D_c; the
credited reconstruction adds precisely delta4 and delta5.

Run the read-only reconstruction with:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/verify_joint_survival_carriers.py --check
```

It exits zero. The source-row digest is
`06820efd31fb6fa50e72a95f52aef3c586f8355e5909dc1bdd1a93179ed7da25`;
the logical certificate digest is
`9b8b6f5bfabed669cea810b759d2d02f19e47cce1999851dcd031cfa77115a72`.
Its row blocks group the twelve late-deficit/z vertices for each
source prefix. They reconstruct one logical artifact, not separate
coverage units. This is exact arithmetic accompanying the ordinary
proof, without a Lean or whole-repository CI completion claim.
