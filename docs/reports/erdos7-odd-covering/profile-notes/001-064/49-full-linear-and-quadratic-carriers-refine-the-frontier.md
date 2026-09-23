[Index](../../marked_head_profile.md) · [Common survival carrier](46-one-forbidden-carrier-mixture-strengthens-survival.md) · [Six linear carriers](47-six-linear-tests-share-the-survival-carrier.md)

# Full linear and quadratic carriers refine the frontier

The same forbidden-carrier mixture controls all41 linear numerator
costs, all five exceptional quadratic costs and the three survival
hinges, while each original test retains its own source layouts.
Evaluating the full conditional costs at24 vertices, and retaining
the proved profile47 lower bounds at the other1272, gives

    J=417.70065740152455...,
    K=509.8267129840696....

Both improve47 by0.3517899718425943.... The source-square complement
and every comparison barrier remain unchanged. The two complete-core
gaps remain positive, so the strict negative-Q endpoint and
unrestricted Erdős #7 remain open.

Sections1--6 establish the required five-quadratic payment and
conditional margins by ordinary mathematics. Section7 identifies the
globally defined separately concave functions behind the mixed vertex
table. Section8 gives the exact targets, both gain stages and the
full set of remaining controls. No actual-source feasibility cut or
Lean verification is asserted.

## 1. Costs, barriers and actual signed deficits

Let i range over the original AP tuples

    I={(0,0),(0,1),(0,2),(1,0),(2,0)}.

For h(v)=(v^2-16)_+ and the complete auxiliary AP11/AP13 count law
N=N11*N13 of profile35, define

    f_i(v)=E[1_(N11>e,N13>f)*(h(N*v)-h(N))/N], i=(e,f).

The actual test load A_i is not this auxiliary random variable: f_i
is an increasing convex cost applied to each test's independently
labelled complete original357 load. Its selected zero7 source cost is

    psi_i(v)=sum_(n>=1)(p7_n/n)*[f_i(n*v)-f_i(n)],
    p7_1=29/35, p7_n=36/(5*7^n) for n>=2,
    sum_n p7_n=1, sum_n n*p7_n=6/5.

Use exactly the fixed profile38/39 barriers:

|Tuple|C_i|
|---|---|
|(0,0)|1843590625606784/50362520583375|
|(0,1)|51437677469/4932968040|
|(0,2)|868964699/704709720|
|(1,0)|197160180946/16688172501|
|(2,0)|3930317668/2384024643|

Each satisfies C_i>f_i(3)+3*Delta f_i(3). These constants are fixed
on the whole continuous parameter domain and do not depend on a
test layout, carrier, vertex or final target.

Use the actual raw measures eta,Lambda and lambda, the five-cell
data eta_l,n_l,d_l, and the actual mass S=s*M(V) from profile46.
In particular Lambda<=eta tensor raw-pure5, d lambda/d eta<=d_l,
d_l>=1/4, s>=1/4 and sum eta_l<=5/9. Define

    d_i=C_i*S-s*E_M[f_i(A_i)*1_V].                 (Q1)

This is the signed raw deficit of that original test. It is not
required to be positive in order to combine the inequalities below.

## 2. The selected source pays6/5 copies of each event weight

For g_T(v)=(v^2-T)_+, n>=1 and integer v>=1,

    g_T(n(v+1))-g_T(nv)
      =n^2*[g_(T/n^2)(v+1)-g_(T/n^2)(v)]
      >=n^2*[g_T(v+1)-g_T(v)].

For fixed ordered squared endpoints x<y, the difference
(y-T)_+-(x-T)_+ is nonincreasing in T, proving the inequality.
Positive dilations, nonnegative mixtures and additive constants
preserve it. Every f_i has this form. Therefore

    Delta psi_i(v)>=alpha*Delta f_i(v), alpha=6/5. (Q2)

The equality sum n*p7_n=6/5 includes the entire original7 tail.
Here the outside coefficient of the selected psi_i source is1.
The6/5 factor arises from its increments in(Q2), so multiplying the
source envelope by6/5 again would be incorrect.

Fix the original independent zero5 and first-positive5 shallow
layouts b,c5 in BASES, and put

    v_l=Delta f_i(b_l), k_l=C_i-f_i(b_l), t_l=c5_l*v_l.

The three original test events5,15,45 have their own mod5 residues;
their ternary supports are respectively the whole carrier, c5's
root and c5's cell. For their active count N one has

    0<=N<=c5_l,
    (C_i-f_i(A_i))_+<=k_l-v_l*N,
    k_l-v_l*N>=0, 0<=t_l<=k_l.                    (Q3)

For one selected event with ternary support Dtest, full35 event
Itest and actual raw pure5 mass h<=1/5, define positive measures

    K(E)=integral_eta v*1_(Dtest intersect E),
    R(E)=h*K(E)-integral_Lambda v*1_(Itest intersect E)>=0.

The actual source enlargement and restoration of the selected5 cap
pay at least

    alpha*[(1/5-h)*K(Omega)+R(Omega)]               (Q4)

once for this event. Inequality(Q2) supplies the weight. The
corresponding statement for the three events is their sum, with
each event's own h and R; their residues need not coincide.

The existing curvature correction can be retained simultaneously
with(Q4). The order of the source argument is: enlarge the actual
positive5 increment to its pure product while retaining its loss;
restore the selected caps while retaining their loss; then bound
the full restored-cap source by Jensen. The n=2 Jensen step for
psi_i subtracts its established integer-curvature loss. It is a
loss in this last comparison, not another use of the removed-event
loss R or the cap-shrink loss in(Q4). The same actual b,c5 layouts
are kept in both terms until after source and deletion are added.

## 3. Six-cofactor payment before any signed maximization

At every positive original7 depth retain the six actual deleted
pure3 cylinders of depths1,...,6. Their physical cap coefficients
are u_e=6/(5*7^e), sum u_e=1/5. Thus their total multiplicity cap is
6*sum u_e=6/5=alpha. Apply the cap enlargement to the nonnegative
floor in(Q3), before expanding it into signed terms.

For a fixed selected test event let B=sum_lambda u_lambda*K(E_lambda),
where lambda runs over these six cofactors at all7 depths. Then

    B<=alpha*K(Omega),
    sum_lambda u_lambda*R(E_lambda)<=alpha*R(Omega).

Combining deletion with its source payment(Q4) gives

    -h*B+sum_lambda u_lambda*R(E_lambda)
       -alpha*[(1/5-h)*K(Omega)+R(Omega)]
      <=-h*B-(1/5-h)*B=-B/5.                      (Q5)

Apply this separately to the three selected events and add. The
selected-cylinder contribution becomes

    integral_E k d lambda-integral_E(t/5) d eta.  (Q6)

Each event budget is used exactly once. Different quadratic tests
use their own source comparisons and their own budgets; summing
their inequalities with positive coefficients introduces no further
payment. The forbidden carriers are what the inequalities share.

## 4. Exact conditional formulas and empty carriers

For a forbidden shallow carrier c=(r,j), with r in{empty,0,1}
and j in{empty,0,1,2,3,4}, set

    a_l=k_l*n_l-t_l*eta_l/5,
    z_l=k_l*d_l-t_l/5,
    w_l=9*eta_l*k_l,
    A_c(a)=1_(r!=empty)*sum_(ROOT(l)=r)a_l
                                +1_(j!=empty)*a_j.

The depth1 and depth2 terms of(Q6) are retained exactly in A_c,
with their signs. Empty components contribute zero; no nonempty
completion or clipping of a_l is used. For the four remaining
selected pure3 depths3,...,6 use the existing nonnegative cap z_l.
The complete remaining expression is

    T_i(k,t)=(40/729)*max(z)+(1/1458)*max(k*d)
                +(sum(w)+R(w)+max(w))/36+max(k)/72. (Q7)

Here40/729=sum_(a=3..6)3^-a,1/1458=sum_(a>=7)3^-a, and their sum
is1/18. The positive5 cofactor terms remain unchanged and use no
extra selected-event payment. Every term in A_c+T_i still receives
the outer complete7 factor1/5.

For clarity, the complete fixed-layout source in the implementation is

    U_i(theta;b,c5)=P7_i(theta)+B_i(theta;b)+P5_i(theta;c5)
                                      -(4/25)*mu_i*d_eta(b,c5),

where P7_i is the unchanged positive original7 complement, mu_i is
the established integer curvature of psi_i, and

    B_i(theta;b)=sum_l[n_l*psi_i(b_l)+eta_l*barpsi_i(b_l)]
          +max_l sum_(a>=3)3^-a*
                          Delta(d_l*psi_i+barpsi_i)(b_l+a-3),
    barpsi_i(v)=sum_(n>=2)(p5_n/n)*[psi_i(nv)-psi_i(n)]-psi_i(v)/5,
    p5_n=4/5^n.

The retained positive5 term is

    P5_i(c5)=sum_(n>=2)(p5_n/n)*[
          R_n(c5)-psi_i(n)*x+(n-2)*(R_n-psi_i(n)*x)]
                  +x*sum_(n>=2)p5_n*psi_i(n),
    x=sum eta_l, R_n=max_c5 R_n(c5).

R_n(c5) is the complete pure3 envelope for psi_i(n*B1) at that
test's first-positive5 layout. If psi_i(v)=a_i*v^2+z_i for v>=h,
its whole tail in the first sum is

    a_i*T1*(M_c5-x)+a_i*(T2-2*T1)*(max_c5 M_c5-x),
    Tj=sum_(n>=h)p5_n*n^j,

with M_c5 the complete pure3 square envelope. No tail is truncated.
For delta_l=b_l-c5_l the fixed-layout distance lower bound is

    d_eta(b,c5)=sum_l eta_l*delta_l^2
       -[max(0,max_l delta_l)^2+max(0,max_l(-delta_l))^2]/18.

Define the requested conditional margin

    m_i(theta;c)=C_i*s-max_(b,c5)[U_i(theta;b,c5)
                                          +(A_c(a)+T_i(k,t))/5]. (Q8)

For the actual common carrier mixture

    pi_c=5*sum_e u_e*1_(c_e=c), sum_c pi_c=1,

the pre-maximization bound from(Q5)--(Q7) is

    d_i>=C_i*s-U_i-T_i/5-sum_e u_e*A_(c_e)(a).

Substitute pi, then take the layout maximum separately for each
carrier in the upper comparison. This proves

    d_i>=sum_c pi_c*m_i(theta;c)                    (Q9)

for all five i simultaneously with the profile46 survival and
source-mass inequalities. The same pi handles partial and empty
actual forbidden carriers, including padded absent7 depths.

## 5. The old margins are recovered exactly

The strict global floor C_i>f_i(3)+3*Delta f_i(3) supplies all
necessary sign conditions. Put v_*=Delta f_i(3). Then

    min k_l>=C_i-f_i(3)>3*v_*, max t_l<=3*v_*,
    min z_l>0,
    sum_l a_l>3*v_*[s-sum(eta)/5]>=0.

The final strict inequality also follows when v_*=0 from the strict
floor and s>0. Thus at least one root sum and one cell entry are
positive, and the existing unconditioned cap with no explicit zero
branches agrees with the18-carrier maximum:

    max_c A_c(a)=R(a)+max(a).

Therefore the existing true three-event margin u_i of profile38/39 is

    u_i(theta)=min_c m_i(theta;c).                  (Q10)

The carrier and layout maxima commute; no min-max exchange of
different orders is involved. In particular m_i(theta;c)>=u_i(theta)
for every carrier. If a stored value ell_i(v) is only a certified
lower bound for u_i(v), it remains a safe conditional lower bound.

For a later nonnegative barrier increase delta, the source and t do
not change and the complete cap satisfies

    W(k+delta*1,t)<=W(k,t)+delta*W(1,0),
    W(1,0)=5*(s-D).

Consequently the new conditional margin obeys

    m_(i,C_i+delta)(theta;c)>=u_i(theta)+delta*D.   (Q11)

Keeping the unweighted shallow carrier before the final maximum
actually gives the sharper comparison

    m_(i,C_i+delta)(theta;c)>=m_i(theta;c)+delta*D_c,

because its unweighted cap is5*(s-D_c). Since D_c>=D and
m_i(theta;c)>=u_i(theta), this also implies(Q11). The source and
correction t must be unchanged for this barrier comparison.

The older AP norms preceding profile38 have larger barriers. Their
constants cannot be inserted into(Q10) as if they were the current
C_i. The nonnegative-increase lemma(Q11) cannot be reversed to get
a lower bound for a reduced barrier. If such an earlier comparison
is reused, a safe crude reduction is at most the barrier decrease
times s, assuming both floors remain admissible and the retained
source/event comparison improves the earlier one. The current
five-direction extension needs no such reduction: it uses precisely
the existing profile38/39 barriers and margins.

## 6. True separate concavity and safe aggregate replacement

For fixed b,c5,c, A_c(a) is separately affine in the source parameter
blocks and T_i is separately convex. B_i is separately convex by
the joint actual/pure source calculation and complete deep maximum.
P5_i is a positive sum of separately convex envelopes plus affine
centering; its exact quadratic-tail coefficients are nonnegative.
The distance d_eta is affine for fixed layouts. The positive7
complement is separately convex by its original positive sum of
independent source envelopes; writing it as a difference of source
values in software is not the convexity argument.

Thus the fixed-layout expression in(Q8) is separately convex. Its
finite maximum is convex in each parameter block, so each m_i(c)
is separately concave. The finite minimum(Q10) is also separately
concave. Nonnegative weighted combinations with the same c, followed
by one carrier minimum, preserve this property. This concerns the
true formulas, not a numerically patched vertex table.

The existing quadratic numerator remainder has the form

    Mq=sum_i u_i+oQ*mg, oQ>=0.

Leave the source-square margin mg unconditional unless separately
proved otherwise, and define

    Mq_c=sum_i m_i(c)+oQ*mg.                       (Q12)

The actual quadratic deficits are bounded below by sum pi*Mq_c:
use(Q9) for the five exceptional tests and distribute the already
valid unconditional square bound over pi. The source-square
comparison barrier, H16 and its complementary tuple coefficients
remain those of the existing consumer.

At a vertex where the stored Mq contains the exact five u_i, the
safe substitution is

    Mq_c_lower=Mq_stored-sum_i u_i+sum_i m_i(c).    (Q13)

Any other stored lower bounds in Mq remain untouched. More generally,
subtract the exact five contributions actually included in that
stored aggregate, not an older or weaker version of them. For
example, if Mq_stored=A_lower+sum_i u_i, subtracting ell_i<u_i and
adding m_i(c) would count sum_i(u_i-ell_i) twice.

The final J or combined target uses its original nonnegative
quadratic coefficient AC; the Gamma target uses coefficient1.
These can be combined with profile46's survival and mass terms and
the six-linear conditional terms already proved. The existing
sign-selected S endpoint and positive-survival checks still apply.
Only checks of the resulting fixed targets over their required
vertices, branches and core interfaces can supply new numerical
bounds. The conditional theorem itself supplies no such scan result.

## 7. One global comparison with24 refined vertex lower bounds

Use the fixed globally charged linear barriers and original independent
source layouts of profile47. For every one of the41 costs let m_i(c)
be the genuine conditional margin from47(L4), and u_i=min_c m_i(c).
The proof of47(L5) applies to all41 costs. The only restriction to six
there was which conditional tables were evaluated. Thus, with the same
actual carrier mixture pi as the survival and source-mass inequalities,

    sum_i w_i*d_i >= sum_c pi_c*G_full(theta;c),
    G_full(theta;c)=sum_(i=1..41) w_i*m_i(theta;c).

The complete weights w_i are positive. Every m_i(c) is separately
concave. Therefore G_full is separately concave for each fixed c.

The global function behind profile47 is

    G_47(theta;c)=sum_(i in Six) w_i*m_i(theta;c)
                       +sum_(i outside Six) w_i*u_i(theta).

Since m_i(c)>=u_i, one has G_full>=G_47 for every parameter and
carrier. In addition47(L9) gives m_i(c)>=old_i+DeltaC_i*D. These
facts validate retaining the complete old47 lower bound at any vertex
where the other35 true conditional margins are not evaluated.

Let E consist exactly of the24 vertices

    398,402,404,406,410,414,416,418,422,426,428,430,
    616,618,620,622,628,630,632,634,640,642,644,646.

At E evaluate all41 actual conditional margins, retaining each
original test's own100 baseline/first-positive5 layout pairs. At the
other1272 vertices retain the old47 conditional table. Every resulting
entry is a lower bound for the one globally defined G_full. The
patched table is not asserted to be concave: separate concavity of
G_full is what justifies extending fixed-target vertex checks.

For the five exceptional quadratic costs, use Q9/Q10 established above.
The global quadratic aggregate is

    Q_full(theta;c)=sum_(j=1..5) m_j^Q(theta;c)+oQ*m_g(theta),

where m_g is the existing independent source-square margin and oQ>=0.
Its actual deficit is at least sum_c pi_c*Q_full(theta;c); for fixed c
this is separately concave. At E evaluate the five true conditional
margins and retain the old source-square lower bound. Elsewhere keep
the complete old Mquad, a valid lower bound by m_j^Q(c)>=u_j^Q.
The true five independent margins included in every evaluated old
aggregate are recovered exactly, then subtracted before replacement.
No source-square conditioned theorem or new barrier is used.

The same actual mass S obeys S>=sum pi_c*D_c and S<=s. The already
credited survival bound is rho_actual*S>=q*S+sum pi_c*M_c^+.
For the J target the conditional correction is AC*Q_full+G_full;
for Gamma13 it is Q_full; for T81 it stays cG*m_g-R81; for the
combined target it is AC*Q_full+G_full+cG*m_g-R81. The source slopes
H16,H41,A81 and all fixed barriers are unchanged. Apply the exact
sign-selected mass endpoint argument47(L14) to each target. The
nonnegative factors AC and target offsets preserve separate concavity.

## 8. Exact targets and the remaining controls

This produces two comparisons, tested over all1296vertices and18
carriers. Each keeps both actual-mass endpoints, giving233280target
endpoint checks and46656positive denominator checks. Eight fallback
branches and two complete cores are recomputed for each comparison.

    comparison                  J                   K
    profile47                   418.052447373367     510.178502955912
    full41 at24, old quadratic   417.700657401525     510.033589563087
    full41+five quadratic at24   417.700657401525     509.826712984070

The exact final targets are

    J=32591696604416043922570546637202187327127
      /78026443164264664967078568539321769600,
    K=85328025019970695504683045091497055540870007
      /167366720587347706354383529516845195792000.

Relative to47, J and final K improve by0.3517899718425943....
The linear-only K improvement is0.14491339282529858...; adding the
five quadratic carriers then improves K by0.2068765790172957....
Quadratic conditioning alone could not improve47 because its402/A
witness remained unchanged. Refining the other35 linear costs first
moves the K obstruction to398; quadratic conditioning then removes
that obstruction. This explains why the joint refinement helps while
the isolated quadratic step did not.

The linear-only K controls are exactly

    398,410,422 at carrier(1,1),
    616,628,640 at carrier(1,0),

all at D_c. With the five quadratic costs included, the exact K
controls are

    402,404,406,414,416,418,426,428,430 at carrier(0,1),
    618,620,622,630,632,634,642,644,646 at carrier(0,0),

again all at D_c. Every one of the24 refined vertices was evaluated
individually. Equality of these final relaxed bounds is not a claim
that the source parameters have identical actual realizations.

Gamma13, T81 and rho remain exactly equal to47. The two final
complete-core gaps K+error-403 are106.827289152228... and
107.04768478496403.... They remain positive; this is not a proof of
the strict negative-Q condition or unrestricted Erdős #7.

The evaluator
[full_linear_carrier_frontier.py](../../frontier/source-budgets/full_linear_carrier_frontier.py)
and its
[verifier](../../frontier/source-budgets/verify_full_linear_carrier_frontier.py)
reconstruct all39 source rows, the46 survival margins and the47
linear lower bounds, then evaluate the24 frontier rows. Each of the
46 original tests retains its own100 source-layout pairs and18
forbidden carriers. The other1272 entries retain their already
proved47 lower bounds. Original costs and complete affine/quadratic
source tails use the pinned existing source evaluator; no temporary
cache is a canonical input.

The preceding47 targets are independently recovered during the new
consumer calculation. The new targets are checked at both actual-mass
endpoints, with the correct sign-selected endpoint also recorded.
These finite calculations verify the numerical premises of the
ordinary universal argument, not a claim of Lean verification.

No actual-source feasibility cut is used. In particular404 and406
remain controls. No claim that any relaxed maximizing row is an
attained actual covering family is needed or supplied by this
argument. The unchanged constant-barrier stopping bound of profile44
still applies to its specified older independent numerator family;
this carrier refinement changes that comparison family.
