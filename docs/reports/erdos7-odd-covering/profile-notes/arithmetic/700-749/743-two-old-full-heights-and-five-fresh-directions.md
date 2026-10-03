# Two old prime heights and five fresh directions on one actual source

For every finite family of distinct odd numerical moduli greater than1
which divide

    315*11*13*17*19^H*23^K * product_(i=1)^5 q_i^E_i,

with arbitrary finite nonnegative H,K,E_i and five distinct fresh primes
sorted at least29,31,37,41,43, the uncovered Haar density is strictly greater
than

    1691267/46368370944 > 1/30000.                         (F5.1)

All original phases are arbitrary and globally fixed. The remaining old
restrictions are v3<=2 and v5,v7,v11,v13,v17<=1 in EVERY original,
including those bearing fresh primes. This is an ordinary source-transfer
proof with two complete exact scalar certificates; it is not a new Lean
verification or a solution of unrestricted Erdős#7.

## 1. The common actual source at arbitrary19 and23 heights

Use the established six-shape actual pruned315 probability laws mu_i,
with complete-query comparison laws Y_i from the old23 result. Their
minimum survivor counts and nonunit query mean bounds are

    Nmin=(77,78,78,75,74,74),
    c=(185/86,178/85,178/85,2,157/77,157/77).

Thus mu_i<=315/Nmin_i Haar315 and every complete315 query L, including
its unit term, satisfies L<=icx Y_i. These statements hold on the same
mu_i for every query, and E Y_i=c_i+1. The earlier integer hinge table
and its nonnegative second differences define each genuine finite Y_i;
no querywise maximizing source is substituted here.

At11,13,17, use Haar conditioned away from the actual pure-prime root,
or one auxiliary root if the original is absent. At p=19 or23, first
avoid that actual or auxiliary root; within EACH other root remove all
actual pure p-power originals at their stated finite heights. The root's
remaining Haar mass is at least

    1/p-sum_(e>=2)p^(-e)=(p-2)/(p(p-1)).

Assign every such root probability1/(p-1), uniformly on its actual
remaining support. This actual probability rho_p has density cap p/(p-2)
and deterministic cylinder caps

    u_p(1)=1/(p-1),
    u_p(e)=p^(1-e)/(p-2), e>=2,
    sum_(e>=1)u_p(e)=1/(p-2).

Take the ONE product probability sigma_i of mu_i and these five pure
laws. The old carrier includes all exponents in fresh-bearing originals.
Define z=(1/10,1/12,1/16,1/17,1/21). The product has Haar density cap

    D_i=(315/Nmin_i)*(11/10)*(13/12)*(17/16)*(19/17)*(23/21).

Now restrict ONCE by all remaining actual old-only mixed originals.
For one fixed outside exponent tuple there is at most one original per315
cofactor, because original numerical labels are distinct. Singleton outside
supports have no unit cofactor after pure deletion and cost at most c_i;
larger supports cost at most c_i+1. The union debit gives actual retained
mass at least

    delta_i=c_i+2+sum z-(c_i+1)product(1+z)>0.

The six deltas are

    54557/701760,
    28793/285600,28793/285600,
    7933/57120,
    135383/1099560,135383/1099560.

On the resulting actual probability mu, which may be nonuniform,

    h_i mu<=Haar_old, h_i=delta_i/D_i,
    h_i>=hmin=763798/62292165.                            (F5.2)

The minimum is taken over paired values from the same shape. This is
measure domination, not merely a lower bound for some unrelated
survivor set. Every mixed original retains its original phase, all
finite heights are paid, and only this one actual restriction is used.

## 2. A common unbounded comparison supplies the full hinge profile

Let B11,B13,B17 be independent Bernoulli variables with parameters
1/10,1/12,1/16. Independently define N19,N23 by

    P(N_p>=e)=u_p(e), e>=1,
    Z_i=Y_i*2^(B11+B13+B17)*(1+N19)*(1+N23).

Every full old query Q on sigma_i satisfies Q<=icx Z_i. To prove this,
condition on previous coordinates and apply the convex event-increment
bound to the next coordinate's cylinders with their deterministic caps.
The nested auxiliary events replace arbitrary actual overlaps only as an
upper bound. For EACH fixed auxiliary depth, weighted Jensen reduces the
sum of possibly different query slots to scaled individual complete
queries; apply the query-uniform old comparator separately before
averaging that depth. Repeating this argument gives the displayed product.
Missing finite layers can be padded by1. Independence is imposed only
on the auxiliary comparison variables, never on actual mixed fields.

For every shape, exact low-atom enumeration verifies

    P(Z_i>8)<=delta_i<=P(Z_i>=8).

Consequently let V_i be the upper delta_i probability portion of Z_i,
with a fraction of the atom8 if necessary, normalized to mass1.
For every increasing convex phi, restriction of the actual source gives

    E_mu phi(Q)
       <=phi(8)+E(phi(Z_i)-phi(8))_+/delta_i
        =E phi(V_i).                                    (F5.3)

This follows by applying the raw comparator to the increasing convex
function (phi-phi(8))_+ and using actual restriction mass>=delta_i.
The upper-tail law is the same for every query and every convex test.
In particular

    E V_i=8+E(Z_i-8)_+/delta_i,
    E(V_i-t)_+=E V_i-t                       if t<=8,
    E(V_i-t)_+=E(Z_i-t)_+/delta_i             if t>=8.    (F5.4)

All these bounds concern the same actual source mu. The profile consumer
computes them at

    T=(1,8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384).

The first head shape dominates every listed hinge, the mean, and the
pair fee defined below, across all six shapes. Its mean is
14.550223890... and its pair-fee expectation is259.281173559... . The
machine data retain exact rational values; decimals do not carry the proof.

The two geometric auxiliary tails are included exactly. One independent
formula, useful for reproducing the profile, is the following. Write
u_p(j)=P(N_p>=j), with u_p(0)=1, and

    R_p(j)=sum_(e>j)u_p(e)
          =1/(p-2)                         if j=0,
          =(p/(p-1))*u_p(j+1)               if j>=1.

For integer a>=1,t>=0, put j=floor(t/a). Then

    E(a(1+N_p)-t)_+=(a(1+j)-t)u_p(j)+a R_p(j).

For the double product, sum over N19<floor(t/a) and use the affine
formula on its entire remaining ray, multiplying the first moment by
E(1+N23)=22/21. This terminates exactly and discards no tail.

## 3. All31 actual fresh-support fields belong to this one source

Use reference capacities r=(28,30,36,40,42), m=r-1, and kappa=1/125.
For each nonempty fresh support J and fixed positive exponent tuple e,
complete the old-cofactor query to L_(J,e), keeping every actual original
projection. Numerical-label distinctness gives at most one original per
old cofactor at that exact tuple. Define the finite convex combination

    alpha_(J,e)=product_(i in J)(q_i-1)/q_i^e_i,
    Omega_J=product_(i in J)(1-q_i^(-E_i)),
    C_J=(1-Omega_J)+sum_e alpha_(J,e)L_(J,e).              (F5.5)

If any relevant height is0, this is simply1. Thus all31 fields satisfy
C_J>=1 and the increasing-convex bound(F5.3), by Jensen, on the SAME mu.
Their actual dependence is unrestricted. They need not be bounded by384;
the finite old carrier bounds each individual instance, but there is no
height-uniform hard bound in this argument.

Set A_i=C_{i}, u_i=(r_i-A_i)_+, P=product_i u_i, and

    b_J=product_(i outside J)u_i,
    Q2=sum_(|J|=2)b_J C_J,
    H=sum_(|J|>=3)b_J C_J,
    Hbar=sum_(|J|>=3)C_J product_(i outside J)m_i,
    W=(P-Q2-H)_+.

There are5 unary fields,10 pair fields and16 higher-support fields. The
fixed coefficients in Hbar sum to11794. The actual finite-height carving
construction first restricts each fresh coordinate to its actual unary
survivor, then thins it to the allowed mass. Charging each actual mixed
cylinder on the tensor of these dominated submeasures gives fresh-fibre
Haar survivor at least W/product r. This holds pointwise in the old source.
For larger fresh primes the normalized response is nondecreasing:
where all u_i>0 it is

    product_i(1-A_i/r_i)
       *[1-sum_(|J|>=2)C_J/product_(j in J)(r_j-A_j)]_+.

Both factors are nonnegative and nondecreasing with the capacities;
continuity handles a zero u_i. No phase or source is chosen again.

## 4. A new five-variable gate has no upper field cutoff

Let g interpolate v^2 linearly at all knots T, and continue beyond384
with slope640. It is increasing and convex on[1,infinity), with final
slope256+384=640. It is already affine from256 onward. It need not bound
c^2 beyond384. For0<=s<=640 its full conjugate is exactly

    g*(s)=sup_(c>=1)(sc-g(c))=max_(v in T)(sv-v^2).

For every pair J and0<=lambda<=kappa,

    lambda b_J<=kappa*35*39*41=11193/25=447.72<640.       (F5.6)

Thus the finite knot formula for g* is valid even for unbounded C_J.

Define f_i(a)=sum_t c_(i,t)(a-t)_+/100, using the following NONZERO
columns; every omitted coefficient, including those at10,32,40, is0.

|i / t|1|8|12|16|20|24|
|---|---:|---:|---:|---:|---:|---:|
|1|3807|11613|70291|61190|0|0|
|2|0|16717|43538|67999|0|0|
|3|0|9544|17126|26966|25256|40091|
|4|1054|3672|11755|22279|4955|59499|
|5|0|4058|9732|16635|4017|60575|

Put

    Psi(u)=max_(0<=lambda<=kappa)
              [lambda P-sum_(|J|=2)g*(lambda b_J)].

The exact scalar certificates prove

    sum_i f_i(A_i)+Psi(u)>=18000 for EVERY A_i>=1.       (F5.7)

For the interior box product[1,r_i], each verifier chooses a rational
lambda per box and an affine supporting line for each convex f_i.
The resulting lower-bound function is concave in each coordinate
separately: the product terms are affine in that coordinate and negative
g* of an affine function is concave. Its minimum on a box is therefore
bounded by its32 corner values. Accepted boxes partition the full box;
integer volume and complete binary-tree counts verify exhaustive coverage.
The exterior follows from a single unary fee and the lambda0 baseline10;
the smallest exterior lower bound is1021083/50>18000.

The primary checker uses grid256, lambda grid4096 and center supporting
lines:9373 nodes,4687 leaves. The independent checker uses grid512,
lambda grid2048, left-endpoint supporting lines, a different normalized
split rule, and direct18-knot maximization of the conjugate:30605 nodes,
15303 leaves. Both cover exact box volume43820595 and all exterior points.
These are exact all-domain enclosures, not samples from the numerical fit.

Young's inequality and Hbar>=H imply

    kappa W+sum_pairs g(C_J)+kappa Hbar>=Psi(u).

Indeed H+W>=P-Q2 and lambda<=kappa, so the right-hand dual value is
bounded by the left-hand expression for each lambda. Combining(F5.7)
gives the full31-field pointwise inequality

    kappa W+F(C)>=18000,
    F(C)=sum_i f_i(C_i)+sum_pairs g(C_J)+kappa Hbar.      (F5.8)

## 5. The same-source budget is below16791

Every penalty in(F5.8) is an increasing convex function or a positive
linear function of a field. Apply(F5.3) to each field separately, and
then use the first-shape profile's simultaneous domination. No joint
maximizer or field independence is required. The common source fee is
at most

    sum_i E f_i(V_1)+10 E g(V_1)+(11794/125) E V_1
       =16790.222130747847... <16791.                   (F5.9)

The exact rational value appears in the retained result and agrees with
the independent profile calculation. Each unary coefficient is nonnegative; g is a constant
plus positive hinge increments at the listed knots; the mean coefficient
is positive. Therefore the checked profile domination suffices for all
six actual source shapes. All16 high-support fields and every geometric
exponent tail in(F5.5) have been charged.

Integration of(F5.8), exact carving, and(F5.2) now give

    E_mu W>(18000-16791)/kappa=1209*125,
    Haar(full survivors)
       >=hmin E_mu W/product r
       >hmin*1209*125/(28*30*36*40*42)
        =1691267/46368370944>1/30000.

This proves(F5.1) with a strict conservative bound. The density comparison
uses one actual supported law, not a separate best law per field.

## Exact consumer and remaining scope

The [old-height source invariant](742-a-common-source-for-subsets-of-five-old-prime-heights.md)
constructs the common actual source. The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old19_old23_five_fresh.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old19_old23_five_fresh.json)
pin and replay its source arithmetic, compute the entire double-tail
hinge profile, compare all six source costs, and check the whole primary
continuous domain and exterior. Fixed coefficients are retained in the
consumer and emitted in the result. With no output argument, any stale
retained result is rejected.

An independent survival-sum calculation reproduces every listed hinge,
the mean and chord expectation, and each shape's complete source fee.
The independent domain certificate uses different spatial/dual grids,
left-endpoint supporting lines, direct conjugate maxima and normalized
splits. Both exact domain checks cover the full volume described above.
The consumer inherits the head D2 geometry and ordinary source/carving
proofs; it does not claim Lean verification.

The gate18000 and the common-source fee are both needed. The remaining
3/5/7/11/13/17 exponent restrictions and five-fresh support restriction
have not been removed. No optimal-source or optimal-gate claim is made.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old19_old23_five_fresh.py
```
