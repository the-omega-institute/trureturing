# Linear schedule credits fail on an actual irredundant core

A finite family of forty actual distinct odd moduli separates a supported
query law from a proposed correlated-replacement certificate. The complete
normalized-Haar survivor law has all-height nonunit query norm below4.
Nevertheless every certificate of the linear fractional-schedule form
specified below exceeds16079/768>566/49, even if its exterior leakage is
replaced by zero and its descendant routing is optimized arbitrarily.

The family lies outside the coarse reciprocal-Haar sufficient regime:
its survivor mass h is less than A/(566/49), where A is the entire
seven-prime reciprocal mass. Every original has a private witness, so
passing to a survivor-equivalent subfamily cannot remove the obstruction.

This excludes a specific method of converting correlated replacement
schedules to unweighted query bounds. It does not exclude nonlinear
inside-survival bounds, credits restricted to actual query incidences,
other supported laws, or unrestricted Erdős#7. The existing Gibbs and
fixed-cardinality results of Reports530--532 remain unchanged. This is
ordinary mathematics with exact finite counts and complete Euler tails,
not new Lean verification.

## 1. One actual family and one actual law

Put P={3,5,7,11,13,17,19} and L=product P=4849845. The original pairs
(d,a_d) are as follows; each denotes the one globally fixed class a_d mod d.

|d|a_d|d|a_d|d|a_d|d|a_d|
|---:|---:|---:|---:|---:|---:|---:|---:|
|3|0|35|3|105|13|247|6|
|5|0|39|2|119|5|255|7|
|7|0|51|1|133|5|273|11|
|11|0|55|4|143|3|285|34|
|13|0|57|1|165|19|323|3|
|15|1|65|7|187|6|357|41|
|17|0|77|1|195|22|385|43|
|19|0|85|2|209|7|399|20|
|21|2|91|4|221|8|429|5|
|33|2|95|4|231|8|455|53|

Let M be this forty-label inventory, U its entire survivor, and H the
product Haar probability on the seven adic coordinates. The retained
[input](../../frontier/cover-geometry/linear_schedule_credit_obstruction_input.json)
contains one literal private witness for every original. Each witness lies
in its own class and none of the other39. Hence every survivor-equivalent
subfamily B subset M is M itself. No alternate subfamily choice reduces
its number of occupied labels.

Exact marking of all L residues gives

    |U mod L|=741126,
    h=H(U)=247042/1616615,
    3/20<h<A/(566/49)<A/(565/51),                 (SC1)
    A=product_(p in P)p/(p-1)-1=212731/110592.

Every original modulus is odd, nonunit and distinct. The marked set is
the complete original survivor, not a chosen subset. All probability
claims below use rho=H(.|U), with the same uniform higher digits.

The known uniform seven-prime lower bound is

    alpha7=7235955529/6075000000000<1/800.         (SC2)

It is the constant used for legal-family replacement estimates in
[Report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md).
The obstruction below fixes this constant. It does not exclude a different
method that proves a larger lower bound simultaneously for all of its
actual replacement families.

## 2. The selected-law free energy retains every query height

For any L-cell probability nu supported on U, extend its higher digits
by independent Haar tails. Write

    q_e(nu)=max_(a mod e)nu([a]_e),
    R_unused(nu)=sum_(nonunit P-smooth e notin M)q_e(nu).

For g|L, put b_g=product_(p|g)p/(p-1). Since L is squarefree, every
nonunit query e has g=gcd(e,L)>1 and

    q_e(nu)=(g/e)q_g(nu),
    sum_(e:gcd(e,L)=g)g/e=b_g.                   (SC3)

Thus there are exact nonnegative finite coefficients

    a_1=0,
    a_g=b_g-1_(g in M) for g>1,
    R_unused(nu)=sum_(g|L)a_g q_g(nu).           (SC4)

No height cutoff has entered this identity. Every unused original label
and every higher prime-power query remains in the Euler sum.

For any vector0<=c<=a define, with natural logarithms,

    F(c)=min_(nu supported on U)
             [D(nu||rho)+sum_(g|L)c_g q_g(nu)],
    Z_c=h exp(-F(c)).                            (SC5)

This is a finite simplex minimization. Its minimum exists; entropy is
strictly convex, so its minimizer mu_c is unique. Here rho is positive
on every actual survivor cell. A supporting phase dual gives the usual
Gibbs expression on U if required, but the obstruction needs only SC5.

Entropy and all coefficients are nonnegative. Monotonicity in c and
the competitor nu=rho give

    0<=F(c)<=F(a)<=R_unused(rho)
      <=[A-sum_(d in M)1/d]/h
       =99943555709/27320868864<4.                (SC6)

The last inequality uses q_e(rho)<=1/(e h) and sums every unused
numerical label. In particular it holds before selecting any descendant
flow, maximizing query phases, or replacement schedule.

A capacity-diversion construction has c_g=a_g-g r_g with0<=g r_g<=a_g.
It is included in SC6. Its free-energy estimate for the unused cost is

    U_c=F(c)+(a-c).q(mu_c)>=0.                    (SC7)

Equivalently U_c=F(a)+B_F(a,c), where
B_F(a,c)=F(c)-F(a)+(a-c).q(mu_c). Improving the curvature estimate for
this term cannot remove the lower bound below; only its nonnegativity
will be used.

## 3. The precise linear schedule contract

For each occupied label d choose one maximizing query cylinder J_d of
mu_c. A schedule pi is a probability on subsets T of M: replace precisely
the original classes with labels in T by their J_d, retaining all other
originals. Each outcome still uses one globally fixed phase per numerical
label.

One proposed linear credit vector w has nonnegative entries and satisfies

    sum_(d in S)w_d<=Pr_pi(T intersects S)
       for every S subset M.                   (SC8)

This is a sufficient inside-survivor condition: at an actual x in U,
apply SC8 to I(x)={d:x in J_d}. It bounds the probability that replacement
removes x from below by sum_d w_d 1_(J_d)(x).

Legal-family averaging with an all-height unused-label potential can
then give a bound of the form

    w.q_M(mu_c)<=1-(alpha7-Lambda)/Z_c,           (SC9)

where Lambda>=0 is the exterior leakage computed under that same law,
fixed dual, actual original phases and any shared descendant flow.
The theorem below grants any nonnegative Lambda. It therefore does not
need to assume that separately optimized exterior flows can be combined.

For finitely many schedules choose lambda_j>=0 and credit vectors w^j
such that every occupied label is paid:

    sum_j lambda_j w^j_d>=1 for every d in M.     (SC10)

The resulting proposed complete numerical query certificate is

    C=U_c+sum_j lambda_j[1-(alpha7-Lambda_j)/Z_c], (SC11)

with the same c,mu_c and Z_c in every term. Any nonnegative replacement
for U_c is allowed by the lower-bound argument. The method includes
arbitrary correlated schedules and arbitrary common descendant routing;
it requires SC8's inequalities for all subsets, not merely the incidence
sets actually realized by the selected J_d on U.

## 4. Every such certificate fails, uniformly over its choices

Take S=M in SC8. Each schedule has

    sum_d w^j_d<=Pr_pi_j(T is nonempty)<=1.

Summing SC10 over the forty distinct original labels yields

    40<=sum_j lambda_j sum_d w^j_d<=sum_j lambda_j. (SC12)

This loss comes from the global credit constraint. Suppressing exterior
coverage cells, retaining all original phases and increasing the quality
of a descendant-flow solver cannot alter SC12.

For an elementary entire-series bound,

    exp(1)<=1+1+1/2+(1/6)sum_(k>=0)4^-k
          =49/18<11/4.

Indeed every successive factorial ratio after3! is at least4. Together
with SC1, SC2 and SC6 this gives

    alpha7/Z_c=alpha7 exp(F(c))/h
      <(1/800)(11/4)^4/(3/20)
       =14641/30720<1.                           (SC13)

Since each Lambda_j>=0, SC7 and SC11--SC13 prove

    C>40(1-14641/30720)
      =16079/768>566/49.                         (SC14)

This covers every permitted c, law selected by SC5, supporting dual,
fixed replacement cylinder choice, schedule collection, fractional cover
and descendant flow. No numerical minimizer of F, leakage optimizer or
phase sample was used. In fact the conclusion already holds with zero
exterior leakage and zero unused-cost payment, strictly more favorable
than the proposed actual certificate.

The private witnesses in Section1 prevent a survivor-equivalent actual
subfamily from evading the forty-label count. SC14 is a method obstruction,
not a lower bound for R_P(mu_c) or for all probabilities on U.

## 5. The same actual survivor has a small all-height query law

The obstruction is not caused by a large optimal query norm. For the
one actual law rho, the producer calculates every residue count at the
forty gcd labels g in M. Let

    m_g=max_(a mod g)|{x in U mod L:x=a mod g}|.

Retain SC3 for all other gcd labels. Then

    R_P(rho)
      =sum_(g|L,g>1)b_g q_g(rho)
      <=sum_(g in M)b_g m_g/741126
         +(1/h)[A-sum_(g in M)b_g/g]
       =1506044247059/409813032960<4.             (SC15)

For an omitted gcd label, q_g(rho)<=1/(g h). The coefficient identity
sum_(g|L,g>1)b_g/g=A supplies the exact entire remainder. This pays every
query height, including every occupied query phase; it does not count
only a finite list of tested residues.

Thus one full-survivor law already lies far below both566/49 and565/51,
while every numerical certificate SC11 lies above16079/768. The simple
reciprocal estimate A/h alone would not cross either threshold, by SC1.
The actual cylinder incidences are useful information even in this small
literal family.

## 6. What must change before pursuing this route further

The obstruction is different from the exponential replacement-budget
exclusions in
[Report532](532-fixed-quota-and-reciprocal-payment-obstructions.md).
It applies to the all-subset linear credit rule SC8, irrespective of
nonnegative phase-sensitive exterior leakage. It leaves the weighted
Gibbs results and their nonlinear inside-survival estimates intact.

There is a strictly more faithful sufficient credit condition. Instead
of imposing SC8 at every abstract subset S, require only

    sum_(d in I(x))w_d<=Pr_pi(T intersects I(x))
       for every actual x in U,                 (SC16)
    I(x)={d:x in the one fixed maximizing J_d}.

The same inside-survivor integration still proves its linear query
credit. SC16 need not force sum_d w_d<=1 if the full incidence M is
never realized. It therefore avoids the specific count argument SC12.
This observation does not prove that the repaired certificate crosses
the target: its actual incidence constraints, source selection, exterior
leakage and common flow must still be controlled together. Alternatively
one may retain a nonlinear inside-survival bound rather than replace it
by SC8. Neither repair is a resolution of the unrestricted problem.

## 7. Reproducibility

The standard-library
[producer](../../frontier/cover-geometry/linear_schedule_credit_obstruction.py)
and [data](../../frontier/cover-geometry/linear_schedule_credit_obstruction.json)
verify174 named checks through1773 evaluations, including all1600
private-witness/class comparisons, the full4849845-point survivor count,
all40 complete residue partitions, exact Euler remainders and the strict
method-versus-actual-law separation. Failure branches remain active under-O.
The literal input fixes the actual family; no exploratory search or
floating optimizer is required to reproduce the result.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/linear_schedule_credit_obstruction.py

The finite producer verifies the instance and exact constants. Sections2--5
supply the uniformity over certificate choices and all query heights.
