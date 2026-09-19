[Index](../../marked_head_profile.md) · [Complete J heads](219-one-late-source-split-controls-complete-saturated-j-heads.md) · [Complete J moments](241-one-original-j-head-controls-complete-square-and-factorial-moments.md) · [Complete survival and linear heads](242-the-complete-j-survival-and-linear-heads-retain-one-late-split.md)

# All original J costs have exact moment envelopes and a method boundary

The complete original52-cost comparison on both saturated actual J
faces satisfies

    comparison <= 447.557978209946065... .            (JM1)

This retains all original independent tests, the signed actual
survivor mass, the outside whole-square payment, all four AP11
blocks, the independent AP13 term and both infinite tails.
All numerical upper inputs are J results219,241,242. The older
comparison226 supplies only the unchanged original functions,
weights and comparison formula; none of its K-domain numerical
upper bounds is a J input.

The same rational certificate establishes a limitation of the
present independent scalar-moment method. If each original test
is bounded separately using the22 constraints below, its best
possible complete comparison lies in

    [447.557978209902653..., 447.557978209946065...].  (JM2)

The interval width is less than10^-10. In particular this fixed
method cannot cross403. Its lower witnesses are abstract load
measures, not actual source configurations or covering families.
A method retaining additional joint source constraints is not
subject to this lower bound.

## 1. One entire J domain and22 moment constraints

All inputs use219's identical geometry record: raw source mass1/4,
survivor mass S=3/20, both saturated actual J faces, and one common
late split theta in[1/135,1/90]. Every original test has its own
admissible positive integer load A. A bound uniform over all such
tests may be applied to each independently; their loads are not
identified with one another.

For a load distribution mu on the positive integers write

    <f,mu> = sum_(n>=1) f(n)*mu(n).

The first five basis functions and bounds are

| Function | Bound |
| --- | ---: |
|1|S=3/20, exactly|
|n|16/25|
|n^2|371/80|
|Phi5(n)=(n-5)_+*(n-4)/2|6353/7200|
|H4(n)=(n-4)_+|29483/147000|

Add219's original cost functions0 and16,242's four complete AP11
block functions, and242's eleven original linear-tail functions
at indices1,2,7,10,17,18,23,26,32,33,36. This gives22 functions
b_j and bounds B_j. Their original all-load identities, common
geometry, source hashes and signs are checked before consumption.
The inherited scans retain their complete containing-choice
families and omitted-label tails.

Let M be the relaxation consisting of all nonnegative measures
mu on the positive integers with

    <1,mu>=S,  <b_j,mu><=B_j for j!=mass.            (JM3)

Every actual admissible J load distribution belongs to M. The
reverse inclusion is not asserted. In particular independent
members of M need not arise from one common actual source.

## 2. Rational majorants cover every positive integer

For each original cost and each of the seven outside targets
(four AP11 blocks, H4, mean and square), the certificate retains
coefficients y_j satisfying

    f(n) <= sum_j y_j*b_j(n) for every integer n>=1,
    y_j>=0 for j!=mass.                              (JM4)

The coefficient of exact mass is free in sign. Integrating gives

    <f,mu> <= sum_j y_j*B_j =: U_f.                 (JM5)

Each basis and target has a known affine or quadratic polynomial
continuation from n=9. The checker verifies n=1,...,8 directly and
checks the entire continuation of the gap

    q(n)=a*n^2+b*n+c.

If a=0, it requires b>=0 and q(9)>=0. If a>0, its minimum on
integers n>=9 occurs at9 or at the two integers adjacent to
-b/(2a), clipped below by9. These exact rational evaluations
certify all remaining integers. A negative leading coefficient,
or a decreasing affine continuation, is rejected.

Thus there is no finite load cutoff in(JM4), and no inference from
a numerical mesh to an infinite tail. The data contains59 such
proofs, with472 low-load inequalities and59 whole-tail checks.
The verifier neither imports nor calls a floating-point optimizer.

## 3. An integer-sensitive raw81 envelope

Original index46 is f46(n)=(n^2-81)_+. It obeys the simple bound

    f46(n) <= (243/91)*Phi5(n),  n>=1 integer.        (JM6)

For1<=n<=9 the left side is zero. For n>=9 the difference is

    (243/91)*Phi5(n)-(n^2-81)
      = (n-18)*(61*n-1089)/182.                     (JM7)

Its two real roots are1089/61 and18. There is no integer strictly
between them, so(JM7) is nonnegative on all integer loads. The
polynomial can be negative between its roots over the reals;
requiring nonnegativity on all real loads would lose this bound.
Consequently

    <f46,mu> <= (243/91)*(6353/7200)
              =171531/72800.                         (JM8)

This value is attained in the relaxation M by the exact measure

    mu = (91927/655200)*delta_1
         +(6353/655200)*delta_18.                    (JM9)

It has mass3/20 and factorial moment6353/7200. The checker also
verifies its other20 moment inequalities. Therefore(JM8) is
optimal for this target using the current22-moment relaxation,
without any claim that(JM9) is an actual J source distribution.

## 4. Assemble every original payment and the complete denominator

Let f_i,w_i,0<=i<52, be the original ordered cost functions and
positive weights. Preserve the original negative mass coefficient
cS, positive outside-square coefficient cQ, and offset C0. Using
the corresponding verified upper bounds gives

    Nbar=cS*S+sum_(i=0..51) w_i*U_(f_i)+cQ*U_square
        =35.495449222434287... .                      (JM10)

The largest weighted contributions are displayed only to locate
the remaining costs; none is removed from the sum.

| Original index | Weighted upper payment |
| --- | ---: |
|0|6.075990627615473...|
|41|4.299799247873298...|
|16|4.284461104780121...|
|47|3.038441933448549...|
|32|1.934679027813051...|
|7|1.759002070411559...|
|46|1.735565588257895...|
|1|1.542995133900929...|

242's complete count law gives the remaining tail

    Tcount=(U_mean-S)/7986+S/87846
          =277/4392300.                              (JM11)

Writing the four independent AP11 upper bounds as U_B0,...,U_B3,
the positive denominator lower bound remains

    Ebar=S-U_H4/6-(U_B0+U_B1+U_B2+U_B3+Tcount)/7
        =67792212611/813541806000
        =0.083329722100353869... .                   (JM12)

The complete comparison is C0+Nbar/Ebar, giving(JM1). Its margin
for a403 certificate, measured in numerator units, is

    (403-C0)*Ebar-Nbar = -3.713003941588428773... .    (JM13)

No missing original term or infinite count outcome is replaced
by zero. The survivor mass is exact, so its signed coefficient
does not require a separate relaxation.

## 5. Independent rational witnesses certify the method boundary

For each of the59 targets f, retain a finite supported rational
measure mu_f in M. These witnesses contain248 positive atoms in
total. The checker verifies all22 constraints for each one,
including exact mass:1298 rational moment checks. Put

    L_f=<f,mu_f>.

Every valid envelope using(JM3) must satisfy

    U'_f >= sup_(mu in M)<f,mu> >= L_f.             (JM14)

The witnesses for different targets are independent. This is
appropriate to the method in which every original test is
estimated separately. It supplies no common-source attainment
claim and does not equate their load variables.

Substitute L_f for every positive target upper in(JM10)--(JM12),
and call the resulting expressions Nlo and Ehi. They are both
strictly positive. Every candidate tuple of independent scalar
moment envelopes with a valid positive denominator satisfies

    N' >= Nlo >0,  0<E'<=Ehi,
    C0+N'/E' >= C0+Nlo/Ehi.                          (JM15)

The mass term is fixed, all numerator target weights are
positive, and every denominator deduction is increasing in its
target values. These signs justify(JM15). Exact substitution gives
the left endpoint of(JM2); the already certified envelopes give
its right endpoint. Thus(JM2) brackets the infimum of this fixed
independent scalar-envelope method, even if no joint optimizer
or actual source realizes all the lower witnesses simultaneously.

The remaining directions require information absent from(JM3),
such as actual source coupling, common deletion constraints or
new complete head bounds. Merely identifying independently
labelled loads and optimizing a single aggregate target would
change the problem and is not justified here.

## 6. Exact artifact and scope

The standard-library checker and rational data are

- [Complete J moment consumer](../../frontier/j-source/j_face_complete_moment_cost_comparison.py)
- [Rational envelopes and moment witnesses](../../certificates/source_norms/j-source/j_face_complete_moment_cost_comparison.json)

The certificate preserves152 nonzero envelope coefficients,
the exact finite witnesses, all target identities, the whole-tail
minima, source hashes and complete comparison values. Its default
mode recomputes the stored result through the canonical artifact
reader; it does not rerun the expensive predecessor source scans.

These are ordinary rational certificates and source inequalities.
The result neither crosses403 nor extends the J faces to an
off-face neighborhood. No unrestricted Erdos7 result, actual-family
attainment or Lean verification is asserted.
