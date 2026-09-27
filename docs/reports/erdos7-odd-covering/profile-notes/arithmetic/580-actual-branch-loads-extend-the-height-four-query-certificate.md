# Actual branch loads extend the height-four query certificate

Fix P={3,5,7,11,13,17,19}, Q=P without3. Let the actual originals be
any finite family of distinct nonunit odd P-smooth numerical moduli,
with one globally fixed residue per modulus. Its pure3 originals are
exactly 1 mod3 and3 mod9. At each nonunit Q-cofactor d, suppose all
original projections at ternary exponents0,1,2,3 occupy at most two
Q phases. Later heights and phases are unrestricted subject to the
branch-load condition below.

On the finite actual cofactor inventory, select at most two phases at
each d containing those shallow phases;
spare slots may also remove an exponent4 phase. Use ONE actual
Report569 PA source nu on the selected Q-survivor. Write

    A=[0]_9 union [6]_9,
    B3=[2]_9 union [5]_9 union [8]_9.

Let L_A4 count the residual exponent4 originals whose ternary phase
lies in A, using their actual Q phases, and put rho_A=E_nu L_A4.
An original whose Q phase was selected contributes zero on this source.
The following sufficient condition permits a third exponent4 phase:

    rho_A < rho_star
          =15232049749731473125568032040735530696696089170781
           /17675397446262147818643258984205266694377556670000
          =0.8617656149481734... .                         (BA1)

There is then one actual supported joint probability mu with

    R_P(mu) <= N/[1-rho_A/33-K3/66-K7/22] <566/49,          (BA2)

where R_P sums the maximum cylinder probability for EVERY nonunit
numerical P-smooth query, at every height, and

    B=432040125182653876501/86355045355449035400,
    N=B+(10/11)(1+B)
     =3312131027463407253507/316635166303313129800,
    K3=12019840537595758779003/5715264751774801992890,
    K7=6258510165289233442029877862409645975916115839
       /7807154349055719001167517219171937585855811250.

No additional bound is imposed on the number of active cofactors, on the
exponent4 branch-B3 load, or on any later residual height. At rho_A=0,
the complete query bound is11.227261991232368... . Arbitrary additional
originals touching23 or29 then leave actual Haar survivor mass
greater than1/9000. The general continuation bound is given below.

This strictly extends Report574's through-exponent4 hypothesis inside
the stated fixed pure3 slice. It does not remove the through-exponent3
condition or handle arbitrary pure3 families. In particular it does not
settle unrestricted Erdős #7. These are ordinary proofs and exact
arithmetic, with no new Lean verification or external novelty claim.

## 1. The same source carries both branch loads

Reuse the actual source and simultaneous full-height positive-part
bounds from [Report574](574-four-level-query-hinge-removes-pointwise-overlap.md):

    R_Q(nu)<=B, E_nu(L-t)_+<=K_t,
    nu<=9 H_Q/alpha_min,
    alpha_min=7575003978548161/73724315753088000.             (BA3)

The positive-part estimate, used here for0<=t<=7, holds for every
partial one-phase nonunit Q query layout L, and by convexity for its
convex mixtures. K3 and K7
are the complete-suffix values of the existing envelope; no height
tail is discarded. No query-specific source is substituted into BA3.

Let u_A and u_B be Haar conditioned on A and B3. For e>=4 let
L_Ae,L_Be count the actual residual Q incidences at that exponent
whose ternary cylinders lie in the indicated branch. Original
numerical distinctness implies that their sum has at most one phase
per Q-label. Originals outside the pure survivor do not act on either
branch. Define

    alpha_e=54*3^(-e), sum_(e>=4) alpha_e=1,
    Y_A=sum_(e>=4)alpha_e L_Ae,
    Y_B=sum_(e>=4)alpha_e L_Be.                             (BA4)

Absent exponents contribute the zero layout. Each Y is a convex
mixture under the SAME nu. For the complete actual survivor mask chi,
put c_j(x)=integral chi(t,x)du_j(t). Since a depth-e cylinder in A
has u_A mass(9/2)3^(-e), while one in B3 has mass3*3^(-e), the actual
union bounds are

    1-c_A<=Y_A/12, 1-c_B<=Y_B/18.                          (BA5)

The relation that is retained beyond Report579's scalar total is

    Y_A=(2/3)L_A4+(1/3)Z_A,
    Z_A=3 sum_(e>=5)alpha_e L_Ae.                          (BA6)

Z_A is another convex mixture, so

    E_nu(Y_A-1)_+ <= (2/3)rho_A+(1/3)K3,
    E_nu(Y_B-7)_+ <= K7.                                  (BA7)

The first inequality follows pointwise from
((2/3)L_A4+(1/3)Z_A-1)_+
<= (2/3)L_A4+(1/3)(Z_A-3)_+.
Thus the statistic rho_A measures an actual original/branch relation;
it is not assigned independently of the source or original phases.

## 2. One joint law, asymmetric thresholds and the full query sum

Set kappa_A=11/12, kappa_B=11/18 and use equal root weights:

    h_j(x)=1/max(c_j(x),kappa_j),
    eta(dt,dx)=(1/2)chi(t,x)u_A(dt)h_A(x)nu(dx)
              +(1/2)chi(t,x)u_B(dt)h_B(x)nu(dx).            (BA8)

These are two submeasures of one actual survivor. Because c_j h_j<=1,
eta's Q marginal is at most nu. At ternary depth1, the two roots are
disjoint and their Q marginals are each at most nu/2. For every
Q-smooth d>=1 and a>=2, the actual cylinder caps give

    q_(3^a d)(eta)
      <=3^(2-a) max{(1/4)q_d(h_A nu),(1/6)q_d(h_B nu)}.

Here q_d(sigma)=max_r sigma([r]_d) for any finite measure sigma,
including q_1(sigma)=sigma(1). Sum ALL depths, using
sum_(a>=2)3^(2-a)=3/2. This yields

    R_P(eta)<=B+(1/2)(1+B)
       +sum_(d>=1,Q-smooth)
          max{(3/8)q_d(h_A nu),(1/4)q_d(h_B nu)}.          (BA9)

Each maximum uses the two normalizer measures derived from this same
construction. Their maximizing phases need not maximize a query under
eta. In particular h_A<=12/11 and h_B<=18/11 equalize the two
deep-query coefficients at9/22. Hence BA9 is at most

    B+[(1/2)+(9/22)](1+B)=N.                              (BA10)

Finite query boxes followed by monotone convergence justify every
sum; bounded h_j and R_Q(nu)<=B ensure finiteness. This includes the
Q-unit once at every positive ternary depth and excludes it once
from the pure-Q contribution.

Writing s_eta=eta(1), BA5 and BA7 give

    1-s_eta
      =(1/2)E_nu[(kappa_A-c_A)_+/kappa_A]
       +(1/2)E_nu[(kappa_B-c_B)_+/kappa_B]
      <=[E_nu(Y_A-1)_++E_nu(Y_B-7)_+]/22
      <=rho_A/33+K3/66+K7/22.                             (BA11)

Put s0=1-rho_A/33-K3/66-K7/22. The exact threshold BA1 is

    rho_star=33(1-49N/566-K3/66-K7/22).

It guarantees s0>49N/566>0. Normalizing ONCE, mu=eta/s_eta, proves
BA2. Both its Q marginal and its relative branch weights may change
with the actual residual fibres. A fixed-u restriction is not asserted.

There is a stronger same-source positive-part version. For any
0<=r<=3/2, replace (2/3)rho_A+(1/3)K3 in BA7 by

    Gamma_A(r)=(2/3)E_nu(L_A4-r)_++(1/3)K_(3-2r).         (BA12)

This follows from BA6 by splitting the threshold1 as
(2/3)r+(1/3)(3-2r). Then R_P(mu)<=N/[1-(Gamma_A(r)+K7)/22],
which passes whenever

    Gamma_A(r)<22(1-49N/566)-K7
              =1.275547664851623... .                     (BA13)

The bound uses the same actual nu throughout; it is a sufficient
condition, not an assertion that every actual family meets it.

## 3. Arithmetic checking and arbitrary23/29 continuation

Let D_A4 be the actual residual exponent4 cofactors in branch A.
The source density in BA3 gives the entirely arithmetic sufficient
condition

    sum_(d in D_A4)1/d < alpha_min*rho_star/9
       =0.009838270672642870... .                         (BA14)

Each d occurs once at this exponent. A small actual rho_A can also
satisfy BA1 when the density-based BA14 is too coarse.

The two branches in BA8 are disjoint. Their Haar density caps agree:

    (1/2)(9/2)(12/11)=(1/2)3(18/11)=27/11.

Consequently eta<=243 H_P/(11 alpha_min), with no doubling of the
disjoint branch caps. Apply Report569 SD15--SD16 to THIS submeasure,
with s_eta>=s0 and raw query sum<=N. After conditioning the23 and29
coordinates on their actual pure-power survivors, every additional
original touching23 or29 is charged under that same product law.
The remaining mass is at least(566s0-49N)/567. Dividing by the full
density cap gives

    H(full survivor)>=alpha_min(566s0-49N)/13608>0.         (BA15)

Indeed (11/243)(21/22)(27/28)/567=1/13608. All additional numerical
labels, phases, P-smooth cofactors and finite heights remain arbitrary.
The entire family here is supported on P union{23,29}; primes outside
that set are not included in this continuation theorem.

At rho_A=0 the bound is

    5077349916577157708522677346911843565565363056927
    /45495414676673208339450453294815817703090068480000000
    =0.00011160135483236862... >1/9000.

## 4. A strict structural extension with actual fixed residues

Take the five original (modulus,residue) pairs

    (3,1), (9,3), (385,0), (1155,386), (31185,28107).

At cofactor385=5*7*11 their Q phases at exponents0,1,4 are0,1,2.
The latter two originals have ternary phases2 mod3 and0 mod81.
Select S_385={0,1}. The through-exponent3 condition holds, whereas
Report574's through-exponent4 condition fails. The residual exponent4
cylinder lies in A, so

    rho_A=nu([2]_385)<=9/(385 alpha_min)
          =0.2275148063208694... <rho_star.

BA2 gives R_P(mu)<=11.31096107971715...<566/49; BA15 exceeds1/12500.
The exact program provides a private residue for each of the five
originals, so the separating original is not redundant. This witness
separates sufficient structural classes; it does not assert failure
of every older instance-specific certificate or novelty of its bare
noncoverage. Indeed this particular witness has only one active
residual cofactor and also meets Report572's incidence condition.
The general result above permits arbitrarily many residual cofactors;
that broader quantifier does not come from this finite witness.

There is also an irredundant21-original witness with six simultaneously
active residual cofactors under the displayed source. Keep the two
pure3 originals. For q_i=5,7,11,13,17,19, indexed i=0,...,5, add

| ternary exponent | Q phase modulo q_i | ternary phase |
|---:|---:|---:|
|0|0|vacuous|
|1|1|2 mod3|
|4|2|2+3i mod81|

Finally add4 mod385. Select phases{0,1} at each q_i and{4} at385.
All six exponent4 cylinders lie in B3, so rho_A=0. Each prime
cofactor has three projected phases through exponent4, violating
Report574's condition. At the Q event with all six prime roots2,
the same chosen PA law has mass

    1/[(5-2)(7-2)(11-2)(13-2)(17-2)(19-2)]=1/378675>0.

Indeed the5 and7 roots are uniform outside{0,1}; at11 there is one
additional forbidden root4 only when the old5 and7 roots both equal4.
Every row is below its PA cap and retains mass one. The all2 event
does not trigger that additional restriction, and13,17,19 only avoid
their roots0,1. On this event six distinct cofactors are active,
so Report572's M<=2 premise fails for THIS specified source.
No claim is made that every different auxiliary selector must fail.

Every original has a private CRT point without enumerating the full
period: for the pure3 classes take all Q roots3 and ternary residue1
or3 mod81; for an original at q_i set its Q root to the indicated
phase, every other Q root to3, and its ternary residue to0,2 or2+3i
for exponents0,1,4 respectively; for4 mod385 set the5,7,11 roots4,
the other Q roots3, and the ternary residue0. These points meet their
own original and none of the others. BA2 and BA15 apply with rho_A=0
and require no incidence bound on the residual source.

## 5. What the retained branch relation changes

[Report579](579-two-root-convex-clipping-has-an-exact-certificate-boundary.md)
allows arbitrary fixed finite prefix refinements but bounds losses
only from the scalar total Y_A+Y_B and its moments. That certificate
cannot pass the gate even with individual query and loss caps.
BA6 retains additional information: how much of the dominant
exponent4 load actually lies in the narrower A branch. The separate
thresholds1 and7 can then spend the two branch losses together while
keeping the deep-query coefficients equal. There is no conflict with
the earlier scalar-certificate obstruction, which does not contain
this actual allocation constraint.

The unresolved case includes large branch-A exponent4 load, failure
of the shallow two-phase selection, and other pure3 configurations.
Failure of BA1 or BA13 is not a lower bound on attainable query norms.
No positive query saving is inferred solely from deleted mass.

The [exact producer](../../frontier/cover-geometry/branch_asymmetric_height_four.py)
and [data](../../frontier/cover-geometry/branch_asymmetric_height_four.json)
pass160 named checks of the source constants, branch-cylinder identities,
complete geometric tails, strict gates, density continuation and both
actual witnesses. The retained controls include48 saturated survivals,
144 hinge-decomposition points and10 overlapping, nested or dead fibres.
The source inputs and producer are bound by their SHA-256 digests.
Running the same Python3.9+ standard-library entry from a different
working directory, under isolated Python with a space-containing program
path, produces identical data.
The ordinary proofs above carry arbitrary heights and actual-family
quantifiers; finite controls do not replace them.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/branch_asymmetric_height_four.py
