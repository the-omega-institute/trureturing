[Index](../marked_head_profile.md) · [Full numerator carriers](49-full-linear-and-quadratic-carriers-refine-the-frontier.md) · [Actual source endpoints](50-sharp-source-survival-endpoints.md)

# A common deleted-measure coupling for survival and numerator costs

For arbitrary original mixed7 labels, the existing mass slack controls
an entire missing measure, not only the total amount of deletion. This
gives a uniform way to retain deep cofactor/load correlations for all
survival and numerator tests at once.

The result below is ordinary mathematics. It does not establish a
positive uniform improvement of the present global comparison. The
remaining new inequality is identified in section5.

## 1. Actual deletion and its original-cofactor cap measure

Let Lambda be the actual raw35 source, of mass s, and nu7 the actual
normalized pure7 survivor law. For every present original mixed7 label
i=(a,b,e), a+b>0,e>=1, retain its genuine CRT product

    E_i=C_i x K_i,

where C_i is its one original3^a5^b residue cylinder. Different i may
have different residues and may overlap. Write

    p_i=nu7(K_i), u_i=6/(5*7^e), p_i<=u_i,
    B=union_i E_i,
    S=(Lambda tensor nu7)(B^c).

An absent label contributes no cylinder. There is no assumption that
the actual p_i attain their upper caps or that the E_i are disjoint.

On the original35 space define two positive measures:

    delta(dx)=nu7({z:(x,z) in B}) Lambda(dx),
    V(dx)=[sum_i u_i*1_(C_i)(x)] Lambda(dx).          (1)

Then delta is the actual deletion projected onto the old coordinates;
V retains all the original cofactor cylinders before cap and union
losses. Pointwise union bounding gives

    0<=delta<=V.

Let T be any valid upper bound for V(1), and D=s-T. The inherited
source cap formula gives such a T=s-D(theta). One can instead use
the stronger actual common-carrier bound D_pi=sum_c pi_c*D_c whenever
its already-proved cap calculation gives V(1)<=s-D_pi. Then

    epsilon:=S-D>=0,
    (V-delta)(1)=V(1)-(s-S)<=epsilon.              (2)

This is a measure inequality. In particular, near saturation of the
existing mass bound controls every bounded observation of deletion.

The bookkeeping is explicit:

    epsilon=[T-sum_i u_i Lambda(C_i)]
            +sum_i(u_i-p_i)Lambda(C_i)
            +[sum_i p_i Lambda(C_i)-delta(1)].       (3)

The terms are respectively unused geometric cofactor capacity, loss
in the actual seven probabilities, and overlap of deleted labels.
All are nonnegative. No contribution is counted twice.

## 2. Exact bounded transfer and endpoint rigidity

For every measurable 0<=phi<=R, (1)-(2) imply

    integral_delta phi>=integral_V phi-R*epsilon.   (4)

More precisely, R*(V-delta)(1) can replace R*epsilon. If the original
mass bound is exact, S=D, then V=delta as measures. Thus every
integrable nonnegative cost transfers exactly at that endpoint:

    integral_delta phi=integral_V phi.              (5)

For a sequence with S-D tending to0, (4) gives total-variation control
of bounded observables. It does not infer convergence of an unbounded
hinge merely from mass convergence. Section3 supplies the needed
uniform moments for the original labelled load family.

For an original357 test A, let A0 be its original zero7 test load.
The pointwise inequality A>=A0 gives, for increasing f>=0,

    integral_B f(A)>=integral_delta f(A0).

Therefore for every truncation R>=0,

    integral_B f(A)
      >=sum_i u_i*integral_(C_i) min(R,f(A0))-R*(S-D). (6)

The positive sum may be restricted to any selected original cofactors,
without invalidating(6). It can thus retain a finite group of deep
mixed7 cofactors while the mass slack covers every omitted depth and
every union/cap defect. This changes the deletion payment itself.

There cannot be a general transfer without the slack term. For example,
placing each test label's K_i inside the already removed pure7 class
can make delta=0 while V is nonzero. The finite `cap-loss` case in
the checker exhibits this with genuine original modulus labels and
a positive virtual hinge integral. It is not a counterexample to(4).

## 3. Complete uniform mixed moments for independently labelled tests

Let Bp=1+sum_(a>=1)1_[0]_(p^a) under raw p-adic Haar measure, and put
Q=B3*B5. Write M_k=E[Q^k]. Its factors have the geometric count law

    Pr(Bp=n)=(p-1)/p^n, n>=1.

In particular

    M0=1, M1=15/8, M2=45/8, M3=3795/128.

Let Z1,...,Zm be arbitrary complete original35 tests, each with its
own residue for every3^a5^b label, and with unit term1. Their residues
need not agree with each other or with any forbidden cofactor C_i.
For positive integers r,s,

    integral_V (Z_i^r-1)*(Z_j^s-1)<=H_(r,s),       (7)
    H_(r,s)=(1/5)*E[(Q-1)*(Q^r-1)*(Q^s-1)].

Proof: first truncate every family to finitely many labels. Expand
Z_i^r-1 as the nonnegative sum over ordered r-tuples of its labels,
excluding only the tuple consisting entirely of the unit label.
Do the same for Z_j^s-1. A term also has one nonunit cofactor label
from V. The Haar mass of their common intersection is either zero
or

    3^(-max a)*5^(-max b).

It is at most that value regardless of the independently chosen
residues. Lambda is bounded above by full raw35 Haar measure. All
these intersection maxima are attained simultaneously by the nested
zero residues used to define Q. Summing each positive7 depth's cap
gives sum_e6/(5*7^e)=1/5. This proves(7) for finite families; monotone
convergence proves the complete statement and all exponent tails.

The constants needed for simultaneous linear and quadratic costs are

    H11=2227/640,
    H12=H21=13481/320,
    H22=884579/1280.                               (8)

They are obtained from the exact complete moments through

    5*H_(r,s)=M_(r+s+1)-M_(r+s)-M_(r+1)+M_r
                         -M_(s+1)+M_s+M1-1.

For costs f_i with f_i(1)=0 and

    0<=f_i(v)<=a_i*(v^(r_i)-1), r_i in{1,2},

and nonnegative target weights w_i, put

    Phi=sum_i w_i*f_i(Z_i),
    alpha=sum_(r_i=1)w_i*a_i,
    beta=sum_(r_i=2)w_i*a_i,
    M=alpha^2*H11+2*alpha*beta*H12+beta^2*H22.

The pairwise version(7) gives integral_V Phi^2<=M even though all
the original tests are independently labelled. Applying Cauchy-Schwarz
to the same positive error measure V-delta proves

    integral_delta Phi>=integral_V Phi-sqrt(M*epsilon). (9)

An entirely rational dual version, valid for every R>0, is

    integral_delta Phi
       >=integral_V Phi-R*epsilon-M/(4*R).          (10)

Indeed, Phi<=R+(Phi-R)_+ and (Phi-R)_+<=Phi^2/(4R).
These are uniform estimates, not inference from the tensor witness.

The linear and quadratic AP numerator costs in profile49 have the
required growth bounds after centering at1. For example,

    E[1_active*(h(Nv)-h(N))/N]<=Pr(active)*(v-1)

for a linear hinge, and the corresponding squared hinge is bounded
by E[1_active*N]*(v^2-1). The complete auxiliary moments supply a_i.
If f_i(1) is nonzero, first subtract this constant and subtract it
from the comparison barrier C_i as well; the actual deficit is
unchanged. No source constant is silently discarded.

## 4. One absorption formula for survival and all numerator deficits

For each independently labelled full357 test A_i, define

    U_i=integral_(Lambda tensor nu7) f_i(A_i),
    d_i=C_i*S-integral_(B^c) f_i(A_i).

This includes the survival hinges with C_i=1 and the fixed linear
or quadratic numerator barriers. The exact identity is

    d_i=C_i*S-U_i+integral_B f_i(A_i).

All tests share the same forbidden source and the same delta,V,S.
Applying(9) to their zero7 loads A_(i,0), with the chosen nonnegative
consumer weights, yields

    sum_i w_i*d_i
      >=(sum_i w_i*C_i)*S
        -[sum_i w_i*U_i-integral_V sum_i w_i*f_i(A_(i,0))]
        -sqrt(M*(S-D)).                            (11)

The rational penalty from(10) can replace the square root. For a
finite selected-cofactor implementation, use(6) instead and retain
the actual clipped joint integrals. Equation(11) changes numerator
and survival deficits together, and every deletion contribution is
used exactly once with its actual target coefficient.

At S=D, there is no measure-transfer error. The bracket in(11),
rather than the old pre-deletion source cost alone, is the relevant
joint extremum. This is compatible with the new actual-tensor bound
showing that changing survival alone cannot reach the target while
the profile49 numerator is held fixed.

## 5. The remaining relation is explicit; no uniform gain is claimed

Equations(6) and(11) still require a new joint source estimate. If an
existing original7 decomposition gives

    U_i<=P_i(theta)+integral_Lambda psi_i(A_(i,0)),

the quantity that must now be bounded uniformly is

    sum_i w_i*integral_Lambda psi_i(A_(i,0))
       -sum_j u_j*integral_(C_j) sum_i w_i*f_i(A_(i,0)), (12)

with one common actual forbidden cofactor family C_j. Maximizing the
first term independently and discarding or independently minimizing
the second term recovers the old loss. The present theorem does not
show that the second term is bounded below by a positive constant
whenever the first is near its old maximum.

A precise stability target for one scalar source is the following.
For F an inherited source upper bound, seek gamma>0 and kappa>=0 with

    V(f(A0))>=gamma-kappa*[F-Lambda(psi(A0))]         (13)

for every actual source and original test in the specified parameter
region. For kappa>0 this is equivalent to the joint upper bound

    Lambda(psi(A0))-(1/kappa)*V(f(A0))
        <=F-gamma/kappa.

It is an inequality about the same actual family, not a conclusion
from one maximizing witness. Its weighted multi-test version applies
directly to(12). Neither(13) nor a numerical gain from(12) has been
proved here.

The newly required observations can be stated without ambiguity:

    J_(j,i,k)=Lambda(C_j intersect {A_(i,0)>=k}).

For integer t,

    V(h_t(A_(i,0)))=sum_j u_j*sum_(k>=t+1)J_(j,i,k).

The analogous weighted tails determine the quadratic costs. These
intersections retain the original cofactor and the original test
load together. The old cell masses, total remaining count, scalar
source norms, or a re-encoding of them do not specify these values.
Finite selected labels and clipped loads give a finite observation
system; the complete moment bounds above control the unbounded
transfer. Establishing a useful bound for(12) is the mathematical
frontier left by this result.

## Exact checks and limitations

[The checker](../frontier/common_deleted_measure_coupling.py) reconstructs the actual raw35 forbidden source at height3.
It uses four genuine mixed7 label families: the canonical endpoint
construction, deliberate overlapping cylinders, cylinders killed by
the pure7 source, and independently scrambled old/seven residues.
It checks pointwise delta<=V, the exact cap/overlap decomposition,
the complete inherited mass budget, and bounded/unbounded transfers
for two hinges, an independent quadratic test and their joint cost.
The moment constants are evaluated as exact geometric moments.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/common_deleted_measure_coupling.py --check
```

The checker is read-only unless `--output PATH` is supplied. `--check`
compares the reconstructed exact data with the
[certificate](../certificates/source_norms/common_deleted_measure_coupling.json). The
finite checks exercise cap shrinkage and overlap instead of assuming
them away. They do not certify an unproved positive uniform source
gain or a new K bound. The arbitrary-family and infinite-tail claims
are supplied by the ordinary arguments above.
