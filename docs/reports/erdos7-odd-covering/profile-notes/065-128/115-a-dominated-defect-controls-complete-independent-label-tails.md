[Index](../../marked_head_profile.md) · [Common deleted measure](../001-064/57-common-deleted-measure-coupling.md) · [Actual shared defects](85-a-broad-five-slot-source-deletion-tradeoff.md)

# A dominated defect controls complete independent-label tails

A small error mass alone does not control an unbounded original-label
load. The actual positive survivor excess has an additional property:
it is dominated by the raw source, hence by raw35 Haar measure. This
gives explicit complete tail bounds that tend to zero with the defect
mass. Their infinite sums have exact finite-correction formulas.

The result applies to independent residues at every original modulus.
It supplies a quantitative transfer interface, not a transport of75's
forced27 geometry or a new complete off-face comparison. In particular
it gives no new global K or unrestricted Erdős #7 resolution.

## 1. Use the positive survivor excess, not an arbitrary error measure

Let H be product Haar probability on the old3/5 coordinates. The actual
raw source Lambda and survivor marginal mu satisfy

    0<=mu<=Lambda<=H.

Suppose a proved measure inequality gives

    mu<=w*Lambda+epsilon,
    0<=w<=1, epsilon>=0, epsilon(1)<=e<=1.          (DT1)

Define the Jordan positive part

    nu=(mu-w*Lambda)_+.

Then

    mu<=w*Lambda+nu,
    0<=nu<=mu<=Lambda<=H, nu<=epsilon, nu(1)<=e.    (DT2)

Indeed all measures are absolutely continuous with respect to the
positive measure mu+w*Lambda+epsilon. The corresponding pointwise
positive-part inequalities prove(DT2). No unproved domination of
epsilon by Haar is needed; it is nu that has this domination.

For example, if85's correctly placed5 and15 families and the actual
shallow3/9 carrier weights give

    w(c,j)=1-t_c/5-(1/5-q5)*I_H(j)
                         -(1/5-q15)*I_root1(c)*I_H(j),

then0<=t_c<=2 and0<=q5,q15<=1/5 imply1/5<=w<=1. The bounded
transfer uses epsilon=V-delta, with mass omega. Hence(DT2) applies
with e=omega, or with any proved common upper bound for omega. This
example presupposes the actual shared-budget and carrier identities;
it does not assert those identities from the definition of w alone.

## 2. Complete mixed moments with a small-mass cap

For i=1,...,k let

    Z_i=sum_(a,b>=0)1_(C_(i,a,b)),

where C_(i,a,b) is an arbitrary residue cylinder modulo3^a*5^b and
the unit term is1. Tests and their labels need not have nested or
matching residues. Omitting a nonunit label only decreases the bounds.

For every positive integer k put

    Delta_k(a)=(a+1)^k-a^k,
    Psi_k(e)=sum_(a,b>=0) Delta_k(a)*Delta_k(b)
                                       *min(e,3^-a*5^-b).     (DT3)

Then the same actual defect measure satisfies

    integral_nu product_(i=1..k) Z_i <=Psi_k(e).     (DT4)

To prove this, truncate each test, expand the product into its ordered
original-label tuples, and fix the largest3- and5-exponents a,b of a
tuple. Its CRT intersection is empty or a cylinder of Haar mass
3^-a*5^-b. By(DT2) its nu mass is at most both this cap and e.
There are Delta_k(a)*Delta_k(b) exponent tuples with these maxima.
Enlarging the finite positive sum to all exponents gives(DT4).
Monotone convergence removes every truncation. This argument never
identifies independent test residues or asserts simultaneous
attainment of their intersection caps.

In particular, let

    B1(e)=Psi_1(e)-e,
    B2(e)=Psi_2(e)-e,
    B11(e)=Psi_2(e)-2*Psi_1(e)+e.

The useful centered versions are

    integral_nu(Z-1)<=B1(e),
    integral_nu(Z²-1)<=B2(e),
    integral_nu(Z1-1)*(Z2-1)<=B11(e).              (DT5)

These formulas remove unit tuples before taking cap bounds. They
do not replace the unknown nu(1) by e in a negative term. For the
last formula, at every(a,b)!=(0,0) the count of ordered pairs whose
two labels are nonunit is Delta_2(a)*Delta_2(b)-2; the all-unit
maximum contributes zero. This proves the displayed subtraction.

## 3. Evaluate the infinite series by a finite correction

Write

    M_k(p)=sum_(a>=0) Delta_k(a)*p^-a.

The needed complete moments are

    M1(p)=p/(p-1), M2(p)=p*(p+1)/(p-1)²,
    M1(3)*M1(5)=15/8, M2(3)*M2(5)=45/8.            (DT6)

These are the raw35 moments already used in57. For e>0,

    Psi_k(e)=M_k(3)*M_k(5)
       -sum_(3^-a*5^-b>=e) Delta_k(a)*Delta_k(b)
                                          *(3^-a*5^-b-e).    (DT7)

Only finitely many terms satisfy the displayed condition. Everything
outside it retains its complete geometric mass in(DT6). Thus(DT7)
is exact and does not discard any exponent tail. The value at e=0
is defined separately as0, directly from(DT3) or nu=0.

For k=1,2 the helper also evaluates(DT3) independently by summing
complete five-coordinate rows followed by a complete three tail.
If q=1/p and the tail starts at N, its values are

    sum_(a>=N) p^-a=q^N/(1-q),
    sum_(a>=N)(2a+1)*p^-a
                =q^N*((2N+1)/(1-q)+2q/(1-q)²).    (DT8)

Every rational input e therefore gives an exact rational answer.

## 4. The full error tends to zero, but no uniform linear price exists

For any finite N, split(DT3) into the exponent square and its
complement. If T_k(p,N+1) is the complete tail in(DT8), then

    Psi_k(e)<=e*(N+1)^(2k)
                +M_k(5)*T_k(3,N+1)
                +M_k(3)*T_k(5,N+1).              (DT9)

The complement is enlarged by a nonnegative overlap. First make
the two complete tails small by choosing N, then make the finite
term small by reducing e. This proves Psi_k(e)->0 as e->0. The
same conclusion holds for the centered bounds in(DT5).

A linear estimate with a constant independent of e is impossible
even for a genuine Haar-dominated defect. Take the original labels
3^a*5^b for0<=a,b<=N with zero residues, and let nu be Haar restricted
to the zero cylinder modulo15^N. Its mass is e_N=15^-N. On this
cylinder the load equals(N+1)², so

    integral_nu(Z-1)/e_N=(N+1)²-1,
    integral_nu(Z²-1)/e_N=(N+1)^4-1.               (DT10)

Both ratios diverge. This is a limitation of uniform dominated-error
transfer, not a claim that every such nu occurs in an actual covering
source. It explains why the admissible error price need not be a
fixed multiple of the residual budget.

## 5. One error measure pays all original costs together

Suppose independently labelled tests Z_i have nonnegative weights
b_i and proved growth bounds

    0<=f_i(v)-f_i(1)<=a_i*(v-1)+c_i*(v²-1),
    a_i,c_i>=0, v>=1.

Then(DT2),(DT5) imply

    sum_i b_i*integral_mu f_i(Z_i)
       <=sum_i b_i*f_i(1)*S
          +integral_(w*Lambda) sum_i b_i*(f_i(Z_i)-f_i(1))
          +(sum_i b_i*a_i)*B1(e)+(sum_i b_i*c_i)*B2(e),        (DT11)

where S=mu(1) is the actual survivor mass. The constants are
multiplied by that mass, not an endpoint mass. All costs use the
same nu and the same e; no independent error law is introduced.
The right side's source integrals and growth coefficients still
need their own valid bounds in a numerical consumer.

For the current source problem, this controls an unbounded zero7
load after a measure comparison is established. Positive-seven
terms already separated by their own bridge keep their existing
complete estimates. Formula(DT11) does not silently replace a
full357 test by its zero7 part, nor does it prove off-face versions
of the pure3/forced27 deletion identities in75 and109.

## 6. Concave tail error changes the shared-budget optimization

Each term in(DT3) is increasing and concave in e. The centered
bounds inherit these properties from their nonnegative nonunit
tuple sums. Adding them to a finite objective that is convex in
the carrier defects does not imply joint convexity in all defects.
In particular, substituting omega=e-G*q5-g15*q15 does not justify
maximizing the resulting expression only at polygon vertices.

An exact scalar example is the budget q+omega=1/5 with objective

    3*q+B1(omega).

At omega=0,1/5 its two endpoint values are3/5 and89/120. At the
interior point omega=1/15 it is299/360, strictly larger than both.
This refutes the unrestricted vertex shortcut for this class of
composed bounds; it is not an actual covering-family construction.

Two valid interfaces remain: use the uniform upper bound Bk(e)
before optimizing the finite carrier-defect polygon, or fix omega,
optimize the remaining polygon, and rigorously optimize the final
one-dimensional omega function. Merely checking the full polygon's
vertices is insufficient.

## Reproduction and scope

[dominated_defect_complete_tails.py](../../frontier/cover-geometry/dominated_defect_complete_tails.py)
exports `cap_series(e,k)` and `centered_bounds(e)` for k=1,2. The
[certificate](../../certificates/source_norms/cover-geometry/dominated_defect_complete_tails.json)
contains exact rational mass rows, two independent full-tail
evaluations,45 finite Haar-quantile checks for separately labelled
tests, and the concave-error counterexample. Quantile checks optimize
over all dominated submeasures of the finite uniform space; they do
not enumerate actual forbidden covering families. The ordinary
tuple and measure arguments prove the arbitrary-height statement.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/dominated_defect_complete_tails.py --check
```

The reusable content is the complete dominated-defect transfer and
its optimization boundary. No Lean verification, new global bound,
or completed unrestricted proof is claimed.
