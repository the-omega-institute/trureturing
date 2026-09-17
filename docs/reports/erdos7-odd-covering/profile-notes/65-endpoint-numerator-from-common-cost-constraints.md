[Index](../marked_head_profile.md) · [Linear endpoint](59-endpoint-linear-source-deletion-bound.md) · [Complete numerator reference](61-exact-tensor-numerator-reference.md) · [Common deep source](64-one-zero-seven-layout-and-complete-pure-three-tails.md)

# One common cost law strengthens the complete endpoint numerator

For the entire actual endpoint class of profiles59 and64, the current
AP-transformed numerator has the uniform upper bound

    N_endpoint <=36.00101643084306... .                    (1)

The endpoint class consists of actual finite forbidden families tending
to theta404, survivor mass S=D=3/20, and carrier mixture(root0,cell1).
Every original test retains independently chosen residues, which may
change along the sequence. The statement concerns the46 transformed
cost directions and the complete raw81 comparison with their current
weights and signed barriers. It does not assert simultaneous attainment
of their separately bounded costs or of the physical AP numerator.

For comparison with the fixed-numerator obstruction of profile56, use
that profile's one actual tensor witness denominator

    d_tensor=12117093811/128357460000.

The new numerator bound satisfies

    C0+N_endpoint/d_tensor <=402.9561199451897...<403.      (2)

This denominator belongs to the specified witness. It is not a lower
bound for the denominators of arbitrary endpoint families. Equation(2)
is therefore a benchmark for the improved numerator, not a uniform K
bound. A uniform survival denominator, a quantitative square/numerator
neighborhood, and the global source-domain comparison remain separate
obligations. Unrestricted Erdős #7 remains open. These are ordinary
proofs and exact rational certificates, not Lean verification.

## 1. Every old cost bound applies to every original test

Fix one actual limiting endpoint source and its surviving measure mu.
For each independently labelled complete original357 test A, the two
new moment bounds are

    mu(1)=D=3/20,
    integral A dmu<=1157/1800,
    integral A^2 dmu<=469/100.                           (3)

Let f_0,...,f_45 be exactly the profile49 transformed costs. Its first
41 are linear-growth costs and its last five are quadratic-growth
costs. Keep their current signed barriers C_j and old conditional
margin bounds m_j at theta404/carrier(0,1). The old theorem says

    integral f_j(A) dmu<=C_j*D-m_j                       (4)

for every admissible original test A, not just for a distinguished
choice of residues attached to the name j. The same is true of the
six inherited raw81 bounds

    integral (A^2-81/n^2)_+ dmu
       <=square357(81/n^2,theta404), n=1,...,6.           (5)

Their right sides are pre-deletion source bounds; deleting points
preserves them because the costs are nonnegative.

The54 constraints used below are the two bounds in(3), all46 bounds
in(4), and all six bounds in(5). Their order is explicit in the
certificate. A different test A_i satisfies all54 constraints. Thus
one may combine cost bounds evaluated on A_i without identifying it
with any other independently labelled test A_k.

This observation is the reason the common constraints are useful.
Taking only the minimum of a moment bound and the old bound for each
single cost omits valid combinations of several costs on that same
test. All the combinations below retain the one actual measure mu.

## 2. Exact majorants on the entire unbounded integer domain

Write the54 constraint functions as g_j and their upper bounds as B_j.
For each of the52 target functions f, choose rational numbers

    alpha in Q, lambda_j>=0

such that

    f(v)<=alpha+sum_j lambda_j*g_j(v)
                  for every integer v>=1.              (6)

Then, on the actual source,

    integral f(A) dmu<=alpha*D+sum_j lambda_j*B_j.        (7)

The constant alpha can be negative because the actual mass is exactly
D. Every coefficient on an upper constraint is nonnegative. Each target
uses its own majorant; no independence assumption on the actual loads
or their joint law is needed to sum their positive-weight bounds.

The supplied rational coefficients are certificate inputs. No numerical
optimization result is trusted by the checker. It proves(6) directly:
every g_j and target f has, from the pinned AP cost formulas, an exact
integer tail

    a*v^d+b, d in{1,2}, v>=K_j.

For K=max K_j over the functions actually used, the majorant difference
is an explicit rational quadratic

    q(v)=q0+q1*v+q2*v^2, v>=K.

The checker verifies q2>=0. If q2=0 it also checks q1>=0, so checking K
settles the whole tail. If q2>0, the integer minimum on v>=K is attained
at K or at a clipped floor/ceiling of -q1/(2*q2). Evaluating these few
integers exactly settles every unbounded load. The remaining integers
1,...,K-1 are evaluated with the exact original cost functions.

This proves the full majorant, including any quadratic mass that could
escape to arbitrarily large loads. A finite load grid alone would not
suffice. Coefficients rounded for presentation are never used; the
program and certificate retain the exact rational numbers.

For each target retain the smaller of(7) and its already valid old
bound. Improvements are not added to an old cost bound. Identity
majorants retain costs for which the new constraints give no gain.

## 3. The complete unchanged numerator identity

Let U_i be the resulting52 upper bounds. For the46 transformed costs
use the original barriers and weights to define

    M41=sum_(i<41)w_i*(C_i*D-U_i),
    m_g=45*D-469/100=103/50,
    Mquad=sum_(41<=i<46)(C_i*D-U_i)+oQ*m_g,
    oQ=1600217/12882870.

The square barrier is45. It is not replaced by an older source norm
or by the improved square bound itself.

With the same full AP11/AP13 count probabilities p_n as profile61,

    R81=sum_(n=1..6)p_n*n^2*U_(46+n-1).

Atoms7 and8 and the entire n>=9 tail remain in the unchanged square
coefficient cG. They are neither discarded nor charged again in R81.
Keeping H16,H41,A81,AC,C0 unchanged gives

    N_endpoint=(AC*H16+H41+A81)*D
                  -AC*Mquad-M41-cG*m_g+R81.             (8)

The program independently expands(8) into a multiple of D plus the
52 positive-weight cost terms and the positive coefficient of the
square bound. Equality of the two exact expressions checks the signs
and barrier cancellations. The residual coefficient of D is negative;
this is valid because the endpoint mass is fixed, and that signed
term must be retained in any neighborhood extension. All four disjoint improvement groups are
nonnegative: the41 linear costs, the five quadratic costs with their
complement, the raw81 square tail, and the six low raw81 terms.
Their sum equals the old fixed numerator minus(8).

This yields(1). Dividing by the separately specified witness denominator
and adding C0 yields(2), with positive exact rational slack below403.
That arithmetic comparison does not change the role or scope of the
denominator.

## 4. Changing finite families and independent tests

The bounds are first proved on an actual limiting endpoint family.
For arbitrary sequences of finite original families and the finitely
many independently changing target tests, select a joint labelwise
diagonal subsequence. Every fixed original source/test cylinder then
stabilizes. The source measures converge in L1 using their complete
geometric forbidden-union tails and the lower pure7 normalizer5/6.

Every target cost has at most quadratic growth. The ordered-pair
polynomial-times-geometric tail from profile62 uniformly controls the
quadratic load tails across all original tests and source heights.
For each fixed finite label box the costs are bounded, so their
integrals converge; the uniform complete tail passes this convergence
to all52 full costs. Thus any sequence violating the claimed limsup
would produce a limiting endpoint family violating(6)--(8).

There is no assumed nesting, common residue or tensor form for the
actual tests. The tensor source occurs only in the benchmark denominator.

## 5. Reproduction and remaining comparison

The standard-library [checker](../frontier/endpoint_numerator_common_costs.py)
reads hash-pinned source/cost inputs, verifies all52 rational majorants
on every positive integer, reconstructs every barrier and coefficient,
and checks both complete numerator expansions. It writes through the
existing semantic certificate writer only when explicitly requested.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_numerator_common_costs.py --check
```

The [certificate](../certificates/source_norms/endpoint_numerator_common_costs.json)
contains the exact coefficients, finite low-load gaps, analytic tail
critical values, complete per-cost bounds and aggregate identities.
Its semantic parts assemble into one exact rational artifact.

The result quantitatively passes the previously obstructing witness
benchmark by changing the numerator uniformly on the entire specified
endpoint class. It does not supply a global denominator lower bound,
and does not update the existing uniform K certificate.
