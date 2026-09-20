[Index](../../marked_head_profile.md) · [Sharp isolated cross](175-the-isolated-pure-three-five-cross-is-actually-sharp.md) · [Pure-three moments](171-the-pure-three-path-has-a-joint-complete-moment-bound.md) · [Pure-five moments](164-the-pure-five-first-and-second-moments-have-a-sharp-joint-envelope.md) · [Current complete face comparison](174-the-pure-three-factorial-tail-retains-its-original-head.md) · [Actual source domination](../065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md)

# The two pure-prime paths share their shallow square state

On both complete saturated actual K faces, let Z3 and Z5 be the
independently labelled complete pure-three and pure-five test
loads. Their joint block satisfies

    U=integral[Z3^2+2Z3+Z5^2+2Z5+2Z3*Z5]
      <=1567/1350.                              (JP1)

The previously separate bounds gave539/450. The saving is
exactly1/27, so the complete original square improves to

    Q<=2203/450-1/27=6559/1350.                 (JP2)

Keeping174's full52 cost vector and then applying the existing
majorant propagation gives the complete face comparison

    K<=458.605006966515903581... .              (JP3)

This improves174 by0.07911011069652208065... . All original
costs, factorial improvements, geometric and polynomial tails,
and the complete survival denominator remain.

The result concerns both saturated actual faces, with r=rho=0.
It does not extend off those faces or give a new global K bound.
No actual-family sharpness, Lean theorem or unrestricted Erdos7
resolution is asserted.175's isolated cross remains sharp; the
gain comes from retaining its shallow choices together with
the two marginal moments.

## 1. Keep one actual source and three shallow choices

Write

    Z3=X+Y+R3, R3=sum_(a>=3)I_(J_a),
    Z5=F+R5,   R5=sum_(b>=2)I_(F_b).

Let r be the root selected by X, j the cell selected by Y,
and f the first-five slot selected by F. Thus

    r in{0,1}, j in{0,...,4}, f in{P,A,B,Q,H}.

Source-null ternary choices can be replaced by a surviving
choice for an upper bound, because the entire integrand is
nondecreasing in both loads. The50 displayed triples therefore
cover every independent shallow choice, including omissions.

Use171's proved root, cell and deep-cylinder caps

    A=(7/90,7/90),
    B=(1/40,1/18,1/30,1/30,1/30),
    c3=(7/10,11/20,3/10,3/10,3/10),             (JP4)

and164's proved first-slot and deep-cylinder caps

    FIRST5=(0,2/75,14/225,7/150,7/150),
    c5=(0,2/15,14/45,2/5,7/30).                (JP5)

All remaining tables are loaded directly from the existing
whole_factorial_same_head.FactorialHead: pre, descendant, w,
and the surviving fixed-rectangle caps head_caps. They retain
the actual first-beta condition and the separate forced27
deletion. No new first-five cap is assumed.

The second K orientation permutes both root0 cells in all
these tables and caps together. First-beta permutations move
the root1 cells together; their c3 and B entries agree. Since
all50 shallow triples are included, these relabelings leave
the common bound unchanged.

## 2. A pointwise bound pays the deep cross only once

The actual face case of128's source domination gives

    mu<=w*Lambda, Lambda<=Haar3 x Haar5.         (JP6)

The union excess is zero on the stated saturated face. This
is domination of the same actual projected survivor measure,
not a product assumption about that measure.

If a deep ternary test J_a has parent cell c and a deep five
test F_b has parent slot s, their product cylinder has Haar
mass3^-a*5^-b. Where pre(c,s)=0 the source itself is absent.
Elsewhere w is constant on that rectangle. Consequently

    mu(J_a intersection F_b)
      <=w(c,s)*3^-a*5^-b
      <=a_c*3^-a*5^-b,
    a_c=max_(s:pre(c,s)>0)w(c,s)
       =(1,4/5,4/5,4/5,4/5)_c.                (JP7)

Summing over every independently chosen b>=2 gives

    integral I_(J_a)*R5<=a_c*3^-a/20.          (JP8)

The full term2R3*R5 will be assigned to the three-path reward
using(JP8). It is absent from the five-path reward below. No
cross term or deletion budget is counted twice.

## 3. The same shallow triple enters both complete path rewards

Put ROOT=(0,0,1,1,1) and

    n_c=I(ROOT(c)=r)+I(c=j).

The shallow-three moment is bounded by

    shallow3=3A_r+(3+2I(ROOT(j)=r))*B_j.        (JP9)

The shallow cross with F has bound

    firstcross=sum_(ROOT(c)=r)head_caps(c,f)
                  +head_caps(j,f).            (JP10)

For the cross of X+Y with a deep five test whose parent is s,
the descendant-source inequality gives coefficient

    H_s=sum_(ROOT(c)=r)descendant(c,s)*w(c,s)
                      +descendant(j,s)*w(j,s). (JP11)

The coefficient pre(c,f)*w(c,f) similarly bounds the cross
of a deep J_a with the fixed first-five test F after multiplying
by3^-a. These are the existing source and descendant cylinder
operators, applied to the actual chosen r,j,f.

At ternary depth a let m_c count preceding deep-three labels
in cell c. The contributions of its own moment, earlier
ternary labels, F and all ofR5 are bounded by3^-a times

    alpha3_c+2c3_c*m_c,
    alpha3_c=c3_c*(3+2n_c)
                +2pre(c,f)*w(c,f)+a_c/10.      (JP12)

At five depth b let k_s count preceding deep-five labels in
slot s. Its own moment, F and X+Y contribute at most5^-b times

    alpha5_s+2c5_s*k_s,
    alpha5_s=c5_s*(3+2I(s=f))+2H_s.            (JP13)

For equal parent cells or slots, intersections with earlier
tests are bounded by the deeper cylinder; for different
parents they vanish. No nesting of independent test residues
is assumed. The terms in(JP12) and(JP13), together with the
shallow terms, form an exhaustive disjoint algebraic expansion
of the integrand in(JP1).

## 4. Two Bellman bounds retain arbitrary deep label changes

For a reward alpha_l+beta_l*m_l with alpha_l,beta_l>=0 and
discount q, define

    V_l(m)=(alpha_l+beta_l*m_l)/(1-q)
                   +beta_l*q/(1-q)^2,
    V(m)=max_l V_l(m).

For the chosen parent l,

    alpha_l+beta_l*m_l+q*V_l(m+e_l)=V_l(m).

For another parent t, its coordinate is unchanged and
alpha_l+beta_l*m_l<=(1-q)*V_l(m). Thus

    alpha_l+beta_l*m_l+q*V(m+e_l)<=V(m).         (JP14)

Iteration covers any independently changing sequence of
parents. The terminal potential is O(N*q^N) and vanishes.
Apply this to(JP12), starting at a=3 with q=1/3, and to(JP13),
starting at b=2 with q=1/5. The resulting complete bounds are

    T3=max_c[c3_c*(n_c+2)
                 +pre(c,f)*w(c,f)+a_c/20]/9;
    T5=max_s[c5_s*(11 if s=f else7)/40+H_s/10]. (JP15)

Both depend on the same actual shallow triple. The complete
candidate is therefore

    C(r,j,f)=shallow3+3FIRST5_f
                       +2firstcross+T3+T5.     (JP16)

For a fixed measure all series are nonnegative, so monotone
convergence gives the all-depth result. For varying finite
sources and labels approaching the face, mu_N<=Haar supplies
the uniform truncation bound

    sum_(a>A)(2a+1)3^-a
      +sum_(b>B)(2b+1)5^-b+(3^-A+5^-B)/4.       (JP17)

The first two terms bound the omitted marginal moments. The
last bounds cross pairs outside the finite rectangle, using
coprimality of3^a and5^b. This tends to zero independently of
all labels. Stabilizing finitely many labels and then removing
the truncation justifies the inherited actual face limit.

## 5. Fifty exact candidates give a complete square improvement

The maximum of all50 rational candidates is1567/1350. Its
unique shallow maximizing triple is(r,j,f)=(0,1,B). The terms
there are

    shallow3=23/45, 3FIRST5_B=14/75,
    firstcross=59/1350, T3=4/15, T5=49/450.

The maximum is a fact about these upper-bound operators;
simultaneous actual attainability is not asserted.

The block previously retained in the complete square was

    34/45+49/180+17/100=539/450.

The first two summands are171 and164's marginal bounds, and
the third is175's isolated cross. Replacing their sum by(JP1)
saves1/27. The unit-unit term, every genuinely mixed original
label, every seven-containing pair and all other LCM categories
stay unchanged. This proves(JP2).

## 6. Consume the result in the current full52 comparison

Start from174's actual cost vector and both of its factorial
corrections. Substituting Q=6559/1350 and applying the existing
majorant propagation improves original costs43 and45 further.
The two numerator savings are

    direct square saving=0.004921222353602965410...,
    propagated cost saving=0.001393963361341624046... .

The resulting complete numerator and denominator are

    N=34.885614907723196670873...,
    d=50511415637/632754738000>0.

The denominator retains every AP11 block, the AP13 loss and
the complete remaining count tail. With the original offset,
the exact comparison is

    K=10400057256905306369753414112442365309736204225439
        /22677592043090460737750844455566666200000000000
     =458.605006966515903581... .               (JP18)

The [helper](../../frontier/comparison-bounds/pure_axis_joint_square_comparison.py)
loads the existing source tables and caps, reconstructs every
candidate and the general Bellman coefficient identities, and
consumes the bound in the current complete52-cost vector. Its
[certificate](../../certificates/source_norms/comparison-bounds/pure_axis_joint_square_comparison.json)
retains all50 candidates, both path rewards, complete source
hashes, the majorant proofs and all denominator terms.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/pure_axis_joint_square_comparison.py --check
```
