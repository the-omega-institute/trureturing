[Index](../../marked_head_profile.md) · [Previous joint square](184-the-two-pure-prime-paths-share-their-shallow-square-state.md) · [Complete deep-three deletion](../065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Actual pointwise source domination](../065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md)

# The two prime paths retain the same compulsory deletion

On both complete saturated actual K faces, the two pure-prime
test paths obey

    U=integral(Z3^2+2Z3+Z5^2+2Z5+2Z3*Z5)<=125/108. (SD1)

This improves184's1567/1350 by1/300. It reduces the complete square
to13109/2700. Retaining184's full cost vector, including all174
factorial gains, and its complete denominator gives

    K<=10399866722898697544974622986709693690268831574139
         /22677592043090460737750844455566666200000000000
      =458.596605104173253415416279... .            (SD2)

The complete-face improvement over184 is0.0084018623426501658....
Original costs43 and45 also improve through the existing majorant
consumer. This is an ordinary all-depth inequality with an exact
rational consumer, without any actual-family sharpness claim.
It is not an off-face or global theorem, a Lean result, or a
resolution of unrestricted Erdos7.

## 1. Locate the same deletion measure inside the shallow cross

Use184's actual survivor mu, raw source Lambda and canonical cells
ROOT=(0,0,1,1,1). The four distinct retained forbidden families
give mu<=w*Lambda. By75, saturation also makes delta=V, so the
complete deep-three forbidden family V3 may be retained in the
same inequality:

    mu<=w*Lambda-V3.                              (SD3)

Every original deep-three forbidden carrier lies in root0 and
has full five section3^-a*q(F). The forced27 carriers all lie
in cell1. Therefore, for every five-coordinate measurable F,

    V3(root0 times F)=q(F)/90,
    V27(cell1 times F)=q(F)/135.                  (SD4)

These coefficients sum every original seven depth and every
required three depth. For the shallow test choices r,j set
psi=1_root r+1_cell j. Since V27 is part of V3,

    integral psi*1_F dV3
       >=[I(r=0)/90+I(j=1)/135]*q(F).             (SD5)

When both indicators contain the forced27 support, it has
multiplicity two in psi. The two terms in(SD5) count that
multiplicity of the same measure; they do not posit a second
deletion budget.

Let pre, raw, w and descendant be the original184 source tables;
let h_cs denote its head_caps. For the five slots P,A,B,Q,H,

    Q_s=q(slot s)=(0,1/5,1/5,3/20,1/5),
    h_cs=w_cs*raw_cs-I(c=1)*Q_s/135.              (SD6)

Thus184's firstcross already subtracts the complete27 amount
once for every occurrence of cell1. Its root0 aggregate has used
Q_f/135 of the full Q_f/90 available in(SD4). The additional
deduction is exactly

    X*=sum_(ROOT(c)=r) h_cf+h_jf-I(r=0)*Q_f/270.  (SD7)

No further cell1 deduction is made in(SD7). This avoids subtracting
the already retained27 family a second time from the same head cap.

## 2. The five-tail cross retains its own source factor

For a deep-five test F_b in slot s, b>=2,184 used

    H_s=sum_(ROOT(c)=r) descendant_cs*w_cs
                             +descendant_js*w_js.

That bound contains the four selected families, but contains no
deep-three forbidden deduction. By(SD5) it may be strengthened to

    H*_s=H_s-I(s!=P)*[I(r=0)/90+I(j=1)/135].     (SD8)

The P slot is source-empty. The replacement by5^-b in the other
slots requires care, particularly in Q, where q(F_b) can be smaller.
On each root0 cell the raw source is bounded by eta_c*q(F_b).
Its contribution to psi*w*Lambda, less the two deductions in(SD5),
is bounded by

    [sum_(c<2) n_c*descendant_cs*w_cs
                    -I(r=0)/90-I(j=1)/135]*q(F_b),
    n_c=I(ROOT(c)=r)+I(c=j).                     (SD9)

The coefficient is nonnegative for every allowed r,j and s!=P.
The exact consumer checks all these coefficients. We may therefore
use q(F_b)<=5^-b after subtraction. Root1 terms retain their original
nonnegative Haar bounds. This proves

    integral psi*1_(F_b) dmu<=H*_s*5^-b           (SD10)

without assuming that Q is fully occupied by the five source.
Both K orientations and all first-beta cells use the same complete
source-table permutation as184. No beta-vertex interpolation or
new source realizability assumption is involved.

## 3. Keep both deep choices through the two Bellman bounds

Retain the proved171 and164 marginal caps c3_c,c5_s. Define

    P_cf=pre_cf*w_cf,
    k_cs=w_cs if pre_cs>0, and0 otherwise.

The pointwise bridge in128/184 gives, for arbitrary independent
deep test labels J_a in cell c and F_b in slot s,

    mu(J_a intersect F_b)<=k_cs*3^-a*5^-b.        (SD11)

Keep the shallow root r, cell j and first-five slot f fixed. The
whole joint deep contribution is at most

    max_(c,s) {
      [c3_c*(n_c+2)+P_cf]/9
      +c5_s*(11 if s=f else7)/40
      +H*_s/10+k_cs/180 }.                       (SD12)

To justify the two maxima, first fix an arbitrary entire five-tail
sequence and let theta_s=sum_(b>=2,slot(F_b)=s)5^-b. Then theta_s>=0
and sum theta_s=1/20. The deep-three reward at count m_c is

    c3_c*(2*n_c+2*m_c+3)+2*P_cf+2*sum_s k_cs*theta_s.

171/184's nonnegative affine-potential lemma bounds this arbitrary
three path by the best constant coarse cell c. Its completed sum is

    [c3_c*(n_c+2)+P_cf]/9+(1/9)*sum_s k_cs*theta_s.

For this fixed c, the extra term is a per-five-depth reward
k_cs/9. Combine it with the five marginal and shallow-three
cross reward

    c5_s*(3+2*I(s=f)+2*m_s)+2*H*_s+k_cs/9.

The same lemma with discount1/5 and first depth2 bounds every
five path by the best constant coarse slot s, yielding(SD12).
The finite maximum over c can be interchanged with the supremum
over five sequences. A constant coarse state is the optimizer of
these relaxed Bellman rewards; original residues remain independent
and need not form nested cylinders.

The term k_cs/180 is exactly the complete mixed-tail coefficient
2*(1/18)*(1/20)*k_cs. It occurs only once. Keeping c,s jointly
without the deductions(SD7)--(SD8) reproduces1567/1350 exactly;
the strict improvement here comes from the compulsory deletion.

## 4. All1250 states and the complete consumer

The shallow contribution is

    3*A_r+(3+2*I(ROOT(j)=r))*B_j+3*FIRST5_f+2*X*.  (SD13)

Evaluate(SD12)--(SD13) over2*5*5*5*5=1250 choices. The unique
maximizer is(r,j,f;c,s)=(0,1,2;1,2). Its terms are

    shallow3=23/45, first5=14/75, 2*X*=58/675,
    three joint tail=59/225,
    five joint tail=289/2700, deep mixed=1/225.

Their sum is125/108. The next distinct maximum over shallow
choices is599/540. The helper checks the exact affine Bellman
identities and all remaining root0 source-factor signs in every
case. These finite checks evaluate the proved infinite bounds;
they do not replace the arbitrary-label or source-limit arguments.

The same uniform tails used by184 remain sufficient:

    sum_(a>A)(2a+1)*3^-a+sum_(b>B)(2b+1)*5^-b
                               +(3^-A+5^-B)/4 ->0.

They justify the varying-source diagonal limit as well as the
fixed-source monotone limit. The deductions only lower caps and
leave these raw tail bounds available.

The replaced block is exactly the two marginal pure-prime blocks
and their mutual cross. Every other LCM class is retained. Hence

    Q_new=6559/1350-1/300=13109/2700.

Use184's52 improved costs as inputs to the existing complete
majorant consumer. The numerator gains are

    direct square gain=0.0004429100118242668869...,
    further43/45 gain=0.0002277921345648148148... .

All174 factorial and184 majorant savings remain. The unchanged
full denominator, including every AP11 block, AP13 loss and
infinite count tail, is50511415637/632754738000>0. The resulting
complete numerator is34.88494420557680758917..., which gives(SD2).

The [helper](../../frontier/retained-transport/pure_axis_shared_deletion_comparison.py) and
[certificate](../../certificates/source_norms/retained-transport/pure_axis_shared_deletion_comparison.json)
pin75's original complete deletion,184's complete input vector,
all source tables and the full denominator. No assertion that an
actual family attains125/108 is needed or made.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/retained-transport/pure_axis_shared_deletion_comparison.py --check
```
