[Index](../../marked_head_profile.md) · [Original factorial head](../065-128/112-the-factorial-tail-retains-one-compatible-original-head.md) · [Joint pure-five moments](164-the-pure-five-first-and-second-moments-have-a-sharp-joint-envelope.md)

# The first-five support lowers the complete factorial bound

On both complete actual saturated K faces, the full second factorial
upper bound improves from619/720 to

    T5<=3091/3600.

The improvement is1/900. It comes from retaining the same deep-five
slot in the original head cross and the complete pure-five pair block.
The five density caps cannot all be attained in the head's chosen slot.
All original head residues remain independent, and every geometric and
polynomial tail remains complete.

The same original head is also retained when this bound is combined
with each positive quadratic cost. The helper reconstructs all52
original costs, uses165's improved square bound2233/450 simultaneously,
and keeps the complete111 survival denominator. The complete comparison
improves from459.0991409076946 to459.03512880963814, a reduction
of0.06401209805649051. This is an ordinary saturated-face theorem, not an
off-face extension, a new global K bound, a Lean theorem or a solution
of unrestricted Erdos7.

## 1. Identify the two positive summands being replaced

Use112's original layout

    ell=(r3,c9,s5,r15,s15,c45,s45),
    B=1+I3+I9+I5+I15+I45,
    h4(v)=(v-4)_+,
    R5=sum_(b>=2)1_(F_b),

where F_b is the independently chosen original test cylinder of
modulus5^b. Let mu be the same actual survivor measure throughout.
The relevant block of112's factorial expansion is exactly

    integral_mu [h4(B)R5+binom(R5,2)].                 (JF1)

The old first term was bounded by O5(w h4(B)); the second is the
pure-five/pure-five subseries of the complete distinct-tail-pair cap.
At maximum exponent b there are b-2 unordered pairs of distinct deep
pure-five labels, so that subseries is

    P55=(2/5)sum_(b>=2)(b-2)5^-b=1/200.               (JF2)

This is also recorded explicitly as1/100 before halving in128's
complete pair partition at sigma=E27=all defects=0. The same partition
has total2539/3600, leaving2521/3600 after removing(JF2). Thus no
unidentified gain is subtracted from an opaque total. All mixed-three,
old-five/other-old, old-five/seven and seven/seven categories remain.

## 2. Keep the five head rows before their maximum

Use112's existing descendant coefficients d(c,s) and retained density
w(c,s). For a fixed original layout define

    A_s=sum_c d(c,s)w(c,s)h4(B(c,s)),
    c=(0,2/15,14/45,2/5,7/30) in slots(P,A,B,Q,H).

The actual deep-cylinder caps c_s are164's bounds. The proof of112's
original O5 already gives, for every b>=2 cylinder F_b in slot s,

    integral h4(B)1_(F_b) dmu <= A_s 5^-b,
    mu(F_b)<=c_s 5^-b.                              (JF3)

If n_s counts earlier deep test labels in slot s, the contribution at
depth b to(JF1) is at most

    (A_s+c_s n_s)5^-b.                              (JF4)

Cylinders in different first slots are disjoint. Same-slot cylinders
need not intersect; counting every earlier same-slot label only raises
the bound. No nesting restriction has been imposed on the original
labels.

For general nonnegative A_s,c_s and r in(0,1), put

    V_s(n)=(A_s+c_s n_s)/(1-r)+c_s r/(1-r)^2,
    V(n)=max_s V_s(n).

For a choice k and reward R_k=A_k+c_k n_k,

    R_k+r V_k(n+e_k)=V_k(n).

For j different from k, its count is unchanged and
R_k<=(1-r)V_k(n), hence

    R_k+r V_j(n+e_k)
      <=(1-r)V_k(n)+r V_j(n)<=V(n).

Taking the maximum proves the Bellman inequality. Iteration is valid
for every changing allocation. Its remaining potential is O(N r^N),
which tends to zero. Choosing a maximizing slot forever attains the
allocation bound; this does not claim attainability by actual sources.
At n=0, r=1/5 and initial factor5^-2, the result is

    integral [h4(B)R5+binom(R5,2)] dmu
      <= Qrow(ell):=max_s(A_s/20+c_s/80).            (JF5)

In particular

    Qrow<=max_s A_s/20+max_s c_s/80
         =O5(w h4(B))+1/200.                       (JF6)

The direct complete-row replacement never worsens any layout.
Nonnegative summands and the summable bound O(b5^-b) justify passage
from finite original test families to every complete tail.

## 3. A second valid bound retains the first-five event explicitly

Let K=I3+I9+I15+I45, G=1_{K=4}, H=1_{K>=3}, and f=s5. The exact
identity is

    h4(B)=G+I5 H.                                  (JF7)

The overlap at K=4,I5=1 is required: h4(B) then equals2. Define

    e_f=min(c_f,sum_c d(c,f)w(c,f)H(c,f)).

By(JF3) applied to H and by H<=1, any deep cylinder in f satisfies
mu(H intersect F_b)<=e_f 5^-b. In the other first slots I5 vanishes.
Applying the same affine Bellman proof with A_f=e_f and A_s=0
otherwise gives

    integral [I5 H R5+binom(R5,2)] dmu
      <=max(c_f/80+e_f/20,max_(s!=f)c_s/80).

Therefore a second upper bound for(JF1) is

    Qcond=O5(w G)
          +max(c_f/80+e_f/20,max_(s!=f)c_s/80).     (JF8)

The helper uses Qjoint=min(Qrow,Qcond). These are two upper bounds on
the same complete positive block, so taking their smaller value is
valid. The first-slot labels, survivor measure and residual have not
changed. A separate all-layout comparison gives45 layouts where Qrow
is smaller,2 where Qcond is smaller and12453 where they coincide.

## 4. Maximize the whole original layout after substitution

Write J(ell) for112's old head value, excluding its constant
P=2539/3600. Define

    Jnew(ell)=J(ell)-O5(w h4(B))+Qjoint(ell)-1/200.

The full bound is

    T5<=Jnew(ell)+P.                               (JF9)

All12500 original layouts are enumerated exactly:459 improve strictly
and12041 remain unchanged. The maximum is

    max_ell Jnew(ell)=23/150,
    23/150+2539/3600=3091/3600.                    (JF10)

The two maximizing layouts remain
(1,3,2,1,2,3,2) and(1,4,2,1,2,4,2). At either layout, and at113's
old common maximizing layout(0,1,2,0,2,1,2),

    O5(w h4)=2/225,
    O5(w G)=1/225,
    e_B=4/45,
    Qjoint=23/1800.

The old block is2/225+1/200=1/72; its reduction is1/900. The scalar
maximization does not assume these old witnesses remain controlling;
it checks every original layout anew.

For each of113's ten nonnegative quadratic expansions, the full cost
is bounded by

    f(1)D+max_(ell,extra)[M_f(ell,extra)+theta Jnew(ell)]
          +theta P.                               (JF11)

The same layout is used in both terms inside the maximum. Different
cost tests retain their independent original labels. The raw81n1 row
with negative hinge coefficients keeps its previous accepted bound.
All1250000 combined objectives are evaluated exactly. New fractions
are scaled using lcm(66706983000,21600), not the old5400 head scale.

## 5. Reproducible complete comparison and boundary

The retained actual mass and complete first and second moments are

    D=53/360, L=1151/1800, Q=2233/450.

The complete survival denominator stays50511415637/632754738000.
The accepted original cost indices41,42,43,44,45,48,49,50,51 improve;
the ten new common maxima still use(0,1,2,0,2,1,2), each uniquely.
Index47 already had a stronger retained bound and does not change.
Majorant propagation produces no additional improvement. The exact
complete-comparison reduction from165 is

    135965768797331647321/2124063621182080245096.

The new comparison remains56.03512880963814 above403. This gain
therefore does not close even the current saturated-face comparison.

The certificate records every original cost, its separate head
maximum, majorant propagation, the full numerator and the comparison.
It checks the predecessor content hashes through certificate_io,
including multipart artifacts, and all arithmetic uses exact rational
numbers. The scope remains both complete saturated faces only.

Run the result and its canonical check with

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/pure_five_joint_factorial_comparison.py --write
    python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/pure_five_joint_factorial_comparison.py --check

The data artifact is
[the complete joint-factorial certificate](../../certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json).
