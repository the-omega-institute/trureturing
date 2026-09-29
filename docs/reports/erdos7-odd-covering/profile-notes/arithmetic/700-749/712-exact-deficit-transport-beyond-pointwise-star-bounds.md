# Quantitative deficit transport beyond pointwise star-profile domination

A certified target product carrier can still be used when the actual singleton
carrier has less mass on some coordinates. Construct the target submeasure on
the same actual pure-coordinate laws, pay the exact mass lying in singleton
blockers once, and normalize only after all original constraints are imposed.
This gives an ordinary quantitative extension of [Report710](710-shared-support-and-query-carriers-pass-the-fixed-depth-two-profile.md); it is not a new
Lean application of CAR revelation scaling or the cycle minimax theorem.

## One finite dominated completion, including all boundary cases

Fix one actual family with the original phases and distinct numerical labels
unchanged. Work under its actual pure-coordinate survivor probabilities lambda_q
and its five allowed ternary leaves. For each coordinate q and active leaf l,
let A_ql avoid all source-live actual singleton3q^e/9q^e blockers and put

    a_ql=lambda_q(A_ql), 0<=a_ql<=1.

Fix a previously certified target0<m_ql<=1, weights w>=0 summing to1, and a
threshold t<T=615/49. For a single coordinate, abbreviate a=a_ql,m=m_ql,A=A_ql.
Define a measure eta on the SAME actual coordinate carrier by

    if a>=m:
        eta=(m/a) lambda_q|A;
    if a<m:
        eta=lambda_q|A + ((m-a)/(1-a)) lambda_q|A^c.       (DL1)

The first denominator is nonzero because a>=m>0. In the second branch,
a<m<=1 forces a<1. If a=1, only the first branch applies and eta=m lambda_q.
If a=0, only the second applies and eta=m lambda_q. Thus no zero denominator
or atomlessness assumption is hidden.

Both coefficients are in[0,1], so eta is dominated by lambda_q. Its total mass
is m; its actual-good mass is min(m,a); its actual-bad mass is(m-a)_+.
This construction does not change an original, move a forbidden phase, or
assume that the target singleton profile is itself arithmetically realized.
It selects an auxiliary dominated measure on the existing actual carrier.
Set inactive-leaf measures to zero and define

    nu=sum_l w_l delta_l tensor product_q eta_ql.         (DL2)

## The existing G and H apply before the final singleton deletion

Conditional on any active leaf, nu is a product with the target coordinate
masses m_ql. Because each eta_ql<=lambda_q, its normalized q-cylinder cap is
still c_q/(m_ql q^e). These are precisely the hypotheses used by the target's
support-event Shearer calculation and the labelled ordered-increment query
bound. Neither proof requires the auxiliary carrier already to avoid singleton
blockers; that requirement is needed only for the final supported law.

Let V avoid every remaining actual original with nonternary support size at
least2. Their d,3d,9d label inventories, root/leaf assignments and phases are
unchanged. The target's certified probability bridge gives

    nu(V)>=G(m,w).

The same target gives, for EVERY permitted finite query layout L,

    integral (L-t)_+ dnu <= Hstar(m,w,t).                (DL3)

This is the same nu for all layouts. Its full nonternary tail is already
included in Hstar. No total-variation estimate for an unbounded hinge is used.

Let Astar be the actual simultaneous singleton survivor. On leaf l it is the
product of the coordinate sets A_ql. The mass to remove from nu is EXACTLY

    D=nu(Astar^c)
     =sum_l w_l [product_q m_ql-product_q min(m_ql,a_ql)]. (DL4)

This is a charge on one common product carrier, not a sum of independently
optimized losses. Restrict once more to the actual complete survivor
U=V intersect Astar. Then

    alpha=nu(U)>=G-D.                                  (DL5)

As long as G-D>0, the one actual-supported law mu=nu|U/alpha satisfies

    R_{v3<=2}(mu)<=t-1+Hstar/alpha
                  <=t-1+Hstar/(G-D).                   (DL6)

Thus the sufficient quantitative transport condition is

    D < Dmax := G-Hstar/(T-t)
                =((T-t)G-Hstar)/(T-t).                 (DL7)

Here T-t>0 is required explicitly. Since Hstar>=0, strict DL7 implies
G-D>Hstar/(T-t)>=0 and therefore validates normalization. It also gives
R<T-1=566/49, the existing pure-conditioned23/29 continuation gate, with
its whole-family ternary-height-two restriction retained.

Only lower bounds on the actual a_ql are needed: DL4 decreases when any a_ql
increases. A convenient weaker linear budget is

    D<=sum_l sum_q w_l (m_ql-a_ql)_+
                     product_(r!=q)m_rl.

The exact product difference additionally retains the overlap of losses within
one leaf. It reduces to zero on the earlier pointwise-domination region.

The same construction applies to the common target masses in
[Report711](711-small-prime-star-bounds-certify-depth-two-common-carriers.md).
Choose the entire target certificate before evaluating its loss; pieces from
different target measures cannot be combined as one law.

## Exact tolerated losses for both retained target certificates

For both targets t=6, so T-t=321/49>0. The independent arithmetic is in
[the exact verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_deficit.py)
and its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_deficit.json).

The fixed DT target permits the STRICT loss bound

    D <2548523432511439183713026082610425361
       /144163396658716343601299047151648437500
      =.0176780201603092... .                           (DL8)

The simpler sufficient condition D<=3/200 follows from its score>1/10,
because(321/49)(3/200)<1/10.

The target m_DT-1/100 on the four active leaves permits

    D <8199125928384385168395508313924674353749
       /1740893571533828566613924008593750000000000
      =.004709722674867757... .                         (DL9)

The simpler sufficient condition D<=1/220 follows from its score>3/100,
because(321/49)(1/220)<3/100. These are two separately certified target
choices, not independently optimized pieces to be combined into one law.

## An actual arithmetic example outside the old box

Use the distinct odd numerical originals

    0 mod3, 1 mod9, 0 mod5,
    11 mod15, 41 mod45, 76 mod225.                     (DL10)

The pure ternary survivors, in the interface order, are

    (4,7 | 2,5,8) mod9.

The actual pure5 law is uniform on the20 residues modulo25 not divisible by5.
The15-class is root2 with x5=1. The45-class is leaf5mod9 with the SAME x5=1;
its projection is contained in the15 projection, so their union has mass1/4,
not1/2. The225-class is leaf4mod9 with x25=1 and mass1/20. Consequently the
actual five-leaf q=5 blocker masses are exactly

    (1/20,0,1/4,1/4,1/4).

Other q in the benchmark have no singleton blockers, hence a_ql=1 there.
These facts were checked on all100 relevant pairs of retained ternary leaf
and pure5 residue, using their unique CRT lift modulo225. No arbitrary cap
vector was labelled an actual family.

The old box fails because its leaf0,q5 allowance is1/100, while this family
has1/20. For the fixed DT target, the only deficit occurs on that coordinate.
With w=(8/25,3/10,19/100,0,19/100),

    D=(w0/20) product_(q!=5)m_DT,q0
      =1568/210375=.007453357100415924... <3/200.

The resulting exact common-law bounds are

    G-D=3778997/37867500,
    score_after_loss
      =1474022156405118438534954040144425361
       /22006250580302494817643779783273437500 >0,
    R<=23893398933029251967809147092414968389
        /2196119493608275883234736670486590625
       =10.87982644048746... <566/49.

DL10 is a transparent noncovering example that certifies STRICT enlargement of
the sufficient-condition region. It is not claimed to be a hard cover or a
counterexample to any noncoverage theorem. Holding these pure/singleton
originals fixed, the proof continues to handle arbitrary additional original
phases on nonsingleton nonternary supports in the benchmark core and the
stated outside continuation, subject to distinct labels and whole-family v3<=2.

The checker also evaluates DL1 on the actual finite pure5 carrier for every
leaf, confirming mass m, domination by lambda5, good mass min(m,a), and bad
mass(m-a)_+. It reconstructs the source certificates before checking these derived losses;
checks remain active under optimized standard-library Python.
The theorem remains conditional on the certified target's low-dimensional
probability bridge and complete-query interface. It does not certify every
possible actual profile or remove the small-support/height assumptions.

Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_deficit.py
```
