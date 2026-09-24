# Finite-prefix templates allow arbitrary old residue tails

Let P={3,5,7,11,13,17,19}, and choose p in{7,11,13,17,19}. Consider a
finite family of congruence classes with pairwise distinct odd numerical
moduli greater than1, supported on P union{23,29}. Old-only classes are
arbitrary. At3,5,p choose two reference prefixes A_q,B_q of depths

    h_3=11, h_5=7, h_p=6,

with A_q and B_q different modulo q. At each other old prime q choose one
prefix C_q modulo q^4. For every complete later numerical label
m_i=d_i*23^j*29^k, j+k>0, require one fixed selector sigma_i in{A,B}, with

    a_i=sigma_(i,q) modulo q^min(h_q,v_q(d_i)), q=3,5,p,
    a_i=C_q modulo q^min(4,v_q(d_i)), q in P minus{3,5,p}. (F1)

The same selector must work at all three split coordinates. It is fixed
for the complete numerical label, across all tested points and estimates;
labels sharing d_i may choose differently. Exponent zero is vacuous.
All deeper old residue digits, finite heights and23/29 phases may vary
arbitrarily by label. No original full global reference paths are required.

Then this family does not cover the integers. On the actual completed
old source used below, old points with positive original later-fibre
survival have mass strictly greater than1/20000.

This extends [report517](517-joint-anchor-budgets-close-five-split-patterns-with-finite-prefix-agreement.md)
by allowing arbitrary tails at the three split coordinates too. Its
source separation is reused without any new geometry optimization.
The proof is an ordinary same-source coupling and exact scalar calculation,
not new Lean verification. The finite template and prime-support
conditions remain part of the theorem; unrestricted Erdős#7 is unresolved.

## One comparison family preserves all actual labels

Let H_q be the largest later queried q exponent, or0 if no later class
queries q. Extend A_q,B_q through max(H_q,h_q) at3,5,p. At each other
old q extend C_q through max(H_q,4), identically for both references.
Finite CRT produces two comparison references A*,B* modulo the product
of these prime powers. The enlarged period preserves the declared
first-root splits even at a coordinate with H_q=0.

For each original later label retain its numerical modulus, its fixed
sigma_i and both23/29 phases. Replace its old residue by A* modulo d_i
or B* modulo d_i according to that selector. CRT gives one repaired
residue modulo m_i. Keep every old-only class literally unchanged.
This comparison is defined once for the entire family, independently of
the tested old point, source history or chosen bound.

The comparison family has two full references split at3,5,p and common
through every queried depth at the other four old primes. It satisfies
the full-common source-separation result inside report517. A separate
selector at each split coordinate would not supply this comparison:
one label choosing A at3 and B at5 need not match either global reference.

For q=3,5,p define

    E_q={x:x_q=A_q modulo q^h_q} union
        {x:x_q=B_q modulo q^h_q}.

For each other old prime define E_q={x:x_q=C_q modulo q^4}, and let
E be their union. Coordinates unchanged by the repair may be omitted.

If a class changes at q, its exponent exceeds the prescribed prefix
depth. Both its original and comparison q-cylinders lie in the same
prescribed prefix cylinder, by F1. Hence that entire class is inactive
in both versions at every old point outside E. Unchanged classes have
identical old activations and new phases. Thus the complete later
survivor fibres agree pointwise outside E, for every new-coordinate
point simultaneously. The number of classes does not multiply the
exceptional mass: all changed indicators lie in this one fixed union.

## The actual source controls both anchor and later cylinders

Use one completed-and-charged source nu, determined by the unchanged
old-only family, in its physical order3,5,7,11,13,17,19. Its construction
is the one in reports466/467 and Michael Schroeder's *Nine Prime Divisors
in Odd Distinct Covering Systems*, edition1.0.1; the
[library entry](../../../../../Library/Arith/schroeder2026nine.md)
records the source and verification boundary.

Write H35 for product Haar on the complete3/5 coordinates and G35 for
the actual completed3/5 survivor set. Initialization is the unnormalized
measure

    alpha35=1_G35 H35, alpha35(1)<=3/8.

At each later old q, the normalized kernel N_q(h,dx_q) obeys a Haar
density cap for every full earlier history h. Deletion gives a live
subprobability kernel L_q(h,dx_q)=D_q(h,x_q)N_q(h,dx_q), with0<=D_q<=1.
Survivors are never renormalized, and later steps preserve coordinates
already exposed. The physical caps at7,11,13,17,19 are

    C7=3/2, C11=5/3, C13=3/2, C17=2, C19=9/5.

For every event B in the joint3/5 coordinates, reverse integration of
the later live kernels against1 gives a function bounded by1. Therefore

    nu(proj35^-1 B)<=alpha35(B)<=H35(B).                 (F2)

This controls the entire joint anchor marginal, including arbitrarily
deep digits. It does not assert independence under the final source.
In particular,

    nu(E_3)<=2/3^11, nu(E_5)<=2/5^7.                   (F3)

For a fixed event B at a later old q, incoming live mass is at most3/8;
the full-history cap gives N_q(h,B)<=C_q H_q(B), and later deletion
cannot increase that event's mass. Consequently

    nu({x:x_q in B})<=(3/8)C_q H_q(B).                 (F4)

The two p-prefix cylinders are disjoint because their first digits
differ, so their total Haar mass is2/p^6. The common-prefix cylinder
at each other q has mass1/q^4. Combining F3 and F4 gives

    nu(E)<=epsilon_p
       :=2/3^11+2/5^7+(3/4)C_p/p^6
         +(3/8)sum_(q in{7,11,13,17,19},q!=p) C_q/q^4. (F5)

These bounds use the same unnormalized source as the separator.
Normalizing by nu(1), permuting actual conditional kernels or assuming
a cap after conditioning on final survival would not justify F2--F5.

## The source separation exceeds the full repair cost

For role p, let delta_p be the minimum of report517's worst-type A6
source gap and report491's direct nonworst source gap. The retained
five-role result supplies these exact fractions. For the fully repaired
family it proves

    nu({x:comparison later survival is positive})>=delta_p.

The inherited missing-shallow and deleted-root reductions are applied
to this full-reference comparison family, after choosing one old
completion. They delete classes inactive on the source and relocate only
unused reference coordinates. Their zero-fibre event on nu is unchanged;
the reductions do not choose a different source for the error bound.

The source gap minus the full prefix-repair cost is:

| Split prime p | delta_p-epsilon_p |
| --- | ---: |
|7|0.000060938899203411124...|
|11|0.0003314151482887454...|
|13|0.00014373477782596443...|
|17|0.0001667025756718762...|
|19|0.00029458322261537227...|

All five are strictly greater than1/20000. Because original and
comparison fibres agree outside E,

    nu({x:original later survival is positive})
      >=delta_p-nu(E)>1/20000.                         (F6)

The source is supported on points avoiding the original old-only
classes. At such a positive-fibre point, the finite original later
family leaves an actual new-coordinate residue uncovered. Reducing
to the finite queried period and applying CRT supplies an integer
omitted by the entire original family.

The margin in F6 measures the source mass of positive fibres. It gives
no uniform lower bound on their positive values. Each individual finite
family has positive natural survivor density by periodicity, but no
uniform whole-period Haar-density floor is asserted here.

## The templates permit more than two global paths

Let D=3^11*5^7*p^6*product_(q in P minus{3,5,p})q^4 and set d=3D.
Choose one A-template residue a modulo D. At the three distinct complete
labels d*23^j, j=1,2,3, choose old residues a,a+D,a+2D modulo d, with
arbitrary new phases supplied by CRT. All three satisfy the same A
template, yet they are three distinct old residues modulo the same d.
No two global old paths represent all three. A fourth distinct label
may use the B template if both selectors are to occur.

This demonstrates the strictly broader allowed family, not a covering
example. Arbitrary first-root patterns, unrelated finite prefixes,
selectors changing between coordinates and additional prime supports
still require further arguments. More general prefix depths can be
used whenever their version of F5 is strictly less than delta_p; the
uniform depths11,7,6,4 are sufficient and are not claimed optimal.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_prefix_template_source.py

The consumer pins report517's exact five-role result, reconstructs the
worst/nonworst minimum and physical-prime error terms as rational
numbers, and compares the retained result. Its --output option writes
that result. It does not import the earlier producer or rerun geometry,
row certificates, profile weights or optimization. Input hashes identify
the inherited evidence; the coupling and source-measure arguments above
are separate ordinary mathematical proofs.
