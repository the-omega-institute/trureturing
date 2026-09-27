# The complete square has a feasible dual above the target

For the same actual109 source and all512 screens as
[Report704](704-a-full-joined-dual-excludes-the-retention-target.md), replacing
the selected33-label charge by its COMPLETE square gives the exact bound

    G_full(f sigma)<=U_full
      =118279958795823862369936857351498127502543
       /52202124862381649659046400000000000000000000
      =0.0022658073614367333... .                    (FS1)

This holds for every jointly measurable retention0<=f<=1, including arbitrary
digit depth. It remains ABOVE the target193/100000. It neither excludes that
target nor supplies a retained field reaching it. No optimum is claimed.
The result is an ordinary mathematical deduction with exact integer checking,
not new Lean verification or a resolution of unrestricted Erdős#7.

## Complete ownership and the stronger criterion

Keep the same33 numerical query labels as699: eight central labels
{3,5,9,15,25,45,75,225}, five exterior prime labels7,11,13,17,19, and twenty
pair-product labels, excluding3*5 which is already central. One complete
layout a chooses ONE residue for each label, shared by all its occurrences.
Let I_(d,a) be that label's incidence indicator and n_a=sum_d I_(d,a). Then

    L_full,a=n_a^2+2n_a
            =3 sum_d I_(d,a)+2 sum_(d<e) I_(d,a)I_(e,a),
    K_full(nu)=max_a integral L_full,a dnu.         (FS2)

There are33 unary atoms and528 unordered pairs,561 occurrences of total
weight1155. The699 charge used all33 unaries and88 pairs, of weight275.
The440 added pairs have weight880. They are added exactly once, without
replacing any numerical label or assigning a second phase to an occurrence.

Let C_j be the unchanged complete fee vector, including the original loss
terms and all four fullmode8 additions. Keep c=1084133/201247200 and g=1-c.
If v_full,j is the full selected ownership in screen j, set

    r_full,j=C_j-c v_full,j,
    G_full(nu)=g nu(1)-sum_j r_full,j S_j(nu)-c K_full(nu). (FS3)

All512 remaining coefficients are nonnegative:506 positive and6 zero.
The zero groups are0,32,64,128,160,256. More precisely, the unchanged complete
query weights W_j satisfy

    C_j-c v_full,j=(C_j-c W_j)+c(W_j-v_full,j),
    C_j-c W_j>=0,  W_j-v_full,j>=0.               (FS4)

The verifier recomputes these identities. Thus original losses and every
unselected all-height query term retain their budget; the selected atoms
are not subtracted from an inventory which lacks them. The actual source
resolves the selected central depths and the declared interface includes
the complete higher query tails.

The comparison with699 is in the direction of a STRONGER gate. Write
v_partial and K_partial for its old selection. On the same finite measure
with finite charged screens, each complete layout's added charge is
nonnegative and bounded by sum_j(v_full,j-v_partial,j)S_j. Consequently

    0<=K_full-K_partial<=sum_j(v_full,j-v_partial,j)S_j,
    G_full-G_partial
      =c[sum_j(v_full,j-v_partial,j)S_j-(K_full-K_partial)]>=0. (FS5)

The maximizing layouts need not agree; the pointwise bound for EVERY layout
proves the upper difference bound. Report704's upper bound for G_partial
therefore cannot serve as an upper bound for G_full. FS1 uses a new dual for
the full ownership and its new remaining coefficients.

## A legal dual does not require a maximizing-layout oracle

For each positive r_full,j, take a probability mixture of admissible query
rows q_jt. Separately take one probability law on complete layouts. With
probabilities alpha_jt and beta_a, their debit function is

    d=sum_j r_full,j sum_t alpha_jt q_jt
       +c sum_a beta_a L_full,a.

Every query mixture is bounded by its complete screen, and the layout
mixture is bounded by K_full. Hence on the SAME source,

    G_full(f sigma)<=integral f(g-d) d sigma
                    <=integral[g-d]_+ d sigma=U_full. (FS6)

This certificate has249835 query rows and229 positive complete-layout
probabilities. Each of its507 probability budgets has integer numerators
summing to10^12. All2125830 positive source categories are integrated, with
544253 positive residuals and source mass305684996597/646498195200.

The witness SHA256 is
`c54760c08e4ea7940a9b00c9b44c63625d5d532f1603e2d401243784082dda0a`.
The exact residual sum gives FS1. Finitely many legal complete layouts
suffice: they lower-bound the subtracted K_full. A positive primal claim
would require the opposite bound on the TRUE maximum, which is not supplied
by FS6 or by taking the sign of its residual.

For each pair, generalized CRT decides phase compatibility BEFORE pooling
free roots. An incompatible pair contributes zero, even if both distinct
root residues would receive the same pooled token. Pooling applies the same
root permutation to every incident numerical label in one complete layout.
It therefore averages legal whole layouts; it does not multiply separately
averaged pair marginals.

## Arbitrary depth and the declared common-source class

The reduction in689 preserves every joint central depth-two and exterior
first-root atom mass, and does not increase the complete higher screens.
Every full-square atom, including pairs involving three or four exterior
coordinates, is constant on these same JOINT atoms. Redistribution therefore
preserves every layout charge and K_full. Whole-layout root pooling cannot
increase K_full, by equivariance and convexity. The source is invariant and
all remaining fees are nonnegative, so these operations cannot decrease the
gate and preserve domination by sigma. FS6 on the finite category interface
therefore proves FS1 for arbitrary-depth retentions. If a positive-fee screen
is infinite, the gate is minus infinity and the bound is immediate.

The common-source transfer also extends under EXACTLY the hypotheses stated
in704: keep the109 original phases, actual predicate Phi, central survivor
support S, normalizers and complete fees. Allow one joint central measure
nu0<=(8/3)Haar|S and ONE common exterior product of Borel probabilities nu_q,
supported off root0 and assigning mass1/(q-1) to every other root. Exterior
laws may be singular; they may not vary by central cell or by query.

Report693(MA1--MA2) redistributes the input using the OLD conditional reference
laws while preserving each joint atom mass. The weights bound a whole selector
sum with one global descendant tuple. Since full-square atoms are constant on
these joint atoms, the same argument preserves every selected charge; it does
not require an exterior density. Subsequent pooling again cannot increase
the charged maxima. This supplies the measure-level transfer, in addition to
the finite arithmetic below.

For each old category mass m_z, multiply its positive residual by

    R_(l,m)=(82/81 if l=4 else1)(1876/1875 if m=10 else1)

before summing the eleven disjoint actual branches. There is no exterior
root1, or exactly one exterior root1 with its special/other child. If their
weighted residual sums are C*,A*_q,B*_q, the common-reference bound is

    C*+sum_q max(q A*_q, q B*_q/(q-1)).           (FS7)

This is the maximum over a SINGLE common tuple0<=t_q<=q of
C*+sum_q[A*_q t_q+B*_q(q-t_q)/(q-1)]. The certificate recomputes all branch
sums; all five slopes are negative, so the common endpoint is t_q=0 for all q.
With the old central reference fixed, the result is

    V_full=4311420765150753542366884950935606544727
            /1870582105768417813094400000000000000000000
          =0.002304855131381502... .

Allowing the stated joint central variation gives

    W_full=29822099110997316737073869531830137813169
            /12927496237421662512000000000000000000000000
          =0.0023068735479241736... .              (FS8)

These remain above the target. Separate marginal caps cannot replace the
joint central cap, and independent per-cell source choices are not included.

## Exact replay and remaining question

The [witness](../../frontier/cover-geometry/joined33_full_square_witness.json)
contains the fixed rational budgets, complete layouts and source identities.
The existing [dual verifier](../../frontier/cover-geometry/joined33_full_dual_verify.py)
also checks this block, reusing the pinned exact source reconstruction and
arbitrary-precision integer transform. It checks all561 atoms, all512 budget
identities, every probability budget and every positive source category.
From the repository root, with NumPy installed:

```sh
python3 -I -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joined33_full_dual_verify.py --block full-square
```

The [result](../../frontier/cover-geometry/joined33_full_square_verify.json)
separates exact certificate validity from the Boolean `below_target`.
The canonical full-square replay passes1624770 explicit checks.
The default `joined` mode retains704's smaller atom selection and strict
target checks; its exact bounds are unchanged. An independent mathematical
audit checked the comparison direction and common-source transfer, and an
independent small computation reconstructed561 atoms and512 budgets with
explicit compatible and incompatible CRT controls. These supplement the
ordinary proof; they do not turn the finite computation into Lean verification.

What remains unresolved here is whether this stronger complete-square gate
reaches193/100000, or whether a different valid dual excludes that target.
Either outcome would concern this source and criterion. The unrestricted
problem still requires arbitrary phases, heights and prime supports to be
handled under one actual source and one global original-label assignment.
