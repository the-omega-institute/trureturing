# 60. A fixed positive cylinder cover across head profiles

Fix the actual seven-phase 154-class survivor set S from
[Chapter 59](59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md).
Keep its [complete original congruences](../frontier/source-budgets/uniform_phase_capacity_input.json),
all twenty named coordinate alphabets and their original heights. In the cylinder-cover
construction choose each whole-prefix versus child-cover decision using
the certified balanced profile, and likewise freeze each terminal
whole-coordinate versus safe-atom decision. After these choices are
fixed, the result is a cover by actual partial cylinders whose geometry
depends only on the original labels and these choices. At a core node,
choose its whole cylinder whenever that has price no greater than the
child cover. At a terminal safe set, ties choose the unrestricted
coordinate. These comparisons use the original balanced caps only.

Writing C for this finite multiset of selected cylinders, the construction
gives the pointwise inequality

    1_S <= sum_(c in C) 1_c.

Whole-prefix choices cover all their surviving descendants, child covers
include every actual coordinate value, and terminal product covers
include every actual allowed completion. Cylinders may overlap; the
pointwise inequality does not require disjointness.

Let c_A count the selected cylinders fixing exactly the coordinate set A.
Each such cylinder fixes full actual prime-power coordinates. Its mass
under any law with deterministic global product-cylinder bounds at new
full-height atom caps r'_p is at most product_(p in A)r'_p. Therefore

    mu(survivors) <= min(1,P(r')),
    P(r') = sum_A c_A product_(p in A)r'_p.             (P1)

Here r'_p is the cap on one atom of Z/p^(H_p)Z for **each of all twenty
coordinates**, including the seven core primes. The thirteen terminal
leaf primes do not exhaust the variables. The law may choose coordinates
adaptively and nonanticipatively; its deterministic cap holds conditional
on the complete transcript and on that choice. The global-cylinder
inequality from Chapter 59 then applies to every selected cylinder.

All c_A are nonnegative integers. The polynomial is multi-affine: each
coordinate is either unrestricted or fixed once in a cylinder. The cover
need not be optimal at the new caps, and no new-profile comparison is
assumed. Validity uses the same global-cylinder inequality as before,
so it continues to include every admissible adaptive sampling order.

The coefficients can be computed without listing the cylinders. A
whole-prefix choice has relative polynomial1 and a forbidden node has0.
A child split multiplies the sum of its child polynomials, including
actual-value multiplicities, by the variable r_p. At a complete core
node, each terminal coordinate contributes either1 or (q-d_q)r_q,
according to the frozen cover choice. Multiply those factors. Merge
terms with the same named-coordinate set by adding integer coefficients.
These recurrences count the chosen actual partial cylinders exactly.

For the certified seven-phase input, expansion yields38 monomials and
12533129880604949291 cylinders counted with their original identities.
At the balanced caps its value is exactly

    P(r)=696181396681816852739454137354543 /
         1086338369123261718750000000000000,

the original certified survivor upper bound. The
[complete polynomial certificate](../certificates/source_norms/source-budgets/positive_cylinder_polynomial.json)
records every integer coefficient and its named-prime support.

For any other profile with continuation allowances C',J' and threshold
T'>1, independently justify those allowances under the same actual joint
law. Changing the head caps does not preserve the old C, J or T
automatically. Define

    B'=C'+(J'-1)/(T'-1).

If P(r')<=B', then every legal law has

    epsilon+C'+(J'-1)/(T'-1)
      >= 1-P(r')+B' >=1.                              (P2)

Thus the same actual input supplies a reusable necessary condition
P(r')>B' for that sufficient certificate to pass. This is not a claim
that all new profiles satisfy the exclusion condition, nor that this
cut characterizes feasibility. It lets a future parameter search retain
the already established obstruction instead of re-solving this input
for every candidate profile. Intermediate depth caps may restrict the
laws further; their omission from this cut never strengthens a claimed
feasibility conclusion.


## Complete coefficient table

A mask m fixes coordinate i exactly when bit i is one, starting at bit 0.
The corresponding ordered primes are

    (3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73).

Thus each row contributes c_m times the product of r'_p over its set bits.
The mask applies to full prime-power coordinates at their original heights.

| Coordinate mask m | Integer coefficient c_m |
|---:|---:|
| 1 | 41 |
| 7 | 193113 |
| 15 | 5483178 |
| 31 | 786903165 |
| 63 | 75813227208 |
| 255 | 34805580850215 |
| 511 | 446452795718181 |
| 639 | 544601826394605 |
| 767 | 703738983880422 |
| 895 | 153482304011400 |
| 1023 | 985268657297925 |
| 1279 | 13320682245607968 |
| 1535 | 128696309521428726 |
| 1663 | 2136640024709190 |
| 1791 | 7076598639394284 |
| 1919 | 658143314829000 |
| 2047 | 12735852820891200 |
| 8447 | 147628926799200 |
| 8831 | 2478878602611840 |
| 8959 | 31744140760997280 |
| 9087 | 18176740633846080 |
| 9215 | 90266957230301280 |
| 25087 | 1487202905076065100 |
| 33407 | 12095667688374270 |
| 33535 | 130184144559342720 |
| 33663 | 3400257572712000 |
| 33791 | 22865928444859500 |
| 139391 | 92500723181512800 |
| 139519 | 96901981426819800 |
| 139647 | 957082086318619800 |
| 139775 | 457792963164167400 |
| 140415 | 426526668005545800 |
| 140543 | 203796476064442800 |
| 140671 | 2626839105562009800 |
| 140799 | 328254213585375000 |
| 140927 | 1567359836562920400 |
| 141055 | 184347566349546600 |
| 141183 | 3625672357567260000 |


## Exact reproduction and limits

The [producer](../frontier/source-budgets/positive_cylinder_polynomial.py)
counts the selected geometry with exact actual-value multiplicities.
The [independent verifier](../frontier/source-budgets/verify_positive_cylinder_polynomial.py)
imports neither that producer nor its partition recurrence. It evaluates
each actual local core leaf, freezes the same balanced-price choices,
and adds each selected child separately. Its
[independent certificate](../certificates/source_norms/source-budgets/positive_cylinder_polynomial_verification.json)
checks all 38 coefficients individually, their complete sum, and the
exact original balanced evaluation. The cost recurrence uses 35,558
states and 3,191,384 actual local leaf evaluations; expansion uses 5,950
coefficient states, 399,129 actual children and 333,420 additions.
Both programs expose `--write` and `--check` under `python3 -B -I -S -O`.

Changing the original phases, numerical moduli or coordinate alphabets
requires a new geometric covering justification. At new caps P can exceed
one, and the useful bad-mass lower bound is max(0,1-P). The cut is a
necessary condition for the stated sufficient budget; it does not prove
failure of every profile or characterize all feasible laws. These are
ordinary mathematical deductions and exact computations, with no new
Lean declaration or claim that unrestricted Erdős #7 is settled.
