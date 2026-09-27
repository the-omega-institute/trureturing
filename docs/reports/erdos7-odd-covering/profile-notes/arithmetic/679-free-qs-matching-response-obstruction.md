# Releasing all ten qs labels defeats this matching-response gate

For one admissible native central layout, adding every `qs` event to the existing actual edge-union deletion produces a matching-response table whose complete gate is less than `1/10^10` for **every** cell field `0 <= theta <= 1`. In particular it cannot reach the inherited head threshold `193/100000`. This obstruction does not depend on weak-marker priority, a field library, or a fixed parametric form for the field.

The result concerns the stated response construction and its complete comparison gate. It is not an upper bound on the actual survivor density, an impossibility theorem for all source constructions, or an odd covering. Tightening the actual joint-event bounds, changing the response construction, or changing a duly justified complete comparison remains outside this certificate.

## One globally fixed layout and a realizable central corner

Use `Q = (7,11,13,17,19)` and its ten lexicographically ordered unordered edges. The native nulls are `(3,5)`, the weak leaves are `(4,6)`, and the square-star roles at 7 are `(R,C,ell) = (0,2,4)`. All ten separately labelled `9qs` originals have central leaf `alpha_e = 5`, fixed once for the whole source. In root-major coordinates, the literal residues are

    l -> floor(l/3) + 3(l mod 3) modulo 9,
    m -> floor(m/5) + 5(m mod 5) modulo 25.

Thus leaf 5 means `7 mod 9`, leaf 4 means `4 mod 9`, and the central pure square nulls both mean literal residue 1. The corner laws are

    w = (2,2,2,0,1,2)/9,
    v_5 = 0, v_6 = 3/75, v_m = 4/75 otherwise.

Delete the central 15 rectangle `l < 3, m < 5`. There are 80 remaining cells. As in Report659's explicit source, distribute each leaf's mass uniformly inside that leaf. These actual laws avoid the pure classes `2 mod 3`, `1 mod 9`, `4 mod 5`, `1 mod 25`, and satisfy the same density and all-depth selector caps. No assertion that arbitrary abstract comparison corners are actual laws is required.

The forty linear stars `cq`, with `c in {3,5,15,9,25,45,75,225}`, retain their common-root incidences. The ten `qs` incidences are released in addition to all previously released square-star, square-pair and `9qs` incidences. Every original numerical modulus keeps its own globally fixed residue.

For an explicit compatibility witness, at each `q in Q` take pure root 0 and common deleted live root `t_q = 1`. For every `cq`, choose one residue with central component `0 mod c` and outside root `1 mod q`. Give `qs` residue 2, `q^2 s` residue 4, and `q s^2` residue 5; give `9qs` central component `7 mod 9` and both outside roots 3. At each q, choose square-star central components `0 mod 3`, `2 mod 5`, `4 mod 9`, respectively, and outside square prefix 2. CRT simultaneously supplies these distinct originals; the verifier checks all 105 listed numerical labels. In particular the chosen square7 role and all labelled alpha values coexist with the retained forty incidences. On each edge the four first-root pairs are `(2,2)`, `(3,3)`, `(4,4)`, and `(5,5)`, which the verifier checks individually. Thus, when `9qs` is active, these four actual edge events are pairwise disjoint; the witness does not rely on trivial within-edge containment. These assignments establish admissibility, not a covering or attainment of the response caps.

## The same-source response construction

Write

    r_q = 1/(q-1), a_q = 1/[q(q-2)], d_{qs} = r_q r_s,
    Z_7(l,m) = 5/6 - [1_(floor(l/3)=0) + 1_(floor(m/5)=2) + 1_(l=4)]/35,
    Z_q = (q-2)/(q-1) - 2 a_q, q > 7.

In each cell, combine the four actual edge events `q^2 s`, `q s^2`, `qs`, and the active `9qs`. Their product-source cap is

    beta_{qs}(l,m) = a_q r_s + r_q a_s + d_{qs} + d_{qs} 1_(l=5).

The constant `d_{qs}` is the new cost of deleting the actual `qs` event. It is not a charge in a different source. The union estimate permits arbitrary endpoint values and overlaps. On the simultaneous full box, with every increment active and `Z_7 >= 157/210`,

    1 - sum_{q<s} beta_{qs}/(Z_q Z_s)
      >= 3268184199595333/4382751255268945 > 0.

Hence the existing strict induced matching-source construction used in Reports623/629/632/659 applies. It provides one actual pair-avoiding submeasure in each cell, with the empty response and simultaneous query upper responses

    H_T(c) = sum_{J matching in Q\T} (-1)^|J|
               product_{e in J} beta_e(c)
               product_{q in Q\(T union vertices(J))} Z_q(c).

On five coordinates, matchings have size at most two. The source and every query use this same table, and a single `theta(c)` multiplies all its responses. Since `qs` was formerly null by root incidence and is now null by actual pair avoidance, the complete 512-fee array stays unchanged. Retain every original selector, all remaining-original tails, all nonunit support charges and the four guarded `9q^2` debits.

Explicitly, take `g = 200163067/201247200`. The base 512 coefficients are Report640's pinned `combined512_coefficients`; add `g a_q` at index `288 + 2^i` for indices `i = 1,2,3,4` of q in Q. Let `C_j` be this final array. For each coordinate, the four selector levels are whole measure, root-restricted measure, weighted leaf, and deep leaf. In integer denominators 9 and 75 the deep numerators are 9 and 60; a deep selector is not multiplied by a leaf weight. There are 559 original central selectors and 17,888 mode/support/selector readings.

The complete gate is

    G(theta) = g sum_c w_l v_m H_empty(c) theta_c
               - sum_{j=0}^{511} C_j max_k sum_c R_{jk}(c) theta_c,

where `R_{jk}(c)` is that original selector's coefficient times `H_{T_j}(c)`. For the constant-one field, exact evaluation gives

    G(1) = -1793736311487940720438438757
             /82770023646214483138560000000
         = -0.021671327764202927... .

This negative value alone would not establish the claimed obstruction. The following bound does.

## A rational bound valid for every field

Choose nonnegative rational multipliers `lambda_{jk}` with

    sum_k lambda_{jk} <= C_j for every j.

All selector responses are nonnegative. Therefore, for every `theta in [0,1]^80`,

    C_j max_k sum_c R_{jk}(c) theta_c
      >= sum_k lambda_{jk} sum_c R_{jk}(c) theta_c.

Set

    D_c = g w_l v_m H_empty(c) - sum_{j,k} lambda_{jk} R_{jk}(c).

Then the universal upper bound is

    G(theta) <= sum_c D_c theta_c <= sum_c max(0,D_c).

The numerical certificate supplies 354 nonzero multipliers with common denominator `10^12`. Each row records the original mode, outside support, literal x-menu index, literal y-menu index and nonnegative integer numerator. The standard-library verifier reconstructs every response by a vertex-deletion recurrence, verifies every one of the 512 fee budgets exactly and obtains

    sum_c max(0,D_c)
      = 28213946244578637328303303
          /718489788595611832800000000000000000
      < 1/10000000000
      < 193/100000.

No numerical LP optimality statement is used. The zero field gives gate zero, but the certificate proves the displayed small positive upper bound, not that the exact optimum is zero.

Because this rules out even unrestricted cell fields at one actual corner and one fixed layout, adding a field library or weakening priority constraints cannot make this response-table construction prove the desired uniform release of all ten qs incidences. The earlier 678 result, which retains those ten incidences, is untouched.

## Portable exact evidence

The self-contained multiplier and coefficient container is [free_qs_matching_response_obstruction.json](../../frontier/cover-geometry/free_qs_matching_response_obstruction.json). Its source640 hash is checked against the actual existing numerical input. The standard-library verifier [free_qs_matching_response_obstruction_verify.py](../../frontier/cover-geometry/free_qs_matching_response_obstruction_verify.py) accepts explicit `--candidate`, `--source640`, and `--output` paths. Run it with

    python3 -I -S -B -O free_qs_matching_response_obstruction_verify.py \
      --source640 remaining33_global_root_exclusion_certificate.json

Its 4,843 explicit checks pass with Python assertions disabled. The output [free_qs_matching_response_obstruction_verification.json](../../frontier/cover-geometry/free_qs_matching_response_obstruction_verification.json) records the exact inequalities and the simultaneous CRT phase witness. It imports no optimizer and no discovery program. The LP was only a way to propose the rational multipliers; their mathematical force is the elementary inequality above and exact replay. This is ordinary mathematics and finite rational verification, not new Lean verification.

An independently written [second verifier](../../frontier/cover-geometry/free_qs_matching_response_obstruction_independent.py) and [result](../../frontier/cover-geometry/free_qs_matching_response_obstruction_independent.json) pass4,395 exact checks. It enumerates all26 matchings directly instead of using the vertex recurrence, reconstructs all559 selectors and512 budgets, and obtains the identical unit gate and universal upper bound. It independently checks all105 numerical phases, the four disjoint first-root pairs on every edge, and the realizable central leaf densities. It reads the numerical certificate and phase list, not the first verifier implementation. Both verifiers use the standard library only. Their canonical outputs reproduce the retained data byte for byte.

From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_qs_matching_response_obstruction_verify.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/free_qs_matching_response_obstruction_independent.py
```
