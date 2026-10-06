# Zhang's one-deletion Lonely Runner family

Let `N = n - 1` and remove one speed `r` from `1, ..., N`.  Zhang's
Question 2.11 (arXiv:2608.13599v2) asks for the exact lower bound and equality
cases of the resulting Lonely Runner value.

**Theorem 1.1 (one-deletion bound and equality).**

For every `2 ≤ N`, `1 ≤ r ≤ N`,

$$
\frac1N\le \operatorname{lonelyValue}([N]\setminus\{r\}),
\qquad
\operatorname{lonelyValue}([N]\setminus\{r\})=\frac1N
\Longleftrightarrow r=N\ \lor\ N=2.
$$

*Proof.* Machine-checked in Lean as
`D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.result` (`✓ std3`). ∎

For `r > N/2`, the rational time `1/r` has every retained residue at least
one unit from an endpoint after division by `r`, hence gives a strict bound.
For `2r ≤ N`, the proof constructs `q` and `a` with
`N+r < q < 2N` and `a*r ≡ 1 (mod q)`.  The retained residues of `v*a/q` avoid
`0`, `1`, and `q-1`, giving distance at least `2/q > 1/N`.  The endpoint and
the `N=2` cases are sharp by the nearest-integer bound.

The formal definition uses the supremum over all real times, while the proof
uses explicit rational witnesses and proves a global `1/2` upper bound.  This
settles the registered one-deletion family only; it does not claim the
unrestricted Lonely Runner Conjecture.

*Source.* Yuhan Zhang, arXiv:2608.13599v2, Question 2.11 (2026).

*Resolves.* `Problems/zhang-2026-lonely-runner-one-deletion` (proved) by
`D5/S1/Phase/LonelyRunnerDeletion/OneDeletion.result`.

## Verified locator

- URL: https://arxiv.org/abs/2608.13599v2
- Locator: Question 2.11; Remark 2.8 and Proposition 2.10.
