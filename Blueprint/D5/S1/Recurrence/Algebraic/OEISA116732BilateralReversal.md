# Bilateral reversal for the A116732 companion

## Abstract

The unrounded A116732 companion extends uniquely to all integer indices, and the extension satisfies Somos's reversal identity u_n = −u_{2−n}.

**Definition 1.1 (The bilateral recurrence).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsRec`

*Formalization.* `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsRec` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

A function u from the integers to the integers satisfies the bilateral recurrence when u_n = u_{n−1} + u_{n−2} + u_{n−3} − u_{n−4} for every integer n, including negative n.

**Definition 1.2 (The initial values).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsInit`

*Formalization.* `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsInit` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

The initial values are u_0 = u_1 = u_2 = 0 and u_3 = 1.

**Theorem 1.3 (Unique extension and reversal).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

There is exactly one function u from the integers to the integers with these initial values that satisfies the bilateral recurrence, and every such function satisfies u_n = −u_{2−n} for every integer n. The trailing coefficient of the recurrence is −1, so a solution vanishing at 0, 1, 2 and 3 vanishes at every integer, by induction upward and downward. This gives uniqueness, and existence comes from reflecting the forward solution through index one. The characteristic polynomial is palindromic: comparing the recurrence at n and at 6 − n shows that n ↦ u_n + u_{2−n} again satisfies the recurrence. The recurrence at n = 3 forces u_{−1} = −1, so this sum vanishes at 0, 1, 2 and 3, hence everywhere, which is the identity. This is Corollary 7 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.24369110), which reproves the identity recorded by Michael Somos in A116732.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsInit`
- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.IsRec`
- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.result`
