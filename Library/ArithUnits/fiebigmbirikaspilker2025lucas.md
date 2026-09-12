---
bibkey: fiebigmbirikaspilker2025lucas
authors: Morgan Fiebig, aBa Mbirika, Jürgen Spilker
year: 2025
title: "Period patterns, entry points, and orders in the Lucas sequences: theory and applications"
doi: null
url: https://arxiv.org/abs/2408.14632v2
claim: 'Conjecture 5.2. Set $U_n:=U_n(p,q)$, and let $m \geq 1$ and $n \in \mathbb{Z}$. Assume that both $p$ and $m$ are even. If $U_{2n} \equiv 0 \pmod{m}$ and $U_{2n+1} \equiv q^n \pmod{m}$, then exactly one of the following two conclusions occur: (i) $U_n \equiv 0 \pmod{m}$, or (ii) $U_n \equiv \frac{m}{2} \pmod{m}$ where $n = c \cdot \frac{e_U(m)}{2}$, where $c$ is some odd integer and $e_U(m)$ is the entry point of $m$ in $(U_n)_{n \geq 0}$.'
strata_touched:
  - D5/S1/Recurrence/LucasEvenDescent
license: citation-only
triage: anchor
---

# Period patterns, entry points, and orders in the Lucas sequences

The paper extends the modular theory of the Fibonacci and Lucas sequences to the
two-parameter Lucas sequences `U_n(p,q)` and `V_n(p,q)`, where `U_0 = 0`,
`U_1 = 1`, `V_0 = 2`, `V_1 = p`, and both satisfy `x_{n+1} = p*x_n - q*x_{n-1}`.
Its statistics are the period `pi(m)`, the entry point `e(m)`, and the order
`omega(m) = pi(m)/e(m)`.

Conjecture 5.2, quoted above, is the paper's own open problem, carried in
Section 5 ("Open questions and future work"). The paper attributes it to
observations by Diego Garcia-Fernandezsesma and Oliver Lippard together with
Mbirika, following the Problem Session of the 21st International Fibonacci
Conference; the index form in clause (ii) is credited to Lippard. It repairs a
statement whose sufficiency direction the paper shows holds only when `p` or `m`
is odd, and asks what happens when both are even.

Three conventions of the paper are inherited by the conjecture and are quoted
here because the third is load-bearing: the parameters satisfy `gcd(p,q) = 1`
with `p` and `q` nonzero; the sequences are nondegenerate, so `q != 0` and
`alpha/beta` is not a root of unity; and the moduli are restricted to those with
`gcd(q,m) = 1`, "for otherwise, the sequence may not be purely periodic
according to our definition", which is also what guarantees that `e_U(m)`
exists. The entry point is defined there as "the least integer `r>0` (if it
exists) such that `m` divides `S_r`".

The module proves the conjecture. It does not use the first two conventions; the
implication holds without any nonzero, coprimality or nondegeneracy restriction
on `p` and `q`, so the formal statement is more general than the conjecture in
those parameters. It does use `gcd(q,m) = 1`.

## Verified locator

- Abstract, version history and journal reference: https://arxiv.org/abs/2408.14632v2
- The conjecture and the three conventions were read in the LaTeX source obtained
  from https://arxiv.org/e-print/2408.14632v2 (`Conjecture 5.2` at the label
  `conj:aBa_Diego_Oliver`; the modulus convention at the label
  `conv:gcd_of_m_and_q_equals_1`).
- Journal reference as listed on that page: The Fibonacci Quarterly 63.2 (2025)
  345-376.
