---
bibkey: bradshaw2025collatz
authors: Z. P. Bradshaw
year: 2025
title: "On a Family of Solutions to Arithmetic Differential Equations Involving the Collatz Map"
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf
claim: "Conjecture 20: the solutions to the generalized Collatz commutation problem are squarefree for every pair of parameters of equal parity."
strata_touched:
  - D5/S0/Certificates/BradshawConjectureTwentyRefutation
license: citation-only
triage: anchor
---

# Arithmetic differentiation and the generalized Collatz map

Z. P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences **28** (2025),
Article **25.1.8**.

Printed page 3 defines the arithmetic derivative:

> We define the arithmetic derivative to be a non-linear derivation
> $D : \mathbb{N} \to \mathbb{N}$ on the set of natural numbers with the property
> that $D(1) = D(0) = 0$ and $D(p) = 1$ for all primes $p$. Explicitly, we define
> $D$ so that $D(mn) = D(m)n + mD(n)$ (1) for every $m, n \in \mathbb{N}$.

Printed page 16 defines the generalized Collatz functions:

> It should also be noted that similar problems can be formulated for the
> generalized Collatz functions $C_{a,b}(n) := \begin{cases}\frac{an+b}{2}, & \text{if }n\text{ odd}; \\ \frac{n}{2}, & \text{if }n\text{ even},\end{cases}$
> with $a \equiv b \pmod{2}$.

Conjecture 20, printed page 16:

> The solutions to the commutation problem $D(C_{a,b}(n)) = C_{a,b}(D(n))$ are
> squarefree for every $a \equiv b \pmod{2}$.

The formal predicate lists the four derivative properties in the order
$D(0)=0$, $D(1)=0$, prime values, and the product rule. The formal map uses
natural-number integer division and the odd test `n % 2 = 1`. For parameters
of equal parity, each selected branch agrees with the source formula.

The encoded claim quantifies over arithmetic derivatives and natural
$a,b,n$ of equal parameter parity. The extra hypothesis $1 \le n$ makes the
claim weaker than the source statement, so refuting it refutes the source,
and excludes the trivial $n=0$ boundary. At $(a,b,n)=(17,7,125)$ both sides
of the commutation equation equal $641$, but $125=5^3$ is not squarefree.
These parameters are positive and odd with $b<a$, as in the five pairs
tested in the source.

## Verified locator

- URL: https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf
- Journal of Integer Sequences 28 (2025), Article 25.1.8.
- Printed page 3: Section 2, definition of the arithmetic derivative, equation (1).
- Printed page 16: generalized Collatz functions and Conjecture 20.
- The article has no DOI; the journal URL is the stable locator.
