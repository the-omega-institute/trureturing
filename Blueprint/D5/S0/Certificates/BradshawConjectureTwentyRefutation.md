# Bradshaw's Conjecture 20 is false

## Abstract

At a = 17, b = 7, the nonsquarefree input 125 satisfies Bradshaw's commutation equation.

**Definition 1.1 (The arithmetic derivative).**

$$\forall D \in (\mathbb{N} \to \mathbb{N}),\; (\operatorname{IsArithmeticDerivative}\left(D\right)) \Leftrightarrow ((\operatorname{D}\left(0\right) = 0) \land ((\operatorname{D}\left(1\right) = 0) \land ((\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow (\operatorname{D}\left(p\right) = 1)) \land (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{D}\left(m \cdot n\right) = \operatorname{D}\left(m\right) \cdot n + m \cdot \operatorname{D}\left(n\right)))))$$

*Formalization.* `D5/S0/Certificates/BradshawConjectureTwentyRefutation.IsArithmeticDerivative` (`✓ std3`).

*Citation.* Z. P. Bradshaw (2025). *On a Family of Solutions to Arithmetic Differential Equations Involving the Collatz Map*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf>.

*Commentary.*

Bradshaw, printed page 3: "We define the arithmetic derivative to be a non-linear derivation $D : \mathbb{N} \to \mathbb{N}$ on the set of natural numbers with the property that $D(1) = D(0) = 0$ and $D(p) = 1$ for all primes $p$. Explicitly, we define $D$ so that $D(mn) = D(m)n+mD(n)$ (1) for every $m, n \in \mathbb{N}$."

The predicate records the four properties in the order D(0) = 0, D(1) = 0, prime values, and the product rule. All inputs and values are natural numbers, including zero; Prime denotes Nat.Prime.

**Definition 1.2 (The generalized Collatz map).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{C}\left(a, b, n\right) = \operatorname{ite}\left(\operatorname{NatMod}\left(n, 2\right) = 1, \operatorname{NatDiv}\left(a \cdot n + b, 2\right), \operatorname{NatDiv}\left(n, 2\right)\right)$$

*Formalization.* `D5/S0/Certificates/BradshawConjectureTwentyRefutation.C` (`✓ std3`).

*Citation.* Z. P. Bradshaw (2025). *On a Family of Solutions to Arithmetic Differential Equations Involving the Collatz Map*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf>.

*Commentary.*

Bradshaw, printed page 16: "It should also be noted that similar problems can be formulated for the generalized Collatz functions $C_{a,b}(n) := \begin{cases}\frac{an+b}{2},&\text{if }n\text{ odd};\\\frac{n}{2},&\text{if }n\text{ even},\end{cases}$ with $a \equiv b (\mathrm{mod} 2)$."

The encoding C(a,b,n) uses exactly these two branches. NatDiv(x,y) is natural-number integer division, and NatMod(x,y) is the natural remainder. The expression ite(P,x,y) chooses x when P holds and y otherwise. For natural n, NatMod(n,2) = 1 means n is odd, and the other branch means n is even. The map is defined for all natural a,b,n; the claim imposes equal parity on a and b, so the fractions in the source quotation have exact integral values on their respective branches. The formal definition displayed above uses NatDiv for both quotients.

**Definition 1.3 (Conjecture 20 on positive inputs).**

$$(claim) \Leftrightarrow (\forall D \in (\mathbb{N} \to \mathbb{N}),\; (\operatorname{IsArithmeticDerivative}\left(D\right)) \Rightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{NatMod}\left(a, 2\right) = \operatorname{NatMod}\left(b, 2\right)) \Rightarrow ((1 \le n) \Rightarrow ((\operatorname{D}\left(\operatorname{C}\left(a, b, n\right)\right) = \operatorname{C}\left(a, b, \operatorname{D}\left(n\right)\right)) \Rightarrow (\operatorname{Squarefree}\left(n\right))))))$$

*Formalization.* `D5/S0/Certificates/BradshawConjectureTwentyRefutation.claim` (`✓ std3`).

*Citation.* Z. P. Bradshaw (2025). *On a Family of Solutions to Arithmetic Differential Equations Involving the Collatz Map*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf>.

*Commentary.*

Bradshaw, Conjecture 20, printed page 16: "The solutions to the commutation problem $D(C_{a,b}(n)) = C_{a,b}(D(n))$ are squarefree for every $a \equiv b (\mathrm{mod} 2)$."

The encoding quantifies over D : Nat to Nat satisfying all four defining properties and over natural a,b,n. Equal remainders modulo two encode the stated parity condition; Squarefree is Mathlib's predicate on natural numbers. The extra hypothesis 1 ≤ n makes claim weaker than the source statement, so refuting it refutes the source, and excludes the trivial n = 0 boundary. The intended domain of (a,b) is read as naturals of equal parity; the counterexample has a,b positive and odd with b < a, as in the source's five tested pairs.

**Theorem 1.4 (A nonsquarefree commuting input).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BradshawConjectureTwentyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bradshaw-arithmetic-derivative-collatz-squarefree-refutation` (refuted) by `D5/S0/Certificates/BradshawConjectureTwentyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bradshaw-arithmetic-derivative-collatz-squarefree-refutation","declaration_gid":"D5/S0/Certificates/BradshawConjectureTwentyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Z. P. Bradshaw (2025). *On a Family of Solutions to Arithmetic Differential Equations Involving the Collatz Map*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.pdf>.

*Commentary.*

An arithmetic derivative exists: for each n, sum k times NatDiv(n,p) over its prime factorization, where k is the multiplicity of p. The empty factorizations at zero and one give zero; prime factorization of a product gives the product rule, with zero factors treated separately. For every derivative satisfying the four properties, the prime values and product rule give D(25) = 10, D(125) = 75, D(533) = 54 and D(1066) = 641. These values follow from the properties alone. At a = 17, b = 7, C(17,7,125) = 1066 and C(17,7,75) = 641. Thus both sides of the commutation equation equal 641, although 125 = 5³ is divisible by 5² and is not squarefree.

## References

- Truth anchor: `D5/S0/Certificates/BradshawConjectureTwentyRefutation.C`
- Truth anchor: `D5/S0/Certificates/BradshawConjectureTwentyRefutation.IsArithmeticDerivative`
- Truth anchor: `D5/S0/Certificates/BradshawConjectureTwentyRefutation.claim`
- Truth anchor: `D5/S0/Certificates/BradshawConjectureTwentyRefutation.result`
