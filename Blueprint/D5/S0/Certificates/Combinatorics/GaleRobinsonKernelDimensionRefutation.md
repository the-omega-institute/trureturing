# Beluhov's invariant-kernel dimension conjecture fails at type (1,3,6)

## Abstract

Over the rational-function field Q(a,b,c), the proper Gale--Robinson type (1,3,6) has at least six independent elements in its parity-gauge invariant kernel. Beluhov's Conjecture 3 predicts five.

**Definition 1.1 (Independent parameter ring).**

$$Parameters = \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(3\right), \mathbb{Q}\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.Parameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

The three variables of Parameters are independent indeterminates over Q. This is the polynomial representation of the three Gale--Robinson coefficients, rather than a numerical assignment.

**Definition 1.2 (Coefficient field).**

$$K = \operatorname{FractionRing}\left(Parameters\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.K` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 2, page 5: "let 𝒜Frac = ℤ(α) be the field of all integer-coefficient rational functions of α₁, α₂, …, α⌊n/2⌋." For the three-term Gale--Robinson recurrence, K is Q(a,b,c), the fraction field of Q[a,b,c], equivalently the field of integer-coefficient rational functions in these three variables.

**Definition 1.3 (First coefficient).**

$$a = \operatorname{algebraMap}\left(Parameters, K\right)\left(\operatorname{X}\left(0\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

a is the image of the first polynomial variable under the canonical algebra map Parameters to K. X in this formula has variable type Fin(3) and coefficient ring Q.

**Definition 1.4 (Second coefficient).**

$$b = \operatorname{algebraMap}\left(Parameters, K\right)\left(\operatorname{X}\left(1\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

b is the image of the second polynomial variable under the same algebra map.

**Definition 1.5 (Third coefficient).**

$$c = \operatorname{algebraMap}\left(Parameters, K\right)\left(\operatorname{X}\left(2\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

c is the image of the third polynomial variable under the same algebra map.

**Definition 1.6 (Gale--Robinson type).**

$$GRType = \operatorname{record}\left(\operatorname{n1} : \mathbb{N}, \operatorname{n2} : \mathbb{N}, \operatorname{n3} : \mathbb{N}\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.GRType` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 10, page 23: "Let 𝐧 = (n₁, n₂, n₃) with n₁, n₂, n₃ being positive integers such that n = n₁ + n₂ + n₃." GRType is a record with three natural-number fields n₁, n₂ and n₃. record lists the field names and their types; these names are labels, not free variables. Positivity is required by proper. n1(t), n2(t), n3(t) denote the corresponding projections.

**Definition 1.7 (Order of a type).**

$$\forall t : GRType, \operatorname{order}\left(t\right) = \operatorname{n1}\left(t\right) + \operatorname{n2}\left(t\right) + \operatorname{n3}\left(t\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.order` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

The order is the sum of the three entries.

**Definition 1.8 (Proper types).**

$$\forall t : GRType, (\operatorname{proper}\left(t\right)) \Leftrightarrow ((0 < \operatorname{n1}\left(t\right)) \land ((0 < \operatorname{n2}\left(t\right)) \land ((0 < \operatorname{n3}\left(t\right)) \land ((\operatorname{gcd}\left(\operatorname{n1}\left(t\right), \operatorname{gcd}\left(\operatorname{n2}\left(t\right), \operatorname{n3}\left(t\right)\right)\right) = 1) \land ((\operatorname{n1}\left(t\right) \ne \operatorname{n2}\left(t\right)) \land ((\operatorname{n1}\left(t\right) \ne \operatorname{n3}\left(t\right)) \land (\operatorname{n2}\left(t\right) \ne \operatorname{n3}\left(t\right))))))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.proper` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 10, page 24: "We call a type 𝐧 proper if it is primitive and n₁, n₂, n₃ are pairwise distinct." Page 23 defines primitive by gcd(n₁,n₂,n₃) = 1. The formula includes the positive-entry condition from the definition of a type. gcd(n1(t),gcd(n2(t),n3(t))) is the joint gcd; all three distinctness conditions are present.

**Definition 1.9 (Finite exponent carrier).**

$$\forall n : \mathbb{N}, \operatorname{Exp}\left(n\right) = \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n + 1\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.Exp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Exp(n) is the function type Fin(n) to Fin(n+1). val extracts a Fin element's natural-number label, or a subtype's underlying element, according to its argument. Every exponent in a degree-n monomial is at most n, so this finite carrier retains all relevant monomials.

**Definition 1.10 (Parity-gauge constraints).**

$$\forall n : \mathbb{N}, \forall d : \operatorname{Exp}\left(n\right), (\operatorname{admissible}\left(d\right)) \Leftrightarrow ((\sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{val}\left(d\left(i\right)\right)) = n) \land ((\sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{val}\left(i\right) \cdot \operatorname{val}\left(d\left(i\right)\right)) = \operatorname{natDiv}\left(n \cdot \operatorname{natSub}\left(n, 1\right), 2\right)) \land ((\operatorname{mod}\left(n, 2\right) = 1) \Rightarrow ((\sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 0, \operatorname{val}\left(d\left(i\right)\right), 0\right)) = \operatorname{natDiv}\left(n + 1, 2\right)) \land (\sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(\operatorname{mod}\left(\operatorname{val}\left(i\right), 2\right) = 1, \operatorname{val}\left(d\left(i\right)\right), 0\right)) = \operatorname{natDiv}\left(n, 2\right))))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.admissible` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 5, page 11: "This is equivalent to each exponent tuple (d₀, d₁, …, dₙ₋₁) which occurs in Φ satisfying d₀e₀ + d₁e₁ + ⋯ + dₙ₋₁eₙ₋₁ = e₀ + e₁ + ⋯ + eₙ₋₁ for all integer e ∈ ℰ." Section 2, page 5 gives the even-order basis 1,i and the odd-order basis i,i mod 2,(i+1) mod 2. The formula states the degree and index-weight conditions and, for odd n, both parity-weight conditions. Section 10, page 24 says that ℰ depends only on the parity of n; this is the parity-only reading used here. mod is natural-number remainder; natSub is natural subtraction truncated at zero; natDiv is natural integer division, so natDiv(r,2) is floor(r/2), never rational division. ite(c,t,f) chooses t if c and f otherwise.

**Definition 1.11 (Gauge-homogeneous domain subspace).**

$$\forall n : \mathbb{N}, \operatorname{upsilon}\left(n\right) = \operatorname{span}\left(K, \operatorname{range}\left((\lambda d : \{r : \operatorname{Exp}\left(n\right) \mid \operatorname{admissible}\left(r\right)\}, \operatorname{monomial}\left(\operatorname{Finsupp.equivFunOnFinite.symm}\left((\lambda i : \operatorname{Fin}\left(n\right), \operatorname{val}\left(\operatorname{val}\left(d\right)\left(i\right)\right))\right), 1\right))\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.upsilon` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 5, page 11: "The polynomials Φ which satisfy our additional constraint form a linear subspace Υ⊠ of Υ." upsilon(n) is the K-span of the unit-coefficient monomials satisfying admissible. toFinsupp denotes the existing Mathlib equivalence Finsupp.equivFunOnFinite.symm from functions on Fin(n) to finitely supported functions. range is the image of its displayed function; monomial(e,r) has exponent e and coefficient r.

**Definition 1.12 (Polynomial variables).**

$$\forall n : \mathbb{N}, \forall i : \mathbb{N}, \operatorname{x}\left(n, i\right) = \operatorname{ite}\left(i < n, \operatorname{X}\left(\operatorname{Fin.mk}\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.x` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

x(n,i) is X at label i when i<n, and zero otherwise, in MvPolynomial(Fin(n),K). finMk denotes Fin.mk and constructs a bounded index, with the branch inequality supplying its bound. This total extension leaves every variable of a proper type's recurrence inside its index range.

**Definition 1.13 (The Gale--Robinson recurrence form).**

$$\forall t : GRType, \operatorname{quadratic}\left(t\right) = \operatorname{C}\left(a\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n1}\left(t\right)\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n2}\left(t\right) + \operatorname{n3}\left(t\right)\right) + \operatorname{C}\left(b\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n2}\left(t\right)\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n3}\left(t\right) + \operatorname{n1}\left(t\right)\right) + \operatorname{C}\left(c\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n3}\left(t\right)\right) \cdot \operatorname{x}\left(\operatorname{order}\left(t\right), \operatorname{n1}\left(t\right) + \operatorname{n2}\left(t\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.quadratic` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 10, page 23 gives sᵢsᵢ₊ₙ = a₁sᵢ₊ₙ₁sᵢ₊ₙ₂₊ₙ₃ + a₂sᵢ₊ₙ₂sᵢ₊ₙ₃₊ₙ₁ + a₃sᵢ₊ₙ₃sᵢ₊ₙ₁₊ₙ₂. C embeds an element of K as a constant polynomial. The three coefficients are encoded by a,b,c, and the complementary indices are sums of the other two type entries. In particular the last term for (1,3,6) is c X₆ X₄.

**Definition 1.14 (Homogenized shift substitution).**

$$\forall t : GRType, \forall i : \operatorname{Fin}\left(\operatorname{order}\left(t\right)\right), \operatorname{substitution}\left(t, i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 < \operatorname{order}\left(t\right), \operatorname{x}\left(\operatorname{order}\left(t\right), 0\right) \cdot \operatorname{X}\left(\operatorname{Fin.mk}\left(\operatorname{val}\left(i\right) + 1\right)\right), \operatorname{quadratic}\left(t\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.substitution` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

substitution(t,i) replaces Xᵢ by X₀Xᵢ₊₁ for every nonterminal index and by quadratic(t) for the terminal index. The substitution keeps the source's zero-based variable labels.

**Definition 1.15 (The linear invariant operator).**

$$\forall t : GRType, \forall P : \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(\operatorname{order}\left(t\right)\right), K\right), \operatorname{phi}\left(t\right)\left(P\right) = \operatorname{x}\left(\operatorname{order}\left(t\right), 0\right)^{\operatorname{natSub}\left(\operatorname{order}\left(t\right), 2\right)} \cdot \operatorname{quadratic}\left(t\right) \cdot P - \operatorname{aeval}\left(\operatorname{substitution}\left(t\right)\right)\left(P\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.phi` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 5, page 10 defines φ(Φ) = x₀^(n−2) R Φ − Φ(x₀x₁,x₀x₂,…,x₀xₙ₋₁,R), where R is the recurrence's quadratic form. phi is the K-linear map given by multiplication by x₀^(n−2)R minus evaluation at the homogenized substitution. aeval fixes coefficients in K. It is defined on the whole polynomial ring and then restricted through omega to upsilon(n); the source defines the operator on the homogeneous subspace.

**Definition 1.16 (Restricted kernel).**

$$\forall t : GRType, \operatorname{omega}\left(t\right) = \operatorname{inf}\left(\operatorname{upsilon}\left(\operatorname{order}\left(t\right)\right), \operatorname{ker}\left(\operatorname{phi}\left(t\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.omega` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Section 5, page 11: "Let Ω⊠ be the kernel of φ over Υ⊠." inf denotes submodule intersection. omega(t) is the intersection of upsilon(order(t)) and the kernel of phi(t), viewed as a K-submodule of the polynomial ring. Thus its elements satisfy both domain membership and the actual polynomial identity phi(t)(Φ)=0.

**Definition 1.17 (Beluhov Conjecture 3).**

$$(claim) \Leftrightarrow (\forall t : GRType, (\operatorname{proper}\left(t\right)) \Rightarrow (\operatorname{finrank}\left(K, \operatorname{omega}\left(t\right)\right) = \operatorname{natDiv}\left(\operatorname{order}\left(t\right), 2\right)))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.claim` (`✓ std3`).

*Citation.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

Conjecture 3, page 24: "For every proper type 𝐧 of order n, it holds that dim Ω⊠ = ⌊n/2⌋." The encoding quantifies over all proper GRType records. Module.finrank is the dimension over K. It uses the source's stated parity-only gauge space and independent coefficients, without a finite-field specialization. Natural integer division order(t)/2 encodes the floor.

**Theorem 1.18 (Refutation at type (1,3,6)).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nikolai Beluhov (2026). *Diamond Determinants and Somos Sequences*. URL: <https://arxiv.org/abs/2602.24239v2>.

*Commentary.*

The type (1,3,6) is proper and has order 10. Six explicit polynomials H₀,…,H₅ satisfy the degree-10, index-weight-45 constraints and phi(Hⱼ)=0. Their coefficients at exponent tuples 1111111111, 2011111021, 2101111012, 2110011211, 2110101121 and 2110110112 form diag(1,b,b²,c,bc²,bc). Because b and c are nonzero indeterminates in K, these six elements are independent. The domain subspace is spanned by a finite monomial set, so the restricted kernel is finite dimensional and its dimension is at least 6, contradicting the predicted 5. A matching upper bound is not asserted. The larger type-dependent gauge space obtained by imposing only the three nonzero recurrence terms is outside this statement.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.Exp`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.GRType`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.K`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.Parameters`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.a`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.admissible`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.b`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.c`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.omega`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.order`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.phi`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.proper`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.quadratic`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.result`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.substitution`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.upsilon`
- Truth anchor: `D5/S0/Certificates/Combinatorics/GaleRobinsonKernelDimensionRefutation.x`
