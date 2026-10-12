# Two-dimensional pseudo-Paley cliques

## Abstract

The two-dimensional cliques containing one in quartic pseudo-Paley graphs are exactly the odd-generator planes.

**Definition 1.1 (Cyclotomic class character).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall x \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{chi}\left(p, x\right) = x^{\left(p^{2} + 1\right) \cdot \left(p - 1\right)}$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.chi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The power character labels the p+1 cyclotomic classes of the quartic finite field.

**Definition 1.2 (Norm of an affine representative).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall t \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{Q}\left(p, b, t\right) = \left(b + t\right)^{p^{2} + 1}$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is the p-squared norm power of b+t; it is used on prime-field affine parameters.

**Lemma 1.3 (Character through the norm).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall t \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{chi}\left(p, b + t\right) = \operatorname{Q}\left(p, b, t\right)^{p - 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.chi_eq_Q_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The character factors as the norm power followed by the p-minus-one power.

**Lemma 1.4 (A fixed prime-field element).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall x \in \operatorname{GaloisField}\left(p, 4\right),\; x^{p - 1} = 1 \Rightarrow x^{p} = x$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.pow_char_eq_self_of_pow_sub_one_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A p-minus-one root of unity is fixed by the p-th power.

**Lemma 1.5 (Quartic exponent factorization).**

$$\forall p \in \mathrm{Nat},\; 1 \le p \Rightarrow \left(p - 1\right) \cdot \left(p + 1\right) \cdot \left(p^{2} + 1\right) = p^{4} - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.q_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All arithmetic is in the natural numbers; subtraction is truncated subtraction.

**Lemma 1.6 (Parity of the norm).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] p \ne 2 \Rightarrow \left(\forall g \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{IsPrimitiveRoot}\left(g, p^{4} - 1\right) \Rightarrow \left(\forall k \in \mathrm{Nat},\; \exists u \in \operatorname{ZMod}\left(p\right),\; \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), u\right) = \left(g^{\left(p + 1\right) \cdot k}\right)^{p^{2} + 1} \land \left(\operatorname{IsSquare}\left(u\right) \Leftrightarrow \operatorname{Even}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.c_square_iff_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm of the indicated generator power lies in the prime field and is a square exactly when its exponent index is even.

**Lemma 1.7 (Trace and norm prevent collapse).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{CharP}\left(F, p\right)] \forall b \in F,\; \left(\left(b + b^{p^{2}}\right)^{p} = b + b^{p^{2}} \land \left(b \cdot b^{p^{2}}\right)^{p} = b \cdot b^{p^{2}}\right) \Rightarrow b^{p} = b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.trace_norm_fixed_implies_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both the relative trace and norm are fixed by the p-th power, their common source element is fixed as well.

**Definition 1.8 (The affine norm polynomial).**

$$\forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] \forall B \in F,\; \forall C \in F,\; \forall t \in F,\; \operatorname{normPoly}\left(B, C, t\right) = t^{2} + B \cdot t + C$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.normPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial expression retains its leading coefficient one.

**Lemma 1.9 (Two affine points share a class).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{CharP}\left(F, p\right)] \forall B \in F,\; \forall C \in F,\; \forall t \in F,\; \forall s \in F,\; \left(\left(B^{p} \ne B \land C^{p} = C\right) \land \left(t^{p} = t \land s^{p} = s\right)\right) \Rightarrow \left(\operatorname{normPoly}\left(B, C, t\right)^{p} \cdot \operatorname{normPoly}\left(B, C, s\right) = \operatorname{normPoly}\left(B, C, t\right) \cdot \operatorname{normPoly}\left(B, C, s\right)^{p} \Leftrightarrow \left(t = s \lor t \cdot s = C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.cross_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the trace coefficient is outside the prime field and the norm is inside it, proportional norms occur exactly for equal points or for a pair whose product is the norm.

**Lemma 1.10 (The affine mate of infinity).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] [\operatorname{CharP}\left(F, p\right)] \forall B \in F,\; \forall C \in F,\; \forall t \in F,\; \left(\left(B^{p} \ne B \land C^{p} = C\right) \land t^{p} = t\right) \Rightarrow \left(\operatorname{normPoly}\left(B, C, t\right)^{p} = \operatorname{normPoly}\left(B, C, t\right) \Leftrightarrow t = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.infinity_cross_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-field norm direction has exactly the affine parameter zero.

**Definition 1.11 (The projective pairing).**

$$\forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] \forall C \in F,\; \operatorname{projectiveMate}\left(C, \operatorname{\mathit{Option}.\mathit{none}}\right) = \operatorname{\mathit{Option}.\mathit{some}}\left(0\right) \land \left(\forall t \in F,\; \left(t = 0 \Rightarrow \operatorname{projectiveMate}\left(C, \operatorname{\mathit{Option}.\mathit{some}}\left(t\right)\right) = \operatorname{\mathit{Option}.\mathit{none}}\right) \land \left(t \ne 0 \Rightarrow \operatorname{projectiveMate}\left(C, \operatorname{\mathit{Option}.\mathit{some}}\left(t\right)\right) = \operatorname{\mathit{Option}.\mathit{some}}\left(\frac{C}{t}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveMate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Option.none represents infinity. It exchanges infinity with zero and sends each nonzero parameter to C/t, avoiding total division at zero.

**Lemma 1.12 (Nonsquares have no singleton orbits).**

$$\forall F \in \mathit{Type},\; [\operatorname{Field}\left(F\right)] \forall C \in F,\; C \ne 0 \Rightarrow \left(\left(\forall x \in \operatorname{Option}\left(F\right),\; \operatorname{projectiveMate}\left(C, x\right) \ne x\right) \Leftrightarrow \left(\neg \operatorname{IsSquare}\left(C\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveMate_no_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero norm the projective pairing is fixed-point-free precisely when the norm is not a square.

**Definition 1.13 (Projective class map).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{projectiveClass}\left(p, b, \operatorname{\mathit{Option}.\mathit{none}}\right) = 1 \land \left(\forall t \in \operatorname{ZMod}\left(p\right),\; \operatorname{projectiveClass}\left(p, b, \operatorname{\mathit{Option}.\mathit{some}}\left(t\right)\right) = \operatorname{chi}\left(p, b + \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Infinity represents one and an affine prime-field parameter represents b+t.

**Lemma 1.14 (Nonzero affine norms).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall t \in \operatorname{ZMod}\left(p\right),\; b^{p} \ne b \Rightarrow \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.norm_Q_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An element outside the prime field cannot be cancelled by a prime-field affine parameter.

**Lemma 1.15 (Quadratic expansion of the norm).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall t \in \operatorname{ZMod}\left(p\right),\; \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)\right) = \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)^{2} + \left(b + b^{p^{2}}\right) \cdot \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right) + b \cdot b^{p^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.Q_as_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm has quadratic, trace and constant terms, with every affine parameter mapped into the quartic field.

**Lemma 1.16 (Equality gives proportional norm directions).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall t \in \operatorname{ZMod}\left(p\right),\; \forall s \in \operatorname{ZMod}\left(p\right),\; \left(b^{p} \ne b \land \operatorname{projectiveClass}\left(p, b, \operatorname{\mathit{Option}.\mathit{some}}\left(t\right)\right) = \operatorname{projectiveClass}\left(p, b, \operatorname{\mathit{Option}.\mathit{some}}\left(s\right)\right)\right) \Rightarrow \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)\right)^{p} \cdot \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), s\right)\right) = \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)\right) \cdot \operatorname{Q}\left(p, b, \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), s\right)\right)^{p}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.equal_projective_class_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal class characters force the p-th-power cross product equality of the two nonzero norms.

**Lemma 1.17 (Embedded prime-field parameters).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall t \in \operatorname{ZMod}\left(p\right),\; \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)^{p} = \operatorname{algebraMap}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.prime_field_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every embedded prime-field parameter is fixed by the p-th power.

**Theorem 1.18 (At most two projective points per class).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall b \in \operatorname{GaloisField}\left(p, 4\right),\; \forall y \in \operatorname{GaloisField}\left(p, 4\right),\; b^{p} \ne b \Rightarrow \operatorname{\mathit{Finset}.\mathit{card}}\left(\operatorname{\mathit{Finset}.\mathit{filter}}\left(\lambda (t: \operatorname{Option}\left(\operatorname{ZMod}\left(p\right)\right)) \mapsto \operatorname{projectiveClass}\left(p, b, t\right) = y, (\operatorname{\mathit{Finset}.\mathit{univ}}: \operatorname{Finset}\left(\operatorname{Option}\left(\operatorname{ZMod}\left(p\right)\right)\right))\right)\right) \le 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projective_fiber_card_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b outside the prime field, the affine fiber equation is a nonzero polynomial of degree at most two. The infinity fiber has a nonzero linear equation on its affine part. The two bounds give at most two points in every projective fiber.

**Definition 1.19 (Cyclotomic class).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall g \in \operatorname{GaloisField}\left(p, 4\right),\; \forall j \in \mathrm{Nat},\; \operatorname{cyclotomicClass}\left(p, g, j\right) = \{(x: \operatorname{GaloisField}\left(p, 4\right)) \mid \exists m \in \mathrm{Nat},\; x = g^{j + \left(p + 1\right) \cdot m}\}$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.cyclotomicClass` (`✓ std3`).

*Citation.* Shamil Asgarli; Chi Hoi Yip (2024). *The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes*. DOI: [10.48550/arXiv.2110.07176](https://doi.org/10.48550/arXiv.2110.07176). URL: <https://arxiv.org/abs/2110.07176v5>.

*Commentary.*

Cyclotomic classes (p. 1): “Let $N \mid (q - 1)$. Let $C_{0}$ be the subgroup of $\left(\mathbb{F}_{q}\right)^{*}$ with index $N$, and let $C_{1}$, …, $C_{N - 1}$ be all the cosets of $C_{0}$, where $C_{j} = g^{j}C_{0}$. The sets $C_{0}$, $C_{1}$, …, $C_{N - 1}$ are called the $N$-th cyclotomic classes of $\mathbb{F}_{q}$.”

The source takes the p+1-th cyclotomic classes of the quartic finite field. The primitive element is g, and natural exponents enumerate the cyclic subgroup generated by its p+1-th power.

**Definition 1.20 (Connection set).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall g \in \operatorname{GaloisField}\left(p, 4\right),\; \forall I \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{connection}\left(p, g, I\right) = \operatorname{\mathit{Set}.\mathit{iUnion}}\left(\lambda (j: \mathrm{Nat}) \mapsto \operatorname{\mathit{Set}.\mathit{iUnion}}\left(\lambda (_: j \in I) \mapsto \operatorname{cyclotomicClass}\left(p, g, j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.connection` (`✓ std3`).

*Citation.* Shamil Asgarli; Chi Hoi Yip (2024). *The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes*. DOI: [10.48550/arXiv.2110.07176](https://doi.org/10.48550/arXiv.2110.07176). URL: <https://arxiv.org/abs/2110.07176v5>.

*Commentary.*

Definition 1.1 (pp. 1–2): “Suppose $q$ is a prime power, $d$ a positive integer such that $2d \mid (q - 1)$, and $I$={$m_{1}$, …, $m_{d}$} ⊂ {0, 1, …, $2d - 1$} with $|I| = d$. Let $C_{0}$, $C_{1}$, …, $C_{2d - 1}$ be the $2d$-th cyclotomic classes of $\mathbb{F}_{q}$. The graph $\operatorname{PP}\left(q, 2d, I\right)$ is defined to be the Cayley graph $\operatorname{Cay}\left(\left(\mathbb{F}_{q}\right)^{+}, D\right)$ where D=⋃ⱼ₌₁ᵈ $C_{m_{j}}$.”

Here the source parameters are q=p^4 and 2d=p+1; the selected natural indices form I. The union is the literal connection set.

**Definition 1.21 (Pseudo-Paley graph).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] \forall g \in \operatorname{GaloisField}\left(p, 4\right),\; \forall I \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{PP}\left(p, g, I\right) = \operatorname{\mathit{SimpleGraph}.\mathit{fromRel}}\left(\lambda (x: \operatorname{GaloisField}\left(p, 4\right)) \mapsto \lambda (y: \operatorname{GaloisField}\left(p, 4\right)) \mapsto y - x \in \operatorname{connection}\left(p, g, I\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.PP` (`✓ std3`).

*Citation.* Shamil Asgarli; Chi Hoi Yip (2024). *The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes*. DOI: [10.48550/arXiv.2110.07176](https://doi.org/10.48550/arXiv.2110.07176). URL: <https://arxiv.org/abs/2110.07176v5>.

*Commentary.*

Definition 1.1 (pp. 1–2): “Suppose $q$ is a prime power, $d$ a positive integer such that $2d \mid (q - 1)$, and $I$={$m_{1}$, …, $m_{d}$} ⊂ {0, 1, …, $2d - 1$} with $|I| = d$. Let $C_{0}$, $C_{1}$, …, $C_{2d - 1}$ be the $2d$-th cyclotomic classes of $\mathbb{F}_{q}$. The graph $\operatorname{PP}\left(q, 2d, I\right)$ is defined to be the Cayley graph $\operatorname{Cay}\left(\left(\mathbb{F}_{q}\right)^{+}, D\right)$ where D=⋃ⱼ₌₁ᵈ $C_{m_{j}}$.”

SimpleGraph.fromRel supplies the symmetric irreflexive relation of the additive Cayley graph; the difference is y-x.

**Definition 1.22 (Asgarli–Yip Conjecture 5.9).**

$$(\mathit{claim}: \mathit{Prop}) = \left(\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{\mathit{Nat}.\mathit{Prime}}\left(p\right)\right)] p \ne 2 \Rightarrow \left(\forall g \in \operatorname{GaloisField}\left(p, 4\right),\; \operatorname{IsPrimitiveRoot}\left(g, p^{4} - 1\right) \Rightarrow \left(\forall V \in \operatorname{Submodule}\left(\operatorname{ZMod}\left(p\right), \operatorname{GaloisField}\left(p, 4\right)\right),\; \left(\operatorname{\mathit{Module}.\mathit{finrank}}\left(\operatorname{ZMod}\left(p\right), V\right) = 2 \land (1: \operatorname{GaloisField}\left(p, 4\right)) \in V\right) \Rightarrow \left(\left(\exists I \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; I \subseteq \operatorname{\mathit{Finset}.\mathit{range}}\left(p + 1\right) \land \left(\operatorname{\mathit{Finset}.\mathit{card}}\left(I\right) = \operatorname{\mathit{Nat}.\mathit{div}}\left(p + 1, 2\right) \land \operatorname{\mathit{SimpleGraph}.\mathit{IsClique}}\left(\operatorname{PP}\left(p, g, I\right), (V: \operatorname{Set}\left(\operatorname{GaloisField}\left(p, 4\right)\right))\right)\right)\right) \Leftrightarrow \left(\exists k \in \mathrm{Nat},\; \operatorname{Odd}\left(k\right) \land V = \operatorname{\mathit{Submodule}.\mathit{span}}\left(\operatorname{ZMod}\left(p\right), \left\{1, g^{\left(p + 1\right) \cdot k}\right\}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.claim` (`✓ std3`).

*Citation.* Shamil Asgarli; Chi Hoi Yip (2024). *The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes*. DOI: [10.48550/arXiv.2110.07176](https://doi.org/10.48550/arXiv.2110.07176). URL: <https://arxiv.org/abs/2110.07176v5>.

*Commentary.*

Conjecture 5.9 (p. 17): “Let $V$ be a $2$-dimensional subspace in $\mathbb{F}_{p^{4}}$, such that $1 \in V$. Then $V$ is a clique in $\operatorname{PP}\left(p^{4}, p + 1, I\right)$ for some $I$ if and only if $V = \mathbb{F}_{p}$ ⊕ $a\mathbb{F}_{p}$, where $a = g^{(p + 1)k}$ and $k$ is an odd integer.”

The prime p is odd, g has order p^4-1, and V is a two-dimensional ZMod p-subspace containing one. The source's 'for some I' means I is contained in Finset.range (p+1) and has cardinality Nat.div (p+1) 2. The direct sum is Submodule.span of one and the indicated generator power. Natural odd indices enumerate the same powers as odd integer indices, because the order p^4-1 is even.

**Theorem 1.23 (Classification of the two-dimensional cliques).**

$$\mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result` (`✓ std3`). ∎

*Resolves.* `Problems/asgarli-yip-2021-pseudo-paley-two-dimensional-cliques` (proved) by `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"asgarli-yip-2021-pseudo-paley-two-dimensional-cliques","declaration_gid":"D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shamil Asgarli; Chi Hoi Yip (2024). *The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes*. DOI: [10.48550/arXiv.2110.07176](https://doi.org/10.48550/arXiv.2110.07176). URL: <https://arxiv.org/abs/2110.07176v5>.

*Commentary.*

The p+1 projective points map to cyclotomic classes with at most two points per fiber. A clique fits into (p+1)/2 classes, forcing every fiber to be a pair. The mate of infinity selects a generator power in the zeroth class. Its norm is a square exactly for even indices; a square norm gives a singleton fiber, so clique indices are odd. Conversely, an odd index gives a nonsquare norm and the fixed-point-free pairing exchanges zero with infinity and pairs the other parameters by C/t. Its classes form the required index set.

## References

- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.PP`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.Q`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.Q_as_quadratic`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.c_square_iff_even`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.chi`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.chi_eq_Q_pow`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.claim`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.connection`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.cross_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.cyclotomicClass`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.equal_projective_class_cross`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.infinity_cross_iff`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.normPoly`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.norm_Q_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.pow_char_eq_self_of_pow_sub_one_eq_one`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.prime_field_fixed`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveClass`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveMate`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projectiveMate_no_fixed_iff`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.projective_fiber_card_le_two`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.q_factor`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result`
- Truth anchor: `D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.trace_norm_fixed_implies_fixed`
