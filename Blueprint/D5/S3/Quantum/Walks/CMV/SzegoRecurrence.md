# SzegoRecurrence

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

**Definition 1.1 (residue).**

$$\forall (d a : \mathbb{Z}) , \operatorname{residue} d a = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid e \operatorname{mod} d = a\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.residue` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For integers d and a, residue d a is the real span of Laurent monomials whose integer exponent has remainder a modulo d. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Definition 1.2 (W).**

$$\forall (x : \mathbb{N}) , \operatorname{W} x = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid - (2 \cdot \operatorname{Nat.cast}\left(x\right)) \leq e \land e \leq 2 \cdot \operatorname{Nat.cast}\left(x\right)\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.W` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, W x is the real span of Laurent monomials with integer exponents from minus twice x through twice x, including both endpoints.

**Definition 1.3 (E).**

$$\forall (x : \mathbb{N}) , \operatorname{E} x = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid - (2 \cdot \operatorname{Nat.cast}\left(x\right)) \leq e \land e \leq 2 \cdot \operatorname{Nat.cast}\left(x\right) \land e \operatorname{mod} 2 = 0\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, E x is the real span of Laurent monomials with even integer exponents from minus twice x through twice x, including both endpoints. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Definition 1.4 (IsProjection).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (V : Submodule \mathbb{R} (LaurentPolynomial \mathbb{R})) (f h : LaurentPolynomial \mathbb{R}) , \operatorname{IsProjection} B V f h \iff (h \in V) \land (\forall (q : LaurentPolynomial \mathbb{R}) , q \in V \to B q (f - h) = 0)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.IsProjection` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For a real bilinear form B, a Laurent subspace V and Laurent polynomials f and h, IsProjection holds exactly when h belongs to V and every q in V has zero B pairing with f minus h.

**Theorem 1.5 (T mem spanOn).**

$$\forall \{S : Set \mathbb{Z}\} \{e : \mathbb{Z}\} , e \in S \to (\operatorname{LaurentPolynomial.T} e) \in \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (S))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.T_mem_spanOn` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If an integer exponent e belongs to a set S, its Laurent monomial belongs to the real span of the monomials with exponents in S.

**Theorem 1.6 (spanOn mono).**

$$\forall \{S Sprime : Set \mathbb{Z}\} , S \subseteq Sprime \to \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (S)) \leq \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (Sprime))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.spanOn_mono` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a set of integer exponents S is contained in another set, the real span of its Laurent monomials is contained in the real span of the monomials from the larger set.

**Theorem 1.7 (form zero on span).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (S : Set \mathbb{Z}) (r : LaurentPolynomial \mathbb{R}) , (\forall (e : \mathbb{Z}) , e \in S \to (B (\operatorname{LaurentPolynomial.T} e)) r = 0) \to \forall (q : LaurentPolynomial \mathbb{R}) , q \in \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (S)) \to (B q) r = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.form_zero_on_span` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For a real bilinear form B and a Laurent polynomial r, if every monomial with exponent in S has zero B pairing with r, every Laurent polynomial in their real span also has zero pairing with r.

**Theorem 1.8 (residue class orthogonal).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (d a b : \mathbb{Z}) , a \neq b \to (\forall (i j : \mathbb{Z}) , i \operatorname{mod} d \neq j \operatorname{mod} d \to (B (\operatorname{LaurentPolynomial.T} i)) (\operatorname{LaurentPolynomial.T} j) = 0) \to \forall (p : LaurentPolynomial \mathbb{R}) , p \in \operatorname{residue} d a \to \forall (q : LaurentPolynomial \mathbb{R}) , q \in \operatorname{residue} d b \to (B p) q = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.residue_class_orthogonal` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a real bilinear form B pairs monomials with different integer remainders modulo d to zero, then it pairs every polynomial in residue d a with every polynomial in residue d b to zero whenever a and b are distinct integers. For integer arguments, mod denotes the Euclidean remainder: for nonzero d it lies between 0 inclusive and abs(d) exclusive, and e mod 0 equals e.

**Theorem 1.9 (E le W).**

$$\forall (x : \mathbb{N}) , \operatorname{E} x \leq \operatorname{W} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_le_W` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, the even-exponent window E x is contained in the full Laurent window W x.

**Theorem 1.10 (E le even).**

$$\forall (x : \mathbb{N}) , \operatorname{E} x \leq \operatorname{residue} 2 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_le_even` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, E x is contained in the Laurent subspace residue 2 0.

**Theorem 1.11 (projection unique).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (V : Submodule \mathbb{R} (LaurentPolynomial \mathbb{R})) , (\forall (p : LaurentPolynomial \mathbb{R}) , p \neq 0 \to 0 < (B p) p) \to \forall \{f h k : LaurentPolynomial \mathbb{R}\} , \operatorname{IsProjection} B V f h \to \operatorname{IsProjection} B V f k \to h = k$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.projection_unique` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a real bilinear form B is strictly positive on every nonzero Laurent polynomial paired with itself, any two B projections of the same Laurent polynomial onto the same subspace are equal.

**Theorem 1.12 (finite projection exists).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (V : Submodule \mathbb{R} (LaurentPolynomial \mathbb{R})) [FiniteDimensional \mathbb{R} \operatorname{CoeSort.coe}\left(V\right)] , (\forall (p : LaurentPolynomial \mathbb{R}) , p \neq 0 \to 0 < (B p) p) \to \forall (f : LaurentPolynomial \mathbb{R}) , \exists (h : LaurentPolynomial \mathbb{R}) , \operatorname{IsProjection} B V f h$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.finite_projection_exists` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For a real bilinear form B that is strictly positive on every nonzero Laurent polynomial paired with itself, each Laurent polynomial has a B projection onto every finite-dimensional real Laurent subspace.

**Theorem 1.13 (finite orthonormal projection).**

$$\forall (B : LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] LaurentPolynomial \mathbb{R} \to_{l} [\mathbb{R}] \mathbb{R}) (v : \mathbb{N} \to LaurentPolynomial \mathbb{R}) , (\forall (i j : \mathbb{N}) , (B (v i)) (v j) = \operatorname{if} i = j \operatorname{then} 1 \operatorname{else} 0) \to \forall (N : \mathbb{N}) (f : LaurentPolynomial \mathbb{R}) , \operatorname{have} V : = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (v) (\{j : \mathbb{N} \mid j < N\})) ; \operatorname{have} h : = \sum j \in \operatorname{Finset.range} N , (B (v j)) f \cdot v j ; \operatorname{IsProjection} B V f h \land (B h) h = \sum j \in \operatorname{Finset.range} N , ((B (v j)) f)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.finite_orthonormal_projection` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a sequence of real Laurent polynomials is orthonormal for a real bilinear form B, the sum of the first N polynomials weighted by their B pairings with f is a B projection of f onto their span. Its B pairing with itself is the sum of the squares of those N pairings.

**Definition 1.14 (V).**

$$\forall (Y : \mathbb{N}) , \operatorname{V} Y = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid - \operatorname{Nat.cast}\left(Y\right) \leq e \land e \leq \operatorname{Nat.cast}\left(Y\right) + 1\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.V` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural Y, V Y is the real span of Laurent monomials with integer exponents from minus Y through Y plus one, including both endpoints.

**Definition 1.15 (W finite).**

$$\forall (x : \mathbb{N}) , FiniteDimensional \mathbb{R} \operatorname{CoeSort.coe}\left((\operatorname{W} x)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.W_finite` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, the real Laurent subspace W x is finite-dimensional.

**Definition 1.16 (E finite).**

$$\forall (x : \mathbb{N}) , FiniteDimensional \mathbb{R} \operatorname{CoeSort.coe}\left((\operatorname{E} x)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_finite` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural x, the real Laurent subspace E x is finite-dimensional.

**Definition 1.17 (innerCore).**

$$\begin{aligned}\operatorname{innerCore} : \operatorname{InnerProductSpace.Core} \mathbb{R} (LaurentPolynomial \mathbb{R})\\\forall (x y : LaurentPolynomial \mathbb{R}) , \operatorname{innerCore.inner} x y = \operatorname{sigma} x y\\\forall (x y : LaurentPolynomial \mathbb{R}) , \operatorname{sigma} x y = \operatorname{sigma} y x\\\forall (x : LaurentPolynomial \mathbb{R}) , 0 \leq \operatorname{sigma} x x\\\forall (x y z : LaurentPolynomial \mathbb{R}) , \operatorname{sigma} (x + y) z = \operatorname{sigma} x z + \operatorname{sigma} y z\\\forall (x y : LaurentPolynomial \mathbb{R}) (r : \mathbb{R}) , \operatorname{sigma} (r \cdot x) y = r \cdot \operatorname{sigma} x y\\\forall (x : LaurentPolynomial \mathbb{R}) , \operatorname{sigma} x x = 0 \to x = 0\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.innerCore` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

The form sigma supplies a real inner product core on Laurent polynomials, with symmetry, nonnegativity, linearity and definiteness.

**Definition 1.18 (exponent).**

$$\forall (j : \mathbb{N}) , \operatorname{exponent} j = \operatorname{if} j \operatorname{mod} 2 = 0 \operatorname{then} - \operatorname{Nat.cast}\left((\operatorname{Nat.div} j 2)\right) \operatorname{else} \operatorname{Nat.cast}\left((\operatorname{Nat.div} j 2)\right) + 1$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.exponent` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 3, arXiv PDF p. 8: “Laurent polynomials {χⱼ}ⱼ₌₀∞ are obtained from the Gram-Schmidt orthonormalization of {1,z,z⁻¹,z²,z⁻²,…}.” The Laurent monomials are ordered 0,1,−1,2,−2,… . Division by 2 is natural-number division rounded down. For natural arguments, mod denotes Nat.mod, the remainder of natural-number division.

**Definition 1.19 (monomials).**

$$\forall (j : \mathbb{N}) , \operatorname{monomials} j = \operatorname{LaurentPolynomial.T} (\operatorname{exponent} j)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monomials` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 3, arXiv PDF p. 8: “Laurent polynomials {χⱼ}ⱼ₌₀∞ are obtained from the Gram-Schmidt orthonormalization of {1,z,z⁻¹,z²,z⁻²,…}.” LaurentPolynomial.T and exponent give exactly this order.

**Definition 1.20 (chi).**

$$\operatorname{chi} = \operatorname{InnerProductSpace.gramSchmidtNormed} \mathbb{R} \operatorname{monomials}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 3, arXiv PDF p. 8: “Laurent polynomials {χⱼ}ⱼ₌₀∞ are obtained from the Gram-Schmidt orthonormalization of {1,z,z⁻¹,z²,z⁻²,…}.” The real moment inner product supplies the orthonormalization.

**Theorem 1.21 (chi orthonormal).**

$$\forall (i j : \mathbb{N}) , (\operatorname{sigma} (\operatorname{chi} i)) (\operatorname{chi} j) = \operatorname{if} i = j \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_orthonormal` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For all natural i and j, the sigma pairing of chi i and chi j is one when the indices coincide and zero otherwise.

**Theorem 1.22 (chi window).**

$$\forall (Y : \mathbb{N}) , \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{chi}) (\{j : \mathbb{N} \mid j < 2 \cdot Y + 2\})) = \operatorname{V} Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_window` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural Y, the real span of chi j over indices less than twice Y plus two equals the Laurent window V Y.

**Theorem 1.23 (chi zero).**

$$\operatorname{chi} 0 = \operatorname{LaurentPolynomial.T} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_zero` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

The first orthonormal Laurent polynomial chi 0 is the constant monomial with exponent zero.

**Theorem 1.24 (sigma shift).**

$$\forall (e : \mathbb{Z}) (p q : LaurentPolynomial \mathbb{R}) , (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} e \cdot p)) (\operatorname{LaurentPolynomial.T} e \cdot q) = (\operatorname{sigma} p) q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.sigma_shift` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every integer e and real Laurent polynomials p and q, multiplying both polynomials by the Laurent monomial at e preserves their sigma pairing.

**Theorem 1.25 (sigma shift adjoint).**

$$\forall (e : \mathbb{Z}) (p q : LaurentPolynomial \mathbb{R}) , (\operatorname{sigma} p) (\operatorname{LaurentPolynomial.T} (- e) \cdot q) = (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} e \cdot p)) q$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.sigma_shift_adjoint` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every integer e and real Laurent polynomials p and q, the sigma pairing of p with q multiplied by the monomial at negative e equals the pairing of p multiplied by the monomial at e with q.

**Definition 1.26 (coeffLM).**

$$\forall (e : \mathbb{Z}) , \operatorname{coeffLM} e = \operatorname{Finsupp.lapply} e \circ_{l} \operatorname{LinearEquiv.toLinearMap}\left((\operatorname{AddMonoidAlgebra.coeffLinearEquiv} \mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For an integer e, coeffLM e is the real linear map extracting the coefficient at exponent e from a real Laurent polynomial.

**Theorem 1.27 (coeffLM T).**

$$\forall (e j : \mathbb{Z}) , (\operatorname{coeffLM} e) (\operatorname{LaurentPolynomial.T} j) = \operatorname{if} e = j \operatorname{then} 1 \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_T` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For integer exponents e and j, the coefficient at e of the Laurent monomial at j is one if the exponents coincide and zero otherwise.

**Theorem 1.28 (mem spanOn iff).**

$$\forall (S : Set \mathbb{Z}) (p : LaurentPolynomial \mathbb{R}) , p \in \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (S)) \iff \forall (e : \mathbb{Z}) , \neg e \in S \to (\operatorname{coeffLM} e) p = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.mem_spanOn_iff` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For any set S of integer exponents, a real Laurent polynomial belongs to the real span of the monomials from S exactly when all its coefficients outside S vanish.

**Definition 1.29 (polyWindow).**

$$\forall (n : \mathbb{N}) , \operatorname{polyWindow} n = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid 0 \leq e \land e \leq \operatorname{Nat.cast}\left(n\right)\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.polyWindow` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, polyWindow n is the real span of Laurent monomials with exponents from zero through n, including both endpoints.

**Definition 1.30 (polyBelow).**

$$\forall (n : \mathbb{N}) , \operatorname{polyBelow} n = \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} (\operatorname{LaurentPolynomial.T}) (\{e : \mathbb{Z} \mid 0 \leq e \land e < \operatorname{Nat.cast}\left(n\right)\}))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.polyBelow` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, polyBelow n is the real span of Laurent monomials with nonnegative exponents strictly less than n.

**Definition 1.31 (phi).**

$$\operatorname{phi} = \operatorname{InnerProductSpace.gramSchmidt} \mathbb{R} \operatorname{fun} (n : \mathbb{N}) \mapsto \operatorname{LaurentPolynomial.T} \operatorname{Nat.cast}\left(n\right)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

The sequence phi is obtained by applying real Gram-Schmidt orthogonalization, without normalization, to the Laurent monomials with natural exponents in increasing order.

**Theorem 1.32 (phi mem window).**

$$\forall (n : \mathbb{N}) , (\operatorname{phi} n) \in \operatorname{polyWindow} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_mem_window` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phi n belongs to polyWindow n.

**Theorem 1.33 (coeff window zero).**

$$\forall (n : \mathbb{N}) \{p : LaurentPolynomial \mathbb{R}\} , p \in \operatorname{polyWindow} n \to \forall (e : \mathbb{Z}) , e < 0 \lor \operatorname{Nat.cast}\left(n\right) < e \to (\operatorname{coeffLM} e) p = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeff_window_zero` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a real Laurent polynomial belongs to polyWindow n, its coefficient at an integer exponent e is zero whenever e is negative or exceeds n.

**Theorem 1.34 (phi monic).**

$$\forall (n : \mathbb{N}) , (\operatorname{coeffLM} \operatorname{Nat.cast}\left(n\right)) (\operatorname{phi} n) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_monic` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, the coefficient of phi n at exponent n is one.

**Theorem 1.35 (phi orthogonal).**

$$\forall (n : \mathbb{N}) (e : \mathbb{Z}) , 0 \leq e \land e < \operatorname{Nat.cast}\left(n\right) \to (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} e)) (\operatorname{phi} n) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_orthogonal` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n and integer exponent e from zero inclusive to n exclusive, the sigma pairing of the monomial at e with phi n is zero.

**Theorem 1.36 (phi orthogonal span).**

$$\forall (n : \mathbb{N}) , \forall (q : LaurentPolynomial \mathbb{R}) , q \in \operatorname{polyBelow} n \to (\operatorname{sigma} q) (\operatorname{phi} n) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_orthogonal_span` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, every polynomial in polyBelow n has zero sigma pairing with phi n.

**Definition 1.37 (phiStar).**

$$\forall (n : \mathbb{N}) , \operatorname{phiStar} n = \operatorname{LaurentPolynomial.T} \operatorname{Nat.cast}\left(n\right) \cdot \operatorname{LaurentPolynomial.invert} (\operatorname{phi} n)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phiStar n is phi n with all exponents negated and then shifted by n.

**Theorem 1.38 (phiStar norm).**

$$\forall (n : \mathbb{N}) , (\operatorname{sigma} (\operatorname{phiStar} n)) (\operatorname{phiStar} n) = (\operatorname{sigma} (\operatorname{phi} n)) (\operatorname{phi} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_norm` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phiStar n and phi n have the same sigma pairing with themselves.

**Theorem 1.39 (coeffLM shift).**

$$\forall (e i : \mathbb{Z}) (p : LaurentPolynomial \mathbb{R}) , (\operatorname{coeffLM} e) (\operatorname{LaurentPolynomial.T} i \cdot p) = (\operatorname{coeffLM} (e - i)) p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_shift` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For integers e and i and a real Laurent polynomial p, the coefficient at e after multiplication by the monomial at i is the coefficient of p at e minus i.

**Theorem 1.40 (coeffLM invert).**

$$\forall (e : \mathbb{Z}) (p : LaurentPolynomial \mathbb{R}) , (\operatorname{coeffLM} e) (\operatorname{LaurentPolynomial.invert} p) = (\operatorname{coeffLM} (- e)) p$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_invert` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For an integer e and a real Laurent polynomial p, the coefficient at e after exponent inversion is the coefficient of p at negative e.

**Theorem 1.41 (phiStar constant).**

$$\forall (n : \mathbb{N}) , (\operatorname{coeffLM} 0) (\operatorname{phiStar} n) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_constant` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, the constant coefficient of phiStar n is one.

**Theorem 1.42 (phiStar coeff zero).**

$$\forall (n : \mathbb{N}) (e : \mathbb{Z}) , e < 0 \lor \operatorname{Nat.cast}\left(n\right) < e \to (\operatorname{coeffLM} e) (\operatorname{phiStar} n) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_coeff_zero` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, the coefficient of phiStar n at an integer exponent e is zero whenever e is negative or exceeds n.

**Theorem 1.43 (phiStar orthogonal).**

$$\forall (n : \mathbb{N}) (e : \mathbb{Z}) , 1 \leq e \land e \leq \operatorname{Nat.cast}\left(n\right) \to (\operatorname{sigma} (\operatorname{LaurentPolynomial.T} e)) (\operatorname{phiStar} n) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_orthogonal` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n and integer exponent e from one through n inclusive, the sigma pairing of the monomial at e with phiStar n is zero.

**Theorem 1.44 (phiStar mem window).**

$$\forall (n : \mathbb{N}) , (\operatorname{phiStar} n) \in \operatorname{polyWindow} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_mem_window` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phiStar n belongs to polyWindow n.

**Definition 1.45 (verblunsky).**

$$\forall (n : \mathbb{N}) , \operatorname{verblunsky} n = - (\operatorname{coeffLM} 0) (\operatorname{phi} (n + 1))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.verblunsky` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, verblunsky n is the negative of the constant coefficient of phi at index n plus one.

**Theorem 1.46 (monic szego).**

$$\forall (n : \mathbb{N}) , \operatorname{phi} (n + 1) = \operatorname{LaurentPolynomial.T} 1 \cdot \operatorname{phi} n - \operatorname{verblunsky} n \cdot \operatorname{phiStar} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monic_szego` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phi at index n plus one equals phi n multiplied by the monomial at exponent one, minus verblunsky n times phiStar n.

**Definition 1.47 (normSquare).**

$$\forall (n : \mathbb{N}) , \operatorname{normSquare} n = (\operatorname{sigma} (\operatorname{phi} n)) (\operatorname{phi} n)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normSquare` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, normSquare n is the sigma pairing of phi n with itself.

**Theorem 1.48 (normSquare pos).**

$$\forall (n : \mathbb{N}) , 0 < \operatorname{normSquare} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normSquare_pos` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, normSquare n is strictly positive.

**Theorem 1.49 (verblunsky sq lt one).**

$$\forall (n : \mathbb{N}) , (\operatorname{verblunsky} n)^{2} < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.verblunsky_sq_lt_one` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, the square of the real Verblunsky coefficient verblunsky n is strictly less than one.

**Definition 1.50 (gramNorm).**

$$\forall (n : \mathbb{N}) , \operatorname{gramNorm} n = \sqrt{(\operatorname{normSquare} n)}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.gramNorm` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, gramNorm n is the real square root of normSquare n.

**Definition 1.51 (normalizedPhi).**

$$\forall (n : \mathbb{N}) , \operatorname{normalizedPhi} n = (\operatorname{gramNorm} n)^{-1} \cdot \operatorname{phi} n$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalizedPhi` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, normalizedPhi n is phi n multiplied by the reciprocal of gramNorm n.

**Definition 1.52 (normalizedPhiStar).**

$$\forall (n : \mathbb{N}) , \operatorname{normalizedPhiStar} n = (\operatorname{gramNorm} n)^{-1} \cdot \operatorname{phiStar} n$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalizedPhiStar` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, normalizedPhiStar n is phiStar n multiplied by the reciprocal of gramNorm n.

**Theorem 1.53 (normalized szego).**

$$\forall (n : \mathbb{N}) , \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{verblunsky} n)\right) \cdot \operatorname{normalizedPhi} (n + 1) = \operatorname{LaurentPolynomial.T} 1 \cdot \operatorname{normalizedPhi} n - \operatorname{verblunsky} n \cdot \operatorname{normalizedPhiStar} n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalized_szego` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, szegoRho at verblunsky n times normalizedPhi at index n plus one equals normalizedPhi n multiplied by the monomial at exponent one, minus verblunsky n times normalizedPhiStar n.

**Theorem 1.54 (monic star szego).**

$$\forall (n : \mathbb{N}) , \operatorname{phiStar} (n + 1) = \operatorname{phiStar} n - \operatorname{verblunsky} n \cdot (\operatorname{LaurentPolynomial.T} 1 \cdot \operatorname{phi} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monic_star_szego` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, phiStar at index n plus one equals phiStar n minus verblunsky n times phi n multiplied by the monomial at exponent one.

**Theorem 1.55 (normalized star inverse).**

$$\forall (n : \mathbb{N}) , \operatorname{normalizedPhiStar} (n + 1) = \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{verblunsky} n)\right) \cdot \operatorname{normalizedPhiStar} n - \operatorname{verblunsky} n \cdot \operatorname{normalizedPhi} (n + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalized_star_inverse` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural n, normalizedPhiStar at index n plus one equals szegoRho at verblunsky n times normalizedPhiStar n, minus verblunsky n times normalizedPhi at index n plus one.

**Theorem 1.56 (chi even).**

$$\forall (k : \mathbb{N}) , \operatorname{chi} (2 \cdot k) = \operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left(k\right)) \cdot \operatorname{normalizedPhiStar} (2 \cdot k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_even` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural k, chi at index twice k equals normalizedPhiStar at that index multiplied by the Laurent monomial at negative k.

**Theorem 1.57 (chi odd).**

$$\forall (k : \mathbb{N}) , \operatorname{chi} (2 \cdot k + 1) = \operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left(k\right)) \cdot \operatorname{normalizedPhi} (2 \cdot k + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_odd` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For every natural k, chi at index twice k plus one equals normalizedPhi at that index multiplied by the Laurent monomial at negative k.

## References

- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_finite`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_le_W`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.E_le_even`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.IsProjection`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.T_mem_spanOn`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.V`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.W`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.W_finite`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_even`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_odd`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_orthonormal`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_window`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.chi_zero`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_T`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_invert`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeffLM_shift`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.coeff_window_zero`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.exponent`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.finite_orthonormal_projection`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.finite_projection_exists`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.form_zero_on_span`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.gramNorm`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.innerCore`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.mem_spanOn_iff`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monic_star_szego`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monic_szego`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.monomials`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normSquare`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normSquare_pos`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalizedPhi`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalizedPhiStar`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalized_star_inverse`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.normalized_szego`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_coeff_zero`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_constant`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_mem_window`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_norm`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phiStar_orthogonal`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_mem_window`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_monic`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_orthogonal`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.phi_orthogonal_span`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.polyBelow`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.polyWindow`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.projection_unique`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.residue`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.residue_class_orthogonal`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.sigma_shift`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.sigma_shift_adjoint`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.spanOn_mono`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.verblunsky`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/SzegoRecurrence.verblunsky_sq_lt_one`
- Dependency: [D5/S3/Quantum/Walks/Riesz/Moments](../Riesz/Moments.md)
- Dependency: [D5/S3/Weil/Szego/CanonicalTransfer](../../../Weil/Szego/CanonicalTransfer.md)
