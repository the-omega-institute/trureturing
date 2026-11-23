# A weighted character sieve for primitive roots

## Abstract

A weighted character sieve for primitive roots

**Definition 1.1 (The sieve primes).**

$$\operatorname{sievePrimes}\left(p, e, T\right) = \{t \in T \mid \operatorname{Prime}\left(t\right) \land \left(\operatorname{dvd}\left(t, p - 1\right) \land \left(\neg \operatorname{dvd}\left(t, e\right)\right)\right)\}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterSieve.sievePrimes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Only primes dividing p-1 that do not divide e enter the sieve; all other members of T are ignored.

**Definition 1.2 (The exact sieve defect).**

$$\operatorname{defect}\left(p, e, T, a\right) = \operatorname{if}\left(\left(\forall q \in \mathbb{N},\; q \in \operatorname{primeFactors}\left(e\right) \Rightarrow \left(\neg a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), q\right)\right)\right) \land 2 \le \operatorname{card}\left(\{t \in \operatorname{sievePrimes}\left(p, e, T\right) \mid a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), t\right)\}\right), \operatorname{card}\left(\{t \in \operatorname{sievePrimes}\left(p, e, T\right) \mid a \in \operatorname{powerSubgroup}\left(\operatorname{Units}\left(p\right), t\right)\}\right) - 1, 0\right)$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterSieve.defect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Let b(a) count the sieve primes t for which a is a t-th power. The defect is b(a)-1 at e-free units with b(a)>=2, and zero elsewhere. It is nonnegative. For nonzero supported e and a covering T it equals the primitive-root indicator minus the elementary sieve indicator.

**Theorem 1.3 (The full corrected error for arbitrary margins).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{R},\; \forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\neg e = 0\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{dvd}\left(q, p - 1\right) \Rightarrow \left(\operatorname{dvd}\left(q, e\right) \lor q \in T\right)\right)\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in \operatorname{sievePrimes}\left(p, e, T\right) \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)\right) \le M\right)\right) \Rightarrow \operatorname{abs}\left(\sum_{a \in \operatorname{PrimitiveResidues}\left(p\right)} {\operatorname{W}\left(a\right)} - \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{defect}\left(p, \operatorname{gcd}\left(e, p - 1\right), T, a\right)} - \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right)}\right) \le \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{Kabs}\left(\operatorname{gcd}\left(e, p - 1\right), \operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot M\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterSieve.primitive_weight_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Put f=gcd(e,p-1). With the nonzero, cover and character hypotheses, use K_abs(f,U) to bound the absolute corrected error for every delta(U). No sign restriction on W or delta is needed. The signed coefficient K is recovered exactly when delta(U)>=0 or f has no prime factors.

**Theorem 1.4 (A two-sided corrected estimate for primitive-root weight).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall W \in \operatorname{ZMod}\left(p\right) \to \mathbb{R},\; \forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\neg e = 0\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{dvd}\left(q, p - 1\right) \Rightarrow \left(\operatorname{dvd}\left(q, e\right) \lor q \in T\right)\right)\right) \Rightarrow \left(\forall M \in \mathbb{R},\; \left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in \operatorname{sievePrimes}\left(p, e, T\right) \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\sum_{a \in \operatorname{Residues}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{chi}\left(a\right)}\right)\right) \le M\right)\right) \Rightarrow \left(\left(0 \le \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \lor \operatorname{primeFactors}\left(\operatorname{gcd}\left(e, p - 1\right)\right) = \operatorname{empty}\left(\right)\right) \Rightarrow \operatorname{abs}\left(\sum_{a \in \operatorname{PrimitiveResidues}\left(p\right)} {\operatorname{W}\left(a\right)} - \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right) \cdot \operatorname{defect}\left(p, \operatorname{gcd}\left(e, p - 1\right), T, a\right)} - \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{W}\left(a\right)}\right) \le \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{K}\left(\operatorname{gcd}\left(e, p - 1\right), \operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot M\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterSieve.primitive_weight_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Let p be prime and e be nonzero. Put f=gcd(e,p-1). The set T covers the prime divisors of p-1 absent from e. Write U=sievePrimes(p,e,T), and R for the product of the distinct prime divisors of e. For nonprincipal characters whose order divides R or tR for some t in U, the absolute real part of the weighted character sum is at most M. For delta(U)>=0 or empty prime support of f, the absolute error bound retains the full weighted defect sum. W is an arbitrary real weight, with no sign restriction. Units(p) denotes the unit group and PrimitiveResidues(p) the residues of order p-1.

The character expansion supplies a two-sided estimate for the elementary sieve weight. The exact pointwise identity is 1_primitive(a)=1_f-free(a)(1-b(a))+defect(p,f,T,a). Multiplying by any real W(a) and summing preserves this equality. Thus the weighted defect belongs in the conclusion, including when it is negative. There is no need to compare signed terms pointwise.

A nonnegative weighted defect gives the defect-free one-sided lower bound P>=theta(f)(delta(U)S-K(f,U)M), where S is the total unit weight. For supported e this is P>=theta(e)(delta(U)S-K(e,U)M). The two-sided absolute error estimate retains the defect. A stronger, easily checked sufficient condition is W(a)>=0 at every f-free unit belonging to at least two t-th power subgroups for t in U. Neither condition is assumed by the theorem. When U has at most one member, the defect vanishes. For negative delta the absolute coefficient K_abs gives the two-sided bound.

The cover is essential: p=3, e=1 and empty T would otherwise count weight supported at the nongenerator 1. Reducing all output parameters to f removes the prime-support restriction on e. At p=3, e=0, empty T and weight supported at 1, the nonzero condition prevents the false bound 1<=0. At p=3, e=2 and empty T, constant weight 1 with M=0 attains equality in the theta factor. Weight supported at 1 with M=1 attains equality in K=1. These parameter choices exclude a uniform increase of theta or a uniform decrease of K. They do not prove that the constants are optimal separately for every parameter choice.

**Definition 1.5 (A smoothed von Mangoldt character sum).**

$$\operatorname{S}\left(p, chi\right) = \sum_{m \in \operatorname{range}\left(p\right)} {\operatorname{Lambda}\left(m\right) \cdot \left(1 - \frac{m}{p}\right) \cdot \operatorname{chi}\left(m\right)}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedCharacterSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian (2015). *On Grosswald's conjecture on primitive roots*. DOI: [10.4064/aa8109-12-2015](https://doi.org/10.4064/aa8109-12-2015). URL: <https://doi.org/10.4064/aa8109-12-2015>.

*Commentary.*

The variable m runs through 0<=m<p. Lambda is the von Mangoldt function, with Lambda(0)=Lambda(1)=0. Division in the displayed sum takes place in the complex numbers. The real weight is nonnegative and chi is evaluated at m modulo p.

**Definition 1.6 (Smoothed weight at primitive residues).**

$$\operatorname{Psm}\left(p\right) = \sum_{a \in \operatorname{PrimitiveResidues}\left(p\right)} {\operatorname{wp}\left(a\right)}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedPrimitiveWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. D. Cohen, T. Oliveira e Silva, T. S. Trudgian (2015). *On Grosswald's conjecture on primitive roots*. DOI: [10.4064/aa8109-12-2015](https://doi.org/10.4064/aa8109-12-2015). URL: <https://doi.org/10.4064/aa8109-12-2015>.

*Commentary.*

Here w_p(a) is the sum of Lambda(m)(1-m/p) over 0<=m<p with m congruent to a modulo p.

**Definition 1.7 (The full smoothed defect correction).**

$$\operatorname{Dsm}\left(p, e, T\right) = \sum_{a \in \operatorname{Units}\left(p\right)} {\operatorname{wp}\left(a\right) \cdot \operatorname{defect}\left(p, e, T, a\right)}$$

*Formalization.* `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

The parameter e is explicit; the gcd-reduced criterion uses f=gcd(e,p-1). Both factors in every summand are nonnegative.

**Theorem 1.8 (A quantitative smoothed estimate after gcd reduction).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall M \in \mathbb{R},\; \left(\neg e = 0\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{dvd}\left(q, p - 1\right) \Rightarrow \left(\operatorname{dvd}\left(q, e\right) \lor q \in T\right)\right)\right) \Rightarrow \left(\left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in \operatorname{sievePrimes}\left(p, e, T\right) \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\operatorname{S}\left(p, chi\right)\right)\right) \le M\right)\right) \Rightarrow \left(0 \le \operatorname{re}\left(\operatorname{S}\left(p, 1\right)\right) \land \left(0 \le \operatorname{Psm}\left(p\right) \land \left(0 \le \operatorname{Dsm}\left(p, \operatorname{gcd}\left(e, p - 1\right), T\right) \land \operatorname{abs}\left(\operatorname{Psm}\left(p\right) - \operatorname{Dsm}\left(p, \operatorname{gcd}\left(e, p - 1\right), T\right) - \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot \operatorname{re}\left(\operatorname{S}\left(p, 1\right)\right)\right) \le \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{Kabs}\left(\operatorname{gcd}\left(e, p - 1\right), \operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot M\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothed_primitive_weight_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Put f=gcd(e,p-1), U=sievePrimes(p,e,T) and S=Re(S(p,1)). The principal sum, the primitive weight and the defect D_sm(p,f,T) are nonnegative. The absolute difference P_sm(p)-D_sm(p,f,T)-theta(f)delta(U)S is at most theta(f)K_abs(f,U)M. This retains both sides of the estimate and applies to every delta(U). Only the nonzero, cover and character-bound hypotheses are needed; no positive margin is assumed by this quantitative theorem.

**Theorem 1.9 (The signed margin without a defect gain is sufficient).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall M \in \mathbb{R},\; \left(\neg e = 0\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{dvd}\left(q, p - 1\right) \Rightarrow \left(\operatorname{dvd}\left(q, e\right) \lor q \in T\right)\right)\right) \Rightarrow \left(\left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in \operatorname{sievePrimes}\left(p, e, T\right) \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\operatorname{S}\left(p, chi\right)\right)\right) \le M\right)\right) \Rightarrow \left(\operatorname{K}\left(\operatorname{gcd}\left(e, p - 1\right), \operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot M < \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot \operatorname{re}\left(\operatorname{S}\left(p, 1\right)\right) \Rightarrow \left(0 < \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \land \left(\exists q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \land \left(q < p \land \operatorname{orderOf}\left(\operatorname{residue}\left(q, p\right)\right) = p - 1\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterSieve.exists_prime_primitiveRoot_of_smoothed_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Under the same nonzero, cover and character hypotheses, K(f,U)M<delta(U)Re(S(p,1)) implies the corrected positivity criterion. If delta(U) were nonpositive, U would contain a prime t and its controlled characters would force M>=0. Since K(f,U)>=0 and the principal smoothed sum is nonnegative, strict signed positivity would be impossible. The conclusion includes delta(U)>0, so K_abs=K. The density is positive and the smoothed defect is nonnegative, which gives the corrected criterion and then a prime primitive root below p.

**Theorem 1.10 (A positive margin yields a prime primitive root).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(\forall e \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\mathbb{N}\right),\; \forall M \in \mathbb{R},\; \left(\neg e = 0\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \Rightarrow \left(\operatorname{dvd}\left(q, p - 1\right) \Rightarrow \left(\operatorname{dvd}\left(q, e\right) \lor q \in T\right)\right)\right) \Rightarrow \left(\left(\forall chi \in \operatorname{DirichletCharacter}\left(\mathbb{C}, p\right),\; \left(\neg chi = 1\right) \Rightarrow \left(\left(\operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right) \lor \left(\exists t \in \mathbb{N},\; t \in \operatorname{sievePrimes}\left(p, e, T\right) \land \operatorname{dvd}\left(\operatorname{orderOf}\left(chi\right), t \cdot \prod_{q \in \operatorname{primeFactors}\left(e\right)} {q}\right)\right)\right) \Rightarrow \operatorname{abs}\left(\operatorname{re}\left(\operatorname{S}\left(p, chi\right)\right)\right) \le M\right)\right) \Rightarrow \left(0 < \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{delta}\left(\operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot \operatorname{re}\left(\operatorname{S}\left(p, 1\right)\right) - \operatorname{theta}\left(\operatorname{gcd}\left(e, p - 1\right)\right) \cdot \operatorname{Kabs}\left(\operatorname{gcd}\left(e, p - 1\right), \operatorname{sievePrimes}\left(p, e, T\right)\right) \cdot M + \operatorname{Dsm}\left(p, \operatorname{gcd}\left(e, p - 1\right), T\right) \Rightarrow \left(\exists q \in \mathbb{N},\; \operatorname{Prime}\left(q\right) \land \left(q < p \land \operatorname{orderOf}\left(\operatorname{residue}\left(q, p\right)\right) = p - 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/CharacterSieve.exists_prime_primitiveRoot_of_smoothed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. McGown, E. Treviño, T. Trudgian (2016). *Resolving Grosswald's conjecture on GRH*. DOI: [10.7169/facm/2016.55.2.5](https://doi.org/10.7169/facm/2016.55.2.5). URL: <https://doi.org/10.7169/facm/2016.55.2.5>.

*Commentary.*

Let p be prime and e be nonzero. Keep the cover condition on T and the character-order support built from e, and bound the absolute real part of each supported smoothed sum by M. Put f=gcd(e,p-1). A strictly positive value theta(f)(delta(U)Re(S(p,1))-K_abs(f,U)M)+D_sm(p,f,T) produces a prime q<p of order p-1 modulo p. There is no extra disjunction concerning the prime support of e, the sign of M, or p=2.

The integer f is nonzero and its prime support divides p-1. The sieve sets U(f) and U(e) coincide, and the radical R(f) divides R(e), so every character needed for f is controlled by the original hypothesis. The arbitrary-weight gcd estimate applies to the nonnegative residue-class weight obtained from Lambda(m)(1-m/p). Its weighted defect is nonnegative. The principal character sum equals the total weight on units. Positivity gives m<p with Lambda(m)>0, hence m=q^k for a prime q and positive k. The order of q^k divides the order of q, which divides p-1. Since the first order is p-1, the order of q is p-1. Finally q<=q^k=m<p. The defect is retained in the positivity criterion, and delta may have either sign. The criterion is sufficient and does not characterize all primes possessing a prime primitive root.

Strictness matters: p=2, e=1, empty T and M=0 give zero margin, but no prime lies below p. Requiring two distinct prime primitive roots or one below the square root of p is a further question: neither a proof under the complete hypotheses nor a counterexample under those hypotheses is supplied by this estimate.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.defect`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.exists_prime_primitiveRoot_of_smoothed`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.exists_prime_primitiveRoot_of_smoothed_signed`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.primitive_weight_error_bound`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.primitive_weight_lower_bound`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.sievePrimes`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedCharacterSum`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedDefect`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothedPrimitiveWeight`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/CharacterSieve.smoothed_primitive_weight_error_bound`
- Dependency: [D5/S3/Arith/PrimitiveRoot/CharacterExpansion](CharacterExpansion.md)
