# Operator identities descend through the same seminorm kernel

## Abstract

The quaternion seminorm on H × M₃(R) satisfies all six conditions while hiding two nonzero raw operator defects.

**Definition 1.1 (The raw synthesis operator).**

$$\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall m \in \operatorname{Bilinear}\left(R, V\right),\; \forall a \in V,\; \forall b \in V,\; \forall c \in V,\; \operatorname{synthesis}\left(m, a, b, c\right) = \operatorname{m}\left(\operatorname{m}\left(a, b\right) - \operatorname{m}\left(b, a\right), c\right) + \operatorname{m}\left(a, \operatorname{m}\left(b, c\right)\right) - \operatorname{m}\left(b, \operatorname{m}\left(a, c\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.synthesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let V be a real vector space and m : V →ₗ[R] V →ₗ[R] V its actual bilinear multiplication. Write xy = m(x,y). The parentheses are k c + a(bc) − b(ac), with k = ab − ba. No associativity is assumed in this definition.

**Definition 1.2 (The raw projection expression).**

$$\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall m \in \operatorname{Bilinear}\left(R, V\right),\; \forall p \in V \to \mathbb{R},\; \forall a \in V,\; \forall b \in V,\; \forall c \in V,\; \operatorname{projection}\left(m, p, a, b, c\right) = \operatorname{smul}\left(-\frac{1}{\operatorname{mul}\left(2, \operatorname{p}\left(\operatorname{m}\left(a, b\right) - \operatorname{m}\left(b, a\right)\right)^{2}\right)}, \operatorname{m}\left(\operatorname{m}\left(a, b\right) - \operatorname{m}\left(b, a\right), \operatorname{synthesis}\left(m, a, b, c\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same readout p defines q(x)=p(x)². The coefficient multiplies k T(c) in that order. Division is real division; no nonzero-denominator hypothesis is hidden in the definition.

**Definition 1.3 (The six conditions on the original algebra).**

$$\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall m \in \operatorname{Bilinear}\left(R, V\right),\; \forall p \in V \to \mathbb{R},\; \forall e \in V,\; \forall a \in V,\; \forall b \in V,\; \operatorname{Candidate}\left(m, p, e, a, b\right) = \left((\forall x \in V,\; 0 \leq \operatorname{p}\left(x\right)) \land ((\forall t \in \mathbb{R},\; \forall x \in V,\; \operatorname{p}\left(\operatorname{smul}\left(t, x\right)\right) = \operatorname{mul}\left(\operatorname{abs}\left(t\right), \operatorname{p}\left(x\right)\right)) \land ((\forall x \in V,\; \forall y \in V,\; \operatorname{p}\left(x + y\right) \leq \operatorname{p}\left(x\right) + \operatorname{p}\left(y\right)) \land ((\exists x \in V,\; 0 < \operatorname{p}\left(x\right)) \land ((\forall x \in V,\; \forall y \in V,\; \operatorname{p}\left(\operatorname{m}\left(x, y\right)\right) = \operatorname{mul}\left(\operatorname{p}\left(x\right), \operatorname{p}\left(y\right)\right)) \land ((\forall x \in V,\; \operatorname{p}\left(\operatorname{m}\left(e, x\right) - x\right) + \operatorname{p}\left(\operatorname{m}\left(x, e\right) - x\right) = 0) \land (\forall c \in V,\; (\operatorname{p}\left(\operatorname{synthesis}\left(m, a, b, c\right)\right) = 0) \Rightarrow (\operatorname{p}\left(c\right) = 0)))))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.Candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B1 is carried by the bilinear type of m. B2 requires a nonnegative real-valued seminorm with absolute homogeneity and the triangle inequality. E asserts a positive readout. N is exact multiplicativity. U_p uses one witness e for both readout unit equations. F quantifies over every raw c with the same witnesses a and b. This packages chosen witnesses for the existential conditions; universal quantification over such witnesses preserves the original inference question.

**Definition 1.4 (The proposed exact lifting to the original domain).**

$$claim = \left(\forall V \in Type,\; [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] \forall m \in \operatorname{Bilinear}\left(R, V\right),\; \forall p \in V \to \mathbb{R},\; \forall e \in V,\; \forall a \in V,\; \forall b \in V,\; (\operatorname{Candidate}\left(m, p, e, a, b\right)) \Rightarrow ((\forall c \in V,\; \operatorname{synthesis}\left(m, a, b, \operatorname{synthesis}\left(m, a, b, \operatorname{synthesis}\left(m, a, b, c\right)\right)\right) = \operatorname{smul}\left(-\operatorname{mul}\left(4, \operatorname{p}\left(\operatorname{m}\left(a, b\right) - \operatorname{m}\left(b, a\right)\right)^{2}\right), \operatorname{synthesis}\left(m, a, b, c\right)\right)) \land (\forall c \in V,\; \operatorname{projection}\left(m, p, a, b, \operatorname{projection}\left(m, p, a, b, c\right)\right) = \operatorname{projection}\left(m, p, a, b, c\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The assertion quantifies over all real vector spaces, bilinear multiplications, readouts and witnesses satisfying the six conditions. It would place both the cubic identity and idempotence on the original vector space. The coefficient is 4q(ab−ba); in the model below it is 16. Counterexample 5.7 distinguishes these equations from their valid equations on the readable quotient. This assertion records precisely the stronger inference it denies.

**Definition 1.5 (The complete simultaneous countermodel).**

$$Certificate = \left((\operatorname{Candidate}\left(m, p, 1, a, b\right)) \land ((\forall c \in Raw,\; \operatorname{p}\left(c\right)^{2} = \operatorname{normSq}\left(\operatorname{fst}\left(c\right)\right)) \land ((\forall c \in Raw,\; (c \in N) \Leftrightarrow (\operatorname{fst}\left(c\right) = 0)) \land ((\forall c \in Raw,\; (c \in N) \Leftrightarrow (\operatorname{p}\left(c\right) = 0)) \land ((k = \operatorname{pair}\left(\operatorname{smul}\left(2, kH\right), K\right)) \land ((\operatorname{p}\left(k\right)^{2} = 4) \land ((\forall c \in Raw,\; \operatorname{T}\left(c\right) = \operatorname{pair}\left(\operatorname{smul}\left(4, \operatorname{mul}\left(kH, \operatorname{fst}\left(c\right)\right)\right), \operatorname{smul}\left(2, \operatorname{mul}\left(K, \operatorname{snd}\left(c\right)\right)\right)\right)) \land ((\forall c \in Raw,\; \operatorname{P}\left(c\right) = \operatorname{pair}\left(\operatorname{fst}\left(c\right), \operatorname{smul}\left(-\frac{1}{4}, \operatorname{mul}\left(K, \operatorname{mul}\left(K, \operatorname{snd}\left(c\right)\right)\right)\right)\right)) \land ((\forall c \in Raw,\; (\operatorname{T}\left(\operatorname{T}\left(\operatorname{T}\left(c\right)\right)\right) + \operatorname{smul}\left(16, \operatorname{T}\left(c\right)\right) \in N) \land (\operatorname{P}\left(\operatorname{P}\left(c\right)\right) - \operatorname{P}\left(c\right) \in N)) \land ((\operatorname{T}\left(\operatorname{T}\left(\operatorname{T}\left(\operatorname{pair}\left(0, I\right)\right)\right)\right) + \operatorname{smul}\left(16, \operatorname{T}\left(\operatorname{pair}\left(0, I\right)\right)\right) = \operatorname{pair}\left(0, \operatorname{diagonal}\left(40, 40, -128\right)\right)) \land ((\operatorname{P}\left(\operatorname{P}\left(\operatorname{pair}\left(0, I\right)\right)\right) - \operatorname{P}\left(\operatorname{pair}\left(0, I\right)\right) = \operatorname{pair}\left(0, \operatorname{diagonal}\left(\frac{5}{16}, \frac{5}{16}, 2\right)\right)) \land ((\operatorname{T}\left(\operatorname{T}\left(\operatorname{T}\left(\operatorname{pair}\left(0, I\right)\right)\right)\right) + \operatorname{smul}\left(16, \operatorname{T}\left(\operatorname{pair}\left(0, I\right)\right)\right) \neq 0) \land ((\operatorname{P}\left(\operatorname{P}\left(\operatorname{pair}\left(0, I\right)\right)\right) - \operatorname{P}\left(\operatorname{pair}\left(0, I\right)\right) \neq 0) \land ((\forall c \in Raw,\; \operatorname{E}\left(\operatorname{pi}\left(c\right)\right) = \operatorname{fst}\left(c\right)) \land ((\forall c \in Raw,\; \operatorname{pi}\left(\operatorname{T}\left(c\right)\right) = \operatorname{quotientT}\left(\operatorname{pi}\left(c\right)\right)) \land ((\forall c \in Raw,\; \operatorname{pi}\left(\operatorname{P}\left(c\right)\right) = \operatorname{quotientP}\left(\operatorname{pi}\left(c\right)\right)) \land ((\forall x \in Q,\; \operatorname{quotientT}\left(\operatorname{quotientT}\left(\operatorname{quotientT}\left(x\right)\right)\right) = \operatorname{smul}\left(-16, \operatorname{quotientT}\left(x\right)\right)) \land (\forall x \in Q,\; \operatorname{quotientP}\left(\operatorname{quotientP}\left(x\right)\right) = \operatorname{quotientP}\left(x\right))))))))))))))))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here Raw = Quaternion R × Matrix (Fin 3) (Fin 3) R has its usual componentwise associative multiplication m and unit e=(1,I). Set A=E₁₂+E₂₃, B=E₂₁+2E₃₂, K=diag(1,1,−2), i=(0,1,0,0), j=(0,0,1,0), and kH=(0,0,0,1). The witnesses are a=(i,A), b=(j,B), k=ab−ba. Put p(h,X)=‖h‖, T=synthesis m a b, and P=projection m p a b. N is the actual two-sided ideal ker(fst : Raw →ₐ[R] H). Thus membership in N is equivalent both to h=0 and to p(h,X)=0. Let Q=Raw/N, write π for its quotient homomorphism, and let E : Q ≃ₐ[R] H be the algebra equivalence induced by the surjective first projection. Define quotientT(x)=E⁻¹(4 kH E(x)) and quotientP(x)=x. The two intertwining equations prove that these are induced by the original T and P through this very quotient. Every displayed conjunction is part of Certificate, including all original c, both nonzero defects at (0,I), the exact quotient identification, and both quotient polynomial laws.

**Theorem 1.6 (All clauses hold in one model).**

$$Certificate$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.raw_counterexample_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Associativity gives T(c)=2kc. The commutator is (2kH,K); kH²=−1 and ‖kH‖=1. Hence p(Tc)=4p(c), proving F on every raw c. Homogeneity, the triangle inequality and multiplicativity are inherited through the first projection from the quaternion norm. The actual product unit proves U_p and has readout one, proving E. The full product calculation gives P(h,X)=(h,−K(KX)/4). Both polynomial defects therefore have first component zero for every c. At (0,I), the cubic defect is diag(40,40,−128) in the matrix component and the idempotence defect is diag(5/16,5/16,2). Their (0,0) entries prove nonvanishing. The first isomorphism theorem identifies the quotient by N with H, preserving multiplication and real scalars. Intertwining transports both operators; kH²=−1 proves the quotient cubic, and quotientP is the identity. The result is the complete algebraic example of Counterexample 5.7; it asserts no physical realization or classification theorem.

**Theorem 1.7 (The raw lifting inference is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the proposed universal inference to the constructed model and its six-condition certificate. It makes the cubic defect vanish at (0,I), contradicting its nonzero matrix entry. The certificate also proves that raw idempotence fails at the same point, while both defects vanish under the same readout and both equations hold on the quotient.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.Candidate`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.Certificate`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.projection`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.raw_counterexample_certificate`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.result`
- Truth anchor: `D5/S3/Quantum/Algebra/RawReadoutOperatorRefutation.synthesis`
