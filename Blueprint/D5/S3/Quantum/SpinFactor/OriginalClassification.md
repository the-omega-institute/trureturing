# Original spin classification and matrix consequences

## Abstract

Complete original-D H2 classification and both Pauli multiplication orders

The Pauli consumers and the complete classification share this source owner. The same_D_consequences theorem is a conditional fixed-orientation consumer. The complete_classification theorem additionally uses the actual arbitrary-D pure and residual rigidity arguments; the complete_consequences theorem uses both paths.

The carrier is the original real spin factor E = R × R^3 with the pinned Jordan product, cone, evaluations alpha_(m,v) for every m >= norm(v), including zero, subnormalized and unequal masses, and original norm |s| + norm(x). D is one arbitrary total E -> E -> E used in every directed Gram entry and every phase-square slot. No additivity, homogeneity, continuity, unit rows, translation neutrality, P3, NN, PY, R, CP or physical-realization premise is added.

The exact endpoint is: for every total D, the actual directed complex two-label Gram PSD condition P2, with both directed off-diagonal entries and both diagonals for every positive evaluation, together with the literal same-D plus/minus phase-square balance PB, holds if and only if there is one orientation epsilon in {plus, minus} such that D((s,x),(t,y)) = (0, epsilon times (x cross y)) for every real s,t and every original x,y. Both implications and all zero, proportional, unequal-length, unit and nonunit inputs are included.

The forward proof consumes OriginalPureRigidity.global_pure to obtain one global pure sign from only P2 and PB, then consumes OriginalResidual.all_inputs_of_pure to extend that same sign to arbitrary scalar/vector inputs. The residual proof consumes the exact finite SO(3) word theorem and moving-axis/right-word transport; it does not use density, closure or continuity of unknown D.

The reverse implication identifies the chosen orientation with the fixed Pauli product and consumes OriginalSpinConsumers.same_D_consequences. The resulting Consequences record the same-D unit and translation neutrality, real bilinearity, original-norm bounds and continuity, every finite complex Gram PSD table, and the original reassociation identity R. MatrixInterfaces records all original positive masses, the cone, the original order-unit norm and the fixed product/readout realization. These are mathematical consequences for the same D, not extra premises.

The conclusion concerns the complete specified finite spin model. A Pauli matrix representation is a mathematical realization of its products, cone, norm and evaluations. It supplies no physical preparation, instrument, channel, resource cost or realization of a complete original source.

**Definition 1.1 (Original carrier).**

$$E = \operatorname{Prod}\left(\mathbb{R}, \operatorname{Fin}\left(3\right) \to \mathbb{R}\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical OriginalDContract carrier E = R x (Fin 3 -> R). Write a = (s,x); this source consumes that exact carrier.

**Definition 1.2 (Unit).**

$$unit = (1, 0)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.unit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit has scalar coordinate one and vector coordinate zero.

**Definition 1.3 (Four-coordinate transport).**

$$\forall a \in E,\; \operatorname{toFamily}\left(a\right) = \operatorname{toLp}\left(2, (\operatorname{fst}\left(a\right),\operatorname{snd}\left(a\right)\left(0\right),\operatorname{snd}\left(a\right)\left(1\right),\operatorname{snd}\left(a\right)\left(2\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.toFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing spin-product carrier orders the canonical vector coordinates as scalar, x, y, z. This map is the supplier transport from the canonical carrier.

**Definition 1.4 (Scalar and vector transport).**

$$\forall a \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{fst}\left(\operatorname{ofFamily}\left(a\right)\right) = a\left(0\right) \land \left(\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{snd}\left(\operatorname{ofFamily}\left(a\right)\right)\left(i\right) = a\left(\operatorname{Fin.succ}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.ofFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse coordinate transport returns the original scalar and function-valued vector coordinates.

**Definition 1.5 (Original Jordan product).**

$$\forall a \in E,\; \forall b \in E,\; \operatorname{jordan}\left(a, b\right) = (\operatorname{fst}\left(a\right) \cdot \operatorname{fst}\left(b\right) + \operatorname{OriginalDContract.dot}\left(\operatorname{snd}\left(a\right), \operatorname{snd}\left(b\right)\right), (\operatorname{fst}\left(a\right)) \cdot (\operatorname{snd}\left(b\right)) + (\operatorname{fst}\left(b\right)) \cdot (\operatorname{snd}\left(a\right)))$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.jordan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is definitionally the canonical OriginalDContract.jordan; jordan_supplier records its correspondence with PauliFixedProductFamily.S.

**Definition 1.6 (Bilinear cross channel).**

$$\forall a \in E,\; \forall b \in E,\; \operatorname{cross}\left(a, b\right) = (0, \operatorname{OriginalDContract.cross}\left(\operatorname{snd}\left(a\right), \operatorname{snd}\left(b\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The channel transports PauliFixedProductFamily.C to the canonical OriginalDContract.cross channel and discards both scalar coordinates.

**Definition 1.7 (Global orientation).**

$$\forall o \in Bool,\; \operatorname{sign}\left(o\right) = \operatorname{ite}\left(o, 1, -1\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.sign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

False selects sign minus one. True selects sign plus one.

**Definition 1.8 (Fixed original relation).**

$$\forall o \in Bool,\; \forall a \in E,\; \forall b \in E,\; \operatorname{fixed}\left(o, a, b\right) = (\operatorname{sign}\left(o\right)) \cdot (\operatorname{cross}\left(a, b\right))$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.fixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One orientation is selected for the entire relation, independently of inputs and evaluations.

**Definition 1.9 (Original norm).**

$$\forall a \in E,\; \operatorname{originalNorm}\left(a\right) = \operatorname{abs}\left(\operatorname{fst}\left(a\right)\right) + \operatorname{vnorm}\left(\operatorname{snd}\left(a\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.originalNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the exact OriginalDContract norm |s| + vnorm x.

**Definition 1.10 (Original cone).**

$$\forall a \in E,\; \operatorname{cone}\left(a\right) \Leftrightarrow \operatorname{vnorm}\left(\operatorname{snd}\left(a\right)\right) \le \operatorname{fst}\left(a\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.cone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positivity is the exact OriginalDContract cone inequality vnorm x <= s.

**Definition 1.11 (All-mass evaluations).**

$$\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall a \in E,\; \operatorname{evaluate}\left(m, v, a\right) = m \cdot \operatorname{fst}\left(a\right) + \operatorname{OriginalDContract.dot}\left(v, \operatorname{snd}\left(a\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw matrix coordinates represent every canonical Evaluation mass m and vector v with vnorm v <= m, including zero, subnormalized and unequal masses.

**Definition 1.12 (Positive real linear functionals).**

$$\forall alpha \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \operatorname{PositiveEvaluation}\left(alpha\right) \Leftrightarrow \left(\forall a \in E,\; \operatorname{cone}\left(a\right) \Rightarrow 0 \le alpha\left(a\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.PositiveEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real linear functional is positive on the entire original spin cone.

**Definition 1.13 (Linear evaluation map).**

$$\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall a \in E,\; \operatorname{evaluationLinear}\left(m, v\right)\left(a\right) = \operatorname{evaluate}\left(m, v, a\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.evaluationLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evaluation formula is real linear before imposing positivity.

**Definition 1.14 (Pauli observable).**

$$\forall a \in E,\; \operatorname{phi}\left(a\right) = \operatorname{scalarB}\left(\operatorname{fst}\left(a\right), \operatorname{toLp}\left(2, \operatorname{snd}\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supplier scalarB gives the Hermitian matrix s I plus x dot sigma.

**Definition 1.15 (Unnormalized density).**

$$\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{density}\left(m, v\right) = ((\frac{1}{2}: \mathbb{C})) \cdot (\operatorname{scalarB}\left(m, \operatorname{toLp}\left(2, v\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density has trace m and is positive exactly when norm v is at most m.

**Definition 1.16 (Both matrix orientations).**

$$\forall o \in Bool,\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{product}\left(o, A, B\right) = \operatorname{ite}\left(o, B \cdot A, A \cdot B\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

False uses ordinary multiplication. True uses the opposite order.

**Definition 1.17 (Actual directed Gram table).**

$$\forall I \in Type,\; \forall D \in E \to \left(E \to E\right),\; \forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall a \in I \to E,\; \forall i \in I,\; \forall j \in I,\; \operatorname{gram}\left(D, m, v, a\right)\left(i, j\right) = (\operatorname{evaluate}\left(m, v, \operatorname{jordan}\left(a\left(i\right), a\left(j\right)\right)\right): \mathbb{C}) - \operatorname{Complex.I} \cdot (\operatorname{evaluate}\left(m, v, D\left(a\left(i\right), a\left(j\right)\right)\right): \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ordered pair uses the actual D value, including each diagonal and both directed off-diagonal entries.

**Definition 1.18 (Two-label complex positivity).**

$$\forall D \in E \to \left(E \to E\right),\; \operatorname{P2}\left(D\right) \Leftrightarrow \operatorname{OriginalDContract.P2}\left(D\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.P2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This node is an alias of OriginalDContract.P2: every canonical positive Evaluation and every original pair uses the same total D in both directed off-diagonal entries and on both diagonals.

**Definition 1.19 (Original plus/minus balance).**

$$\forall D \in E \to \left(E \to E\right),\; \operatorname{PB}\left(D\right) \Leftrightarrow \operatorname{OriginalDContract.PB}\left(D\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.PB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This node is an alias of OriginalDContract.PB: the canonical phaseR/phaseS outer pairs at t = +1 and t = -1 are compared with the same D.

**Definition 1.20 (Continuity in the original norm).**

$$\forall D \in E \to \left(E \to E\right),\; \operatorname{OriginalContinuous}\left(D\right) \Leftrightarrow \left(\forall a \in E,\; \forall b \in E,\; \forall eta \in \mathbb{R},\; 0 < eta \Rightarrow \left(\exists delta \in \mathbb{R},\; 0 < delta \land \left(\forall a1 \in E,\; \forall b1 \in E,\; \operatorname{originalNorm}\left(a1 - a\right) < delta \Rightarrow \left(\operatorname{originalNorm}\left(b1 - b\right) < delta \Rightarrow \operatorname{originalNorm}\left(D\left(a1, b1\right) - D\left(a, b\right)\right) < eta\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.OriginalContinuous` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Input and output increments are measured by |s| plus norm x.

**Definition 1.21 (Same-relation consequences).**

$$\forall D \in E \to \left(E \to E\right),\; \operatorname{Consequences}\left(D\right) \Leftrightarrow \left(\operatorname{P2}\left(D\right) \land \left(\operatorname{PB}\left(D\right) \land \left(\left(\forall r \in \mathbb{R},\; \forall b \in E,\; D\left((r) \cdot (unit), b\right) = 0\right) \land \left(\left(\forall r \in \mathbb{R},\; \forall a \in E,\; D\left(a, (r) \cdot (unit)\right) = 0\right) \land \left(\left(\forall r \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall a \in E,\; \forall b \in E,\; D\left(a + (r) \cdot (unit), b + (q) \cdot (unit)\right) = D\left(a, b\right)\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; \forall c \in E,\; D\left(a + b, c\right) = D\left(a, c\right) + D\left(b, c\right)\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; \forall c \in E,\; D\left(a, b + c\right) = D\left(a, b\right) + D\left(a, c\right)\right) \land \left(\left(\forall r \in \mathbb{R},\; \forall a \in E,\; \forall b \in E,\; D\left((r) \cdot (a), b\right) = (r) \cdot (D\left(a, b\right))\right) \land \left(\left(\forall r \in \mathbb{R},\; \forall a \in E,\; \forall b \in E,\; D\left(a, (r) \cdot (b)\right) = (r) \cdot (D\left(a, b\right))\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; \operatorname{originalNorm}\left(D\left(a, b\right)\right) \le \operatorname{originalNorm}\left(a\right) \cdot \operatorname{originalNorm}\left(b\right)\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; \forall a1 \in E,\; \forall b1 \in E,\; \operatorname{originalNorm}\left(D\left(a, b\right) - D\left(a1, b1\right)\right) \le \operatorname{originalNorm}\left(a - a1\right) \cdot \operatorname{originalNorm}\left(b\right) + \operatorname{originalNorm}\left(a1\right) \cdot \operatorname{originalNorm}\left(b - b1\right)\right) \land \left(\operatorname{OriginalContinuous}\left(D\right) \land \left(\left(\forall n \in Nat,\; \forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{vnorm}\left(v\right) \le m \Rightarrow \left(\forall a \in \operatorname{Fin}\left(n\right) \to E,\; \operatorname{PosSemidef}\left(\operatorname{gram}\left(D, m, v, a\right)\right)\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \forall c \in E,\; \operatorname{jordan}\left(\operatorname{jordan}\left(a, b\right), c\right) - \operatorname{jordan}\left(a, \operatorname{jordan}\left(b, c\right)\right) = D\left(D\left(a, b\right), c\right) - D\left(a, D\left(b, c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.Consequences` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every conclusion concerns the same arbitrary total relation D on the canonical OriginalDContract carrier, including the original reassociation identity.

**Definition 1.22 (Original cone, norm and evaluation interfaces).**

$$\forall o \in Bool,\; \forall D \in E \to \left(E \to E\right),\; \operatorname{MatrixInterfaces}\left(o, D\right) \Leftrightarrow \left(\left(\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{PosSemidef}\left(\operatorname{density}\left(m, v\right)\right) \Leftrightarrow \operatorname{vnorm}\left(v\right) \le m\right) \land \left(\left(\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{trace}\left(\operatorname{density}\left(m, v\right)\right) = (m: \mathbb{C})\right) \land \left(\left(\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{PositiveEvaluation}\left(\operatorname{evaluationLinear}\left(m, v\right)\right) \Leftrightarrow \operatorname{vnorm}\left(v\right) \le m\right) \land \left(\left(\forall alpha \in \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right),\; \operatorname{PositiveEvaluation}\left(alpha\right) \Rightarrow \left(\exists m \in \mathbb{R},\; \exists v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{vnorm}\left(v\right) \le m \land \left(\forall a \in E,\; alpha\left(a\right) = \operatorname{evaluate}\left(m, v, a\right)\right)\right)\right) \land \left(\left(\forall m \in \mathbb{R},\; \forall v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall a \in E,\; \operatorname{trace}\left(\operatorname{density}\left(m, v\right) \cdot \operatorname{phi}\left(a\right)\right) = (\operatorname{evaluate}\left(m, v, a\right): \mathbb{C})\right) \land \left(\left(\forall a \in E,\; \operatorname{PosSemidef}\left(\operatorname{phi}\left(a\right)\right) \Leftrightarrow \operatorname{cone}\left(a\right)\right) \land \left(\left(\forall a \in E,\; \forall r \in \mathbb{R},\; \left(\operatorname{PosSemidef}\left(((r: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) - \operatorname{phi}\left(a\right)\right) \land \operatorname{PosSemidef}\left(((r: \mathbb{C})) \cdot ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))) + \operatorname{phi}\left(a\right)\right)\right) \Leftrightarrow \operatorname{originalNorm}\left(a\right) \le r\right) \land \left(\left(\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{PosSemidef}\left(rho\right) \Rightarrow \left(\exists m \in \mathbb{R},\; \exists v \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \operatorname{vnorm}\left(v\right) \le m \land rho = \operatorname{density}\left(m, v\right)\right)\right) \land \left(\forall a \in E,\; \forall b \in E,\; \operatorname{product}\left(o, \operatorname{phi}\left(a\right), \operatorname{phi}\left(b\right)\right) = \operatorname{phi}\left(\operatorname{jordan}\left(a, b\right)\right) - (\operatorname{Complex.I}) \cdot (\operatorname{phi}\left(D\left(a, b\right)\right))\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinFactor/OriginalClassification.MatrixInterfaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every positive original linear functional and every positive two by two matrix is represented with its full canonical mass and vector. The matrix order interval retains the exact OriginalDContract norm.

**Theorem 1.23 (One global orientation supplies all consumers).**

$$\forall o \in Bool,\; \forall D \in E \to \left(E \to E\right),\; \left(\forall a \in E,\; \forall b \in E,\; D\left(a, b\right) = \operatorname{OriginalDContract.crossD}\left(\operatorname{ite}\left(o, plus, minus\right), a, b\right)\right) \Rightarrow \left(\operatorname{Consequences}\left(D\right) \land \operatorname{MatrixInterfaces}\left(o, D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalClassification.same_D_consequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is the canonical OriginalDContract.crossD orientation on every original input; fixed_crossD connects it to one Bool-selected Pauli multiplication order. For ordinary order the complex Gram quadratic form is tr(rho Z* Z), with Z the finite sum of Hermitian labels with arbitrary complex coefficients. Cyclicity gives tr(Z rho Z*), which is nonnegative. Opposite order transposes the same directed Gram table. The canonical PB and reassociation, original-norm bounds, continuity, all-mass evaluation interfaces and all finite Gram consequences are then supplied for this same D. No argument divides by the mass; this endpoint is conditional and does not classify an arbitrary D.

**Theorem 1.24 (Complete P2-PB iff classification).**

$$\forall D \in E \to \left(E \to E\right),\; \left(\operatorname{P2}\left(D\right) \land \operatorname{PB}\left(D\right)\right) \Leftrightarrow \left(\exists epsilon \in Orientation,\; \forall a \in E,\; \forall b \in E,\; D\left(a, b\right) = \operatorname{crossD}\left(epsilon, a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalClassification.complete_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original total D, P2 D and PB D are equivalent to the existence of one Orientation epsilon, chosen globally before any input, with D a b = crossD epsilon a b for all a,b in the original E.

**Theorem 1.25 (Same-D consequences of the classified orientation).**

$$\forall D \in E \to \left(E \to E\right),\; \operatorname{P2}\left(D\right) \Rightarrow \left(\operatorname{PB}\left(D\right) \Rightarrow \left(\exists epsilon \in Orientation,\; \left(epsilon = plus \lor epsilon = minus\right) \land \left(\left(\forall a \in E,\; \forall b \in E,\; D\left(a, b\right) = \operatorname{crossD}\left(epsilon, a, b\right)\right) \land \left(\operatorname{Consequences}\left(D\right) \land \operatorname{MatrixInterfaces}\left(\operatorname{orientationBool}\left(epsilon\right), D\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinFactor/OriginalClassification.complete_consequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D satisfying the original P2 and PB, the endpoint returns one global Orientation epsilon, its all-input crossD equality, the full Consequences structure, and the corresponding MatrixInterfaces structure. The structures retain unit and translation neutrality, real bilinearity, original-norm continuity and bounds, all finite complex Gram tables, R, all positive evaluations and masses, the cone and the original norm. No physical realization or stronger regularity is asserted.

## References

- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.Consequences`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.E`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.MatrixInterfaces`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.OriginalContinuous`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.P2`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.PB`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.PositiveEvaluation`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.complete_classification`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.complete_consequences`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.cone`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.cross`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.density`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.evaluate`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.evaluationLinear`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.fixed`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.gram`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.jordan`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.ofFamily`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.originalNorm`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.phi`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.product`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.same_D_consequences`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.sign`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.toFamily`
- Truth anchor: `D5/S3/Quantum/SpinFactor/OriginalClassification.unit`
- Dependency: [D5/S3/Quantum/Algebra/PauliFixedProductFamily](../Algebra/PauliFixedProductFamily.md)
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](../Measurement/FourQubitParentConstruction.md)
- Dependency: [D5/S3/Quantum/SpinFactor/OriginalDContract](OriginalDContract.md)
- Dependency: [D5/S3/Quantum/SpinFactor/OriginalPureRigidity](OriginalPureRigidity.md)
- Dependency: [D5/S3/Quantum/SpinFactor/OriginalResidual](OriginalResidual.md)
