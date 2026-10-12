# Lossy Qubit Partial Joint-Measurability Tightness

## Abstract

Partial joint measurability bounds the efficiency of two lossy projective qubit measurements.

**Definition 1.1 (Lossy measurement effects).**

$$\forall eta \in \mathbb{R},\; \forall r \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall b \in \operatorname{Fin}\left(3\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{effects}\left(eta, r, b, y\right) = \operatorname{ite}\left(b = (2: \operatorname{Fin}\left(3\right)), (1 - eta) \cdot ((1: QubitMatrix)), (eta) \cdot (\operatorname{ActualPureQubitCostInfimum.blochMatrix}\left(1, \operatorname{ite}\left(b = (0: \operatorname{Fin}\left(3\right)), r\left(y\right), -r\left(y\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.effects` (`✓ std3`).

*Citation.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

Equation (13) multiplies each conclusive projector by the efficiency eta and assigns the remaining weight to the identity. The matrix blochMatrix 1 r is the projector (I + r dot sigma)/2 for a unit Bloch vector r. Outcomes zero and one correspond to the positive and negative Bloch directions; outcome two is the no-click outcome. Inputs zero and one select the two measurements.

**Definition 1.2 (The outcomes to be determined).**

$$\forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{G}\left(y\right) = \operatorname{ite}\left(y = (0: \operatorname{Fin}\left(2\right)), \{0, 1\}, (\emptyset: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.G` (`✓ std3`).

*Citation.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

In case (d), both conclusive outcomes of the first input must be determined, and no outcome of the second input is constrained. The indices here start at zero.

**Definition 1.3 (The positive conclusive remainder).**

$$\forall E \in \operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(2\right) \to QubitMatrix\right)\right),\; \forall W \in \operatorname{Fin}\left(2\right) \to QubitMatrix,\; \forall beta \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{starPart}\left(E, W, beta, y\right) = W\left(beta\right) - \sum_{b \in \operatorname{Finset.filter}\left(((b: \operatorname{Fin}\left(3\right)) \mapsto (\neg (b \in \operatorname{G}\left(y\right)))), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right))\right)} (E\left(beta, b, y\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.starPart` (`✓ std3`).

*Citation.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

Definition 2 defines the starred operator by subtracting from the common marginal the effects whose outcomes lie in the complement of G at that input. The complement is taken in Fin 3. Its positivity is a separate condition in GJointMeasurable.

**Definition 1.4 (Partial joint measurability).**

$$\forall eta \in \mathbb{R},\; \forall r \in \operatorname{Fin}\left(2\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; (\operatorname{GJointMeasurable}\left(eta, r\right)) \Leftrightarrow (\exists E \in \operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(3\right) \to \left(\operatorname{Fin}\left(2\right) \to QubitMatrix\right)\right),\; \exists W \in \operatorname{Fin}\left(2\right) \to QubitMatrix,\; (\forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{ConcealmentKernelNecessityRefutation.IsPOVM}\left(((k: \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(3\right)) \mapsto (E\left(\operatorname{Prod.fst}\left(k\right), \operatorname{Prod.snd}\left(k\right), y\right)))\right)) \land ((\forall beta \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \sum_{(b: \operatorname{Fin}\left(3\right))} (E\left(beta, b, y\right)) = W\left(beta\right)) \land ((\forall b \in \operatorname{Fin}\left(3\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{effects}\left(eta, r, b, y\right) = \sum_{(beta: \operatorname{Fin}\left(2\right))} (E\left(beta, b, y\right))) \land ((\forall beta \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{starPart}\left(E, W, beta, y\right)\right)) \land (\forall beta \in \operatorname{Fin}\left(2\right),\; \forall y \in \operatorname{Fin}\left(2\right),\; \forall b \in \operatorname{Fin}\left(3\right),\; (b \in \operatorname{G}\left(y\right)) \Rightarrow (E\left(beta, b, y\right) = \operatorname{ite}\left(b = \operatorname{Fin.castSucc}\left(beta\right), \operatorname{starPart}\left(E, W, beta, y\right), (0: QubitMatrix)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.GJointMeasurable` (`✓ std3`).

*Citation.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

Definition 2 requires a POVM for each input, common marginals across inputs, agreement with the lossy effects, and positive starred operators. For each outcome in G, only the branch whose binary label equals that outcome can contribute, and its effect equals the starred operator. The binary label embeds into Fin 3 by Fin.castSucc.

**Definition 1.5 (The efficiency bound).**

$$(claim) \Leftrightarrow (\forall r \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall s \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \forall eta \in \mathbb{R},\; (\left\lVert r \right\rVert = 1) \Rightarrow ((\left\lVert s \right\rVert = 1) \Rightarrow ((0 \le eta) \Rightarrow ((eta \le 1) \Rightarrow ((\operatorname{GJointMeasurable}\left(eta, ![r, s]\right)) \Rightarrow (eta \cdot (2 + \left\lVert \operatorname{WithLp.toLp}\left(2, \operatorname{crossProduct}\left(\operatorname{WithLp.ofLp}\left(r\right), \operatorname{WithLp.ofLp}\left(s\right)\right)\right) \right\rVert) \le 2))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.claim` (`✓ std3`).

*Citation.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

For any two unit Bloch vectors and any efficiency between zero and one, partial joint measurability implies eta times (2 plus the Euclidean norm of their cross product) is at most 2. Mathlib's crossProduct acts on coordinate functions, and WithLp.toLp 2 equips its value with the Euclidean norm. For unit vectors this norm is the sine of their angle, and hence also the sine of the acute angle between the unoriented axes. This is the necessity direction of the threshold in Eq. (36).

**Theorem 1.6 (Necessity of the threshold).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.result` (`✓ std3`). ∎

*Resolves.* `Problems/lobo-balanzo-juando-pironio-2026-eq36-tightness` (proved) by `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lobo-balanzo-juando-pironio-2026-eq36-tightness","declaration_gid":"D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* E. P. Lobo; M. Balanzó-Juandó; S. Pironio (2026). *Generalized measurement incompatibility*. DOI: [10.48550/arXiv.2605.16151](https://doi.org/10.48550/arXiv.2605.16151). URL: <https://arxiv.org/abs/2605.16151v1>.

*Commentary.*

Write a Hermitian operator as a scalar multiple of the identity plus v dot sigma, so v is its vector of Pauli coefficients. A positive qubit operator dominated by a rank-one projector is a multiple of that projector. At the second input, the conclusive coefficient vectors are therefore parallel to its axis. The coefficient vector of the difference of the two no-click effects has norm at most 1 minus eta at either input. Comparing the common marginal difference across inputs and taking its cross product with the second axis gives eta times the cross-product norm at most twice (1 minus eta). This proves the asserted bound for every axis pair. The source gives the complementary sufficient construction and reports numerical evidence of tightness; the statement here proves necessity exactly.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.G`
- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.GJointMeasurable`
- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.effects`
- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.result`
- Truth anchor: `D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness.starPart`
- Dependency: [D5/S3/Quantum/Measurement/FourQubitParentConstruction](FourQubitParentConstruction.md)
