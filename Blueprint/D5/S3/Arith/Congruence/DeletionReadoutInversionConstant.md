# Deletion Readout Inversion Constant

## Abstract

Full-deletion readings determine every coordinate with an attained product constant.

**Definition 1.1 (Deletion reading).**

$$\forall r: \mathbb{N}, m: (\operatorname{Fin}\left(r\right)) \to \mathbb{N},\\{}T: \operatorname{Finset}\left(\operatorname{Fin}\left(r\right)\right), a: \prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right), z: (\prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right)) \to \mathbb{R},\\{}\operatorname{R}\left(T, a, z\right) := \sum_{c \in \prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right)} \operatorname{z}\left(c\right) \cdot \prod_{i \in T} \mathbf {1}_{c_{i} \neq a_{i}}.$$

*Formalization.* `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each selected coordinate, the factor vanishes exactly when the configuration takes the deleted value. Thus the sum retains precisely the configurations avoiding every prescribed value in T.

**Definition 1.2 (Observation norm).**

$$\forall r: \mathbb{N}, m: (\operatorname{Fin}\left(r\right)) \to \mathbb{N}, \forall i \in \operatorname{Fin}\left(r\right), 2 \le m_{i},\\{}z: (\prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right)) \to \mathbb{R},\\{}\operatorname{obsNorm}\left(z\right) := \operatorname{max}_{T \subseteq \operatorname{Fin}\left(r\right), a \in \prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right)} \lvert \operatorname{R}\left(T, a, z\right) \rvert.$$

*Formalization.* `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.obsNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum ranges over every coordinate subset and every dependent tuple of deleted values. The lower bound on each alphabet size makes this finite indexing family nonempty.

**Definition 1.3 (Tensor inverse row sum).**

$$\forall r: \mathbb{N}, m: (\operatorname{Fin}\left(r\right)) \to \mathbb{N},\\{}kappa(m) := \prod_{i \in \operatorname{Fin}\left(r\right)} (2 - \frac{1}{m_{i} - 1}).$$

*Formalization.* `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each factor is the absolute row sum of J divided by m_i minus one, minus the identity. Their product is the tensor inverse row sum.

**Theorem 1.4 (Sharp full-deletion inversion bound).**

$$\forall r: \mathbb{N}, m: (\operatorname{Fin}\left(r\right)) \to \mathbb{N}, \forall i \in \operatorname{Fin}\left(r\right), 2 \le m_{i},\\{}z: (\prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right)) \to \mathbb{R},\\{}(\forall c: \prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right), \lvert \operatorname{z}\left(c\right) \rvert \le \operatorname{kappa}\left(m\right) \cdot \operatorname{obsNorm}\left(z\right)) \land \\{}\forall c^{*}: \prod_{i \in \operatorname{Fin}\left(r\right)} \operatorname{Fin}\left(m_{i}\right),\\{}\operatorname{let} w(c) := \prod_{i \in \operatorname{Fin}\left(r\right)} (\operatorname{if} c_{i} = {c^{*}}_{i} \operatorname{then} 2 \cdot m_{i} - 3 \operatorname{else} -1),\\{}\operatorname{obsNorm}\left(w\right) = \prod_{i \in \operatorname{Fin}\left(r\right)} (m_{i} - 1) \land \lvert \operatorname{w}\left(c^{*}\right) \rvert = \operatorname{kappa}\left(m\right) \cdot \operatorname{obsNorm}\left(w\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.deletion_readout_inversion_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate matrix J minus I is inverted by J divided by m_i minus one, minus I. Tensoring these inverses reconstructs each coefficient from the full-deletion readings, and the absolute row sums factor.

For the displayed vector w, each coordinate sum is m_i minus two and each deleted coordinate sum has absolute value m_i minus one. Consequently every reading factors coordinatewise, the full deletion reading attains the observation norm, and the coefficient at the distinguished tuple attains the inversion bound.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.R`
- Truth anchor: `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.deletion_readout_inversion_constant`
- Truth anchor: `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.kappa`
- Truth anchor: `D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.obsNorm`
