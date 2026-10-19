# Binary Renyi combining

## Abstract

Binary Renyi entropy and binary convolution supply shared scalar definitions for information combining.

**Definition 1.1 (Binary Renyi entropy).**

$$\forall alpha \in \mathbb{R},\; \forall p \in \mathbb{R},\; \operatorname{hRenyi}\left(alpha, p\right) = \frac{1}{1 - alpha} \cdot \operatorname{Real.log}\left(p^{alpha} + \left(1 - p\right)^{alpha}\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.hRenyi` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

Page 2, before Theorem I.1: "In the following, we denote the binary Rényi entropy as hα." The formula is the binary specialization of Renyi entropy with natural logarithms. Real powers are explicit in its Lean definition.

**Definition 1.2 (Binary convolution).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \operatorname{bconv}\left(p, q\right) = p \cdot \left(1 - q\right) + \left(1 - p\right) \cdot q$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.bconv` (`✓ std3`).

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

The star in the source denotes binary convolution: the probability that two independent binary variables have different values.

**Theorem 1.3 (Binary convolution multiplies biases).**

$$\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; 1 - 2 \cdot \operatorname{bconv}\left(p, q\right) = \left(1 - 2 \cdot p\right) \cdot \left(1 - 2 \cdot q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.bconv_bias` (`✓ std3`). ∎

*Citation.* Christoph Hirche; Xinyue Guan; Marco Tomamichel (2023). *Chain Rules for Rényi Information Combining*. DOI: [10.1109/ISIT54713.2023.10206941](https://doi.org/10.1109/ISIT54713.2023.10206941). URL: <https://arxiv.org/abs/2305.02589v1>.

*Commentary.*

The polynomial identity holds for all real inputs. For binary probabilities, it expresses the bias of the XOR as the product of the two input biases. The order-three equality and the Hirche concavity argument both use this identity.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.bconv`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.bconv_bias`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining.hRenyi`
