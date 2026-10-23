# A product decomposition of the generalized CHSH groups

## Abstract

For every n at least two, the presented generalized CHSH group is a semidirect product of C_(2n) x C_2^(n-2) by C_n, with an explicit cyclic action.

**Definition 1.1 (The first free generator).**

$$\operatorname{P0} = \operatorname{FreeGroup}.\operatorname{of}\left(0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.P0` (`✓ std3`).

*Citation.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

P0 is generator 0 of FreeGroup (Fin 3), representing the paper's P_0.

**Definition 1.2 (The second free generator).**

$$\operatorname{P1} = \operatorname{FreeGroup}.\operatorname{of}\left(1\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.P1` (`✓ std3`).

*Citation.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

P1 is generator 1 of FreeGroup (Fin 3), representing the paper's P_1.

**Definition 1.3 (The central free generator).**

$$\operatorname{J} = \operatorname{FreeGroup}.\operatorname{of}\left(2\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.J` (`✓ std3`).

*Citation.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

J is generator 2 of FreeGroup (Fin 3), representing the paper's J.

**Definition 1.4 (The relator set).**

$$\forall n \in \mathbb{N},\; \operatorname{rels}\left(n\right) = \left\{\operatorname{P0}^{n}, \operatorname{P1}^{n}, \operatorname{J}^{n}, \operatorname{commutatorElement}\left(\operatorname{J}, \operatorname{P0}\right), \operatorname{commutatorElement}\left(\operatorname{J}, \operatorname{P1}\right)\right\} \cup \{r: \operatorname{FreeGroup}\left(\operatorname{Fin}\left(3\right)\right) \mid \exists i \in \mathbb{N},\; (1 \le i) \land ((i \le \operatorname{Nat}.\operatorname{div}\left(n, 2\right)) \land (r = \operatorname{J}^{i} \cdot \left(\operatorname{P0}^{i} \cdot \operatorname{P1}^{-(i: \mathbb{Z})}\right)^{2}))\}$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.rels` (`✓ std3`).

*Citation.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

Section 5, printed p. 24, defines: G_n = <P_0, P_1, J | P_0^n, P_1^n, J^n, [J, P_0], [J, P_1], J^i(P_0^iP_1^(-i))^2 for 1 <= i <= floor(n/2)>. These words are equal to the identity. The index i is natural; its negated exponent is cast to the integers. Nat.div n 2 is natural division, with value floor(n/2).

**Definition 1.5 (The presented group).**

$$\forall n \in \mathbb{N},\; \operatorname{G}\left(n\right) = \operatorname{PresentedGroup}\left(\operatorname{rels}\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.G` (`✓ std3`).

*Citation.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

G n is the quotient of the free group on these three generators by the normal closure of rels n, the group G_n of Section 5.

**Definition 1.6 (The abelian factor).**

$$\forall n \in \mathbb{N},\; \operatorname{L}\left(n\right) = \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2 \cdot n\right)\right) \times (\operatorname{Fin}\left(n - 2\right) \to \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

L n is C_(2n) times n-2 independent copies of C_2. Fin (n-2) indexes the independent involutions; subtraction here is natural subtraction.

**Definition 1.7 (A homomorphism out of a cyclic group).**

$$\forall H \in \operatorname{Type},\; [\operatorname{Group}\left(H\right)], \forall n \in \mathbb{N},\; \forall a \in H,\; \forall ha \in a^{n} = 1,\; \operatorname{cyclicHom}\left(n, a, ha\right) = \operatorname{AddMonoidHom}.\operatorname{toMultiplicativeLeft}\left(\operatorname{ZMod}.\operatorname{lift}\left(n, \langle \operatorname{zmultiplesHom}\left(\operatorname{Additive}\left(H\right), \operatorname{Additive}.\operatorname{ofMul}\left(a\right)\right), (\operatorname{zmultiplesHom}\left(\operatorname{Additive}\left(H\right), \operatorname{Additive}.\operatorname{ofMul}\left(a\right)\right)\left((n: \mathbb{Z})\right) = 0) \rangle\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.cyclicHom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

For a^n = 1, cyclicHom sends the additive residue of an integer j to a^j. It uses the additive universal map ZMod.lift and the multiplicative type conversion. The parenthesized proposition in the subtype constructor is its constructor proof field: zmultiplesHom sends the integer n to zero.

**Theorem 1.8 (Evaluation on an integer residue).**

$$\forall H \in \operatorname{Type},\; [\operatorname{Group}\left(H\right)], \forall n \in \mathbb{N},\; \forall a \in H,\; \forall ha \in a^{n} = 1,\; \forall i \in \mathbb{Z},\; \operatorname{cyclicHom}\left(n, a, ha, \operatorname{ofAdd}\left((i: \operatorname{ZMod}\left(n\right))\right)\right) = a^{i}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.cyclicHom_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

For every group H, natural n, element a with a^n = 1 and integer i, cyclicHom n a ha sends ofAdd (i : ZMod n) to the integer power a^i.

**Definition 1.9 (The cyclic generator).**

$$\forall n \in \mathbb{N},\; \operatorname{s}\left(n\right) = (\operatorname{ofAdd}\left(1\right), 1)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.s` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

The first component is 1 in ZMod (2*n), converted to multiplicative notation; the function component is constantly the identity.

**Definition 1.10 (The independent involutions).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n - 2\right),\; \operatorname{t}\left(n, i\right) = (1, \operatorname{Pi}.\operatorname{mulSingle}\left(i, \operatorname{ofAdd}\left(1\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.t` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

t n i has first component 1 and is 1 except for ofAdd 1 at i in its function component. The paper's one-based index is i.val+1.

**Definition 1.11 (The homomorphism from the abelian factor).**

$$\forall H \in \operatorname{Type},\; [\operatorname{Group}\left(H\right)], \forall n \in \mathbb{N},\; \forall a \in H,\; \forall b \in \operatorname{Fin}\left(n - 2\right) \to H,\; \forall ha \in a^{2 \cdot n} = 1,\; \forall hb \in \left(\forall i \in \operatorname{Fin}\left(n - 2\right),\; b\left(i\right)^{2} = 1\right),\; \forall hc \in \left(\forall i \in \operatorname{Fin}\left(n - 2\right),\; \forall j \in \operatorname{Fin}\left(n - 2\right),\; \operatorname{Commute}\left(b\left(i\right), b\left(j\right)\right)\right),\; \forall hd \in \left(\forall i \in \operatorname{Fin}\left(n - 2\right),\; \operatorname{Commute}\left(a, b\left(i\right)\right)\right),\; \operatorname{liftL}\left(n, a, b, ha, hb, hc, hd\right) = \operatorname{MonoidHom}.\operatorname{noncommCoprod}\left(\operatorname{cyclicHom}\left(2 \cdot n, a, ha\right), \operatorname{MonoidHom}.\operatorname{noncommPiCoprod}\left(\operatorname{fun} i: \operatorname{Fin}\left(n - 2\right) \mapsto \operatorname{cyclicHom}\left(2, b\left(i\right), hb\left(i\right)\right), (\forall i \in \operatorname{Fin}\left(n - 2\right),\; \forall j \in \operatorname{Fin}\left(n - 2\right),\; i \ne j \Rightarrow \left(\forall x \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \forall y \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{Commute}\left(\operatorname{cyclicHom}\left(2, b\left(i\right), hb\left(i\right)\right)\left(x\right), \operatorname{cyclicHom}\left(2, b\left(j\right), hb\left(j\right)\right)\left(y\right)\right)\right))\right), (\forall x \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2 \cdot n\right)\right),\; \forall y \in \operatorname{Fin}\left(n - 2\right) \to \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{Commute}\left(\operatorname{cyclicHom}\left(2 \cdot n, a, ha\right)\left(x\right), \operatorname{MonoidHom}.\operatorname{noncommPiCoprod}\left(\operatorname{fun} i: \operatorname{Fin}\left(n - 2\right) \mapsto \operatorname{cyclicHom}\left(2, b\left(i\right), hb\left(i\right)\right), (\forall i \in \operatorname{Fin}\left(n - 2\right),\; \forall j \in \operatorname{Fin}\left(n - 2\right),\; i \ne j \Rightarrow \left(\forall x \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \forall y \in \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right),\; \operatorname{Commute}\left(\operatorname{cyclicHom}\left(2, b\left(i\right), hb\left(i\right)\right)\left(x\right), \operatorname{cyclicHom}\left(2, b\left(j\right), hb\left(j\right)\right)\left(y\right)\right)\right))\right)\left(y\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.liftL` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

The images a and b i satisfy a^(2*n) = 1, (b i)^2 = 1 and commute pairwise. noncommPiCoprod forms the map from the involution factors and noncommCoprod joins it to the cyclic factor. The parenthesized propositions display the full proof arguments: images from distinct involution factors commute, and each cyclic-factor image commutes with each image of the involution product.

**Definition 1.12 (The product of independent involutions).**

$$\forall n \in \mathbb{N},\; \operatorname{ts}\left(n\right) = \prod_{i\in \operatorname{Fin}\left(n - 2\right)} \operatorname{t}\left(n, i\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.ts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

ts multiplies all independent involutions over Fin (n-2); the product is 1 when n = 2.

**Definition 1.13 (The dependent last involution).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{u}\left(n, k\right) = \operatorname{if} (1 \le k) \land (k \le n - 2) \operatorname{then} \operatorname{t}\left(n, \langle k - 1, (k - 1 < n - 2) \rangle\right) \operatorname{else} \operatorname{if} k = n - 1 \operatorname{then} \operatorname{s}\left(n\right)^{n} \cdot \operatorname{ts}\left(n\right) \operatorname{else} 1$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

For 1 <= k <= n-2, u n k is t n at the finite index k-1. At k = n-1 outside that interval it is s n raised to n times ts n; at all other indices it is 1. The parenthesized proposition k-1 < n-2 is the Fin constructor proof field under the first branch's condition. This definition also fixes the values for n below two.

**Definition 1.14 (The cyclic orbit coordinates).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{e}\left(n, k\right) = \operatorname{s}\left(n\right) \cdot \operatorname{u}\left(n, k\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.e` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

e n k is s n times the k-th extended involution. For n at least two, e n 0 = e n n = s n.

**Definition 1.15 (One cyclic step).**

$$\forall n \in \mathbb{N},\; \operatorname{step}\left(n\right) = \operatorname{liftL}\left(n, \operatorname{e}\left(n, 1\right), \operatorname{fun} i: \operatorname{Fin}\left(n - 2\right) \mapsto \operatorname{e}\left(n, \operatorname{val}\left(i\right) + 2\right) \cdot \operatorname{e}\left(n, 1\right)^{-1}, (\operatorname{e}\left(n, 1\right)^{2 \cdot n} = 1), (\forall i \in \operatorname{Fin}\left(n - 2\right),\; \left(\operatorname{e}\left(n, \operatorname{val}\left(i\right) + 2\right) \cdot \operatorname{e}\left(n, 1\right)^{-1}\right)^{2} = 1), (\forall i \in \operatorname{Fin}\left(n - 2\right),\; \forall j \in \operatorname{Fin}\left(n - 2\right),\; \operatorname{Commute}\left(\operatorname{e}\left(n, \operatorname{val}\left(i\right) + 2\right) \cdot \operatorname{e}\left(n, 1\right)^{-1}, \operatorname{e}\left(n, \operatorname{val}\left(j\right) + 2\right) \cdot \operatorname{e}\left(n, 1\right)^{-1}\right)), (\forall i \in \operatorname{Fin}\left(n - 2\right),\; \operatorname{Commute}\left(\operatorname{e}\left(n, 1\right), \operatorname{e}\left(n, \operatorname{val}\left(i\right) + 2\right) \cdot \operatorname{e}\left(n, 1\right)^{-1}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

step sends s to e n 1 and each t n i to e n (i.val+2) times the inverse of e n 1. Its four parenthesized proof arguments assert order dividing 2*n for the first image, square one for each involution image, pairwise commutation of those images, and their commutation with the first image.

**Definition 1.16 (The cyclic automorphism).**

$$\forall n \in \mathbb{N},\; \forall hn \in 2 \le n,\; \operatorname{stepAut}\left(n, hn\right) = \operatorname{MulEquiv}.\operatorname{mk}\left(\operatorname{Equiv}.\operatorname{mk}\left(\operatorname{step}\left(n\right), \operatorname{step}\left(n\right)^{[n - 1]}, (\forall x \in \operatorname{L}\left(n\right),\; \left(\operatorname{step}\left(n\right)^{[n - 1]}\right)\left(\operatorname{step}\left(n\right)\left(x\right)\right) = x), (\forall x \in \operatorname{L}\left(n\right),\; \operatorname{step}\left(n\right)\left(\left(\operatorname{step}\left(n\right)^{[n - 1]}\right)\left(x\right)\right) = x)\right), (\forall x \in \operatorname{L}\left(n\right),\; \forall y \in \operatorname{L}\left(n\right),\; \operatorname{step}\left(n\right)\left(x \cdot y\right) = \operatorname{step}\left(n\right)\left(x\right) \cdot \operatorname{step}\left(n\right)\left(y\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.stepAut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

For n at least two, step iterated n times is the identity on L n. stepAut has forward function step n and inverse function the (n-1)-fold iterate of step n. The parenthesized propositions are constructor proof fields: the two Equiv.mk fields assert the inverse identities for every x in L n, and the MulEquiv.mk field asserts preservation of multiplication for every x and y in L n.

**Definition 1.17 (The action of C_n).**

$$\forall n \in \mathbb{N},\; \operatorname{alpha}\left(n\right) = \operatorname{if} hn: 2 \le n \operatorname{then} \operatorname{cyclicHom}\left(n, \operatorname{stepAut}\left(n, hn\right), (\operatorname{stepAut}\left(n, hn\right)^{n} = 1)\right) \operatorname{else} 1$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

For n at least two, alpha maps ofAdd 1 to stepAut n. Thus alpha(s) = s times u n 1 and alpha(t n i) = u n (i.val+2) times u n 1. The dependent last involution gives the wrap-around. The parenthesized proof argument asserts that stepAut n hn raised to n is the identity automorphism under the branch hypothesis hn. For n below two, alpha is the constant identity homomorphism.

**Definition 1.18 (The uniform decomposition).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \operatorname{Nonempty}\left(\operatorname{MulEquiv}\left(\operatorname{G}\left(n\right), \operatorname{SemidirectProduct}\left(\operatorname{L}\left(n\right), \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(n\right)\right), \operatorname{alpha}\left(n\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

Section 1.4 (Further work), item 2, printed p. 7: "In Section 5, we give efficient explicit presentations for G_n and its multiplication table. Can we go further and characterize these groups in terms of direct and semidirect products of small well-known groups? The first few cases are as follows" The encoding answers this question for every natural n >= 2 by an actual multiplicative equivalence. C_m is Multiplicative (ZMod m); the elementary abelian factor uses Fin (n-2), and alpha is the displayed action.

**Theorem 1.19 (The decomposition theorem).**

$$\forall n \in \mathbb{N},\; 2 \le n \Rightarrow \operatorname{Nonempty}\left(\operatorname{MulEquiv}\left(\operatorname{G}\left(n\right), \operatorname{SemidirectProduct}\left(\operatorname{L}\left(n\right), \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(n\right)\right), \operatorname{alpha}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result` (`✓ std3`). ∎

*Resolves.* `Problems/cui-mehta-mousavi-nezhadi-2020-chsh-group-decomposition` (proved) by `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cui-mehta-mousavi-nezhadi-2020-chsh-group-decomposition","declaration_gid":"D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Cui; A. Mehta; H. Mousavi; S. S. Nezhadi (2020). *A generalization of CHSH and the algebraic structure of optimal strategies*. DOI: [10.22331/q-2020-10-21-346](https://doi.org/10.22331/q-2020-10-21-346). URL: <https://arxiv.org/abs/1911.01593>.

*Commentary.*

The forward homomorphism sends P0 to inr(ofAdd 1), P1 to inl(s) times inr(ofAdd 1), and J to inl(s^2). In the presented group, the elements P0^i P1^(-i) commute, allowing the inverse map from L. Its compatibility with conjugation by P0 gives a homomorphism from the semidirect product. Both composites fix the generators, so the maps form a multiplicative equivalence. No group-order computation is used.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.G`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.J`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.L`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.P0`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.P1`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.alpha`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.cyclicHom`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.cyclicHom_int`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.e`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.liftL`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.rels`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.result`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.s`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.step`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.stepAut`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.t`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.ts`
- Truth anchor: `D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition.u`
