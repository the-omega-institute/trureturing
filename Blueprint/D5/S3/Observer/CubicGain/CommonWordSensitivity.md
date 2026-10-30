# Common-word source sensitivity

## Abstract

Uniform golden growth of common-word response errors in original source coordinates.

An original coefficient world W stores r,b,d and the four ordinary coefficients k of one polynomial g(s)=k₀+k₁s+k₂s²+k₃s³. Its source is the existing P=sourceMatrix(r,b)=[[r,b],[r(1-r)/b,1-r]]. The result below holds on the entire OriginalWorld product carrier, and in particular on every original parent world. It includes lower degrees, zero samples, repeated roots and zero drift. No polynomial is fitted to a later window.

**Definition 1.1 (Chronological future product).**

Lean statement: `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureProduct`

*Formalization.* `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every Boolean word u, futureProduct([])=I and futureProduct(e::u)=futureProduct(u)E(e), where E(true)=J=[[0,1],[1,0]] and E(false)=M=[[0,1],[1,1]]. The head acts first, so the terminal product is Eₙ⋯E₁. The empty future word has product I.

**Definition 1.2 (Clock-eight product).**

Lean statement: `D5/S3/Observer/CubicGain/CommonWordSensitivity.clockEight`

*Formalization.* `D5/S3/Observer/CubicGain/CommonWordSensitivity.clockEight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

clockEight=M J chronological(6)=[[3,1],[8,3]]. Thus the initial six actions J,M,J,M,M,M are followed by J and M. Future actions multiply on the left of this actual clock-eight product.

**Definition 1.3 (Absolute-clock numerical response).**

Lean statement: `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureRead`

*Formalization.* `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureRead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original coefficient world W and every future word u of length n, Y(W,u)=futureRead(W,u)=d+g(8+n)tr(futureProduct(u) clockEight P). The same P, g and d occur at every clock. This is numerical evaluation, with no claim that an additional action or read has been acquired.

**Definition 1.4 (Original eight coordinates).**

Lean statement: `D5/S3/Observer/CubicGain/CommonWordSensitivity.sourceCoordinates`

*Formalization.* `D5/S3/Observer/CubicGain/CommonWordSensitivity.sourceCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every W, omega(W)=sourceCoordinates(W)=(r,b,r(1-r)/b,d,k₀,k₁,k₂,k₃). Distances use the ordinary maximum norm on these eight coordinates. Write B(W,H) for the condition that every one of the eight coordinate absolute values is at most H. Write script W for OriginalWorld and n(u) for the natural length of u.

**Theorem 1.5 (Uniform original-source sensitivity).**

$$\forall W,W'\in \mathcal{W}, \forall H\in \mathbb{R}, (H\geq 1\land \operatorname{B}(W,H)\land \operatorname{B}(W',H))\implies \forall u\in \{J,M\}^{*}, \lvert \operatorname{Y}(W,u)-\operatorname{Y}(W',u)\rvert \leq (1+1048576H)\varphi^{\operatorname{n}(u)}(1+\operatorname{n}(u))^{3}\Vert \operatorname{omega}(W)-\operatorname{omega}(W')\Vert _{\infty}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CommonWordSensitivity.common_word_source_sensitivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let phi=(1+sqrt(5))/2. The displayed theorem quantifies over both original worlds, H and every finite word. H is a common coordinate bound, and the distance is the eight-coordinate source distance. The coefficient 1048576 is a conservative uniform constant.

For v=(1,phi), each native action has nonnegative entries and sends v below phi v coordinatewise. Induction on chronological words gives sum_j Tᵤ(i,j)vⱼ≤phiⁿvᵢ, while preserving nonnegativity. Since 1≤vᵢ<2, every entry of Tᵤ is at most 2phiⁿ. Multiplication by the fixed clock-eight matrix bounds every advanced entry by 32phiⁿ. The four terms of its trace pairing with a matrix whose entries have absolute value at most H are therefore bounded by 128phiⁿH.

At the absolute clock 8+n, a cubic with coefficient absolute values bounded by H has absolute value at most 2048H(1+n)³. The same estimate applied to the coefficient difference bounds the gain difference by 2048(1+n)³ times the source distance. Every source-matrix entry is bounded by 2H, including 1-r, and every source-matrix entry difference is bounded by the source distance. Splitting the response difference into drift, gain and source terms gives the displayed inequality. The bound is uniform in the word and its length.

This result supplies the source-coordinate part of response stability. It does not construct a compact original preimage or prove an inverse Lipschitz estimate from acquired boundary coordinates. In particular the source distance here has not been replaced by the distance between acquired records. The bound makes no claim about execution rights, new observations, physical installation or a universal finite prediction error.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/CommonWordSensitivity.clockEight`
- Truth anchor: `D5/S3/Observer/CubicGain/CommonWordSensitivity.common_word_source_sensitivity`
- Truth anchor: `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureProduct`
- Truth anchor: `D5/S3/Observer/CubicGain/CommonWordSensitivity.futureRead`
- Truth anchor: `D5/S3/Observer/CubicGain/CommonWordSensitivity.sourceCoordinates`
- Dependency: [D5/S3/Observer/CubicGain/OriginalWorld](OriginalWorld.md)
