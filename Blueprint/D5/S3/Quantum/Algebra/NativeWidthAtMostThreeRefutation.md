# The original inner-cone flat-spectrum event is false

## Abstract

The original universal inner-cone event is false: unrestricted native width-three factors cannot have a positive scalar column Gram at dimensions (3,5,3,5).

**Definition 1.1 (The complete original universal event).**

$$claim = \left(\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; (0 < a) \Rightarrow ((a \le b) \Rightarrow ((0 < c) \Rightarrow ((c \le d) \Rightarrow ((a \cdot a + b \cdot b \le 3 \cdot a \cdot b) \Rightarrow ((c \cdot c + d \cdot d \le 3 \cdot c \cdot d) \Rightarrow ((b \le 2 \cdot a) \Rightarrow ((d \le 2 \cdot c) \Rightarrow (\exists M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \exists N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \exists lambda \in Real,\; (0 < lambda) \land (((b \cdot c \le a \cdot d) \Rightarrow (\operatorname{conjTranspose}\left(\operatorname{flow}\left(M, N\right)\right) \cdot \operatorname{flow}\left(M, N\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), \operatorname{identity}\left(\operatorname{prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right)\right)\right))) \land ((a \cdot d \le b \cdot c) \Rightarrow (\operatorname{flow}\left(M, N\right) \cdot \operatorname{conjTranspose}\left(\operatorname{flow}\left(M, N\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), \operatorname{identity}\left(\operatorname{prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(d\right)\right)\right)\right))))))))))))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four dimensions are natural numbers. The eight premises are 0<a, a<=b, 0<c, c<=d, a*a+b*b<=3*a*b, c*c+d*d<=3*c*d, b<=2*a and d<=2*c. The existential M and N are unrestricted complex triples of a-by-b and d-by-c matrices. One real lambda>0 and the same M,N witness both implications. F=QuantumMaxFlowBound.flow M N has native rows Fin a times Fin d and columns Fin b times Fin c. At equality of a*d and b*c, both column and row Gram identities are required with that same lambda. No independence, normalization, coefficient-kernel, plane or classification premise is present.

**Theorem 1.2 (Unrestricted native positive-scalar obstruction).**

$$\forall M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(5\right), Complex\right),\; \forall N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right), Complex\right),\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow (\operatorname{conjTranspose}\left(\sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right))\right) \cdot \sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)) \ne \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), \operatorname{identity}\left(\operatorname{prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.positive_scalar_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary M:Fin 3->Matrix(Fin 3)(Fin 5) Complex and N:Fin 3->Matrix(Fin 5)(Fin 3) Complex, and every real lambda>0, the native column Gram cannot equal lambda times I on Fin 5 times Fin 3. Choose a least-width decomposition of the original Kronecker sum. If either family is dependent, select a nonzero relation coefficient and delete that index using Fin.succAbove, absorbing its right or left factor into the other factors; the sum is unchanged. Minimality therefore supplies independent families A,D of width k<=3, including k=0. Multiply A by c=((sqrt lambda) inverse:Real):Complex. The compiled scalar identity star(c)*c*lambda=1 gives an identity Gram without changing either native product carrier. Scaling by nonzero c preserves independence. This is a derived reduction, not a new hypothesis.

**Theorem 1.3 (The simultaneous complex-plane consumer).**

$$\forall M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(5\right), Complex\right),\; \forall N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right), Complex\right),\; (\operatorname{LinearIndependent}\left(Complex, M\right)) \Rightarrow ((\operatorname{LinearIndependent}\left(Complex, N\right)) \Rightarrow (\operatorname{conjTranspose}\left(\sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right))\right) \cdot \sum_{r : \operatorname{Fin}\left(3\right)} (\operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)) \ne \operatorname{identity}\left(\operatorname{prod}\left(\operatorname{Fin}\left(5\right), \operatorname{Fin}\left(3\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.native_three_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For independent native triples the Gram identity is impossible. Define H_rs=(1/3)*trace(N(r)* N(s)), where the star denotes conjugate transpose. Flattening N proves H positive definite. Its invertible factorization H=B*B gives M'=BM and N'=B inverse transpose N. The coefficient contraction B transpose times B inverse transpose equals I, so the Kronecker sum is preserved. Partial trace of the original Gram identity derives sum_r M'(r)* M'(r)=I_5. Independence of M is preserved. The coefficient-first stack S is therefore injective. Apply CommonCoefficientPlane.common_plane to this actual M', obtaining one complex two-dimensional plane neutral for every Hermitian coefficient-kernel form. For every physical column pair l,m, expansion of the Gram identity places T_lm(r,s)=(N'(r)* N'(s))_lm-delta_rs delta_lm in the complex compression kernel. Compression commutes with conjugate transpose, so the Hermitian real and imaginary parts both lie in that kernel. The same plane annihilates their full pairings, hence also T_lm, including off-diagonal l,m and the zero-kernel case. Transport the plane by WithLp to EuclideanSpace and choose an orthonormal basis V with V*V=I_2. Set W_j,(r,l)=N'(r)_j,l, P=W*W and C=V tensor I_3. The neutral block equations prove C*PC=I_6. Rank inequalities yield 6<=rank(W)<=5.

**Theorem 1.4 (Literal refutation of the original event).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the original universal claim at (a,b,c,d)=(3,5,3,5). Both quadratic premises read 34<=45 and both ratio premises read 5<=6; all eight premises hold. Both products are 15, so both original implications apply to the same witnesses and scalar. The column implication alone contradicts positive_scalar_obstruction. All reduced widths are discharged: k=0 gives zero Gram versus identity; k=1 has a nonzero native tensor-kernel vector because a 3-by-5 map is not injective; k=2 is whitened and its 6-by-5 injective stack has trivial coefficient compression kernel, forcing N'(r)*N'(s)=delta_rs I_3. Its concatenation would then have six orthonormal columns in five rows. The rank-Kronecker helper used for k=2 has a genuinely arbitrary coefficient width; the Fin 3-only supplier is not applied to Fin 2. The k=3 contradiction is the simultaneous complex-plane argument above. This proves the stated universal event false. No optimal threshold, minimal counterexample or physical realization is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.native_three_refutation`
- Truth anchor: `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.positive_scalar_obstruction`
- Truth anchor: `D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.result`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](CommonCoefficientPlane.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](../TensorNetworks/BridgeGraph/QuantumMaxFlowBound.md)
