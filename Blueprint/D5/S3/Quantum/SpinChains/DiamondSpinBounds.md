# Native operators and bounds for the equal-spin diamond

## Abstract

Native normalized spin operators on four complete complex factors satisfy weight invariance, singlet isotropy and a uniform pair-order bound.

Let S be a natural number. Each of the four factors is the complete complex spin-S space with orthonormal basis indexed by W(S) = Fin(2S+1). Index r has weight S−r; the native normalized raising matrix Jplus(2S) has coefficient √((r+1)(2S−r)) from r+1 to r, with zero endpoint, and lowering is its adjoint. Put C(S) = Fin(4) → W(S), V(S) = C(S) → ℂ and O(S) = Matrix(C(S),C(S),ℂ). Norms are the Euclidean norms and inner products conjugate the first argument. Matrices act on every complex superposition in V(S). Sites 0,1,2,3 correspond to vertices 1,2,3,4. A submodule infimum denotes intersection; bottom is the zero submodule.

**Definition 1.1 (An operator at one site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (x: \operatorname{C}\left(S\right)), (\forall (y: \operatorname{C}\left(S\right)), (\operatorname{site}\left(S, i, A, x, y\right) = \operatorname{A}\left(x\left(i\right), y\left(i\right)\right) \cdot \operatorname{prodExcept}\left(i, x, y\right))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.site` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

prodExcept(i,x,y) is the product of Kronecker deltas δ(xⱼ,yⱼ) over the three sites j≠i. Thus site is exactly the tensor placement of A with identities on all other factors.

**Definition 1.2 (The raising operator at a site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{raising}\left(S, i\right) = \operatorname{site}\left(S, i, \operatorname{Jplus}\left(2 \cdot S\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.raising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the normalized native raising matrix on the full factor.

**Definition 1.3 (The lowering operator at a site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{lowering}\left(S, i\right) = \operatorname{site}\left(S, i, (\operatorname{Jplus}\left(2 \cdot S\right))^{*}\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.lowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjoint convention includes both ladder endpoints.

**Definition 1.4 (The five edges).**

$$\operatorname{edges} = \operatorname{finset}\left((0,1), (0,2), (0,3), (1,2), (1,3)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each listed unordered edge is included once. The absent edge is (2,3); there are no loops or additional coefficients.

**Definition 1.5 (The diamond Hamiltonian).**

$$\forall (S: \mathbb{N}), (\operatorname{hamiltonian}\left(S\right) = \sum_{(i,j)\in\operatorname{edges}} 2 \cdot (\operatorname{X}\left(i\right) \cdot \operatorname{X}\left(j\right) + \operatorname{Y}\left(i\right) \cdot \operatorname{Y}\left(j\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.hamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing Xᵢ=site(S,i,Jx(2S)) and Yᵢ=site(S,i,Jy(2S)), this is 2Σedges(XᵢXⱼ+YᵢYⱼ). The native Cartesian identity proves it equals Σedges(Jᵢ⁺Jⱼ⁻+Jᵢ⁻Jⱼ⁺), with coefficient +1 on each of the five edges. Operators at distinct sites commute, so the Hamiltonian is Hermitian.

**Definition 1.6 (Total raising).**

$$\forall (S: \mathbb{N}), (\operatorname{totalRaising}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{raising}\left(S, i\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalRaising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over all four sites.

**Definition 1.7 (Total lowering).**

$$\forall (S: \mathbb{N}), (\operatorname{totalLowering}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{lowering}\left(S, i\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalLowering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the adjoint of total raising.

**Definition 1.8 (Total weight).**

$$\forall (S: \mathbb{N}), (\operatorname{totalWeight}\left(S\right) = \sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{site}\left(S, i, \operatorname{Jz}\left(2 \cdot S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At configuration x its diagonal entry is 4S−Σᵢxᵢ. The Hamiltonian commutes with total weight.

**Definition 1.9 (The entire singlet space).**

$$\forall (S: \mathbb{N}), (\operatorname{singletSpace}\left(S\right) = \operatorname{inf}\left(\operatorname{ker}\left(\operatorname{totalRaising}\left(S\right)\right), \operatorname{ker}\left(\operatorname{totalLowering}\left(S\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.singletSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both kernels are taken on V(S). No pair-coupling sector or multiplicity is selected. The total ladder commutator implies that every vector here has total weight zero.

**Definition 1.10 (The entire zero-weight space).**

$$\forall (S: \mathbb{N}), (\operatorname{zeroWeightSpace}\left(S\right) = \operatorname{ker}\left(\operatorname{totalWeight}\left(S\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.zeroWeightSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It consists exactly of vectors supported on configurations Z(S) with Σᵢxᵢ=4S. These coordinate vectors form an orthonormal basis of the entire kernel. The middle configuration xᵢ=S belongs to Z(S), including at S=0.

**Definition 1.11 (The actual Hermitian restriction).**

$$\forall (S: \mathbb{N}), (\forall (x: \operatorname{Z}\left(S\right)), (\forall (y: \operatorname{Z}\left(S\right)), (\operatorname{restrictedHamiltonian}\left(S, x, y\right) = \operatorname{hamiltonian}\left(S, \operatorname{val}\left(x\right), \operatorname{val}\left(y\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.restrictedHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(S) is the subtype of C(S) just described. Invariance of zero weight identifies this submatrix with the genuine restricted operator, including its action, inner product and eigenvectors.

**Definition 1.12 (The weight operator at a site).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{z}\left(S, i\right) = \operatorname{site}\left(S, i, \operatorname{Jz}\left(2 \cdot S\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At configuration x the diagonal entry is S−xᵢ.

**Definition 1.13 (The transverse pair operator).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\operatorname{xy}\left(S, i, j\right) = \operatorname{raising}\left(S, i\right) \cdot \operatorname{lowering}\left(S, j\right) + \operatorname{lowering}\left(S, i\right) \cdot \operatorname{raising}\left(S, j\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.xy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both ladder products act on the complete four-factor carrier.

**Definition 1.14 (The vertical pair operator).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\operatorname{zz}\left(S, i, j\right) = \operatorname{z}\left(S, i\right) \cdot \operatorname{z}\left(S, j\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.zz` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For distinct sites this is their commuting weight product.

**Definition 1.15 (The isotropic pair operator).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\operatorname{dot}\left(S, i, j\right) = \frac{1}{2} \cdot \operatorname{xy}\left(S, i, j\right) + \operatorname{zz}\left(S, i, j\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.dot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is XᵢXⱼ+YᵢYⱼ+ZᵢZⱼ. The native pair bound holds for every distinct pair.

**Definition 1.16 (The isotropic diamond sum).**

$$\forall (S: \mathbb{N}), (\operatorname{isotropic}\left(S\right) = \sum_{(i,j)\in\operatorname{edges}} \operatorname{dot}\left(S, i, j\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.isotropic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All five coefficient-one edges are present.

**Definition 1.17 (The vertical diamond sum).**

$$\forall (S: \mathbb{N}), (\operatorname{vertical}\left(S\right) = \sum_{(i,j)\in\operatorname{edges}} \operatorname{zz}\left(S, i, j\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.vertical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the diagonal sum over exactly the same five edges.

**Definition 1.18 (The homogeneous complex quadratic form).**

$$\forall (S: \mathbb{N}), (\forall (v: \operatorname{V}\left(S\right)), (\forall (A: \operatorname{O}\left(S\right)), (\operatorname{expect}\left(v, A\right) = \operatorname{inner}\left(v, A \cdot v\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.expect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner product conjugates v in its first argument. No normalization is assumed.

**Definition 1.19 (The middle configuration).**

$$\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{middleConfiguration}\left(S, i\right) = S))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.middleConfiguration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coordinate is the basis index S, of local weight zero.

**Definition 1.20 (The positive binomial product).**

$$\forall (S: \mathbb{N}), (\forall (x: \operatorname{C}\left(S\right)), (\operatorname{binomialProduct}\left(S, x\right) = \operatorname{ofReal}\left(\operatorname{binomialProductReal}\left(S, x\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.binomialProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It is the tensor product of the native binomial vectors at real parameter one.

**Definition 1.21 (Its real coefficients).**

$$\forall (S: \mathbb{N}), (\forall (x: \operatorname{C}\left(S\right)), (\operatorname{binomialProductReal}\left(S, x\right) = \prod_{i\in\operatorname{Fin}\left(4\right)} \operatorname{sqrt}\left(\operatorname{choose}\left(2 \cdot S, \operatorname{val}\left(x\left(i\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DiamondSpinBounds.binomialProductReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every coefficient is strictly positive, including at both endpoints.

**Theorem 1.22 (Native spin relations and the whole-carrier pair bound).**

$$\begin{aligned}\forall (S: \mathbb{N}), ((1 \le S) \Rightarrow (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), ((i \ne j) \Rightarrow (\operatorname{PosSemidef}\left(\operatorname{ofNat}\left(S\right)^{2} \cdot 1 - \operatorname{dot}\left(S, i, j\right)\right))))))\\\forall (S: \mathbb{N}), (\forall (x: \operatorname{C}\left(S\right)), (0 < \operatorname{binomialProductReal}\left(S, x\right)))\\\forall (S: \mathbb{N}), (\forall (x: \operatorname{C}\left(S\right)), (\operatorname{binomialProduct}\left(S, x\right) = \operatorname{ofReal}\left(\operatorname{binomialProductReal}\left(S, x\right)\right)))\\\forall (S: \mathbb{N}), (\forall (Q: \operatorname{O}\left(S\right)), (\forall (A: \operatorname{O}\left(S\right)), (\forall (B: \operatorname{O}\left(S\right)), (\operatorname{comm}\left(Q, A \cdot B\right) = \operatorname{comm}\left(Q, A\right) \cdot B + A \cdot \operatorname{comm}\left(Q, B\right)))))\\\forall (S: \mathbb{N}), (\operatorname{hamiltonian}\left(S\right) = \sum_{(i,j)\in\operatorname{edges}} (\operatorname{raising}\left(S, i\right) \cdot \operatorname{lowering}\left(S, j\right) + \operatorname{lowering}\left(S, i\right) \cdot \operatorname{raising}\left(S, j\right)))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (x: \operatorname{C}\left(S\right)), (\left(\operatorname{lowering}\left(S, i\right) \cdot \operatorname{binomialProduct}\left(S\right)\right)\left(x\right) = \operatorname{ofNat}\left(\operatorname{val}\left(x\left(i\right)\right)\right) \cdot \operatorname{binomialProduct}\left(S, x\right))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{comm}\left(\operatorname{totalLowering}\left(S\right), \operatorname{raising}\left(S, i\right)\right) = -2 \cdot \operatorname{z}\left(S, i\right)))\\\forall (n: \mathbb{N}), ((\operatorname{Jplus}\left(n\right))^{*} \cdot \operatorname{Jplus}\left(n\right) = \operatorname{diag}\left(r\mapsto\operatorname{ofNat}\left(\operatorname{val}\left(r\right)\right) \cdot \left(\operatorname{ofNat}\left(n\right) + 1 - \operatorname{ofNat}\left(\operatorname{val}\left(r\right)\right)\right)\right))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{comm}\left(\operatorname{totalLowering}\left(S\right), \operatorname{z}\left(S, i\right)\right) = \operatorname{lowering}\left(S, i\right)))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (x: \operatorname{C}\left(S\right)), (\left(\operatorname{raising}\left(S, i\right) \cdot \operatorname{binomialProduct}\left(S\right)\right)\left(x\right) = \left(2 \cdot \operatorname{ofNat}\left(S\right) - \operatorname{ofNat}\left(\operatorname{val}\left(x\left(i\right)\right)\right)\right) \cdot \operatorname{binomialProduct}\left(S, x\right))))\\\forall (n: \mathbb{N}), (\operatorname{Jplus}\left(n\right) \cdot (\operatorname{Jplus}\left(n\right))^{*} = \operatorname{diag}\left(r\mapsto\left(\operatorname{ofNat}\left(\operatorname{val}\left(r\right)\right) + 1\right) \cdot \left(\operatorname{ofNat}\left(n\right) - \operatorname{ofNat}\left(\operatorname{val}\left(r\right)\right)\right)\right))\\\forall (S: \mathbb{N}), (\operatorname{Hermitian}\left(\operatorname{restrictedHamiltonian}\left(S\right)\right))\\\forall (S: \mathbb{N}), (\operatorname{singletSpace}\left(S\right) \subseteq \operatorname{zeroWeightSpace}\left(S\right))\\\forall (S: \mathbb{N}), (\forall (v: \operatorname{V}\left(S\right)), ((v \in \operatorname{singletSpace}\left(S\right)) \Rightarrow (\operatorname{expect}\left(v, \operatorname{hamiltonian}\left(S\right)\right) = \frac{4}{3} \cdot \operatorname{expect}\left(v, \operatorname{isotropic}\left(S\right)\right))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (v: \operatorname{V}\left(S\right)), (\forall (x: \operatorname{C}\left(S\right)), (\left(\operatorname{site}\left(S, i, A\right) \cdot v\right)\left(x\right) = \sum_{r\in\operatorname{W}\left(S\right)} \operatorname{A}\left(x\left(i\right), r\right) \cdot v\left(\operatorname{update}\left(x, i, r\right)\right))))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (B: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\operatorname{site}\left(S, i, A + B\right) = \operatorname{site}\left(S, i, A\right) + \operatorname{site}\left(S, i, B\right)))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), ((\operatorname{site}\left(S, i, A\right))^{*} = \operatorname{site}\left(S, i, (A)^{*}\right))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), ((i \ne j) \Rightarrow (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (B: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\operatorname{site}\left(S, i, A\right) \cdot \operatorname{site}\left(S, j, B\right) = \operatorname{site}\left(S, j, B\right) \cdot \operatorname{site}\left(S, i, A\right)))))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\forall (B: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\operatorname{site}\left(S, i, A \cdot B\right) = \operatorname{site}\left(S, i, A\right) \cdot \operatorname{site}\left(S, i, B\right)))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (c: \mathbb{C}), (\forall (A: \operatorname{Matrix}\left(\operatorname{W}\left(S\right), \operatorname{W}\left(S\right), \mathbb{C}\right)), (\operatorname{site}\left(S, i, c \cdot A\right) = c \cdot \operatorname{site}\left(S, i, A\right)))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (v: \operatorname{V}\left(S\right)), (\forall (x: \operatorname{C}\left(S\right)), (\left(\operatorname{z}\left(S, i\right) \cdot v\right)\left(x\right) = \left(\operatorname{ofNat}\left(S\right) - \operatorname{ofNat}\left(\operatorname{val}\left(x\left(i\right)\right)\right)\right) \cdot v\left(x\right)))))\\\forall (S: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(4\right)), (\operatorname{z}\left(S, i\right) = \operatorname{diag}\left(x\mapsto\operatorname{ofNat}\left(S\right) - \operatorname{ofNat}\left(\operatorname{val}\left(x\left(i\right)\right)\right)\right)))\\\forall (S: \mathbb{N}), (\forall (v: \operatorname{V}\left(S\right)), ((v \in \operatorname{zeroWeightSpace}\left(S\right)) \Leftrightarrow (\forall (x: \operatorname{C}\left(S\right)), ((\sum_{i\in\operatorname{Fin}\left(4\right)} \operatorname{val}\left(x\left(i\right)\right) \ne 4 \cdot S) \Rightarrow (v\left(x\right) = 0)))))\\\forall (S: \mathbb{N}), (\forall (v: \operatorname{V}\left(S\right)), ((v \in \operatorname{zeroWeightSpace}\left(S\right)) \Rightarrow (\operatorname{hamiltonian}\left(S\right) \cdot v \in \operatorname{zeroWeightSpace}\left(S\right))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/DiamondSpinBounds.native_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed rows form one conjunction. In the two local ladder products diag maps r in Fin(n+1) to its displayed entry; in the site weight identity it maps x in C(S). The maps ofNat and ofReal embed scalars in the complex numbers. Write comm(A,B)=AB−BA and update(x,i,r) for replacement at site i. The conjunction records the exact site action, linearity, adjoints and commutation, the normalized ladder products, weight support and invariance, Hermiticity of the restriction, singlet expectation isotropy, and the pair order bound. Every spin, site, matrix and vector variable retains its full stated range.

A strictly positive product of binomial vectors is a Dᵢⱼ eigenvector of eigenvalue S². Adding S² times the identity to Dᵢⱼ gives an entrywise nonnegative matrix. The Perron comparison bound and the Hermitian spectral theorem yield Dᵢⱼ≤S²I for S≥1 on the whole complex carrier, with every coupling sector and multiplicity included.

Total-ladder commutators give ⟨v,Kv⟩=(4/3)⟨v,Iv⟩ for every singlet. This is an expectation identity; no vector equation Kv=(4/3)Iv is asserted. Both total ladders imply zero total weight, and weight invariance identifies the displayed submatrix with the complete Hermitian restriction.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.binomialProduct`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.binomialProductReal`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.dot`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.edges`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.expect`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.hamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.isotropic`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.lowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.middleConfiguration`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.native_relations`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.raising`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.restrictedHamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.singletSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.site`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalLowering`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalRaising`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.totalWeight`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.vertical`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.xy`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.z`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.zeroWeightSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/DiamondSpinBounds.zz`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance](../../Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance.md)
- Dependency: [D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment](../Contextuality/TemporalHardySpinAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionUniversalThresholdRefutation](../Entanglement/PrecessionUniversalThresholdRefutation.md)
