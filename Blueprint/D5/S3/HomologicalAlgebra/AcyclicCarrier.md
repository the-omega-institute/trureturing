# The augmented acyclic carrier theorem

## Abstract

Homotopies carried by basis-indexed acyclic subcomplexes.

In every formula, C(n) and D(n) denote the objects of the given nonnegative chain complexes, dC(n):C(n+1) to C(n) and dD(n):D(n+1) to D(n) are their differentials, and B(n,b) denotes the source basis vector. The coefficient coeff(n,b,c) is B(n).repr(dC(n)(B(n+1,b)))(c). Hom and Lin denote R-linear maps, ChainMap denotes native complex morphisms, and composition is written in the usual function order. Universe parameters u, v, w and x are independent; ModuleCat(R,v) denotes the object universe v. Submodule membership and inclusion are over R. K(n,b,m) denotes the submodule field of CarrierData; Carried(K,n,m,g) means that every g(B(n,b)) lies in K(n,b,m).

**Definition 1.1 (Basis-indexed carriers).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\operatorname{CarrierData}\left(B\right):=\{(K:\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N}), \operatorname{Submodule}\left(R, \operatorname{D}\left(m\right)\right))|(\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N})(z:\operatorname{D}\left(m+1\right)), (z\in \operatorname{K}\left(n, b, m+1\right)) \implies (\operatorname{dD}\left(m\right)(z)\in \operatorname{K}\left(n, b, m\right))) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n+1\right))(c:\operatorname{I}\left(n\right)), (\operatorname{coeff}\left(n, b, c\right)\neq0) \implies (\forall (m:\mathbb{N}), \operatorname{K}\left(n, c, m\right)\subseteq \operatorname{K}\left(n+1, b, m\right)))\}\end{gathered}$$

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.CarrierData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For an arbitrary commutative ring R, nonnegative ModuleCat chain complexes C and D, an arbitrary family of index types I(n), and bases B(n) of C(n), a carrier assigns submodules A(n,b)(m) of D(m). The target differential preserves each carrier. If c has nonzero coefficient in the basis expansion of the boundary of b, every degree of the carrier of c lies in the corresponding degree of the carrier of b.

**Definition 1.2 (Carried linear maps).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right))(n:\mathbb{N})(m:\mathbb{N})(g:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right)), \operatorname{Carried}\left(K, n, m, g\right) \iff \forall (b:\operatorname{I}\left(n\right)), g(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, m\right)\end{gathered}$$

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.Carried` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A map from C(n) to D(m) is carried when the image of every basis vector b belongs to A(n,b)(m).

**Definition 1.3 (Augmented carrier acyclicity).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right)), \forall (x:Universe)(T:\operatorname{Type}\left(x\right)), [\operatorname{AddCommGroup}\left(T\right)][\operatorname{Module}\left(R, T\right)] \forall (aug:\operatorname{Lin}\left(R, \operatorname{D}\left(0\right), T\right)), \operatorname{Acyclic}\left(K, aug\right) \iff (aug\circ \operatorname{dD}\left(0\right)=0) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(z:\operatorname{D}\left(0\right)), ((z\in \operatorname{K}\left(n, b, 0\right)) \land (\operatorname{aug}\left(z\right)=0)) \implies (\exists (y:\operatorname{D}\left(1\right)), (y\in \operatorname{K}\left(n, b, 1\right)) \land (\operatorname{dD}\left(0\right)(y)=z))) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N})(z:\operatorname{D}\left(m+1\right)), ((z\in \operatorname{K}\left(n, b, m+1\right)) \land (\operatorname{dD}\left(m\right)(z)=0)) \implies (\exists (y:\operatorname{D}\left(m+2\right)), (y\in \operatorname{K}\left(n, b, m+2\right)) \land (\operatorname{dD}\left(m+1\right)(y)=z)))\end{gathered}$$

*Formalization.* `D5/S3/HomologicalAlgebra/AcyclicCarrier.Acyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

The augmentation may take values in an arbitrary R-module. It vanishes on boundaries. In each individual carrier, augmentation-zero elements in degree zero lift to degree one, and cycles in every positive degree lift to the next degree. No contraction or chosen lift is assumed.

**Theorem 1.4 (Finite-support boundary extension).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right))(n:\mathbb{N})(m:\mathbb{N})(g:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right)), (\operatorname{Carried}\left(K, n, m, g\right)) \implies (\forall (b:\operatorname{I}\left(n+1\right)), g(\operatorname{dC}\left(n\right)(\operatorname{B}\left(n+1, b\right)))\in \operatorname{K}\left(n+1, b, m\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.face` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried linear map sends the boundary of each source basis vector into the carrier of that vector. Expand the boundary using Basis.repr, sum only over its finite support, apply coefficient-support nesting to each term, and use closure of the target submodule under scalar multiplication and finite sums.

**Theorem 1.5 (Subtraction preserves bounds).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right))(n:\mathbb{N})(m:\mathbb{N})(f:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right))(g:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right)), ((\operatorname{Carried}\left(K, n, m, f\right)) \land (\operatorname{Carried}\left(K, n, m, g\right))) \implies (\operatorname{Carried}\left(K, n, m, f-g\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

The difference of two maps carried in the same degrees remains carried.

**Theorem 1.6 (Support-preserving basis lift).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (n:\mathbb{N})(Y:\operatorname{ModuleCat}\left(R, v\right))(Z:\operatorname{ModuleCat}\left(R, v\right))(KY:\operatorname{I}\left(n\right)\to \operatorname{Submodule}\left(R, Y\right))(phi:\operatorname{Lin}\left(R, Y, Z\right))(Phi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), Z\right)), (\forall (b:\operatorname{I}\left(n\right)), Phi(\operatorname{B}\left(n, b\right))\in \operatorname{map}\left(\operatorname{KY}\left(b\right), phi\right)) \implies (\exists (Psi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), Y\right)), (\forall (b:\operatorname{I}\left(n\right)), Psi(\operatorname{B}\left(n, b\right))\in \operatorname{KY}\left(b\right)) \land (phi\circ Psi=Phi))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.basis_exists_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For any target linear map phi and basis-indexed source map Phi, if every Phi(B(b)) has a preimage in its specified submodule, choose those preimages and extend along the source basis. The extension is carried and its composite with phi equals Phi by basis extensionality. The basis can be empty or infinite, and neither target has a basis requirement.

**Theorem 1.7 (Positive-degree primitive).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right)), \forall (x:Universe)(T:\operatorname{Type}\left(x\right)), [\operatorname{AddCommGroup}\left(T\right)][\operatorname{Module}\left(R, T\right)] \forall (aug:\operatorname{Lin}\left(R, \operatorname{D}\left(0\right), T\right)), \forall (n:\mathbb{N})(m:\mathbb{N})(Phi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m+1\right)\right)), ((\operatorname{Acyclic}\left(K, aug\right)) \land (\operatorname{Carried}\left(K, n, m+1, Phi\right)) \land (\operatorname{dD}\left(m\right)\circ Phi=0)) \implies (\exists (Psi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m+2\right)\right)), (\operatorname{Carried}\left(K, n, m+2, Psi\right)) \land (\operatorname{dD}\left(m+1\right)\circ Psi=Phi))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried map into positive-degree cycles lifts through the target differential with the same individual carrier bounds. Extend the carrier primitives along the source basis.

**Theorem 1.8 (Augmentation-zero primitive).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right)), \forall (x:Universe)(T:\operatorname{Type}\left(x\right)), [\operatorname{AddCommGroup}\left(T\right)][\operatorname{Module}\left(R, T\right)] \forall (aug:\operatorname{Lin}\left(R, \operatorname{D}\left(0\right), T\right)), \forall (n:\mathbb{N})(Phi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(0\right)\right)), ((\operatorname{Acyclic}\left(K, aug\right)) \land (\operatorname{Carried}\left(K, n, 0, Phi\right)) \land (aug\circ Phi=0)) \implies (\exists (Psi:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(1\right)\right)), (\operatorname{Carried}\left(K, n, 1, Psi\right)) \land (\operatorname{dD}\left(0\right)\circ Psi=Phi))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

A carried degree-zero map annihilated by the augmentation lifts to degree one with the same carrier bounds. Extend the degree-zero primitives along the source basis.

**Theorem 1.9 (Integer scaling preserves bounds).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right))(n:\mathbb{N})(m:\mathbb{N})(g:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right))(e:\mathbb{Z}), (\operatorname{Carried}\left(K, n, m, g\right)) \implies (\operatorname{Carried}\left(K, n, m, e\cdot g\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.comp_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Integer multiples of carried maps remain carried.

**Theorem 1.10 (Boundary precomposition).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right))(n:\mathbb{N})(m:\mathbb{N})(g:\operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(m\right)\right)), (\operatorname{Carried}\left(K, n, m, g\right)) \implies (\operatorname{Carried}\left(K, n+1, m, g\circ \operatorname{dC}\left(n\right)\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.d_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Precomposing a carried map with the source boundary preserves the shifted carrier bound. The finite-support boundary expansion gives the bound.

**Theorem 1.11 (Dependent sequence of primitive choices).**

$$\begin{gathered}\forall (s:Universe)(State:\mathbb{N}\to \operatorname{Type}\left(s\right))(initial:\operatorname{State}\left(0\right)\to Prop)(step:\forall (m:\mathbb{N}), \operatorname{State}\left(m\right)\to \operatorname{State}\left(m+1\right)\to Prop), ((\exists (q:\operatorname{State}\left(0\right)), \operatorname{initial}\left(q\right)) \land (\forall (m:\mathbb{N})(q:\operatorname{State}\left(m\right)), \exists (t:\operatorname{State}\left(m+1\right)), \operatorname{step}\left(m, q, t\right))) \implies (\exists (seq:\forall (m:\mathbb{N}), \operatorname{State}\left(m\right)), (\operatorname{initial}\left(\operatorname{seq}\left(0\right)\right)) \land (\forall (m:\mathbb{N}), \operatorname{step}\left(m, \operatorname{seq}\left(m\right), \operatorname{seq}\left(m+1\right)\right)))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_sequence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

Given an initial state and an allowed successor for every state in every degree, dependent recursion produces a sequence satisfying the initial and successor predicates.

**Theorem 1.12 (Carried component induction).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\operatorname{CarrierData}\left(B\right)), \forall (x:Universe)(T:\operatorname{Type}\left(x\right)), [\operatorname{AddCommGroup}\left(T\right)][\operatorname{Module}\left(R, T\right)] \forall (aug:\operatorname{Lin}\left(R, \operatorname{D}\left(0\right), T\right)), \forall (e:\mathbb{Z})(f:\forall (n:\mathbb{N}), \operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(n\right)\right))(g:\forall (n:\mathbb{N}), \operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(n\right)\right)), ((\operatorname{Acyclic}\left(K, aug\right)) \land (\forall (n:\mathbb{N}), \operatorname{dD}\left(n\right)\circ \operatorname{f}\left(n+1\right)=e\cdot {\operatorname{f}\left(n\right)\circ \operatorname{dC}\left(n\right)}) \land (\forall (n:\mathbb{N}), \operatorname{dD}\left(n\right)\circ \operatorname{g}\left(n+1\right)=e\cdot {\operatorname{g}\left(n\right)\circ \operatorname{dC}\left(n\right)}) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right)), \operatorname{f}\left(n\right)(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, n\right)) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right)), \operatorname{g}\left(n\right)(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, n\right)) \land (aug\circ \operatorname{f}\left(0\right)=aug\circ \operatorname{g}\left(0\right))) \implies (\exists (h:\forall (n:\mathbb{N}), \operatorname{Lin}\left(R, \operatorname{C}\left(n\right), \operatorname{D}\left(n+1\right)\right)), (\forall (n:\mathbb{N}), \operatorname{Carried}\left(K, n, n+1, \operatorname{h}\left(n\right)\right)) \land (\operatorname{f}\left(0\right)-\operatorname{g}\left(0\right)=\operatorname{dD}\left(0\right)\circ \operatorname{h}\left(0\right)) \land (\forall (n:\mathbb{N}), \operatorname{f}\left(n+1\right)-\operatorname{g}\left(n+1\right)=\operatorname{dD}\left(n+1\right)\circ \operatorname{h}\left(n+1\right)+e\cdot {\operatorname{h}\left(n\right)\circ \operatorname{dC}\left(n\right)}))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_homotopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For an arbitrary integer sign and two carried component families obeying the corresponding twisted chain equations and equal augmentation, degree induction constructs carried homotopy components. The state includes the residual cycle condition. Degree zero uses an augmentation-zero primitive; each successor subtracts the preceding homotopy on the source boundary, verifies that the residual is a cycle using the chain equations, and chooses a carrier primitive.

**Theorem 1.13 (Native carried chain homotopy).**

$$\begin{gathered}\forall u,v,w, (R:\operatorname{Type}\left(u\right)) [\operatorname{CommRing}\left(R\right)](C:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(D:\operatorname{ChainComplex}\left(\operatorname{ModuleCat}\left(R, v\right), \mathbb{N}\right))(I:\mathbb{N}\to \operatorname{Type}\left(w\right))(B:\forall (n:\mathbb{N}), \operatorname{Basis}\left(\operatorname{I}\left(n\right), R, \operatorname{C}\left(n\right)\right)),\\\forall (K:\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N}), \operatorname{Submodule}\left(R, \operatorname{D}\left(m\right)\right))(aug:\operatorname{Lin}\left(R, \operatorname{D}\left(0\right), R\right))(f:\operatorname{ChainMap}\left(C, D\right))(g:\operatorname{ChainMap}\left(C, D\right)), ((\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N})(z:\operatorname{D}\left(m+1\right)), (z\in \operatorname{K}\left(n, b, m+1\right)) \implies (\operatorname{dD}\left(m\right)(z)\in \operatorname{K}\left(n, b, m\right))) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n+1\right))(c:\operatorname{I}\left(n\right)), (\operatorname{coeff}\left(n, b, c\right)\neq0) \implies (\forall (m:\mathbb{N}), \operatorname{K}\left(n, c, m\right)\subseteq \operatorname{K}\left(n+1, b, m\right))) \land (aug\circ \operatorname{dD}\left(0\right)=0) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(z:\operatorname{D}\left(0\right)), ((z\in \operatorname{K}\left(n, b, 0\right)) \land (\operatorname{aug}\left(z\right)=0)) \implies (\exists (y:\operatorname{D}\left(1\right)), (y\in \operatorname{K}\left(n, b, 1\right)) \land (\operatorname{dD}\left(0\right)(y)=z))) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right))(m:\mathbb{N})(z:\operatorname{D}\left(m+1\right)), ((z\in \operatorname{K}\left(n, b, m+1\right)) \land (\operatorname{dD}\left(m\right)(z)=0)) \implies (\exists (y:\operatorname{D}\left(m+2\right)), (y\in \operatorname{K}\left(n, b, m+2\right)) \land (\operatorname{dD}\left(m+1\right)(y)=z))) \land (aug\circ \operatorname{f}\left(0\right)=aug\circ \operatorname{g}\left(0\right)) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right)), \operatorname{f}\left(n\right)(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, n\right)) \land (\forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right)), \operatorname{g}\left(n\right)(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, n\right))) \implies (\exists (H:\operatorname{Homotopy}\left(f, g\right)), \forall (n:\mathbb{N})(b:\operatorname{I}\left(n\right)), \operatorname{H}\left(n, n+1\right)(\operatorname{B}\left(n, b\right))\in \operatorname{K}\left(n, b, n+1\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_homotopy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lean FRO, LLC; AxiomMath contributors (2026). *Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem*. URL: <https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532>.

*Commentary.*

For every commutative ring R, arbitrary nonnegative ModuleCat chain complexes C and D, and arbitrary bases B(n) indexed by I(n), assume differential-closed basis-indexed carriers, nesting for every nonzero coefficient of each source basis boundary, and augmented acyclicity separately in every carrier. For every pair of chain maps f and g that agree after the augmentation D(0) to R and carry B(n)(b) into A(n,b)(n), there exists a native Homotopy f g whose component H.hom n (n+1) sends B(n)(b) into A(n,b)(n+1). The ring, module and index universes are arbitrary. The theorem permits zero rings, empty and infinite source bases, and non-surjective augmentations, and imposes no target basis, target projectivity, source acyclicity, global contractibility or homotopy-as-input hypothesis. The native Homotopy equations give f(0)-g(0)=dH(0), and f(n+1)-g(n+1)=dH(n+1)+H(n)d in positive degrees. The signed component construction with sign one gives the native Homotopy with exactly these carrier bounds.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Acyclic`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.Carried`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.CarrierData`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.basis_exists_lift`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.comp_left`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.d_comp`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_homotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_carried_primitive0`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_homotopy`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.exists_sequence`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.face`
- Truth anchor: `D5/S3/HomologicalAlgebra/AcyclicCarrier.sub`
