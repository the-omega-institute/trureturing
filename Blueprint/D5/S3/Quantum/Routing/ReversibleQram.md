# Reversible QRAM routing and coherent readout

## Abstract

A reversible Boolean routing network selects one memory leaf, restores its workspace, and acts coherently on arbitrary complex amplitudes.

Addresses are binary words of any natural length n. Address 0 has one empty word; Address (n + 1) is Bool times Address n. Wires 0 is one Boolean wire, and Wires (n + 1) consists of two Wires n registers. The leftmost wire is the root input. The state clean n e puts e at that root and false at every scratch wire. The layout reuses each parent enable as its left output. Intermediate enables are therefore stored in place rather than retained in additional node registers.

**Definition 1.1 (One routing split).**

Lean statement: `D5/S3/Quantum/Routing/ReversibleQram.split`

*Formalization.* `D5/S3/Quantum/Routing/ReversibleQram.split` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

For address bit b, first XOR b AND the left root into the right root. Then XOR the resulting right root into the left root. These are the Toffoli and CNOT operations of Section IV. Starting with root values (e,false), their outputs are (e AND NOT b,e AND b). Other wires are untouched by this split. With e true at the first level, the Toffoli reduces to the address-copy CNOT described there. Both gates are permutations on arbitrary dirty wire configurations.

**Definition 1.2 (The recursive gate network).**

Lean statement: `D5/S3/Quantum/Routing/ReversibleQram.route`

*Formalization.* `D5/S3/Quantum/Routing/ReversibleQram.route` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

At depth zero route is the identity. At depth n + 1 it applies split with the first address bit, then routes both subregisters using the remaining address. Thus the network is defined by local gates; its definition does not use the one-hot specification. The separate function oneHot places e at the addressed leaf and false at every other leaf. The function leaf reads an individual leaf, with false and true leading bits selecting the left and right subregisters.

**Definition 1.3 (Leaf-controlled additions).**

Lean statement: `D5/S3/Quantum/Routing/ReversibleQram.readLeaves`

*Formalization.* `D5/S3/Quantum/Routing/ReversibleQram.readLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

Fix a classical memory D from Address n to an additive commutative group G. At each leaf, its Boolean wire controls addition of that leaf's datum to the bus. A fork first reads its left subtree and then its right subtree into the same bus. Product equivalences only rearrange the register coordinates around those additions. The resulting permutation preserves every routing wire. The recursively defined readAmount is the sum of the enabled data, and describes the effect of this sequence. The paper's Boolean readout is the special case of addition modulo two; arbitrary additive commutative data groups are the extension used here.

**Definition 1.4 (Compute, read, and uncompute).**

Lean statement: `D5/S3/Quantum/Routing/ReversibleQram.query`

*Formalization.* `D5/S3/Quantum/Routing/ReversibleQram.query` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

The address controls route, the leaf additions follow, and the inverse route is then applied. The inverse reverses the order of the local gates. This composition defines query on all basis configurations, without an initialization hypothesis. For dirty wires w, it preserves the address and w and adds readAmount n D (route n a w) to the bus. For clean n true, this amount is exactly D(a).

**Definition 1.5 (The complex query matrix).**

Lean statement: `D5/S3/Quantum/Routing/ReversibleQram.queryMatrix`

*Formalization.* `D5/S3/Quantum/Routing/ReversibleQram.queryMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

For finite G with decidable equality, queryMatrix is Mathlib's Matrix.permMatrixHom applied directly to query. Its rows and columns are indexed by Address n times (Wires n times G). The homomorphism uses the inverse permutation: forward movement of basis states therefore acts on amplitudes by pullback along the inverse. The function initialized embeds an arbitrary complex amplitude function on Address n times G into the full basis by making it zero whenever the routing workspace differs from clean n true.

**Theorem 1.6 (Correctness at every natural depth).**

$$\begin{aligned}\forall (n: \mathbb{N}), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (i: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (e: \operatorname{Bool}), (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.leaf}\left(n, \operatorname{D5.S3.Quantum.Routing.ReversibleQram.route}\left(n, a, \operatorname{D5.S3.Quantum.Routing.ReversibleQram.clean}\left(n, e\right)\right), i\right) = \operatorname{ite}\left(i = a, e, \operatorname{Bool.false}\right)))))\\\forall (n: \mathbb{N}), (\forall (G: \operatorname{Type}), (\forall (A: \operatorname{AddCommGroup}\left(G\right)), (\forall (D: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \to G), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (w: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Wires}\left(n\right)), (\forall (r: G), (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.query}\left(n, D, (a, (w, r))\right) = (a, (w, r + \operatorname{D5.S3.Quantum.Routing.ReversibleQram.readAmount}\left(n, D, \operatorname{D5.S3.Quantum.Routing.ReversibleQram.route}\left(n, a, w\right)\right))))))))))\\\forall (n: \mathbb{N}), (\forall (G: \operatorname{Type}), (\forall (A: \operatorname{AddCommGroup}\left(G\right)), (\forall (D: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \to G), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (r: G), (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.query}\left(n, D, (a, (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.clean}\left(n, \operatorname{Bool.true}\right), r))\right) = (a, (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.clean}\left(n, \operatorname{Bool.true}\right), r + D\left(a\right)))))))))\\\forall (n: \mathbb{N}), (\forall (G: \operatorname{Type}), (\forall (A: \operatorname{AddCommGroup}\left(G\right)), (\forall (F: \operatorname{Fintype}\left(G\right)), (\forall (E: \operatorname{DecidableEq}\left(G\right)), (\forall (D: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \to G), (\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Routing.ReversibleQram.queryMatrix}\left(n, D\right)\right) \cdot \operatorname{D5.S3.Quantum.Routing.ReversibleQram.queryMatrix}\left(n, D\right) = 1 \land \left(\operatorname{D5.S3.Quantum.Routing.ReversibleQram.queryMatrix}\left(n, D\right) \cdot \operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Routing.ReversibleQram.queryMatrix}\left(n, D\right)\right) = 1 \land \forall (psi: (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \times G) \to \mathbb{C}), (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Routing.ReversibleQram.queryMatrix}\left(n, D\right), \operatorname{D5.S3.Quantum.Routing.ReversibleQram.initialized}\left(n, psi\right)\right) = \operatorname{D5.S3.Quantum.Routing.ReversibleQram.initialized}\left(n, \lambda (s: (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \times G)) \mapsto psi\left((\operatorname{Prod.fst}\left(s\right), \operatorname{Prod.snd}\left(s\right) - D\left(\operatorname{Prod.fst}\left(s\right)\right))\right)\right))\right)))))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/ReversibleQram.correctness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan (2015). *On the robustness of bucket brigade quantum RAM*. DOI: [10.1088/1367-2630/17/12/123010](https://doi.org/10.1088/1367-2630/17/12/123010). URL: <https://arxiv.org/abs/1502.03450>.

*Commentary.*

For every natural n, every address a, every leaf i and either Boolean enable e, routing clean n e gives leaf value e when i = a and false otherwise. In particular an enabled root produces exactly one excited leaf, and a disabled root produces only zero leaves. The empty address at n = 0 is included. The proof inducts through the actual split and both recursive gate networks.

For every additive commutative G, memory D, address a, dirty workspace w and initial bus r, query preserves a and w and changes the bus to r + readAmount n D (route n a w). For w = clean n true it changes the bus to r + D(a), restoring every scratch wire and the root enable. The readout proof follows the successive additions; the routing induction supplies the addressed datum.

For every finite additive commutative G with decidable equality and every D, queryMatrix has both adjoint products equal to the identity. For every complex amplitude function psi on Address n times G, multiplying initialized psi by queryMatrix yields initialized of the function (a,r) mapped to psi(a,r - D(a)). This is the exact coherent action for arbitrary superpositions of addresses and bus values. It preserves support on the initialized routing workspace. Unitarity and the inverse-permutation action use the pinned permutation-matrix identities directly.

The memory D is fixed classical data. These statements concern an ideal reversible Boolean circuit and its complex linear action. They establish no physical locality of the bus, noise guarantee, primitive gate count or depth, three-state router implementation, or copying of unknown quantum memories. Section IV itself warns that its bus interacts with all memory bits. Page-Wootters claims and the original three-state bucket-brigade construction require separate arguments.

## References

- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.correctness`
- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.query`
- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.queryMatrix`
- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.readLeaves`
- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.route`
- Truth anchor: `D5/S3/Quantum/Routing/ReversibleQram.split`
