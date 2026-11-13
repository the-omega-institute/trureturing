# Sequential spatial qutrit QRAM

## Abstract

Sequential address absorption and local qutrit transport implement clean classical-bit lookup at every natural depth, with exact complex linear action.

The model follows Hann, Lee, Girvin and Jiang, Section II.B and Figure 1(b), Appendix A and Figure 10, and Appendix B equation (B1). Qutrit has three basis labels: wait W, zero and one. encode maps either Boolean to its occupied label. W is router wait and spatial vacuum in this model. Address n is the existing recursive binary word: Unit at zero and Bool times Address n at a successor. bit reads its bits in head-first order.

**Definition 1.1 (Actual rails and routers).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.Interior`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.Interior` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

Tree n is Qutrit times Interior n: its first coordinate is the incident rail. Interior 0 is Unit, so depth zero has one spatial leaf and no router. Interior (n+1) contains one router and two Tree n children. Each child's incident rail is exactly its parent's corresponding output rail. State n contains n distinct qutrit address slots, one distinct external bus, and Tree n. vacuum initializes every router and mode to W. input replaces only the tree's incident coordinate.

**Definition 1.2 (Full SWAP and controlled full SWAP).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.route`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.route` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

absorb swaps incident and router labels on their full three-level spaces. leftGate swaps incident and the left output exactly when the router is zero; rightGate swaps incident and the right output exactly when it is one. route applies these two gates in that order. All other coordinates are preserved. These are literal permutations on arbitrary dirty basis states, constructed by the existing involution-to-permutation API. children applies specified operations in both subtrees, leaving the parent incident and router unchanged. No gate is selected by an externally supplied address value.

**Definition 1.3 (Sequential address absorption).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.load`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.load` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

descend n k routes through k existing router levels and performs absorption SWAPs at that depth; the same recursive schedule acts in both subtrees. At zero tree depth descend is inert. inject exchanges address slot k with the root incident rail and preserves every other slot and the bus. load n k is the composition of the first k injections, each followed by descend at the appropriate depth. Steps beyond n are inert. The circuit schedule depends on indices and depth, never on address data.

**Definition 1.4 (The dynamic prefix invariant).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.loading`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.loading` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

remaining n a k puts W in slots with index less than k and retains the encoded address bit in every other slot. programmed n a k puts the first k address bits in the routers on a's prefix path, with all other routers and every spatial mode W. loading combines remaining, an arbitrary unchanged external bus label, and programmed. The local induction shows that descend sends the next incident address bit into its waiting router, extends this prefix by one, and leaves the incident and output rails vacuum. The other subtree remains vacuum. Induction over injections proves the stated loading invariant for every k at most n.

**Definition 1.5 (One payload through adjacent modes).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.transport`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.transport` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

transport applies route at the root and recursively in both children. arrived n a p retains the fully programmed routers, puts p at spatial leaf a and W in every other mode. leaf observes an actual leaf rail. The operational induction transports an arbitrary incident label p through the programmed path into arrived. Its leaf equation makes the unique occupied payload explicit when p is zero or one; for p = W every spatial leaf is vacuum. All intermediate parent incident rails are cleared by their local exchange with the selected child.

**Definition 1.6 (Vacuum-preserving local readout).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.readLeaves`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.readLeaves` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

Fix classical memory D from Address n to Bool. dataGate is identity for false and swaps zero and one for true, fixing W in either case. This is precisely X-tilde from equation (B1). readLeaves applies the appropriate fixed dataGate at every spatial leaf, leaving internal router and incident coordinates unchanged. On arrived, every unoccupied leaf remains W and the unique payload becomes encode (b XOR D(a)). There is no address-selected memory operation.

**Definition 1.7 (Read and reverse the actual circuit).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.query`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.query` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

forward loads all n address signals, swaps the external bus with the root incident rail, and transports it to a spatial leaf. query applies forward, readLeaves on the spatial tree, and the exact inverse of forward. clean is loading with k = 0 and external bus encode b. The loading and transport inductions identify forward(clean) with all address slots W, the external bus W, and arrived. Local readout changes only the occupied payload. The inverse restores each address slot, the external bus position, every router to wait and every spatial rail to vacuum.

**Definition 1.8 (Complex linear action).**

Lean statement: `D5/S3/Quantum/Routing/HannSpatialQram.queryMatrix`

*Formalization.* `D5/S3/Quantum/Routing/HannSpatialQram.queryMatrix` (`✓ std3`).

*Citation.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

queryMatrix is Mathlib's Matrix.permMatrixHom applied directly to query. initialized psi is the finite sum over all addresses and encoded bus bits of psi(a,b) at clean n a b, and zero contributions elsewhere. The matrix is unitary. Its inverse-permutation pullback sends these amplitudes to psi(a,b XOR D(a)), for arbitrary complex psi. This uses the existing permutation-matrix identities and the clean circuit theorem directly.

**Theorem 1.9 (All-depth sequential spatial lookup).**

$$\begin{aligned}(\forall (n: \mathbb{N}), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (b: \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.Qutrit}\left(\right)), (\forall (k: \mathbb{N}), (k \le n \Rightarrow \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.load}\left(n, k\right)\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.loading}\left(n, a, b, 0\right)\right) = \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.loading}\left(n, a, b, k\right))))))\\\land (\forall (n: \mathbb{N}), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (p: \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.Qutrit}\left(\right)), (\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.transport}\left(n\right)\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.input}\left(n, \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.programmed}\left(n, a, n\right), p\right)\right) = \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.arrived}\left(n, a, p\right) \land \forall (i: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.leaf}\left(n, \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.transport}\left(n\right)\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.input}\left(n, \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.programmed}\left(n, a, n\right), p\right)\right), i\right) = \operatorname{ite}\left(i = a, p, \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.Qutrit.wait}\right))))))\\\land (\forall (n: \mathbb{N}), (\forall (D: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \to \operatorname{Bool}), (\forall (a: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right)), (\forall (b: \operatorname{Bool}), (\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.query}\left(n, D\right)\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.clean}\left(n, a, b\right)\right) = \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.clean}\left(n, a, \operatorname{Bool.xor}\left(b, D\left(a\right)\right)\right))))))\\\land (\forall (n: \mathbb{N}), (\forall (D: \operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \to \operatorname{Bool}), (\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.queryMatrix}\left(n, D\right)\right) \cdot \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.queryMatrix}\left(n, D\right) = 1 \land \left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.queryMatrix}\left(n, D\right) \cdot \operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.queryMatrix}\left(n, D\right)\right) = 1 \land \forall (psi: (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \times \operatorname{Bool}) \to \mathbb{C}), (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Routing.HannSpatialQram.queryMatrix}\left(n, D\right), \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.initialized}\left(n, psi\right)\right) = \operatorname{D5.S3.Quantum.Routing.HannSpatialQram.initialized}\left(n, \lambda (s: (\operatorname{D5.S3.Quantum.Routing.ReversibleQram.Address}\left(n\right) \times \operatorname{Bool})) \mapsto psi\left((\operatorname{Prod.fst}\left(s\right), \operatorname{Bool.xor}\left(\operatorname{Prod.snd}\left(s\right), D\left(\operatorname{Prod.fst}\left(s\right)\right)\right))\right)\right))\right))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannSpatialQram.correctness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Connor T. Hann; Gideon Lee; S. M. Girvin; Liang Jiang (2021). *Resilience of quantum random access memory to generic noise*. URL: <https://arxiv.org/pdf/2012.05340v2>.

*Commentary.*

The four clauses give prefix loading at every intermediate k, the exact transport state and its leaf observations, clean XOR lookup for both bus values, and both adjoint identities with the complex-amplitude action. All natural depths include zero: there are no address slots or routers there, but the external bus swaps into a unique spatial leaf, reads it and returns.

These statements formalize the published ideal three-level construction under the ordinary sequential address schedule. They do not identify its dirty-state permutation with the pipelined Figure 10 ordering. The original 0708.1879 fiducial qubit f is not identified with W. The existing Boolean ReversibleQram network supplies address types, not spatial dynamics. No depth, gate-count, noise, energy or global superposition activation bound, microscopic Hamiltonian or copying of unknown quantum data follows from these claims.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.Interior`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.correctness`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.load`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.loading`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.query`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.queryMatrix`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.readLeaves`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.route`
- Truth anchor: `D5/S3/Quantum/Routing/HannSpatialQram.transport`
- Dependency: [D5/S3/Quantum/Routing/ReversibleQram](ReversibleQram.md)
