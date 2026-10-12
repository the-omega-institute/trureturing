# Affine modular behavior theorem 11.2

## Abstract

The exact congruence boundary of actual affine path and adaptive transcripts.

**Theorem 1.1 (All-path congruence and minimum realized boundary).**

$$\forall N \in \mathrm{Network},\; \forall v \in N.V,\; \left(0 < \operatorname{allPathModulus}\left(N, v\right) \land \operatorname{allPathModulus}\left(N, v\right) \mid N.m\right) \land \left(\left(\forall t \in \operatorname{ZMod}\left(N.m\right),\; \forall u \in \operatorname{ZMod}\left(N.m\right),\; \left(\forall w \in N.V,\; \forall p \in \operatorname{NPath}\left(N, v, w\right),\; \operatorname{pathTranscript}\left(p, t\right) = \operatorname{pathTranscript}\left(p, u\right)\right) \Leftrightarrow \operatorname{boundary}\left(N, v, t\right) = \operatorname{boundary}\left(N, v, u\right)\right) \land \left(\left(\forall t \in \operatorname{ZMod}\left(N.m\right),\; \forall u \in \operatorname{ZMod}\left(N.m\right),\; \left(\forall C \in \mathrm{Type},\; \forall s \in (w: N.V) \to \operatorname{List}\left(\operatorname{Event}\left(N\right)\right) \to C \to \operatorname{Option}\left(\{e: N.E|N.src\left(e\right)=w\} \times C\right),\; \forall c \in C,\; \forall n \in \mathbb{N},\; \operatorname{execute}\left(s, n, v, t, c\right).history = \operatorname{execute}\left(s, n, v, u, c\right).history\right) \Leftrightarrow \operatorname{boundary}\left(N, v, t\right) = \operatorname{boundary}\left(N, v, u\right)\right) \land \left(\operatorname{Surjective}\left(\operatorname{boundary}\left(N, v\right)\right) \land \left(\operatorname{Natcard}\left(\operatorname{range}\left(\operatorname{boundary}\left(N, v\right)\right)\right) = \operatorname{allPathModulus}\left(N, v\right) \land \left(\forall S \in \mathrm{Type},\; \forall r \in \operatorname{ZMod}\left(N.m\right) \to S,\; \left(\forall t \in \operatorname{ZMod}\left(N.m\right),\; \forall u \in \operatorname{ZMod}\left(N.m\right),\; r\left(t\right) = r\left(u\right) \Rightarrow \left(\forall w \in N.V,\; \forall p \in \operatorname{NPath}\left(N, v, w\right),\; \operatorname{pathTranscript}\left(p, t\right) = \operatorname{pathTranscript}\left(p, u\right)\right)\right) \Rightarrow \operatorname{allPathModulus}\left(N, v\right) \le \operatorname{Natcard}\left(\operatorname{range}\left(r\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AffineNetworks/AffineModularBehavior.theorem11_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All formulas quantify the original Network N. Its fields N.m, N.V, N.E, N.src, N.dst, N.d, N.a and N.c have their original meanings. Type denotes Lean's universe-zero Type; C and S denote the arbitrary Control and State types, s the legal selector, c the common initial control, r the readout, and u the second initial phase. Natcard, range and Surjective mean Nat.card, Set.range and Function.Surjective. Function arguments follow the Lean source; implicit network and endpoint arguments are inferred from the bound path.

Fix a positive modulus m, a nonempty finite directed multigraph with named edges, and positive port divisors d_v of m. At every vertex the actual source is all of ZMod m. Each edge e is legal at every source phase and transports that same phase by t ↦ a_e t+c_e modulo m. The natural multiplier may be zero. Loops, parallel edges, repeated edge occurrences and the empty path are retained.

For an actual path γ:v→w let A_γ be the product of its edge multipliers, with A_empty=1. Define D_v as the lcm of d_w/gcd(d_w,A_γ) over all such paths. This is the independent all-path divisor image, without a bound on path length. D_v is a positive divisor of m. The boundary map b_v is actual reduction from ZMod m to ZMod D_v; equality of its values is congruence modulo D_v.

A fixed-path transcript starts with the initial vertex and port answer. Each step appends the chosen named edge, the destination vertex and its actual port answer. For two initial phases, equality of every such finite transcript is equivalent to equality under b_v. No hidden phase is included in a public event.

An adaptive execution stores the physical phase separately from its public vertex, history, internal control and halt flag. The control type is arbitrary and need not be finite. Its deterministic selector uses only the vertex, full obtained history and internal control. It either halts or chooses an outgoing named edge and the next control state. The executor updates the phase by the original affine rule and appends the actual edge and port; a halt is absorbing. Every finite horizon, including horizon zero, is allowed.

For phases t,t′ at v, all adaptive histories agree for every selector, every common internal initial state and every finite horizon if and only if b_v(t)=b_v(t′). The universal quantifier is essential: a particular selector can halt immediately or choose an uninformative path.

Reduction b_v is surjective, so its realized image has exactly D_v states. For any deterministic readout r from the full source into any state type, if equal r-values imply agreement of every fixed-path transcript, then its realized image has at least D_v states. The count concerns attained values, not unused labels. This gives both attainment and the minimum.

Ordered-path induction proves T_γ(t′)−T_γ(t)=A_γ(t′−t). Reduction at w and gcd cancellation show that its terminal ports agree precisely when d_w/gcd(d_w,A_γ) divides t′−t. Taking the lcm gives the boundary kernel. Every intermediate observation is itself the endpoint of a prefix path.

$\forall N \in \mathrm{Network},\; \forall v \in N.V,\; \left(\forall w \in N.V,\; \forall p \in \operatorname{NPath}\left(N, v, w\right),\; \forall t \in \operatorname{ZMod}\left(N.m\right),\; \forall u \in \operatorname{ZMod}\left(N.m\right),\; \operatorname{portRead}\left(N, w, \operatorname{pathRun}\left(p, t\right)\right) = \operatorname{portRead}\left(N, w, \operatorname{pathRun}\left(p, u\right)\right) \Leftrightarrow \operatorname{pathQuotient}\left(p\right) \mid \operatorname{natAbs}\left((u.val: \mathbb{Z}) - (t.val: \mathbb{Z})\right)\right) \land \left(\forall t \in \operatorname{ZMod}\left(N.m\right),\; \forall u \in \operatorname{ZMod}\left(N.m\right),\; \left(\forall w \in N.V,\; \forall p \in \operatorname{NPath}\left(N, v, w\right),\; \operatorname{portRead}\left(N, w, \operatorname{pathRun}\left(p, t\right)\right) = \operatorname{portRead}\left(N, w, \operatorname{pathRun}\left(p, u\right)\right)\right) \Leftrightarrow \operatorname{boundary}\left(N, v, t\right) = \operatorname{boundary}\left(N, v, u\right)\right)$

For adaptive executions, a simultaneous induction maintains one actual named path and a shared public history and control state, while the two independently updated phases equal their respective actual runs along that path. Equal prefix ports force the same next selection. Conversely, a controller that replays the remaining named-edge list executes any fixed legal path. Finally, sufficient readouts factor onto the realized reduction image, whose surjectivity gives the cardinality bound.

The boundary describes the joint kernel of all possible path experiments. It does not assert that one physical run can acquire every boundary class. No phase-dependent guard, fee or extra reference is present. Randomized control, acquisition costs and recovery memory are outside this statement.

## References

- Truth anchor: `D5/S3/Arith/AffineNetworks/AffineModularBehavior.theorem11_2`
- Dependency: [D5/S3/Arith/AffineNetworks/AffineModularStopping](AffineModularStopping.md)
- Dependency: [D5/S3/ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization](../../ConceptDynamics/RefinementFactorization/RealizedImageKernelFactorization.md)
