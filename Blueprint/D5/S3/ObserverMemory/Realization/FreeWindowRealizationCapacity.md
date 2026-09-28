# Free Window Realization Capacity

## Abstract

The realized finite words determine the exact total state capacity.

Let S be a finite set, A any output alphabet, D:S -> S a total update, q:S -> A a readout, and n a natural number. Define w_n(s)=(q(D^j(s))) for 0 <= j <= n, W_n=range(w_n), and I_n(s)=w_n(s), with codomain W_n. A word state w has readout g_n(w)=w(0). Empty S and n=0 are included.

For an arbitrary finite total carrier M, WindowCorrect(D,q,n,I,F,g) means g(F^j(I(s)))=q(D^j(s)) for every source s and 0 <= j <= n. The fixed update F and readout g act on all of M. The initial preparation I need not be surjective and need not commute with D and F; unused states count toward the capacity.

**Theorem 1.1 (Overlapping labels determine the output window).**

$$(\forall x, k<n, L\left(U\left(x\right), k\right)=L\left(x, k+1\right))\Rightarrow\forall x, j\leq n, L\left(\left(U^{j}\right)\left(x\right), 0\right)=L\left(x, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.overlap_output_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and A be arbitrary types, n a natural number, U:X -> X, and L:X -> (Fin(n+1) -> A). Assume L(U(x))(k)=L(x)(k+1) for every x and k<n. Then for every x and j<=n, the first letter after j updates is L(x)(j). No finiteness or nonempty overlap is required.

Induct on j in the stronger identity L(U^j(x))(k)=L(x)(k+j) for k+j<=n. One overlap step increases k, and the induction hypothesis handles the remaining updates. Taking k=0 gives the complete output window.

**Theorem 1.2 (Exact capacity with arbitrary representative successors).**

$$\begin{gathered}\forall S \text{finite}, A, D:S\to S, q:S\to A, n\in\mathbb{N}:\\(\forall M \text{finite}, I,F,g, WindowCorrect\left(D, q, n, I, F, g\right)\Rightarrow\lvert W_{n} \rvert\leq\lvert M \rvert)\land\\Finite\left(W_{n}\right)\land Surjective\left(I_{n}\right)\land(\exists r:W_{n}\to S, RightInverse\left(r, I_{n}\right))\land\\(\forall r:W_{n}\to S, RightInverse\left(r, I_{n}\right)\Rightarrow(WindowCorrect\left(D, q, n, I_{n}, U_{r}, g_{n}\right)\land\\\forall w\in W_{n}, t\in\mathbb{N}, futureReadoutWord\left(U_{r}, g_{n}, n, \left(\left(U_{r}\right)^{t}\right)\left(w\right)\right)=\left(\left(U_{r}\right)^{t}\right)\left(w\right)))\land\\(\exists D_{0}:B\to B, q_{0}:B\to Bool, r_{0}:WindowState\left(D_{0}, q_{0}, 0\right)\to B, RightInverse\left(r_{0}, I_{0}\right)\land I_{0}\circ D_{0}\neq U_{0}\circ I_{0})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.free_window_realization_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a representative map r:W_n -> S satisfying I_n(r(w))=w, define U_r(w)=I_n(D(r(w))). The theorem asserts the lower bound for every finite realization, finiteness of W_n, surjectivity of I_n, existence of a representative map, and correctness of U_r for every such choice. Its carrier is exactly W_n, so this realizes the minimum total number |W_n| of states.

More precisely, for every word state w and every natural time t, the length n+1 output word from U_r^t(w) equals the label U_r^t(w). Thus every later output window remains in W_n. This does not require it to match the later window of the source originally used to prepare w.

The final conjunct gives an explicit noncommuting example on B=Bool x Bool at horizon zero. Write I_0=prepare(D_0,q_0,0) and U_0=representativeUpdate(D_0,q_0,0,r_0). Take D_0(a,b)=(b,b), q_0(a,b)=a, and r_0(w)=(w(0),false). This is a right inverse of preparation, but I_0(D_0(false,true)) has letter true while U_0(I_0(false,true)) has letter false.

For the lower bound, choose one source for each realized word. Two equal prepared states would give equal outputs at every required time, hence the same word. The resulting injection from W_n into M gives |W_n| <= |M|.

For attainment, adjacent labels satisfy (U_r(w))(k)=w(k+1) whenever k<n. The overlap theorem identifies the output window with the word label. Applying it to every later state proves the assertion at all starting times.

## References

- Truth anchor: `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.free_window_realization_capacity`
- Truth anchor: `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.overlap_output_window`
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../Prediction/ConditionalEntropyStability.md)
