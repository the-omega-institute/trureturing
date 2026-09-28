# Free Window Realization Capacity

## Abstract

The realized finite words determine the exact total state capacity.

Let S be a finite set, A any output alphabet, D:S -> S a total update, q:S -> A a readout, and n a natural number. Define w_n(s)=(q(D^j(s))) for 0 <= j <= n, W_n=range(w_n), and I_n(s)=w_n(s), with codomain W_n. A word state w has readout g_n(w)=w(0). Empty S and n=0 are included.

For an arbitrary finite total carrier M, WindowCorrect(D,q,n,I,F,g) means g(F^j(I(s)))=q(D^j(s)) for every source s and 0 <= j <= n. The fixed update F and readout g act on all of M. The initial preparation I need not be surjective and need not commute with D and F; unused states count toward the capacity.

**Theorem 1.1 (Exact capacity with arbitrary representative successors).**

$$\begin{gathered}\forall S \text{finite}, A, D:S\to S, q:S\to A, n\in\mathbb{N}:\\(\forall M \text{finite}, I,F,g, WindowCorrect\left(D, q, n, I, F, g\right)\Rightarrow\lvert W_{n} \rvert\leq\lvert M \rvert)\land\\Finite\left(W_{n}\right)\land Surjective\left(I_{n}\right)\land(\exists r:W_{n}\to S, RightInverse\left(r, I_{n}\right))\land\\\forall r:W_{n}\to S, RightInverse\left(r, I_{n}\right)\Rightarrow(WindowCorrect\left(D, q, n, I_{n}, U_{r}, g_{n}\right)\land\\\forall w\in W_{n}, t\in\mathbb{N}, futureReadoutWord\left(U_{r}, g_{n}, n, \left(\left(U_{r}\right)^{t}\right)\left(w\right)\right)=\left(\left(U_{r}\right)^{t}\right)\left(w\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.free_window_realization_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a representative map r:W_n -> S satisfying I_n(r(w))=w, define U_r(w)=I_n(D(r(w))). The theorem asserts the lower bound for every finite realization, finiteness of W_n, surjectivity of I_n, existence of a representative map, and correctness of U_r for every such choice. Its carrier is exactly W_n, so this realizes the minimum total number |W_n| of states.

More precisely, for every word state w and every natural time t, the length n+1 output word from U_r^t(w) equals the label U_r^t(w). Thus every later output window remains in W_n. This does not require it to match the later window of the source originally used to prepare w.

For the lower bound, choose one source for each realized word. Two equal prepared states would give equal outputs at every required time, hence the same word. The resulting injection from W_n into M gives |W_n| <= |M|.

For attainment, adjacent labels satisfy (U_r(w))(k)=w(k+1) whenever k<n. Induction on j gives (U_r^j(w))(k)=w(k+j) whenever k+j<=n. Taking k=0 identifies the output window with the word label. Applying the same identity to every later state proves the assertion at all starting times.

## References

- Truth anchor: `D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity.free_window_realization_capacity`
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../Prediction/ConditionalEntropyStability.md)
