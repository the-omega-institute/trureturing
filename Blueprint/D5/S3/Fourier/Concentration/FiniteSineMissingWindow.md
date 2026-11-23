# Finite Sine-Score Missing Windows

## Abstract

One assignment of tail signs keeps a finite sine score below a strict bound throughout a closed interval.

**Definition 1.1 (Signed linear score).**

$$\operatorname{signedScore}\left(s, c, b\right) = \sum_{j \in s} \sigma\left(\operatorname{b}\left(j\right)\right) \cdot c_{j}$$

*Formalization.* `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.signedScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign σ is +1 for true and −1 for false. Only coordinates of the given finite set contribute. Coefficient families and scores are real-valued.

**Theorem 1.2 (One sign vector for all grid nodes).**

$$\begin{aligned}V=\sum_{j \in s} w_{j}^{2},\quad\delta>0,\quad(V=0 \lor \left|K\right| \cdot \operatorname{exp}\left(\frac{-\delta^{2}}{2 \cdot V}\right)<1),\\(\forall k \in K,j \in s, \left|c_{k,j}\right| \le w_{j})\\\longrightarrow \exists b: J \to \mathbb{B},\quad\forall k \in K,\quad\operatorname{signedScore}\left(s, c_{k}, b\right)<\delta\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_signs_on_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take finite types J and K, a subset s of J, nonnegative weights w, and real coefficients c indexed by K and J. The output b is Boolean valued. Sample independent fair signs, using the same sign space for every node. At a fixed node, each signed coefficient is centered and lies between minus its coordinate weight and that weight. The pinned Hoeffding inequality bounds the probability that the score reaches the positive threshold δ by exp(−δ²/(2V)), where V is the sum of the squared weights. Subadditivity over the nodes gives total bad probability at most the node count times this bound. A strict budget below one leaves a sign vector that works at every node.

When V vanishes, each selected coefficient is zero, so every sign vector works for a positive threshold. The argument also applies to a singleton tail.

The finite-family concentration argument is related to the Kahane–Salem–Zygmund estimate in Defant and Mastyło, Aspects of the Kahane–Salem–Zygmund inequalities in Banach spaces, Theorem 3.1 (DOI 10.1007/s13398-022-01369-4).

**Definition 1.3 (Weighted sine score with initial phases).**

$$\operatorname{sineScore}\left(f, \varphi, w, t\right) = \sum_{j \in J} w_{j} \cdot \operatorname{sin}\left(\varphi_{j} + f_{j} \cdot t\right)$$

*Formalization.* `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.sineScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Frequencies are angular rates. For ordinates γ and time scale r, use the rates γ/r.

**Theorem 1.4 (Prescribed head phases and a uniform tail bound).**

$$\begin{aligned}V = \sum_{j \in H^{c}} w_{j}^{2},\quad M = \sum_{j \in H} w_{j} + \delta + h \cdot \sum_{j \in H^{c}} w_{j} \cdot \left|f_{j}\right|,\\h>0,\quad \delta>0,\quad(V=0 \lor (\left\lfloor\frac{R}{h}\right\rfloor_{+} + 1) \cdot \operatorname{exp}\left(\frac{-\delta^{2}}{2 \cdot V}\right)<1)\\\longrightarrow \exists \varphi: J \to \mathbb{R},\\(\forall j \in H, \varphi_{j} = \theta_{j})\quad \land (\forall j \in H^{c}, \varphi_{j} \in \{0,\pi \})\\\land (\forall t \in [0,R], \operatorname{sineScore}\left(f, \varphi, w, t\right)<M)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_phases_on_closed_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be the head in the finite index type J, Hᶜ its complement, f and θ real-valued frequencies and head phases, and w nonnegative weights. For length R and positive mesh h, use the nodes kh from k = 0 through the natural floor of R/h. Each t in [0,R] is within h of its left node, including the right endpoint. Apply the grid theorem to the tail coefficients wⱼ sin(fⱼ kh), then lift the two signs to phases 0 and π.

The head contributes at most its weight, with its phases fixed at their prescribed values. The unit Lipschitz bound for sine extends the tail estimate between nodes at a cost no greater than h times the sum of wⱼ|fⱼ| over the tail. The bound is strict over the entire closed interval.

For nine frequencies j/9 with j from 1 through 9 and unit weights, take the first frequency as the head and prescribe phase π/2. On [0, 1/8], the mesh h = 1/8 has two nodes, and δ = 4 gives budget 2 exp(−1) < 1 with tail variance 8. The tail slope is at most 8, so the selected phases give a score strictly below 6 and a normalized deficit strictly above 1/3.

**Theorem 1.5 (Arbitrarily late windows in the original orbit).**

$$\begin{aligned}V = \sum_{j \in H^{c}} w_{j}^{2},\quad M = \sum_{j \in H} w_{j} + \delta + h \cdot \sum_{j \in H^{c}} w_{j} \cdot \left|f_{j}\right|,\\\operatorname{LinearIndependent}\left(\mathbb{Q}, f\right),\quad h>0,\quad \delta>0,\\(V=0 \lor (\left\lfloor\frac{R}{h}\right\rfloor_{+} + 1) \cdot \operatorname{exp}\left(\frac{-\delta^{2}}{2 \cdot V}\right)<1),\quad M<B\\\longrightarrow \forall A \in \mathbb{R},\quad \exists a>A,\\\forall u \in [a,a + R],\quad \operatorname{sineScore}\left(f, 0, w, u\right)<B\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rational linear independence rules out nonzero integer relations. `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit` then gives a time strictly above any start whose unit phases approximate the selected phase vector. Multiplication by the same unit phase during the window preserves each chord error. Taking imaginary parts and summing against the weights bounds the score error uniformly over the interval.

Let M denote head mass plus the grid threshold and slope allowance, and let W be the total weight. For any target B > M, the chord tolerance (B − M)/(W + 1) spends at most the available margin. For W > 0 and B = (1 − ε)W, the normalized sine deficit throughout the translated window is strictly greater than ε.

For a singleton frequency and weight both equal to one, take R = 1/16, h = 1/8, and δ = 1/4. The sole grid node gives budget exp(−1/32) < 1, and the upper bound 3/8 leaves a strict margin below B = 1/2. Thus sin(u) stays below 1/2 on intervals of length 1/16 beginning arbitrarily late.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_arbitrarily_late_missing_window`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_phases_on_closed_window`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.exists_signs_on_grid`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.signedScore`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteSineMissingWindow.sineScore`
- Truth anchor: `D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit`
- Dependency: [D5/S3/Fourier/WeightedPhaseRelationLattice](../WeightedPhaseRelationLattice.md)
