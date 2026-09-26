# Phase History Bound

## Abstract

Actual sequential source moments and a common-center phase-history operator bound.

The source has a two-dimensional complex memory and a fresh blank physical bit at each step. Every emitted bit and the final memory are retained. Bit is Bool, with false denoted 0 and true denoted 1; bit converts these labels to the real numbers 0 and 1. Throughout, p is real with 0<p<1, n and all time indices are natural numbers, and phi and delta are arbitrary real sequences. Space(A) is the complex Euclidean space on the finite type A, e is its coordinate basis, Unitary(A) is its linear isometry equivalence group, and indicator(P) is 1 or 0 according to P.

**Definition 1.1 (Memory amplitudes).**

$$memory\left(p, 0, 0\right) = sqrt\left(1 - p\right) \land \left(memory\left(p, 0, 1\right) = sqrt\left(p\right) \land \left(memory\left(p, 1, 0\right) = 1 \land memory\left(p, 1, 1\right) = 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.memory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows are indexed by the incoming memory and columns by the outgoing memory. The emitted physical bit copies the incoming memory. These amplitudes are nonnegative.

**Definition 1.2 (Squared memory amplitudes).**

$$transition\left(p, 0, 0\right) = 1 - p \land \left(transition\left(p, 0, 1\right) = p \land \left(transition\left(p, 1, 0\right) = 1 \land transition\left(p, 1, 1\right) = 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transition matrix is the entrywise square of memory, with rows (1-p,p) and (1,0). Each row sums to one. The probability law below is derived from the physical amplitudes.

**Definition 1.3 (The blank-input isometry).**

$$step\left(p, gamma, pair\left(j, k\right), i\right) = indicator\left(j = i\right) \cdot exp\left(imaginaryUnit \cdot gamma \cdot bit\left(i\right)\right) \cdot memory\left(p, i, k\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma is real and i,j,k range over Bit. step is a matrix from Bit to Bit x Bit. Its orthonormal columns specify the action of a two-bit unitary on the blank physical input.

**Definition 1.4 (A path retains its terminal memory).**

$$Path\left(0\right) = Bit \land Path\left(n + 1\right) = Prod\left(Bit, Path\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.Path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Path(n) represents (x(0),...,x(n)). Its first n entries are physical archive bits and x(n) is final memory. pathFintype recursively supplies the finite enumeration, and pathDecidableEq recursively decides equality; both use the Bool instances at length zero and product instances at successors.

**Definition 1.5 (The initial memory label).**

$$head\left(0, i\right) = i \land head\left(n + 1, pair\left(i, x\right)\right) = i$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.head` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

head(n,x) is x(0). At length zero the entire path is the memory label.

**Definition 1.6 (Real-valued occupation observations).**

$$observed\left(0, i, s\right) = bit\left(i\right) \land \left(observed\left(n + 1, pair\left(i, x\right), 0\right) = bit\left(i\right) \land observed\left(n + 1, pair\left(i, x\right), s + 1\right) = observed\left(n, x, s\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.observed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For 0<=s<=n, observed(n,x,s) is the occupation bit x(s). The definition saturates at final memory beyond n; the moment theorem uses only times through n. Write X(s) for the function x mapped to observed(n,x,s).

**Definition 1.7 (The source path mass).**

$$pathMass\left(p, 0, i\right) = 1 \land pathMass\left(p, n + 1, pair\left(i, x\right)\right) = transition\left(p, i, head\left(n, x\right)\right) \cdot pathMass\left(p, n, x\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.pathMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pathMass is the product of the n squared memory amplitudes. Fixing head(n,x)=i supplies the initial condition; there is no stationary initial distribution.

**Definition 1.8 (The physical amplitude along a path).**

$$pathAmplitude\left(p, phi, 0, t, i\right) = 1 \land pathAmplitude\left(p, phi, n + 1, t, pair\left(i, x\right)\right) = exp\left(imaginaryUnit \cdot phi\left(t\right) \cdot bit\left(i\right)\right) \cdot memory\left(p, i, head\left(n, x\right)\right) \cdot pathAmplitude\left(p, phi, n, t + 1, x\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.pathAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start time t shifts the phase history. Each factor is the local phase on incoming memory times its transition amplitude.

**Definition 1.9 (The full archive-and-memory source matrix).**

$$source\left(p, phi, n, t, x, i\right) = indicator\left(head\left(n, x\right) = i\right) \cdot pathAmplitude\left(p, phi, n, t, x\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

source(p,phi,n,t) has rows Path(n) and columns Bit. It includes the final memory and preserves both input columns. At n=0 it is exactly the identity matrix on Bit, independently of p, phi and t.

**Definition 1.10 (The path and physical register have the same coordinates).**

$$register\left(n, x\right) = pair\left(archive\left(n, x\right), terminal\left(n, x\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.register` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

register(n) is an equivalence from Path(n) to ((Fin(n) to Bit) x Bit): archive lists x(0) through x(n-1), and terminal is x(n). It recursively uses SequentialRegisterCircuit.headRest, with the unique empty archive at zero.

**Definition 1.11 (Expectation in a fixed input column).**

$$expectation\left(p, n, i, f\right) = \sum_{x:Path\left(n\right)}{indicator\left(head\left(n, x\right) = i\right) \cdot pathMass\left(p, n, x\right) \cdot f\left(x\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.expectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

f is any real function on Path(n). Write E(n,i,f) for this expectation with p understood. Its weights are the Born probabilities of the actual circuit, and their normalization is a conclusion below.

**Definition 1.12 (The nonstationary occupation mean).**

$$mean\left(p, i, s\right) = \frac{p}{1 + p} + \left(bit\left(i\right) - \frac{p}{1 + p}\right) \cdot \left(-p\right)^{s}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q=p/(1+p) is the equilibrium occupation. The transient (bit(i)-q)(-p)^s retains the deterministic initial bit. Write m(i,s)=mean(p,i,s).

**Theorem 1.13 (One actual unitary sequence realizes the path law at every length).**

$$\forall p \in \mathbb{R},\; \left(0 < p \land p < 1\right) \Rightarrow \left(\forall phi \in Function\left(\mathbb{N}, \mathbb{R}\right),\; \exists U \in Function\left(\mathbb{N}, Unitary\left(Prod\left(Bit, Bit\right)\right)\right),\; \left(\forall t \in \mathbb{N},\; \forall i \in Bit,\; \forall j \in Bit,\; \forall k \in Bit,\; U\left(t, e\left(pair\left(0, i\right)\right), pair\left(j, k\right)\right) = step\left(p, phi\left(t\right), pair\left(j, k\right), i\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall i \in Bit,\; \forall x \in Path\left(n\right),\; circuit\left(U, n, t, blankState\left(0, n, i\right), register\left(n, x\right)\right) = source\left(p, phi, n, t, x, i\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall i \in Bit,\; \forall x \in Path\left(n\right),\; norm\left(source\left(p, phi, n, t, x, i\right)\right)^{2} = indicator\left(head\left(n, x\right) = i\right) \cdot pathMass\left(p, n, x\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall i \in Bit,\; E\left(n, i, constant\left(1\right)\right) = 1\right) \land \left(\left(\forall n \in \mathbb{N},\; \forall i \in Bit,\; \forall s \in \mathbb{N},\; s \le n \Rightarrow E\left(n, i, X\left(s\right)\right) = mean\left(p, i, s\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall i \in Bit,\; \forall s \in \mathbb{N},\; \forall t \in \mathbb{N},\; \left(s \le t \land t \le n\right) \Rightarrow E\left(n, i, product\left(X\left(s\right), X\left(t\right)\right)\right) - mean\left(p, i, s\right) \cdot mean\left(p, i, t\right) = \left(-p\right)^{t - s} \cdot mean\left(p, i, s\right) \cdot \left(1 - mean\left(p, i, s\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PhaseHistoryBound.actual_source_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same U is chosen before n and t, so it realizes every length and every start time. circuit, blankState, and the unitary Hilbert spaces are those of SequentialRegisterCircuit. The first equation specifies U on its blank-input subspace; the second identifies its actual composed coefficients with source. The remaining equations give squared amplitudes, normalization, mean, and the exact two-time covariance. product denotes pointwise multiplication of real functions. The proof first extends each local isometry to a unitary, then identifies the recursive circuit coefficients and derives the moments by conditioning on the first transition. In particular, at p=1/2, n=2, i=0, s=1, t=2, the covariance is -1/8.

Linearity extends the coefficient identity to every complex memory vector v: the actual initialized circuit coefficient at register(n,x) is the sum over i of v(i)source(p,phi,n,t,x,i). Thus these are coherent source maps, including superpositions of the two memory inputs. An arbitrary finite reference is retained in the operator inequality below.

**Definition 1.14 (The uniform history constant).**

$$historyConstant\left(p\right) = \frac{\frac{1 + p}{1 - p} + \frac{1}{1 - p^{2}}}{4}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.historyConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both denominators are positive for 0<p<1. The first term bounds correlated fluctuations; the second controls the transient displacement from a center shared by the two initial conditions.

**Definition 1.15 (The accumulated discrepancy).**

$$phaseSum\left(delta, n, t, x\right) = \sum_{s:Fin\left(n\right)}{delta\left(t + val\left(s\right)\right) \cdot observed\left(n, x, val\left(s\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.phaseSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This sum includes the n emitted occupations, with start time t. The final memory is retained in the path but adds no extra phase.

**Definition 1.16 (One scalar center for both input columns).**

$$center\left(p, delta, n\right) = \frac{p}{1 + p} \cdot \sum_{s:Fin\left(n\right)}{delta\left(val\left(s\right)\right)} + \left(\frac{1}{2} - \frac{p}{1 + p}\right) \cdot \sum_{s:Fin\left(n\right)}{delta\left(val\left(s\right)\right) \cdot \left(-p\right)^{val\left(s\right)}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H is the sum of delta(s)(-p)^s for 0<=s<n. This center is the arithmetic midpoint of the two conditional means of phaseSum(delta,n,0). Their deviations from the center are (bit(i)-1/2)H. The scalar center is independent of the input vector and reference.

**Definition 1.17 (The coherently centered source difference).**

$$error\left(p, theta, phi, n, b\right) = source\left(p, constant\left(theta\right), n, 0\right) - exp\left(imaginaryUnit \cdot b\right) \cdot source\left(p, phi, n, 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhaseHistoryBound.error` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

theta is the real phase of the constant source and phi is the known virtual phase history. b is one real scalar, multiplying the entire second source matrix by the same complex phase. Write D=error(p,theta,phi,n,center(p,delta,n)).

**Theorem 1.18 (Uniform operator and finite-reference bounds).**

$$\forall p \in \mathbb{R},\; \left(0 < p \land p < 1\right) \Rightarrow \left(\forall n \in \mathbb{N},\; \forall theta \in \mathbb{R},\; \forall phi \in Function\left(\mathbb{N}, \mathbb{R}\right),\; \forall delta \in Function\left(\mathbb{N}, \mathbb{R}\right),\; \left(\forall t \in \mathbb{N},\; t < n \Rightarrow \left(\exists k \in \mathbb{Z},\; theta - phi\left(t\right) = delta\left(t\right) + k \cdot 2 \cdot \pi\right)\right) \Rightarrow \left(PSD\left(historyConstant\left(p\right) \cdot \sum_{s:Fin\left(n\right)}{delta\left(val\left(s\right)\right)^{2}} \cdot identity\left(Bit\right) - adjoint\left(D\right) \cdot D\right) \land \left(\forall J \in Type,\; \left(Fintype\left(J\right) \land DecidableEq\left(J\right)\right) \Rightarrow PSD\left(historyConstant\left(p\right) \cdot \sum_{s:Fin\left(n\right)}{delta\left(val\left(s\right)\right)^{2}} \cdot identity\left(Prod\left(J, Bit\right)\right) - adjoint\left(tensor\left(identity\left(J\right), D\right)\right) \cdot tensor\left(identity\left(J\right), D\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PhaseHistoryBound.phase_history_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bound is historyConstant(p) times the sum of delta(s)^2 for 0<=s<n. identity(J) is the identity matrix, adjoint is conjugate transpose, and tensor is the matrix Kronecker product; TensorError=identity(J) tensor D. PSD means positive semidefinite. J may be any finite type in any universe, including the empty type. Equivalently, every vector v on Bit and every vector w on J x Bit satisfy squared output norm at most Bound times their squared input norm. This includes arbitrary coherent and reference-entangled inputs without a normalization premise. The congruence condition allows any real representatives delta, without a minimal-distance restriction or a finite upper cutoff on n. For n=0 both sources are the identity, the center and error are zero, and the bound is zero.

For the bound, the exact covariance gives absolute covariance at most p raised to the time separation, divided by 4. Its geometric row sum is bounded by (1+p)/(1-p), controlling the variance of the weighted phase sum. Cauchy-Schwarz bounds H squared by the phase energy divided by (1-p^2). Adding the squared common-center bias H squared/4 gives exactly historyConstant(p). The inequality between a phase chord and its real lift then bounds each column's squared error. The two columns have disjoint head support, so the error Gram matrix is diagonal. This yields the operator inequality, and tensoring its positive semidefinite remainder with the reference identity proves the reference statement.

**Example 1.19 (The original golden memory is the p=alpha squared source).**

$$
alpha = \frac{sqrt\left(5\right) - 1}{2} \land \left(p = alpha^{2} \land \left(alpha^{2} + alpha = 1 \land \left(memory\left(p, 0, 0\right) = sqrt\left(alpha\right) \land \left(memory\left(p, 0, 1\right) = alpha \land historyConstant\left(p\right) = \frac{\frac{1 + alpha^{2}}{1 - alpha^{2}} + \frac{1}{1 - alpha^{4}}}{4}\right)\right)\right)\right)
$$

*Source.* Repository-derived.

*Commentary.*

alpha=(sqrt(5)-1)/2 lies strictly between zero and one and satisfies alpha squared plus alpha equals one. Consequently sqrt(1-alpha squared)=sqrt(alpha) and sqrt(alpha squared)=alpha, so the memory rows are exactly (sqrt(alpha),alpha) and (1,0). Substituting p=alpha squared into the local step therefore realizes the original memory amplitudes by the same actual unitary circuit for all lengths and start times. The center and history constant are specialized at alpha squared, not at alpha. The bound then applies to every constant theta, virtual history, congruent real lift and finite reference.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.Path`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.actual_source_moments`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.center`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.error`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.expectation`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.head`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.historyConstant`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.mean`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.memory`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.observed`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.pathAmplitude`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.pathMass`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.phaseSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.phase_history_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.register`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.source`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.step`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhaseHistoryBound.transition`
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](SequentialRegisterCircuit.md)
