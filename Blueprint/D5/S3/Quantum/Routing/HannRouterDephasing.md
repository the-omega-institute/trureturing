# Single-hold physical router dephasing

## Abstract

One independent router hold in the initialized spatial QRAM has an exact tree kernel and sharp fidelity.

**Definition 1.1 (Actual internal router coordinates).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterDephasing.routerMismatch`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterDephasing.routerMismatch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

addressWord converts the existing recursive Address to its head-first Boolean list. routerMismatch compares the router coordinate in each Interior and then both child Trees. It excludes all incident and output rails. The loaded trees come from HannSpatialQram.load n n on clean inputs. Their comparison is proved by induction on the literal programmed trees: equal first bits leave the child comparison; opposite first bits contribute one root difference and one occupied path in each distinct subtree. ell below is the length of BinaryWordGeometry.lcp of the two addressWords. loadedTree(n,a,b) in the display abbreviates the Tree projection of load n n (clean n a b).

**Definition 1.2 (Independent four-dimensional local records).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterDephasing.environmentRecord`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterDephasing.environmentRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Environment zero is Unit. At a successor it is Option Qutrit times the two child environments. none is the common coordinate and some s is the coordinate for label s. localRecord has amplitude sqrt(q) at none and sqrt(1-q) at some s. environmentRecord multiplies these amplitudes over the actual routers. recordOverlap is the sum of a record times the conjugate of the other record over the complete environment basis. The local marginal is q X plus (1-q) times the W,zero,one diagonal of X.

**Definition 1.3 (Actual continuation and environment marginal).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterDephasing.noisyOutput`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterDephasing.noisyOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

postLoad is exchange, transport, fixed leaf readout, then the inverse of the original forward circuit. Its composition with the actual load is the original query. jointOutput pulls initialized amplitudes through these permutations and appends the independent router records at the hold. noisyOutput is its environment partial trace, as verified entry by entry. No gate, bus, address slot or spatial mode receives noise. outputBasis at (a,b) is clean n a (b XOR D(a)); idealOutput is the sum of psi(a,b) on this basis.

**Definition 1.4 (Squared fidelity and its minimum).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterDephasing.minimumFidelity`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterDephasing.minimumFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

squaredFidelity is the full-State double sum conjugate(idealOutput(s)) times noisyOutput(s,t) times idealOutput(t). addressProbability(a) is the sum of normSq over both bus amplitudes. addressEnergy is the double address sum p(a)p(a')kernel(a,a'). Normalized means the complete address/bus normSq sum is one. kernel is one on the diagonal and q to the power 2(n-ell)-1 otherwise. minimumFidelity is (1 + sum over j in range n of 2^j q^(2j+1))/2^n. Reindexing j to j+1 gives the sum from 1 through n. uniformInput has bus false and amplitude the positive inverse square root of 2^n; the theorem also identifies it with 2^(-n/2).

**Theorem 1.5 (Physical router kernel and least ideal-output fidelity).**

$$\forall n \in Nat,\; \forall q \in Real,\; 0 \le q \Rightarrow \left(q \le 1 \Rightarrow \left(\forall D \in \operatorname{Address}\left(n\right) \to Bool,\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall X \in \operatorname{Matrix}\left(Qutrit, Qutrit, Complex\right),\; \forall s \in Qutrit,\; \forall t \in Qutrit,\; \sum_{e\in \operatorname{Option}\left(Qutrit\right)}{\operatorname{localRecord}\left(q, s, e\right) \cdot \operatorname{conj}\left(\operatorname{localRecord}\left(q, t, e\right)\right)} \cdot X\left(s, t\right) = q \cdot X\left(s, t\right) + \left(1 - q\right) \cdot \operatorname{ite}\left(s = t, X\left(s, t\right), 0\right)\right) \land \left(\forall t \in \operatorname{Tree}\left(n\right),\; \operatorname{recordOverlap}\left(n, q, t, t\right) = 1\right)\right) \land \left(\forall a \in \operatorname{Address}\left(n\right),\; \forall aPrime \in \operatorname{Address}\left(n\right),\; \forall b \in Bool,\; \forall bPrime \in Bool,\; \operatorname{routerMismatch}\left(n, \operatorname{loadedTree}\left(n, a, b\right), \operatorname{loadedTree}\left(n, aPrime, bPrime\right)\right) = \operatorname{ite}\left(a = aPrime, 0, 2 \cdot \left(n - \operatorname{ell}\left(a, aPrime\right)\right) - 1\right) \land \operatorname{recordOverlap}\left(n, q, \operatorname{loadedTree}\left(n, a, b\right), \operatorname{loadedTree}\left(n, aPrime, bPrime\right)\right) = \operatorname{kernel}\left(n, q, a, aPrime\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall s \in \operatorname{State}\left(n\right),\; \forall t \in \operatorname{State}\left(n\right),\; \sum_{e\in \operatorname{Environment}\left(n\right)}{\operatorname{jointOutput}\left(n, q, D, psi\right)\left(s, e\right) \cdot \operatorname{conj}\left(\operatorname{jointOutput}\left(n, q, D, psi\right)\left(t, e\right)\right)} = \operatorname{noisyOutput}\left(n, q, D, psi\right)\left(s, t\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall a \in \operatorname{Address}\left(n\right),\; \forall aPrime \in \operatorname{Address}\left(n\right),\; \forall b \in Bool,\; \forall bPrime \in Bool,\; \operatorname{noisyOutput}\left(n, q, D, psi\right)\left(\operatorname{clean}\left(n, a, \operatorname{xor}\left(b, D\left(a\right)\right)\right), \operatorname{clean}\left(n, aPrime, \operatorname{xor}\left(bPrime, D\left(aPrime\right)\right)\right)\right) = psi\left(\operatorname{pair}\left(a, b\right)\right) \cdot \operatorname{conj}\left(psi\left(\operatorname{pair}\left(aPrime, bPrime\right)\right)\right) \cdot \operatorname{kernel}\left(n, q, a, aPrime\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall s \in \operatorname{State}\left(n\right),\; \forall t \in \operatorname{State}\left(n\right),\; \left(\left(\forall a \in \operatorname{Address}\left(n\right),\; \forall b \in Bool,\; s \ne \operatorname{clean}\left(n, a, b\right)\right) \lor \left(\forall a \in \operatorname{Address}\left(n\right),\; \forall b \in Bool,\; t \ne \operatorname{clean}\left(n, a, b\right)\right)\right) \Rightarrow \operatorname{noisyOutput}\left(n, q, D, psi\right)\left(s, t\right) = 0\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \operatorname{Normalized}\left(n, psi\right) \Rightarrow \left(\left(\sum_{s\in \operatorname{State}\left(n\right)}{\operatorname{normSq}\left(\operatorname{idealOutput}\left(n, D, psi, s\right)\right)} = 1 \land \operatorname{squaredFidelity}\left(n, q, D, psi\right) = \operatorname{addressEnergy}\left(n, q, \operatorname{addressProbability}\left(n, psi\right)\right)\right) \land \operatorname{minimumFidelity}\left(n, q\right) \le \operatorname{re}\left(\operatorname{squaredFidelity}\left(n, q, D, psi\right)\right)\right)\right)\right) \land \operatorname{Normalized}\left(n, \operatorname{uniformInput}\left(n\right)\right)\right) \land \operatorname{squaredFidelity}\left(n, q, D, \operatorname{uniformInput}\left(n\right)\right) = \operatorname{minimumFidelity}\left(n, q\right)\right) \land \operatorname{minimumFidelity}\left(0, q\right) = 1\right) \land \left(\forall ab \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right),\; \operatorname{uniformInput}\left(n, ab\right) = \operatorname{ite}\left(\operatorname{snd}\left(ab\right), 0, \operatorname{rpow}\left(2, \frac{\operatorname{neg}\left(\operatorname{realCast}\left(n\right)\right)}{2}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterDephasing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All natural depths, every classical D and every normalized complex address/bus amplitude are included. The q interval is closed. At depth zero there are no routers and minimumFidelity is one. Off-span entries vanish. The minimum proof splits address weights by the first bit; the nonnegative remainder is proportional to the squared difference of the two branch masses. Constant kernel row sums give uniform attainment. The router mismatch formula determines the exponent in each clean-output matrix entry. The result assumes this single router hold and ideal remaining gates.

**Theorem 1.6 (Clean input amplitude evaluation).**

$$\forall n \in Nat,\; \forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall a \in \operatorname{Address}\left(n\right),\; \forall b \in Bool,\; \operatorname{initialized}\left(n, psi, \operatorname{clean}\left(n, a, b\right)\right) = psi\left(\operatorname{pair}\left(a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterDephasing.initialized_clean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every depth and arbitrary complex joint address/bus amplitudes, initialized evaluates to the corresponding coefficient on each clean basis state. This is the exact amplitude supplier used by the heterogeneous physical hold.

**Theorem 1.7 (Finite ket evaluation under a sum).**

$$\forall iota \in Type,\; \forall sigma \in Type,\; \forall indices \in \operatorname{Fintype}\left(iota\right),\; \forall bases \in \operatorname{Fintype}\left(sigma\right),\; \forall decidable \in \operatorname{DecidableEq}\left(sigma\right),\; \forall v \in iota \to sigma,\; \forall psi \in iota \to Complex,\; \forall g \in sigma \to Complex,\; \sum_{s\in sigma}{\sum_{i\in iota}{\operatorname{ite}\left(s = v\left(i\right), psi\left(i\right), 0\right)} \cdot g\left(s\right)} = \sum_{i\in iota}{psi\left(i\right) \cdot g\left(v\left(i\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterDephasing.sum_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both index types are arbitrary finite types. The basis type has decidable equality. Summing a finite ket against any function evaluates that function at each ket basis point. No injectivity of the basis map is assumed.

**Theorem 1.8 (Conjugate finite ket evaluation).**

$$\forall iota \in Type,\; \forall sigma \in Type,\; \forall indices \in \operatorname{Fintype}\left(iota\right),\; \forall bases \in \operatorname{Fintype}\left(sigma\right),\; \forall decidable \in \operatorname{DecidableEq}\left(sigma\right),\; \forall v \in iota \to sigma,\; \forall psi \in iota \to Complex,\; \forall g \in sigma \to Complex,\; \sum_{s\in sigma}{\operatorname{conj}\left(\sum_{i\in iota}{\operatorname{ite}\left(s = v\left(i\right), psi\left(i\right), 0\right)}\right) \cdot g\left(s\right)} = \sum_{i\in iota}{\operatorname{conj}\left(psi\left(i\right)\right) \cdot g\left(v\left(i\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterDephasing.sum_ket_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate ket identity has the same complete finite-type scope. These two summation identities are consumed in the full-State fidelity calculation for arbitrary joint amplitudes.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.environmentRecord`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.initialized_clean`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.minimumFidelity`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.noisyOutput`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.result`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.routerMismatch`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.sum_ket`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterDephasing.sum_ket_conj`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/BinaryWordGeometry](../../Combinatorics/Graph/Walks/BinaryWordGeometry.md)
- Dependency: [D5/S3/Quantum/Routing/HannSpatialQram](HannSpatialQram.md)
