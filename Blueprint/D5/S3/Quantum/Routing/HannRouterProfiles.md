# Physical router profiles

## Abstract

Independent heterogeneous records on the actual loaded Hann routers have exactly the active-profile rank, complex kernel and complete fidelity-minimizer fibers.

**Definition 1.1 (Internal router coordinates).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.Router`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.Router` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Router zero is empty. At a successor, none denotes the root router and some(b,v) denotes v in the right child when b is true and the left child otherwise. routerLabel reads the router field of the actual nested Tree. Incident and output rails are excluded. This indexes every internal router, including those off the programmed path.

**Definition 1.2 (Deepest physical router).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.deepest`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.deepest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

snoc appends a final bit to the existing head-first Address. deepest n u is the actual depth-n router reached by the length-n prefix u. In the fully programmed tree for snoc u b, its label at deepest n i is encode b if i equals u and wait otherwise. Siblings snoc u false and snoc u true agree at every other internal router. Both statements hold at every natural n.

**Definition 1.3 (Actual sequential loading).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

loadedLabel reads routerLabel after load n n on loading n a bus zero. The existing sequential-loading identity identifies this tree with programmed n a n, for every external qutrit bus label. Thus no bus label affects the observed router profile.

**Definition 1.4 (Active profile equality).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rate q is an arbitrary function on all internal routers. A router is active precisely when its rate is less than one. SameProfile requires equality of loadedLabel at every active router, allowing the two bus labels to differ. Separates means that this equality always forces the two addresses to coincide.

**Theorem 1.5 (Exact physical profile separation criterion).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n + 1\right) \to Real,\; \left(\forall a \in \operatorname{Address}\left(n + 1\right),\; \forall aPrime \in \operatorname{Address}\left(n + 1\right),\; \forall bus \in Qutrit,\; \forall busPrime \in Qutrit,\; \left(\forall v \in \operatorname{Router}\left(n + 1\right),\; q\left(v\right) < 1 \Rightarrow \operatorname{loadedLabel}\left(n + 1, a, bus, v\right) = \operatorname{loadedLabel}\left(n + 1, aPrime, busPrime, v\right)\right) \Rightarrow a = aPrime\right) \Leftrightarrow \left(\forall u \in \operatorname{Address}\left(n\right),\; q\left(\operatorname{deepest}\left(n, u\right)\right) < 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterProfiles.profile_separation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive tree depth n+1, all addresses are distinguished exactly when every depth-n router has rate less than one. Necessity uses two siblings under an inactive deepest router: every other literal router label agrees. Sufficiency observes the deepest router under the first address prefix. Different prefixes give an occupied label versus wait; equal prefixes give the two encoded final bits. No restriction on the real rates is needed for this combinatorial equivalence, so independent rates in the closed unit interval and both endpoints are included. The statement concerns the actual loaded physical coordinates. It does not assert record independence, Gram rank or kernel, simplex optimization, or a noisy-continuation formula.

**Definition 1.6 (Independent local environments).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.Environment`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.Environment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Environment n is the function space Router n to Option Qutrit, giving four independent coordinates per internal router. The common coordinate is none; some wait, some zero and some one are the three literal label coordinates. At each node v, localRecord uses sqrt(q(v)) on the common coordinate and sqrt(1-q(v)) on its own label. At depth zero the environment is a singleton and the empty tensor product is one.

**Definition 1.7 (Physical tensor records and loading bridge).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.treeRecord`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.treeRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

treeRecord n q t multiplies the original HannRouterDephasing.localRecord over every literal routerLabel of t. record n q a uses loadedLabel after the actual load, with an arbitrary unobserved qutrit bus. The theorem identifies treeRecord after load with record for every bus. Rates are independent functions on Router n, each in the closed unit interval. No incident or output rail receives a record.

**Definition 1.8 (Realized active profiles and class records).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.Profile`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.Profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Profile n q is the range of the address-to-label function restricted to nodes with q(v)<1. profile is the surjective class map. classRecord selects any representative; records of equal profiles coincide because q(v)=1 at all inactive nodes. Thus its definition is independent of that selection. Unattained label assignments are absent. Equality of classes is exactly SameProfile, even for different external bus labels.

**Definition 1.9 (Complex physical Gram and its kernel).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.gram`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gram(a,b) is the environment sum record(a,e) times conjugate(record(b,e)), in density-matrix orientation. All these records are real. A class is sampled by selecting its label coordinate at each active node and the common coordinate elsewhere. The sample is zero on all other classes and has the strictly positive product of sqrt(1-q(v)) over active nodes on its own class. These actual environment coordinates prove class-record independence. Mathlib Gram rank and kernel theorems then apply. classSum is the sum of arbitrary coefficients over each profile fiber.

**Definition 1.10 (Physical quadratic forms).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.classEnergy`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.classEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

addressEnergy(p) is the real double sum p(a)p(b)gram(a,b).re. classEnergy(x) is the environment sum of normSq of the superposition sum x(c)classRecord(c,e). The class records are linearly independent, so this quadratic is strictly positive on every nonzero real coefficient vector. The class-mass factorization identifies addressEnergy with classEnergy after pushforward.

**Definition 1.11 (Probability laws and disintegrations).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.ClassDistribution`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.ClassDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ClassDistribution and AddressDistribution are the bundled Convexity.StdSimplex over realized classes and addresses. Their weights are nonnegative and sum to one. classMass is the existing simplex map along profile, and its weights are classSum. This map is surjective: every class law has a nonnegative disintegration over all its address fibers, including when some class weights vanish.

**Definition 1.12 (Actual hold and unchanged ideal continuation).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.jointOutput`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.jointOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

jointOutput pulls the original initialized amplitudes back through the actual load and the original HannRouterDephasing.postLoad permutation, then appends treeRecord at that physical hold state. postLoad is unchanged: exchange, transport, leaf readout and reverse forward. noisyOutput traces the complete independent environment, and squaredFidelity is the full physical-State ideal-output expectation. idealOutput, outputBasis, Normalized and addressProbability retain their original scalar-module definitions; only the router rates and records are heterogeneous. In the formula, prehold(n,D,s) abbreviates inverse(load n n)(inverse(postLoad n D)(s)); loadedTree abbreviates the tree component of load n n (loading n a bus zero).

**Definition 1.13 (Arbitrary joint amplitudes and realizable laws).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.inputDistribution`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.inputDistribution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inputDistribution is the address law of any normalized complex address/bus input, summing normSq over both bus labels. No product-state assumption is made. distributionInput realizes every address law using its nonnegative square roots and the clean false bus. Hence minimization over normalized joint inputs and over the address simplex have exactly the same class-mass criterion.

**Definition 1.14 (Full-rank activity criterion).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.DeepestActive`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.DeepestActive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DeepestActive zero q is True. At depth m+1 it means q(deepest m u)<1 for every length-m prefix u. Full rank is equivalent to this condition at every depth; at zero the rank is one. The proof uses deepest_label to distinguish different parents and final bits, and sibling_labels to merge siblings under an inactive deepest node. These physical relations feed the Gram-rank conclusion.

**Theorem 1.15 (Complete physical profile, rank, kernel and minimizer event).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \left(\forall v \in \operatorname{Router}\left(n\right),\; 0 \le q\left(v\right) \land q\left(v\right) \le 1\right) \Rightarrow \left(\forall D \in \operatorname{Address}\left(n\right) \to Bool,\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\forall a \in \operatorname{Address}\left(n\right),\; \forall bus \in Qutrit,\; \operatorname{treeRecord}\left(n, q, \operatorname{loadedTree}\left(n, a, bus\right)\right) = \operatorname{record}\left(n, q, a\right)\right) \land \left(\forall t \in \operatorname{Tree}\left(n\right),\; \sum_{e\in \operatorname{Environment}\left(n\right)}{\operatorname{normSq}\left(\operatorname{treeRecord}\left(n, q, t, e\right)\right)} = 1\right)\right) \land \left(\forall a \in \operatorname{Address}\left(n\right),\; \forall b \in \operatorname{Address}\left(n\right),\; \forall bus \in Qutrit,\; \forall busPrime \in Qutrit,\; \operatorname{profile}\left(n, q, a\right) = \operatorname{profile}\left(n, q, b\right) \Leftrightarrow \left(\forall v \in \operatorname{Router}\left(n\right),\; q\left(v\right) < 1 \Rightarrow \operatorname{loadedLabel}\left(n, a, bus, v\right) = \operatorname{loadedLabel}\left(n, b, busPrime, v\right)\right)\right)\right) \land \operatorname{LinearIndependent}\left(Complex, \operatorname{classRecord}\left(n, q\right)\right)\right) \land \operatorname{rank}\left(\operatorname{gram}\left(n, q\right)\right) = \operatorname{card}\left(\operatorname{Profile}\left(n, q\right)\right)\right) \land \left(\forall z \in \operatorname{Address}\left(n\right) \to Complex,\; \operatorname{mulVec}\left(\operatorname{gram}\left(n, q\right), z\right) = 0 \Leftrightarrow \left(\forall c \in \operatorname{Profile}\left(n, q\right),\; \operatorname{classSum}\left(n, q, z, c\right) = 0\right)\right)\right) \land \left(\operatorname{rank}\left(\operatorname{gram}\left(n, q\right)\right) = 2^{n} \Leftrightarrow \operatorname{DeepestActive}\left(n, q\right)\right)\right) \land \left(n = 0 \Rightarrow \operatorname{rank}\left(\operatorname{gram}\left(n, q\right)\right) = 1\right)\right) \land \left(\forall p \in \operatorname{AddressDistribution}\left(n\right),\; \operatorname{addressEnergy}\left(n, q, \operatorname{weights}\left(p\right)\right) = \operatorname{classEnergy}\left(n, q, \operatorname{weights}\left(\operatorname{classMass}\left(n, q, p\right)\right)\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall s \in \operatorname{State}\left(n\right),\; \operatorname{idealOutput}\left(n, D, psi, s\right) = \operatorname{initialized}\left(n, psi, \operatorname{prehold}\left(n, D, s\right)\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \forall a \in \operatorname{Address}\left(n\right),\; \forall aPrime \in \operatorname{Address}\left(n\right),\; \forall bit \in Bool,\; \forall bitPrime \in Bool,\; \operatorname{noisyOutput}\left(n, q, D, psi, \operatorname{outputBasis}\left(n, D, \operatorname{pair}\left(a, bit\right)\right), \operatorname{outputBasis}\left(n, D, \operatorname{pair}\left(aPrime, bitPrime\right)\right)\right) = psi\left(\operatorname{pair}\left(a, bit\right)\right) \cdot \operatorname{conj}\left(psi\left(\operatorname{pair}\left(aPrime, bitPrime\right)\right)\right) \cdot \operatorname{gram}\left(n, q\right)\left(a, aPrime\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \operatorname{squaredFidelity}\left(n, q, D, psi\right) = \operatorname{ofReal}\left(\operatorname{addressEnergy}\left(n, q, \operatorname{addressProbability}\left(n, psi\right)\right)\right)\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \operatorname{Normalized}\left(n, psi\right) \Rightarrow \left(\sum_{s\in \operatorname{State}\left(n\right)}{\sum_{e\in \operatorname{Environment}\left(n\right)}{\operatorname{normSq}\left(\operatorname{jointOutput}\left(n, q, D, psi, s, e\right)\right)}} = 1 \land \sum_{s\in \operatorname{State}\left(n\right)}{\operatorname{normSq}\left(\operatorname{idealOutput}\left(n, D, psi, s\right)\right)} = 1\right)\right)\right) \land \left(\forall p \in \operatorname{AddressDistribution}\left(n\right),\; \operatorname{Normalized}\left(n, \operatorname{distributionInput}\left(n, p\right)\right) \land \operatorname{inputDistribution}\left(n, \operatorname{distributionInput}\left(n, p\right)\right) = p\right)\right) \land \left(\exists x \in \operatorname{ClassDistribution}\left(n, q\right),\; \left(\left(\left(\left(\forall z \in \operatorname{ClassDistribution}\left(n, q\right),\; \operatorname{classEnergy}\left(n, q, \operatorname{weights}\left(x\right)\right) \le \operatorname{classEnergy}\left(n, q, \operatorname{weights}\left(z\right)\right)\right) \land \left(\forall y \in \operatorname{ClassDistribution}\left(n, q\right),\; \left(\forall z \in \operatorname{ClassDistribution}\left(n, q\right),\; \operatorname{classEnergy}\left(n, q, \operatorname{weights}\left(y\right)\right) \le \operatorname{classEnergy}\left(n, q, \operatorname{weights}\left(z\right)\right)\right) \Rightarrow y = x\right)\right) \land \operatorname{Surjective}\left(\operatorname{classMass}\left(n, q\right)\right)\right) \land \left(\forall p \in \operatorname{AddressDistribution}\left(n\right),\; \left(\forall r \in \operatorname{AddressDistribution}\left(n\right),\; \operatorname{addressEnergy}\left(n, q, \operatorname{weights}\left(p\right)\right) \le \operatorname{addressEnergy}\left(n, q, \operatorname{weights}\left(r\right)\right)\right) \Leftrightarrow \operatorname{classMass}\left(n, q, p\right) = x\right)\right) \land \left(\forall psi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \operatorname{Normalized}\left(n, psi\right) \Rightarrow \left(\left(\forall phi \in \operatorname{Prod}\left(\operatorname{Address}\left(n\right), Bool\right) \to Complex,\; \operatorname{Normalized}\left(n, phi\right) \Rightarrow \operatorname{re}\left(\operatorname{squaredFidelity}\left(n, q, D, psi\right)\right) \le \operatorname{re}\left(\operatorname{squaredFidelity}\left(n, q, D, phi\right)\right)\right) \Leftrightarrow \operatorname{classMass}\left(n, q, \operatorname{inputDistribution}\left(n, psi\right)\right) = x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterProfiles.physical_profile_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural depth, every independent rate in the closed unit interval, every classical memory D and arbitrary complex joint address/bus amplitudes are included. The class simplex is compact and the physical squared-norm objective is continuous. Its midpoint gap is one quarter of the strictly positive quadratic of the difference, so the minimizing class law x is unique. All minimizing address laws are exactly the entire pushforward fiber over x, and the same criterion characterizes all normalized-input fidelity minimizers. No full-support condition is imposed. The generic Gram and simplex arguments are consumed auxiliary reasoning. Leinster, arXiv:0910.0906v4, Theorem 3.1 and Corollary 4.1 give generic optimizer context; no unproved literature premise enters the Lean proof. The result is conditional on the stated independent single router hold and ideal remaining gates. It gives no general nonhomogeneous sharp-minimum algorithm.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.ClassDistribution`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.DeepestActive`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.Environment`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.Profile`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.Router`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.classEnergy`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.deepest`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.gram`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.inputDistribution`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.jointOutput`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.physical_profile_event`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.profile_separation_iff`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.treeRecord`
- Dependency: [D5/S3/Quantum/Routing/HannRouterDephasing](HannRouterDephasing.md)
- Dependency: [D5/S3/Quantum/Routing/HannSpatialQram](HannSpatialQram.md)
