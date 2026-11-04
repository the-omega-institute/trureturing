# Finite Configuration Acquisition

## Abstract

Finite configuration acquisition from an installed stationary port.

**Theorem 1.1 (The history criterion and an executable finite table).**

$$\forall E: \operatorname{Type}, [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)], F: \operatorname{Finset}\left(\operatorname{Finset}\left(E\right)\right), \operatorname{Nonempty}\left(F\right) \implies \forall Q: \operatorname{Type}, r: \operatorname{State}\left(F\right) \to Q,\\{}{{\exists p: \operatorname{History}\left(E, Q\right) \to \operatorname{Decision}\left(F\right), \operatorname{Acquires}\left(r, p\right)} \iff \operatorname{CommonEnabled}\left(r\right)} \land {\operatorname{CommonEnabled}\left(r\right) \iff \operatorname{IsolatedSinks}\left(r\right)} \land {\operatorname{CommonEnabled}\left(r\right) \iff \operatorname{FiniteAcquirable}\left(r\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition.acquisition_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E is a finite set of named events and F is any nonempty family of subsets of E. Every member of F may be the initial state. An event is enabled at C precisely when it is absent from C and inserting it produces a member of F. Sinks are defined by the absence of such events; no lower-set, reachability or connectedness assumption is imposed.

A history consists of the current port symbol and the complete reverse list of requested events paired with their preceding symbols. The entry history has an empty list. A successful Run stops with a claim equal to the actual current state, or makes one legal requested insertion and continues with its actual new port symbol. There are no refusal probes, enabled menus, resets, copies, extra reads or unrecorded changes.

Acquires quantifies all initial states and allows arbitrary mathematical functions of the complete history. On a nonsingleton entry fiber, the common first decision cannot be a correct stop for every member. It must therefore request one event enabled at every member. This argument imposes no restriction on later history use.

CommonEnabled asks for a common enabled event on every nonsingleton fiber. IsolatedSinks says that each sink has its own singleton fiber and that every fiber containing a nonsink has a common enabled event. Singleton nonsinks can still stop immediately when identified.

FiniteAcquirable supplies an injective natural-number encoding on the effective symbol image, a literal finite instruction list, a fixed fallback, and actual bounded runs of tablePolicy. The lookup program compares natural codes and recurses on the finite list, so each decision terminates by finite computation. Encoding and table preparation are part of the known model and code table. The existing common-legal-action selection theorem supplies the table entries; the execution and termination proof uses the strict decrease of the number of missing events.

The equivalence sandwiches every finite-computation history protocol between the unrestricted history class and an explicitly constructed finite-table protocol. Starting at C, the latter performs at most card E minus card C additions, then returns its actual stopping configuration. It permits zero additions and an early stop at a nonsink. The result optimizes neither preparation, memory, computation time nor physical realization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition.acquisition_criterion`
- Dependency: [D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence](DeterministicSafePolicyExistence.md)
