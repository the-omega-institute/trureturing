# Coherent returns, component phases and finite path-output templates

## Abstract

Synchronized labelled returns characterize bounded component phases and give a finite cover by multipower templates, with a two-loop obstruction to finite single-power replacement.

Vertices and output symbols are finite. Arrow types are unrestricted: parallel arrows, loops and nondeterministic choices remain actual arrows. Components are fibers of the native quotient by mutual directed reachability. Output equality does not identify graph paths, arrows or separately observed color histories. The template conclusion is a cover; arbitrary independent exponent choices are not asserted to realize graph paths.

**Definition 1.1 (Labels depend on actual arrows).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.EdgeLabel`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.EdgeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For vertex type V with a quiver and symbol type alpha, EdgeLabel V alpha assigns a symbol to every arrow, with its source and target implicit. No arrow type is assumed finite or subsingleton.

**Definition 1.2 (Outputs are native path weights).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.output`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any actual Quiver.Path H, output label H is the list underlying Path.weight in FreeMonoid alpha, where each arrow has singleton weight FreeMonoid.of(label e). Empty paths output the empty word and every arrow contributes exactly one symbol.

**Definition 1.3 (The native SCC fiber).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Component`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Component` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For S in Quiver.StronglyConnectedComponent V, Component S consists of vertices a whose native quotient class is S. Its quiver retains all ambient arrows between its vertices.

**Definition 1.4 (Inclusion preserves arrows).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentInclusion`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion prefunctor sends a component vertex to its ambient vertex and sends each actual internal arrow to that same ambient arrow.

**Definition 1.5 (Endpoint equality closes the whole path).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.liftComponentPath`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.liftComponentPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given an ambient path H and proofs that both endpoints belong to S, liftComponentPath returns an internal path whose image under the inclusion prefunctor is exactly H. Native mutual reachability supplies the closing path that puts each intermediate vertex in the same fiber. The equality retains actual arrows, not just their output labels.

**Definition 1.6 (Restrict labels to the component).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentLabel`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

componentLabel label S evaluates the original label on each actual arrow of the component quiver.

**Theorem 1.7 (Component inclusion preserves path length).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_length`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vertex type V, arbitrary quiver, strongly connected component S and actual internal path H, the ambient image of H under componentInclusion S has exactly the same length as H. No finiteness assumption is needed.

**Theorem 1.8 (Component inclusion preserves labelled output).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_output`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_output` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vertex type V, arbitrary quiver, symbol type alpha, edge labelling, strongly connected component S and actual internal path H, the output of its ambient image under the original labels is exactly its internal output under componentLabel label S. No finiteness assumption is needed.

**Definition 1.9 (Cyclicity uses an actual positive return).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Cyclic`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Cyclic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cyclic S means that there are q in Component S and an actual internal return C : Quiver.Path q q with positive path length. A one-vertex component is cyclic exactly when a positive return exists.

**Definition 1.10 (Exact LCM synchronization).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SynchronizedAt`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SynchronizedAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SynchronizedAt label q requires, for every pair of actual positive q-return paths A and B, equality of wordPower(L/length A)(output A) and wordPower(L/length B)(output B), where L is the least common multiple of their path lengths. It does not assume unique returns or unique graph paths.

**Definition 1.11 (Synchronization at some component basepoint).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Coherent`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Coherent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coherent label S asserts that SynchronizedAt holds at some actual vertex of Component S under the restricted edge labels.

**Definition 1.12 (Positive bounded cyclic block and all-edge laws).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.BoundedPhases`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.BoundedPhases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BoundedPhases label S asserts existence of a natural p with 1 <= p <= Nat.card(Component S), a cyclic word P : ZMod p -> alpha and a phase theta : Component S -> ZMod p. Every actual internal arrow e : a -> b has label P(theta a) and theta b = theta a + 1. A function on the p residues is a word with exactly p positions.

**Definition 1.13 (One purely periodic stream per entry).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PeriodicPrefixes`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PeriodicPrefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every entry a in Component S there exist one stream X : Nat -> alpha and one positive period p, with X(n+p)=X(n) for every n. For every actual finite internal path H from a and every i < length H, output(H)[i]? = some(X(i)). Empty paths are included.

**Definition 1.14 (Powers of actual returns).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.returnPower`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.returnPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

returnPower A 0 is the empty return. returnPower A (k+1) is A composed with returnPower A k, retaining every arrow of every copy.

**Definition 1.15 (Power and literal segments).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PowerTemplate`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PowerTemplate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A PowerTemplate is a finite list of pairs (P,a) of finite words. Each pair contributes P to a chosen nonnegative power followed by literal a. An empty P is only a literal segment. Omitting empty blocks and concatenating neighboring literals gives the conventional form a0 P1^k1 a1 ... Pd^kd ad, with every counted Pi nonempty.

**Definition 1.16 (Evaluate a fixed template).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.templateOutput`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.templateOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

templateOutput t k concatenates wordPower(k(0))(P), the first literal and the remaining template evaluated with i mapped to k(i+1). The blocks and literals are fixed before the exponents are chosen.

**Definition 1.17 (Count only positive periodic blocks).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.factorCount`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.factorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

factorCount t is the number of segments whose power block is nonempty. Literal-only segments and the empty template contribute zero factors.

**Definition 1.18 (Actual visited component set).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedComponents`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedComponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

visitedComponents H is the finite set of native SCC classes of the vertices in H, including both endpoints. The SCC-run construction proves that after leaving a component the path cannot revisit it.

**Definition 1.19 (Path-specific cyclic component count).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedCyclicCount`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedCyclicCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

visitedCyclicCount H counts the cyclic components in visitedComponents H. Since the component runs cannot revisit a class, it is the number of cyclic SCCs in this path's compressed component itinerary.

**Definition 1.20 (One finite family covers every actual path).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.FiniteTemplateCover`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.FiniteTemplateCover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one finite set T of PowerTemplate values such that for every actual finite graph path H, some t in T and some nonnegative exponent tuple k satisfy output H = templateOutput t k and factorCount t <= visitedCyclicCount H. Zero-factor templates, empty paths, acyclic graphs and paths through several cyclic SCCs are allowed.

**Definition 1.21 (Two distinct example vertices).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopVertex`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TwoLoopVertex has constructors left and right. The type has exactly these two vertices and carries the displayed finite instance.

**Definition 1.22 (Actual example arrows).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopArrow`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopArrow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TwoLoopArrow has a left loop, a right loop and one directed bridge from left to right. These are the only arrows of the example quiver; there is no reverse bridge.

**Definition 1.23 (Two loops and a directed bridge).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopLabel`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The example graph has vertices left and right, a loop at each vertex and one arrow from left to right. Over Fin 3 the left loop has symbol 0, the right loop symbol 1 and the bridge symbol 2. Its two cyclic SCCs are distinct and coherent.

**Definition 1.24 (Actual crossing paths with two exponents).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopCrossing`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopCrossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

twoLoopCrossing i j traverses the left loop i times, then the bridge, then the right loop j times. It is an actual left-to-right path; the graph also contains noncrossing paths.

**Definition 1.25 (The crossing sublanguage).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopWord`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

twoLoopWord i j is 0^i 2 1^j. For every n, the words indexed by i in Fin(n+1) with j=n-i are distinct and have length n+1.

**Definition 1.26 (Single-power templates include literal exceptions).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SinglePowerTemplate`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SinglePowerTemplate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SinglePowerTemplate stores fixed words before, block and after. An empty block permits a fixed literal exception, so the obstruction also excludes finite single-power families enlarged by finite literals.

**Definition 1.27 (Evaluate a single-power template).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.singlePowerOutput`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.singlePowerOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

singlePowerOutput t k is t.before followed by wordPower k t.block and then t.after, for any nonnegative k.

**Definition 1.28 (Growing output counts and no finite single-power cover).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopBoundary`

*Formalization.* `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two native SCCs are distinct and cyclic, every cyclic component is coherent, all crossing paths have the displayed outputs, and there are n+1 distinct crossing outputs of length n+1 for every n. No fixed finite set of SinglePowerTemplate values covers all of these outputs. This is an output-language obstruction; no observer history or decoder-width model is introduced.

**Theorem 1.29 (The complete local equivalence).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.coherent_component_phases`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.coherent_component_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type, arbitrary arrow-valued quiver, symbol type, edge labels and actual cyclic SCC S, Coherent label S is equivalent to BoundedPhases label S, and BoundedPhases label S is equivalent to PeriodicPrefixes label S. Coherence also implies SynchronizedAt at every component vertex. A positive actual return defines a repeated stream. LCM synchronization identifies every positive return stream; minimal-period facts give positivity and divisibility. Common closing paths give residue independence, completed edges give both edge laws, and the first p positions of the chosen return give surjectivity onto the p residues, hence p is at most the number of component vertices. No phase, primitive root, return divisibility, determinism or short-cycle bound is assumed.

**Theorem 1.30 (Local characterization, finite global cover and two-loop obstruction).**

Lean statement: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.result`

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite labelled quiver with finite output alphabet, the local characterization holds for every cyclic SCC. If every cyclic SCC is coherent, FiniteTemplateCover holds. The same conclusion includes TwoLoopBoundary. The global construction cuts actual paths into SCC runs, proves no revisit using native mutual reachability, writes each cyclic run as a rotated block power and bounded remainder, and enumerates one finite family of bounded output signatures. The factor bound uses the cyclic components visited by that particular path. In the two-loop graph each single-power template contributes at most one output of any fixed length; the n+1 distinct crossing outputs therefore exclude a finite single-power cover. The multipower form permits growing fixed-length output counts and supplies no uniform candidate-width conclusion by itself. No conclusion about a particular observation history or decoder is asserted.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.BoundedPhases`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Coherent`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Component`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.Cyclic`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.EdgeLabel`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.FiniteTemplateCover`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PeriodicPrefixes`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.PowerTemplate`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SinglePowerTemplate`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.SynchronizedAt`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopArrow`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopBoundary`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.TwoLoopVertex`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.coherent_component_phases`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentInclusion`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.componentLabel`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_length`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.component_inclusion_output`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.factorCount`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.liftComponentPath`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.output`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.result`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.returnPower`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.singlePowerOutput`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.templateOutput`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopCrossing`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopLabel`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.twoLoopWord`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedComponents`
- Truth anchor: `D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.visitedCyclicCount`
