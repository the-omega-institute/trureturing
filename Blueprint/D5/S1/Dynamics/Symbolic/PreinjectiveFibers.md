# Finite Fibers from Preinjectivity

## Abstract

Native preinjectivity bounds every complete-output fiber of a finite-alphabet integer block code by card(A)^(2(k+1)).

Let A : Type(u), k be a natural number and h : (Fin(k+2) → A) → A be arbitrary. The original BipermutativeLift.code maps x : Z → A to i ↦ h(j ↦ x(i+j)). The original BipermutativePreinjectivity.Preinjective predicate says that configurations differing at finitely many integer coordinates and having equal complete code images are equal. No endpoint permutativity or injectivity hypothesis is imposed.

**Definition 1.1 (Read the two outer collars).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall k: \mathbb{N},\\\forall a: \mathbb{Z},\\\forall b: \mathbb{Z},\\\forall x: (\mathbb{Z} \to A),\\\operatorname{collarPair}(k, a, b, x) = ((j: \operatorname{Fin}(k + 1) \mapsto \operatorname{x}(a - \operatorname{cast}(k + 1) + \operatorname{cast}(j))), (j: \operatorname{Fin}(k + 1) \mapsto \operatorname{x}(b + 1 + \operatorname{cast}(j))))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.collarPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each component is a word indexed by Fin(k+1). The left collar occupies a-(k+1) through a-1, and the right collar occupies b+1 through b+(k+1). The definition itself allows arbitrary integers a,b and arbitrary alphabets.

**Theorem 1.2 (A finite family is separated by two collars).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\operatorname{BipermutativePreinjectivity.Preinjective}(h) \Rightarrow\\\forall y: (\mathbb{Z} \to A),\\\forall F: \operatorname{Finset}((\mathbb{Z} \to A)),\\(\forall x: (\mathbb{Z} \to A),x \in F \Rightarrow \operatorname{BipermutativeLift.code}(h, x) = y) \Rightarrow\\\exists a: \mathbb{Z},\\\exists b: \mathbb{Z},\\a \le b \land\\\operatorname{Set.InjOn}(\operatorname{collarPair}(k, a, b), \operatorname{coeSet}(F))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.finite_family_two_collar_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jarkko Kari and Siamak Taati (2015). *Statistical Mechanics of Surjective Cellular Automata*. DOI: [10.1007/s10955-015-1281-2](https://doi.org/10.1007/s10955-015-1281-2). URL: <https://arxiv.org/html/1311.2319v3>.

*Commentary.*

The alphabet need not be finite or nonempty. For every finite family F of arbitrary integer configurations whose complete images all equal the prescribed y, there exist a≤b such that collarPair(k,a,b) is injective on F.

Choose one distinguishing coordinate for each unequal pair in F and enclose all these coordinates in a single interval [a,b]. Suppose two members x,z agree on both outer collars. Splice x on [a,b] into z outside [a,b]. A local output window missing the interval is unchanged. A window meeting the interval stays within the padded interval, where its exterior entries agree by the collars, so its output equals the corresponding output of x and hence of z. The splice differs from z on only finitely many coordinates. Preinjectivity forces it to equal z, so x and z agree throughout [a,b]. The chosen distinguishing coordinates then force x=z. The interval can depend on F; no single interval for the entire fiber is asserted.

The cited source's Theorem 22 proof, immediately before equation (34), uses preinjectivity and finite-type gluing to determine an interior pattern from boundary and image patterns: a finite splice preserves the complete image and hence equals the original. This is the classical boundary mechanism used here. The exact finite-family collar encoding for arbitrary alphabets is a repository deduction.

**Theorem 1.3 (Every complete-output fiber is uniformly finite).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall k: \mathbb{N},\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\operatorname{BipermutativePreinjectivity.Preinjective}(h) \Rightarrow\\\forall y: (\mathbb{Z} \to A),\\\operatorname{Set.Finite}(\{x: (\mathbb{Z} \to A) \mid \operatorname{BipermutativeLift.code}(h, x) = y\}) \land\\\operatorname{Set.ncard}(\{x: (\mathbb{Z} \to A) \mid \operatorname{BipermutativeLift.code}(h, x) = y\}) \le \operatorname{Nat.card}(A)^{2 \cdot (k + 1)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.finite_fiber_ncard_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jarkko Kari and Siamak Taati (2015). *Statistical Mechanics of Surjective Cellular Automata*. DOI: [10.1007/s10955-015-1281-2](https://doi.org/10.1007/s10955-015-1281-2). URL: <https://arxiv.org/html/1311.2319v3>.

*Commentary.*

For every universe u, every A : Type(u) with Finite(A), every natural k, every arbitrary local rule h and every complete output y : Z → A, native preinjectivity implies both explicit finiteness of {x : Z → A | code(h,x)=y} and its Set.ncard bound card(A)^(2(k+1)). The empty and singleton alphabets are included. Configurations and outputs have no finite-support or periodicity restriction, and no balance, finite-fiber or growth certificate is an extra premise.

Apply the finite-family encoding to any finite subset of the fiber. Its target consists of pairs of words of length k+1, so it has card(A)^(k+1)·card(A)^(k+1)=card(A)^(2(k+1)) elements. An injection gives that bound for every finite subset. If the full fiber were infinite, it would contain a finite subset with one more element than the bound, a contradiction. Applying the bound to the now finite full fiber proves the ncard inequality. This is a classical deduction; the bound is not asserted sharp and supplies no effective inversion algorithm.

The exact complete-output fiber finiteness and ncard bound are repository deductions from the classical boundary mechanism, the native code interface and generic finite-set cardinality results. The cited Theorem 22 concerns measure-entropy preservation for a preinjective factor map from a shift of finite type onto a shift; its proof is cited for the mechanism, not as a statement of this exact bound. No literature novelty is claimed.

For an entropy application, equip the finite alphabet with discrete uniformity, put X=A^Z and let Y be the actual range of code(h). The source X is compact, and continuity of code(h) makes Y compact. Let S be spatial shift by one on X, T its restriction to Y, and π : X → Y the code with its codomain restricted to its range. The original code_shift identity makes π a surjective semiconjugacy. Subtype equality identifies each π-fiber with the complete-output fiber above, with the same explicit finiteness and uniform bound. D5.S1.Dynamics.FiniteFiberEntropy.finite_fiber_entropy therefore gives equal covering entropy for S on X and T on Y, including the empty case. These are spatial shift dynamics; this consequence does not concern iteration of code(h).

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.collarPair`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.finite_family_two_collar_encoding`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PreinjectiveFibers.finite_fiber_ncard_le`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity](PermutativeLifts/BipermutativePreinjectivity.md)
