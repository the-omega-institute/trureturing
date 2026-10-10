# Trace-Keyed Artifact Cache Soundness

## Abstract

When realized build inputs have no key collision, a trace-keyed artifact cache filled only by from-scratch builds yields from-scratch artifacts, and an unaffected module whose writer key is present at lookup is restored.

**Theorem 1.1 (Reader builds equal from-scratch builds).**

$$\begin{gathered}\forall B: \operatorname{BuildSystem}, writers: \operatorname{Set}\left(\operatorname{Snapshot}\left(B.Node, B.Src\right)\right), T: \operatorname{Snapshot}\left(B.Node, B.Src\right),\\{}\operatorname{NoCollision}\left(B, \operatorname{insert}\left(T, writers\right)\right) \Rightarrow\\{}\forall schedule: B.Node \to \operatorname{List}\left(\operatorname{Op}\left(B.Node, B.Src\right)\right),\\{}(\forall n, W, m, \operatorname{store}\left(W, m\right) \in \operatorname{schedule}\left(n\right) \Rightarrow W \in writers) \Rightarrow\\{}\forall n: B.Node, \operatorname{cachedBuild}\left(B, \lambda n \mapsto \operatorname{run}\left(B, \operatorname{schedule}\left(n\right)\right), T, n\right) = \operatorname{build}\left(B, T, n\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness.cachedBuild_eq_build` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A build system B bundles types of modules, sources, artifacts, digests and keys with a compiler from a source and a set of artifacts, a key function from a source and a set of digests, and an artifact digest. A snapshot assigns every module a source and the finite set of modules whose artifacts its build reads; a natural-number rank decreases along these dependencies. build compiles a module's source against the set of its dependencies' artifacts. traceKey hashes the source together with the set of digests of those artifacts.

A cache state maps keys to optional artifacts. store(W, m) writes the from-scratch artifact of m in W under its key, clean empties the cache, and run applies a list of operations to the empty cache. cachedBuild computes the key of a module from its own dependency artifacts, returns the stored artifact on a hit and compiles on a miss. The state consulted for each module is arbitrary, so stores and cleans may interleave with the reader in any order.

NoCollision asks only that equal keys realized by the writers and the reader come from equal sources and equal sets of dependency artifacts; an injective pairing satisfies it. Every state reached by writer stores and cleans holds only from-scratch artifacts under their own keys. Strong induction on rank makes the reader's dependency artifacts equal to the from-scratch ones, so the key it computes is traceKey. A hit was stored by some writer under the same key, NoCollision equates the two build inputs, and compile returns the same artifact; a miss compiles the same input directly.

The conclusion does not require the reader to be distinct from the writers: any snapshot whose stores are honest from-scratch builds may write without affecting soundness.

**Theorem 1.2 (Unaffected modules are restored).**

$$\begin{gathered}\forall B: \operatorname{BuildSystem}, writers: \operatorname{Set}\left(\operatorname{Snapshot}\left(B.Node, B.Src\right)\right), T: \operatorname{Snapshot}\left(B.Node, B.Src\right),\\{}\operatorname{NoCollision}\left(B, \operatorname{insert}\left(T, writers\right)\right) \Rightarrow\\{}\forall schedule: B.Node \to \operatorname{List}\left(\operatorname{Op}\left(B.Node, B.Src\right)\right),\\{}(\forall n, W, m, \operatorname{store}\left(W, m\right) \in \operatorname{schedule}\left(n\right) \Rightarrow W \in writers) \Rightarrow\\{}\forall S: \operatorname{Snapshot}\left(B.Node, B.Src\right), n: B.Node, \operatorname{Unaffected}\left(S, T, n\right) \Rightarrow \forall a: B.Art,\\{}\operatorname{run}\left(B, \operatorname{schedule}\left(n\right)\right)(\operatorname{traceKey}\left(B, S, n\right)) = \operatorname{some}\left(a\right) \Rightarrow\\{}\operatorname{cachedBuild}\left(B, \lambda n \mapsto \operatorname{run}\left(B, \operatorname{schedule}\left(n\right)\right), T, n\right) = a.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness.cachedBuild_restores_unaffected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unaffected(S, T, n) holds when n has the same source and the same dependency set in S and T and every dependency is unaffected. By induction along this predicate the from-scratch artifacts of n in S and T coincide.

By the previous theorem the reader's dependency artifacts are the from-scratch artifacts of T, which coincide with those of S on the dependencies of an unaffected module. The key the reader computes for n is therefore the key of n in S, so the lookup returns the stored artifact a and the reader's artifact for n is a: n is restored, not compiled.

Consequently a module the reader compiles is affected, meaning a source or dependency change occurs in its dependency closure, or the consulted cache state lacks the key of that module in S.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness.cachedBuild_eq_build`
- Truth anchor: `D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness.cachedBuild_restores_unaffected`
