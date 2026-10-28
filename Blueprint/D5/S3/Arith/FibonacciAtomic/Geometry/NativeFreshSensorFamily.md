# Independent persistent native sectors

## Abstract

Disjoint original beta cherries carry independent rational period-two sectors invisible at every designated observation time.

**Theorem 1.1 (Terminal and designated support on arbitrary native contexts).**

$$\forall t: \operatorname{Source}\left(\right), (\forall p: \operatorname{Address}\left(\right), ((\operatorname{subtree}\left(p, t\right) = \operatorname{some}\left(\operatorname{mul}\left(\operatorname{beta}\left(\right), \operatorname{beta}\left(\right)\right)\right)) \Rightarrow ((\forall q: \operatorname{Address}\left(\right), ((q \in \operatorname{terminals}\left(\operatorname{grown}\left(t\right)\right)) \Rightarrow (\operatorname{coordinate}\left(\operatorname{half}\left(p\right), q\right) = 0))) \land ((\forall q: \operatorname{Address}\left(\right), ((q \in \operatorname{sensors}\left(t\right)) \Rightarrow (\operatorname{coordinate}\left(\operatorname{half}\left(p\right), q\right) = 0))) \land (\forall q: \operatorname{Address}\left(\right), ((q \in \operatorname{sensors}\left(t\right)) \Rightarrow (\operatorname{coordinate}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right), \operatorname{half}\left(p\right)\right), q\right) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily.designated_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original beta cherry, half vanishes at all current terminals and all designated sensors; its native adjacency update also vanishes at every designated sensor. Embedding through the actual original context proves these assertions for every ambient terminal and sensor.

**Theorem 1.2 (Every rational parameter and every natural time).**

$$\forall t: \operatorname{Source}\left(\right), (\forall k: \mathbb{N}, (\forall ch: \operatorname{Cherries}\left(t, k\right), ((\operatorname{Injective}\left(\operatorname{H}\left(ch\right)\right)) \land ((\forall theta: \operatorname{Fin}\left(k\right) \to \mathbb{Q}, (\operatorname{apply}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), \operatorname{apply}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), \operatorname{H}\left(ch, theta\right)\right)\right) = \operatorname{H}\left(ch, theta\right))) \land ((\forall theta: \operatorname{Fin}\left(k\right) \to \mathbb{Q}, (\forall j: \mathbb{N}, (\forall q: \operatorname{Address}\left(\right), ((q \in \operatorname{sensors}\left(t\right)) \Rightarrow (\operatorname{coordinate}\left(\operatorname{iterate}\left(\operatorname{adjacency}\left(\operatorname{grown}\left(t\right)\right), j, \operatorname{H}\left(ch, theta\right)\right), q\right) = 0))))) \land (\forall theta: \operatorname{Fin}\left(k\right) \to \mathbb{Q}, (\forall q: \operatorname{Address}\left(\right), ((q \in \operatorname{terminals}\left(\operatorname{grown}\left(t\right)\right)) \Rightarrow (\operatorname{coordinate}\left(\operatorname{H}\left(ch, theta\right), q\right) = 0)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily.persistent_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cherries(t,k) records k literal beta cherries in the original finite Source and disjoint full address cones: for distinct indices i,j, root(i)++p differs from root(j)++q for every pair of suffixes p,q. This is disjointness of native logical cones. H(theta) is the finite sum of theta(i) times half(root(i)). Its coordinate at root(i)L is theta(i)/2, proving injectivity over all rational parameters. Each summand and its first update vanish at every designated sensor. Period two proves invisibility for every natural time, including zero. Every current terminal of grown(t) has zero value in H(theta). The first update may be visible at nondesignated terminals; designated blindness does not assert full-service equality. The native fresh-zero entrance generally differs from H(theta), and no acquisition of this sector is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily.designated_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily.persistent_family`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector](NativeFreshSensorSector.md)
