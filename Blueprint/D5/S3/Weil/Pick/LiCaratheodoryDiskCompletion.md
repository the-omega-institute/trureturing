# Li-Caratheodory Disk Completion

## Abstract

The Li-Caratheodory identity carries its Mobius disk geometry and unit normalization.

**Theorem 1.1 (The normalized identity includes its disk half-plane map).**

$$\begin{gathered}\forall lambda: \mathbb{N} \to \mathbb{R},\\{}(\left(lambda\left(0\right) = 0 \land 0 < lambda\left(1\right)\right) \land \operatorname{Eventually}\left((z: \mathbb{C} \mapsto \operatorname{HasSum}\left((n: \mathbb{N} \mapsto \operatorname{complexCast}\left(lambda\left(n + 1\right)\right) \cdot z^{n}), \frac{\operatorname{logDeriv}\left(xiReading, \frac{1}{1 - z}\right)}{\left(1 - z\right)^{2}}\right)), \operatorname{nhds}\left(\operatorname{complex}\left(0\right)\right)\right)) \Rightarrow\\{}\operatorname{let} liCaratheodory: \mathbb{C} \to \mathbb{C} := (z: \mathbb{C} \mapsto 1 + 2 \cdot \sum_{n\in \mathbb{N}} \frac{\operatorname{complexCast}\left(lambda\left(n + 2\right)\right) - 2 \cdot \operatorname{complexCast}\left(lambda\left(n + 1\right)\right) + \operatorname{complexCast}\left(lambda\left(n\right)\right)}{2 \cdot \operatorname{complexCast}\left(lambda\left(1\right)\right)} \cdot \operatorname{pow}\left(z, n + 1\right)),\\{}\operatorname{let} continuation: \mathbb{C} \to \mathbb{C} := (z: \mathbb{C} \mapsto \frac{1}{\operatorname{complexCast}\left(lambda\left(1\right)\right)} \cdot \operatorname{logDeriv}\left(xiReading, \frac{1}{1 - z}\right)),\\{}\left(\left(\operatorname{EventuallyEq}\left(\operatorname{nhds}\left(\operatorname{complex}\left(0\right)\right), liCaratheodory, continuation\right) \land \operatorname{MeromorphicOn}\left(continuation, \mathbb{C} \setminus \{1\}\right)\right) \land \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \frac{1}{2} < \operatorname{realPart}\left(\frac{1}{1 - z}\right)\right)\right) \land liCaratheodory\left(0\right) = 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LiCaratheodoryDiskCompletion.li_caratheodory_disk_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient carrier and local generating law are exactly those of the frozen Li identity. The public conclusion retains its local equality and meromorphic continuation.

A direct norm-square calculation shows that the Mobius argument has real part greater than one half throughout the open unit disk. The constructed normalized series also equals one at zero.

## References

- Truth anchor: `D5/S3/Weil/Pick/LiCaratheodoryDiskCompletion.li_caratheodory_disk_completion`
- Dependency: [D5/S3/Weil/TestFunctions/LiCaratheodoryIdentity](../TestFunctions/LiCaratheodoryIdentity.md)
