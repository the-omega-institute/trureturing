# Greathouse's bound for zero-XOR enders

## Abstract

Every least zero-XOR ender satisfies Greathouse's sharp five-thirds bound.

**Definition 1.1 (Increasing zero-XOR sequences).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \operatorname{HasZeroXorSequence}\left(n, m\right) = (\exists (bs : \operatorname{List}\left(\mathbb{N}\right)), (\operatorname{List}.\operatorname{Pairwise}\left(\operatorname{fun} (a : \mathbb{N}) \mapsto \operatorname{fun} (b : \mathbb{N}) \mapsto a < b, bs\right)) \land ((bs \ne []) \land ((\operatorname{List}.\operatorname{headD}\left(bs, 0\right) = n) \land ((\operatorname{List}.\operatorname{getLastD}\left(bs, 0\right) = m) \land (\operatorname{List}.\operatorname{foldr}\left(\operatorname{fun} (a : \mathbb{N}) \mapsto \operatorname{fun} (b : \mathbb{N}) \mapsto \operatorname{HXor}.\operatorname{hXor}\left(a, b\right), 0, bs\right) = 0)))))$$

*Formalization.* `D5/S3/Arith/Additive/GreathouseA359506XorBound.HasZeroXorSequence` (`✓ std3`).

*Citation.* Peter Kagey; Charles R. Greathouse IV (2023). *OEIS A359506: least enders of increasing zero-XOR sequences*. URL: <https://oeis.org/A359506/internal>.

*Commentary.*

OEIS A359506, revision 41, NAME (unpaginated): “a(n) is the least integer m such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = m with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.” The carrier is the natural numbers, including zero. List.Pairwise with strict order states that every earlier entry is smaller. The list is nonempty, and List.headD and List.getLastD with default zero specify both endpoints. List.foldr of HXor.hXor, the natural bitwise XOR operation, starts at zero.

**Definition 1.2 (The least ender predicate).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \operatorname{IsLeastEnder}\left(n, m\right) = ((\operatorname{HasZeroXorSequence}\left(n, m\right)) \land (\forall (m' : \mathbb{N}), (\operatorname{HasZeroXorSequence}\left(n, m'\right)) \Rightarrow (m \le m')))$$

*Formalization.* `D5/S3/Arith/Additive/GreathouseA359506XorBound.IsLeastEnder` (`✓ std3`).

*Citation.* Peter Kagey; Charles R. Greathouse IV (2023). *OEIS A359506: least enders of increasing zero-XOR sequences*. URL: <https://oeis.org/A359506/internal>.

*Commentary.*

IsLeastEnder combines the zero-XOR endpoint predicate with the universal comparison that every other ender is at least the selected endpoint.

**Definition 1.3 (The five-thirds claim).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), \exists (m : \mathbb{N}), (\operatorname{IsLeastEnder}\left(n, m\right)) \land (3 \cdot m \le 5 \cdot (n + 1)))$$

*Formalization.* `D5/S3/Arith/Additive/GreathouseA359506XorBound.claim` (`✓ std3`).

*Citation.* Peter Kagey; Charles R. Greathouse IV (2023). *OEIS A359506: least enders of increasing zero-XOR sequences*. URL: <https://oeis.org/A359506/internal>.

*Commentary.*

OEIS A359506, revision 41, FORMULA (unpaginated): “For n > 1, a(n) >= n + 3. a(4n) = 4n + 3 for n > 0. Conjecture: a(n) <= 5(n+1)/3. - Charles R Greathouse IV, Jan 12 2023” For every natural n, a least ender exists. Its inequality is written with integer coefficients: 3m ≤ 5(n+1). The universal comparison ranges over all possible natural enders, so minimum existence is explicit.

**Theorem 1.4 (The five-thirds bound).**

$$\forall (n : \mathbb{N}), \exists (m : \mathbb{N}), (\operatorname{IsLeastEnder}\left(n, m\right)) \land (3 \cdot m \le 5 \cdot (n + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/GreathouseA359506XorBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey; Charles R. Greathouse IV (2023). *OEIS A359506: least enders of increasing zero-XOR sequences*. URL: <https://oeis.org/A359506/internal>.

*Commentary.*

Write n+1 as a power of two times an odd number. An odd factor at least three gives a four-term zero-XOR sequence. A power of two gives a three-term sequence. Projecting XOR to the high binary blocks excludes every smaller ender. The singleton list containing zero handles n=0. The two resulting exact minimum formulas imply the bound; n=3·2^s−1 attains equality.

## References

- Truth anchor: `D5/S3/Arith/Additive/GreathouseA359506XorBound.HasZeroXorSequence`
- Truth anchor: `D5/S3/Arith/Additive/GreathouseA359506XorBound.IsLeastEnder`
- Truth anchor: `D5/S3/Arith/Additive/GreathouseA359506XorBound.claim`
- Truth anchor: `D5/S3/Arith/Additive/GreathouseA359506XorBound.result`
- Dependency: [D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA](../../../S0/Certificates/Games/EllisThanatipanondaCutFamilyA.md)
