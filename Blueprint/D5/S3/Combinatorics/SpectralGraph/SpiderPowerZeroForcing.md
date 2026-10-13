# Zero forcing powers of equal-legged spiders

## Abstract

The ordinary kth power of the equal-legged spider has zero forcing number (m-1)k.

**Definition 1.1 (All original vertices).**

$$\forall m \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \operatorname{Vertex}\left(m, l\right) = \operatorname{Option}\left(\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(l\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.Vertex` (`✓ std3`).

*Citation.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The vertex type has a center none and m legs with l vertices each. The vertex some(a,i) has source leg label a+1 and depth i+1, with zero-based Fin indices. Its cardinality is ml+1.

**Definition 1.2 (Distances in the source tree).**

$$\forall m \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \operatorname{distance}\left(\operatorname{none}\left(\right), \operatorname{none}\left(\right)\right) = 0 \land \left(\left(\forall a \in \operatorname{Fin}\left(m\right),\; \forall i \in \operatorname{Fin}\left(l\right),\; \operatorname{distance}\left(\operatorname{none}\left(\right), \operatorname{some}\left((a,i)\right)\right) = i+1 \land \operatorname{distance}\left(\operatorname{some}\left((a,i)\right), \operatorname{none}\left(\right)\right) = i+1\right) \land \left(\forall a \in \operatorname{Fin}\left(m\right),\; \forall b \in \operatorname{Fin}\left(m\right),\; \forall i \in \operatorname{Fin}\left(l\right),\; \forall j \in \operatorname{Fin}\left(l\right),\; \operatorname{distance}\left(\operatorname{some}\left((a,i)\right), \operatorname{some}\left((b,j)\right)\right) = \operatorname{ite}\left(a = b, \operatorname{NatDist}\left(i, j\right), i+j+2\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.distance` (`✓ std3`).

*Citation.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The center-to-leg distance is depth, same-leg distance is the absolute depth difference, and different-leg distance is the sum of depths. NatDist is the natural absolute difference. These are the three unique-path distances in the spider of section 3.

**Definition 1.3 (The ordinary graph power).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall u \in \operatorname{Vertex}\left(m, l\right),\; \forall v \in \operatorname{Vertex}\left(m, l\right),\; \operatorname{Adj}\left(\operatorname{power}\left(m, k, l\right), u, v\right) \Leftrightarrow \left(u \ne v \land \operatorname{distance}\left(u, v\right) \le k\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.power` (`✓ std3`).

*Citation.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The power joins distinct vertices at distance at most k. It retains the center and every leg vertex and has no loops. Ordinary forcing uses the existing Black, IsZeroForcing and zeroForcingNumber definitions: a black source with exactly one white neighbor forces that neighbor.

**Theorem 1.4 (Conjecture 10).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \left(2 \le m \land \left(1 \le k \land k+1 \le l\right)\right) \Rightarrow \operatorname{zeroForcingNumber}\left(\operatorname{power}\left(m, k, l\right)\right) = (m-1) \times k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result` (`✓ std3`). ∎

*Resolves.* `Problems/abiad-equal-legged-spider-power-zero-forcing` (proved) by `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abiad-equal-legged-spider-power-zero-forcing","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For every m at least two, k at least one and l at least k+1, the ordinary zero forcing number is (m-1)k. The same statement includes m=2, k=1 and l=k+1, including their simultaneous boundary case.

For a leg of size n>=1 and an order 0<=r<n, let B have diagonal n-1, upper entry B(i,i+1)=n-1-i and lower entry B(i+1,i)=i+1. Rectangular factors C and D satisfy CD=B and DC=B of size n-1 plus 2I. The recursion P(0,A)=I and P(r+1,A)=(A-2rI)P(r,A) gives P(r,B)=QR with Q of shape n by n-r and R of shape n-r by n. Both factors have nonnegative entries, and their positive entries occupy the intervals a through a+r. Therefore P(r,B)(i,j) is positive exactly when the absolute difference of indices is at most r. Rank-nullity gives dimension ker R at least r, and QR annihilates ker R.

Place these B blocks on the original legs. Give the center diagonal the common parameter t, and give each center-to-first-vertex entry and its reverse the value one. The resulting matrix A(t) is generally nonsymmetric. For W=ker P(k,B), take the subspace of W to the mth power consisting of leg vectors whose sum is zero. Its dimension is at least (m-1)dim W. Appending center coordinate zero injects it into ker P(k,A(t)): the sum cancels the center row and the leg rows intertwine with B. Thus the full matrix has kernel dimension at least (m-1)k for every t.

For 0<=r<ell, work over rational polynomials in t and subtract the constant diagonal leg block from P(r,A). If a center correction has row and column depths d and e, its coefficient of order s vanishes when r<d+e+s and is positive when r=d+e+s. This follows inductively: the center row supplies one extra power of t, and a leg row has exactly one inward neighbor with a positive coefficient. At the constant boundary the center row receives the positive leg-band entry. Outside the kth power both the constant leg block and the correction vanish. Inside it, either the positive constant leg entry remains, or the correction has a positive leading coefficient. When d+e=k, both constant contributions are nonnegative and the correction is positive, so cancellation cannot occur.

Multiply the finitely many nonzero polynomials for ordered edges. A nonzero polynomial of degree d cannot vanish at all d+1 distinct natural numbers viewed as rationals, so one common natural t avoids every edge zero simultaneously. Nonedges are zero independently of t. This produces the same rational matrix with exact off-diagonal support and the proved kernel dimension.

Alon's arbitrary-field row-kernel argument applies to this nonsymmetric matrix. A kernel vector vanishing on an ordinary forcing set vanishes at every Black derivation: in a force row the black source and all other neighbors already have coordinate zero, leaving one nonzero edge coefficient times the target coordinate. Restriction of the kernel to the initial set is injective, hence every such set has cardinality at least (m-1)k. No theorem about symmetric maximum nullity is used.

Proposition 9 supplies the matching upper chronology. Initially color the last k vertices of the first m-1 legs. Descending along each selected leg, depth t+k forces depth t. Then depth k on the first leg forces the center; its depths k-j force depths j on the last leg for 1<=j<k; the center forces depth k there. Finally depth t-k on the last leg forces depth t. All sources are black and all competing neighbors are black. Taking the natural infimum of forcing-set cardinalities yields the equality.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.Vertex`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.distance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.power`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree](../GeneralizedPetersen/ZeroForcingThree.md)
