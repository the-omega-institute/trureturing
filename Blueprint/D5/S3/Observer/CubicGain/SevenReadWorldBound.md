# Complete Seven-Reading World Bound

## Abstract

Each positive fixed source width admits at most three complete worlds in a guarded literal seven-reading fiber.

A complete original world W=(r,b,d,a) determines P=[[r,b],[r(1-r)/b,1-r]] and the entire polynomial g(s)=a₀+a₁s+a₂s²+a₃s³. Its native domain FullWorld has 0<r<1, b>0 and g nonzero. This is precisely the original positive trace-one rank-one source domain: every c>0 satisfying bc=r(1-r) is the displayed lower-left entry. Ordinary polynomial coefficients are unique, and every nonzero real polynomial of degree at most three occurs.

Let E be either J=[[0,1],[1,0]] or M=[[0,1],[1,1]]. The implementation uses a Boolean e, false for J and true for M. The six actions are J,M,J,M,J,E in chronological order. Starting with Q₀=I, each next product is Qᵢ=EᵢQᵢ₋₁ and each reading is d+g(i)tr(QᵢP). The seven readings use clocks 0 through 6, the same P, the same whole g and the same d. Write F_E(b;A,C,z,Y,p,v) for the set sevenFiber with readings (0,A,C,z,Y,p,v) and the specified source entry b. All observation parameters are real.

Put j=b+r(1-r)/b, T=1+b, U=1+2b and V=1+kb, where k=2 for E=J and k=3 for E=M. The seven literal traces are (1,j,T,j+r,U,j+2r,V). In particular the fifth action here is J. Define K=16TUV, B₀=-dTUV, B₂=(C-d)UV, B₄=(Y-d)TV and B₆=(v-d)TU. Let G₁=5B₀+15B₂-5B₄+B₆, G₃=-B₀+9B₂+9B₄-B₆ and G₅=B₀-5B₂+15B₄+5B₆. Each G is an affine polynomial in d. The polynomial driftPolynomial is H_E=(A-d)G₃G₅-2(z-d)G₁G₅+(p-d)G₁G₃.

The four even rows fix the entire polynomial g by interpolation at 0,2,4,6. They give Kg(1)=G₁, Kg(3)=G₃ and Kg(5)=G₅. The odd rows therefore imply H_E(d)=0 without division by any odd sample. The coefficient of d³ is 16b(1+2b)²(4b³+16b²+5b+8) for J and 192b⁴(3b²+12b+4) for M. These coefficients are positive for every b>0. Thus H_E is a nonzero cubic for every choice of observations.

**Theorem 1.1 (Drift multiplicity pays for every complete world).**

$$\forall E \in \{J,M\}, \forall b,A,C,z,Y,p,v \in \mathbb{R}, b>0, z\neq A \implies \forall S \in \operatorname{Finset}\left(\operatorname{OriginalWorld}\left(\right)\right), S\subseteq\operatorname{F}\left(E, b,A,C,z,Y,p,v\right) \implies \operatorname{D}\left(S\right)\leq\operatorname{R}\left(\operatorname{H}\left(E, b,A,C,z,Y,p,v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SevenReadWorldBound.native_drift_multiset_le_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here S is a finite set of distinct complete worlds, D(S) is the multiset of their drifts with repetitions retained, and R(H_E) is the multiset of real roots of H_E with algebraic multiplicity. The multiset inequality compares the count of each real value, rather than only its presence.

The condition z≠A prevents G₁ and G₃ from both vanishing at a retained drift. If two of G₁,G₃,G₅ are active, their independent affine source traces determine r and j uniquely. At a fixed drift the even rows already determine the whole gain, so this gives one complete world.

If only G₁ is active, j is fixed and the source equation is r²-r+b(j-b)=0. If only G₃ is active, n=j+r is fixed and the source equation is r²-(1+b)r+b(n-b)=0. Each monic quadratic admits at most two distinct sources. In either case the two vanished gain samples and the corresponding observations give (X-d)² dividing H_E. Hence a drift supporting two complete worlds has root multiplicity at least two. A repeated source root contributes one world. Summing these pointwise capacities gives the multiset inequality.

**Theorem 1.2 (Finite complete-world fiber of size at most three).**

$$\forall E \in \{J,M\}, \forall b,A,C,z,Y,p,v \in \mathbb{R}, b>0, z\neq A \implies \operatorname{Finite}\left(\operatorname{F}\left(E, b,A,C,z,Y,p,v\right)\right) \land \lvert\operatorname{F}\left(E, b,A,C,z,Y,p,v\right)\rvert \leq3$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SevenReadWorldBound.seven_read_world_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real-root multiset of a nonzero cubic has total size at most three. Applying the multiset bound to every finite subset of the actual fiber bounds every such subset by three and proves that the whole fiber is finite. This includes the empty fiber.

The result is separate for each fixed b>0 and each E. It imposes no upper bound on b or c and no restriction on the signs, sample zeros, nonsample roots, repeated roots or degree of g beyond being nonzero and of degree at most three. Zero drift is included. It gives no cardinality bound on the union over b and assumes no genericity or bounded source box.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/SevenReadWorldBound.native_drift_multiset_le_roots`
- Truth anchor: `D5/S3/Observer/CubicGain/SevenReadWorldBound.seven_read_world_bound`
- Dependency: [D5/S3/Observer/CubicGain/FullWorldMeanSpan](FullWorldMeanSpan.md)
