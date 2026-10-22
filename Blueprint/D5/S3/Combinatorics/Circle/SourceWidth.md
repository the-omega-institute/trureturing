# A universal support width for centered circle sources

## Abstract

Every centered doubling source of length k at least three has one complete physical-label permutation whose every prefix lies between zero and N minus floor(N/3) minus two.

**Definition 1.1 (The original odd modulus).**

$$\forall k \in \mathrm{Nat},\; \operatorname{modulus}\left(k\right) = 2^{k} - 1$$

*Formalization.* `D5/S3/Combinatorics/Circle/SourceWidth.modulus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer modulus is N = 2^k - 1. The width theorem assumes k at least three, so N is at least seven.

**Definition 1.2 (Centered residues).**

$$\forall N \in \mathrm{Int},\; \forall x \in \mathrm{Int},\; \operatorname{centered}\left(N, x\right) = \operatorname{emod}\left(x + \operatorname{ediv}\left(N, 2\right), N\right) - \operatorname{ediv}\left(N, 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Circle/SourceWidth.centered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Division and remainder are integer Euclidean operations. For positive odd N this selects the unique congruent integer in [-floor(N/2), floor(N/2)].

**Definition 1.3 (All physical source occurrences).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall p \in \operatorname{Fin}\left(k\right),\; \operatorname{actualSource}\left(k, t, p\right) = \operatorname{centered}\left(\operatorname{modulus}\left(k\right), 2^{\operatorname{val}\left(p\right)} \cdot t\right)$$

*Formalization.* `D5/S3/Combinatorics/Circle/SourceWidth.actualSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The position p in Fin(k) is the physical label. Equal values at different positions remain different occurrences. The natural parameter t is unrestricted; reduction modulo N includes zero, nonunits and sources whose least period is smaller than k.

**Definition 1.4 (The support capacity).**

$$\forall k \in \mathrm{Nat},\; \operatorname{capacity}\left(k\right) = \operatorname{modulus}\left(k\right) - \operatorname{ediv}\left(\operatorname{modulus}\left(k\right), 3\right) - 2$$

*Formalization.* `D5/S3/Combinatorics/Circle/SourceWidth.capacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Writing A = floor(N/3), the capacity is B = N - A - 2. For k at least three, A is at least two and N is either 3A or 3A+1.

**Theorem 1.5 (One complete word with every height in the support strip).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; 3 \le k \Rightarrow \left(\exists word \in \operatorname{List}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{Nodup}\left(word\right) \land \left(\operatorname{toFinset}\left(word\right) = \mathrm{univ} \land \left(\forall n \in \mathrm{Nat},\; n \le k \Rightarrow \left(0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, word\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, word\right)\right)\right) \le \operatorname{capacity}\left(k\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SourceWidth.universal_source_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least three and every natural t, there is one list word of distinct Fin(k) labels containing all labels. For each n from zero through k, the sum of its first n actual source values is in the closed integer interval [0,B]. The interval membership in Lean is exactly the conjunction of the two displayed inequalities. No zero-sum, packet partition, compatible boundary vector or generic source property is assumed by this theorem.

The centered arithmetic gives the strict source successor: 2s when 4|s| < N, 2s-N when 4s > N, and 2s+N when 4s < -N. Odd N excludes both half endpoints. With epsilon equal to one for negative s and zero otherwise, u = s + N epsilon satisfies u_next-u = s. The code retains this potential identity and the original successor in SourcePath. The congruence 2^k = 1 modulo N closes the path on the original k physical labels. Telescoping gives the original cyclic sum zero; no successor relation is applied to contracted nets.

A large label has |s| > A. Its immediate successor has the opposite sign and magnitude b = N-2|s| in [1,A]. Between this parent and the next large label, two consecutive small values must be related by doubling. The only exception could be N=3A and a value equal to A or -A. That exceptional orbit remains trapped in the alternating pair, so it cannot occur on a path ending at a large label. Thus the entire original arc consists of one large parent followed by an opposite dyadic ladder b,2b,... . Cutting the retained label list at the first next large label partitions it into full physical arcs; recursion consumes every arc, including zero-net arcs and arcs crossing the original seam.

At every large parent the same original unsigned potential lies in [A+1,N-A-1]. Choose one physical large label minimizing u and rotate the complete original cycle to that label. Every arc starts at h = u_parent-u_min and ends at the next such height. These are one common boundary vector, of width at most N-2A-2. An arc's total is exactly its endpoint potential difference, so an internal reordering creates no offset at the next join.

For a positive parent a and a negative ladder of length j and total magnitude S=(2^j-1)b, put n=min(2^j-1,floor(h/b)). Select the original ladder labels indicated by the binary digits of n before the parent, and place the complementary labels after it. The recursive binary selection returns both lists together with a permutation proof and selected mass nb; it never replaces physical labels by distinct numerical values. Before the parent, heights decrease from h to h-nb. Afterwards they decrease from h-nb+a to the original endpoint h+a-S. If h is at least S, the peak is that endpoint. Otherwise 0 <= h-nb <= b-1, so the peak is at most a+b-1. Because a>A, this is N-a-1 <= B. Negative parents use the same construction at reflected height B-h. The two actual endpoints and this one capacity inequality control every intermediate height for either sign or zero arc net.

If no large label exists, take a label of maximum magnitude m. If m is zero, every source value is zero. Otherwise an inner successor would have magnitude 2m, contradicting maximality. An outer successor forces N <= 3m <= 3A <= N, hence N=3A and m=A. The deterministic original path is then trapped in the alternating values A and -A. Its unsigned potentials lie in [A,2A]; rotating at a minimum potential gives all heights in [0,A], which is contained in [0,B]. This retains all repeated occurrences and covers zero within the universal quantifiers.

The external target is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. That conjecture requests C=(N-1)/2 for every positive k. The theorem here is a separate repository development of the support bound B for k>=3; it makes no literature-novelty claim and does not settle the full conjecture or its preregistration #20057. For k>=4, B>C, and the all-source capacity-C gap remains open. The k=1 and k=2 boundary cases are outside this theorem.

**Theorem 1.6 (Exact width after relocating the low physical labels).**

$$\forall r \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(1 \le r \land \left(1 \le m \land 1 \le d\right)\right) \Rightarrow \left(\operatorname{Perm}\left(\operatorname{append}\left(\operatorname{rotate}\left(\operatorname{take}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right), d - 1\right), \operatorname{drop}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right)\right), \operatorname{finRange}\left(r \cdot m + d\right)\right) \land \left(2^{r \cdot m + d - 1} - 1 - \operatorname{min}\left(2^{d - 1} - 1, \operatorname{ediv}\left(\operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right) - 1, 2\right)\right) \le 2^{r \cdot m + d - 1} - 1 \land \left(\left(\forall n \in \mathrm{Nat},\; 0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r \cdot m + d, \operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right)\right), \operatorname{take}\left(n, \operatorname{append}\left(\operatorname{rotate}\left(\operatorname{take}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right), d - 1\right), \operatorname{drop}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right)\right)\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r \cdot m + d, \operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right)\right), \operatorname{take}\left(n, \operatorname{append}\left(\operatorname{rotate}\left(\operatorname{take}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right), d - 1\right), \operatorname{drop}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right)\right)\right)\right)\right) \le 2^{r \cdot m + d - 1} - 1 - \operatorname{min}\left(2^{d - 1} - 1, \operatorname{ediv}\left(\operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right) - 1, 2\right)\right)\right) \land \left(\operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r \cdot m + d, \operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right)\right), \operatorname{append}\left(\operatorname{rotate}\left(\operatorname{take}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right), d - 1\right), \operatorname{drop}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right)\right)\right)\right) = 0 \land \left(\exists n \in \mathrm{Nat},\; n \le r \cdot m + d \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(r \cdot m + d, \operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right)\right), \operatorname{take}\left(n, \operatorname{append}\left(\operatorname{rotate}\left(\operatorname{take}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right), d - 1\right), \operatorname{drop}\left(r \cdot m + d - 1, \operatorname{finRange}\left(r \cdot m + d\right)\right)\right)\right)\right)\right) = 2^{r \cdot m + d - 1} - 1 - \operatorname{min}\left(2^{d - 1} - 1, \operatorname{ediv}\left(\operatorname{ediv}\left(\left(2^{m}\right)^{r} - 1, 2^{m} - 1\right) - 1, 2\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SourceWidth.geometric_source_relocation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r,m,d be arbitrary positive naturals, B=2^m, k=rm+d and t=(B^r-1)/(B-1), with the quotient taken in the naturals. Put a=d-1, A=2^a, C=2^(k-1)-1 and W=C-min(A-1,(t-1)/2), with integer subtraction and Euclidean division in the width. The literal word rotates the first k-1 entries of finRange(k) by a and appends its last entry. Thus its labels are a,...,k-2,0,...,a-1,k-1. It is a permutation of the original Fin(k) labels. Every natural-length prefix, including saturated takes beyond k, has integer sum in [0,W], the total is zero, W<=C, and some prefix of length at most k attains W. This includes r=1, m=1, d=1, their intersections and the empty low block.

Multiplication by two on residues modulo N=2^k-1 is a cyclic action because 2^k=1 modulo N. Each original label retains its position in that action even when values coincide. The unsigned representative U_i=s_i+N when the centered source s_i is negative, and U_i=s_i otherwise, is an integer potential: U_(i+1)-U_i=s_i, including the last-to-first edge. Contiguous physical sums therefore telescope in the integers; a modular relation alone would not control their heights.

The geometric quotient equals the r-term sum of powers of B. Write L_j=sum_(e<j) B^e and u_j=2At-(2A-1)L_j. The exact source identity 2^(jm+d)t=N L_j+u_j, together with representative range checks, gives the negative-label representatives at nu_j=a+jm for 1<=j<=r. The nonfinal returns satisfy At<=u_j<=2At, and all intervening powers of two remain in the same full physical envelope At<=U_i<=ABt for a<=i<=k-1. Its upper endpoint is attained at i=a+m; the last unsigned and centered representatives are (N+t)/2 and (t-N)/2. These bounds are derived from the source, with no annulus, unit, distinctness or true-period hypothesis.

The main block has heights U_(a+n)-At and attains M=ABt-At=C-(A-1) at n=m. Reinserting the low labels adds only nonnegative actual increments, ending at L=C-(t-1)/2 at n=k-1. The final physical label returns to zero. Both M and L are visited, so their maximum is exactly W. This is the attained width of the displayed word; no minimum over all permutations or global optimality is claimed.

The source reference is Damasdi–Frankl–Pach–Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. This symbolic family construction is repository-derived and makes no literature-novelty claim. The earlier ThreeParentFamily sources form the sign-and-rotation subfamily r=3,m=2,d=R-2 for R>=4: modulo N, -2^(R-1)*21 equals 11*2^(R-1)-1. Their sources overlap; their schedules and optimality statements are not identified here. The full arbitrary-source Conjecture 3.1 remains open. No unit-cycle, girth or full-demand conclusion outside this source family is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.actualSource`
- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.capacity`
- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.centered`
- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.geometric_source_relocation`
- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.modulus`
- Truth anchor: `D5/S3/Combinatorics/Circle/SourceWidth.universal_source_width`
