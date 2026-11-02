# Exact growth from finite rank-one fibers

## Abstract

Finite rank-one relation fibers determine Lee-ball images, maximum-pair growth and the full odd asymmetric quotient family with exact diameter.

**Theorem 1.1 (A nonzero displacement controls arbitrarily long finite fibers).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Write Dᵣ={(x,y)∈Z²: |x|+|y|≤r}. Let f:Z²→G be additive for an arbitrary additive commutative group G, and let h=(h₁,h₂)≠0 satisfy f(h)=0. Assume every kernel vector of Lee norm at most 2r is an integer multiple of h. Set A=max(0,2r+1−|h₁+h₂|) and B=max(0,2r+1−|h₁−h₂|). Then |f(Dᵣ)|+⌊(AB+1)/2⌋=2r²+2r+1. The integer positive parts in A and B are taken before converting to natural numbers. Either width may vanish. There is no finiteness or surjectivity condition on G or f, no primitivity or sign condition on h, and no additional radius restriction.

All points in a fiber inside Dᵣ differ by integer multiples of h, because the difference of two diamond points has Lee norm at most 2r. Integer norm interpolation shows that the admissible multiples form a finite interval: if y−x=k h with k>0, then k(y−h)=(k−1)y+x, so the triangle inequality and homogeneity force y−h back into Dᵣ. Remove Cᵣ=Dᵣ∩(Dᵣ+h), retaining Rᵣ=Dᵣ∖Cᵣ. A retained point is the bottom of its fiber in the h direction. If two retained points share an image, a positive multiple forces the later one into Cᵣ; a negative multiple swaps their roles. Thus f is injective on Rᵣ even when a fiber has many points.

For surjectivity choose, in each nonempty finite fiber, a point w minimizing w·h. A point of Cᵣ has w−h in the same fiber, with dot product lower by h₁²+h₂²>0. A minimizer therefore survives the trimming. This finite minimum replaces a one-step deletion argument and requires neither a primitive displacement nor a bound on fiber length. Consequently Rᵣ maps bijectively onto f(Dᵣ), and |f(Dᵣ)|+|Cᵣ|=|Dᵣ|.

Under S(x,y)=(x+y,x−y), Cᵣ is the equal-parity part of the product of two integer intervals. The interval for t=h₁+h₂ or h₁−h₂ is [max(−r,t−r),min(r,t+r)], with width max(0,2r+1−|t|). Equal-parity coordinates have the integral inverse ((u+v)/2,(u−v)/2). In each interval the parity of r occurs ⌈width/2⌉ times and the other parity ⌊width/2⌋ times; for odd positive widths the initial endpoint has the parity of r, for either sign of t. The existing residue-count and filtered-product cardinality suppliers give |Cᵣ|=⌈A/2⌉⌈B/2⌉+⌊A/2⌋⌊B/2⌋=⌊(AB+1)/2⌋, including empty intervals. The inherited two-parity LeeCode gives |Dᵣ|=(r+1)²+r². These counts combined with the fiber bijection prove the balance.

**Theorem 1.2 (A finite transversal in an arbitrary additive target).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Write Dᵣ={(x,y)∈Z²: |x|+|y|≤r}. Let f:Z²→G be additive, where G is any additive commutative group, let B>0 and r<2B be natural numbers, and set h=(0,2B). Assume f(h)=0 and every relation z of Lee norm at most 2r is 0, h or −h. Then the finite image f(Dᵣ) has cardinality 2r²+2r+1 for r<B and 2B(2r−B+1) for B≤r. The target need not be finite and f need not be surjective.

This axial API is a specialization of the preceding balance, with h=(0,2B). Its three allowed short relations 0,h,−h are mapped to the multiples 0•h,1•h,(−1)•h. Both rectangle widths are max(0,2r+1−2B). For r<B the cap is empty. Otherwise its cardinality is 2(r−B)²+2(r−B)+1, and the balance gives 2B(2r−B+1). Geometrically max(|y|,|y−2B|)=B+|y−B| also identifies the overlap with (0,B)+Dᵣ₋ᴮ. The shared finite-fiber theorem supplies the actual proof; no separate axial trimming argument is needed. The original radius premise is retained in this public API and supplied by the actual maximum-pair consumer below.

**Theorem 1.3 (Every actual composite maximum pair has the same ball growth).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.sharp_pair_growth`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.sharp_pair_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let s≥3 be natural, n=2s+1 composite, p its least prime factor, and B=(n−p)/2. The inherited parameter theorem supplies n=p(2t+1) with t≥1, so B=pt and A=p(t+1). Let G be a finite noncyclic additive commutative group in any universe, with distinct a,b, signed radius-s cover by a,b, and Nat.card G=MaximumOrder(s). For every natural r≤s, the signed Cayley ball {x•a+y•b: |x|+|y|≤r} has cardinality 2r²+2r+1 for r<B and 2B(2r−B+1) for B≤r. These hypotheses concern the actual pair; they do not select a particular model group or marking.

For the actual coefficient map, Smith normal form supplies one common divisor c≥2 together with containment of its relation kernel K in cZ². Its actual index is Nat.card G. Since p²≤n, the maximum order is greater than 2s². The inherited lattice upper bound therefore forces odd c dividing n and c²≤p². The least-factor inequality gives p≤c, so c=p. Keeping this same containment is essential for the compression that follows.

Apply S(x,y)=(x+y,x−y), put M=S(K), and let L={z:pz∈M}. The inherited square lift, residue rectangle and scaled-index laws show that L covers the square of side m=n/p and has actual index m²−1. NearSquareLatticeRigidity.near_square_rigidity at deficit one forces its two displacement parameters to be one. Its basis is (m,−ε),(−1,εm), with ε=±1. Taking integral preimages in the original S-image gives the two diagonal relations and, for every kernel vector, coordinates (A(u−v),B(u+v)), or the coordinate swap. No marked-group isomorphism is needed.

Here A+B=2s+1, A−B=p≥3, and s<2B. A nonzero first coordinate in the displayed diagonal form costs at least A+B or 2A, both greater than 2s. With first coordinate zero, the second coordinate is a multiple of 2B; every multiple beyond ±2B costs at least 4B>2s. Consequently the only possible short nonzero relations are (0,±2B), or their swaps, and the corresponding relation is actually present. Coordinate swap preserves Dᵣ. Applying the preceding general counting theorem therefore proves the ball formula for every r≤s.

Consecutive nested balls yield sphere sizes without an additional assertion: sphere zero has size one; for 1≤r≤s the size is 4r when r<B, 4B−1 when r=B, and 4B when r>B. At r=B exactly one pair is identified. At r=s the second branch is 2AB=Nat.card G, as required by the cover. The radius restriction is essential: the known s=4 product ZMod 3×ZMod 12 is already exhausted at radius four, so radius five has 36 points whereas the extended expression would give 48.

Bajnok–Beatty arXiv:2406.04045v1 supplies the Cayley-diameter problem and the known lower families, not an attribution of the cap-transversal proof to that source. BajnokBeattyFiniteUpper, LeeSquareCompression, NearSquareLatticeRigidity and BajnokBeattySharpMaximum supply the kernel containment, compression, rigidity, maximum and nontruncating arithmetic used in this derivation. This is a formal consequence of those inputs with the finite-fiber counting mechanism above; no current-literature priority or novelty is asserted.

**Theorem 1.4 (The full odd asymmetric lattice family has exact growth and diameter).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.asymmetric_quotient_growth`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.asymmetric_quotient_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let p,m,a,b be odd integers with p≥3 and 0<a,b<m. In Z² put v₁=(p(m−a)/2,p(m+a)/2), v₂=(p(m−b)/2,−p(m+b)/2), K=Zv₁+Zv₂ and G=Z²/K. The halves are integral. Let F be the canonical quotient map, let f(x,y)=F(x,y) under the standard identification with integer pairs, and put s=(pm−1)/2. Then G is finite and noncyclic, with |G|=p²(m²−ab)/2. For every natural r≤s, put wₐ=2r−p(m−a)+1 and wᵦ=2r−p(m−b)+1. The exact identity is |f(Dᵣ)|+⌊(max(0,wₐ)max(0,wᵦ)+1)/2⌋=2r²+2r+1. The positive parts are taken in the integers before conversion to natural numbers.

The same quotient map F covers at radius s and fails to cover at radius s−1. More precisely, for every natural R, LeeCovers(F,R) holds exactly when s≤R. Thus s is the signed Cayley diameter for the coordinate images F(1,0),F(0,1). All conclusions refer to this actual quotient and this same pair. No primality assumption on p is used, and no condition comparing 2min(a,b) with m is needed.

The map S(x,y)=(x+y,x−y) sends v₁ to (pm,−pa) and v₂ to (−pb,pm). Hence the Lee norm of q₁v₁+q₂v₂ is p max(|mq₁−bq₂|,|−aq₁+mq₂|). If q₁,q₂ are nonnegative and unequal, the larger coefficient exceeds the smaller by at least one; the corresponding coordinate has absolute value at least m, because m−a and m−b are positive. Simultaneous negation handles two nonpositive coefficients. For opposite signs the terms add in absolute value, and a nonzero integer coefficient supplies the same lower bound. Unequal coefficients therefore cost at least pm in Lee norm.

For r≤s, a relation of norm at most 2r has norm at most pm−1. Its coefficients must coincide, so it is an arbitrary integer multiple of h=v₁+v₂. The vector h is nonzero and lies in K; S(h)=(p(m−b),p(m−a)). The rank-one displacement theorem above applies directly. Its two rectangle widths are precisely the positive parts of wᵦ and wₐ. This argument includes fibers of arbitrary finite length; it does not reduce the relations to 0,h,−h.

The determinant is −p²(m²−ab)/2 and is nonzero since ab<m². The existing two-vector index theorem identifies its absolute value with |G|, giving finiteness. Every coordinate of v₁ and v₂ is divisible by p, so reduction modulo p induces a surjection G→(Z/pZ)². A product of two cyclic groups of order p is cyclic only when their orders are coprime. Since p≥3, this quotient is noncyclic, and G is noncyclic as well. This uses the modulus p itself, including composite p.

At r=s the widths are pa,pb, both positive and odd. Substituting their half-product cap count into the growth identity gives |f(Dₛ)|=|G|, hence actual coverage. At r=s−1 the widths are pa−2,pb−2, again positive and odd. The same count gives the exact deficit |G|−|f(Dₛ₋₁)|=p(2m−a−b)>0. This proves failure of coverage one step below s; monotonicity of the Lee bound then proves the covering equivalence for every natural R. The growth formula is asserted only through s, whereas the covering equivalence has no upper radius restriction.

For p=3,m=11,a=b=9, the basis is (3,30),(3,−30), the group has order 180 and the diameter is 16. At radius 15 both widths equal 25, so the cap has 313 points and the image has 481−313=168 points. Here 2min(a,b)=18>11, and h=(6,0) permits long fibers. This instance illustrates why the full rank-one fiber statement is needed.

Bajnok–Beatty arXiv:2406.04045v1 provides the Cayley-diameter context and known lower constructions. The asymmetric quotient family, its coefficient-separation argument and its deduction of exact diameter from the full growth identity are repository derivations from the finite-fiber and determinant-index results. They are not attributed to that paper, and no novelty or open-problem claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.asymmetric_quotient_growth`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_displacement`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.sharp_pair_growth`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySharpMaximum](BajnokBeattySharpMaximum.md)
