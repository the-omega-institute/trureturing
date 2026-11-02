# Exact growth from the upper overlap cap

## Abstract

A transversal of the short relation fibers determines every in-range ball of an actual composite maximum pair.

**Theorem 1.1 (A finite transversal in an arbitrary additive target).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Write Dᵣ={(x,y)∈Z²: |x|+|y|≤r}. Let f:Z²→G be additive, where G is any additive commutative group, let B>0 and r<2B be natural numbers, and set h=(0,2B). Assume f(h)=0 and every relation z of Lee norm at most 2r is 0, h or −h. Then the finite image f(Dᵣ) has cardinality 2r²+2r+1 for r<B and 2B(2r−B+1) for B≤r. The target need not be finite and f need not be surjective.

The overlap Cᵣ=Dᵣ∩(Dᵣ+h) is the upper cap: its points z have both z and z−h in Dᵣ. Remove exactly Cᵣ and retain Rᵣ=Dᵣ∖Cᵣ. Every deleted point has the same image as z−h. This lower point survives, because a second deletion would put z and z−2h in Dᵣ, although their distance 4B exceeds 2r. Thus Rᵣ still maps onto f(Dᵣ). If two retained points have the same image, their difference is 0 or ±h. The two nonzero possibilities force the higher point into the deleted cap. Hence f is injective on Rᵣ and gives a bijection Rᵣ→f(Dᵣ).

The identity max(|y|,|y−2B|)=B+|y−B| identifies Cᵣ with the empty set when r<B and with (0,B)+Dᵣ₋ᴮ otherwise. The existing two-parity LeeCode and decodeLee representation supplies |D_q|=(q+1)²+q². The bijection gives |f(Dᵣ)|=|Dᵣ|−|Cᵣ| by ordinary finite-set cardinality laws. Subtracting the translated smaller diamond gives the displayed second branch. The encoding and the finite-cardinality identities are inherited suppliers; the retained-domain injection and surjection are the fiber argument used here.

**Theorem 1.2 (Every actual composite maximum pair has the same ball growth).**

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

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.lee_ball_image_card_of_short_kernel`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth.sharp_pair_growth`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattySharpMaximum](BajnokBeattySharpMaximum.md)
