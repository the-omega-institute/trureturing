[Index](../../marked_head_profile.md) · [Row/tree coupling](443-one-supported-law-couples-rows-and-tree-prefixes.md) · [Common prefix laws](376-complete-prime-chain-transport-and-joint-prefix-laws.md)

# Uniform subtree restrictions couple two prefix trees

These are ordinary finite averaging and flow deductions. They reuse report443's row/tree coupling theorem. The exact constructor supplies finite controls, not new Lean certification or a literature-priority claim.

## A depth-two restriction theorem

Let F be an actual subset of {0,...,m-1} x {0,...,p-1} x Y, where Y is the leaf set of a finite rooted tree with nonnegative rational proper-prefix caps kappa(v). Fix 1<=q<=m and 1<=t<=p.

Assume that for EVERY q-element root set A and EVERY choice of t-element child sets U_r at the roots r in A, the column projection of

    F intersect { (r,c,y): r in A and c in U_r }

supports a probability satisfying all the caps kappa(v).

Then ONE probability nu on the original F simultaneously satisfies

    nu(root r)                 <= 1/(m-q+1),
    nu(root r, child c)        <= (t/p)/(m-q+1),
    nu(Y_v)                    <= kappa(v),
    nu(root r, Y_v)            <= (q/m) kappa(v),
    nu(root r, child c, Y_v)   <= (q/m)(t/p) kappa(v).

No particular root/child fibre is assumed to support a column law. All conclusions concern the SAME probability before any later independent layout phases are selected.

Proof. Choose a t-element U_r independently and uniformly at every one of the m roots, including roots outside a later q-element root test. For each complete choice U, restrict the actual source to c in U_r, then project it to root/column pairs P_U. The hypothesis says every q-root projection of P_U supports the required column-prefix law. Report443 therefore gives one probability eta_U on P_U with root cap 1/(m-q+1), pure column caps kappa(v), and joint root/column cap (q/m)kappa(v).

Lift eta_U to the restricted actual source. For instance, distribute eta_U(r,y) uniformly among the nonempty set of actual children c in U_r satisfying (r,c,y) in F. This is a law nu_U on genuine triples; its root and column marginals equal eta_U. Choose the coupling and lifting deterministically from F,U and the prescribed capacities, without consulting any later layout.

Average nu_U uniformly over all choices U. The root and pure-column caps persist under averaging. A fixed child c belongs to U_r with probability t/p. When absent its cylinder mass is zero; when present its mass is at most the corresponding root mass. Hence

    nu(r,c) <= Pr(c in U_r)/(m-q+1),
    nu(r,c,Y_v) <= Pr(c in U_r)(q/m)kappa(v).

This gives all five assertions. The laws eta_U may vary arbitrarily with the full U: the argument uses a uniform pointwise upper bound on each conditional law, not independence of the law and the inclusion event. Every operation is finite and preserves rationality.

## Any finite row height

Let the row coordinate be the leaves of a complete m-ary tree of height D>=1. Suppose the column projection of F restricted to every complete q-ary row subtree supports the prescribed column-prefix law. Set beta=q/m and r=m-q+1. Then one actual law has

    nu(row-prefix u of depth a) <= beta^(a-1)/r,             1<=a<=D,
    nu(Y_v)                    <= kappa(v),
    nu(row-prefix u, Y_v)       <= beta^a kappa(v),          1<=a<=D.

For every first row root, independently and uniformly choose a complete q-ary subtree of height D-1 below it. Apply report443 to the first-row roots and the projected restricted source, lift to actual leaves and average. A specified row prefix of depth a survives the random restriction with probability beta^(a-1). The same two pointwise estimates prove the result.

Uniform means choosing each local q-child subset uniformly and independently along the selected subtree; equivalently every complete q-ary subtree of the fixed height has equal probability. The construction does not claim pure row cap r^(-a) for a>=2. Such a stronger simultaneous template is unnecessary for the consumer below and remains unproved here.

## Three robust first-five roots at heights (3,2)

Let R be an actual subset of Z/125 x Z/49. Call a first-five root robust when its actual remaining-five-depth-two/whole-seven fibre meets every local ternary depth-two five-tree times every full five-ary depth-two seven-tree. Assume three distinct first-five roots are robust. Other occupied roots may occur; no law needs to be placed on them. No restriction is imposed on the number of occupied second-five children, the fine matching numbers, or the individual fixed-mod25 fibres.

In particular, suppose R meets every product of a complete ternary depth-three five-tree and a complete five-ary depth-two seven-tree and exactly three first-five roots occur. Each occupied first-five root can be isolated by a legal first-five choice using the two unoccupied roots. Its actual fibre must therefore block every local product, proving robustness. This establishes the arbitrary exactly-three-occupied-root source class left open in report443.

For each fixed local five-tree in a robust root fibre, the seven projection meets every five-ary tree; complement duality supplies a ternary seven-tree and its uniform law with every depth-b prefix mass at most 3^(-b).

Apply the depth-two restriction theorem with m=p=5, q=t=3 and kappa(v)=3^(-b), separately in each of the three actual fibres. Mix those laws equally. The single resulting law on R has caps, with A the five-prefix depth and B the seven-prefix depth,

    cap(0,B) = 3^(-B),
    cap(1,B) = 3^(-B)/3,
    cap(2,0) = 1/9,
    cap(3,0) = 1/15,
    cap(2,B) = 3^(-B)/5,                B>=1,
    cap(3,B) = (3/25)3^(-B),            B>=1.

The weaker final-five marginal 1/15 is enough. The proof does not require 1/27 or assume that a fixed mod25 fibre itself blocks all local product trees.

Keep all twelve original divisor labels 5^A 7^B, A=0,...,3, B=0,...,2, with independently chosen residue phases. Each ordered indicator pair is either disjoint or has intersection a cylinder at the LCM of the two original labels. Exactly (2A+1)(2B+1) ordered label pairs have maximum exponents (A,B). With

    S_K = sum_(b=0)^K (2b+1)3^(-b) = 3-(K+2)3^(-K),

the full 144-term upper bound is

    Gamma_6125
       <= 2 S_2 + 5/9 + 7/15 + (46/25)(S_2-1)
        = 2024/225
        = 9-1/225 < 9.

The law is selected solely from the actual source and prescribed caps before testing any original phases. There is no centered-phase identification, replacement of a modulus label by its radical, or recombination of points from different actual fibres.

## General height certificate and its range

For H>=2 and K>=1, suppose an actual source in Z/5^H x Z/7^K has three distinct robust first-five roots: each of their whole remaining-five/whole-seven fibres blocks all local ternary and five-ary product trees. Full product-tree blocking with exactly three occupied first-five roots again implies this premise by isolation. Apply the arbitrary row-height theorem in those three fibres and mix equally. For A>=2 the resulting caps are

    cap(A,0) = (1/9)(3/5)^(A-2),
    cap(A,B) = (1/3)(3/5)^(A-1)3^(-B),             B>=1,

with cap(0,B)=3^(-B), cap(1,B)=3^(-B)/3 as before. Define

    U_H = sum_(A=2)^H [(2A+1)/9](3/5)^(A-2)
        = [20-5(H+3)(3/5)^(H-1)]/9.

Keeping every original divisor label, the single-law LCM bound is

    B_(H,K) = 2 S_K + [(9 S_K-4)/5] U_H.

This increases with H and K. The exact domain B_(H,K)<9 for H>=2, K>=1 is

    H=2: every finite K;
    H=3: K=1 or K=2;
    H=4 or H=5: K=1.

Indeed the boundary values are

    B_(3,2)=2024/225,    B_(3,3)=2248/225,
    B_(4,1)=8854/1125,  B_(4,2)=11659/1125,
    B_(5,1)=48428/5625, B_(6,1)=256882/28125.

At H=2 the formula agrees with the already established report443 certificate; it is not a newly closed height range here. The displayed range concerns this sufficient bound, not the true minimax values.

## Limits of the conclusion

In particular, at heights (3,K) the valid bound is

    Gamma_(125*7^K) <= (96/25)S_K-184/225.

At K=3 this certificate equals 2248/225>9; as K tends to infinity it tends to 2408/225>9. Its success at K=2 therefore does not give all-seven-height closure. These larger numbers limit this certificate; they do not show an actual minimax lower bound.

The hypothesis requires three robust first-five roots. It includes sources with four or five occupied roots if three are robust, but does not cover an arbitrary source lacking that property. It does not establish arithmetic realization of every abstract source, does not transport the complete cofactor moment floor, and does not settle Erdős #7. It closes the specific exactly-three-occupied-root abstract source class left open in report443, including sources for which every fixed mod25 fibre fails that report's local blocking selector.

## Exact construction without listing every conditional law

The [standard-library depth-two constructor](../../frontier/cover-geometry/subtree_restriction_coupling.py) groups a root's t-child choices by their projected column-neighborhood signature. It computes the report443 coupling once per full signature profile. Conditional on a profile, root choices remain independent and uniform within their groups. For each root/column pair, its actual lift is averaged over that root's group, distributing uniformly over available actual children. The profile gets weight equal to the product of the group multiplicities divided by binom(p,t)^m.

This is exactly the same uniform restriction average as in the proof, compressed by equal projected supports. Every projected-cap premise is checked by the existing exact report443 constructor. The final actual law is checked again for unit mass, literal support, all root/child marginals, and all mixed prefix caps. Worst-case profile count remains binom(p,t)^m; grouping is an optimization, not a new hypothesis or a truncation.

Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/subtree_restriction_coupling.py
```

The constructor implements the depth-two row theorem; the arbitrary-D result is the ordinary proof above, not an implemented arbitrary-depth interface. Its exact run on the two existing fixtures gives:

| Reused source | Original restrictions per local source | Grouped flows | Actual law support | Same-law LCM upper |
| --- | ---: | ---: | ---: | ---: |
| report443 450-point source | 100,000 | 1,024 | 180 | 36637/4500 |
| report442 540-point source | 100,000 | 27 | 231 | 373903/45000 |

Each fixture has three identical local source patterns, so the local construction is computed once and transported to the three distinct actual root fibres. The first source has no fixed-mod25 fibre passing report443's local blocker selector. Both constructed laws satisfy all twelve stated cylinder caps and the full 144-pair upper bound 2024/225. The fixture-specific laws already known in earlier reports can have smaller bounds; these controls verify the new general constructor rather than claiming optimized laws for those sources.

The small depth-two ternary diagonal control has nine actual points and returns their uniform law, attaining the mixed leaf cap 1/9. Malformed and insufficient-premise inputs are rejected. Exact height controls compare the formula with the literal LCM sum on 380 finite height pairs; the unbounded height range is supplied by the formula and monotonicity proof, not that finite test set.
