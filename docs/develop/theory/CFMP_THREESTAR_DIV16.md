# CFMP pure three-star topology: a 16-tetrahedron divisibility obstruction

## Scope

Consider a finite valid orientable ideal triangulation in which every
abstract tetrahedron is a pure three-star packet: after naming its vertices
`c,p1,p2,p3`, the three low local edges are `c-p1,c-p2,c-p3`, and the three
high local edges are the peripheral triangle `p1-p2,p1-p3,p2-p3`. Assume
all low quotient edges have degree exactly eight. Face pairings preserve the
low/high quotient-edge classes, as they must in a role-homogeneous colored packet.
This role-homogeneity is automatic when low means degree 8 and high means
degree at least 10, but is an additional hypothesis if a high local edge is
also allowed to have degree 8.

The existing CFMP three-edge paper already records the independent parity
fact that every high quotient edge has even degree. The theorem here is a
different, vertex-link obstruction on the number of tetrahedra.

## Theorem

Every such triangulation has a number of tetrahedra divisible by `16`.
More precisely, the center ideal-vertex links split into orientable closed
components `S_i`, and if `N_i` tetrahedra have their center in `S_i`, then

```
F(S_i) = N_i,
E(S_i) = 3*N_i/2,
V(S_i) = 3*N_i/8,
chi(S_i) = -N_i/8,
genus(S_i) = 1 + N_i/16.
```
Consequently `16 | N_i` for every component and `16 | N` globally.

## Proof

The face opposite `c` is an HHH face. Each face opposite `p_i` is an LLH
face: its two low edges meet at the unique vertex `c`. A face pairing
preserves the global low/high class of each edge, so it sends HHH faces to
HHH faces and LLH faces to LLH faces. On an LLH face, the intersection of the
two low edges is unique; therefore the face map sends center to center. HHH
faces contain no center and cannot identify a center with a peripheral
vertex. Thus center and peripheral ideal vertices form disjoint link
components.

Fix a center-link component `S_i`. Each tetrahedron whose center lies in
`S_i` contributes one truncation triangle, giving `F=N_i`. Its three LLH
faces contribute the three sides incident to that center triangle. Every LLH
face is paired once with another LLH face, so `E=3*N_i/2`.

A vertex of `S_i` is an end of a quotient low edge at the center. A degree
8 low quotient edge has eight local occurrences, all with the same center
end because LLH face maps preserve center. Hence every low quotient edge
represented in `S_i` contributes exactly one link vertex. There are three low
occurrences per tetrahedron, so `V=3*N_i/8`.

The valid orientable triangulation has closed orientable ideal-vertex links,
so `chi(S_i)=2-2g_i`. The cell count gives `chi=-N_i/8`, hence
`N_i=16(g_i-1)`. This proves the divisibility and genus formulas.

## Degree-class consequence

If the high quotient classes have degrees 8 and 14, with counts `a` and `b`,
then the 3-star edge count and the theorem give

```
N = 16*k,
4*a + 7*b = 24*k.
```
For exactly one high degree-8 class (`a=1`), the first possible solution is
`k=6`, namely `N=96` and `b=20`. Candidate counts with `N=40` or `N=72`
are therefore impossible before any angle or co-volume calculation.

## Literature and repository audit

The current CFMP three-edge document records the HHH/LLH alternation and
high-edge even-degree obstruction, but does not state the center-link
component count or the `16 | N` consequence. Uemura, arXiv:2609.34108v1
(September 2026), gives invariant-box and local angle criteria and explicit
face-pairing families; a full-text search of the primary HTML found no
three-star center-link divisibility statement. This theorem is a purely
topological necessary condition and is independent of Uemura's geometric
criteria.

This obstruction narrows role-homogeneous pure-star searches, but it does not
rule out a genuinely lowered-threshold construction in which a degree-8
quotient class occurs in both local roles. In that mixed-role case an LLH face
may pair to an HHH face, so the center/peripheral separation used above is
not available. The theorem does not itself establish geometricity or rule
out the first role-homogeneous admissible case `N=96`.
