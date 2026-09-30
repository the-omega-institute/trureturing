# Exact all-region RT on a three-loop bouquet over F13

## Theorem

Take a planar graph with one central 6-valent vertex and three loop pairs of outer 4-valent vertices. Each outer vertex has two boundary legs; each loop pair is joined by a loop edge and each outer vertex joins the center. Over F13, let central coefficient rows be C=[[7,4,8],[11,12,3],[11,6,5],[4,9,8],[4,7,12],[2,4,1]]. Write lambda=(x1,x2,x3). For loop j with loop coordinate zj, use boundary outputs (C2j·lambda+zj,C2j·lambda-zj,C2j+1·lambda+2zj,C2j+1·lambda-2zj).

The network has one AME(6,13) center and six AME(4,13) outer tensors, with identical positive amplitudes. The induced boundary state is uniform on a 6-dimensional linear support and obeys S(R)=m(R) log 13 for all 4096 boundary regions.

The center is AME(6,13): every triple of rows of C is independent (all 20 triples checked). Each outer tensor is AME(4,13) because u,v,u+2v,u-2v are pairwise independent.

## Rank/min-cut proof

For a region R let rj be its selected-leg count in loop j. A loop is partial exactly when rj in {1,2,3}. Let h be the number of partial loops and define e(0)=e(1)=0, e(2)=1, e(3)=e(4)=2 and E=sum e(rj). Exact row reduction yields rank(F_R)=h+min(3,E), rank(G_R)=h+min(3,6-E).

The graph cut optimized over the central vertex has exactly this same value after the Schmidt correction: the entropy exponent is 2h + min(3,E) + min(3,6-E) - 6, and this equals the optimized graph cut. Each partial loop contributes 2, while complete loops contribute 0 or 2 according to the central side. Therefore the uniform linear-support entropy lemma gives S(R)=m(R) log 13 for all regions.

## Reproducible certificate and scope

The verifier tools/scripts/agent/rt/verify_bouquet3_f13.py checks all 88 virtual central direction patterns, central rank 3 and full support rank 6, then enumerates all 4096 regions and compares exact Schmidt exponents with graph min-cuts. This is a finite tensor-network theorem with positive identical amplitudes; arbitrary phases are not covered. It does not claim arbitrary-k closure or a gravitational RT dual.

## Literature boundary

HaPPY (arXiv:1503.06237) covers only connected regions under its geometric hypotheses. Cui et al. (arXiv:1508.04644) give designated-cut max-flow/max-cut results, not one fixed AME assignment for every cut. Apel–Kohler–Cubitt (arXiv:2105.12067) give nonconstructive large-bond random-stabilizer simultaneous exactness. Bao et al. (arXiv:2002.05317) give a broader AME/GHZ framework whose universal matching remains conjectural. None directly gives this explicit seven-tensor F13 bouquet witness.
