# An Actual Boolean K4 Subdivision and Its Exact Certificate

## Abstract

An actual Boolean rank-three K4 certificate refutes the necessary two-degree-four shape.

This document describes the fixed table and the exact propositions Certificate, FourPathDegreeConsequence, claim, and result in BooleanRankThreeK4. All certificate clauses refer to this same original table and these same paths, cycles, and encoders. The statement is a concrete method counterexample; it is neither a universal rank-three budget theorem nor an impossibility of a (3,3) protocol.

Let X=Fin 8, Y=Fin 6, and V=X disjoint-union Y. Write x_i=inl(i), y_j=inr(j), with zero-based indices. Boolean 0 and 1 mean false and true. The partial table has type X -> Y -> Option Bool: a star means none, and a bit means some of that bit. In row order x_0 through x_7, its six-entry rows are 00****, **11**, 1***0*, **1*0*, *0***1, ***0*1, 0**1**, *10***. No output is prescribed at an illegal pair.

G=support(table) is the undirected simple graph on V with x_i adjacent to y_j exactly when table(i,j) is some bit; there are no edges within either side. ActiveConnected requires a legal pair, a legal partner for every input on each side, and connected support. cycleRank is the integer |legal pairs|-|X|-|Y|+1. The left conflict graph joins two rows when a common legal column has different bits; the right conflict graph is the symmetric column construction. Both are computed on the original table.

The enumeration legalPairs:Fin 16 -> X times Y, in order e_0 through e_15, is (0,0),(0,1),(1,2),(1,3),(2,0),(2,4),(3,2),(3,4),(4,1),(4,5),(5,3),(5,5),(6,0),(6,3),(7,1),(7,2). edge(e) is the unordered pair of the corresponding tagged endpoints, incident(v,e) is true exactly when v is either endpoint, and bit(e) is the corresponding table bit (using false as the Option default). The certificate verifies injectivity and exact coverage of legal pairs.

The branch set is {y_0,y_1,y_2,y_3}. The six endpoint pairs ends(i), for i=0,...,5, are (y_0,y_1),(y_0,y_2),(y_0,y_3),(y_1,y_2),(y_1,y_3),(y_2,y_3). The corresponding vertex lists paths(i) are [y_0,x_0,y_1], [y_0,x_2,y_4,x_3,y_2], [y_0,x_6,y_3], [y_1,x_7,y_2], [y_1,x_4,y_5,x_5,y_3], [y_2,x_1,y_3]. pathWalk(i) is the actual G-walk between ends(i); internal(i) removes the first and last vertices of paths(i).

The four closed vertex lists cycles(k), for k=0,...,3, are [x_0,y_0,x_2,y_4,x_3,y_2,x_7,y_1,x_0], [x_0,y_0,x_6,y_3,x_5,y_5,x_4,y_1,x_0], [x_1,y_2,x_3,y_4,x_2,y_0,x_6,y_3,x_1], [x_1,y_2,x_7,y_1,x_4,y_5,x_5,y_3,x_1]. cycleWalk(k) is the corresponding actual closed G-walk, starting at x_0,x_0,x_1,x_1 respectively. cycleVector(k)(e) is true exactly when edge(e) belongs to that walk's edge list.

For an arbitrary vector z:Fin 16 -> Bool, CycleVector(z) means that, at every v in V, the XOR over all sixteen e of z(e) AND incident(v,e) is false. This is the entire even-incidence edge-coordinate definition, not only the four displayed cycle indicators. oddParity(z) is the XOR over all e of z(e) AND bit(e). Odd always refers to label parity, not to the number of edges in a cycle.

For three Boolean bits (a,b,d), encode(a,b,d) is the sixteen-entry vector [a,a,b XOR d,b XOR d,b,b,b,b,a XOR d,a XOR d,a XOR d,a XOR d,a XOR b,a XOR b,d,d]. Its coordinates 0,4,14 are a,b,d. The certificate classifies every even-incidence vector by precisely these three coordinates and gives both the whole-set and odd-fiber cardinalities.

monoX(c,i) means: for every j and Boolean b, table(i,j)=some(b) implies b=c. monoY(d,j) means: for every i and Boolean b, table(i,j)=some(b) implies b=d. These predicates inspect all original incident legal pairs. survives(c,d,x_i) means not monoX(c,i); survives(c,d,y_j) means not monoY(d,j). The selected residualCycle(c,d) is 3,2,1,0 for (c,d)=(0,0),(0,1),(1,0),(1,1), respectively. Survival below is a statement about the actual cycle supports avoiding both whole original classes.

The encoders alpha:Fin 8 -> Fin 3 and beta:Fin 6 -> Fin 3 have lists [0,0,1,0,1,1,0,2] and [0,1,2,2,1,0]. The decoder on Fin 3 times Fin 3 has rows [0,0,1], [1,0,0], [0,1,0]. alphaNat and betaNat take the natural-number values of these encoders. decoderNat:N times N -> Bool uses that matrix when both arguments are less than three and returns false otherwise; it is total on the infinite ambient alphabets.

Admits(table,3,3) means there exist arbitrary message types A,B, encoders X->A and Y->B, and a total decoder A->B->Bool, with each encoder range having Nat.card at most three and correct decoding on every original legal pair. The displayed realization uses A=B=N and has exactly three reachable messages on each side. Nat.card below counts finite sets via their corresponding subtype; all counted sets here are finite.

Legal is the subtype of original pairs (i,j) for which table(i,j).isSome=true. leftInput and rightInput are the original coordinate projections; output is the original table bit. ThreeLeafCausalPeak.CutAdmits(output,l,r,n) quantifies an arbitrary ambient type A, an encoder e from the own-input type to A, and a total decoder d:A -> other-input-type -> Bool. It requires Nat.card(range(e composed with l))<=n and d(e(l(w)),r(w))=output(w) for every legal world w. cutCost is the infimum of these natural-number budgets. In particular, an infinite ambient A is allowed and only actually reachable messages are charged.

Both cut costs equal two. For the left cut, the encoder is [0,0,1,0,0,1,0,1] and the two total decoder rows on Y are [0,0,1,1,0,1] and [1,1,0,0,0,1]. For the right cut, the encoder is [0,1,0,1,1,0] and the decoder rows on X are [0,1,1,1,1,1,0,0] and [0,1,0,0,0,0,1,1]. The opposite outputs at (x_0,y_0),(x_2,y_0) force two distinct reachable left messages for every correct encoder; those at (x_6,y_0),(x_6,y_3) force two distinct reachable right messages. These bounds apply to every ambient alphabet.

The faithful map to BooleanRankThreeFiber sends false to 0 and true to 1 in ZMod 2 via bit2, and maps each original Option entry with bit2 to form mappedTask. The certificate proves the bijection, XOR-to-addition law, exact legal-entry and support correspondence, and equality of both original mono-class predicates. Fiber.residual isolates every deleted original vertex; its remaining edges are precisely original edges whose two endpoints survive. Fiber.Balanced means that every actual simple closed walk has label sum zero. residualWalk(c,d) is the selected actual cycle on this residual support, with the original vertex and edge lists and label sum one.

**Definition 1.1 (The complete positive certificate).**

$$Certificate\iff(C1\land C2\land C3\land C4\land C5\land C6\land C7\land C8\land C9\land C10\land C11\land C12\land C13\land C14\land C15\land C16\land C17\land C18\land C19\land C20\land C21\land C22\land C23\land C24\land C25\land C26\land C27\land C28\land C29\land C30\land C31\land C32\land C33\land C34\land C35\land C36\land C37\land C38\land C39\land C40\land C41\land C42\land C43\land C44\land C45\land C46)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeK4.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C1. ActiveConnected(table): the original legal domain is nonempty, every one of the eight rows and six columns has a legal partner, and G is connected.

C2. cycleRank(table)=3, using integer cardinality subtraction.

C3. Nat.card {p:X times Y | table(p.1,p.2).isSome=true}=16.

C4. Nat.card V=14.

C5. The chromatic number of leftConflict(table) is exactly 2.

C6. The chromatic number of rightConflict(table) is exactly 2.

C7. legalPairs is injective.

C8. For every i in Fin 8 and j in Fin 6, table(i,j).isSome=true if and only if there exists e in Fin 16 with legalPairs(e)=(i,j).

C9. For every Boolean c and i in Fin 8, monoX(c,i) if and only if i equals 1 when c=true and 0 when c=false. Thus the whole original X bit classes are {x_0} and {x_1}.

C10. For every Boolean c and j in Fin 6, monoY(c,j) if and only if j equals 5 when c=true and 4 when c=false. Thus the whole original Y bit classes are {y_4} and {y_5}.

C11. branches.card=4.

C12. For every v in V, G.degree(v)=3 if v belongs to branches, and G.degree(v)=2 otherwise.

C13. For every i in Fin 6, pathWalk(i) is a simple path and its support list is exactly paths(i).

C14. For every i in Fin 6 and v in V, membership of v in internal(i) implies v is not a branch vertex.

C15. For every distinct i,j in Fin 6, the lists internal(i) and internal(j) are disjoint.

C16. For every distinct branch vertices u,v, there exists i in Fin 6 such that ends(i)=(u,v) or ends(i)=(v,u).

C17. For every u,v in V, G.Adj(u,v) if and only if there exists i in Fin 6 for which the unordered pair {u,v} belongs to the edges of pathWalk(i).

C18. For every v in V, there exists i in Fin 6 with v in the support of pathWalk(i). Together C11-C18 describe the actual K4 subdivision, including simplicity, branch degrees, interior disjointness, all branch pairs, and full edge and vertex coverage.

C19. For every k in Fin 4, cycleWalk(k) is a simple cycle, CycleVector(cycleVector(k)) holds, and oddParity(cycleVector(k))=true.

C20. For every Boolean c,d and v in V, if v is in the support of cycleWalk(residualCycle(c,d)), then survives(c,d,v). This selects an actual odd simple cycle avoiding both complete original classes for each of the four choices.

C21. For every z:Fin 16 -> Bool, CycleVector(z) if and only if z=encode(z(0),z(4),z(14)). Equality here is equality of all sixteen coordinates.

C22. Nat.card {z:Fin 16 -> Bool | CycleVector(z)}=8.

C23. For every z:Fin 16 -> Bool satisfying CycleVector(z), oddParity(z)=true if and only if there exists k in Fin 4 with z=cycleVector(k). This quantifies over the entire even-incidence space.

C24. Nat.card {z:Fin 16 -> Bool | CycleVector(z) and oddParity(z)=true}=4.

C25. Nat.card(range(alphaNat))=3.

C26. Nat.card(range(betaNat))=3.

C27. For every i in Fin 8, j in Fin 6, and Boolean c, table(i,j)=some(c) implies decoderNat(alphaNat(i),betaNat(j))=c.

C28. Admits(table,3,3). The preceding encoders and the total natural-number decoder give the exhibited realization.

C29. ThreeLeafCausalPeak.cutCost(output,leftInput,rightInput)=2 on Legal.

C30. ThreeLeafCausalPeak.cutCost(output,rightInput,leftInput)=2 on the same Legal.

C31. For every e in Fin 16, cycleVector(0)(e) XOR cycleVector(1)(e) XOR cycleVector(2)(e) XOR cycleVector(3)(e)=false. Thus the four actual cycle vectors sum to zero.

C32. For every z:Fin 16 -> Bool with CycleVector(z), z equals the vector e |-> (z(0) AND cycleVector(1)(e)) XOR (z(4) AND cycleVector(2)(e)) XOR (z(14) AND cycleVector(3)(e)). Hence the actual cycles span the entire space, with coefficient zero on cycleVector(0).

C33. For every Boolean a,b,d, the vector e |-> (a AND cycleVector(1)(e)) XOR (b AND cycleVector(2)(e)) XOR (d AND cycleVector(3)(e)) is identically false if and only if a=b=d=false. These three actual generators are independent.

C34. For every Boolean a,b,d, CycleVector(encode(a,b,d)) and oddParity(encode(a,b,d))=a XOR b XOR d.

C35. bit2:Bool -> ZMod 2 is bijective.

C36. For every Boolean a,b, bit2(a XOR b)=bit2(a)+bit2(b).

C37. For every i in Fin 8, j in Fin 6 and Boolean b, mappedTask.table(i,j)=some(bit2(b)) if and only if table(i,j)=some(b).

C38. For every a,b in V, Fiber.support(mappedTask).Adj(a,b) if and only if G.Adj(a,b), where Fiber denotes BooleanRankThreeFiber.

C39. For every Boolean c and i in Fin 8, Fiber.monoLeft(mappedTask,bit2(c),i) if and only if monoX(c,i).

C40. For every Boolean d and j in Fin 6, Fiber.monoRight(mappedTask,bit2(d),j) if and only if monoY(d,j).

C41. For every Boolean c,d and a,b in V, Fiber.residual(mappedTask,bit2(c),bit2(d)).Adj(a,b) if and only if G.Adj(a,b) and survives(c,d,a) and survives(c,d,b). This removes the whole original classes, with deleted vertices isolated on the original carrier.

C42. For every e in Fin 16, Fiber.label(mappedTask,edge(e))=bit2(bit(e)).

C43. For every Boolean c,d, residualWalk(c,d) has support cycles(residualCycle(c,d)), has exactly the edges of cycleWalk(residualCycle(c,d)), is a simple cycle, and has walkParity one under the actual Fiber.label(mappedTask) edge labels.

C44. For every Boolean c,d, that residual walkParity equals bit2(oddParity(cycleVector(residualCycle(c,d)))).

C45. For every Boolean c,d, Fiber.Balanced(mappedTask,Fiber.residual(mappedTask,bit2(c),bit2(d))) is false.

C46. For every c,d in ZMod 2, Fiber.Balanced(mappedTask,Fiber.residual(mappedTask,c,d)) is false. Bijectivity of bit2 covers all four deletion choices.

**Definition 1.2 (The explicit necessary degree condition).**

$$FourPathDegreeConsequence\iff\exists u,v\in V,(u\neq v\land deg(u)=4\land deg(v)=4\land(\forall w\in V,w\neq u\implies w\neq v\implies deg(w)=2))$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeK4.FourPathDegreeConsequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There must exist two distinct vertices u,v of G, each of degree four, and every other vertex must have degree two. This is only the explicitly stated necessary degree shape of a full four-path subdivision. It is not a definition or a renaming of the full four-path or theta subdivision property. The latter would additionally specify its actual paths and their coverage.

**Definition 1.3 (The implication being refuted).**

$$claim\iff(Certificate\implies FourPathDegreeConsequence)$$

*Formalization.* `D5/S3/Observer/Separation/BooleanRankThreeK4.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

claim is exactly Certificate -> FourPathDegreeConsequence for this fixed original table. Its antecedent contains all forty-six positive clauses above; none is discarded or replaced by a hypothesis about a different task.

**Theorem 1.4 (The positive certificate refutes the degree consequence).**

$$\neg(Certificate\implies FourPathDegreeConsequence)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/BooleanRankThreeK4.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact theorem type is Not claim, with claim defined as the displayed implication. The proof constructs all forty-six positive Certificate clauses inside result before applying the proposed implication to it. The original one-sided costs, entire cycle space, all four actual residuals, K4 subdivision, and (3,3) protocol refer to the same original table. C12 gives degree three or two for every vertex, contradicting even the first required degree-four endpoint.

## References

- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeK4.Certificate`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeK4.FourPathDegreeConsequence`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeK4.claim`
- Truth anchor: `D5/S3/Observer/Separation/BooleanRankThreeK4.result`
- Dependency: [D5/S3/Observer/Separation/BooleanRankFour](BooleanRankFour.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeFiber](BooleanRankThreeFiber.md)
- Dependency: [D5/S3/Observer/Separation/ThreeLeafCausalPeak](ThreeLeafCausalPeak.md)
