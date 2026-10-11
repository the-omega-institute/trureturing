# Marked walls and ordered binary arcs

## Abstract

Distinguishing either wall identifies literal cyclic words with ordered binary arcs and gives a free double cover compatible with translation.

Fix natural numbers a,b and put L=a+b+2. Positions, literal words and their delta basis are those of TwoWallWords. A mark distinguishes one of the two wall positions without changing the literal word. Binary true denotes letter two and false denotes letter one. Coordinates store p,m,n,u,v with m+n=a+b; thus n=a+b−m and m<L−1. This redundant length coordinate is uniquely determined and includes both empty-arc cases. The function ones is the existing count of true entries in a binary word. All equalities of positions use ZMod(L); natural-number subtractions in lengths and indices are truncated subtraction.

**Definition 1.1 (Distinguishing one wall).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{MarkedWord}\left(a, b\right) = \operatorname{Subtype}\left(((x : \operatorname{Prod}\left(\operatorname{Word}\left(a, b\right), \operatorname{Pos}\left(a, b\right)\right)) \mapsto \operatorname{coe}\left(\operatorname{first}\left(x\right)\right)\left(\operatorname{second}\left(x\right)\right) = \operatorname{wall})\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.MarkedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype retains the counted literal word and a position occupied by a wall.

**Definition 1.2 (The unique other wall).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{otherWall}\left(x\right) = \operatorname{Choose}\left(((q : \operatorname{Pos}\left(a, b\right)) \mapsto (\neg(q = \operatorname{mark}\left(x\right))) \land ((\operatorname{coe}\left(\operatorname{word}\left(x\right)\right)\left(q\right) = \operatorname{wall}) \land (\forall r \in \operatorname{Pos}\left(a, b\right),\; (\operatorname{coe}\left(\operatorname{word}\left(x\right)\right)\left(r\right) = \operatorname{wall}) \Rightarrow ((r = \operatorname{mark}\left(x\right)) \lor (r = q)))))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.otherWall` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are exactly two wall positions. Given the distinguished position, exactly one other wall remains. Choose denotes classical choice from the displayed unique specification.

**Definition 1.3 (Exchanging the distinguished wall).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{J}\left(x\right) = (\operatorname{word}\left(x\right), \operatorname{otherWall}\left(x\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The underlying literal word is retained and its other wall becomes the distinguished wall.

**Definition 1.4 (Translating a marked word).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \operatorname{Pos}\left(a, b\right),\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; (\operatorname{markedRotate}\left(t\right)\left(x\right) = (\operatorname{rotate}\left(t\right)\left(\operatorname{word}\left(x\right)\right), \operatorname{mark}\left(x\right) + t)) \land (\operatorname{inverse}\left(\operatorname{markedRotate}\left(t\right)\right)\left(x\right) = (\operatorname{inverse}\left(\operatorname{rotate}\left(t\right)\right)\left(\operatorname{word}\left(x\right)\right), \operatorname{mark}\left(x\right) - t))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.markedRotate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map translates the word and its mark by t. The inverse translates by minus t. The marked letter stays a wall.

**Definition 1.5 (Linear combinations of marked words).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall K \in \operatorname{Type},\; [\operatorname{Zero}\left(K\right)] \operatorname{MarkedSpace}\left(K, a, b\right) = \operatorname{Finsupp}\left(\operatorname{MarkedWord}\left(a, b\right), K\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.MarkedSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The marked vector space has one delta basis vector for each choice of a literal word and a wall mark.

**Definition 1.6 (Marked delta vectors).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{markedDelta}\left(K, x\right) = \operatorname{single}\left(x, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.markedDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is one at the indicated marked word and zero at all other labels.

**Definition 1.7 (Forgetting the mark).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Q}\left(K, a, b\right) = \operatorname{lmapDomain}\left(K, K, ((x : \operatorname{MarkedWord}\left(a, b\right)) \mapsto \operatorname{word}\left(x\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Linear pushforward sends each marked delta vector to the delta vector of its underlying literal word.

**Definition 1.8 (Summing the two marked lifts).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{S}\left(K, a, b\right) = \operatorname{linearCombination}\left(K, ((w : \operatorname{Word}\left(a, b\right)) \mapsto \sum_{p\in\operatorname{Subtype}\left(((p : \operatorname{Pos}\left(a, b\right)) \mapsto \operatorname{coe}\left(w\right)\left(p\right) = \operatorname{wall})\right)} (\operatorname{markedDelta}\left(K, (w, \operatorname{coe}\left(p\right))\right)))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LinearCombination extends the displayed basis images linearly. The sum is over the subtype of wall positions, so each literal word has precisely two summands.

**Definition 1.9 (The linear mark exchange).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Jstar}\left(K, a, b\right) = \operatorname{lmapDomain}\left(K, K, ((x : \operatorname{MarkedWord}\left(a, b\right)) \mapsto \operatorname{J}\left(x\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.Jstar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map pushes basis labels forward under the exchange of marks.

**Definition 1.10 (Linear translation on the cover).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \operatorname{Pos}\left(a, b\right),\; \operatorname{markedTranslation}\left(K, t\right) = \operatorname{lmapDomain}\left(K, K, \operatorname{markedRotate}\left(t\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.markedTranslation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translation permutes the marked basis labels.

**Definition 1.11 (The one-site marked shift).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{markedU}\left(K, a, b\right) = \operatorname{markedTranslation}\left(K, 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.markedU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the right shift by one site on the marked cover.

**Theorem 1.12 (A free double cover and the descent identities).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; ((((((((\forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{J}\left(\operatorname{J}\left(x\right)\right) = x) \land (\forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \neg(\operatorname{J}\left(x\right) = x))) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{markedRotate}\left(t\right)\left(\operatorname{J}\left(x\right)\right) = \operatorname{J}\left(\operatorname{markedRotate}\left(t\right)\left(x\right)\right))) \land (\operatorname{Q}\left(K, a, b\right) \circ \operatorname{S}\left(K, a, b\right) = \operatorname{scalar}\left(K, 2\right) \cdot \operatorname{id})) \land (\operatorname{S}\left(K, a, b\right) \circ \operatorname{Q}\left(K, a, b\right) = \operatorname{id} + \operatorname{Jstar}\left(K, a, b\right))) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; \operatorname{markedTranslation}\left(K, t\right) \circ \operatorname{S}\left(K, a, b\right) = \operatorname{S}\left(K, a, b\right) \circ \operatorname{translation}\left(K, t\right))) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; \operatorname{Q}\left(K, a, b\right) \circ \operatorname{markedTranslation}\left(K, t\right) = \operatorname{translation}\left(K, t\right) \circ \operatorname{Q}\left(K, a, b\right))) \land (\operatorname{markedU}\left(K, a, b\right) \circ \operatorname{S}\left(K, a, b\right) = \operatorname{S}\left(K, a, b\right) \circ \operatorname{U}\left(K, a, b\right))) \land (\operatorname{Q}\left(K, a, b\right) \circ \operatorname{markedU}\left(K, a, b\right) = \operatorname{U}\left(K, a, b\right) \circ \operatorname{Q}\left(K, a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallMarked.marked_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The other wall of the other wall is the original mark, and the two marks are distinct. Translation preserves this unique pairing. On a marked delta vector, S after Q sums that vector and the vector with the other mark. On a literal delta vector, Q after S adds that vector twice. Translation sends the two marked lifts bijectively to the two lifts of the translated word; this gives the two intertwining identities for every displacement and hence for the one-site shifts. These identities hold over every field, including characteristic two.

**Definition 1.13 (The two ordered binary arcs).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Coordinates}\left(a, b\right) = \operatorname{Subtype}\left(((c : \operatorname{Sigma}\left(\operatorname{Pos}\left(a, b\right), ((p : \operatorname{Pos}\left(a, b\right)) \mapsto \operatorname{Sigma}\left(\mathbb{N}, ((m : \mathbb{N}) \mapsto \operatorname{Sigma}\left(\mathbb{N}, ((n : \mathbb{N}) \mapsto \operatorname{Prod}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Bool}, \operatorname{Fin}\left(n\right) \to \operatorname{Bool}\right))\right))\right))\right)) \mapsto (\operatorname{m}\left(c\right) + \operatorname{n}\left(c\right) = a + b) \land (\operatorname{ones}\left(\operatorname{u}\left(c\right)\right) + \operatorname{ones}\left(\operatorname{v}\left(c\right)\right) = b))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent tuple consists of p,m,n,u,v. The first binary word has length m, the second has length n, and their numbers of true entries add to b. The proof fields are the length and filling equalities; no positivity is imposed on either arc.

**Definition 1.14 (Placing the two arcs on the cycle).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; (\operatorname{mark}\left(\operatorname{encode}\left(c\right)\right) = \operatorname{p}\left(c\right)) \land (\forall q \in \operatorname{Pos}\left(a, b\right),\; \forall d \in \mathbb{N},\; (d = \operatorname{val}\left(q - \operatorname{p}\left(c\right)\right)) \Rightarrow (\operatorname{coe}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\left(q\right) = \operatorname{ite}\left((d = 0) \lor (d = \operatorname{m}\left(c\right) + 1), \operatorname{wall}, \operatorname{ite}\left(d \le \operatorname{m}\left(c\right), \operatorname{ite}\left(\operatorname{u}\left(c\right)\left(\operatorname{finIndex}\left(d - 1\right)\right), \operatorname{two}, \operatorname{one}\right), \operatorname{ite}\left(\operatorname{v}\left(c\right)\left(\operatorname{finIndex}\left(d - \operatorname{m}\left(c\right) - 2\right)\right), \operatorname{two}, \operatorname{one}\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at p, place wall,u,wall,v at consecutive offsets. The displayed piecewise expression reads the unique residue d in [0,L). The two wall offsets and the two interior intervals partition all positions, including when either interval is empty. Reindexing the counts gives a ones, b twos and two walls.

**Definition 1.15 (Reading the arcs from a marked word).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \forall d \in \mathbb{N},\; (d = \operatorname{val}\left(\operatorname{otherWall}\left(x\right) - \operatorname{mark}\left(x\right)\right)) \Rightarrow (\operatorname{decode}\left(x\right) = (\operatorname{mark}\left(x\right), d - 1, a + b - (d - 1), ((i : \operatorname{Fin}\left(d - 1\right)) \mapsto \operatorname{decide}\left(\operatorname{coe}\left(\operatorname{word}\left(x\right)\right)\left(\operatorname{mark}\left(x\right) + \operatorname{natCast}\left((\operatorname{val}\left(i\right) + 1)\right)\right) = \operatorname{two}\right)), ((i : \operatorname{Fin}\left(a + b - (d - 1)\right)) \mapsto \operatorname{decide}\left(\operatorname{coe}\left(\operatorname{word}\left(x\right)\right)\left(\operatorname{mark}\left(x\right) + \operatorname{natCast}\left(((d - 1) + 2 + \operatorname{val}\left(i\right))\right)\right) = \operatorname{two}\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nonzero residue of otherWall(x)−mark(x) has representative d between 1 and L−1. Its predecessor is m; the complementary nonwall length is n. The arcs contain no walls, so equality with letter two recovers their Boolean entries. Reconstructing every site also recovers the total number b of true entries.

**Definition 1.16 (The marked-word coordinate equivalence).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (\operatorname{forward}\left(\operatorname{coordinateEquiv}\left(a, b\right)\right) = ((c : \operatorname{Coordinates}\left(a, b\right)) \mapsto \operatorname{encode}\left(c\right))) \land (\operatorname{inverse}\left(\operatorname{coordinateEquiv}\left(a, b\right)\right) = ((x : \operatorname{MarkedWord}\left(a, b\right)) \mapsto \operatorname{decode}\left(x\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encoding and decoding are mutually inverse; the forward map is encode and the inverse map is decode.

**Definition 1.17 (Mark exchange in arc coordinates).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{coordinateSwap}\left(c\right) = (\operatorname{p}\left(c\right) + \operatorname{natCast}\left((\operatorname{m}\left(c\right) + 1)\right), \operatorname{n}\left(c\right), \operatorname{m}\left(c\right), \operatorname{v}\left(c\right), \operatorname{u}\left(c\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second wall becomes the starting position, the two lengths exchange places, and the two binary words exchange places. The length and filling certificates follow by commutativity of addition.

**Definition 1.18 (Rotation acts only on the position).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall t \in \operatorname{Pos}\left(a, b\right),\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{coordinateRotate}\left(t, c\right) = (\operatorname{p}\left(c\right) + t, \operatorname{m}\left(c\right), \operatorname{n}\left(c\right), \operatorname{u}\left(c\right), \operatorname{v}\left(c\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateRotate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both lengths and both binary words are retained; only p changes to p+t.

**Theorem 1.19 (Round trips, layouts and coordinate symmetries).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; ((((((((\forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{decode}\left(\operatorname{encode}\left(c\right)\right) = c) \land (\forall x \in \operatorname{MarkedWord}\left(a, b\right),\; \operatorname{encode}\left(\operatorname{decode}\left(x\right)\right) = x)) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; (\operatorname{m}\left(c\right) < a + b + 1) \land (\operatorname{n}\left(c\right) = a + b - \operatorname{m}\left(c\right)))) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; (((\operatorname{coe}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\left(\operatorname{p}\left(c\right)\right) = \operatorname{wall}) \land (\operatorname{coe}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\left(\operatorname{p}\left(c\right) + \operatorname{natCast}\left((\operatorname{m}\left(c\right) + 1)\right)\right) = \operatorname{wall})) \land (\forall i \in \operatorname{Fin}\left(\operatorname{m}\left(c\right)\right),\; \operatorname{coe}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\left(\operatorname{p}\left(c\right) + \operatorname{natCast}\left((\operatorname{val}\left(i\right) + 1)\right)\right) = \operatorname{ite}\left(\operatorname{u}\left(c\right)\left(i\right), \operatorname{two}, \operatorname{one}\right))) \land (\forall i \in \operatorname{Fin}\left(\operatorname{n}\left(c\right)\right),\; \operatorname{coe}\left(\operatorname{word}\left(\operatorname{encode}\left(c\right)\right)\right)\left(\operatorname{p}\left(c\right) + \operatorname{natCast}\left((\operatorname{m}\left(c\right) + 2 + \operatorname{val}\left(i\right))\right)\right) = \operatorname{ite}\left(\operatorname{v}\left(c\right)\left(i\right), \operatorname{two}, \operatorname{one}\right)))) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{encode}\left(\operatorname{coordinateSwap}\left(c\right)\right) = \operatorname{J}\left(\operatorname{encode}\left(c\right)\right))) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{coordinateSwap}\left(\operatorname{coordinateSwap}\left(c\right)\right) = c)) \land (\forall c \in \operatorname{Coordinates}\left(a, b\right),\; \neg(\operatorname{coordinateSwap}\left(c\right) = c))) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{encode}\left(\operatorname{coordinateRotate}\left(t, c\right)\right) = \operatorname{markedRotate}\left(t\right)\left(\operatorname{encode}\left(c\right)\right))) \land (\forall t \in \operatorname{Pos}\left(a, b\right),\; \forall c \in \operatorname{Coordinates}\left(a, b\right),\; \operatorname{coordinateRotate}\left(t, \operatorname{coordinateSwap}\left(c\right)\right) = \operatorname{coordinateSwap}\left(\operatorname{coordinateRotate}\left(t, c\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/TwoWallMarked.marked_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The representative of the distance to the other wall determines the first arc length uniquely. Reading and replacing all sites gives both inverse laws. Exchanging the two arcs shifts the starting position by m+1; after the second exchange the displacement is L and therefore zero. The two marks differ, which proves freeness in coordinates. Translation changes only the starting position and commutes with this exchange. All quantifiers include m=0, n=0 and a=b=0.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.Coordinates`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.J`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.Jstar`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.MarkedSpace`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.MarkedWord`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.Q`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.S`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateEquiv`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateRotate`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.coordinateSwap`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.decode`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.encode`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.markedDelta`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.markedRotate`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.markedTranslation`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.markedU`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.marked_coordinates`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.marked_descent`
- Truth anchor: `D5/S3/Quantum/SpinChains/TwoWallMarked.otherWall`
- Dependency: [D5/S3/Quantum/SpinChains/BinaryBinBaseChange](BinaryBinBaseChange.md)
- Dependency: [D5/S3/Quantum/SpinChains/TwoWallWords](TwoWallWords.md)
