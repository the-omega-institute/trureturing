# Type-II Factors at Positive Substitution Cuts

## Abstract

Actual Type-II occurrences and complete return vectors in the seven-letter source word.

The alphabet is Fin 7 and the substitution is phi(a)=[0,a+1] for a<6, with phi(6)=[0,6,6]. All words, occurrences, extensions, boundaries, incidence columns and half-open return intervals are those of RichWordTypeIOccurrence. Consecutiveness permits overlapping occurrence windows. The auxiliary index k always denotes original source index n=k+6; indices below six specify the factor-count recurrence and are not asserted to have the Type-II return theorem.

**Definition 1.1 (Sentinel prefixes).**

$$F\left(0\right) = nil \land \left(\forall k \in \mathbb{N},\; F\left(k + 1\right) = sentinel\left(F\left(k\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(0) is empty and F(k+1)=phi(F(k))[0]. Its occurrences at every natural position are exactly the iterated cuts cut(k,i), including the origin. After k sentinel steps both contexts are obtained by iterating a map that sends a<6 to a+1 and fixes 6. Five iterations send 0 to 5 and every other letter to 6.

**Definition 1.2 (Iterated native boundaries).**

$$\forall i \in \mathbb{N},\; cut\left(0, i\right) = i \land \left(\forall k \in \mathbb{N},\; cut\left(k + 1, i\right) = boundary\left(cut\left(k, i\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cut(0,i)=i and cut(k+1,i)=boundary(cut(k,i)). These maps are strictly increasing, fix zero, and carry positive indices to positive positions. The interval between cut(k,i) and cut(k,i+1) is literally the kth image of the actual letter u(i).

**Definition 1.3 (The literal cyclic factor recurrence).**

$$typeII\left(0\right) = nil \land \left(\forall n \in \mathbb{N},\; typeII\left(n + 1\right) = ite\left(mod\left(n, 6\right) = 5, terminal\left(typeII\left(n\right)\right), sentinel\left(typeII\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.typeII` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(0) is empty. At phases other than 5 modulo 6, append a sentinel zero to phi(W(n)). At phase 5 use [6]phi(W(n))[0,6]. Thus W(6)=6 F(6) 6, has length 65 and Parikh vector (32,16,8,4,2,1,2). Both extra terminal-coordinate units are present. Reversal commutes with the sentinel construction, and the terminal construction wraps it in two equal letters, so all W(n) are palindromes.

**Definition 1.4 (Exact source count recurrence).**

$$f\left(0\right) = 0 \land \left(\forall n \in \mathbb{N},\; f\left(n + 1\right) = mulVec\left(M, f\left(n\right)\right) + increment\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial vector is zero and f(n+1)=M f(n)+increment(n). Here increment(n) is e(0)+2e(6) at phase 5 and e(0) otherwise. Letter counting on the literal word recurrence proves P(W(n))=f(n) at every auxiliary and actual index.

**Definition 1.5 (Positive-cut occurrence enumeration).**

$$\forall i \in \mathbb{N},\; position\left(0, i\right) = cut\left(6, i\right) - 1 \land \left(\forall k \in \mathbb{N},\; position\left(k + 1, i\right) = occurrenceMap\left(k + 6, position\left(k, i\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

position(0,i)=cut(6,i)-1 and position(k+1,i)=occurrenceMap(k+6,position(k,i)). The valid source indices are exactly i>0. The natural subtraction at i=0 does not create an occurrence: the initial F(5) occurrence has no preceding letter and is discarded by the first terminal wrap.

**Definition 1.6 (The complete native contract).**

$$\forall k \in \mathbb{N},\; NativeData\left(k\right) \Leftrightarrow \left(0 < length\left(typeII\left(k + 6\right)\right) \land \left(reverse\left(typeII\left(k + 6\right)\right) = typeII\left(k + 6\right) \land \left(parikh\left(typeII\left(k + 6\right)\right) = f\left(k + 6\right) \land \left(StrictMono\left(position\left(k\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow 0 < position\left(k, i\right)\right) \land \left(\left(\forall q \in \mathbb{N},\; Occ\left(typeII\left(k + 6\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; \left(0 < i \land q = position\left(k, i\right)\right) \land \left(\forall j \in \mathbb{N},\; \left(0 < j \land q = position\left(k, j\right)\right) \Rightarrow j = i\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow \left(word\left(position\left(k, i\right) - 1\right) = ite\left(word\left(i - 1\right) = 0, phase\left(k + 6\right), 6\right) \land word\left(position\left(k, i\right) + length\left(typeII\left(k + 6\right)\right)\right) = ite\left(word\left(i\right) = 0, phase\left(k + 6\right), 6\right)\right)\right) \land \left(\left(word\left(position\left(k, 1\right) - 1\right) = phase\left(k + 6\right) \land \left(word\left(position\left(k, 1\right) + length\left(typeII\left(k + 6\right)\right)\right) = 6 \land \left(word\left(position\left(k, 2\right) - 1\right) = 6 \land word\left(position\left(k, 2\right) + length\left(typeII\left(k + 6\right)\right)\right) = phase\left(k + 6\right)\right)\right)\right) \land \left(\left(Lext\left(typeII\left(k + 6\right)\right) = pair\left(phase\left(k + 6\right), 6\right) \land Rext\left(typeII\left(k + 6\right)\right) = pair\left(phase\left(k + 6\right), 6\right)\right) \land \left(\left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeII\left(k + 6\right), a, b\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; \left(0 < i \land \left(a = position\left(k, i\right) \land b = position\left(k, i + 1\right)\right)\right) \land \left(\forall j \in \mathbb{N},\; \left(0 < j \land \left(a = position\left(k, j\right) \land b = position\left(k, j + 1\right)\right)\right) \Rightarrow j = i\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow returnWord\left(position\left(k + 1, i\right), position\left(k + 1, i + 1\right)\right) = ite\left(mod\left(k + 6, 6\right) = 5, cons\left(6, dropLast\left(subst\left(phi, returnWord\left(position\left(k, i\right), position\left(k, i + 1\right)\right)\right)\right)\right), subst\left(phi, returnWord\left(position\left(k, i\right), position\left(k, i + 1\right)\right)\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow \left(mod\left(k + 6, 6\right) = 5 \Rightarrow \left(\exists y \in List\left(Fin\left(7\right)\right),\; subst\left(phi, returnWord\left(position\left(k, i\right), position\left(k, i + 1\right)\right)\right) = append\left(y, singleton\left(6\right)\right)\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow factor\left(word, position\left(k, i\right), position\left(k, i + 1\right) - position\left(k, i\right) + length\left(typeII\left(k + 6\right)\right)\right) = append\left(returnWord\left(position\left(k, i\right), position\left(k, i + 1\right)\right), typeII\left(k + 6\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow parikh\left(returnWord\left(position\left(k, i\right), position\left(k, i + 1\right)\right)\right) = mulVec\left(pow\left(M, k + 6\right), unit\left(word\left(i\right)\right)\right)\right) \land \left(\left(\forall i \in \mathbb{N},\; 0 < i \Rightarrow returnWord\left(position\left(0, i\right), position\left(0, i + 1\right)\right) = cons\left(6, dropLast\left(image\left(phi, 6, word\left(i\right)\right)\right)\right)\right) \land \left(\left(Consecutive\left(typeII\left(k + 6\right), position\left(k, 2\right), position\left(k, 3\right)\right) \land \left(parikh\left(returnWord\left(position\left(k, 2\right), position\left(k, 2 + 1\right)\right)\right) = mulVec\left(pow\left(M, k + 6\right), unit\left(0\right)\right) \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; Consecutive\left(typeII\left(k + 6\right), a, b\right) \Rightarrow le\left(mulVec\left(pow\left(M, k + 6\right), unit\left(0\right)\right), parikh\left(returnWord\left(a, b\right)\right)\right)\right)\right)\right) \land \left(\left(\forall v \in Function\left(Fin\left(7\right), \mathbb{N}\right),\; \left(\exists a \in \mathbb{N},\; \exists b \in \mathbb{N},\; Consecutive\left(typeII\left(k + 6\right), a, b\right) \land parikh\left(returnWord\left(a, b\right)\right) = v\right) \Leftrightarrow \left(\exists c \in Fin\left(7\right),\; mulVec\left(pow\left(M, k + 6\right), unit\left(c\right)\right) = v\right)\right) \land \left(typeII\left(6\right) = cons\left(6, append\left(F\left(6\right), singleton\left(6\right)\right)\right) \land \left(length\left(typeII\left(6\right)\right) = 65 \land \left(parikh\left(typeII\left(6\right)\right) = vector\left(32, 16, 8, 4, 2, 1, 2\right) \land \left(position\left(0, 2\right) = 128 \land \left(position\left(0, 3\right) = 192 \land returnWord\left(position\left(0, 2\right), position\left(0, 3\right)\right) = cons\left(6, F\left(6\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordTypeIIOccurrence.NativeData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each offset k, this proposition records a nonempty palindromic actual factor, its exact count vector, a strictly increasing positive enumeration of all occurrences, both actual context formulas, both exact extension sets, and a unique adjacent-index description of all consecutive pairs. It also records the literal ordinary or terminal return-word update, all seven return counts, attainment by indices 2 and 3, domination of that vector by every consecutive return, the complete seven-column set of attained return vectors, and the explicit wrapped seed and overlapping return at 128 and 192.

**Theorem 1.7 (Every original index at least six).**

$$\forall n \in \mathbb{N},\; le\left(6, n\right) \Rightarrow NativeData\left(n - 6\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordTypeIIOccurrence.actual_typeII` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least six, NativeData(n-6) holds. The seed recognizer first desubstitutes five sentinels. Its two contexts lie in {5,6}; terminal recognition therefore retains precisely the positive cuts. At subsequent ordinary phases contexts advance by one, and at terminal phases 5 becomes 0 while 6 remains 6. All occurrences are transported in both directions, so adjacent source indices give exactly the consecutive occurrences. Ordinary return intervals are substituted literally; terminal intervals prepend 6 and delete the final 6 of the substituted interval, whose final letter is explicitly proved to be 6. The complete Parikh vector is unchanged by this cancellation. Hence the return at index i has vector M^(k+6)e(u(i)). The first sixfold image of 0 is a prefix of every sixfold letter image; applying further substitutions preserves this prefix and proves all-coordinate domination. The actual letters u(0),u(1),u(2) are 0,1,0, so starts 1 and 2 give context pairs (phase,6) and (6,phase), and the return at index 2 attains the minimum. Every letter occurs at a positive source index, giving every listed return vector. At the seed the attaining interval is [128,192), with return word 6F(6); its two length-65 occurrences overlap in one letter. This supplies the Type-II source factor and return statements. It does not assert an output exponent bound or classify other bispecial factors.

## References

- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.F`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.NativeData`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.actual_typeII`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.cut`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.f`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.position`
- Truth anchor: `D5/S1/Words/RichWordTypeIIOccurrence.typeII`
- Dependency: [D5/S1/Words/RichWordTypeIOccurrence](RichWordTypeIOccurrence.md)
