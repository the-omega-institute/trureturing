# Simultaneous codes for a full positive window

## Abstract

Binary label codes respect missed vertices and adjacent seam clauses.

A word in Word(d) is a finite set of occupied coordinates in Fin(d); wordBits(w)(i) is the Boolean decision of membership, so membership means bit one. bitCodes(c) maps L to wordBits(c(L)). Fin coordinates are zero based, so source coordinate r is i+1. Clauses(d,Y) has unary(i), extra, and pair(i) owners, with pair(0) unused. A label may own any number of these occurrences. forbidden(C,w) is the union of unary owners at occupied coordinates, extra when coordinate zero is occupied, and pair owners at occupied adjacent coordinates. codeList(C,L) consists of all words not forbidden for L. owners(C) is the image of all displayed occurrences. All implicit label types have decidable equality; FiniteType additionally has a finite enumeration. Proof arguments for positive dimensions and valid indices are suppressed in displayed function applications.

**Theorem 1.1 (Low-weight words prove every subfamily inequality).**

$$\forall Y \in FiniteType,\; \forall d \in \mathbb{N},\; \forall C \in \operatorname{Clauses}\left(d, Y\right),\; \left(\left(2 \le d \land \operatorname{card}\left(Y\right) \le 2^{d}\right) \land \left(3 \le d \lor \left(\operatorname{card}\left(\operatorname{owners}\left(C\right)\right) \le 3 \lor \operatorname{card}\left(Y\right) \le 3\right)\right)\right) \Rightarrow \left(\forall S \in \operatorname{Finset}\left(Y\right),\; \operatorname{card}\left(S\right) \le \operatorname{card}\left(\operatorname{listUnion}\left(C, S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.list_union_inequalities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

listUnion(C,S) is the union of codeList(C,L) over L in S. A label outside owners(C) contributes the entire cube of size 2^d. Otherwise the subfamily has at most 2d labels. Every list contains zero. For two labels the zero word and the units outside coordinate zero give at least d words. For three or more labels every unit lies in the union, since a unit violates at most two owners. For at least d+2 labels in dimension at least three, all words of weight two also lie in the union: they violate at most three unary occurrences and one adjacent pair. Distinct occupied adjacent pairs would require at least three coordinates. The zero, unit and weight-two layers have total size 1+d+choose(d,2), at least 2d for d>=3. The counts use finite powerset layers. The two-dimensional four-owner case is excluded from this regular inequality.

**Theorem 1.2 (List membership is exactly the three source restrictions).**

$$\forall Y \in Type,\; \forall d \in \mathbb{N},\; \forall C \in \operatorname{Clauses}\left(d, Y\right),\; 0 < d \Rightarrow \left(\forall L \in Y,\; \forall w \in \operatorname{Word}\left(d\right),\; w \in \operatorname{codeList}\left(C, L\right) \Leftrightarrow \left(\left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{unary}\left(C, i\right) = L \Rightarrow \left(\neg i \in w\right)\right) \land \left(\operatorname{extra}\left(C\right) = L \Rightarrow \left(\neg 0 \in w\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \left(0 < \operatorname{val}\left(i\right) \land \operatorname{pair}\left(C, i\right) = L\right) \Rightarrow \left(\left(\neg i \in w\right) \lor \left(\neg \operatorname{prev}\left(i\right) \in w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.mem_codeList_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unary owner forces its own coordinate to zero. The extra owner forces coordinate zero to zero. Each pair owner at i>0 forces one of i and prev(i) to zero, where prev(i) has value val(i)-1. Repeated labels collect all these conditions.

**Theorem 1.3 (The clauses use the actual ordered window vertices).**

$$\forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; 2 \cdot d \le m + 1 \Rightarrow \left(\forall i \in \operatorname{Fin}\left(d\right),\; \left(\left(\left(\forall j \in \operatorname{ZMod}\left(m + 2\right),\; j \in \operatorname{sourceWindow}\left(m, \operatorname{val}\left(i\right) + 1\right) \Leftrightarrow j \ne \operatorname{cast}\left(\operatorname{val}\left(\operatorname{missedVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right) \land \operatorname{cast}\left(m + 1, \operatorname{ZMod}\left(m + 2\right)\right) \in \operatorname{sourceWindow}\left(m, \operatorname{val}\left(i\right) + 1\right)\right) \land \operatorname{cast}\left(\left(\operatorname{val}\left(i\right) + 1\right) \cdot m, \operatorname{ZMod}\left(m + 2\right)\right) = \operatorname{cast}\left(\operatorname{val}\left(\operatorname{seamVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right) \land \operatorname{cast}\left(\operatorname{val}\left(i\right) \cdot m + m, \operatorname{ZMod}\left(m + 2\right)\right) = \operatorname{cast}\left(\operatorname{val}\left(\operatorname{seamVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.source_window_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sourceWindow(m,r) is the image of r*m+h, for 0<=h<=m, in ZMod(m+2). missedVertex(m,d,i) has value m+1-2*(i+1), and seamVertex has value m+2-2*(i+1). Translation of the m+1 consecutive offsets misses exactly the vertex immediately before its start. The period identity m=-2 identifies that vertex with missedVertex. The donor m+1 is present in every window and outside the child table. For r>=2 the preceding window ends at (r-1)*m+m=r*m, the very start of this window. Rotation by the known already-issued offset a*m turns the absolute window at a+r into this same sourceWindow.

**Theorem 1.4 (Every actual label receives a distinct lawful or exceptional word).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall table \in \operatorname{Fin}\left(m + 1\right) \to Y,\; \left(\operatorname{Odd}\left(m\right) \land 3 \le \operatorname{card}\left(\operatorname{labels}\left(table\right)\right)\right) \Rightarrow \left(\forall d \in \mathbb{N},\; d = \operatorname{clog}\left(2, \operatorname{card}\left(\operatorname{labels}\left(table\right)\right)\right) \Rightarrow \left(\left(2 \cdot d \le m + 1 \land 2 \le d\right) \land \left(\exists c \in \operatorname{Label}\left(table\right) \to \operatorname{Word}\left(d\right),\; \left(\left(\left(\left(\operatorname{Injective}\left(c\right) \land \operatorname{Injective}\left(\operatorname{bitCodes}\left(c\right)\right)\right) \land \left(\left(\forall L \in \operatorname{Label}\left(table\right),\; c\left(L\right) \in \operatorname{codeList}\left(\operatorname{sourceClauses}\left(table, d\right), L\right)\right) \lor \left(\left(\left(\left(\left(\left(\left(d = 2 \land \operatorname{card}\left(\operatorname{Label}\left(table\right)\right) = 4\right) \land \operatorname{Injective}\left(\operatorname{fourOwners}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{castCodes}\left(2, c\right)\left(\operatorname{fourOwner}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right), i\right)\right) = \operatorname{fourWords}\left(i\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(2\right),\; \neg i \in \operatorname{castCodes}\left(2, c\right)\left(\operatorname{unary}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right), i\right)\right)\right)\right) \land \left(\neg 0 \in \operatorname{castCodes}\left(2, c\right)\left(\operatorname{extra}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right)\right)\right)\right)\right) \land 0 \in \operatorname{castCodes}\left(2, c\right)\left(\operatorname{pair}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right), 1\right)\right)\right) \land 1 \in \operatorname{castCodes}\left(2, c\right)\left(\operatorname{pair}\left(\operatorname{castClauses}\left(2, \operatorname{sourceClauses}\left(table, d\right)\right), 1\right)\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \neg i \in c\left(\operatorname{unary}\left(\operatorname{sourceClauses}\left(table, d\right), i\right)\right)\right)\right) \land \left(\neg 0 \in c\left(\operatorname{extra}\left(\operatorname{sourceClauses}\left(table, d\right)\right)\right)\right)\right) \land \left(\left(\left(\left(\forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{ZMod}\left(m + 2\right),\; j \in \operatorname{sourceWindow}\left(m, \operatorname{val}\left(i\right) + 1\right) \Leftrightarrow j \ne \operatorname{cast}\left(\operatorname{val}\left(\operatorname{missedVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{cast}\left(m + 1, \operatorname{ZMod}\left(m + 2\right)\right) \in \operatorname{sourceWindow}\left(m, \operatorname{val}\left(i\right) + 1\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{cast}\left(\left(\operatorname{val}\left(i\right) + 1\right) \cdot m, \operatorname{ZMod}\left(m + 2\right)\right) = \operatorname{cast}\left(\operatorname{val}\left(\operatorname{seamVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{cast}\left(\operatorname{val}\left(i\right) \cdot m + m, \operatorname{ZMod}\left(m + 2\right)\right) = \operatorname{cast}\left(\operatorname{val}\left(\operatorname{seamVertex}\left(m, d, i\right)\right), \operatorname{ZMod}\left(m + 2\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.actual_table_codes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

table is the original label map on every vertex 0 through m of the rotated full positive child. labels(table) is its full image, and Label(table) is the type of members of that image, including unrestricted labels. sourceClauses(table,d) assigns the unary owner table(missedVertex(i)), extra owner table(m), and pair owner table(seamVertex(i)). No code or matching is assumed. clog(2,n) is the least natural d with n<=2^d. The table has at most m+1 labels; odd m and 2*q<=2^q for q>=1 imply 2*d<=m+1, while n>=3 implies d>=2. The finite Hall theorem supplies the injective choice from the proved list inequalities.

The displayed Selected condition expands as the disjunction of regular list membership and the explicit second branch. castClauses and castCodes transport along d=2. fourOwners(C) enumerates unary(0), extra, unary(1), pair(1); fourOwner(C,i) is its value. These are exactly LA=table(m-1), LB=table(m), LC=table(m-3), LD=table(m-2). fourWords enumerates the occupied sets empty, {1}, {0}, {0,1}, hence the source words 00,01,10,11. In the second branch there are exactly four labels and these four owners are distinct. All unary and first-bit restrictions hold, while LD has both adjacent bits one. That branch does not satisfy the regular pair clause.

This result selects simultaneous codes and identifies their source vertices. Even rotated charge rows, their compensation at the donor, the native endpoint inverse, the exceptional physical seam and a full INITIAL decoder require further integration. No price or GLOBAL controller conclusion follows from code selection alone.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.actual_table_codes`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.list_union_inequalities`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.mem_codeList_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes.source_window_vertices`
