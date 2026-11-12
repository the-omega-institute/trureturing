# Literal Marker Decoding and Actual Returns

## Abstract

Exact four-letter marker decoding and attained return minima for the actual seven-letter source.

The input is precisely RichWordTypeIOccurrence.word on Fin 7. Output letters 0,1,2,3 denote a,b,c,d. The dictionary is (a,ab,abb,ac,acc,accdcc,accdccddccdcc), with image lengths (1,2,3,2,3,6,13). Every image begins with its only a; its remaining tail q is marker-free, and the seven tails are distinct, including the empty q(0). No recurrence, context or universality hypothesis is imposed on the source. E is the cumulative image length, and x reads each letter from its unique interval E(j) <= p < E(j+1). Thus x is the actual one-sided eta(u).

**Theorem 1.1 (All-length source reconstruction).**

$$\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(7\right)\right),\; \forall j \in \mathbb{N},\; \operatorname{Occ}\left(\operatorname{append}\left(\operatorname{subst}\left(\operatorname{eta}, w\right), \operatorname{singleton}\left(0\right)\right), \operatorname{E}\left(j\right)\right) \Rightarrow \operatorname{sourceOcc}\left(w, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordOutputDecoder.marked_core_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occurrence of eta(w)a at the actual boundary E(j) reconstructs the whole source window w. The induction compares the next target marker with the next actual boundary. Either unequal distance would place a marker inside a marker-free image tail. Equality of the actual intervening words then identifies the source letter by dictionary injectivity; equal lengths alone do not identify letters. The empty core is included.

**Theorem 1.2 (The exact filtered occurrence decoder).**

$$\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(7\right)\right),\; \forall s \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall t \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall A \in \mathbb{N},\; \operatorname{markerFree}\left(s\right) \Rightarrow \left(\operatorname{markerFree}\left(t\right) \Rightarrow \left(\operatorname{Occ}\left(\operatorname{append}\left(\operatorname{append}\left(\operatorname{append}\left(s, \operatorname{subst}\left(\operatorname{eta}, w\right)\right), \operatorname{singleton}\left(0\right)\right), t\right), A\right) \Leftrightarrow \left(\exists j \in \mathbb{N},\; \left(A + \operatorname{length}\left(s\right) = \operatorname{E}\left(j\right) \land \left(\operatorname{sourceOcc}\left(w, j\right) \land \left(\operatorname{Left}\left(s, j\right) \land \operatorname{Right}\left(t, w, j\right)\right)\right)\right) \land \left(\forall z \in \mathbb{N},\; \left(A + \operatorname{length}\left(s\right) = \operatorname{E}\left(z\right) \land \left(\operatorname{sourceOcc}\left(w, z\right) \land \left(\operatorname{Left}\left(s, z\right) \land \operatorname{Right}\left(t, w, z\right)\right)\right)\right) \Rightarrow z = j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordOutputDecoder.occurrence_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

markerFree(z) means 0 is not a member of z. Left(s,j) means s is empty, or j is positive and s is a suffix of q(u(j-1)). Right(t,w,j) means t is a prefix of q(u(j+length(w))). Both decorations are marker-free. The first marker determines a unique source index, the core reconstruction determines w, and the two actual boundary tails determine the filters. Empty s permits the origin. An empty core has coincident first and last highlighted markers. Adjacent markers from eta(0)=a and overlapping windows are retained.

**Definition 1.3 (Exact transport and attained minimum).**

$$\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(7\right)\right),\; \forall s \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall t \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall m \in \operatorname{Fin}\left(7\right) \to \mathbb{N},\; \operatorname{Transport}\left(w, s, t, m\right) \Leftrightarrow \left(\left(\forall A \in \mathbb{N},\; \operatorname{Occ}\left(\operatorname{decorated}\left(w, s, t\right), A\right) \Leftrightarrow \left(\exists j \in \mathbb{N},\; \left(A + \operatorname{length}\left(s\right) = \operatorname{E}\left(j\right) \land \operatorname{sourceOcc}\left(w, j\right)\right) \land \left(\forall z \in \mathbb{N},\; \left(A + \operatorname{length}\left(s\right) = \operatorname{E}\left(z\right) \land \operatorname{sourceOcc}\left(w, z\right)\right) \Rightarrow z = j\right)\right)\right) \land \left(\left(\forall A \in \mathbb{N},\; \forall B \in \mathbb{N},\; \operatorname{Consecutive}\left(\operatorname{decorated}\left(w, s, t\right), A, B\right) \Leftrightarrow \left(\exists j \in \mathbb{N},\; \exists k \in \mathbb{N},\; A + \operatorname{length}\left(s\right) = \operatorname{E}\left(j\right) \land \left(B + \operatorname{length}\left(s\right) = \operatorname{E}\left(k\right) \land \operatorname{sourceConsecutive}\left(w, j, k\right)\right)\right)\right) \land \left(\left(\forall A \in \mathbb{N},\; \forall B \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall k \in \mathbb{N},\; A + \operatorname{length}\left(s\right) = \operatorname{E}\left(j\right) \Rightarrow \left(B + \operatorname{length}\left(s\right) = \operatorname{E}\left(k\right) \Rightarrow \left(j \le k \Rightarrow B - A = \operatorname{W}\left(\operatorname{parikh}\left(\operatorname{returnWord}\left(j, k\right)\right)\right)\right)\right)\right) \land \left(\left(\exists A \in \mathbb{N},\; \exists B \in \mathbb{N},\; \exists j \in \mathbb{N},\; \exists k \in \mathbb{N},\; \operatorname{Consecutive}\left(\operatorname{decorated}\left(w, s, t\right), A, B\right) \land \left(A + \operatorname{length}\left(s\right) = \operatorname{E}\left(j\right) \land \left(B + \operatorname{length}\left(s\right) = \operatorname{E}\left(k\right) \land \left(\operatorname{sourceConsecutive}\left(w, j, k\right) \land \left(\operatorname{parikh}\left(\operatorname{returnWord}\left(j, k\right)\right) = m \land B - A = \operatorname{W}\left(m\right)\right)\right)\right)\right)\right) \land \left(\forall A \in \mathbb{N},\; \forall B \in \mathbb{N},\; \operatorname{Consecutive}\left(\operatorname{decorated}\left(w, s, t\right), A, B\right) \Rightarrow \operatorname{W}\left(m\right) \le B - A\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/RichWordOutputDecoder.Transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposition records all output occurrences as the entire source occurrence set, exact consecutive-pair correspondence, the weighted length of every corresponding return interval, and attainment plus universal domination of the minimum output gap. decorated(w,s,t) is s eta(w) a t, of length W(parikh(w))+1+length(s)+length(t). For s=t=r(n), the six boundary contributions are (1,1,1,3,5,11). sourceOcc(w,j) means the actual source window u[j,j+length(w)) equals w. sourceConsecutive is the same source predicate as RichWordTypeIOccurrence.Consecutive. Consecutive means strictly increasing starts with no intervening occurrence, with no nonoverlap condition. W(v) is the sum of image-length(c) times v(c) over all seven letters. Source returnWord(j,k) is the actual interval u[j,k). The return gap has no added decoration length.

**Theorem 1.4 (Every original Type-I index).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall t \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \operatorname{suffix}\left(s, \operatorname{r}\left(n\right)\right) \Rightarrow \left(\operatorname{prefix}\left(t, \operatorname{r}\left(n\right)\right) \Rightarrow \operatorname{Transport}\left(\operatorname{typeI}\left(n\right), s, t, \operatorname{mulVec}\left(\operatorname{pow}\left(\operatorname{M}, n\right), \operatorname{unit}\left(6\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordOutputDecoder.typeI_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n >= 0, use any suffix s of r(n) and prefix t of r(n), where the six phase values are (empty,empty,empty,c,cc,ccdcc). The source theorem typeI_not_at_origin and the exact witnessed extension sets supply both actual neighbor letters in {n mod 6,6}; both admit r(n). Every source occurrence is therefore retained. The attained componentwise minimum M^n e(6) transfers to the least output return length W(M^n e(6)).

**Theorem 1.5 (Original Type-II indices at least six).**

$$\forall n \in \mathbb{N},\; 6 \le n \Rightarrow \left(\forall s \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \forall t \in \operatorname{List}\left(\operatorname{Fin}\left(4\right)\right),\; \operatorname{suffix}\left(s, \operatorname{r}\left(n\right)\right) \Rightarrow \left(\operatorname{prefix}\left(t, \operatorname{r}\left(n\right)\right) \Rightarrow \operatorname{Transport}\left(\operatorname{typeII}\left(n\right), s, t, \operatorname{mulVec}\left(\operatorname{pow}\left(\operatorname{M}, n\right), \operatorname{unit}\left(0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordOutputDecoder.typeII_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For original n >= 6 and any suffix s and prefix t of r(n), actual_typeII(n) supplies NativeData(n-6). Its occurrence enumeration and positivity exclude the origin, and its actual context formulas supply both neighbors. Rewriting (n-6)+6=n preserves the original phase and matrix exponent. The attained vector M^n e(0), at source indices position(n-6,2) and position(n-6,3), transfers to the attained output minimum. No Type-II return assertion is made below six.

The interval identity reuses the original morphic_block helper after an injective encoding of the four output letters into integers; this helper has no UniversalInput premise. All source occurrences, consecutive returns and attained vector minima are reused from the source occurrence theorems. The source scalar inequalities (50), the all-factor ordinary critical-exponent criterion and classification, recurrence and aperiodicity hypotheses for that criterion, and the lower bound are separate inputs. This result does not prove the scalar inequalities or a full ordinary critical exponent.

## References

- Truth anchor: `D5/S1/Words/RichWordOutputDecoder.Transport`
- Truth anchor: `D5/S1/Words/RichWordOutputDecoder.marked_core_recovery`
- Truth anchor: `D5/S1/Words/RichWordOutputDecoder.occurrence_decoder`
- Truth anchor: `D5/S1/Words/RichWordOutputDecoder.typeII_transport`
- Truth anchor: `D5/S1/Words/RichWordOutputDecoder.typeI_transport`
- Dependency: [D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism](Complexity/SahasrabudheEvenAdditiveComplexityMorphism.md)
- Dependency: [D5/S1/Words/RichWordTypeIIOccurrence](RichWordTypeIIOccurrence.md)
