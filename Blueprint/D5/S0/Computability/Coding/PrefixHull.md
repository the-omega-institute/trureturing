# Finite prefix bases for least right-unitary word monoids

## Abstract

A finite labelled word family has a finite prefix basis for its least right-unitary submonoid, with exact coefficients and no increase in label count.

Let alpha be a type in an arbitrary universe, n a natural number, and f : Fin n -> List alpha a labelled family of finite words. A containing right-unitary monoid is a set M of words containing the empty word and every f(i), closed under concatenation, and satisfying: if x belongs to M and x ++ y belongs to M, then y belongs to M. The least hull H is the literal intersection of every such M. Right unitarity requires membership of the left factor; it is not closure under arbitrary suffixes.

IsPrefix(x,y) means that x ++ r = y for some word r, including the empty residual. For g : Fin m -> List alpha and a coefficient word s over Fin m, flatMap(g,s) concatenates the g-labelled words in order. The empty coefficient word evaluates to the empty word.

**Theorem 1.1 (Exact bounded prefix basis of the least hull).**

$$\forall alpha \in \mathrm{Type}^{*},\; \forall n \in \mathrm{Nat},\; \forall f \in (\operatorname{Fin}\left(n\right) \to \operatorname{List}\left(alpha\right)),\; \exists m \in \mathrm{Nat},\; m \le n \land \left(\exists g \in (\operatorname{Fin}\left(m\right) \to \operatorname{List}\left(alpha\right)),\; \exists c \in (\operatorname{Fin}\left(n\right) \to \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right)),\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{g}\left(i\right) \neq []\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{IsPrefix}\left(\operatorname{g}\left(i\right), \operatorname{g}\left(j\right)\right) \Rightarrow i = j\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{f}\left(i\right) = \operatorname{flatMap}\left(g, \operatorname{c}\left(i\right)\right)\right) \land \left(\forall w \in \operatorname{List}\left(alpha\right),\; \left(\forall M \in \operatorname{Set}\left(\operatorname{List}\left(alpha\right)\right),\; [] \in M \Rightarrow \left(\left(\forall x \in \operatorname{List}\left(alpha\right),\; \forall y \in \operatorname{List}\left(alpha\right),\; x \in M \Rightarrow \left(y \in M \Rightarrow \operatorname{append}\left(x, y\right) \in M\right)\right) \Rightarrow \left(\left(\forall x \in \operatorname{List}\left(alpha\right),\; \forall y \in \operatorname{List}\left(alpha\right),\; x \in M \Rightarrow \left(\operatorname{append}\left(x, y\right) \in M \Rightarrow y \in M\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{f}\left(i\right) \in M\right) \Rightarrow w \in M\right)\right)\right)\right) \Leftrightarrow \left(\exists s \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; w = \operatorname{flatMap}\left(g, s\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Coding/PrefixHull.finite_prefix_basis_least_right_unitary_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct the generators by induction on the label count and strong induction on total word length. Besides nonemptiness, prefix separation and exact coefficients, retain the invariant that every returned generator belongs to every admissible containing monoid of the current family. Deleting an empty label preserves this invariant because every admissible monoid contains the empty word.

If the nonempty labelled family is prefix-separated, return it with singleton coefficients. Otherwise choose distinct labels i,j with f(i) ++ r = f(j) and replace the word at j by r. Since f(i) is nonempty, total length strictly decreases. Every admissible containing monoid contains r by right unitarity. The reverse containment condition follows by concatenation, so the local replacement preserves admissible containing monoids. Transport coefficients by the substitution taking j to [i,j] and every other label k to [k], then compose using flatMap.

For the terminal generators g, let L be all flatMap(g,s). It contains the empty word and every input, and is closed under concatenation. To prove right unitarity, suppose flatMap(g,s) ++ y = flatMap(g,t) for an arbitrary word y. Induct on s. When s is nonempty, t cannot be empty because all generators are nonempty. The first generators on the two sides are comparable prefixes of the same word, so prefix separation identifies their labels. Cancel that common generator and apply the induction. Thus y also belongs to L.

Since L is an admissible containing monoid, intersection membership implies membership in L. Conversely, the retained invariant puts each generator in every admissible containing monoid, and closure under concatenation puts every word of L in each such monoid. This proves equality with the literal least hull, together with the exact factorization of every original labelled input.

No finiteness, inhabitedness or decidable equality assumption on alpha is needed. Empty alphabets, n = 0, m = 0, empty input words and duplicate labels are included. Nonempty means that each generator word is nonempty; the generator family may be empty. The theorem asserts m <= n and does not assert minimum cardinality, a complexity bound or a converse characterization.

## References

- Truth anchor: `D5/S0/Computability/Coding/PrefixHull.finite_prefix_basis_least_right_unitary_hull`
