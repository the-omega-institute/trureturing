# The Unique Short-Cut Normal Form for Word Conjugacy

## Abstract

Classify every conjugating word by a unique literal exponent and short cut.

**Theorem 1.1 (A fixed conjugating word determines the entire normal-form triple).**

$$\forall u \in Universe,\; \forall A \in \operatorname{Type}\left(u\right),\; \forall a \in \operatorname{List}\left(A\right),\; \forall b \in \operatorname{List}\left(A\right),\; \forall z \in \operatorname{List}\left(A\right),\; (a \ne \operatorname{nil}\left(\right)) \Rightarrow ((\operatorname{append}\left(a, z\right) = \operatorname{append}\left(z, b\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; \exists p \in \operatorname{List}\left(A\right),\; \exists q \in \operatorname{List}\left(A\right),\; ((a = \operatorname{append}\left(p, q\right)) \land ((b = \operatorname{append}\left(q, p\right)) \land ((z = \operatorname{append}\left(\operatorname{wordPower}\left(n, a\right), p\right)) \land (\operatorname{length}\left(p\right) < \operatorname{length}\left(a\right))))) \land (\forall m \in \mathbb{N},\; \forall r \in \operatorname{List}\left(A\right),\; \forall s \in \operatorname{List}\left(A\right),\; ((a = \operatorname{append}\left(r, s\right)) \land ((b = \operatorname{append}\left(s, r\right)) \land ((z = \operatorname{append}\left(\operatorname{wordPower}\left(m, a\right), r\right)) \land (\operatorname{length}\left(r\right) < \operatorname{length}\left(a\right))))) \Rightarrow ((m = n) \land ((r = p) \land (s = q))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every universe u, every alphabet A in Type u, and all finite words a, b and z over A with a nonempty, the equation append(a,z)=append(z,b) holds exactly when there is a unique triple (n,p,q) satisfying a=append(p,q), b=append(q,p), z=append(wordPower(n,a),p) and length(p)<length(a). Uniqueness compares every competing exponent, prefix and suffix for these same a, b and z. It does not assert a unique cut from a and b alone.

Words are ordinary List A values. Concatenation is List.append, and wordPower(n,a) is the existing flatten(replicate(n,a)); no new word carrier or power operation is introduced. The alphabet needs no finiteness, order, inhabitedness or decidable equality. Empty and infinite alphabets remain quantified. Zero exponents, empty z and empty p are included. The short-cut inequality and a=pq force q nonempty, and hence b nonempty; neither is an additional premise. The word a need not be primitive.

Omega.FreeMonoid.Conjugacy supplies the reusable mathematics for an arbitrary carrier with associative concatenation, left identity and cancellation, additive natural length, length-directed prefix splitting, and the zero and successor power equations. These are elementary operation laws, with no classification hypothesis. If z is at least as long as a, prefix splitting removes one complete a and produces a strictly shorter conjugating word. Strong induction therefore reaches a short prefix. If z is already short, splitting produces its complementary suffix directly, with exponent zero.

For uniqueness, cancel complete initial copies of a from two power representations. A zero exponent cannot match a positive exponent because a short prefix cannot start with an entire a. Thus the exponents and literal short prefixes agree. Cancellation in the two factorizations of a then identifies the suffixes. A separate induction proves the converse conjugacy equation for every normal form.

The List interpretation proves every operation law, transports strict and ordinary natural numbers in both directions, and proves equivalence of the abstract normal predicate with all four displayed List clauses. The D5 declaration is the publication citation for this entry; its mathematics belongs to Omega.FreeMonoid.Conjugacy. It uses the proved existence, soundness and uniqueness results without repeating their length-descent proof.

Karhumaki's TUCS TR645, Section 5, Example 5, printed p. 12 / PDF p. 16, states the classical general solution x=rs, y=sr, z=r(sr)^i for i>=0. The identity (rs)^i r=r(sr)^i relates its convention to the displayed one. The report starts with a finite alphabet and does not state this fixed-z unique short-cut normalization. The arbitrary-alphabet scope and whole-triple uniqueness are proved here. The linked source note records that boundary; no original mathematical novelty is claimed.

`D5/L/Automata/karhumaki2004words`

## References

- Truth anchor: `D5/S1/Words/Powers/ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut`
