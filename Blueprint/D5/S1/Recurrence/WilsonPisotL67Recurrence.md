# Wilson's Pisot Sequence L(6,7)

## Abstract

The native rational-ceiling sequence L(6,7) has positive terms and obeys Wilson's signed recurrence at every index at least four.

David W. Wilson's OEIS A048585, revision 18, defines L(6,7) by ordinary upward ceiling and states the four-lag recurrence as holding through index 50000 but unknown in general. The fixed source is https://raw.githubusercontent.com/oeis/oeisdata/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A048/A048585.seq . The elementary proof below follows the preexisting public outline at https://github.com/the-omega-institute/trureturing/issues/21793 . This attribution makes no priority claim beyond that project source.

All indices are natural numbers and all sequence values are integers. The notation rat casts an integer to the rational numbers before division. The function ceil is the least integer greater than or equal to its rational argument; an integer argument stays unchanged. Subtraction of sequence values is integer subtraction; subtraction inside an index is natural subtraction.

**Definition 1.1 (The defining ceiling recursion).**

$$(\operatorname{a}\left(0\right) = 6) \land ((\operatorname{a}\left(1\right) = 7) \land (\forall (n: \mathbb{N}), \operatorname{a}\left(n + 2\right) = \operatorname{ceil}\left(\frac{(\operatorname{rat}\left(\operatorname{a}\left(n + 1\right)\right))^{2}}{\operatorname{rat}\left(\operatorname{a}\left(n\right)\right)}\right)))$$

*Formalization.* `D5/S1/Recurrence/WilsonPisotL67Recurrence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial values are six and seven. Every later value is obtained from the preceding two by the displayed rational quotient and upward ceiling. No linear recurrence or auxiliary identification is assumed in this definition.

**Theorem 1.2 (Positivity and the full four-lag recurrence).**

$$(\forall (n: \mathbb{N}), 0 < \operatorname{a}\left(n\right)) \land (\forall (n: \mathbb{N}), (4 \le n) \implies (\operatorname{a}\left(n\right) = 2 \cdot \operatorname{a}\left(n - 1\right) - \operatorname{a}\left(n - 2\right) + \operatorname{a}\left(n - 3\right) - \operatorname{a}\left(n - 4\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/WilsonPisotL67Recurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define the integer reference sequence v by v(0)=3, v(1)=4, v(2)=6 and v(n+3)=v(n+2)+v(n). Set u(n)=v(n)+3, s(n)=v(n+2)-2v(n+1)+v(n), and d(n)=v(n)v(n+2)-v(n+1)^2. Three-step induction proves v and s positive. The second differences satisfy s(n+3)=s(n+2)+s(n); a second induction proves s(n) at most s(n+1).

Expanding the quadratic determinant gives d(n+3)=d(n)-d(n+1). At indices 7,8,9 the triples (v,s,d) are (41,9,8), (60,13,-4), and (88,19,-9). Three-step induction, using monotonicity of s, proves -s(n) at most d(n) at most s(n) for all n at least seven. Another three-step induction gives 4s(n)<v(n) in that range.

The ceiling error u(n)u(n+2)-u(n+1)^2 is d(n)+3s(n). These inequalities put it between zero and u(n), strictly below the latter. At indices zero through six its exact pairs with u(n) are (5,6), (3,7), (0,9), (8,12), (12,16), (7,22), and (17,31). Thus the window holds at every index, including the zero error at index two.

Divide the window by the positive u(n): the rational quotient lies strictly above u(n+2)-1 and at most u(n+2). The ceiling characterization identifies its ceiling with u(n+2). Two-step induction therefore identifies the native sequence a with u at every index. Finally subtract the shifted identities u(n+3)=u(n+2)+u(n)-3 to obtain the signed order-four recurrence, and translate n+4 to the required natural lag indices. The same window proves positivity of every native denominator.

## References

- Truth anchor: `D5/S1/Recurrence/WilsonPisotL67Recurrence.a`
- Truth anchor: `D5/S1/Recurrence/WilsonPisotL67Recurrence.result`
