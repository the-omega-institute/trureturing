# Uniform prefix bound for the AKMP substitution

## Abstract

For k at least one, every proper prefix of either level-k image has palindromic length at most k+1.

The alphabet is Bool, with a represented by true and b by false. Section 4 of Ambroz, Kadlec, Masakova and Pelantova specifies the substitution a to ababa and b to aba. Palindromic length uses the existing minimum number of nonempty palindrome factors; the empty word has length zero.

**Definition 1.1 (Letter images).**

$$psiLetter\left(true\right) = [true,false,true,false,true] \land psiLetter\left(false\right) = [true,false,true]$$

*Formalization.* `D5/S1/Words/Palindromes/AKMPUniformPrefix.psiLetter` (`✓ std3`).

*Citation.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

Both images are nonempty palindromes.

**Definition 1.2 (Free-monoid substitution).**

$$psiEnd = lift\left(c \mapsto ofList\left(psiLetter\left(c\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/AKMPUniformPrefix.psiEnd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

FreeMonoid.lift extends the letter map multiplicatively. Multiplication in the free monoid is concatenation, so powers of psiEnd are actual iterations of this substitution.

**Definition 1.3 (Iterated letter image).**

$$\forall k \in \mathbb{N},\; \forall c \in Bool,\; W\left(k, c\right) = toList\left(\left(psiEnd^{k}\right)\left(of\left(c\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/AKMPUniformPrefix.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

The zeroth image is the singleton origin. If A and B are the images of a and b at one level, the next images are ABABA and ABA.

**Theorem 1.4 (Uniform proper-prefix bound).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(\forall c \in Bool,\; \forall m \in \mathbb{N},\; m < length\left(W\left(k, c\right)\right) \Rightarrow PL\left(take\left(m, W\left(k, c\right)\right)\right) \le k + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/AKMPUniformPrefix.uniform_prefix_pl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Petr Ambrož, Ondřej Kadlec, Zuzana Masáková, Edita Pelantová (2019). *Palindromic length of words and morphisms in class P*. DOI: [10.1016/j.tcs.2019.02.024](https://doi.org/10.1016/j.tcs.2019.02.024). URL: <https://arxiv.org/abs/1812.00711v2>.

*Commentary.*

A simultaneous induction keeps both images nonempty and palindromic and supplies decompositions for every cut, including complete images. Write a and b for the lengths of A and B. The cuts of ABABA lie in five consecutive intervals, with endpoints a, a+b, 2a+b, 2a+2b and 3a+2b. The first interval inherits an A-prefix decomposition; the second adds A to a B-prefix decomposition; the fourth adds ABA to a B-prefix decomposition.

For the third interval put r=2a+b-m and D=A.drop r. A decomposition of A.take r followed by the single palindrome formed by D, B and the reverse of D gives the required prefix. In the fifth interval use r=3a+2b-m and the single palindrome formed by D, B, A, B and the reverse of D. Each added reflected factor is nonempty because B is nonempty. Reversing these factors uses the palindromicity of A and B. The take/drop identities recover the exact prefix. Each step adds at most one factor. Prefixes of ABA are prefixes of the initial ABA block of ABABA, so the same decompositions cover the second origin.

The final decomposition bounds the existing minimum through Nat.find. This result concerns finite psi-iterate prefixes. It supplies no all-factor language transport, logarithmic asymptotic bound or matching lower bound for the Fibonacci word.

## References

- Truth anchor: `D5/S1/Words/Palindromes/AKMPUniformPrefix.W`
- Truth anchor: `D5/S1/Words/Palindromes/AKMPUniformPrefix.psiEnd`
- Truth anchor: `D5/S1/Words/Palindromes/AKMPUniformPrefix.psiLetter`
- Truth anchor: `D5/S1/Words/Palindromes/AKMPUniformPrefix.uniform_prefix_pl`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/PalindromicLength](FridPrefix/PalindromicLength.md)
