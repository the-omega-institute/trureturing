# Quadratic Prefix Charge in the Literal Tribonacci Word

## Abstract

Explicit prefixes of the literal Tribonacci word have quadratic alternating charge in the substitution level and refute a uniform logarithmic interval bound.

The letters A, B and C are 0, 1 and 2 in Fin 3. The substitution is exactly A to AB, B to AC and C to A. W is the closed A-starting infinite word from TribonacciAlignedWindows, with its actual letters identified with finite substitution iterates by MBonacciSentinelDesubstitution.word_eq_iterate. All positions, lengths and levels are natural numbers; positions start at zero.

**Definition 1.1 (Four substitution steps).**

$$\forall x \in Fin\left(3\right),\; tau\left(x\right) = image\left(sigma, 4, x\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write tau=sigma^4, so tau^n(x)=image sigma (4n) x. The literal images are tau(A)=ABACABAABACAB, tau(B)=ABACABAABAC and tau(C)=ABACABA. Their lengths are 13, 11 and 7. In particular tau(A)=tau(C) followed by A and BACAB.

**Definition 1.2 (Integer letter weights).**

$$weight\left(0\right) = 2 \land \left(weight\left(1\right) = 1 \land weight\left(2\right) = 0\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weights are exactly A=2, B=1 and C=0, with values in the integers.

**Definition 1.3 (Alternating charge from the local start).**

$$\forall v \in List\left(Fin\left(3\right)\right),\; signedWordSum\left(v\right) = alternatingSum\left(map\left(weight, v\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.signedWordSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For v of length m this is the sum of (-1)^i times weight(v[i]) over 0<=i<m. The sign starts positive at the beginning of v, independently of its position in W. The empty sum is zero. Mathlib's alternatingSum_append gives F(uv)=F(u)-F(v) whenever u has odd length.

TribonacciAlignedWindows.four_parity supplies odd length for every tau^n letter image. Thus substitution of such blocks preserves the alternating pattern of the original letters. Put a_n=F(tau^n(A)), b_n=F(tau^n(B)) and c_n=F(tau^n(C)). Expanding the three literal images gives (a_0,b_0,c_0)=(2,1,0) and (a_(n+1),b_(n+1),c_(n+1))=(a_n,2a_n-b_n,4a_n-2b_n-c_n). Induction gives a_n=2, b_n=2-(-1)^n and c_n=2-(2n+2)(-1)^n. These are identities at every natural level.

**Definition 1.4 (The actual recursive prefix family).**

$$prefixWord\left(0\right) = nil\left(\right) \land \left(\forall n \in \mathbb{N},\; prefixWord\left(n + 1\right) = append\left(image\left(sigma, 4 \cdot \left(n + 1\right), 2\right), prefixWord\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.prefixWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Denote prefixWord(n) by U_n. Thus U_0 is empty and U_(n+1)=tau^(n+1)(C) U_n; the new block is prepended. The decomposition tau^(n+1)(A)=tau^(n+1)(C) tau^n(A) tau^n(BACAB) proves inductively that U_n is a literal prefix of tau^n(A). This is a prefix assertion about the original substitution, without an assumed occurrence hypothesis.

**Definition 1.5 (Prefix lengths).**

$$\forall n \in \mathbb{N},\; prefixLength\left(n\right) = length\left(prefixWord\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.prefixLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let m_n=length(U_n). Each letter image is nonempty, so m_n>0 for n>=1. Each of the three fourth images has length at most 13; induction bounds the length of tau^n(A) by 13^n. Prefix containment therefore gives 0<m_n<=13^n for n>=1. Applying MBonacciSentinelDesubstitution.factor_of_prefix directly to that containment, at order 3 and iterate 4n, gives the exact identity factor W 0 m_n=U_n.

**Definition 1.6 (Charge of the prefix family).**

$$\forall n \in \mathbb{N},\; prefixCharge\left(n\right) = signedWordSum\left(prefixWord\left(n\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.prefixCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write q_n=F(U_n). Oddness of the prepended block gives q_0=0 and q_(n+1)=c_(n+1)-q_n. Substituting the formula for c_n and inducting yields q_n=1-(-1)^n(n^2+3n+1). For even positive n its absolute value is n^2+3n; for odd n it is n^2+3n+2. Hence |q_n|>=n^2, including n=0.

**Definition 1.7 (The exact uniform interval claim).**

$$\exists K \in \mathbb{R},\; 0 < K \land \left(\forall s \in \mathbb{N},\; \forall m \in \mathbb{N},\; abs\left(real\left(signedWordSum\left(factor\left(W, s, m\right)\right)\right)\right) \le K \cdot log\left(real\left(m\right) + 2\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciPrefixRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant K is real and strictly positive. Both s and m range over all natural numbers, including m=0. factor W s m consists of W(s),...,W(s+m-1). The integer charge is coerced to a real number before taking its absolute value. The logarithm is the natural real logarithm of the real coercion of m plus 2. There are no unmentioned lower cutoffs or restrictions on the interval start.

**Theorem 1.8 (Failure of every positive logarithmic constant).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TribonacciPrefixRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact negation of claim holds. For each K>0, the contradiction already occurs at s=0 and m=m_n for a sufficiently large positive level n. The result is about the closed word W and the stated weights, without free word, parity or occurrence assumptions.

For n>=1, the elementary bound 13^n+2<=39^n gives log(m_n+2)<=n log(39). Choose a natural n>K log(39); positivity of K log(39) ensures n>=1. Then n^2>K n log(39)>=K log(m_n+2), whereas the actual prefix identity and charge formula give |F(factor W 0 m_n)|>=n^2. This contradicts the claimed bound for that interval. The argument covers every positive real K and all substitution levels needed for the construction; finite examples do not replace the induction.

Adamczewski, Symbolic discrepancy and self-similar dynamics, Annales de l'Institut Fourier 54 (2004), DOI 10.5802/aif.2079, provides general background on discrepancy for substitutions. Its existential weight lower bounds are not used as a theorem for these particular weights or this parity construction. The proof uses the literal word and concatenation identities instead. No optimal upper bound, spectral gap, entropy estimate or literature novelty assertion is part of this conclusion.

## References

- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.claim`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.prefixCharge`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.prefixLength`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.prefixWord`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.result`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.signedWordSum`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.tau`
- Truth anchor: `D5/S1/Words/TribonacciPrefixRefutation.weight`
- Dependency: [D5/S1/Words/TribonacciAlignedWindows](TribonacciAlignedWindows.md)
