# Value One in the Binary XOR Triangle

## Abstract

For every positive natural number, the right edge of its binary XOR triangle has value one exactly when the input is a power of two.

**Definition 1.1 (Adjacent XOR).**

$$\begin{aligned}\operatorname{differences}\left(\operatorname{nil}\right) = \operatorname{nil}\\\forall b \in \mathrm{Bool},\; \operatorname{differences}\left(\operatorname{singleton}\left(b\right)\right) = \operatorname{nil}\\\forall b \in \mathrm{Bool},\; \forall c \in \mathrm{Bool},\; \forall xs \in \operatorname{List}\left(\mathrm{Bool}\right),\; \operatorname{differences}\left(\operatorname{cons}\left(b, \operatorname{cons}\left(c, xs\right)\right)\right) = \operatorname{cons}\left(\operatorname{xor}\left(b, c\right), \operatorname{differences}\left(\operatorname{cons}\left(c, xs\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.differences` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

Peter Kagey's OEIS A334595, revision 18, defines the triangle: "An XOR-triangle is an inverted 0-1 triangle formed by choosing a top row and having each entry in the subsequent rows be the XOR of the two values above it." A row is a list of Boolean bits. The function differences preserves their order and replaces each adjacent pair by ordinary Boolean XOR. Empty rows and one-bit rows have empty differences.

**Definition 1.2 (The retained left edge).**

$$\begin{aligned}\forall xs \in \operatorname{List}\left(\mathrm{Bool}\right),\; \operatorname{leftEdge}\left(0, xs\right) = \operatorname{nil}\\\forall k \in \mathrm{Nat},\; \forall xs \in \operatorname{List}\left(\mathrm{Bool}\right),\; \operatorname{leftEdge}\left(k + 1, xs\right) = \operatorname{cons}\left(\operatorname{headD}\left(xs, \operatorname{false}\right), \operatorname{leftEdge}\left(k, \operatorname{differences}\left(xs\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.leftEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

leftEdge(k, xs) records k entries from the first element of xs down through successive difference rows. The default head of an empty row is false. In the right-edge construction k is the original row length, so every recorded row is nonempty. All k edge positions are retained, including zero bits.

**Definition 1.3 (The unpadded binary input).**

$$\forall n \in \mathrm{Nat},\; \operatorname{sourceRow}\left(n\right) = \operatorname{reverse}\left(\operatorname{bits}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.sourceRow` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

The source's name is "Binary interpretation of the right diagonal of the XOR-triangle with first row generated from the binary expansion of n." Lean's Nat.bits lists bits from least significant to most significant; sourceRow reverses it to obtain the unpadded most-significant-first row. No zeros are added to the input. The theorem uses positive n, including n equal to one.

**Definition 1.4 (Right edge from the top to the apex).**

$$\forall row \in \operatorname{List}\left(\mathrm{Bool}\right),\; \operatorname{rightEdge}\left(row\right) = \operatorname{leftEdge}\left(\operatorname{length}\left(row\right), \operatorname{reverse}\left(row\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.rightEdge` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

The source fixes the orientation with n equal to 19: "Reading the right side of the triangle starting from the upper-right corner gives 10100 which is the binary representation of 20 = a(19)." Reversing the original row turns its right edge into a left edge because Boolean XOR is symmetric. rightEdge retains the original number of positions and reads from the top-right corner to the apex; leading zero bits of the edge are retained.

**Definition 1.5 (Binary decoding with the width retained).**

$$\forall row \in \operatorname{List}\left(\mathrm{Bool}\right),\; \operatorname{decode}\left(row\right) = \operatorname{ofDigits}\left(2, \operatorname{map}\left(\operatorname{BoolToNat}, \operatorname{reverse}\left(row\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.decode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

decode interprets a Boolean row as a most-significant-first binary word. It reverses the row, maps false to zero and true to one, and passes those least-significant-first digits to Nat.ofDigits with base two. The row itself retains its full width even when its value has a shorter canonical binary expansion.

**Definition 1.6 (The sequence A334595).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{decode}\left(\operatorname{rightEdge}\left(\operatorname{sourceRow}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/XorTriangle/ValueOne.a` (`✓ std3`).

*Citation.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Commentary.*

The source row, ordinary adjacent XOR, top-right-to-apex edge and binary decoding define a(n). For the source's n equal to 19, the row is 10011 and the right edge is 10100, giving a(19) equal to 20. For n equal to one the row and edge each consist of the single bit one. The definition is total on natural numbers; the classification below is restricted to positive inputs.

**Theorem 1.7 (The value-one classification).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{a}\left(n\right) = 1 \Leftrightarrow (\exists k \in \mathrm{Nat},\; n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/XorTriangle/ValueOne.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2020). *OEIS A334595: the right edge of a binary XOR triangle*. URL: <https://oeis.org/A334595>.

*Acknowledgement.* Ilya Bogdanov (2020). *Answer to Number triangle*. URL: <https://mathoverflow.net/a/359278>.

*Commentary.*

The fourth %C comment of OEIS A334595, revision 18, is the second conjecture: "Conjecture: a(n) = 1 if and only if n is a power of two." For every natural n at least one, with the unpadded most-significant-first input and all right-edge positions retained, a(n) equals one if and only if there exists a natural k such that n equals 2 to the power k. The exponent may be zero, so n equal to one is included. The proof reconstructs a fixed-width row from its edge and establishes injectivity. At that same width, the word with only its final bit equal to one decodes to one; its unique source row has only its first bit equal to one and decodes to a power of two. The finite-XOR reconstruction uses the reversible-triangle relation also used by Ilya Bogdanov in MathOverflow answer 359278, revision 5. The quoted OEIS text and adapted reversible-triangle argument are attributed to Peter Kagey, the OEIS Foundation and Ilya Bogdanov under CC BY-SA 4.0; the Library notes identify the sources and adaptations. The result is proved within Lean without an invertibility premise or a literature axiom. The record-position conjecture and rotational fixed-point counting are separate assertions.

## References

- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.a`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.decode`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.differences`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.leftEdge`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.result`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.rightEdge`
- Truth anchor: `D5/S3/Combinatorics/XorTriangle/ValueOne.sourceRow`
