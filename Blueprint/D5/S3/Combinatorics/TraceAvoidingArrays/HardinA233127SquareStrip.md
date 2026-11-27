# The finite certificate and the all-height recurrence

## Abstract

Hardin’s recurrence for normalized six-column complementary-pair square strips.

**Definition 1.1 (Forward boundary distributions).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{distribution} = \begin{pmatrix}16&0&16&16&16&16&16&8&8&16&8\\1024&10240&18432&14336&19456&17408&11264&8192&3584&13312&7680\\65536&11894784&19922944&13697024&20905984&19136512&9764864&8257536&2588672&13697024&7602176\\4194304&12731809792&21126709248&13820231680&22066233344&20451426304&9479127040&8522825728&2319450112&14390657024&7769948160\\268435456&13439489540096&22250346512384&14285598097408&23194970882048&21600464273408&9656697094144&8888569036800&2285325254656&15121506107392&8067827630080\\17179869184&14129523280838656&23375634386386944&14905288863776768&24350368624279552&22716013309067264&10021859508617216&9305227035410432&2341169493180416&15875504796073984&8431184010805248\\1099511627776&14834548759546822656&24535730616681889792&15605868810815406080&25552052095188729856&23852115859181928448&10472500808892022784&9754613724198469632&2434602967651844096&16659661645596852224&8832477511238549504\\70368744177664&15567108237574814040064&25744991932724816117760&16360109272758489186304&26808812111241439870976&25031000536475729133568&10970884659964933046272&10230667782738877087744&2545923396239978659840&17479390576998738821120&9261247309720961679360\\4503599627370496&16332950328716430292287488&27010652418350597978193920&17158719867507552292962304&28125783903232205206323200&26262820350752900696244224&11503471623921690059210752&10731832335239811082223616&2667781634235157838823424&18338196923878383063924736&9714047525398103845765120\end{pmatrix}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.distribution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

This 9 by 11 integer matrix has type Fin 9 → Fin 11 → Int. Its first row is the initial scanner distribution; each subsequent row is the preceding row multiplied by the boundary transfer.

**Definition 1.2 (Boundary continuation powers).**

$$(\forall (i: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{w}\left(0, i\right) = 1)) \land (\forall (n: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{w}\left((n) + (1), i\right) = \sum_{k: \operatorname{Fin}\left(11\right)} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(i, k\right)) \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{w}\left(n, k\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.w` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The integer-valued function w has type Nat → Fin 11 → Int. It starts at the constant one vector and applies the boundary transfer once per row.

**Theorem 1.3 (Single-row certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Boundary}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{Valid}\left(s, p\right)) \implies (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{classCount}\left(s, p, k\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{transfer}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{boundaryClass}\left(s, p\right), k\right)))))) \land (\forall (k: \operatorname{Fin}\left(11\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{firstCount}\left(k\right) = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8]\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

Exact scanner fibres reduce the transition counts to 3^6 label rows. The single-row certificate supplies the numerical premises of the all-height induction.

**Theorem 1.4 (The recurrence at every height).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int}) = ((((((((1984) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int}))) - ((1314816) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((411303936) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) - ((70111985664) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((6893422510080) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((389708152569856) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) + ((11733988091625472) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) - ((145241087982698496) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233127SquareStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233127` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233127","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233127: six-colour complementary-pair exclusion on a six-column square strip*. URL: <https://oeis.org/A233127>.

*Commentary.*

The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of D5.S3.Observer.Separation.BooleanRankThreeK4.beta. Exact scanner fibres retain the order restrictions and individual colour multiplicities. The first-row distribution is (16,0,16,16,16,16,16,8,8,16,8). The displayed matrix counts continuations from each valid boundary. A class-constant continuation remains class-constant after one row, hence after every number of rows by semiconjugacy iteration. The unseen sector has eigenvalue 64. The ten completed classes have characteristic polynomial x^3 times (x^7-1920x^6+1191936x^5-335020032x^4+48670703616x^3-3778497478656x^2+147884313935872x-2269391999729664). The full initial row vector is annihilated by (x-64) times that degree-seven cofactor. Its eighth transfer is exactly the indicated linear combination of its first eight distributions, coordinate by coordinate. Pairing this identity with any continuation height proves the recurrence for the literal filtered count at every n+9.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.distribution`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.w`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate](HardinA233127Certificate.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
