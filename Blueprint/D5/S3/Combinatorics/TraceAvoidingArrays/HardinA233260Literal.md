# Five-row antidiagonal arrays

## Abstract

Literal five-row complementary-pair arrays with horizontal and antidiagonal bonds.

An array is a function from Fin 5 times Fin n to Fin 6. A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. It excludes equal colours and colours whose values sum to five. The first entry is zero. The rank r.val*n+j.val defines the strict row-major predecessor relation. No colour is required to occur.

**Definition 1.1 (Strict row-major normalization).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{normal}\left(A\right) = (\forall (p: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.normal` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.2 (Literal array predicate).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(5\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(5\right)), (\forall (s: \operatorname{Fin}\left(5\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.3 (Literal finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, NAME: Number of 5Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.4 (Proper pair-label pattern).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(5\right)), (\forall (s: \operatorname{Fin}\left(5\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Proper pair-label pattern.

**Definition 1.5 (Labelled three-colour count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Labelled three-colour count.

**Theorem 1.6 (Omitting a label forces constant columns).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow (\forall (P: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{Proper}\left(P\right)) \Rightarrow (\forall (d: \operatorname{Fin}\left(3\right)), ((\forall (i: (\operatorname{Fin}\left(5\right)) \times (\operatorname{Fin}\left(n\right))), (P\left(i\right) \ne d)) \Rightarrow (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (r: \operatorname{Fin}\left(5\right)), (P\left((r, j)\right) = P\left(((0: \operatorname{Fin}\left(5\right)), j)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.columns_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Omitting a label forces constant columns.

**Theorem 1.7 (Exact complementary-pair count).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((32: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

Exact complementary-pair count.

The pair labels identify {0,5}, {1,4}, and {2,3}. Canonical first occurrences fix the pair names and the first side of each used pair. A pattern with k used pairs has 2^(5*n-k) lifts. At width at least two, every proper pattern uses two or three labels, and every orbit under label permutations has six members. When one label is omitted, the common neighbours of consecutive rows force each column to be constant, including the last column. The two remaining labels alternate with column parity. Exactly one such pattern is canonical. Summing the two possible lift weights gives the displayed identity.

**Theorem 1.8 (The seven-lag integer recurrence).**

$$\forall (n: \operatorname{Int}), ((11 < n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left(n\right)\right): \operatorname{Int}) = (((((((512) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (1)\right)\right): \operatorname{Int}))) - ((65536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (2)\right)\right): \operatorname{Int})))) + ((2490368) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (3)\right)\right): \operatorname{Int})))) + ((17825792) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (4)\right)\right): \operatorname{Int})))) - ((2818572288) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (5)\right)\right): \operatorname{Int})))) + ((51539607552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (6)\right)\right): \operatorname{Int})))) - ((274877906944) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233260Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (7)\right)\right): \operatorname{Int})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233260` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233260","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233260: five-row complementary-pair antidiagonal arrays*. URL: <https://oeis.org/A233260>.

*Commentary.*

OEIS A233260, revision 7, FORMULA: Empirical: a(n) = 512*a(n-1) -65536*a(n-2) +2490368*a(n-3) +17825792*a(n-4) -2818572288*a(n-5) +51539607552*a(n-6) -274877906944*a(n-7) for n>11

Column states record five independent pair labels. Relabelling reduces their transitions to forty-one classes. The transfer polynomial is x^7-16*x^6+64*x^5-76*x^4-17*x^3+84*x^2-48*x+8. Its vector relation holds after four transitions and its value at one is zero. The scalar relation covers every index at least thirteen; the same finite power table verifies index twelve. The counting bridge scales each lag coefficient by a power of thirty-two. Every count used has positive width. The final statement quantifies all integers greater than eleven.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.columns_constant`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
