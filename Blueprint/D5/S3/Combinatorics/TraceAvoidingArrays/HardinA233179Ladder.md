# Six-row complementary-pair ladders

## Abstract

Hardin's order-24 recurrence for normalized six-row complementary-pair ladders.

Cells are Fin 6 times Fin n and colours are Fin 6. Bonds join consecutive columns at row distance at most one; within-column entries are unconstrained. The first cell is zero. Predecessors are ordered by row.val*n+column.val.

**Definition 1.1 (Row-major predecessor conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{normal}\left(A\right) = (\forall (p: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Row-major predecessor conditions.

**Definition 1.2 (Literal array conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(6\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(6\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Literal array conditions.

**Definition 1.3 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{Legal}\left(A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The literal filtered count.

**Theorem 1.4 (The pair-pattern counting bridge).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((64: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179PairTransfer}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The pair-pattern counting bridge.

The canonical-form theorems apply to the row-major cell order without changing their definitions. A canonical pair pattern using k labels has 2^(6*n-k) colour lifts. Proper patterns at width at least two use two or three labels, and each orbit has six members. If only two labels occur, HardinA233177Ladder.two_label_classification applies to the four-row windows 0–3 and 2–5. Their restrictions inherit Proper and the omitted label by argument substitution. Shared row 2 at columns 0 and 1 identifies both alternating labels, so the restrictions combine coordinatewise. Exactly one such pattern is canonical. Thus, if C is the canonical-pattern count, L=6*C and a=2^(6*n-3)*(C+1), giving the displayed bridge.

**Theorem 1.5 (The recurrence at width 26).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(26\right): \operatorname{Int}) = ((((((((((((((((((((((((448) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(25\right): \operatorname{Int}))) + ((421888) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(24\right): \operatorname{Int})))) - ((95682560) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(23\right): \operatorname{Int})))) - ((48586817536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(22\right): \operatorname{Int})))) + ((7696581394432) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(21\right): \operatorname{Int})))) + ((2219020623282176) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(20\right): \operatorname{Int})))) - ((331924968239529984) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(19\right): \operatorname{Int})))) - ((45544058606667694080) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(18\right): \operatorname{Int})))) + ((7676565708838105251840) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(17\right): \operatorname{Int})))) + ((384720682715267981115392) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(16\right): \operatorname{Int})))) - ((90389119748153097756606464) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(15\right): \operatorname{Int})))) - ((732939612340266155036901376) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(14\right): \operatorname{Int})))) + ((559176850836005482125888323584) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(13\right): \operatorname{Int})))) - ((7028965514623047698676841447424) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(12\right): \operatorname{Int})))) - ((1887473560557987165955670813966336) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(11\right): \operatorname{Int})))) + ((44169859058027396737075939400220672) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(10\right): \operatorname{Int})))) + ((3500683050361467360162023730212503552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(9\right): \operatorname{Int})))) - ((101555160700421718306247628235154128896) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(8\right): \operatorname{Int})))) - ((3466958920006006825501354764976208740352) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(7\right): \operatorname{Int})))) + ((108207134224866861549607317549181730553856) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(6\right): \operatorname{Int})))) + ((1701156622829501613469275506203267231121408) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(5\right): \operatorname{Int})))) - ((52659376845749069097884147249280994259238912) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(4\right): \operatorname{Int})))) - ((315694924216699133847365011797178367569035264) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(3\right): \operatorname{Int})))) + ((9366312983382861719445001674512311832511774720) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left(2\right): \operatorname{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

The recurrence at width 26.

**Theorem 1.6 (Hardin's shifted integer recurrence).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (26)\right): \operatorname{Int}) = ((((((((((((((((((((((((448) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (25)\right): \operatorname{Int}))) + ((421888) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (24)\right): \operatorname{Int})))) - ((95682560) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (23)\right): \operatorname{Int})))) - ((48586817536) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (22)\right): \operatorname{Int})))) + ((7696581394432) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (21)\right): \operatorname{Int})))) + ((2219020623282176) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (20)\right): \operatorname{Int})))) - ((331924968239529984) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (19)\right): \operatorname{Int})))) - ((45544058606667694080) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (18)\right): \operatorname{Int})))) + ((7676565708838105251840) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (17)\right): \operatorname{Int})))) + ((384720682715267981115392) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (16)\right): \operatorname{Int})))) - ((90389119748153097756606464) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (15)\right): \operatorname{Int})))) - ((732939612340266155036901376) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (14)\right): \operatorname{Int})))) + ((559176850836005482125888323584) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (13)\right): \operatorname{Int})))) - ((7028965514623047698676841447424) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (12)\right): \operatorname{Int})))) - ((1887473560557987165955670813966336) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (11)\right): \operatorname{Int})))) + ((44169859058027396737075939400220672) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (10)\right): \operatorname{Int})))) + ((3500683050361467360162023730212503552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int})))) - ((101555160700421718306247628235154128896) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int})))) - ((3466958920006006825501354764976208740352) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) + ((108207134224866861549607317549181730553856) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((1701156622829501613469275506203267231121408) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) - ((52659376845749069097884147249280994259238912) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((315694924216699133847365011797178367569035264) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) + ((9366312983382861719445001674512311832511774720) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233179Ladder}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233179` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233179","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233179: complementary-pair exclusion on a six-row ladder*. URL: <https://oeis.org/A233179>.

*Commentary.*

Hardin's shifted integer recurrence.

Each column contributes six free side bits. Scaling the pair-pattern relation multiplies the coefficient at lag j by 64^j. The finite instance supplies width 26; the shifted transfer relation supplies every greater width. The index n+26 expresses exactly the published range index>25. Width one is outside the bridge's scope.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder](HardinA233177Ladder.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer](HardinA233179PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
