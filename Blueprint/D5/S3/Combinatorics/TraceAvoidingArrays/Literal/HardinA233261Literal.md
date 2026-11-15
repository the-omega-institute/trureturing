# Six-row antidiagonal arrays

## Abstract

Literal six-row complementary-pair arrays with horizontal and antidiagonal bonds.

An array is a function from Fin 6 times Fin n to Fin 6. A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. It excludes equal colours and colours whose values sum to five. The first entry is zero. The rank r.val*n+j.val defines the strict row-major predecessor relation. No colour is required to occur.

**Definition 1.1 (Strict row-major normalization).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{normal}\left(A\right) = (\forall (p: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number of 6Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.2 (Literal array predicate).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(6\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(6\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number of 6Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.3 (Literal finite count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number of 6Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).

**Definition 1.4 (Proper pair-label pattern).**

$$\forall (n: \operatorname{Nat}), (\forall (P: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{Proper}\left(P\right) = (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(6\right)), (\forall (s: \operatorname{Fin}\left(6\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow (P\left((r, j)\right) \ne P\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proper pair-label pattern.

**Definition 1.5 (Labelled three-colour count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{L}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (P: (\operatorname{Fin}\left(6\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{Proper}\left(P\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Labelled three-colour count.

**Theorem 1.6 (Exact complementary-pair count).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((64: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact complementary-pair count.

The pair labels identify {0,5}, {1,4}, and {2,3}. Canonical first occurrences fix the pair names and the first side of each used pair. A pattern with k used pairs has 2^(6*n-k) lifts. At width at least two, every proper pattern uses two or three labels, and every orbit under label permutations has six members. When one label is omitted, the common neighbours of consecutive rows force each column to be constant, including the last column. The two remaining labels alternate with column parity. Exactly one such pattern is canonical. Summing the two possible lift weights gives the displayed identity.

**Theorem 1.7 (The ten-lag integer recurrence).**

$$\forall (n: \operatorname{Int}), ((16 < n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left(n\right)\right): \operatorname{Int}) = ((((((((((1984) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (1)\right)\right): \operatorname{Int}))) - ((1282048) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (2)\right)\right): \operatorname{Int})))) + ((346292224) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (3)\right)\right): \operatorname{Int})))) - ((27028094976) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (4)\right)\right): \operatorname{Int})))) - ((6584184864768) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (5)\right)\right): \operatorname{Int})))) + ((1907721393668096) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (6)\right)\right): \operatorname{Int})))) - ((214149680718675968) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (7)\right)\right): \operatorname{Int})))) + ((12624715655426342912) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (8)\right)\right): \operatorname{Int})))) - ((384499321786383466496) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (9)\right)\right): \operatorname{Int})))) + ((4759259971017064316928) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233261Literal}.\operatorname{a}\left(\operatorname{Int}.\operatorname{toNat}\left((n) - (10)\right)\right): \operatorname{Int})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233261` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233261","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The ten-lag integer recurrence.

A column has six independent pair labels. Its 729 raw states have exactly the horizontal and antidiagonal transitions in the literal array. The sparse successor lists are checked against all raw column pairs. The seventeen tabulated right vectors are checked successive powers on the all-ones vector. Their degree-ten identity after six transitions is propagated by arbitrary further matrix powers. The polynomial vanishes at one, preserving the constant correction six. Scaling lag j by 64^j and cancelling 48 gives the stated integer recurrence at every n greater than sixteen. All lagged widths are at least seven.

At width one there are no bonds. The count remains the literal finite function count; the displayed bridge is asserted only at widths at least two. Absent colours remain allowed throughout. The recurrence has no premise about computation, finite cutoffs, or the occurrence of all colours.

Proof classification: counting_bridge and result are both bind-only. The live consumer of counting_bridge is scale_recurrence, which feeds result. The structural two-label arguments are finite transports of the existing HardinA233258Strip.columns_constant and HardinA233177Ladder.two_label_classification suppliers; the unchanged proof repeats those arguments rather than importing an adapter. The transfer propagation directly reuses TransferMatrix.tabulatedPowers and TransferMatrix.scalarRelationShift. No escape witness or new general method is claimed. The result's proposed admission_basis is open-problem-resolution for the complete external assertion, with counting_bridge a consumed auxiliary.

Problems/hardin233261.md gives the complete event, its clause-by-clause correspondence and Triage. Its immutable event identifier is 932336f06d425b3988e1c636ab6db5275e017dd94af2eccba1f0f52fb052d93f; the preregistration is https://github.com/the-omega-institute/trureturing/issues/28857 and the fixed event is in comment 6768941004. The Proved claim concerns this whole event, including the literal finite-count definitions, not a finite prefix. Library/Automata/hardin2013a233261.md records the source and literature limits. Worldwide continued openness, priority and originality are unverified.

The counting_bridge and result information-escape bindings remain declared_unresolved: IE-C050 ClosedTruthReadout reason=unclassified_form rule=source.residual_requires_open, empty site/readout, certificate=null and escape_from=null. Their compiled Reg attempts do not supply validated bindings. The unfinished-audit disclosure is https://github.com/the-omega-institute/trureturing/issues/28857#issuecomment-6771906994. Independent admission confirmation and canonical freezing remain pending.

Source: R. H. Hardin, OEIS A233261, revision 8, https://oeis.org/A233261. Source licensing: https://oeis.org/LICENSE. The source calls the recurrence Empirical; no literature priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.L`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
