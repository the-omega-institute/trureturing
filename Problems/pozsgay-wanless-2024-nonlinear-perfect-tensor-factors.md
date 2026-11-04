---
slug: pozsgay-wanless-2024-nonlinear-perfect-tensor-factors
bibkey: pozsgaywanless2024tensor
doi: 10.22331/q-2024-05-08-1339
url: https://arxiv.org/abs/2308.07042v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.result
---

# Every classical six-leg perfect tensor factorization has perfect two-wire factors

## Problem

B. Pozsgay and I. M. Wanless, *Tensor network decompositions for absolutely maximally entangled states*, Quantum 8 (2024) 1339, arXiv:2308.07042v3, ask whether the linear factorization result extends to nonlinear classical maps. In `factoringtriunit.tex`, the source defines orthogonal columns and orthogonal arrays in lines 891–902, associates a map from three input symbols to three output symbols with an array in lines 929–937, and gives the six-leg factorization
$u^{(123)}=\mathcal C^{(23)}\mathcal B^{(13)}\mathcal A^{(12)}$
with classical two-wire functions in lines 945–964. After the linear calculation, lines 1196–1200 state:

> In other words, if $G$ represents a linear perfect tensor with 6 legs, and it has a $\triangleright$-decomposition into linear tensors with 4 legs, then those factors will themselves be perfect. It is an open question whether this statement is true in the nonlinear case for $k=6$.

The settled classical statement uses a finite type $x$ and arbitrary maps $a,b,c:x\times x\to x\times x$. The circuit applies $a$ to the first two wires, $b$ to the first output of $a$ and the third wire, and $c$ to the second output of $a$ and the second output of $b$. If its six-column graph is an index-one orthogonal array of strength $3$, the question is whether each four-column gate graph is an index-one orthogonal array of strength $2$.

## Motivation

For a classical map, the source's array has rows consisting of the input triple followed by its output triple. Strength $3$ means that every selection of three columns contains every symbol triple exactly once. A two-wire factor has four columns, consisting of its two inputs and two outputs; strength $2$ is the corresponding perfect-factor condition.

A positive answer makes the nonlinear six-leg factorization usable without the source's linear-field assumptions. It identifies the structure that a classical decomposition must preserve at each gate, which is the condition needed for the factors themselves to represent four-leg perfect tensors in the orthogonal-array model.

## Gap

The preregistration in issue [#25007](https://github.com/the-omega-institute/trureturing/issues/25007) records the bounded literature check:

- The v3 source TeX keeps the nonlinear $k=6$ question open.
- The screened citing works on generalized dual-unitary circuits, matrix-product unitaries, and perfect tensors from biunimodular vectors did not settle this nonlinear factorization question.
- Searches of Zenodo and this repository found no prior settlement.

`not-found-in-searched-scope`.

## Route

Let $h:\operatorname{IsIndexOneOA}(\operatorname{circuitGraph} a b c) 3$ be the hypothesis. The private lemmas `oa_injective` and `oa_surjective` are the projection interfaces: with finite row and symbol types, an index-one strength-three hypothesis, three columns whose selector is injective, and respectively equal entries or prescribed target symbols, they give equality of rows or a row realizing the targets. Every column selector used in the proof has its injectivity discharged explicitly.

For nonempty $x$, `factors_bijective` assumes $[\operatorname{Fintype} x]$, $[\operatorname{Nonempty} x]$, the maps $a,b,c$, and $h$, and returns
$\operatorname{Bijective} a\land\operatorname{Bijective} b\land\operatorname{Bijective} c$.
It applies `oa_injective` to the output columns $3,4,5$ and cancels the three lifted gate maps on the finite triple type.

Here `IsLatin f` means that, for every fixed second input and for every fixed first input, the corresponding one-variable maps are bijective. With the same finite and nonempty assumptions, `first_latin` takes $a,b,c$, $h$, and $\operatorname{Bijective} a$ and returns Latin-square conditions for the first coordinates of $a$ and $b$. Its projection arguments use columns $(1,2,3)$, $(0,2,3)$, and $(0,1,3)$, with fixed symbols supplied by nonemptiness. The lemma `second_latin` takes $a,b,c$, $h$, $\operatorname{Bijective} a$, $\operatorname{Bijective} c$, and the first-coordinate Latin condition for $a$; it returns Latin conditions for the second coordinates of $a$ and $b$, using `oa_surjective` on $(1,4,5)$ and $(0,4,5)$ and `oa_injective` on $(2,4,5)$ and $(1,4,5)$. The lemma `last_latin` takes $a,b,c$, $h$, $\operatorname{Bijective} a$, and the second-coordinate Latin condition for $b$; it returns Latin conditions for both coordinates of $c$, using the projections $(2,3,4)$, $(0,1,4)$, $(2,3,5)$, and $(0,1,5)$.

The private lemma `gate_perfect` proves that, for a finite symbol type, a gate $f$ that is bijective and whose two output coordinates are bijective in each input has all two-column projections of `gateGraph f` bijective. The nonempty branch of `result` applies it to $a$, $b$, and $c$ after the three Latin lemmas. If $x$ is empty, `result` uses `IsEmpty x` and `Function.Bijective.of_isEmpty` to make every two-column projection of each gate graph bijective.

## Falsifier

The settlement would not answer the source question if the formal arrays used a different row or wire convention. Here `IsIndexOneOA` quantifies over every injective ordered selection of $s$ columns and requires the induced map from rows to $s$-tuples to be bijective. The circuit rows are indexed by $x\times x\times x$, and the gate rows by $x\times x$, so the row types are the source's $D^3$ and $D^2$ cases when the alphabet has size $D$. The definition also covers the empty finite type.

The definition `circuit` applies $a$ on wires $(1,2)$, then $b$ on $(1,3)$, then $c$ on $(2,3)$, and `circuitGraph` lists the three inputs followed by the three outputs. The definition `gateGraph` lists the two gate inputs followed by its two outputs. Thus the conclusion is exactly strength $2$ for each factor in the source's classical-map convention. The formal statement assumes no linearity, field structure, initial bijectivity, or dual unitarity.

## Evidence

The canonical source is `D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.lean`.
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization.lean.json`.

Declaration statements:
- `result`: `sha256:2e8ebc63c3619b5cc71ce305c1b4433bd65dfa65dfb710cd610eb71b5c9f222a`;
- `claim`: `sha256:1c6abc5bd2a0fa76f0287e9ef870ab9cddda99ec365de2713b558745f555a640`.

## Triage

Tier 1 open question in a 2024 journal paper, preregistered in issue #25007 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every type $x$ with `Fintype x` and every $a,b,c:x\times x\to x\times x$, if `circuitGraph a b c` is an index-one orthogonal array of strength $3$, then each of `gateGraph a`, `gateGraph b`, and `gateGraph c` is an index-one orthogonal array of strength $2$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- **Mechanism.** Strength-three projections control the circuit's information flow: the output triple makes the circuit injective, finite cancellation makes each gate bijective, and the selected mixed input-output projections isolate each coordinate of the gates as a bijection in each of its two inputs. The two-column criterion then gives the three strength-two gate graphs.
- **Extension and sharpness.** The compiled theorem already ranges over arbitrary functions on every finite alphabet, including the empty case through a separate vacuous branch. No weaker-hypothesis, converse, extremal, or sharpness theorem appears in `result`.
- **Neighbouring questions.** Open: whether analogous factor-perfection statements hold for other network orders or for $k>6$. The source obtains its other decomposition orientation from this one by the site permutation $1\leftrightarrow3$ (`factoringtriunit.tex` l. 633–646); the transfer of `result` to that orientation is not formalized here. The converse, from perfect two-wire factors to a strength-three composite, is not addressed by `result`. The source's quantum, nonclassical, and existence questions are outside this result.
- **Effect on the source.** The nonlinear classical $k=6$ question quoted above is settled under the exact orthogonal-array convention. The source's linear conclusion is included as a special case, while its linear existence conditions, its other decomposition orientation, its $k=8$ discussion, and claims about quantum factors remain separate. The source's implication from perfect factors to some three-column orthogonality conditions does not become the converse proved here.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in issue #25007 and does not establish exhaustive worldwide novelty or priority. The statements in “Argued, not formalized” are explanations or open extensions, not additional Lean declarations. The source's broader physical interpretation of orthogonal arrays as absolutely maximally entangled states, and every source statement outside the exact classical six-leg implication, are not formalized by `result`.
