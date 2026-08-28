# Typed Governance Admission

## Definition 1. Typed producer resolution

Let `Artifact` and `ProducerActor` be arbitrary types with no coercion between
them. A producer assignment and an actor resolver have types

\[
\mathsf{producer}:\mathsf{Artifact}\to\mathsf{Option}\;\mathsf{ProducerActor},
\qquad
\mathsf{resolve}:\mathsf{ProducerActor}\to\mathsf{Option}\;\mathsf{Artifact}.
\]

Define the artifact-to-artifact producer-edge relation by

\[
\mathsf{ProducerEdge}(a,x)
\quad\Longleftrightarrow\quad
\exists q,\;
  \mathsf{producer}(x)=\mathsf{some}(q)
  \land
  \mathsf{resolve}(q)=\mathsf{some}(a).
\]

Define resolution completeness by

\[
\mathsf{ResolutionComplete}
\quad\Longleftrightarrow\quad
\forall x\;q,\;
  \mathsf{producer}(x)=\mathsf{some}(q)
  \to \exists a,\;\mathsf{resolve}(q)=\mathsf{some}(a).
\]

An artifact relation `E` is an admissible producer graph exactly when
`ResolutionComplete` holds and

\[
\forall a\;x,\;E(a,x)\leftrightarrow\mathsf{ProducerEdge}(a,x).
\]

Thus every producer edge is witnessed by a resolved artifact. In particular,
for every `x` and `q`,

\[
\mathsf{producer}(x)=\mathsf{some}(q)
\land
\mathsf{resolve}(q)=\mathsf{none}
\quad\Longrightarrow\quad
\forall a,\;\neg\mathsf{ProducerEdge}(a,x).
\]

The same premises refute `ResolutionComplete`, so no relation `E` is an
admissible producer graph. An unresolved producer actor therefore produces no
artifact edge, but it also makes the graph fail closed; it cannot be accepted
as an empty family of edges whose source silently disappeared.

## Proposition 2. Consumption is not inverse to production input

There exists a finite artifact model with distinct artifacts `x` and `y`, a
runtime-consumer relation `consumers`, and a partial production-input map
`prodInputs` such that

\[
y\in\mathsf{consumers}(x),
\qquad
\mathsf{prodInputs}(y)=\mathsf{some}(\varnothing),
\qquad
x\notin\varnothing.
\]

A concrete witness uses the two-element type with elements `x` and `y`, sets
`consumers(x)={y}`, and sets `prodInputs(y)=some(\varnothing)`. The consumer
edge records that the executable artifact `y` reads `x` at runtime, while the
production-input value records that `y` itself was produced without artifact
inputs. Hence runtime consumption and production input are different
relations and need not be mutual inverses.

## Theorem 3. A finite acyclic judging graph has a root

Let `V` be a finite nonempty type and let
`judges : V \to V \to Prop`, where `judges(j,x)` means that `j` judges `x`.
If `judges` is acyclic, then

\[
\exists r:V,\;\forall j:V,\;\neg\mathsf{judges}(j,r).
\]

Equivalently, some vertex has an empty set of judges. To prove it, assume every
vertex has a judge. Starting from any vertex and repeatedly choosing a judge
produces a sequence in the finite type `V`; a repeated vertex then yields a
directed cycle, contradicting acyclicity.

The statement proves only existence of an empty-judge vertex. It makes no
claim that such a vertex can certify its own consistency.

## Theorem 4. Two-state locality yields incremental preservation

Let `State`, `Artifact`, and `Value` be types. Fix

\[
\mathsf{bytes}:\mathsf{State}\to\mathsf{Artifact}\to\mathsf{Value},
\quad
\mathsf{reads}:\mathsf{State}\to\mathsf{Artifact}\to
  \mathcal P(\mathsf{Artifact}),
\quad
P:\mathsf{State}\to\mathsf{Artifact}\to\mathsf{Prop}.
\]

For states `s` and `t`, define

\[
\mathsf{Changed}(s,t)=
\{a\mid\mathsf{bytes}(s,a)\ne\mathsf{bytes}(t,a)\}.
\]

The required locality hypothesis is universally quantified over both states:

\[
\begin{aligned}
\mathsf{Local}(P,\mathsf{reads})\;:\!\!\Longleftrightarrow\;
\forall s\;t\;x,\;&
\Bigl(\forall a\in
  \{x\}\cup\mathsf{reads}(s,x)\cup\mathsf{reads}(t,x),\\
&\mathsf{bytes}(s,a)=\mathsf{bytes}(t,a)\Bigr)
\to\bigl(P(s,x)\leftrightarrow P(t,x)\bigr).
\end{aligned}
\]

For fixed states `s` and `t`, let
`dep : Artifact \to \mathcal P(Artifact)` be a cross-state over-approximation:

\[
\forall x,\;
\mathsf{reads}(s,x)\cup\mathsf{reads}(t,x)
\subseteq\mathsf{dep}(x).
\]

If `Local(P,reads)` holds, `x` is unchanged, and no artifact in `dep(x)` is
changed, then

\[
P(s,x)\leftrightarrow P(t,x).
\]

Indeed, `x` is byte-equal in the two states by the unchanged premise. Every
artifact in either actual-read set is byte-equal because both read sets lie in
`dep(x)` and `dep(x)` is disjoint from `Changed(s,t)`. The two-state locality
hypothesis then applies. The conclusion is not assumed: it is obtained by
combining locality with the cross-state over-approximation and disjointness.

## Theorem 5. Soundness and liveness are independent of shape-only tests

There is a concrete judge model in which soundness and liveness are logically
independent. Take

\[
\mathsf{Judge}=\mathsf{Bool}\times\mathsf{Bool},
\quad
\mathsf{sound}(j)\Longleftrightarrow j.1=\mathsf{true},
\quad
\mathsf{live}(j)\Longleftrightarrow j.2=\mathsf{true},
\quad
\mathsf{shape}(j)=\star.
\]

Then `(true,false)` is sound but not live, while `(false,true)` is live but not
sound. Neither property implies the other.

More generally, let `shape : Judge \to Shape` and `live : Judge \to Prop`. If
there are `j₁` and `j₂` with equal shape and different liveness, then every
shape-invariant test family fails to characterize liveness:

\[
\forall T:\mathsf{Judge}\to\mathsf{Prop},\;
\Bigl(
  \forall j_1\;j_2,\;
  \mathsf{shape}(j_1)=\mathsf{shape}(j_2)
  \to (T(j_1)\leftrightarrow T(j_2))
\Bigr)
\to
\neg\Bigl(\forall j,\;T(j)\leftrightarrow\mathsf{live}(j)\Bigr).
\]

For if such a `T` characterized liveness, equal shape would force equal
`T`-values and hence equal liveness for `j₁` and `j₂`, contradicting the
witnesses. This quantifies over all shape-only test families; it is stronger
than merely exhibiting one same-shape pair with different liveness.
