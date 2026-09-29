# Isometric representations and orbit coverings

This volume fixes the bridge between a homomorphism into the isometry group
and the orbit covering used to model a hyperbolic manifold by its universal
cover. It proves a conditional covering statement; it does not assert that a
finite-volume hyperbolic lattice satisfies the stated hypotheses.

## 1. The representation action

**Definition 1.1.** Let (G) be a group, (X) a metric space, and
(ho:G\to\operatorname{Isom}(X)) a homomorphism. Its associated action is
(g\cdot x=\rho(g)(x)). Write (X/\rho) for the equivalence classes of the
relation (x\sim_\rho y\iff \exists g,\rho(g)(x)=y).

**Theorem 1.2 (comparison of the two orbit conventions).** The relation
(x\sim_\rho y) agrees with the standard group-action relation
(x\in G\cdot y). The resulting orbit quotients are canonically homeomorphic
with their quotient topologies.

**Proof.** If (y=\rho(g)(x)), then (x=\rho(g^{-1})(y)). Conversely, invert
the witness in the same way. The identity on representatives therefore
respects both equivalence relations and induces mutually inverse maps of the
quotients. Each map is continuous by the defining quotient topology. The
group-action quotient construction and its topology are standard; the
comparison here identifies its convention with the quotient fixed above.

## 2. Covering projection

**Definition 2.1.** The representation is *free* if
(\rho(g)(x)=x\Rightarrow g=1) for every (g,x). It is *properly
discontinuous* if, for all compact (K,L\subseteq X), the set

\[
\{g\in G:(\rho(g)(K)\cap L)\ne\varnothing\}
\]

is finite.

**Theorem 2.2 (covering bridge).** Suppose (X) is Hausdorff and locally
compact. If the isometric representation is free and properly discontinuous,
then the canonical projection (X\to X/\rho) is a covering map.

**Proof.** Under the action in Definition 1.1, freeness is the cancellation
condition for scalar multiplication, proper discontinuity is the compact-set
condition for the action, and each action map is continuous because it is an
isometry. The standard covering theorem for free, properly discontinuous
group actions applies to the standard orbit quotient. Transport its covering
projection across the homeomorphism of Theorem 1.2.

The theorem supplies a topological covering map. It does not establish a
hyperbolic metric or smooth quotient structure, finite volume, or rigidity of
the acting lattice.

## 追加锚（本行以下为增补区）
