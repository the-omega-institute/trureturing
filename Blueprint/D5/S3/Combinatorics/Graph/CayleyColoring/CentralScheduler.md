# The random central coloring daemon

## Abstract

A uniform ranking gives the same legal terminal-history probabilities as sequential uniform enabled choices.

**Theorem 1.1 (Exact terminal-history law).**

$$\forall (V: Type), \forall (K: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (G: \operatorname{SimpleGraph}\left(V\right)), \forall (P: \operatorname{FreePolicy}\left(K, G\right)), \forall (c: V \to K), \forall (h: \operatorname{List}\left(V\right)), (\operatorname{LegalTerminal}\left(G, P, c, h\right) \implies \operatorname{card}\left(\operatorname{RankFiber}\left(G, c, h\right)\right) \cdot \operatorname{choiceProduct}\left(\operatorname{conflict}\left(G, c\right), \operatorname{univ}\left(V\right), h\right) = \operatorname{card}\left(\operatorname{Perm}\left(V\right)\right)) \land (\neg \operatorname{LegalTerminal}\left(G, P, c, h\right) \implies \operatorname{IsEmpty}\left(\operatorname{RankFiber}\left(G, c, h\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law` (`✓ std3`). ∎

*Citation.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

A history is accepted when following the free-color policy produces a proper final coloring. Its ranking fiber consists of permutations yielding that ordered mover list. The enabled sets shrink after each actual recoloring, and permuting the ranks of currently enabled vertices preserves the prefix constraints. The product counts the successive enabled choices from the initial conflict graph. An invalid or nonterminal history has an empty fiber.

**Definition 1.2 (Complete).**

$$\forall (V: \mathit{Type}), [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: \mathit{Equiv}.\mathit{Perm} V), \forall (\mathit{live}: \mathit{Set} V), \forall (\mathit{history}: \mathit{List} V), (\mathit{Complete} V G \mathit{rank} \mathit{live} \mathit{history} : \mathit{Prop}) = \mathit{CayleyScheduler}.\mathit{Prefix} G (\mathit{coe} \mathit{rank}) \mathit{live} \mathit{history} \land \mathit{CayleyScheduler}.\mathit{Stop} G (\mathit{remaining} \mathit{live} \mathit{history})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Complete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (Enabled).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), \forall (v: V), (\mathit{Enabled} V G \mathit{live} v : \mathit{Prop}) = \exists (w : V), (\mathit{active} G \mathit{live}).\mathit{Adj} v w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Enabled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (First).**

$$\forall (V: \mathit{Type}), \forall (\iota: \mathit{Type}), [\mathit{LT} \iota] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: V \to \iota), \forall (\mathit{live}: \mathit{Set} V), \forall (v: V), (\mathit{First} V \iota G \mathit{rank} \mathit{live} v : \mathit{Prop}) = \mathit{CayleyScheduler}.\mathit{Enabled} G \mathit{live} v \land \forall (w : V), \mathit{CayleyScheduler}.\mathit{Enabled} G \mathit{live} w \to w \neq v \to \mathit{rank} v < \mathit{rank} w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.First` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.5 (Free Policy).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), (\mathit{FreePolicy} V K G : \mathit{Type} (\mathit{max} u w)) = \mathit{List} V \to (\mathit{color} : V \to K) \to (v : V) \to (\exists (w : V), (\mathit{conflict} G \mathit{color}).\mathit{Adj} v w) \to \{ \mathit{new} : K  |  \forall (w : V), G.\mathit{Adj} v w \to \mathit{new} \neq \mathit{color} w \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.FreePolicy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (History Rank).**

$$\forall (V: \mathit{Type}), [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), \forall (\mathit{history}: \mathit{List} V), (\mathit{HistoryRank} V G \mathit{live} \mathit{history} : \mathit{Type} (\mathit{max} 0 u)) = \{ \mathit{rank} : \mathit{Equiv}.\mathit{Perm} V  |  \mathit{CayleyScheduler}.\mathit{Prefix} G (\mathit{coe} \mathit{rank}) \mathit{live} \mathit{history} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.HistoryRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.7 (Legal Prefix).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), \forall (l: \mathit{List} V), (\mathit{LegalPrefix} V G \mathit{live} l : \mathit{Prop}) = \mathit{List}.\mathit{recOn} (\mathit{motive} := \mathit{fun} (x : \mathit{List} V) => \mathit{Set} V \to \mathit{Prop}) l (\mathit{fun} (x : \mathit{Set} V) => \mathit{True}) (\mathit{fun} (v : V) (x : \mathit{List} V) (\mathit{rec} : \mathit{Set} V \to \mathit{Prop}) (\mathit{alive} : \mathit{Set} V) => \mathit{CayleyScheduler}.\mathit{Enabled} G \mathit{alive} v \land \mathit{rec} (\mathit{alive} \setminus \{v\})) \mathit{live}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.8 (Legal Run).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{DecidableEq} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{aTwo}: V \to K), \forall (\mathit{aOne}: \mathit{List} V), \forall (a: V \to K), \mathit{LegalRun} V K G \mathit{aTwo} \mathit{aOne} a : \mathit{Prop}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
\forall \{V : \mathit{Type}\} \{K : \mathit{Type}\} [ \mathit{DecidableEq} V] \{G : \mathit{SimpleGraph} V\} (\mathit{color} : V \to K), \mathit{CayleyScheduler}.\mathit{LegalRun} G \mathit{color} [] \mathit{color}
$$

$$
\forall \{V : \mathit{Type}\} \{K : \mathit{Type}\} [ \mathit{DecidableEq} V] \{G : \mathit{SimpleGraph} V\} \{\mathit{color} \mathit{final} : V \to K\} \{v : V\} \{\mathit{tail} : \mathit{List} V\} \{\mathit{new} : K\}, (\exists (w : V), (\mathit{conflict} G \mathit{color}).\mathit{Adj} v w) \to (\forall (w : V), G.\mathit{Adj} v w \to \mathit{new} \neq \mathit{color} w) \to \mathit{CayleyScheduler}.\mathit{LegalRun} G (\mathit{Function}.\mathit{update} \mathit{color} v \mathit{new}) \mathit{tail} \mathit{final} \to \mathit{CayleyScheduler}.\mathit{LegalRun} G \mathit{color} (v :: \mathit{tail}) \mathit{final}
$$

**Definition 1.9 (Moves).**

$$\forall (V: \mathit{Type}), \forall (\iota: \mathit{Type}), [\mathit{LT} \iota] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: V \to \iota), \forall (\mathit{live}: \mathit{Set} V), \forall (v: V), (\mathit{Moves} V \iota G \mathit{rank} \mathit{live} v : \mathit{Prop}) = \exists (w : V), (\mathit{active} G \mathit{live}).\mathit{Adj} v w \land \mathit{rank} v < \mathit{rank} w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Moves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Next Rank).**

$$\forall (V: \mathit{Type}), [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), \forall (\mathit{history}: \mathit{List} V), \forall (v: V), (\mathit{NextRank} V G \mathit{live} \mathit{history} v : \mathit{Type} (\mathit{max} 0 u)) = \{ \mathit{rank} : \mathit{Equiv}.\mathit{Perm} V  |  \mathit{CayleyScheduler}.\mathit{Prefix} G (\mathit{coe} \mathit{rank}) \mathit{live} \mathit{history} \land \mathit{CayleyScheduler}.\mathit{First} G (\mathit{coe} \mathit{rank}) (\mathit{remaining} \mathit{live} \mathit{history}) v \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.NextRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.11 (Policy Run).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{DecidableEq} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{policy}: \mathit{CayleyScheduler}.\mathit{FreePolicy} G), \forall (\mathit{aThree}: \mathit{List} V), \forall (\mathit{aTwo}: V \to K), \forall (\mathit{aOne}: \mathit{List} V), \forall (a: V \to K), \mathit{PolicyRun} V K G \mathit{policy} \mathit{aThree} \mathit{aTwo} \mathit{aOne} a : \mathit{Prop}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.PolicyRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
\forall \{V : \mathit{Type}\} \{K : \mathit{Type}\} [ \mathit{DecidableEq} V] \{G : \mathit{SimpleGraph} V\} \{\mathit{policy} : \mathit{CayleyScheduler}.\mathit{FreePolicy} G\} (\mathit{past} : \mathit{List} V) (\mathit{color} : V \to K), \mathit{CayleyScheduler}.\mathit{PolicyRun} G \mathit{policy} \mathit{past} \mathit{color} [] \mathit{color}
$$

$$
\forall \{V : \mathit{Type}\} \{K : \mathit{Type}\} [ \mathit{DecidableEq} V] \{G : \mathit{SimpleGraph} V\} \{\mathit{policy} : \mathit{CayleyScheduler}.\mathit{FreePolicy} G\} \{\mathit{past} : \mathit{List} V\} \{\mathit{color} \mathit{final} : V \to K\} \{v : V\} \{\mathit{tail} : \mathit{List} V\} (\mathit{enabled} : \exists (w : V), (\mathit{conflict} G \mathit{color}).\mathit{Adj} v w), \mathit{CayleyScheduler}.\mathit{PolicyRun} G \mathit{policy} (\mathit{past} ++ [v]) (\mathit{Function}.\mathit{update} \mathit{color} v \mathit{val} (\mathit{policy} \mathit{past} \mathit{color} v \mathit{enabled})) \mathit{tail} \mathit{final} \to \mathit{CayleyScheduler}.\mathit{PolicyRun} G \mathit{policy} \mathit{past} \mathit{color} (v :: \mathit{tail}) \mathit{final}
$$

**Definition 1.12 (Prefix).**

$$\forall (V: \mathit{Type}), \forall (\iota: \mathit{Type}), [\mathit{LT} \iota] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: V \to \iota), \forall (\mathit{aOne}: \mathit{Set} V), \forall (a: \mathit{List} V), \mathit{Prefix} V \iota G \mathit{rank} \mathit{aOne} a : \mathit{Prop}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
\forall \{V : \mathit{Type}\} \{\iota : \mathit{Type}\} [ \mathit{LT} \iota] \{G : \mathit{SimpleGraph} V\} \{\mathit{rank} : V \to \iota\} (\mathit{live} : \mathit{Set} V), \mathit{CayleyScheduler}.\mathit{Prefix} G \mathit{rank} \mathit{live} []
$$

$$
\forall \{V : \mathit{Type}\} \{\iota : \mathit{Type}\} [ \mathit{LT} \iota] \{G : \mathit{SimpleGraph} V\} \{\mathit{rank} : V \to \iota\} \{\mathit{live} : \mathit{Set} V\} \{v : V\} \{\mathit{tail} : \mathit{List} V\}, \mathit{CayleyScheduler}.\mathit{First} G \mathit{rank} \mathit{live} v \to \mathit{CayleyScheduler}.\mathit{Prefix} G \mathit{rank} (\mathit{live} \setminus \{v\}) \mathit{tail} \to \mathit{CayleyScheduler}.\mathit{Prefix} G \mathit{rank} \mathit{live} (v :: \mathit{tail})
$$

**Theorem 1.13 (Legal).**

$$\forall (V: \mathit{Type}), [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: \mathit{Equiv}.\mathit{Perm} V), \forall (\mathit{live}: \mathit{Set} V), \forall (l: \mathit{List} V), \forall (h: \mathit{CayleyScheduler}.\mathit{Prefix} G (\mathit{coe} \mathit{rank}) \mathit{live} l), \mathit{CayleyScheduler}.\mathit{LegalPrefix} G \mathit{live} l$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.14 (Stop).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), (\mathit{Stop} V G \mathit{live} : \mathit{Prop}) = \forall (v : V), \neg \mathit{CayleyScheduler}.\mathit{Enabled} G \mathit{live} v$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Stop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.15 (Active).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), (\mathit{active} V G \mathit{live} : \mathit{SimpleGraph} V) = \{ \mathit{Adj} := \mathit{fun} (v w : V) => v \in \mathit{live} \land w \in \mathit{live} \land G.\mathit{Adj} v w \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.active` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.16 (Choice Product).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{live}: \mathit{Set} V), \forall (l: \mathit{List} V), (\mathit{choiceProduct} V G \mathit{live} l : \mathbb{N}) = \mathit{List}.\mathit{recOn} (\mathit{motive} := \mathit{fun} (x : \mathit{List} V) => \mathit{Set} V \to \mathbb{N}) l (\mathit{fun} (x : \mathit{Set} V) => 1) (\mathit{fun} (v : V) (x : \mathit{List} V) (\mathit{rec} : \mathit{Set} V \to \mathbb{N}) (\mathit{alive} : \mathit{Set} V) => \mathit{Nat}.\mathit{card} \{ w : V  |  \mathit{CayleyScheduler}.\mathit{Enabled} G \mathit{alive} w \} \cdot \mathit{rec} (\mathit{alive} \setminus \{v\})) \mathit{live}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.choiceProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.17 (Conflict).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{color}: V \to K), (\mathit{conflict} V K G \mathit{color} : \mathit{SimpleGraph} V) = \{ \mathit{Adj} := \mathit{fun} (v w : V) => G.\mathit{Adj} v w \land \mathit{color} v = \mathit{color} w \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.conflict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.18 (Proper policy Run).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{DecidableEq} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{policy}: \mathit{CayleyScheduler}.\mathit{FreePolicy} G), \forall (\mathit{init}: V \to K), \forall (\mathit{history}: \mathit{List} V), \mathit{CayleyScheduler}.\mathit{LegalPrefix} (\mathit{conflict} G \mathit{init}) \mathit{Set}.\mathit{univ} \mathit{history} \land \mathit{CayleyScheduler}.\mathit{Stop} (\mathit{conflict} G \mathit{init}) (\mathit{remaining} \mathit{Set}.\mathit{univ} \mathit{history}) \iff \exists (\mathit{final} : V \to K), \mathit{CayleyScheduler}.\mathit{PolicyRun} G \mathit{policy} [] \mathit{init} \mathit{history} \mathit{final} \land \forall (v w : V), \neg (\mathit{conflict} G \mathit{final}).\mathit{Adj} v w$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.proper_policyRun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.19 (Ranked History).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: \mathit{Equiv}.\mathit{Perm} V), \forall (\mathit{live}: \mathit{Set} V), (\mathit{rankedHistory} V G \mathit{rank} \mathit{live} : \mathit{List} V) = \mathit{choose} (\mathit{fun} (l : \mathit{List} V) => \mathit{Complete} G \mathit{rank} \mathit{live} l)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complete histories exist and are unique for the given graph, ranking and live set.

**Theorem 1.20 (Ranked History spec).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: \mathit{Equiv}.\mathit{Perm} V), \forall (\mathit{live}: \mathit{Set} V), \mathit{CayleyScheduler}.\mathit{Complete} G \mathit{rank} \mathit{live} (\mathit{rankedHistory} G \mathit{rank} \mathit{live})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.21 (Ranked moves complement).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{rank}: \mathit{Equiv}.\mathit{Perm} V), (\mathit{rankedHistory} G \mathit{rank} \mathit{Set}.\mathit{univ}).\mathit{length} = \mathit{Fintype}.\mathit{card} V - \mathit{filterCard} \mathit{fun} (v : V) => \forall (w : V), G.\mathit{Adj} v w \to \mathit{rank} w < \mathit{rank} v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.ranked_moves_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.22 (Remaining).**

$$\forall (V: \mathit{Type}), \forall (\mathit{live}: \mathit{Set} V), \forall (\mathit{history}: \mathit{List} V), (\mathit{remaining} V \mathit{live} \mathit{history} : \mathit{Set} V) = \{v : V | v \in \mathit{live} \land v \neg \in \mathit{history}\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.remaining` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Complete`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Enabled`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.First`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.FreePolicy`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.HistoryRank`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalPrefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.LegalRun`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Moves`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.NextRank`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.PolicyRun`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.Stop`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.active`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.choiceProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.conflict`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.legal`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.proper_policyRun`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.rankedHistory_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.ranked_moves_complement`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.remaining`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition](TreeDecomposition.md)
