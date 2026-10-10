---
bibkey: gesmundo2025bridge
authors: Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan
year: 2025
title: Quantum max-flow in the bridge graph
doi: 10.1007/s00031-024-09863-2
url: https://arxiv.org/abs/2212.09794v2
claim: "Conjectures 1.4 and 3.14 predict quantum max-flow equals quantum min-cut in the symmetric bridge regions; Proposition 3.18 reduces them to Conjecture 3.15 at width three."
strata_touched:
  - D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound
  - D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit
  - D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s00031-024-09863-2

Source: https://arxiv.org/abs/2212.09794v2

The journal version is in Transformation Groups 30, 1751–1784. Page numbers below refer to the arXiv v2 PDF.

## Source statements

Conjecture 1.4, page 6, states: “Let $(a,b),(a',b')\in U_w\cup V_w\cup W_w$. Then”

$$
\operatorname{QMaxFlow}\begin{pmatrix}a&b\\b'&a'\end{pmatrix}_{w}
=\operatorname{QMinCut}\begin{pmatrix}a&b\\b'&a'\end{pmatrix}_{w}
=\min\{a\cdot b',a'\cdot b\}.
$$

Conjecture 3.14, page 19, repeats this statement. Conjecture 3.15, page 19, states: “Let $(a,b),(a',b')\in U_3\cup V_3\cup W_3$. Then” and displays $\operatorname{QMinCut}=\operatorname{QMaxFlow}=\min\{a'b,ab'\}$ with $w=3$.

Page 3 states: “Let F_{T,T′} ∈ A ⊗ B ⊗ A′ ⊗ B′ be the tensor obtained by contracting the factor W of T with the factor W* of T′; this is the tensor network state defined by T and T′ on the bridge graph.”

The definition on page 3 reads: “The quantum max-flow is the maximum possible value of $\operatorname{rank}(F_{T,T'})$ as $T$ and $T'$ vary in the respective spaces; we write” and displays the maximum over $T\in A\otimes B\otimes W$ and $T'\in A'\otimes B'\otimes W^*$.

## Encoding and scope

The Lean letters $(a,b,c,d)$ denote the source's $(a,b,a',b')$. With $w=3$, the matrix is $\sum_{i=1}^3 M_i\otimes N_i$, with complex $a\times b$ matrices $M_i$ and $d\times c$ matrices $N_i$. This is the transpose of the source flattening $(A\otimes B')^*\to B\otimes A'$. Matrix rank is invariant under transpose. The supremum of attainable natural ranks is a maximum: the set is nonempty, finite and bounded by $\min(ad,bc)$.

Page 4 partitions the positive dimension pairs by $\lambda_w=(w+\sqrt{w^2-4})/2$. Thus $U_3\cup V_3\cup W_3$ is $a\le b\le\lambda_3 a$. For $a>0$ and $t=b/a\ge1$, the polynomial $t^2-3t+1$ factors as $(t-(3-\sqrt5)/2)(t-(3+\sqrt5)/2)$. Its smaller root is below 1. Consequently the source condition is equivalent to $a\le b$ and $a^2+b^2\le3ab$. The same reasoning applies to $(c,d)$.

Proposition 2.4, page 9, states: “Let a, b, w, a′, b′ be integers with a ≤ b, a′ ≤ b′. The quantum min-cut in the bridge graph is” followed by $\operatorname{QMinCut}=\min\{aa′w,ab′,a′b\}$. Under $a\le b$ and $c\le d$, this gives $\operatorname{QMinCut}=\min(3ac,ad,bc)$ at width three. The public function uses this ordered-case expression; its identification with the graph min-cut is asserted only on that domain. On the region this is $\min(ad,bc)$. The Lean claim retains both equalities of Conjecture 3.15.

## Related results

Theorem 3.1 is the castling transformation law. The delivered castling proof establishes its needed width-three deficit identity over a field by common kernels and annihilator complements; it does not assume Theorem 3.1.

Theorem 3.10 treats different castling depths. Theorem 3.13 treats proportional dimension pairs. The construction addresses the remaining strict bases by a cyclic resolvent and short and long reservoir equations.

Proposition 3.18, page 20, states: “If” quantum min-cut equals quantum max-flow at width three “for all $(a,b),(a',b')\in U_3\cup V_3\cup W_3$ then” the equality holds at width $w$ “for all $(a,b),(a',b')\in U_w\cup V_w\cup W_w$.” Its induction uses $U_w=U_{w-1}\cup V_{w-1}\cup W_{w-1}$, Lemma 3.17, Theorem 3.10 and Corollary 3.9. This implication is a literature result; the Lean delivery proves its width-three hypothesis and does not formalize Proposition 3.18.
