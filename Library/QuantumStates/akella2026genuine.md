---
bibkey: akella2026genuine
authors: S. Akella, N. Iizuka, A. Miyata
year: 2026
title: "Genuine Multi-Entropy in the Toric Code"
doi: 10.48550/arXiv.2607.06050
url: https://arxiv.org/abs/2607.06050v2
claim: "The paper conjectures that for stabilizer states and q ≥ 4 the q-partite genuine multi-entropy at replica index n < q collapses to multi-entropies of at most q − 2 parties; at q = 4 the n = 3 case reads GM^{(4)}_{n=3} = −(a − 1/9) I_3, and whether a counting argument exists for n = 3 is stated as open."
strata_touched:
  - D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
  - D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit
license: citation-only
triage: anchor
---

# Akella, Iizuka and Miyata, genuine multi-entropy in the toric code

S. Akella, N. Iizuka and A. Miyata, *Genuine Multi-Entropy in the Toric Code*,
arXiv:2607.06050 (v1: 7 July 2026; hep-th, cross-listed cond-mat.str-el and quant-ph).
The current source checked for this note is v2, retrieved on 21 October 2026.

## Verified locator

DOI: 10.48550/arXiv.2607.06050.
Primary version checked: https://arxiv.org/abs/2607.06050v2.
The TeX source of v2 supplies §1 (Eq. (1), the tripartite information; Eqs. (2) and (3), the $n=2$ and $n=3$ collapses), §2 (the definition of $\mathrm{GM}^{(4)}_n$),
§6 (the open question) and Appendix A (the replica definition of the multi-entropy).

## Source statements

Rényi tripartite information (§1): "$I_{3,n} = S^{(2)}_n(BCD:A) +S^{(2)}_n(CDA:B) +S^{(2)}_n(DAB:C)
+S^{(2)}_n(ABC:D) -S^{(2)}_n(AB:CD) -S^{(2)}_n(AC:BD) -S^{(2)}_n(AD:BC)$".

Genuine four-partite multi-entropy (§2): "$\GM[4]_n(A:B:C:D) = S^{(4)}_n(A:B:C:D) -\frac{1}{3}\Big[
S^{(3)}_n(AB:C:D) +S^{(3)}_n(AC:B:D) +S^{(3)}_n(AD:B:C) +S^{(3)}_n(BC:A:D) +S^{(3)}_n(BD:A:C)
+S^{(3)}_n(CD:A:B)\Big] +\frac{1}{3}\Big[ S^{(2)}_n(ABC:D) +S^{(2)}_n(ABD:C) +S^{(2)}_n(ACD:B)
+S^{(2)}_n(BCD:A)\Big] -a\, I_{3,n}$", with "$a$ is a real parameter".

Eq. (3): "$\GM[\mathtt{q}=4]_{n=3}(A:B:C:D) = -\left(a-\tfrac{1}{9}\right) I_3$", where "$I_3$
denotes the common value of the R\'enyi tripartite information $I_{3,n}$ for stabilizer states,
which is independent of $n$", and "Unlike the $n=2$ relation, this reduction is not a consequence
of the Coxeter structure of the corresponding multi-entropy."

Appendix A: "$S_n^{(\mathtt{q})}(A_1:\cdots:A_{\mathtt{q}}) = \frac{1}{1-n}\frac{1}{n^{\mathtt{q}-2}}
\log\left[ \frac{Z_n^{(\mathtt{q})}}{\left(Z_1^{(\mathtt{q})}\right)^{n^{\mathtt{q}-1}}}\right]$",
"$Z_n^{(\mathtt{q})} = \bra{\psi}^{\otimes n^{\mathtt{q}-1}} \Sigma_1(g_1)\Sigma_2(g_2)\cdots
\Sigma_{\mathtt{q}}(g_{\mathtt{q}}) \ket{\psi}^{\otimes n^{\mathtt{q}-1}}$", with the replicas labeled by
the points of $(\mathbb Z/n)^{\mathtt q-1}$, $g_i$ shifting coordinate $i$ and $g_{\mathtt q}$ the identity.

§6: "Whether there is a similar counting argument for $n = 3$ case is an open question."

## Scope

The paper establishes Eq. (3) by explicit computation for toric-code stabilizer states and states
the general $\mathtt q=4$, $n=3$ collapse for stabilizer states; the follow-up arXiv:2608.29627 reports
it as established numerically for general qubit stabilizer states. The $n=2$ counting argument is
in arXiv:2601.16258.

Akella and Gadde, *Rényi multi-entropy of graph states and the $n\to1$ limit*,
[arXiv:2610.27080v1](https://arxiv.org/abs/2610.27080v1) (19 October 2026),
§II Eqs. (7)–(9) and Appendix A, prove positivity and an exact rank sum for qubit
graph states at every odd replica number. Their fixed-$n$ rank formula is general;
the collision-controlled graph hypothesis belongs to their polynomial continuation
result and is not needed for the following fixed-$n=3$ comparison. Their Eq. (2)
explicitly omits the factor $n^{-(q-2)}$ retained in Appendix A of 2607.06050v2 and
in the formal definition here.

At $n=3$, the nonzero elements of $\mathbb F_4$ are $1,\omega,\omega^2$.
For distinct such $a,b$, $ab(a+b)=1$. Thus the invertible diagonal matrix
$D_{uu}=t_u$ transforms their matrix
$\Upsilon_{uv}(t)=\Gamma_{uv}(t_u-t_v)$ into the binary separation matrix:
$(D\Upsilon(t)D)_{uv}=\Gamma_{uv}$ when $t_u\ne t_v$ and zero otherwise.
Its rank therefore depends only on the equality partition, for every graph at
this replica number. With the final party label fixed to $1$, each partition
with two or three blocks has two labelings, and partitions with more than three
blocks have none. The one-block matrix has rank zero. If $R_\pi$ is the binary
rank of the separation matrix, their rank sum becomes
$r_G(3)=2\sum_{|\pi|=2\text{ or }3}R_\pi$. Restoring the stated normalization in
the three arities used by the four-party relation gives

$$
S_3^{(q)}=\frac{\log 2}{2\,3^{q-2}}
\sum_{|\pi|=2\text{ or }3}R_\pi,\qquad q\in\{2,3,4\}.
$$

For four parties let $A,B,C$ be the rank sums over partitions of block sizes
$3+1$, $2+2$, and $2+1+1$, respectively. The four singleton cuts, three balanced
cuts and six pair mergers then give

$$
S_3^{(4)}=\frac{\log 2}{18}(A+B+C),\qquad
\sum_{\text{pair mergers}}S_3^{(3)}=\frac{\log 2}{6}(3A+2B+C),
$$

$$
\sum_{\text{singleton cuts}}S_3^{(2)}=\frac{\log 2}{2}A,\qquad
I_3=\frac{\log 2}{2}(A-B).
$$

Consequently the first three terms in the genuine four-party combination equal
$I_3/9$, yielding $\mathrm{GM}_3^{(4)}=-(a-1/9)I_3$. This is a primary-text and
algebraic comparison with the later rank formula, not a Lean verification of
that paper or an exhaustive priority assessment. The §6 quotation remains the
original paper's question; it does not certify the current absence of other
proofs. The present delivery is a structural formal proof and reusable library
growth for an existing conclusion, with no new unique-solve or global-priority
claim. The existing closed project resolution #13575 and its resolution slug
remain the historical project record.

TernaryPartitionOrbit classifies opposite nonzero ternary modes by anchored equality partitions over an arbitrary index type. StabilizerMultiEntropyCollapse now consumes that classification in its original partition_count proof: arbitrary surjective mergers give quotient colourings, subtracting the quotient colouring's value at its chosen target anchor preserves its equality partition, and representative selection gives a bijection that transports arbitrary weighted partition sums. Four anchored labels have thirteen nonconstant ternary patterns; the fifteen-element partition catalogue verifies the coefficients of the full term, six pair mergers, four singleton cuts and three balanced cuts. This supplies a structural counting argument for the four-party, n=3 relation in Eq. (3). It does not identify a Coxeter group, prove a general partition coefficient formula, or settle other party counts, replica indices, mixed states or qudit analogues.
