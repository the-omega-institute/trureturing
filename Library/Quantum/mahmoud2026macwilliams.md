---
bibkey: mahmoud2026macwilliams
authors: Ali Assem Mahmoud
year: 2026
title: "Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes"
doi: 10.48550/arXiv.2607.26214
url: https://arxiv.org/abs/2607.26214v1
claim: "Theorem 5.3 gives the weight-isometric, monomially inequivalent pairs of [[5,2]] codes S_A = <ZZZZI, XXIIX, IIXXX>, S_B = <ZZIZX, XIZXI, IXXYI> and of [[6,3]] codes S+ = <XXIIXX, IIXXXX, ZZZZIX>, S- = <XXZXII, ZZXYII, IZZZXX>; Question 5.4 asks whether the codespaces of S_A and S_B, or those of S+ and S-, are mapped to one another by some product unitary U1 x ... x Un composed with a qubit permutation. Open problem 2 of §6.2 expects q+1 to be the minimal length at which the quantum extension property QEP(q,n) fails, for every prime power q."
strata_touched:
  - D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence
  - D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength
license: citation-only
triage: anchor
---

# Minimal Counterexamples of the MacWilliams Extension Theorem for Stabilizer Codes

A. A. Mahmoud, "Minimal Counterexamples of the MacWilliams Extension Theorem
for Stabilizer Codes", arXiv:2607.26214v1 (2026-07-30; primary quant-ph,
cross-listed to math-ph).

The paper asks whether every weight-preserving isomorphism of stabilizer groups
is implemented by local Cliffords and a qudit permutation, and constructs
counterexamples at the smallest lengths. Lemma 3.2 shows that the number `t` of
qubits on which the code projector acts as the identity is invariant under
product unitaries and permutations, and Theorem 3.3 (iii) uses it to separate
the codespaces of the basic `[[q+1, q−1]]_q` family. Theorem 5.3 gives two
full-support pairs on which `t` vanishes:

- (ii) the `[[5,2]]` codes `S_A = ⟨ZZZZI, XXIIX, IIXXX⟩` and
  `S_B = ⟨ZZIZX, XIZXI, IXXYI⟩`;
- (iii) the `[[6,3]]` codes `S+ = ⟨XXIIXX, IIXXXX, ZZZZIX⟩` and
  `S− = ⟨XXZXII, ZZXYII, IZZZXX⟩`.

After Theorem 5.3 the paper states:

> For the pairs in Theorem 5.3(ii),(iii) the invariant t vanishes on both
> sides, and we know of no invariant separating the two codespaces under
> general local unitaries:
> Question 5.4 (Extension analogue of LU–LC). Are the codespaces of SA and SB
> of Theorem 5.3(ii)—or those of S+ and S− of Theorem 5.3(iii)—mapped to one
> another by some product unitary U1⊗···⊗Un composed with a qubit
> permutation? More generally: do there exist weight-isometric stabilizer
> codes that are locally unitarily equivalent but not locally Clifford
> equivalent—or is local-unitary equivalence of weight-isometric pairs always
> witnessed monomially?

and §6.2 repeats it as open problem 1, calling the `[[5,2]]` pair "the minimal
open instance".

The quantum extension property is set up over the label alphabet
`A_q = F_q^2` with the trace-symplectic form (§2.1–2.2):

> A \emph{monomial transformation} of $\A_q^n$ is a map $$(u_1,\dots,u_n)\mapsto(\tau_1(u_{\pi^{-1}(1)}),\dots,\tau_n(u_{\pi^{-1}(n)}))$$ for a permutation $\pi\in S_n$ and $\tau_i\in\Sp(2,q)$ acting on each label.

> Fix $q$ and $n$. We say the quantum extension property $\mathrm{QEP}(q,n)$ holds if for every pair $C,D\le\A_q^n$ of trace-symplectically self-orthogonal additive codes and every additive bijection $f\colon C\to D$ with $\wt(f(u))=\wt(u)$ for all $u\in C$, the map $f$ extends to a monomial transformation of $\A_q^n$.

Open problem 2 of §6.2:

> \textbf{Minimal length for general $q$.} Determine the minimal counterexample length for general $q$. For $q=2$ it is $3=q+1$ (Theorem~\ref{thm:census}); we expect $q+1$ to be minimal in general, in the light of the threshold results for additive isometries in \cite{Dyshko16,DyshkoGeom}, but we claim it only for $q=2$.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2607.26214
- URL: https://arxiv.org/abs/2607.26214v1 (the only version; full text
  retrieved 2026-09-29).
- Location: Lemma 3.2 and Theorem 3.3 in §3; Theorem 5.3 and Question 5.4 in
  §5; open problems 1 and 2 in §6.2.
- Source `MzWi_Ext_Th.tex`, md5 `ee3d0a4f9ba273634eb55aad8ed7b850`:
  - the setting, l. 211–217;
  - Definition 2.1, l. 221–223;
  - Definition 2.3, l. 237–239;
  - open problem 2, l. 429.
