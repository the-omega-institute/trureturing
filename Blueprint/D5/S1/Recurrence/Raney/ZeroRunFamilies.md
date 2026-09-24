# Raney Zero-Run Coefficient Families

## Abstract

For every admissible Raney sequence, nonzero residues occur arbitrarily far out and every actual maximal zero-run length lies in finitely many affine prime-power families.

Eu, Huang, and Kao's Conjecture 7.1 asks for finite affine prime-power families containing the tied left-to-right record values of the actual zero-run sequence. The theorem here keeps the literal integral Raney quotient and proves the stronger statement for every actual maximal finite zero interval. Its separate unbounded-support conjunct rules out an infinite zero tail. It neither truncates to finite prefixes nor asserts that every coefficient-family term is realized.

**Definition 1.1 (The literal integral Raney number).**

$$\forall k \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{raneyNumber}\left(k, r, n\right) = \operatorname{NatDiv}\left(r \cdot \operatorname{choose}\left(k \cdot n + r, n\right), k \cdot n + r\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/ZeroRunFamilies.raneyNumber` (`✓ std3`).

*Citation.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Commentary.*

For natural k,r,n, raneyNumber(k,r,n) is the natural quotient r*binomial(k*n+r,n)/(k*n+r), exactly as in the source. The theorem assumes positive k and r. Its proof establishes the needed exact division identity before casting to ZMod(p); it does not divide by k*n+r in the residue field.

**Theorem 1.2 (All actual Raney zero runs have finite coefficient data).**

$$\forall k \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall p \in \mathbb{N},\; (0 < k \land 0 < r \land \operatorname{Prime}\left(p\right) \land \neg (p \mid k \cdot r)) \Rightarrow ((\forall cutoff \in \mathbb{N},\; \exists n \in \mathbb{N},\; cutoff \leq n \land \operatorname{castZMod}\left(\operatorname{raneyNumber}\left(k, r, n\right), p\right) \neq 0) \land (\exists C \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}, \mathbb{N}\right)\right),\; (\forall abc \in \operatorname{members}\left(C\right),\; 0 < \operatorname{third}\left(abc\right)) \land (\forall first \in \mathbb{N},\; \forall last \in \mathbb{N},\; (\operatorname{IsMaximalDeltaInterval}\left(\operatorname{singleton}\left(0\right), \operatorname{raneyResidue}\left(k, r, p\right), first, last\right)) \Rightarrow (\exists abc \in \operatorname{members}\left(C\right),\; \exists m \in \mathbb{N},\; \operatorname{third}\left(abc\right) \cdot \left(last + 1 - first\right) = \operatorname{first}\left(abc\right) \cdot p^{m} + \operatorname{second}\left(abc\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families` (`✓ std3`). ∎

*Resolves.* `Problems/raney-conjecture-7-1-zero-run-record-families` (proved) by `D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"raney-conjecture-7-1-zero-run-record-families","declaration_gid":"D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sen-Peng Eu, Zai-Ting Huang, and Louis Kao (2026). *Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes*. URL: <https://arxiv.org/html/2609.25742v1>.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

Let k,r be positive and p prime with p not dividing k*r. First, for every cutoff there is n at least that cutoff with raneyNumber(k,r,n) nonzero modulo p. Second, one finite set C of integer triples (a,b,c), all with c>0, is chosen before arbitrary first and last. Every actual maximal zero interval satisfies c*(last+1-first)=a*p^m+b for some member of C and some natural m. Thus all tied record lengths belong to the required finite union.

The proof first derives a guarded adjacent-binomial identity. At n=0 the predecessor term is zero; for n>0 it proves that (k-1)*choose(k*n+r-1,n-1) is bounded by choose(k*n+r-1,n), and their natural difference equals the literal quotient. This supplies both integrality and the later residue readout.

Set A=max(k-1,r-1), State=Fin(A+1) x Bool, and Alphabet=State -> ZMod(p). The false Boolean component evaluates choose(k*n+a,n). The true component evaluates the guarded predecessor choose(k*n+a,n-1), with value zero at n=0. For a base-p digit d, the next index (k*d+a)/p remains in Fin(A+1). Lucas' theorem supplies the normal transition, the positive-digit predecessor transition, and the zero-digit borrow transition. The resulting list of p digit transforms is a p-uniform morphism, and the complete evaluation vector is its pointwise fixed word, including leading zeros.

At state r-1, the ordinary value minus (k-1) times the predecessor value is exactly the literal Raney residue. For sufficiently large j with r-1<p^(j-1), the Lucas readout at n=p^j reduces to k modulo p. Since p does not divide k*r, p does not divide k, so these arbitrarily large values are nonzero. Applying the generic actual-block coefficient theorem with Delta={0} proves the second conjunct.

This is repository proof content assembled from the BKS maximal-block mechanism and the literal Raney source. The formal admission is proof_shape content with admission_basis escape-witness, not the bind-only open-problem exemption. The known (3,2) and Catalan (2,1) cases receive no separate credit. The bounded prior search found no full settlement in the inspected repository, arXiv, Crossref, and issue scope; OpenAlex returned HTTP 429, and worldwide priority remains unverified.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/ZeroRunFamilies.raneyNumber`
- Truth anchor: `D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families`
- Dependency: [D5/S1/Recurrence/Raney/FinitePathDisplacements](FinitePathDisplacements.md)
