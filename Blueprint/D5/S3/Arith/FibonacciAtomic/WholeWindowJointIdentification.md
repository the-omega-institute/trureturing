# Complete Joint Identification on Whole Windows

## Abstract

The complete joint law determines the channel intensity and, at positive intensity, all three ordered teacher positions under every real full-support whole-window law.

**Theorem 1.1 (Probability-law certification and the complete identification equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WholeWindowJointIdentification.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/WholeWindowJointIdentification.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be any natural number at least three. The alphabet Sigma consists of the five windows 000, 100, 010, 101 and 001, with bits written from low to high. Write l for the first bit and h for the last bit. Let mu:Sigma -> R be any strictly positive mass function with sum_s mu(s)=1. Inputs x range over the entire product Sigma^n, and have mass w(x)=product_i mu(x_i). The windows are independent with their common law mu; the bits within each window keep their actual joint relation. Positions are indexed from zero through n-1.

For any increasing triple theta=(p,q,r), set G1=h_p l_q, G2=(1-G1)h_q l_r and C_theta=G1+2G2. Thus the first event has priority: if both unmasked seam events hold, the response is 1. The response is 2 only when the first event fails and the second holds, and otherwise it is 0. All input windows outside this triple remain in the joint law.

In the fixed label order 0,1,2, put A=sqrt(2)-1 and D=(3-2sqrt(2))/2. The channel Q has rows (1/2,A,D), (1/4,1/2,1/4) and (D,A,1/2). For any intensity a in the closed interval [0,1], define the conditional row R_{theta,a}(x,j)=a Q(C_theta(x),j)+(1-a)/3. The complete joint mass is J_{theta,a}(x,j)=w(x)R_{theta,a}(x,j).

For every pair of increasing triples theta and eta and every alpha,beta in [0,1], the theorem certifies that both J_{theta,alpha} and J_{eta,beta} are strictly positive at every (x,j) and each has total mass one. It also proves the full equivalence: J_{theta,alpha}=J_{eta,beta} if and only if alpha=beta and either alpha=0 or theta=eta. Equality here is equality of the complete joint mass functions, at every input and every fixed label.

The bounds 1<sqrt(2)<3/2 make all entries of Q positive, and each row sums to one. Convex mixing with the uniform row retains strict positivity, including both endpoints. Finite product expansion gives sum_x w(x)=(sum_s mu(s))^n=1, so summing the conditional rows certifies the two joint probability laws.

At the all-zero input every teacher responds with class 0. Its positive input mass can be canceled, and the label-0 coordinate a/2+(1-a)/3 recovers the intensity. At a common nonzero intensity, cancellation at every input recovers equality of the teacher responses: the column-0 entries 1/2,1/4,D are pairwise distinct.

To recover the positions, use the input with window 001 at p, window 100 at q and zero elsewhere. Its only high bit is at p and its only low bit is at q, and theta responds with 1. Any teacher responding with 1 on this input must have its first position at p and its second at q. Next put 001 at q and 100 at r, with zero elsewhere. Since p<q, the first event is absent, and theta responds with 2. A response of 2 forces the second position to be q and the third to be r. Equality of teacher functions therefore identifies all three roles. These two probes also account for priority preemption.

The reverse implication follows directly from the mass formula. At intensity zero every teacher shares independent uniform labels; at intensity one the original Q is retained. The statement includes n=3 and arbitrary nonadjacent, overlapping or disjoint increasing selections. There is no terminal-language conditioning or seam-legality restriction. Identification concerns exact population laws under the same known mu; it does not assert a finite-sample estimation rate.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WholeWindowJointIdentification.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap](GarbledPosteriorRootGap.md)
